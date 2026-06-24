#!/usr/bin/env python3
"""
LLM 直接读取 JS 源码，生成完整 .ts 文件（带类型注解）。

用法:
  export DEEPSEEK_API_KEY="sk-..."

  python3 generate/llm_ts.py \
      --source-dir tests/typeweaver \
      --output-dir output_ts_llm

  python3 generate/llm_ts.py \
      --source-dir tests/typeweaver \
      --output-dir output_ts_llm \
      --packages ansi-regex,abab
"""
import argparse, json, os, re, sys, time, urllib.request, urllib.error


# ==================== JS 收集 ====================

def collect_js_files(pkg_dir):
    """递归收集所有 .js 文件，返回 {relpath: content}。"""
    files = {}
    for root, dirs, filenames in os.walk(pkg_dir):
        dirs[:] = [d for d in dirs if d not in ("node_modules", ".git", "results")]
        for f in filenames:
            if f.endswith(".js"):
                fpath = os.path.join(root, f)
                rel = os.path.relpath(fpath, pkg_dir)
                with open(fpath, errors="ignore") as fh:
                    content = fh.read()
                files[rel] = content
    return files


# ==================== LLM Prompt ====================

def build_ts_prompt(relpath, js_content, all_relpaths):
    """构造 LLM prompt — 要求直接输出带类型的 .ts 代码。"""
    file_list = "\n".join(f"  - {p}" for p in sorted(all_relpaths))

    return f"""你是 TypeScript 专家。将以下 JS 文件转为 TypeScript，添加精确的类型注解。

## 当前文件: {relpath}
## 包内所有文件:
{file_list}

## JS 源码
```js
{js_content}
```

## 规则
1. 直接输出完整的 TypeScript 代码，保留所有原有逻辑和注释
2. 为所有函数声明添加参数类型和返回类型
3. 为顶层变量声明添加类型注解 (const/let/var)
4. 从使用模式推断精确类型: typeof检查、默认值、return语句、方法调用
5. import/export 语句保持不变
6. 不要用 any/object 除非完全无法推断
7. 不要改变代码结构，只添加类型注解

## 输出
仅输出 ```typescript 代码块中的 .ts 内容，不要任何解释。"""


# ==================== API 调用 ====================

def call_deepseek(api_key, prompt, model="deepseek-chat",
                  base_url="https://api.deepseek.com/v1",
                  temperature=0, max_tokens=4096, timeout=60):
    """调用 DeepSeek API。"""
    url = f"{base_url}/chat/completions"
    body = json.dumps({
        "model": model,
        "messages": [
            {"role": "system", "content": "You are a TypeScript expert. Output only valid TypeScript code, no explanations."},
            {"role": "user", "content": prompt},
        ],
        "temperature": temperature,
        "max_tokens": max_tokens,
    }).encode("utf-8")

    req = urllib.request.Request(url, data=body, headers={
        "Content-Type": "application/json",
        "Authorization": f"Bearer {api_key}",
    })

    try:
        resp = urllib.request.urlopen(req, timeout=timeout)
        data = json.loads(resp.read().decode("utf-8"))
        return data["choices"][0]["message"]["content"]
    except urllib.error.HTTPError as e:
        print(f"  API HTTP error: {e.code} {e.reason}")
        return None
    except Exception as e:
        print(f"  API error: {e}")
        return None


def extract_ts(response):
    """从 LLM 回复中提取 TypeScript 代码。"""
    if not response:
        return None
    m = re.search(r'```(?:typescript|ts)?\s*\n?(.*?)```', response, re.DOTALL)
    if m:
        return m.group(1).strip()
    # 无代码块则直接当做 ts 返回
    if "function" in response or "const" in response or "export" in response:
        return response.strip()
    return None


# ==================== 包发现 ====================

def discover_packages(source_dir):
    pkgs = []
    if not os.path.isdir(source_dir):
        return pkgs
    for name in sorted(os.listdir(source_dir)):
        d = os.path.join(source_dir, name)
        if not os.path.isdir(d):
            continue
        if name in ("results",) or name.endswith("_output") or name.endswith("_erase"):
            continue
        if any(f.endswith(".js") for f in os.listdir(d)):
            pkgs.append(name)
    return pkgs


# ==================== 主流程 ====================

def generate_ts_for_pkg(pkg_dir, pkg_name, output_dir, api_key, skip_existing=True,
                        **opts):
    """对每个 .js 文件调用 LLM 直接生成 .ts，保持目录结构。

    Returns:
        (status, file_count, errors)
    """
    print(f"\n{'='*60}")
    print(f"  LLM TS: {pkg_name}")
    print(f"  源目录: {pkg_dir}")
    print(f"{'='*60}")

    js_files = collect_js_files(pkg_dir)
    if not js_files:
        print(f"  ⚠ 无 .js 文件, 跳过")
        return ("skipped", 0, ["no .js files"])

    all_relpaths = list(js_files.keys())

    pkg_out_dir = os.path.join(output_dir, pkg_name)
    count = 0
    skipped = 0
    failed = 0

    for rel, js_content in sorted(js_files.items()):
        ts_rel = rel[:-3] + ".ts"
        ts_path = os.path.join(pkg_out_dir, ts_rel)

        if skip_existing and os.path.isfile(ts_path):
            print(f"  [{rel}] 跳过 (已存在)")
            skipped += 1
            count += 1
            continue

        print(f"  [{rel}] 调用 LLM ({opts.get('model', 'deepseek-chat')})...", end=" ", flush=True)

        prompt = build_ts_prompt(rel, js_content, all_relpaths)
        response = call_deepseek(api_key, prompt,
                                 model=opts.get("model", "deepseek-chat"),
                                 base_url=opts.get("base_url", "https://api.deepseek.com/v1"),
                                 temperature=opts.get("temperature", 0),
                                 max_tokens=opts.get("max_tokens", 4096),
                                 timeout=opts.get("timeout", 60))

        ts_content = extract_ts(response) if response else None
        if not ts_content:
            print("FAIL — 使用原 JS")
            ts_content = js_content
            failed += 1
        else:
            print(f"OK ({len(ts_content)} chars)")

        os.makedirs(os.path.dirname(ts_path), exist_ok=True)
        with open(ts_path, "w") as f:
            f.write(ts_content + "\n")
        count += 1

    status = "ok" if failed == 0 else f"ok ({failed} fallback)"
    print(f"  生成 {count - skipped}/{count} 个 ({skipped} 跳过) → {pkg_out_dir}/")
    return (status, count, [])


def main():
    parser = argparse.ArgumentParser(
        description="LLM-Direct: LLM 直接生成完整 .ts 文件"
    )
    parser.add_argument("--source-dir", required=True,
                        help="包含 JS 包的目录")
    parser.add_argument("--output-dir", required=True,
                        help="输出 .ts 文件的目录")
    parser.add_argument("--packages",
                        help="逗号分隔的包名列表 (默认: 自动发现)")
    parser.add_argument("--model", default="deepseek-chat")
    parser.add_argument("--base-url", default="https://api.deepseek.com/v1")
    parser.add_argument("--temperature", type=float, default=0)
    parser.add_argument("--max-tokens", type=int, default=4096)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--no-skip", action="store_true",
                        help="即使 .ts 已存在也重新生成")
    args = parser.parse_args()

    api_key = os.environ.get("DEEPSEEK_API_KEY", "")
    if not api_key:
        print("错误: DEEPSEEK_API_KEY 未设置")
        sys.exit(1)

    source_dir = os.path.abspath(args.source_dir)
    output_dir = os.path.abspath(args.output_dir)
    os.makedirs(output_dir, exist_ok=True)

    if args.packages:
        packages = [p.strip() for p in args.packages.split(",") if p.strip()]
    else:
        packages = discover_packages(source_dir)

    if not packages:
        print(f"错误: 在 {source_dir} 未找到任何 JS 包")
        sys.exit(1)

    print("=" * 60)
    print("  LLM 直接生成 .ts")
    print(f"  源目录:   {source_dir}")
    print(f"  输出目录: {output_dir}")
    print(f"  模型:     {args.model}")
    print(f"  包数量:   {len(packages)}")
    print(f"  包列表:   {', '.join(packages)}")
    print("=" * 60)

    total_start = time.time()
    results = []

    for idx, pkg_name in enumerate(packages):
        pkg_dir = os.path.join(source_dir, pkg_name)
        if not os.path.isdir(pkg_dir):
            print(f"  [{idx+1}/{len(packages)}] {pkg_name} — 目录不存在, 跳过")
            results.append((pkg_name, "skipped", 0))
            continue

        status, count, errors = generate_ts_for_pkg(
            pkg_dir, pkg_name, output_dir, api_key,
            skip_existing=not args.no_skip,
            model=args.model,
            base_url=args.base_url,
            temperature=args.temperature,
            max_tokens=args.max_tokens,
            timeout=args.timeout,
        )
        results.append((pkg_name, status, count))

    elapsed = time.time() - total_start

    print(f"\n{'='*60}")
    print(f"  完成, 耗时 {elapsed:.0f}s")
    print(f"{'='*60}")
    print(f"  {'Package':<24} {'Status':<12} {'Files':>6}")
    print(f"  {'-'*44}")
    ok = fail = skipped = 0
    for pkg, status, count in results:
        print(f"  {pkg:<24} {status:<12} {count:>6}")
        if status == "ok":
            ok += 1
        elif status == "skipped":
            skipped += 1
        else:
            fail += 1
    print(f"\n  {ok} ok, {skipped} skipped, {fail} failed")
    print(f"  输出: {output_dir}")


if __name__ == "__main__":
    main()
