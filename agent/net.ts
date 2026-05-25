/**
 * 网络代理配置 - 可复用模块
 *
 * 使用方式：
 *   import { setupProxy } from "./agent/net";
 *   setupProxy(); // 所有 fetch 请求走代理
 *
 * 环境变量：
 *   HTTP_PROXY  - 默认 http://127.0.0.1:10805
 *   NO_PROXY_TLS - 设为 1 跳过 TLS 证书校验
 */

let _setup = false;

export async function setupProxy(proxyUrl?: string) {
  if (_setup) return;
  _setup = true;

  if (typeof globalThis.File === "undefined") {
    (globalThis as any).File = class File extends Blob {
      name: string;
      lastModified: number;
      constructor(bits: any[], name: string, opts?: any) {
        super(bits, opts);
        this.name = name;
        this.lastModified = opts?.lastModified ?? Date.now();
      }
    } as any;
  }

  const { ProxyAgent, setGlobalDispatcher } = await import("undici");

  const uri = proxyUrl || process.env.HTTP_PROXY || "http://127.0.0.1:10805";
  const rejectUnauthorized = process.env.NO_PROXY_TLS !== "1";

  setGlobalDispatcher(
    new ProxyAgent({ uri, requestTls: { rejectUnauthorized } })
  );
}

/** 便捷方法: 带代理的 fetch，无需 setupProxy 也可直接用 */
export async function fetchWithProxy(
  url: string,
  init?: RequestInit
): Promise<Response> {
  await setupProxy();
  return fetch(url, init);
}

/** LLM API 调用封装 */
export async function chat(
  apiKey: string,
  opts: {
    baseUrl?: string;
    model?: string;
    messages: Array<{ role: string; content: string }>;
    tools?: Array<Record<string, unknown>>;
  }
): Promise<any> {
  await setupProxy();

  const baseUrl = opts.baseUrl || "https://api.deepseek.com/v1";
  const model = opts.model || "deepseek-chat";

  const body: Record<string, unknown> = {
    model,
    messages: opts.messages,
    temperature: 0,
  };
  if (opts.tools?.length) body.tools = opts.tools;

  const res = await fetch(`${baseUrl}/chat/completions`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const text = await res.text();
    throw new Error(`API ${res.status}: ${text.slice(0, 200)}`);
  }

  const data = await res.json() as any;
  return data.choices[0].message;
}
