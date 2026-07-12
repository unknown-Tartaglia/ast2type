#!/bin/bash

# 用法:
#   ./make.sh <目录>                   直接类型推断（默认仅第三步）
#   ./make.sh <目录> --prepare         完整流程: 擦除 + AST + 推断
#   ./make.sh <目录> --agent          确定性 + Agent LLM 推断
#   ./make.sh <目录> --agent --agent-candidate-mode gt  使用 GT/历史候选模式
#   ./make.sh <目录> --trace <varId>   追踪某个 varId 的类型变化
#   ./make.sh <目录> -f <file>         反馈注入模式
#   ./make.sh <目录> --js              JS 项目模式（跳过擦除阶段）
#
# 选项可组合:
#   ./make.sh <dir> --prepare --agent --trace 9854

set -e

if [ $# -eq 0 ]; then
    echo "用法: $0 <目录> [选项]"
    echo ""
    echo "选项:"
    echo "  --prepare     预处理: 擦除类型标注 + 生成 AST（默认跳过，直接用已有结果）"
    echo "  --agent       Agent LLM 工具调用推断"
    echo "  --agent-candidate-mode <fair|gt>  Agent 候选模式（默认 fair）"
    echo "  --trace <id>  追踪某个 varId 的类型变化，输出到 output/trace.json"
    echo "  -f <file>     从 feedback JSON 注入预推断的类型"
    echo ""
    echo "示例:"
    echo "  $0 tests/ts/personal_erase              # 只用已有 _erase_output 跑推断"
    echo "  $0 tests/ts/personal --prepare          # 完整流程"
    echo "  $0 tests/ts/personal --prepare --agent  # 完整 + Agent"
    echo "  $0 tests/ts/personal_erase --trace 108  # 追踪"
    echo "  $0 tests/ts/personal_erase -f output/inferinfo.json"
    exit 1
fi

in=$1
dir=${in%/}
mode="standard"
trace_id=""
feedback=""
prepare=false
js_mode=false
agent_candidate_mode="fair"
shift

while [ $# -gt 0 ]; do
    case "$1" in
        --agent)
            mode="agent"
            ;;
        --agent-candidate-mode)
            shift
            if [ $# -eq 0 ]; then
                echo "错误: --agent-candidate-mode 需要 fair 或 gt"
                exit 1
            fi
            agent_candidate_mode="$1"
            ;;
        --prepare)
            prepare=true
            ;;
        --trace)
            shift
            trace_id="$1"
            mode="trace"
            ;;
        -f)
            shift
            feedback="$1"
            mode="feedback"
            ;;
        --js)
            js_mode=true
            ;;
        *)
            echo "未知参数: $1"
            exit 1
            ;;
    esac
    shift
done

# 智能推断路径
if [ "$js_mode" = true ]; then
    input_dir="${dir}_output"
    gt=""
elif [[ "$dir" == *_output ]]; then
    input_dir="$dir"
    base="${dir%_output}"
    if [[ "$base" == *_erase ]]; then
        gt="${base}/_groundtruth.json"
    else
        gt=""
    fi
elif [[ "$dir" == *_erase ]]; then
    input_dir="${dir}_output"
    gt="${dir}/_groundtruth.json"
else
    input_dir="${dir}_erase_output"
    gt="${dir}_erase/_groundtruth.json"
fi


if [ "$prepare" = true ]; then
    if [ "$js_mode" != true ]; then
        # 第一阶段: 擦除类型标注 (TS only)
        echo "=== 擦除类型标注 ==="
        node --max-old-space-size=40960 -r ts-node/register eraseAnnotation.ts -i "$dir" -o "${dir}_erase"
        ast_input="${dir}_erase"
    else
        # JS 模式: 跳过擦除，直接对源码生成 AST
        echo "=== JS 模式: 跳过擦除，直接生成 AST ==="
        ast_input="$dir"
    fi

    # 第二阶段: 生成 AST
    echo "=== 生成 AST ==="
    node --max-old-space-size=40960 -r ts-node/register code2ast.ts -i "$ast_input"
else
    # 非 prepare 模式：检查输入目录是否存在
    if [ ! -d "$input_dir" ]; then
        echo "错误: 输入目录 '$input_dir' 不存在，请先 --prepare"
        exit 1
    fi
fi

# 第三阶段: 类型推断
echo "=== 类型推断 (模式: $mode) ==="
gt_arg=()
[ -n "$gt" ] && [ -f "$gt" ] && gt_arg=(-g "$gt")
case "$mode" in
    standard)
        node --max-old-space-size=40960 -r ts-node/register ast2type.ts \
            -i "$input_dir" \
            "${gt_arg[@]}"
        ;;
    agent)
        node --max-old-space-size=40960 -r ts-node/register ast2type.ts \
            -i "$input_dir" \
            "${gt_arg[@]}" \
            --agent \
            --agent-candidate-mode "$agent_candidate_mode"
        ;;
    trace)
        node --max-old-space-size=40960 -r ts-node/register ast2type.ts \
            -i "$input_dir" \
            "${gt_arg[@]}" \
            --trace "$trace_id"
        ;;
    feedback)
        node --max-old-space-size=40960 -r ts-node/register ast2type.ts \
            -i "$input_dir" \
            "${gt_arg[@]}" \
            -f "$feedback"
        ;;
esac

echo "=== 完成 ==="
