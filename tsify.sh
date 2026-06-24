#!/bin/bash
# ============================================
# JS → TS 类型化工具
# ============================================
# 用法:
#   ./tsify.sh pipeline  --source-dir <dir> --output-dir <dir>
#   ./tsify.sh llm       --source-dir <dir> --output-dir <dir>
#
#   pipeline: 通过 ast2type 管线推断类型, 织入 JS 生成 .ts
#   llm:      通过 LLM (DeepSeek) 直接读取 JS 生成 .d.ts, 织入生成 .ts
#
# 示例:
#   ./tsify.sh pipeline \
#       --source-dir tests/typeweaver \
#       --output-dir output_ts
#
#   DEEPSEEK_API_KEY=sk-... ./tsify.sh llm \
#       --source-dir tests/typeweaver \
#       --output-dir output_ts_llm \
#       --packages ansi-regex
# ============================================

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PYTHON="python3"

cd "$SCRIPT_DIR"

case "${1:-}" in
    pipeline)
        shift
        exec $PYTHON "${SCRIPT_DIR}/generate/pipeline_ts.py" "$@"
        ;;
    llm)
        shift
        if [ -z "${DEEPSEEK_API_KEY:-}" ]; then
            echo "警告: DEEPSEEK_API_KEY 未设置。"
            echo "用法: DEEPSEEK_API_KEY=sk-... $0 llm --source-dir <dir> --output-dir <dir>"
        fi
        exec $PYTHON "${SCRIPT_DIR}/generate/llm_ts.py" "$@"
        ;;
    ""|help|-h|--help)
        echo "JS → TS 类型化工具"
        echo ""
        echo "用法: $0 {pipeline|llm} [选项]"
        echo ""
        echo "子命令:"
        echo "  pipeline   Pipeline 类型推断 → 织入 → .ts"
        echo "  llm        LLM 直接生成 .ts (需要 DEEPSEEK_API_KEY)"
        echo ""
        echo "公共选项:"
        echo "  --source-dir <dir>   包含 JS 包的目录 (必需)"
        echo "  --output-dir <dir>   输出 .ts 的目录 (必需)"
        echo "  --packages <p1,p2>   逗号分隔的包名 (默认: 自动发现)"
        echo "  --no-skip            即使 .ts 已存在也重新生成"
        echo ""
        echo "LLM 选项 (仅 llm 子命令):"
        echo "  --model <name>       模型名 (默认: deepseek-chat)"
        echo "  --temperature <t>    温度 (默认: 0)"
        echo "  --max-tokens <n>     最大 token 数 (默认: 4096)"
        echo ""
        echo "Pipeline 选项 (仅 pipeline 子命令):"
        echo "  --timeout <sec>      每个包的超时秒数 (默认: 600)"
        echo "  --no-cleanup         保留中间产物"
        echo ""
        echo "示例:"
        echo "  $0 pipeline --source-dir tests/typeweaver --output-dir output_ts"
        echo "  $0 llm --source-dir tests/typeweaver --output-dir output_ts_llm"
        echo "  $0 pipeline --source-dir tests/typeweaver --output-dir out --packages ansi-regex"
        ;;
    *)
        echo "未知子命令: $1"
        echo "用法: $0 {pipeline|llm|help}"
        exit 1
        ;;
esac
