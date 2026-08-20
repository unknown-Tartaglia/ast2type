#!/bin/bash
# 保留脚本名作为兼容入口，所有功能由统一 TypeScript CLI 提供。
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
exec node -r ts-node/register "$ROOT/src/cli.ts" "$@"
