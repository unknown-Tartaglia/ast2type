#!/bin/bash

# 检查是否提供目录
if [ $# -eq 0 ]; then
    echo "用法: $0 <目录>"
    echo "示例: $0 output/typeinfo"
    exit 1
fi

in=$1
dir=${in%/}
npx ts-node code2ast.ts -i "$dir"
npx ts-node ast2type.ts -i "${dir}_output"