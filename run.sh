#!/bin/bash

# 检查输入参数
if [ $# -eq 0 ]; then
    echo "用法: $0 目录 [文件]"
    exit 1
fi

dir=$1
file=$2

# 用于汇总统计
declare -A STATUS
rm -f 1 2 3
for input in $(find "$dir" -name "*.js"); do
    [ -e "$input" ] || continue  # 如果没有 json 文件则跳过
    [ -n "$file" ] && [[ "$(basename "$input")" != "$file" ]] && continue

    base=${input#$dir}        # a.js
    anno_file="output/typeinfo/$base.json"   # output/typeinfo/a.js.json

    echo "处理: $input -> $anno_file"

    # 未插入时
    ../fresh_aot/out/x64.debug/d8 ${input} \
    --use-pbc \
    2>3 >2
    exit_code0=${PIPESTATUS[0]}

    # 执行核心命令
    ../fresh_aot/out/x64.debug/d8 ${input} \
        --annotated-type ${anno_file} \
        --use-pbc --log-pbc \
        2>3 | tee 2 | python findAnnoInfo.py "${anno_file}" >>1

    # 捕获退出状态
    exit_code1=${PIPESTATUS[0]}

    if [ $exit_code1 -ne 0 ]; then
        if [ $exit_code0 -ne $exit_code1 ]; then
            STATUS["$input"]="❌FAIL($exit_code1)"
            echo "❌ 失败: $input $exit_code1"
        else
            STATUS["$input"]="🟡WARN($exit_code1) (未插入时也失败)"
            echo "🟡 警告: $input $exit_code1 (未插入时也失败)"
        fi
    else
        STATUS["$input"]="✅SUCCESS"
        echo "✅ 成功: $input"
    fi

    echo "--------------------------------------"
done

echo ""
echo "=========== 汇总结果 ==========="

for key in "${!STATUS[@]}"; do
    printf "%-50s %s\n" "$key" "${STATUS[$key]}"
done

echo "================================"
