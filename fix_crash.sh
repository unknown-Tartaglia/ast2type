#!/bin/bash

# 检查输入参数
if [ $# -ne 2 ]; then
  echo "用法: $0 <测试程序> <json文件>"
  exit 1
fi

file=$1
json=$2
d8="../fresh_aot/out/x64.debug/d8"

# 保存所有 crash 节点内容
echo "[]" > crashes.json

run_test() {
    $d8 ${file} --annotated-type $1 --use-pbc 2>3 | tee 2 | python findAnnoInfo.py "${json}" >1
    return ${PIPESTATUS[0]}
}

bisect_once() {
    length=$(jq 'length' $json)
    local low=0
    local high=$((length - 1))

    while [ $low -lt $high ]; do
        local mid=$(( (low + high) / 2 ))
        echo "正在测试范围 [$low, $high], mid=$mid" >&2

        # 截取 [low, mid] 子区间作为 annotated-type
        jq ".[$low:$((mid + 1))]" $json > temp.json

        # 测试
        run_test temp.json
        if [ $? -ne 0 ]; then
            echo "范围 [$low, $mid] 错误" >&2
            high=$mid
        else
            echo "范围 [$low, $mid] 正常" >&2
            low=$((mid + 1))
        fi
    done

    # low 即 crash index
    echo "$low"
}


# =============================
# 主循环：反复 bisect → 删除节点
# =============================

round=1
while true; do
    echo "===== Round $round：测试当前 $json 是否仍 crash ====="

    run_test $json
    if [ $? -eq 0 ]; then
        echo "程序正常结束，不再有 crash 节点"
        break
    fi

    crash_idx=$(bisect_once)
    echo "删除 crash 节点 index $crash_idx"

    node=$(jq ".[$crash_idx]" "$json")
    jq ". += [ $node ]" crashes.json > tmp && mv tmp crashes.json
    jq "del(.[$crash_idx])" $json > tmp && mv tmp $json

    round=$((round + 1))
done

echo "全部完成！crash 节点已写入 crashes.json"
rm -f temp.json