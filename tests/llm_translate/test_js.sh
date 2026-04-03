#!/bin/bash

# 测试所有JavaScript版本的脚本

set -e

echo "=== JavaScript版本测试 ==="
echo ""

total_files=0
total_passed_files=0
total_test_cases=0
total_passed_tests=0

# 遍历所有case*.js文件
for js_file in case*.js; do
  if [ ! -f "$js_file" ]; then
    continue
  fi

  # 获取基础文件名（不带.js后缀）
  base_name="${js_file%.js}"

  # 对应的测试文件
  test_file="${base_name}.test.json"

  if [ ! -f "$test_file" ]; then
    echo "❌ 错误: 测试文件 $test_file 不存在，跳过 $js_file"
    continue
  fi

  total_files=$((total_files + 1))

  echo "▶ 测试文件: $js_file"

  # 创建Node.js脚本进行测试
  node_script=$(cat <<EOF
const fs = require('fs');
try {
  const func = require('./${js_file}');
  const testCases = require('./${test_file}');

  let passed = 0;
  let failed = 0;
  const failures = [];

  testCases.forEach((tc, idx) => {
    try {
      const result = func(...tc.input);
      const expected = tc.output;
      const resultStr = JSON.stringify(result);
      const expectedStr = JSON.stringify(expected);

      if (resultStr === expectedStr) {
        passed++;
      } else {
        failed++;
        failures.push(\`  测试 \${idx + 1} 失败\`);
        failures.push(\`    预期: \${expectedStr}\`);
        failures.push(\`    实际: \${resultStr}\`);
      }
    } catch (err) {
      failed++;
      failures.push(\`  测试 \${idx + 1} 执行错误: \${err.message}\`);
    }
  });

  console.log(\`  \${passed}/\${testCases.length} 测试通过\`);

  if (failed > 0) {
    console.log(\`  ❌ 失败详情:\`);
    failures.forEach(line => console.log(line));
  } else {
    console.log(\`  ✅ 全部通过!\`);
  }

  // 返回统计信息
  console.log(\`STATS:\${passed}:\${testCases.length}:\${failed === 0 ? 'PASS' : 'FAIL'}\`);
} catch (err) {
  console.error(\`  ❌ 测试加载错误: \${err.message}\`);
  console.log(\`STATS:0:0:ERROR\`);
}
EOF
  )

  # 执行测试并捕获输出
  test_output=$(node -e "$node_script" 2>&1)

  # 提取统计信息
  stats_line=$(echo "$test_output" | grep "^STATS:")

  # 显示测试输出（除了STATS行）
  echo "$test_output" | grep -v "^STATS:" || true

  if echo "$stats_line" | grep -q "STATS:"; then
    passed_tests=$(echo "$stats_line" | cut -d: -f2)
    total_tests=$(echo "$stats_line" | cut -d: -f3)
    file_result=$(echo "$stats_line" | cut -d: -f4)

    total_test_cases=$((total_test_cases + total_tests))
    total_passed_tests=$((total_passed_tests + passed_tests))

    if [ "$file_result" = "PASS" ]; then
      echo "  ✅ $js_file 测试通过 ($passed_tests/$total_tests)"
      total_passed_files=$((total_passed_files + 1))
    elif [ "$file_result" = "ERROR" ]; then
      echo "  ❌ $js_file 测试错误"
    else
      echo "  ❌ $js_file 测试失败 ($passed_tests/$total_tests)"
    fi
  else
    echo "  ❌ $js_file 测试输出格式错误"
  fi

  echo ""
done

echo "=== JavaScript测试结果汇总 ==="
echo "📊 测试文件总数: $total_files"
echo "✅ 通过的测试文件: $total_passed_files/$total_files"
echo "📋 测试用例总数: $total_test_cases"
echo "✅ 通过的测试用例: $total_passed_tests/$total_test_cases"

if [ $total_passed_files -eq $total_files ] && [ $total_files -gt 0 ]; then
  echo "🎉 所有JavaScript测试都通过了!"
  exit 0
elif [ $total_files -eq 0 ]; then
  echo "⚠️ 未找到JavaScript测试文件"
  exit 1
else
  echo "⚠️ 有JavaScript测试失败"
  exit 1
fi