#!/bin/bash

# 测试所有TypeScript版本的脚本

set -e

echo "=== TypeScript版本测试 ==="
echo ""

# 检查TypeScript环境
if command -v ts-node >/dev/null 2>&1; then
  echo "✅ 检测到 ts-node，将直接运行TypeScript文件"
  USE_TS_NODE=true
  TS_NODE_CMD="ts-node --transpile-only"
  TSC_CMD="tsc"
elif command -v tsc >/dev/null 2>&1; then
  echo "✅ 检测到 tsc，将编译后测试"
  USE_TS_NODE=false
  TS_NODE_CMD="ts-node --transpile-only"  # 可能用不到，但设置一下
  TSC_CMD="tsc"
elif command -v npx >/dev/null 2>&1; then
  echo "⚠️  检测到 npx，将尝试使用 npx 运行 TypeScript"
  # 测试 npx ts-node 是否可用
  if npx ts-node --version >/dev/null 2>&1; then
    echo "✅ npx ts-node 可用，将直接运行TypeScript文件"
    USE_TS_NODE=true
    TS_NODE_CMD="npx ts-node --transpile-only"
    TSC_CMD="npx tsc"
  elif npx tsc --version >/dev/null 2>&1; then
    echo "✅ npx tsc 可用，将编译后测试"
    USE_TS_NODE=false
    TS_NODE_CMD="npx ts-node --transpile-only"
    TSC_CMD="npx tsc"
  else
    echo "🔄 尝试通过 npx 临时安装 ts-node..."
    USE_TS_NODE=true
    TS_NODE_CMD="npx ts-node --transpile-only"
    TSC_CMD="npx tsc"
  fi
else
  echo "❌ 错误: 未找到 ts-node、tsc 或 npx，请先安装 TypeScript 或 Node.js/npm"
  echo "   安装命令: npm install -g typescript ts-node"
  echo "   或者安装 Node.js (包含 npm/npx): https://nodejs.org/"
  exit 1
fi

total_files=0
total_passed_files=0
total_test_cases=0
total_passed_tests=0

# 遍历所有case*.ts文件
for ts_file in case*.ts; do
  if [ ! -f "$ts_file" ]; then
    continue
  fi

  # 获取基础文件名（不带.ts后缀）
  base_name="${ts_file%.ts}"

  # 对应的测试文件
  test_file="${base_name}.test.json"

  if [ ! -f "$test_file" ]; then
    echo "❌ 错误: 测试文件 $test_file 不存在，跳过 $ts_file"
    continue
  fi

  total_files=$((total_files + 1))

  echo "▶ 测试文件: $ts_file"

  if [ "$USE_TS_NODE" = true ]; then
    # 使用ts-node直接运行TypeScript
    node_script=$(cat <<EOF
const fs = require('fs');
try {
  const func = require('./${ts_file}');
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
    test_output=$($TS_NODE_CMD -e "$node_script" 2>&1)
  else
    # 使用编译后的JavaScript文件
    js_file="${base_name}.js"

    # 如果编译后的JS文件不存在，尝试编译单个文件
    if [ ! -f "$js_file" ]; then
      echo "  🔄 编译 $ts_file..."
      $TSC_CMD --target es2020 --module commonjs --esModuleInterop --strict "$ts_file" 2>/dev/null || true
    fi

    if [ ! -f "$js_file" ]; then
      echo "  ❌ 编译失败，跳过 $ts_file"
      continue
    fi

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
    test_output=$(node -e "$node_script" 2>&1)
  fi

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
      echo "  ✅ $ts_file 测试通过 ($passed_tests/$total_tests)"
      total_passed_files=$((total_passed_files + 1))
    elif [ "$file_result" = "ERROR" ]; then
      echo "  ❌ $ts_file 测试错误"
    else
      echo "  ❌ $ts_file 测试失败 ($passed_tests/$total_tests)"
    fi
  else
    echo "  ❌ $ts_file 测试输出格式错误"
  fi

  echo ""
done

# 清理编译的文件（如果使用编译方式）
if [ "$USE_TS_NODE" = false ]; then
  echo "🧹 清理编译的JavaScript文件..."
  rm -f case*.js 2>/dev/null || true
fi

echo "=== TypeScript测试结果汇总 ==="
echo "📊 测试文件总数: $total_files"
echo "✅ 通过的测试文件: $total_passed_files/$total_files"
echo "📋 测试用例总数: $total_test_cases"
echo "✅ 通过的测试用例: $total_passed_tests/$total_test_cases"

if [ $total_passed_files -eq $total_files ] && [ $total_files -gt 0 ]; then
  echo "🎉 所有TypeScript测试都通过了!"
  exit 0
elif [ $total_files -eq 0 ]; then
  echo "⚠️ 未找到TypeScript测试文件"
  exit 1
else
  echo "⚠️ 有TypeScript测试失败"
  exit 1
fi