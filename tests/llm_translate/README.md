# JavaScript 测试用例集

这是一个包含10个JavaScript函数和对应测试用例的集合，用于JavaScript到TypeScript的类型推断系统基准测试。

## 文件结构

```
# JavaScript版本
case.js                 # 产品处理函数（示例）
case.test.json          # 对应的测试用例

case1.js - case10.js    # 10个不同的JavaScript函数
case1.test.json - case10.test.json  # 对应的测试文件

# TypeScript版本（已翻译）
case.ts - case10.ts     # 对应的TypeScript类型化版本

# 测试脚本
run_all_tests.sh        # 运行所有JavaScript测试的脚本
run_test.sh             # 运行单个或所有JavaScript测试的脚本
test_js.sh              # 测试JavaScript版本，显示详细统计
test_ts.sh              # 测试TypeScript版本，显示详细统计
run_tests.sh            # 运行所有测试（JS和TS）
```

## 函数说明

### 1. `processProducts` (case.js)
- **功能**: 处理产品数组，过滤有库存的产品，计算最终价格并排序
- **类型模式**: 对象数组、可选字段、条件逻辑

### 2. `analyzeText` (case1.js)
- **功能**: 分析文本，统计单词数、字符数、最长单词和平均单词长度
- **类型模式**: 字符串处理、数字计算

### 3. `arrayIntersection` (case2.js)
- **功能**: 计算两个数组的交集，处理重复值
- **类型模式**: 数组操作、Set使用

### 4. `validateUser` (case3.js)
- **功能**: 验证用户对象，检查必填字段、类型和范围
- **类型模式**: 对象验证、条件错误收集

### 5. `calculateStats` (case4.js)
- **功能**: 计算数值数组的统计信息（平均值、最小值、最大值、总和）
- **类型模式**: 数组过滤、数字计算

### 6. `daysBetween` (case5.js)
- **功能**: 计算两个日期字符串之间的天数差
- **类型模式**: 日期处理、字符串验证

### 7. `groupByCategory` (case6.js)
- **功能**: 按类别对对象数组进行分组
- **类型模式**: 对象分组、动态键

### 8. `searchItems` (case7.js)
- **功能**: 根据过滤条件搜索数组中的对象
- **类型模式**: 条件过滤、函数参数

### 9. `formatString` (case8.js)
- **功能**: 替换字符串中的占位符为实际值
- **类型模式**: 字符串替换、正则表达式

### 10. `paginate` (case9.js)
- **功能**: 对数组进行分页，支持排序
- **类型模式**: 分页逻辑、可选参数

### 11. `charFrequency` (case10.js)
- **功能**: 统计字符串中每个字符的出现频率
- **类型模式**: 字符统计、对象计数

## TypeScript版本

所有JavaScript文件都已翻译为TypeScript版本，保持原始逻辑不变：

- **`case.ts`** - `processProducts` 函数，包含 `Product` 和 `ProcessedProduct` 接口
- **`case1.ts`** - `analyzeText` 函数，包含 `AnalysisResult` 接口
- **`case2.ts`** - `arrayIntersection` 函数，使用泛型 `<T>`
- **`case3.ts`** - `validateUser` 函数，包含 `User` 和 `ValidationResult` 接口
- **`case4.ts`** - `calculateStats` 函数，包含 `Stats` 接口
- **`case5.ts`** - `daysBetween` 函数，返回 `number | null`
- **`case6.ts`** - `groupByCategory` 函数，包含 `Item`, `ItemSummary`, `GroupedItems` 接口
- **`case7.ts`** - `searchItems` 函数，包含 `Filters` 接口和 `FilterValue` 类型
- **`case8.ts`** - `formatString` 函数，包含 `Values` 接口
- **`case9.ts`** - `paginate` 函数，使用泛型 `<T>` 和 `PaginatedResult<T>` 接口
- **`case10.ts`** - `charFrequency` 函数，返回 `Record<string, number>`

## 使用说明

### 运行所有测试

```bash
# 运行JavaScript测试
./test_js.sh

# 运行TypeScript测试（需要安装typescript和ts-node）
./test_ts.sh

# 运行所有测试（JS和TS）
./run_tests.sh

# 旧脚本（兼容性）
./run_all_tests.sh    # 仅JavaScript
./run_test.sh         # 单个或所有JavaScript测试
```

### 运行单个测试

```bash
# 使用完整文件名
./run_test.sh case1.js

# 或只使用基础名
./run_test.sh case1
```

### 新测试脚本特点

- **`test_js.sh`**：测试JavaScript版本，显示每个文件的测试通过率（如7/7）
- **`test_ts.sh`**：测试TypeScript版本，自动检测ts-node或tsc
- **`run_tests.sh`**：统一运行JS和TS测试，显示最终汇总结果

### 直接使用Node.js测试单个文件

```bash
node -e "
const func = require('./case1.js');
const tests = require('./case1.test.json');
tests.forEach((test, i) => {
  const result = func(...test.input);
  console.log(\`Test \${i+1}: \${JSON.stringify(result) === JSON.stringify(test.output) ? '✅' : '❌'}\`);
});
"
```

## 测试用例特点

1. **自包含**: 每个函数都是纯JavaScript实现，无外部依赖
2. **类型多样性**: 包含数组、对象、可选字段、条件返回等复杂类型模式
3. **完整测试**: 每个函数至少有6个测试用例，包含边界情况
4. **JSON可序列化**: 所有输入输出都是JSON可序列化的数据
5. **已验证**: 所有测试用例都已通过验证

## 适用场景

- JavaScript到TypeScript的类型推断系统测试
- 代码分析工具基准测试
- 类型系统验证
- 程序理解研究

## 许可证

此测试用例集可用于研究和开发目的。