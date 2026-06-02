import globals from "globals";
import tseslint from "typescript-eslint";

export default [
  {
    files: ["**/*.{js,ts,mjs,mts}"],
    plugins: {
      "@typescript-eslint": tseslint.plugin,
    },
    languageOptions: {
      parser: tseslint.parser,
      parserOptions: {
        projectService: {
          allowDefaultProject: true, // 允许默认项目
        }
      },
      globals: {
        ...globals.node,
        // 如果需要 Node.js 环境，添加：
        // ...globals.node,
      },
    },
    rules: {
      // TypeScript 规则
      // "@typescript-eslint/no-unused-vars": "error",
      "@typescript-eslint/no-explicit-any": "warn",
      "@typescript-eslint/no-unsafe-argument": "error",    // 禁止 any 类型的参数
      "@typescript-eslint/no-unsafe-assignment": "error",  // 禁止 any 类型的赋值
      "@typescript-eslint/no-unsafe-call": "error",        // 禁止 any 类型的函数调用
      "@typescript-eslint/no-unsafe-member-access": "error", // 禁止 any 类型的属性访问
      "@typescript-eslint/no-unsafe-return": "error",      // 禁止返回 any 类型

      // 通用 JavaScript 规则
      // "no-console": "warn",
      // "prefer-const": "error",
      // "no-var": "error",
    },
  },
];