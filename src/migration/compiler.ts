import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import ts from "typescript";
import type { CompileResult, Diagnostic } from "./contracts";
import { discoverTypeScriptFiles, isTypeScriptSource } from "./files";

export const UNIFORM_COMPILER_OPTIONS: ts.CompilerOptions = {
  esModuleInterop: true,
  moduleResolution: ts.ModuleResolutionKind.Bundler,
  module: ts.ModuleKind.ES2015,
  target: ts.ScriptTarget.ES2015,
  lib: ["lib.es2021.d.ts", "lib.dom.d.ts"],
  jsx: ts.JsxEmit.Preserve,
  skipLibCheck: true,
  declaration: true,
  emitDeclarationOnly: true,
  noEmitOnError: true,
  pretty: false,
};

function categoryName(category: ts.DiagnosticCategory): Diagnostic["category"] {
  switch (category) {
    case ts.DiagnosticCategory.Warning: return "warning";
    case ts.DiagnosticCategory.Error: return "error";
    case ts.DiagnosticCategory.Suggestion: return "suggestion";
    default: return "message";
  }
}

export function normalizeDiagnostic(diagnostic: ts.Diagnostic): Diagnostic {
  const result: Diagnostic = {
    code: diagnostic.code,
    category: categoryName(diagnostic.category),
    message: ts.flattenDiagnosticMessageText(diagnostic.messageText, "\n"),
  };
  if (diagnostic.file) {
    result.file = path.resolve(diagnostic.file.fileName);
    if (diagnostic.start !== undefined) {
      result.start = diagnostic.start;
      result.length = diagnostic.length ?? 0;
      const location = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start);
      result.line = location.line + 1;
      result.column = location.character + 1;
    }
  }
  return result;
}

function prepareDeclarationDirectory(directory: string): void {
  const target = path.resolve(directory);
  if (fs.existsSync(target)) {
    if (!fs.statSync(target).isDirectory() || fs.lstatSync(target).isSymbolicLink()) {
      throw new Error(`declaration output is not a directory: ${target}`);
    }
    const unexpected = fs.readdirSync(target, { recursive: true })
      .map(entry => String(entry))
      .filter(entry => {
        const full = path.join(target, entry);
        return fs.existsSync(full) && fs.statSync(full).isFile()
          && !entry.endsWith(".d.ts") && !entry.endsWith(".d.mts") && !entry.endsWith(".d.cts");
      });
    if (unexpected.length) throw new Error(`declaration output contains non-declaration files: ${unexpected[0]}`);
    fs.rmSync(target, { recursive: true });
  }
  fs.mkdirSync(target, { recursive: true });
}

function emittedDeclarations(directory: string): string[] {
  if (!fs.existsSync(directory)) return [];
  const files: string[] = [];
  const visit = (current: string): void => {
    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      const target = path.join(current, entry.name);
      if (entry.isDirectory()) visit(target);
      else if (entry.isFile() && /\.d\.(?:ts|mts|cts)$/.test(entry.name)) files.push(path.resolve(target));
    }
  };
  visit(directory);
  return files.sort();
}

export interface CheckFilesOptions {
  files: readonly string[];
  declarationDir?: string;
  compilerOptions?: ts.CompilerOptions;
}

export interface CheckProjectOptions {
  root: string;
  config?: string;
  compilerOptions?: ts.CompilerOptions;
}

function diagnosticsResult(diagnostics: readonly ts.Diagnostic[], compilerVersion: string): CompileResult {
  const errors = diagnostics.filter(item => item.category === ts.DiagnosticCategory.Error);
  return {
    status: errors.length ? "type-error" : "pass",
    diagnostics: errors.map(normalizeDiagnostic),
    emittedFiles: [],
    compilerVersion,
  };
}

export function checkFiles(options: CheckFilesOptions): CompileResult {
  const files = [...new Set(options.files
    .filter(isTypeScriptSource)
    .map(file => path.resolve(file)))]
    .sort();
  const temporary = options.declarationDir
    ? undefined
    : fs.mkdtempSync(path.join(os.tmpdir(), "ast2type-tsc-"));
  const declarationDir = path.resolve(options.declarationDir ?? temporary!);

  try {
    prepareDeclarationDirectory(declarationDir);
    if (!files.length) return { status: "pass", diagnostics: [], emittedFiles: [], compilerVersion: ts.version };
    const compilerOptions = {
      ...UNIFORM_COMPILER_OPTIONS,
      ...options.compilerOptions,
      declarationDir,
    };
    const program = ts.createProgram(files, compilerOptions);
    const diagnostics = ts.getPreEmitDiagnostics(program)
      .filter(item => item.category === ts.DiagnosticCategory.Error);
    if (diagnostics.length) {
      prepareDeclarationDirectory(declarationDir);
      return {
        status: "type-error",
        diagnostics: diagnostics.map(normalizeDiagnostic),
        emittedFiles: [],
        compilerVersion: ts.version,
      };
    }

    const emitted: string[] = [];
    const emit = program.emit(
      undefined,
      (fileName, data, writeByteOrderMark) => {
        const target = path.resolve(fileName);
        fs.mkdirSync(path.dirname(target), { recursive: true });
        fs.writeFileSync(target, `${writeByteOrderMark ? "\uFEFF" : ""}${data}`, "utf8");
        emitted.push(target);
      },
      undefined,
      true,
    );
    const emitErrors = emit.diagnostics.filter(item => item.category === ts.DiagnosticCategory.Error);
    if (emit.emitSkipped || emitErrors.length) {
      prepareDeclarationDirectory(declarationDir);
      return {
        status: "type-error",
        diagnostics: emitErrors.map(normalizeDiagnostic),
        emittedFiles: [],
        compilerVersion: ts.version,
      };
    }
    return {
      status: "pass",
      diagnostics: [],
      emittedFiles: emitted.length ? emitted.sort() : emittedDeclarations(declarationDir),
      compilerVersion: ts.version,
    };
  } catch (error) {
    try { prepareDeclarationDirectory(declarationDir); } catch { /* preserve the original failure */ }
    return {
      status: "tool-error",
      diagnostics: [],
      emittedFiles: [],
      compilerVersion: ts.version,
      error: error instanceof Error ? error.message : String(error),
    };
  } finally {
    if (temporary) fs.rmSync(temporary, { recursive: true, force: true });
  }
}

export function checkDirectory(root: string, declarationDir?: string): CompileResult {
  return checkFiles({ files: discoverTypeScriptFiles(root), declarationDir });
}

export function checkProject(options: CheckProjectOptions): CompileResult {
  const root = path.resolve(options.root);
  const config = path.resolve(root, options.config ?? "tsconfig.json");
  let compiler: typeof ts = ts;
  try {
    // Prefer the project's compiler so its tsconfig is interpreted by the intended version.
    try {
      compiler = require(require.resolve("typescript", { paths: [root] })) as typeof ts;
    } catch {
      compiler = ts;
    }
    const loaded = compiler.readConfigFile(config, compiler.sys.readFile);
    if (loaded.error) return diagnosticsResult([loaded.error], compiler.version);
    const parsed = compiler.parseJsonConfigFileContent(
      loaded.config,
      compiler.sys,
      path.dirname(config),
      options.compilerOptions,
      config,
    );
    if (parsed.errors.length) return diagnosticsResult(parsed.errors, compiler.version);
    const program = compiler.createProgram({
      rootNames: parsed.fileNames,
      options: { ...parsed.options, ...options.compilerOptions, noEmit: true },
      projectReferences: parsed.projectReferences,
    });
    return diagnosticsResult(compiler.getPreEmitDiagnostics(program), compiler.version);
  } catch (error) {
    return {
      status: "tool-error",
      diagnostics: [],
      emittedFiles: [],
      compilerVersion: compiler.version,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}
