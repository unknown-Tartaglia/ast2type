export type CompileStatus = "pass" | "type-error" | "tool-error";

export interface Diagnostic {
  file?: string;
  start?: number;
  length?: number;
  line?: number;
  column?: number;
  code: number;
  category: "warning" | "error" | "suggestion" | "message";
  message: string;
}

export interface CompileResult {
  status: CompileStatus;
  diagnostics: Diagnostic[];
  emittedFiles: string[];
  compilerVersion: string;
  error?: string;
}

/** Source offsets are UTF-16 code-unit offsets, matching TypeScript's API. */
export interface TextEdit {
  file: string;
  start: number;
  end: number;
  text: string;
}

export interface AppliedEdits {
  files: string[];
  edits: number;
}

export interface TypeGraphPosition {
  start: { line: number; character: number };
  end?: { line: number; character: number };
}

export interface TypeGraphNode {
  id: number;
  file?: string;
  text?: string;
  label?: string;
  position?: TypeGraphPosition;
  fullType?: unknown;
}

export interface TypeGraph {
  nodes: TypeGraphNode[];
}

export type AnnotationKind = "param" | "return" | "variable" | "property" | "index" | "index-value";

export interface AnnotationEntry {
  identifier: string;
  offset: number;
  annotationStart: number;
  annotationEnd: number;
  line: number;
  col: number;
  type: string;
  kind: AnnotationKind;
  isAsync?: boolean;
  inferable: boolean;
  matchText: boolean;
}

export type GroundTruth = Record<string, AnnotationEntry[]>;
