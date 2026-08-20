import * as fs from "fs";
import * as path from "path";
import type { AppliedEdits, TextEdit } from "./contracts";

const TS_EXTENSIONS = [".ts", ".tsx", ".mts", ".cts"];
const DECLARATION_SUFFIXES = [".d.ts", ".d.mts", ".d.cts"];
const IGNORED_DIRECTORIES = new Set(["node_modules", ".git"]);

export function readSource(file: string): string {
  return fs.readFileSync(file, "utf8");
}

export function writeSource(file: string, content: string): void {
  const target = path.resolve(file);
  fs.mkdirSync(path.dirname(target), { recursive: true });
  const temporary = path.join(
    path.dirname(target),
    `.${path.basename(target)}.${process.pid}.tmp`,
  );
  fs.writeFileSync(temporary, content, "utf8");
  fs.renameSync(temporary, target);
}

export function isTypeScriptSource(file: string): boolean {
  const name = path.basename(file);
  return TS_EXTENSIONS.some(extension => name.endsWith(extension))
    && !DECLARATION_SUFFIXES.some(suffix => name.endsWith(suffix));
}

export function discoverTypeScriptFiles(root: string): string[] {
  const resolvedRoot = path.resolve(root);
  if (!fs.existsSync(resolvedRoot)) return [];
  if (fs.statSync(resolvedRoot).isFile()) {
    return isTypeScriptSource(resolvedRoot) ? [resolvedRoot] : [];
  }

  const files: string[] = [];
  const visit = (directory: string): void => {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => left.name.localeCompare(right.name))) {
      if (entry.isDirectory()) {
        if (!IGNORED_DIRECTORIES.has(entry.name)) visit(path.join(directory, entry.name));
      } else if (entry.isFile()) {
        const file = path.join(directory, entry.name);
        if (isTypeScriptSource(file)) files.push(path.resolve(file));
      }
    }
  };
  visit(resolvedRoot);
  return files;
}

export function resolveInside(root: string, candidate: string): string {
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, candidate);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative === ".." || relative.startsWith(`..${path.sep}`) || path.isAbsolute(relative)) {
    throw new Error(`path escapes root: ${candidate}`);
  }
  return resolved;
}

export function pathsOverlap(left: string, right: string): boolean {
  const first = path.resolve(left);
  const second = path.resolve(right);
  return first === second
    || first.startsWith(`${second}${path.sep}`)
    || second.startsWith(`${first}${path.sep}`);
}

export function applyTextEdits(
  root: string,
  edits: readonly TextEdit[],
  allowedFiles?: readonly string[],
): AppliedEdits {
  const allowed = allowedFiles
    ? new Set(allowedFiles.map(file => path.resolve(file)))
    : undefined;
  const byFile = new Map<string, TextEdit[]>();

  for (const edit of edits) {
    const file = resolveInside(root, edit.file);
    if (allowed && !allowed.has(file)) throw new Error(`file is not editable: ${file}`);
    if (!Number.isInteger(edit.start) || !Number.isInteger(edit.end)
      || edit.start < 0 || edit.end < edit.start) {
      throw new Error(`invalid edit range: ${edit.start}:${edit.end}`);
    }
    const group = byFile.get(file) ?? [];
    group.push({ ...edit, file });
    byFile.set(file, group);
  }

  const updates = new Map<string, string>();
  let editCount = 0;
  for (const [file, fileEdits] of byFile) {
    const content = readSource(file);
    const updated = applyEditsToText(content, fileEdits, file);
    if (updated !== content) {
      updates.set(file, updated);
      editCount += fileEdits.length;
    }
  }

  // Validate every file before writing any of them.
  for (const [file, content] of updates) writeSource(file, content);
  return { files: [...updates.keys()].sort(), edits: editCount };
}

export function applyEditsToText(
  content: string,
  edits: readonly Omit<TextEdit, "file">[],
  label = "source",
): string {
  const ordered = [...edits].sort((left, right) => left.start - right.start || left.end - right.end);
  for (let index = 0; index < ordered.length; index++) {
    const edit = ordered[index];
    if (!Number.isInteger(edit.start) || !Number.isInteger(edit.end)
      || edit.start < 0 || edit.end < edit.start || edit.end > content.length) {
      throw new Error(`invalid edit range in ${label}: ${edit.start}:${edit.end}`);
    }
    if (index > 0 && edit.start < ordered[index - 1].end) {
      throw new Error(`overlapping edits in ${label}`);
    }
  }
  let updated = content;
  for (const edit of ordered.reverse()) {
    updated = updated.slice(0, edit.start) + edit.text + updated.slice(edit.end);
  }
  return updated;
}
