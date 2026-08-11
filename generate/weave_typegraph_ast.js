#!/usr/bin/env node
"use strict";

/**
 * Locate typegraph function declarations with the TypeScript AST.
 *
 * The process is intentionally read-only: JSON is read from stdin and UTF-16
 * edits are written to stdout. The Python wrapper owns filesystem writes.
 */

const fs = require("fs");
const path = require("path");
const ts = require("typescript");

function isInside(root, candidate) {
  const relative = path.relative(root, candidate);
  return relative === "" || (!relative.startsWith(`..${path.sep}`)
    && relative !== ".." && !path.isAbsolute(relative));
}

function scriptKind(file) {
  return /\.jsx$/i.test(file) ? ts.ScriptKind.JSX : ts.ScriptKind.JS;
}

function validType(typeText) {
  if (typeof typeText !== "string" || !typeText.trim()) return false;
  const probe = ts.createSourceFile(
    "__ast2type_type.ts",
    `type __Ast2TypeProbe = ${typeText};`,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  return probe.parseDiagnostics.length === 0;
}

function nodeName(node, sourceFile) {
  if (ts.isConstructorDeclaration(node)) return "constructor";
  if (node.name && (ts.isIdentifier(node.name)
      || ts.isStringLiteral(node.name)
      || ts.isNumericLiteral(node.name))) {
    return node.name.text;
  }

  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) {
    const parent = node.parent;
    if (ts.isVariableDeclaration(parent) && ts.isIdentifier(parent.name)) {
      return parent.name.text;
    }
    if (ts.isPropertyAssignment(parent)) {
      return parent.name.getText(sourceFile);
    }
    if (ts.isBinaryExpression(parent)
        && parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      return parent.left.getText(sourceFile);
    }
  }
  return undefined;
}

function isSyntheticName(name) {
  return name === "" || name === undefined
    || (typeof name === "string" && /^func_\d+$/.test(name));
}

function isBareArrowParameter(node, parameter, sourceFile) {
  if (!ts.isArrowFunction(node)
      || node.parameters.length !== 1
      || node.parameters[0] !== parameter
      || !ts.isIdentifier(parameter.name)) {
    return false;
  }
  return !node.getChildren(sourceFile).some(
    child => child.kind === ts.SyntaxKind.OpenParenToken,
  );
}

function restType(typeText) {
  const value = typeText.trim();
  if (value.endsWith("[]")
      || /^(?:Readonly)?Array\s*</.test(value)
      || value.startsWith("[")) {
    return value;
  }
  return "any[]";
}

function makeEdit(target, relativeFile, start, end, replacement, slot, extra = {}) {
  return {
    file: relativeFile,
    start,
    end,
    replacement,
    target_id: target.id,
    slot,
    ...extra,
  };
}

function editsOverlap(left, right) {
  if (left.file !== right.file) return false;
  if (left.start === left.end && right.start === right.end) {
    return left.start === right.start;
  }
  return Math.max(left.start, right.start) < Math.min(left.end, right.end)
    || (left.start === left.end && left.start > right.start && left.start < right.end)
    || (right.start === right.end && right.start > left.start && right.start < left.end);
}

function indexFunctions(sourceFile) {
  const byStart = new Map();
  function visit(node) {
    if (ts.isFunctionLike(node) && node.body) {
      const start = node.getStart(sourceFile);
      const candidates = byStart.get(start) || [];
      candidates.push(node);
      byStart.set(start, candidates);
    }
    ts.forEachChild(node, visit);
  }
  visit(sourceFile);
  return byStart;
}

function locateTarget(target, sourceFile, functionsByStart, relativeFile) {
  const line = target.position && target.position.start && target.position.start.line;
  const character = target.position && target.position.start
    && target.position.start.character;
  if (!Number.isInteger(line) || line < 1
      || !Number.isInteger(character) || character < 1) {
    return { skipped: { id: target.id, file: relativeFile, reason: "invalid-position" } };
  }

  let requestedStart;
  try {
    requestedStart = sourceFile.getPositionOfLineAndCharacter(line - 1, character - 1);
  } catch (error) {
    return {
      skipped: {
        id: target.id,
        file: relativeFile,
        line,
        character,
        reason: "position-out-of-range",
      },
    };
  }

  const candidates = functionsByStart.get(requestedStart) || [];
  if (candidates.length === 0) {
    return {
      skipped: {
        id: target.id,
        file: relativeFile,
        line,
        character,
        reason: "position-mismatch",
      },
    };
  }

  if (candidates.length !== 1) {
    return {
      skipped: {
        id: target.id,
        file: relativeFile,
        line,
        character,
        reason: "ambiguous-position",
        expected_name: target.name,
      },
    };
  }
  const node = candidates[0];
  const actualName = nodeName(node, sourceFile);
  const notes = [];
  if (!isSyntheticName(target.name) && actualName !== target.name) {
    notes.push({
      reason: "name-mismatch-position-used",
      expected_name: target.name,
      actual_name: actualName,
    });
  }
  return { node, notes };
}

function buildTargetEdits(target, node, sourceFile, relativeFile, locationNotes = []) {
  const edits = [];
  const notes = [...locationNotes];
  const parameterTypes = Array.isArray(target.parameter_types)
    ? target.parameter_types : [];

  node.parameters.forEach((parameter, index) => {
    if (parameter.type) {
      notes.push({ slot: "parameter", index, reason: "already-typed" });
      return;
    }
    let typeText = typeof parameterTypes[index] === "string"
      ? parameterTypes[index].trim() : "any";
    if (!validType(typeText)) {
      typeText = parameter.dotDotDotToken ? "any[]" : "any";
      notes.push({
        slot: "parameter",
        index,
        reason: "invalid-type-fallback",
        fallback: typeText,
      });
    } else if (parameter.dotDotDotToken) {
      const normalized = restType(typeText);
      if (normalized !== typeText) {
        notes.push({
          slot: "parameter",
          index,
          reason: "invalid-rest-type-fallback",
          fallback: normalized,
        });
      }
      typeText = normalized;
    }

    if (isBareArrowParameter(node, parameter, sourceFile)) {
      edits.push(makeEdit(
        target,
        relativeFile,
        parameter.name.getStart(sourceFile),
        parameter.name.getEnd(),
        `(${parameter.name.getText(sourceFile)}: ${typeText})`,
        "parameter",
        { parameter_index: index },
      ));
      return;
    }

    const insertion = parameter.questionToken
      ? parameter.questionToken.getEnd()
      : parameter.name.getEnd();
    edits.push(makeEdit(
      target,
      relativeFile,
      insertion,
      insertion,
      `: ${typeText}`,
      "parameter",
      { parameter_index: index },
    ));
  });

  let returnType = typeof target.return_type === "string"
    ? target.return_type.trim() : "";
  if (ts.isConstructorDeclaration(node) || ts.isSetAccessorDeclaration(node)) {
    notes.push({ slot: "return", reason: "return-type-not-supported" });
  } else if (node.type) {
    notes.push({ slot: "return", reason: "already-typed" });
  } else {
    if (!validType(returnType)) {
      returnType = "any";
      notes.push({
        slot: "return",
        reason: "invalid-type-fallback",
        fallback: returnType,
      });
    }
    const isAsync = Array.isArray(node.modifiers)
      && node.modifiers.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword);
    if (isAsync && !/^Promise\s*<[\s\S]+>$/.test(returnType)) {
      returnType = returnType === "Promise"
        ? "Promise<any>"
        : `Promise<${returnType}>`;
      notes.push({
        slot: "return",
        reason: "async-return-wrapped",
        normalized: returnType,
      });
    }
    const insertion = ts.isArrowFunction(node)
      ? node.equalsGreaterThanToken.getStart(sourceFile)
      : node.body.getStart(sourceFile);
    edits.push(makeEdit(
      target,
      relativeFile,
      insertion,
      insertion,
      `: ${returnType} `,
      "return",
    ));
  }

  if (parameterTypes.length !== node.parameters.length) {
    notes.push({
      slot: "parameters",
      reason: "parameter-count-mismatch",
      source_count: node.parameters.length,
      inferred_count: parameterTypes.length,
    });
  }
  return { edits, notes };
}

function main(payload) {
  const sourceRootInput = payload && payload.source_root;
  if (typeof sourceRootInput !== "string") {
    throw new Error("source_root must be a path string");
  }
  const sourceRoot = fs.realpathSync(sourceRootInput);
  const targets = Array.isArray(payload.targets) ? payload.targets : [];
  const byFile = new Map();
  const skipped = [];

  for (const target of targets) {
    if (!target || !Number.isInteger(target.id) || typeof target.file !== "string") {
      skipped.push({ id: target && target.id, reason: "invalid-target" });
      continue;
    }
    let sourceFile;
    try {
      sourceFile = fs.realpathSync(target.file);
    } catch (error) {
      skipped.push({ id: target.id, file: target.file, reason: "missing-file" });
      continue;
    }
    if (!isInside(sourceRoot, sourceFile)) {
      skipped.push({ id: target.id, file: target.file, reason: "file-outside-source-root" });
      continue;
    }
    const relativeFile = path.relative(sourceRoot, sourceFile);
    const entries = byFile.get(sourceFile) || { relativeFile, targets: [] };
    entries.targets.push(target);
    byFile.set(sourceFile, entries);
  }

  const edits = [];
  const targetReports = [];
  for (const [absoluteFile, entry] of [...byFile.entries()]
      .sort((left, right) => left[1].relativeFile.localeCompare(right[1].relativeFile))) {
    const source = fs.readFileSync(absoluteFile, "utf8");
    const sourceFile = ts.createSourceFile(
      absoluteFile,
      source,
      ts.ScriptTarget.Latest,
      true,
      scriptKind(absoluteFile),
    );
    const functionsByStart = indexFunctions(sourceFile);

    for (const target of entry.targets.sort((left, right) => left.id - right.id)) {
      const located = locateTarget(target, sourceFile, functionsByStart, entry.relativeFile);
      if (located.skipped) {
        skipped.push(located.skipped);
        targetReports.push({ ...located.skipped, status: "skipped", edit_count: 0 });
        continue;
      }

      const built = buildTargetEdits(
        target,
        located.node,
        sourceFile,
        entry.relativeFile,
        located.notes,
      );
      const conflict = built.edits.find(edit => edits.some(existing => editsOverlap(edit, existing)));
      if (conflict) {
        const item = {
          id: target.id,
          file: entry.relativeFile,
          reason: "overlapping-edit",
        };
        skipped.push(item);
        targetReports.push({ ...item, status: "skipped", edit_count: 0 });
        continue;
      }
      edits.push(...built.edits);
      targetReports.push({
        id: target.id,
        file: entry.relativeFile,
        status: built.edits.length > 0 ? "woven" : "located-no-edits",
        edit_count: built.edits.length,
        notes: built.notes,
      });
    }
  }

  edits.sort((left, right) => left.file.localeCompare(right.file)
    || left.start - right.start || left.end - right.end || left.slot.localeCompare(right.slot));
  skipped.sort((left, right) => String(left.file || "").localeCompare(String(right.file || ""))
    || Number(left.id || 0) - Number(right.id || 0));
  return {
    schema_version: 1,
    targets: targets.length,
    located_targets: targetReports.filter(item => item.status !== "skipped").length,
    woven_targets: targetReports.filter(item => item.status === "woven").length,
    edits,
    skipped,
    target_reports: targetReports,
  };
}

let input = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", chunk => { input += chunk; });
process.stdin.on("end", () => {
  try {
    const payload = JSON.parse(input || "{}");
    process.stdout.write(`${JSON.stringify(main(payload))}\n`);
  } catch (error) {
    process.stderr.write(`${error && error.stack ? error.stack : error}\n`);
    process.exitCode = 1;
  }
});
