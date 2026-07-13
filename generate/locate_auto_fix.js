#!/usr/bin/env node
"use strict";

const fs = require("fs");
const path = require("path");
const ts = require("typescript");

function findAncestor(node, predicate) {
  for (let current = node; current; current = current.parent) {
    if (predicate(current)) return current;
  }
  return undefined;
}

function isSupportedDeclaration(node) {
  return ts.isParameter(node)
    || ts.isVariableDeclaration(node)
    || ts.isPropertyDeclaration(node)
    || ts.isPropertySignature(node)
    || ts.isBindingElement(node);
}

function bindingOwner(node) {
  let current = node;
  while (current && !ts.isParameter(current) && !ts.isVariableDeclaration(current)) {
    current = current.parent;
  }
  return current;
}

function leftmostIdentifier(expression) {
  let current = expression;
  while (current) {
    if (ts.isIdentifier(current)) return current;
    if (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) {
      current = current.expression;
      continue;
    }
    if (ts.isParenthesizedExpression(current)
        || ts.isAsExpression(current)
        || ts.isTypeAssertionExpression(current)
        || ts.isNonNullExpression(current)) {
      current = current.expression;
      continue;
    }
    return undefined;
  }
  return undefined;
}

function symbolIdentifier(expression, token) {
  if (ts.isIdentifier(expression)) return expression;
  if (ts.isPropertyAccessExpression(expression)) return expression.name;
  return ts.isIdentifier(token) ? token : undefined;
}

function isForInOrOfDeclaration(declaration) {
  return ts.isVariableDeclaration(declaration)
    && declaration.parent
    && declaration.parent.parent
    && (ts.isForOfStatement(declaration.parent.parent)
      || ts.isForInStatement(declaration.parent.parent));
}

function isBareArrowParameter(parameter, sourceFile) {
  if (!ts.isArrowFunction(parameter.parent)
      || parameter.parent.parameters.length !== 1
      || !ts.isIdentifier(parameter.name)) {
    return false;
  }
  return !parameter.parent.getChildren(sourceFile).some(
    child => child.kind === ts.SyntaxKind.OpenParenToken,
  );
}

function main(payload) {
  const rootFiles = [...new Set((payload.files || []).map(file => path.resolve(file)))].sort();
  const editableFiles = new Set(rootFiles);
  const program = ts.createProgram(rootFiles, {
    target: ts.ScriptTarget.ES2021,
    module: ts.ModuleKind.ES2015,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    jsx: ts.JsxEmit.Preserve,
    skipLibCheck: true,
    noEmit: true,
  });
  const checker = program.getTypeChecker();
  const edits = [];
  const skipped = [];
  const editKeys = new Set();

  function editableSource(node) {
    return node && editableFiles.has(path.resolve(node.getSourceFile().fileName));
  }

  function declarationForIdentifier(identifier) {
    let symbol = checker.getSymbolAtLocation(identifier);
    if (!symbol || (symbol.flags & ts.SymbolFlags.Alias)) return undefined;
    const declarations = [symbol.valueDeclaration, ...(symbol.declarations || [])]
      .filter(Boolean);
    return declarations.find(declaration =>
      isSupportedDeclaration(declaration) && editableSource(declaration));
  }

  function makeEdit(file, start, end, replacement, diagnostic, kind, target) {
    const edit = {
      file: path.resolve(file),
      start,
      end,
      replacement,
      code: diagnostic.code,
      kind,
      target,
    };
    const key = `${edit.file}:${start}:${end}:${replacement}`;
    // Repeated diagnostics for one declaration share an edit and are handled,
    // rather than being reported as unsafe skips.
    if (editKeys.has(key)) return edit;
    if (edits.some(existing => existing.file === edit.file
        && Math.max(existing.start, start) < Math.min(existing.end, end))) {
      return undefined;
    }
    editKeys.add(key);
    edits.push(edit);
    return edit;
  }

  function editDeclaration(declaration, diagnostic, allowInsertion) {
    const owner = ts.isBindingElement(declaration) ? bindingOwner(declaration) : declaration;
    if (!owner || !editableSource(owner)) return undefined;
    if (owner.type) {
      return makeEdit(
        owner.getSourceFile().fileName,
        owner.type.getStart(owner.getSourceFile()),
        owner.type.getEnd(),
        "any",
        diagnostic,
        "replace-type",
        owner.name ? owner.name.getText(owner.getSourceFile()) : "return",
      );
    }
    if (!allowInsertion || isForInOrOfDeclaration(owner) || !owner.name) {
      return undefined;
    }

    const sourceFile = owner.getSourceFile();
    const replacementType = ts.isParameter(owner) && owner.dotDotDotToken
      ? "any[]"
      : "any";
    if (ts.isParameter(owner) && isBareArrowParameter(owner, sourceFile)) {
      return makeEdit(
        sourceFile.fileName,
        owner.name.getStart(sourceFile),
        owner.name.getEnd(),
        `(${owner.name.getText(sourceFile)}: ${replacementType})`,
        diagnostic,
        "annotate-bare-arrow-parameter",
        owner.name.getText(sourceFile),
      );
    }
    const annotationStart = owner.questionToken
      ? owner.questionToken.getEnd()
      : owner.exclamationToken
        ? owner.exclamationToken.getEnd()
        : owner.name.getEnd();
    return makeEdit(
      sourceFile.fileName,
      annotationStart,
      annotationStart,
      `: ${replacementType}`,
      diagnostic,
      "insert-type",
      owner.name.getText(sourceFile),
    );
  }

  function editIdentifier(identifier, diagnostic, allowInsertion = true) {
    if (!identifier) return undefined;
    const declaration = declarationForIdentifier(identifier);
    return declaration
      ? editDeclaration(declaration, diagnostic, allowInsertion)
      : undefined;
  }

  function editAssignmentMismatch(token, diagnostic) {
    for (let current = token; current; current = current.parent) {
      if (isSupportedDeclaration(current) && current.type) {
        return editDeclaration(current, diagnostic, false);
      }
      if (ts.isFunctionLike(current) && current.type) {
        return makeEdit(
          current.getSourceFile().fileName,
          current.type.getStart(current.getSourceFile()),
          current.type.getEnd(),
          "any",
          diagnostic,
          "replace-return-type",
          current.name ? current.name.getText(current.getSourceFile()) : "return",
        );
      }
      if (ts.isReturnStatement(current)) {
        const callable = findAncestor(current.parent, ts.isFunctionLike);
        if (callable && callable.type) {
          return makeEdit(
            callable.getSourceFile().fileName,
            callable.type.getStart(callable.getSourceFile()),
            callable.type.getEnd(),
            "any",
            diagnostic,
            "replace-return-type",
            callable.name ? callable.name.getText(callable.getSourceFile()) : "return",
          );
        }
      }
      if (ts.isBinaryExpression(current)
          && current.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        return editIdentifier(leftmostIdentifier(current.left), diagnostic, false);
      }
    }
    return undefined;
  }

  function locateEdit(sourceFile, token, diagnostic) {
    if (diagnostic.code === 7006) {
      const parameter = findAncestor(token, ts.isParameter);
      if (!parameter || !parameter.name
          || !(parameter.name.pos <= token.pos && token.end <= parameter.name.end)) {
        return undefined;
      }
      return editDeclaration(parameter, diagnostic, true);
    }

    if (diagnostic.code === 2322) {
      return editAssignmentMismatch(token, diagnostic);
    }

    if (diagnostic.code === 2339) {
      const access = findAncestor(token, ts.isPropertyAccessExpression);
      return access
        ? editIdentifier(leftmostIdentifier(access.expression), diagnostic)
        : undefined;
    }

    if (diagnostic.code === 2358) {
      const binary = findAncestor(token, node =>
        ts.isBinaryExpression(node)
        && node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword);
      return binary
        ? editIdentifier(leftmostIdentifier(binary.left), diagnostic)
        : undefined;
    }

    if (diagnostic.code === 2538) {
      const access = findAncestor(token, ts.isElementAccessExpression);
      return access
        ? editIdentifier(symbolIdentifier(access.argumentExpression, token), diagnostic)
        : undefined;
    }

    if (diagnostic.code === 2571) {
      return editIdentifier(ts.isIdentifier(token) ? token : undefined, diagnostic);
    }

    return undefined;
  }

  const diagnostics = [...(payload.diagnostics || [])].sort((left, right) =>
    String(left.file).localeCompare(String(right.file))
    || left.line - right.line
    || left.col - right.col
    || left.code - right.code);
  for (const diagnostic of diagnostics) {
    const absoluteFile = path.resolve(diagnostic.file);
    const sourceFile = program.getSourceFile(absoluteFile);
    if (!sourceFile || !editableFiles.has(absoluteFile)) {
      skipped.push({ ...diagnostic, reason: "source file is not editable" });
      continue;
    }
    try {
      const position = sourceFile.getPositionOfLineAndCharacter(
        diagnostic.line - 1,
        diagnostic.col - 1,
      );
      const token = ts.getTokenAtPosition(sourceFile, position);
      if (!locateEdit(sourceFile, token, diagnostic)) {
        skipped.push({ ...diagnostic, reason: "no safe declaration type target" });
      }
    } catch (error) {
      skipped.push({ ...diagnostic, reason: String(error) });
    }
  }

  edits.sort((left, right) =>
    left.file.localeCompare(right.file) || left.start - right.start || left.end - right.end);
  return { edits, skipped };
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
