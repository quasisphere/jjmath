#!/usr/bin/env node

/**
 * Static validator for Handwave articles and Lean docstrings.
 *
 * This deliberately uses only Node built-ins and repository source files. It
 * does not invoke Lean and does not inspect generated Handwave artifacts.
 */

import fs from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";

const SCRIPT_DIR = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(SCRIPT_DIR, "..");
const REQUIRED_THEOREM_FIELDS = ["name", "statement", "proof"];

function usage() {
  return `Usage: node tools/validate-handwave.mjs [options]

Statically validate Handwave includes against declarations in JJMath/**/*.lean.

Options:
  --json                 Emit machine-readable JSON.
  --article PATH         Check one article (repeatable). PATH may be repository-
                         relative, relative to handwave/, or absolute.
  --prefix PREFIX        Check articles whose repository-relative paths begin
                         with PREFIX (repeatable).
  --strict-external      Report targets absent from JJMath/**/*.lean even when
                         they do not begin with JJMath. By default such targets
                         are listed as unchecked external references.
  -h, --help             Show this help.
`;
}

function parseArgs(argv) {
  const options = {
    json: false,
    strictExternal: false,
    articles: [],
    prefixes: [],
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--json") {
      options.json = true;
    } else if (arg === "--strict-external") {
      options.strictExternal = true;
    } else if (arg === "-h" || arg === "--help") {
      options.help = true;
    } else if (arg === "--article" || arg === "--prefix") {
      if (i + 1 >= argv.length) {
        throw new Error(`${arg} requires a value`);
      }
      const value = argv[++i];
      if (arg === "--article") options.articles.push(value);
      else options.prefixes.push(value);
    } else if (arg.startsWith("--article=")) {
      options.articles.push(arg.slice("--article=".length));
    } else if (arg.startsWith("--prefix=")) {
      options.prefixes.push(arg.slice("--prefix=".length));
    } else {
      throw new Error(`unknown option: ${arg}`);
    }
  }

  return options;
}

async function walkFiles(directory, predicate) {
  const result = [];
  const entries = await fs.readdir(directory, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));
  for (const entry of entries) {
    const entryPath = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      result.push(...await walkFiles(entryPath, predicate));
    } else if (entry.isFile() && predicate(entryPath)) {
      result.push(entryPath);
    }
  }
  return result;
}

function repoRelative(filePath) {
  return path.relative(REPO_ROOT, filePath).split(path.sep).join("/");
}

function lineStarts(source) {
  const starts = [0];
  for (let i = 0; i < source.length; i += 1) {
    if (source.charCodeAt(i) === 10) starts.push(i + 1);
  }
  return starts;
}

function positionAt(starts, offset) {
  let low = 0;
  let high = starts.length;
  while (low + 1 < high) {
    const middle = Math.floor((low + high) / 2);
    if (starts[middle] <= offset) low = middle;
    else high = middle;
  }
  return { line: low + 1, column: offset - starts[low] + 1 };
}

/**
 * Replace comments and string/character literals by spaces while preserving
 * newlines and offsets. Also collect doc comments. Lean permits nested block
 * comments, so the small scanner tracks their depth.
 */
function maskLeanSource(source) {
  // split("") preserves JavaScript UTF-16 offsets, unlike code-point
  // iteration; offsets therefore continue to agree with String#slice.
  const chars = source.split("");
  const docComments = [];
  let i = 0;

  const blank = (index) => {
    if (chars[index] !== "\n" && chars[index] !== "\r") chars[index] = " ";
  };

  while (i < source.length) {
    if (source.startsWith("--", i)) {
      while (i < source.length && source[i] !== "\n") blank(i++);
      continue;
    }

    if (source.startsWith("/-", i)) {
      const start = i;
      const isDoc = source.startsWith("/--", i);
      let depth = 0;
      while (i < source.length) {
        if (source.startsWith("/-", i)) {
          depth += 1;
          blank(i++);
          blank(i++);
        } else if (source.startsWith("-/", i)) {
          depth -= 1;
          blank(i++);
          blank(i++);
          if (depth === 0) break;
        } else {
          blank(i++);
        }
      }
      if (isDoc) {
        docComments.push({ start, end: i, text: source.slice(start, i) });
      }
      continue;
    }

    if (source[i] === '"') {
      blank(i++);
      while (i < source.length) {
        if (source[i] === "\\") {
          blank(i++);
          if (i < source.length) blank(i++);
        } else if (source[i] === '"') {
          blank(i++);
          break;
        } else {
          blank(i++);
        }
      }
      continue;
    }

    // Lean character literals are uncommon in declarations but can contain
    // punctuation which resembles a command. Mask only a syntactically small
    // single-quoted literal, leaving identifiers such as f' untouched.
    if (source[i] === "'" && /^(?:'[^'\\\r\n]'|'\\[^\r\n]+?')/.test(source.slice(i))) {
      blank(i++);
      while (i < source.length) {
        if (source[i] === "\\") {
          blank(i++);
          if (i < source.length) blank(i++);
        } else if (source[i] === "'") {
          blank(i++);
          break;
        } else {
          blank(i++);
        }
      }
      continue;
    }

    i += 1;
  }

  return { masked: chars.join(""), docComments };
}

function parseHandwaveFields(docText) {
  if (!docText.includes("%%handwave")) return null;

  const fields = new Map();
  const lines = docText.slice(docText.indexOf("%%handwave") + "%%handwave".length).split(/\r?\n/);
  let current = null;
  for (const line of lines) {
    const match = line.match(/^\s*([A-Za-z][A-Za-z0-9_-]*)\s*:\s*(.*)$/);
    if (match) {
      current = match[1].toLowerCase();
      fields.set(current, match[2]);
    } else if (current !== null) {
      fields.set(current, `${fields.get(current)}\n${line}`);
    }
  }

  return Object.fromEntries([...fields].map(([key, value]) => [key, value.trim()]));
}

function attachedDocComment(source, declarationOffset, docComments) {
  let candidate = null;
  for (const doc of docComments) {
    if (doc.end > declarationOffset) break;
    candidate = doc;
  }
  if (candidate === null) return null;

  // Attributes may sit between a docstring and its declaration. Any other
  // source command means the comment belongs to something earlier.
  const intervening = source.slice(candidate.end, declarationOffset);
  const withoutAttributes = intervening.replace(/@\[[\s\S]*?\]/g, "");
  return withoutAttributes.trim() === "" ? candidate : null;
}

function qualifiedName(namespaceParts, declaredName) {
  let name = declaredName;
  if (name.startsWith("_root_.")) return name.slice("_root_.".length);
  if (name.startsWith("«") && name.endsWith("»")) name = name.slice(1, -1);
  return [...namespaceParts, ...name.split(".")].filter(Boolean).join(".");
}

function parseLeanDeclarations(filePath, source) {
  const { masked, docComments } = maskLeanSource(source);
  const starts = lineStarts(source);
  const declarations = [];
  const context = [];
  const lines = masked.split(/\n/);
  let offset = 0;

  for (const line of lines) {
    const namespaceMatch = line.match(/^\s*namespace(?:\s+([^\s]+))?\s*$/);
    const sectionMatch = line.match(/^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$/);
    const endMatch = line.match(/^\s*end(?:\s+([^\s]+))?\s*$/);

    if (namespaceMatch) {
      let namespaceName = namespaceMatch[1];
      if (namespaceName === undefined) {
        const followingOffset = offset + line.length + 1;
        const following = masked.slice(followingOffset).match(/^\s*([^\s]+)/);
        namespaceName = following?.[1];
      }
      if (namespaceName !== undefined) {
        context.push({ kind: "namespace", name: namespaceName });
      }
    } else if (sectionMatch) {
      context.push({ kind: "section", name: sectionMatch[1] ?? null });
    } else if (endMatch) {
      if (context.length > 0) context.pop();
    } else {
      const declarationMatch = line.match(
        /^\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|unsafe|local)\s+)*)(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)(?:\s+([^\s:{[(]+))?/,
      );
      if (declarationMatch) {
        const modifiers = declarationMatch[1].trim().split(/\s+/).filter(Boolean);
        let declaredName = declarationMatch[3];
        let declarationOffset;
        if (declaredName !== undefined) {
          declarationOffset = offset + line.indexOf(declaredName, declarationMatch.index);
        } else {
          const followingOffset = offset + line.length + 1;
          const following = masked.slice(followingOffset).match(/^\s*([^\s:{[(]+)/);
          if (following !== null) {
            declaredName = following[1];
            declarationOffset = followingOffset + following[0].lastIndexOf(declaredName);
          }
        }
        if (
          declaredName !== undefined
          && !modifiers.includes("private")
          && !modifiers.includes("local")
        ) {
          const namespaceParts = context
            .filter((entry) => entry.kind === "namespace")
            .flatMap((entry) => entry.name.split("."));
          const doc = attachedDocComment(source, offset + line.search(/\S|$/), docComments);
          declarations.push({
            name: qualifiedName(namespaceParts, declaredName),
            kind: declarationMatch[2],
            file: repoRelative(filePath),
            ...positionAt(starts, declarationOffset),
            handwave: doc === null ? null : parseHandwaveFields(doc.text),
          });
        }
      }
    }
    offset += line.length + 1;
  }

  return declarations;
}

function normalizeArticleSelector(value) {
  const absolute = path.isAbsolute(value) ? value : path.resolve(REPO_ROOT, value);
  let relative = repoRelative(absolute);
  if (!relative.startsWith("handwave/") && !relative.startsWith("../")) {
    relative = `handwave/${value.replace(/^\.\//, "")}`;
  }
  return relative.replace(/\/$/, "");
}

function filterArticles(articleFiles, options) {
  if (options.articles.length === 0 && options.prefixes.length === 0) return articleFiles;
  const exact = new Set(options.articles.map(normalizeArticleSelector));
  const prefixes = options.prefixes.map(normalizeArticleSelector);
  return articleFiles.filter((filePath) => {
    const relative = repoRelative(filePath);
    return exact.has(relative) || prefixes.some((prefix) => relative.startsWith(prefix));
  });
}

function parseArticle(filePath, source) {
  const starts = lineStarts(source);
  const validIncludes = [];
  const validStarts = new Set();
  const includePattern = /@include\{lean:([^}\r\n]+)\}/g;
  for (const match of source.matchAll(includePattern)) {
    const target = match[1].trim();
    if (target === "" || /\s/.test(target)) continue;
    validStarts.add(match.index);
    validIncludes.push({
      target,
      offset: match.index,
      ...positionAt(starts, match.index),
    });
  }

  const malformed = [];
  for (const match of source.matchAll(/@include\b/g)) {
    if (!validStarts.has(match.index)) {
      const position = positionAt(starts, match.index);
      const lineEnd = source.indexOf("\n", match.index);
      malformed.push({
        offset: match.index,
        ...position,
        text: source.slice(match.index, lineEnd < 0 ? source.length : lineEnd).trim(),
      });
    }
  }

  return { file: repoRelative(filePath), validIncludes, malformed };
}

function makeIssue(kind, article, include, extra = {}) {
  return {
    kind,
    article: { file: article.file, line: include.line, column: include.column },
    ...extra,
  };
}

async function validate(options) {
  const leanFiles = await walkFiles(path.join(REPO_ROOT, "JJMath"), (file) => file.endsWith(".lean"));
  const declarations = [];
  for (const file of leanFiles) {
    declarations.push(...parseLeanDeclarations(file, await fs.readFile(file, "utf8")));
  }

  const declarationIndex = new Map();
  for (const declaration of declarations) {
    if (!declarationIndex.has(declaration.name)) declarationIndex.set(declaration.name, declaration);
  }
  const localNamespaceRoots = new Set(
    declarations
      .filter((declaration) => declaration.name.includes("."))
      .map((declaration) => declaration.name.split(".")[0]),
  );

  const allArticleFiles = await walkFiles(
    path.join(REPO_ROOT, "handwave"),
    (file) => file.endsWith(".hw") || file.endsWith(".hw.md"),
  );
  const articleFiles = filterArticles(allArticleFiles, options);
  if ((options.articles.length > 0 || options.prefixes.length > 0) && articleFiles.length === 0) {
    throw new Error("no Handwave articles matched the requested path/prefix filters");
  }
  const articles = [];
  for (const file of articleFiles) {
    articles.push(parseArticle(file, await fs.readFile(file, "utf8")));
  }

  const issues = [];
  const uncheckedExternal = [];
  let includeCount = 0;
  for (const article of articles) {
    for (const malformed of article.malformed) {
      issues.push(makeIssue("malformed-include", article, malformed, { text: malformed.text }));
    }
    for (const include of article.validIncludes) {
      includeCount += 1;
      const declaration = declarationIndex.get(include.target);
      if (declaration === undefined) {
        const targetRoot = include.target.split(".")[0];
        if (localNamespaceRoots.has(targetRoot) || options.strictExternal) {
          issues.push(makeIssue("unresolved-include", article, include, { target: include.target }));
        } else {
          uncheckedExternal.push({
            article: { file: article.file, line: include.line, column: include.column },
            target: include.target,
          });
        }
        continue;
      }

      if (declaration.kind === "theorem" || declaration.kind === "lemma") {
        const missingFields = REQUIRED_THEOREM_FIELDS.filter(
          (field) => declaration.handwave?.[field]?.trim() === undefined || declaration.handwave[field].trim() === "",
        );
        if (missingFields.length > 0) {
          issues.push(makeIssue("missing-handwave-fields", article, include, {
            target: include.target,
            declaration: {
              file: declaration.file,
              line: declaration.line,
              column: declaration.column,
              kind: declaration.kind,
            },
            missingFields,
          }));
        }
      }
    }
  }

  return {
    ok: issues.length === 0,
    repository: REPO_ROOT,
    stats: {
      leanFiles: leanFiles.length,
      declarations: declarations.length,
      articles: articles.length,
      includes: includeCount,
      issues: issues.length,
      uncheckedExternal: uncheckedExternal.length,
    },
    issues,
    uncheckedExternal,
  };
}

function humanOutput(result) {
  const lines = [];
  if (result.ok) lines.push("Handwave validation passed.");
  else lines.push(`Handwave validation found ${result.stats.issues} issue(s).`);
  lines.push(
    `Scanned ${result.stats.articles} article(s), ${result.stats.includes} include(s), `
      + `${result.stats.declarations} public declaration(s) in ${result.stats.leanFiles} Lean file(s).`,
  );

  for (const issue of result.issues) {
    const articleLocation = `${issue.article.file}:${issue.article.line}:${issue.article.column}`;
    if (issue.kind === "unresolved-include") {
      lines.push(`\n[unresolved include] ${articleLocation}`);
      lines.push(`  ${issue.target} was not found in JJMath/**/*.lean`);
    } else if (issue.kind === "malformed-include") {
      lines.push(`\n[malformed include] ${articleLocation}`);
      lines.push(`  ${issue.text || "@include"}`);
    } else if (issue.kind === "missing-handwave-fields") {
      lines.push(`\n[missing Handwave metadata] ${articleLocation}`);
      lines.push(`  ${issue.target}`);
      lines.push(
        `  declared at ${issue.declaration.file}:${issue.declaration.line}:${issue.declaration.column}; `
          + `missing ${issue.missingFields.join(", ")}`,
      );
    }
  }

  if (result.uncheckedExternal.length > 0) {
    lines.push(
      `\nSkipped ${result.uncheckedExternal.length} nonlocal include(s) absent from the local source index. `
        + "Use --strict-external to report them as unresolved.",
    );
  }
  return `${lines.join("\n")}\n`;
}

async function main() {
  let options;
  try {
    options = parseArgs(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`validate-handwave: ${error.message}\n\n${usage()}`);
    process.exitCode = 2;
    return;
  }

  if (options.help) {
    process.stdout.write(usage());
    return;
  }

  try {
    const result = await validate(options);
    if (options.json) process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
    else process.stdout.write(humanOutput(result));
    if (!result.ok) process.exitCode = 1;
  } catch (error) {
    process.stderr.write(`validate-handwave: ${error.message}\n`);
    process.exitCode = 2;
  }
}

await main();
