import * as path from "path";
import { Command } from "commander";
import { eraseTypeScript } from "./src/migration/ts";

const program = new Command()
  .requiredOption("-i, --input <directory>", "TypeScript source directory")
  .option("-o, --output <directory>", "erased project output", "./erased");

program.parse(process.argv);
const options = program.opts();
const output = path.resolve(options.output);
const result = eraseTypeScript(path.resolve(options.input), output);

console.log(`Done. Processed ${result.files} files.`);
console.log(`  Extracted ${result.annotations} type annotations from ${result.annotatedFiles} files.`);
console.log(`  Erased source -> ${output}`);
console.log(`  Ground truth  -> ${path.join(output, "_groundtruth.json")}`);
