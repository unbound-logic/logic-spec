// The test command of a mutation run (stryker.config.json): every test file, one after another,
// the slowest last, stopping at the first that fails. A mutant some test catches stops there
// rather than waiting for the slowest files; one that no test catches runs every file, as
// `npm test` does. Each file runs in `node --test`, as in `npm test`; a new test file joins the run
// by itself. With --times=FILE, it writes each file's time to FILE.

import { spawnSync } from "node:child_process";
import fs from "node:fs";

// The slowest files, in this order at the end: differential alone takes about as long as all the
// others together, and property-fuzz is the next slowest.
const LAST = ["test/property-fuzz.test.ts", "test/differential.test.ts"];

const files = fs
  .readdirSync("test")
  .filter((f) => f.endsWith(".test.ts"))
  .map((f) => `test/${f}`)
  .sort();
const order = [...files.filter((f) => !LAST.includes(f)), ...LAST.filter((f) => files.includes(f))];
const times = process.argv.find((a) => a.startsWith("--times="))?.slice("--times=".length);
if (times) fs.writeFileSync(times, "");

for (const file of order) {
  const start = process.hrtime.bigint();
  const result = spawnSync(process.execPath, ["--test", file], { stdio: "inherit" });
  if (times) fs.appendFileSync(times, `${(Number(process.hrtime.bigint() - start) / 1e9).toFixed(1).padStart(7)} s  ${file}\n`);
  if (result.status !== 0) process.exit(result.status ?? 1);
}
