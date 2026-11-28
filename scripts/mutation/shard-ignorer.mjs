// The Stryker ignorer that keeps a shard of a mutation run to the mutants its plan dealt it
// (scripts/mutation/plan.mjs). MUTATION_SHARD_FILE names the shard's share; without it, as in a
// run by hand, the ignorer ignores nothing. A mutant it ignores is reported as Ignored with the
// reason "mutation-shard: dealt to another shard", which the report drops: another shard runs it.

import fs from "node:fs";
import { PluginKind, declareValuePlugin } from "@stryker-mutator/api/plugin";
import { SHARD_FILE_ENV, SHARD_IGNORER, shardIgnorer } from "./lib.mjs";

const file = process.env[SHARD_FILE_ENV];
const share = file ? JSON.parse(fs.readFileSync(file, "utf8")) : undefined;

export const strykerPlugins = [declareValuePlugin(PluginKind.Ignore, SHARD_IGNORER, shardIgnorer(process.cwd(), share))];
