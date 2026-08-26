// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Basis Research
//
// opencode plugin for the Verus verification-telemetry system (Component 2).
//
// Three jobs, mirroring the Claude Code hooks:
//   * session start -> fail-closed HARD GATE. Probe the Verus MCP `version`
//     tool; if the server is missing or unhealthy, abort the session with a
//     message that the Verus MCP server is required.
//   * tool execute  -> BRANCH GUARD. Check bash commands against the repo's
//     branch discipline (initials-prefixed branches, no direct commits/pushes
//     to main; see CLAUDE.md / AGENTS.md) and block violations, like the
//     Claude Code PreToolUse hook.
//   * session end   -> fail-soft CAPTURE. Read the session from the opencode
//     SQLite store, map it to the shared envelope, and POST it.
//
// Both jobs delegate to committed Python (stdlib only) so the mapping/merge
// logic is shared with the other adapters. The plugin resolves the repo root
// from the session directory and runs the scripts from the checked-out toyDB.

import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
// .opencode/plugin/ -> repo root is two levels up.
const REPO_ROOT = join(HERE, "..", "..");
const PKG_DIR = join(REPO_ROOT, ".claude", "hooks");
const RUNNER = join(REPO_ROOT, ".opencode", "plugin", "verus_runner.py");
const BRANCH_GUARD = join(PKG_DIR, "branch_guard.py");

function runPython(args, extraEnv) {
  const env = { ...process.env, PYTHONPATH: PKG_DIR, ...(extraEnv || {}) };
  return spawnSync("python3", [RUNNER, ...args], {
    env,
    encoding: "utf-8",
    timeout: 60000,
  });
}

export const VerusTelemetry = async ({ project, directory }) => {
  return {
    // ---- Hard gate at session start -------------------------------------
    "session.start": async () => {
      if (!existsSync(RUNNER)) return;
      const res = runPython(["gate"]);
      const healthy = res.status === 0;
      if (!healthy) {
        const reason = (res.stdout || res.stderr || "probe failed").trim();
        // Fail closed: abort the session.
        throw new Error(
          "Verus MCP server is required to work on toyDB. The verus-tools-mcp " +
            "server did not respond to a `version` probe, so this session is " +
            "blocked (fail-closed gate). Ensure verus-tools-mcp is installed and " +
            "the committed opencode `mcp` config registers it. Reason: " +
            reason
        );
      }
    },

    // ---- Branch-discipline guard on bash commands -----------------------
    // Same policy and same guard script as the Claude Code PreToolUse hook.
    // Exit 2 => violation (throw blocks the call, message reaches the agent);
    // anything else fails open so the guard never bricks the bash tool.
    "tool.execute.before": async (input, output) => {
      if (!input || input.tool !== "bash") return;
      const cmd = output && output.args && output.args.command;
      if (!cmd || !existsSync(BRANCH_GUARD)) return;
      const res = spawnSync(
        "python3",
        [BRANCH_GUARD, "check", "--command", String(cmd)],
        { encoding: "utf-8", timeout: 10000 }
      );
      if (res.status === 2) {
        throw new Error(
          (res.stderr || "").trim() || "blocked by branch guard"
        );
      }
    },

    // ---- Fail-soft capture at session end -------------------------------
    "session.end": async (input) => {
      if (!existsSync(RUNNER)) return;
      const sessionId =
        (input && (input.sessionID || input.sessionId || input.id)) || "";
      const args = ["capture"];
      if (sessionId) args.push(sessionId);
      if (directory) args.push("--directory", directory);
      try {
        runPython(args);
      } catch (_err) {
        // Never break the user's session on a telemetry error.
      }
    },
  };
};

export default VerusTelemetry;
