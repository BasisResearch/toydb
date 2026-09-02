// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Basis Research
//
// opencode plugin for the Verus verification-telemetry system (Component 2).
//
// opencode's plugin API (as of 1.18.x) has NO `session.start` / `session.end`
// hooks — those keys are silently ignored. The real surface we use:
//   * `event` (generic bus-event handler) —
//       session.created -> gate probe. opencode cannot abort a session from
//       an event handler, so the gate is a LOUD warning (stderr / opencode
//       log), not a hard block; capture keeps gate_violation visible on the
//       dashboard instead.
//       session.idle   -> fail-soft CAPTURE, fired after each turn. The
//       ingest endpoint upserts by session_id, so one upload per idle is
//       idempotent and crash-safe (unlike an end-of-session-only capture).
//   * `tool.execute.before` — BRANCH GUARD + VERUS GUARD. Check bash commands
//     against the repo's branch discipline (initials-prefixed branches, no
//     direct commits/pushes to main) and the "Verus goes through the MCP
//     server, not the shell" rule (see CLAUDE.md / AGENTS.md), like the
//     Claude Code PreToolUse hooks.
//
// Both jobs delegate to committed Python (stdlib only) so the mapping/merge
// logic is shared with the other adapters. The plugin resolves the repo root
// from its own location and runs the scripts from the checked-out toyDB.

import { spawn, spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
// .opencode/plugin/ -> repo root is two levels up.
const REPO_ROOT = join(HERE, "..", "..");
const PKG_DIR = join(REPO_ROOT, ".claude", "hooks");
const RUNNER = join(REPO_ROOT, ".opencode", "plugin", "verus_runner.py");
const BRANCH_GUARD = join(PKG_DIR, "branch_guard.py");
const VERUS_CLI_GUARD = join(PKG_DIR, "verus_cli_guard.py");

function runPython(args, extraEnv) {
  const env = { ...process.env, PYTHONPATH: PKG_DIR, ...(extraEnv || {}) };
  return spawnSync("python3", [RUNNER, ...args], {
    env,
    encoding: "utf-8",
    timeout: 60000,
  });
}

// Fire-and-forget variant. `session.idle` fires after EVERY turn, and the
// capture reads SQLite, probes the MCP server and POSTs to the ingest
// endpoint — up to the 60 s timeout. Doing that with spawnSync would block
// Node's event loop, freezing opencode and starving every other plugin's
// event subscribers for the duration. Nothing consumes the result, so detach.
function runPythonDetached(args, extraEnv) {
  const env = { ...process.env, PYTHONPATH: PKG_DIR, ...(extraEnv || {}) };
  const child = spawn("python3", [RUNNER, ...args], {
    env,
    detached: true,
    stdio: "ignore",
  });
  child.on("error", () => {});
  child.unref();
}

export const VerusTelemetry = async ({ project, directory }) => {
  return {
    // ---- Branch-discipline guard on bash commands -----------------------
    // Same policy and same guard script as the Claude Code PreToolUse hook.
    // Exit 2 => violation (throw blocks the call, message reaches the agent);
    // anything else fails open so the guard never bricks the bash tool.
    "tool.execute.before": async (input, output) => {
      if (!input || input.tool !== "bash") return;
      const cmd = output && output.args && output.args.command;
      if (!cmd) return;
      // Each guard is gated on ITS OWN presence. Sharing one existence check
      // meant deleting or renaming branch_guard.py silently switched off
      // Verus CLI enforcement as well.
      const guards = [
        [BRANCH_GUARD, "blocked by branch guard"],
        [VERUS_CLI_GUARD, "blocked by verus guard"],
      ];
      for (const [guard, fallback] of guards) {
        if (!existsSync(guard)) continue;
        const res = spawnSync(
          "python3",
          [guard, "check", "--command", String(cmd)],
          { encoding: "utf-8", timeout: 10000 }
        );
        if (res.status === 2) {
          throw new Error((res.stderr || "").trim() || fallback);
        }
      }
    },

    // ---- Gate (session.created) + capture (session.idle) ----------------
    // Delivered through the generic `event` hook: opencode has no dedicated
    // session-start/session-end plugin hooks. Always fail-soft — a telemetry
    // error must never break the user's session or other event subscribers.
    event: async ({ event }) => {
      if (!event || !existsSync(RUNNER)) return;
      try {
        if (event.type === "session.created") {
          const res = runPython(["gate"]);
          if (res.status !== 0) {
            const reason = (res.stdout || res.stderr || "probe failed").trim();
            console.error(
              "[verus-gate] Verus MCP server is required to work on toyDB, " +
                "but the `version` probe failed. This session is UNGATED and " +
                "will be recorded with gate_violation on the dashboard. " +
                "Reason: " + reason
            );
          }
        }
        if (event.type === "session.idle") {
          const sessionId =
            event.properties && event.properties.sessionID;
          const args = ["capture"];
          if (sessionId) args.push(sessionId);
          if (directory) args.push("--directory", directory);
          runPythonDetached(args);
        }
      } catch (_err) {
        // Never break the user's session on a telemetry error.
      }
    },
  };
};

export default VerusTelemetry;
