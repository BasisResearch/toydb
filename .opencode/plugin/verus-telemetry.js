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
//   * `tool.execute.before` — BRANCH GUARD. Check bash commands against the
//     repo's branch discipline (initials-prefixed branches, no direct
//     commits/pushes to main; see CLAUDE.md / AGENTS.md), like the Claude
//     Code PreToolUse hook.
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

// session.idle fires after every turn, so a synchronous capture would block the
// event loop on each one while the ingest endpoint responds. Coalesce bursts
// per session behind a short debounce, then fire the capture as a detached,
// non-blocking child. Capture is idempotent (upsert by session_id), so
// dropping intermediate idles loses nothing.
const CAPTURE_DEBOUNCE_MS = 2000;
const CAPTURE_TIMEOUT_MS = 60000;
const captureTimers = new Map();

function runPython(args, extraEnv) {
  const env = { ...process.env, PYTHONPATH: PKG_DIR, ...(extraEnv || {}) };
  return spawnSync("python3", [RUNNER, ...args], {
    env,
    encoding: "utf-8",
    timeout: CAPTURE_TIMEOUT_MS,
  });
}

// Fire-and-forget capture: spawn asynchronously, ignore all stdio, and unref so
// the child never keeps opencode alive or blocks its event loop. A self-kill
// timer bounds a hung upload; every failure path is swallowed.
function spawnCapture(args) {
  try {
    const child = spawn("python3", [RUNNER, ...args], {
      env: { ...process.env, PYTHONPATH: PKG_DIR },
      stdio: "ignore",
    });
    child.on("error", () => {});
    const killer = setTimeout(() => {
      try {
        child.kill();
      } catch (_err) {
        // already gone
      }
    }, CAPTURE_TIMEOUT_MS);
    if (typeof killer.unref === "function") killer.unref();
    child.on("exit", () => clearTimeout(killer));
    child.unref();
  } catch (_err) {
    // Never break the user's session on a telemetry error.
  }
}

function scheduleCapture(sessionId, directory) {
  const key = sessionId || "";
  const existing = captureTimers.get(key);
  if (existing) clearTimeout(existing);
  const timer = setTimeout(() => {
    captureTimers.delete(key);
    const args = ["capture"];
    if (sessionId) args.push(sessionId);
    if (directory) args.push("--directory", directory);
    spawnCapture(args);
  }, CAPTURE_DEBOUNCE_MS);
  if (typeof timer.unref === "function") timer.unref();
  captureTimers.set(key, timer);
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
          scheduleCapture(sessionId, directory);
        }
      } catch (_err) {
        // Never break the user's session on a telemetry error.
      }
    },
  };
};

export default VerusTelemetry;
