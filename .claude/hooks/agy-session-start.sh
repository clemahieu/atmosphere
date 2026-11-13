#!/usr/bin/env bash
# SPDX-License-Identifier: MIT

# SessionStart hook for agy: inject the untracked project-root CLAUDE.md beside
# the worktrees when present (since agy loads AGENTS.md inside the worktree and
# does not walk into the parent directory), and inject the commit attribution
# trailer for Gemini sessions (Co-Authored-By: <model> <noreply@google.com>),
# since agy emits no trailer of its own. ATMO_SESSION_START_ROOT overrides the
# parent directory in tests.
set -u

if [ "${ATMO_SESSION_START_ROOT+set}" = set ]; then
  root=$ATMO_SESSION_START_ROOT
else
  top=$(git rev-parse --show-toplevel 2>/dev/null || true)
  root=${top:+$(dirname "$top")}
fi

jq_prog='
  def gemini_model:
    (.modelName // "") as $raw
    | if ($raw | test("^(?i)(gemini|orchestrator)")) then
        ($raw
         | sub(" \\([^)]*\\)$"; "")
         | sub("-(low|medium|high|xhigh|max)$"; ""; "i")) as $base
        | if ($raw | test("^(?i)(gemini-pro-orchestrator-argon|orchestrator \\(argon\\))")) then
            "Gemini 4 Argon"
          elif ($raw | test("^(?i)(gemini-pro-orchestrator|orchestrator)")) then
            "Gemini 4 Carbon"
          elif ($base | contains(" ")) then
            $base
          else
            $base
            | split("-")
            | map(if test("^[a-zA-Z]") then (.[0:1] | ascii_upcase) + (.[1:] | ascii_downcase) else . end)
            | join(" ")
          end
      else null end;

  (try fromjson catch {}) as $in
  | (if ($in | type) == "object" then $in else {} end) as $obj
  | ($obj.modelName // "") as $raw
  | ($obj | gemini_model) as $model
  | (if $model != null then
       "The commit trailer this harness asks for is Co-Authored-By: \($model) <noreply@google.com> (if Model Selection changes during the session, use the active Gemini model'\''s human-readable name without its effort suffix)."
     elif ($raw == "" or ($raw | test("^(?i)(auto|none)$"))) then
       "When committing with git on a Gemini model, the commit trailer this harness asks for is Co-Authored-By: <model> <noreply@google.com>, where <model> is the active model'\''s human-readable name without its effort suffix (for example, Gemini 4 Carbon)."
     else null end) as $trailer
  | [
      (if $has_rules then {systemMessage: {systemMessage: $rules}} else empty end),
      (if $trailer != null then {systemMessage: {systemMessage: $trailer}} else empty end)
    ] as $steps
  | if ($steps | length) > 0 then {injectSteps: $steps} else {} end
'

if [ -n "$root" ] && [ -f "$root/CLAUDE.md" ]; then
  jq -cRs --argjson has_rules true --rawfile rules "$root/CLAUDE.md" "$jq_prog"
else
  jq -cRs --argjson has_rules false --arg rules "" "$jq_prog"
fi
