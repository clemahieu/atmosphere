#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Claude's subscription meters: the week, the five-hour window when the plan has one, and each
scoped model limit, read from Claude's usage endpoint and printed as one line of JSON.

`~/.claude.json`'s cachedUsageUtilization is the interactive app's last fetch. A pool of headless
sessions does not fetch it, so that copy stays one reading and a fitted rate never appears. This
asks the endpoint that fetch asks, with the access token headless sessions keep in
`~/.claude/.credentials.json`. It does not refresh that token: rotating the refresh token would
take it from a session that still holds the old one, and a session refreshes the file itself. An
expired token is an error, and the pool keeps the readings it has.

Prints {"read": <epoch seconds>, "meters": [{"meter": "claude-week"|"claude-5h"|"claude-<model>",
"percent": <float>, "resets_at": <epoch seconds|null>}, ...]}.

Exit status: 0 printed; 1 no token, an expired token, a usage reply this does not know, or the
endpoint refusing.

usage: tools/claude-usage.py          (read the meters)
       tools/claude-usage.py --test   (this script's own tests)
"""
import json
import sys
import tempfile
import unittest
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path

USAGE_URL = "https://api.anthropic.com/api/oauth/usage"
BETA = "oauth-2025-04-20"
# Refresh nothing inside this many seconds of expiry: the file's token is the one a session wrote.
FRESH = 300
CREDENTIALS = Path.home() / ".claude" / ".credentials.json"


class Status(Exception):
    """The endpoint answered with an HTTP status and no meter."""

    def __init__(self, status):
        super().__init__(f"HTTP {status}")
        self.status = status


def epoch(stamp):
    """Epoch seconds from an ISO 8601 time, or None for none."""
    return None if stamp is None else datetime.fromisoformat(stamp.replace("Z", "+00:00")).timestamp()


def meters_of(payload):
    """(meter, percent, resets_at) for the week, the five-hour window when present, and each scoped
    model limit. A window the plan does not have is absent. ValueError when the reply names none."""
    found = []
    week, five = payload.get("seven_day"), payload.get("five_hour")
    if isinstance(week, dict) and week.get("utilization") is not None:
        found.append(("claude-week", float(week["utilization"]), epoch(week.get("resets_at"))))
    if isinstance(five, dict) and five.get("utilization") is not None:
        found.append(("claude-5h", float(five["utilization"]), epoch(five.get("resets_at"))))
    for limit in payload.get("limits") or []:
        if not isinstance(limit, dict) or limit.get("kind") != "weekly_scoped" or limit.get("percent") is None:
            continue
        scope = limit.get("scope") if isinstance(limit.get("scope"), dict) else {}
        model = scope.get("model") if isinstance(scope.get("model"), dict) else {}
        name = model.get("display_name")
        if isinstance(name, str) and name:
            found.append((f"claude-{name.lower()}", float(limit["percent"]), epoch(limit.get("resets_at"))))
    if not found:
        raise ValueError("no Claude meter in the usage reply")
    return found


def fresh(oauth, now):
    """Whether `oauth`'s access token is still inside its validity, with FRESH seconds to spare."""
    expires = oauth.get("expiresAt")
    return isinstance(expires, (int, float)) and expires / 1000 - now > FRESH


def collect(path, now, get):
    """The meters at `path`'s access token, read at `now`, through `get(url, token) -> body`.
    ValueError when the token is missing or expired; Status when the endpoint refuses."""
    oauth = json.loads(Path(path).read_text())["claudeAiOauth"]
    token = oauth.get("accessToken")
    if not isinstance(token, str) or not token:
        raise ValueError("no access token")
    if not fresh(oauth, now):
        raise ValueError("access token expired")
    found = meters_of(json.loads(get(USAGE_URL, token)))
    return {"read": now, "meters": [{"meter": meter, "percent": percent, "resets_at": resets}
                                    for meter, percent, resets in found]}


def http_get(url, token):
    """The body `url` returned for `token`, or Status for an HTTP error. The body of an error is
    not kept: it is not a meter."""
    request = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {token}",
        "Accept": "application/json",
        "anthropic-beta": BETA,
        "User-Agent": "atmosphere-loop/claude-usage",
    })
    try:
        with urllib.request.urlopen(request, timeout=30) as reply:
            return reply.read().decode()
    except urllib.error.HTTPError as error:
        raise Status(error.code) from None


PAYLOAD = {
    "five_hour": {"utilization": 10, "resets_at": "2026-11-13T18:00:00+00:00"},
    "seven_day": {"utilization": 13, "resets_at": "2026-11-15T05:00:00+00:00"},
    "seven_day_opus": None,
    "limits": [
        {"kind": "weekly_all", "percent": 13, "resets_at": "2026-11-15T05:00:00+00:00", "scope": None},
        {"kind": "weekly_scoped", "percent": 12, "resets_at": "2026-11-15T05:00:00.486689+00:00",
         "scope": {"model": {"id": None, "display_name": "Fable"}, "surface": None}},
        {"kind": "weekly_scoped", "percent": 1, "resets_at": "2026-11-15T05:00:00+00:00",
         "scope": {"model": None, "surface": "desk"}},
    ],
}


class Tests(unittest.TestCase):
    NOW = datetime(2026, 11, 13, 22, 0).timestamp()

    def test_the_week_the_five_hour_window_and_a_scoped_model_are_meters(self):
        found = dict((meter, (percent, resets)) for meter, percent, resets in meters_of(PAYLOAD))
        self.assertEqual(set(found), {"claude-week", "claude-5h", "claude-fable"})
        self.assertEqual(found["claude-week"][0], 13.0)
        self.assertEqual(found["claude-5h"][0], 10.0)
        self.assertEqual(found["claude-fable"][0], 12.0)
        self.assertEqual(found["claude-week"][1], datetime.fromisoformat("2026-11-15T05:00:00+00:00").timestamp())

    def test_a_plan_without_a_five_hour_window_has_none_and_a_reply_with_no_meter_is_unknown(self):
        payload = {**PAYLOAD, "five_hour": None}
        self.assertNotIn("claude-5h", [meter for meter, _, _ in meters_of(payload)])
        with self.assertRaises(ValueError):
            meters_of({"five_hour": None, "seven_day": None, "limits": []})

    def credentials(self, oauth):
        folder = Path(tempfile.mkdtemp())
        path = folder / "credentials.json"
        path.write_text(json.dumps({"claudeAiOauth": oauth}))

        def remove():
            path.unlink(missing_ok=True)
            folder.rmdir()

        self.addCleanup(remove)
        return path

    def test_a_fresh_token_is_sent_once_and_the_reply_is_the_meters_read_at_now(self):
        path = self.credentials({"accessToken": "tok", "expiresAt": (self.NOW + 3600) * 1000})
        seen = {}

        def get(url, token):
            seen["url"], seen["token"] = url, token
            return json.dumps(PAYLOAD)

        found = collect(path, self.NOW, get)
        self.assertEqual(seen, {"url": USAGE_URL, "token": "tok"})
        self.assertEqual(found["read"], self.NOW)
        self.assertEqual({row["meter"]: row["percent"] for row in found["meters"]},
                         {"claude-week": 13.0, "claude-5h": 10.0, "claude-fable": 12.0})

    def test_a_missing_or_expired_token_is_an_error_and_names_no_token(self):
        path = self.credentials({"accessToken": "secret-value", "expiresAt": (self.NOW - 10) * 1000})
        with self.assertRaises(ValueError) as expired:
            collect(path, self.NOW, lambda url, token: "unused")
        self.assertNotIn("secret-value", str(expired.exception))
        path.write_text(json.dumps({"claudeAiOauth": {"expiresAt": (self.NOW + 3600) * 1000}}))
        with self.assertRaises(ValueError):
            collect(path, self.NOW, lambda url, token: "unused")

    def test_an_endpoint_that_refuses_is_its_status(self):
        path = self.credentials({"accessToken": "tok", "expiresAt": (self.NOW + 3600) * 1000})

        def get(url, token):
            raise Status(401)

        with self.assertRaises(Status) as refused:
            collect(path, self.NOW, get)
        self.assertEqual(refused.exception.status, 401)
        self.assertNotIn("tok", str(refused.exception))


def main():
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]], verbosity=1)
    if sys.argv[1:]:
        sys.exit(f"usage: {sys.argv[0]} [--test]")
    try:
        found = collect(CREDENTIALS, datetime.now().timestamp(), http_get)
    except (OSError, ValueError, KeyError, TypeError, Status, json.JSONDecodeError) as failure:
        print(f"claude usage: {failure}", file=sys.stderr)
        return 1
    print(json.dumps(found))
    return 0


if __name__ == "__main__":
    sys.exit(main())
