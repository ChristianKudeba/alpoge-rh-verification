"""Recover the checked opening source assets from the first draft into the active draft."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import tempfile

from release_store import REPO, api, download, listing, matches, put

FIRST_DRAFT = 453277794
ACTIVE_EDITION = 453307898
TAG = "rh-literal-kernel-v1"


def core_edition():
    current = api(f"repos/{REPO}/releases/{ACTIVE_EDITION}")
    if current["id"] != ACTIVE_EDITION or current["author"]["login"] != "github-actions[bot]":
        raise ValueError("unexpected core release")
    if current["tag_name"] != TAG:
        raise ValueError("the core publication tag changed: " + current["tag_name"])
    return current


def recover_staged(folder, current):
    if not current["draft"]:
        return
    if current["target_commitish"] != "main":
        # Always send tag_name on a draft edit. GitHub can generate an untagged
        # placeholder when target_commitish is edited without the existing tag.
        checked = api(f"repos/{REPO}/releases/{ACTIVE_EDITION}", "--method", "PATCH",
                      "-f", "tag_name=" + TAG, "-f", "target_commitish=main",
                      "-f", "body=The verified MIT source is being typeset. "
                      "The source and renderer hashes are recorded in the final publication.")
        if (checked["id"], checked["tag_name"], checked["target_commitish"]) != (ACTIVE_EDITION, TAG, "main"):
            raise ValueError("core draft identity changed during metadata update")
    old = api(f"repos/{REPO}/releases/{FIRST_DRAFT}")
    if old["author"]["login"] != "github-actions[bot]" or not old["draft"]:
        raise ValueError("unexpected owner or state of staging release")
    source = listing(FIRST_DRAFT)
    active = listing(ACTIVE_EDITION)
    expected = [f"source-{i:04d}.ndjson.zst" for i in range(17)]
    if any(n not in source for n in expected):
        raise ValueError("partial staging release lost a previously checked asset")

    def copy(name):
        item = source[name]
        digest = item.get("digest", "").removeprefix("sha256:")
        if not re.fullmatch(r"[0-9a-f]{64}", digest) or item["state"] != "uploaded":
            raise ValueError("incomplete staging asset")
        if matches(active.get(name), digest, item["size"]):
            return
        with tempfile.TemporaryDirectory(dir=folder) as work:
            path = Path(work) / name
            download(item, path)
            put(current, dict(active), path)
        print("Recovered " + name, flush=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        list(pool.map(copy, expected))
