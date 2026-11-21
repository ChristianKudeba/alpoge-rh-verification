"""Verify the opening input assets of the restarted remote edition."""
from release_store import REPO, api, listing, matches

FIRST_DRAFT = 453277794
ACTIVE_EDITION = 453307898
TAG = "rh-literal-kernel-v1"


def core_edition():
    current = api(f"repos/{REPO}/releases/{ACTIVE_EDITION}")
    if (current["id"] != ACTIVE_EDITION or current["author"]["login"] != "github-actions[bot]"
            or current["tag_name"] != TAG):
        raise ValueError("unexpected core release identity or tag")
    return current


def recover_staged(folder, current):
    # The main preparation job owns uploads. Read the content hashes of both
    # releases here, including on a retry while an upload is still in progress.
    old = api(f"repos/{REPO}/releases/{FIRST_DRAFT}")
    if old["author"]["login"] != "github-actions[bot]" or not old["draft"]:
        raise ValueError("unexpected archived staging release")
    previous = listing(FIRST_DRAFT)
    active = listing(ACTIVE_EDITION)
    checked = 0
    for n in range(17):
        name = f"source-{n:04d}.ndjson.zst"
        original = previous[name]
        now = active.get(name)
        if not now or now["state"] != "uploaded":
            continue
        if not matches(now, original["digest"].removeprefix("sha256:"), original["size"]):
            raise ValueError("different content in restarted source asset: " + name)
        checked += 1
    print(f"Verified {checked} available opening assets against the first staging pass.", flush=True)
