"""Content-verified access to the hosted edition's release assets."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

TAG = "rh-literal-kernel-v1"
REPO = os.environ.get("GITHUB_REPOSITORY", "ChristianKudeba/alpoge-rh-verification")
EXPECTED_REPO = "ChristianKudeba/alpoge-rh-verification"


def gh(*args, **opts):
    if REPO.casefold() != EXPECTED_REPO.casefold():
        raise RuntimeError("unexpected publication repository")
    return subprocess.run(["gh", *args], check=True, **opts)


def api(route, *args):
    return json.loads(gh("api", *args, route, capture_output=True).stdout)


def paginate(route):
    return [item for page in api(route, "--paginate", "--slurp") for item in page]


def release(create=False, *, tag=TAG, target=None, title=None, body=None):
    route = f"repos/{REPO}/releases"
    matches = [r for r in paginate(route + "?per_page=100") if r["tag_name"] == tag]
    if len(matches) == 1:
        return matches[0]
    if matches or not create:
        raise RuntimeError("release lookup failed")
    return api(route, "--method", "POST", "-f", f"tag_name={tag}", "-F", "draft=true",
               "-f", "target_commitish=" + (target or os.environ["GITHUB_SHA"]),
               "-f", "name=" + (title or "Riemann hypothesis: literal mathematical term edition"),
               "-f", "body=" + (body or "Verified export shards, typesettable LaTeX volumes and their integrity manifest."))


def listing(release_id):
    rows = paginate(f"repos/{REPO}/releases/{release_id}/assets?per_page=100")
    return {row["name"]: row for row in rows}


def info(path):
    path = Path(path)
    with path.open("rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    return digest, path.stat().st_size


def matches(asset, sha, size):
    return bool(asset and asset.get("state") == "uploaded" and
                asset["size"] == size and asset.get("digest") == "sha256:" + sha)


def download(asset, path):
    path = Path(path)
    for attempt in range(4):
        try:
            with path.open("wb") as dest:
                gh("api", f"repos/{REPO}/releases/assets/{asset['id']}",
                   "-H", "Accept: application/octet-stream", stdout=dest)
            sha, size = info(path)
            if not matches(asset, sha, size):
                raise RuntimeError("downloaded asset differs from its release digest")
            return
        except (OSError, RuntimeError, subprocess.CalledProcessError):
            if attempt == 3:
                raise
            time.sleep(2 ** attempt)


def put(rel, assets, path, *, tag=TAG):
    """Only identical completed uploads are reused. Transient empty uploads can retry."""
    path = Path(path)
    sha, size = info(path)
    for attempt in range(5):
        a = assets.get(path.name)
        if matches(a, sha, size):
            return a
        if not rel["draft"]:
            raise RuntimeError("the published release is immutable to this pipeline")
        if a:
            if a.get("state") != "starter" or a["size"] != 0:
                raise RuntimeError(f"refusing to replace conflicting asset {path.name}")
            gh("api", "--method", "DELETE", f"repos/{REPO}/releases/assets/{a['id']}")
        if size >= 2 ** 31:
            raise ValueError("individual release asset exceeds GitHub's limit")
        try:
            gh("release", "upload", tag, str(path), "--repo", REPO, capture_output=True)
        except subprocess.CalledProcessError as exc:
            if attempt == 4:
                raise RuntimeError(f"upload failed for {path.name}: {exc.stderr[-1000:]}") from exc
        assets.update(listing(rel["id"]))
        if matches(assets.get(path.name), sha, size):
            return assets[path.name]
        time.sleep(2 ** attempt)
    raise RuntimeError("release asset could not be verified")


def write_json(path, data):
    Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                          encoding="utf-8")
