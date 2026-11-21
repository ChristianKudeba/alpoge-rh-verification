"""Content-verified access to the hosted edition's release assets."""
import hashlib
import http.client
import json
import os
from pathlib import Path
import subprocess
import time
from urllib.parse import quote

TAG = "rh-literal-kernel-v1"
REPO = os.environ.get("GITHUB_REPOSITORY", "ChristianKudeba/alpoge-rh-verification")
EXPECTED_REPO = "ChristianKudeba/alpoge-rh-verification"


def gh(*args, **opts):
    if REPO.casefold() != EXPECTED_REPO.casefold():
        raise RuntimeError("unexpected publication repository")
    return subprocess.run(["gh", *args], check=True, **opts)


def api(route, *args):
    attempts = 1 if "--method" in args or "-X" in args else 5
    for attempt in range(attempts):
        try:
            return json.loads(gh("api", *args, route, capture_output=True).stdout)
        except (subprocess.CalledProcessError, json.JSONDecodeError):
            if attempt + 1 == attempts:
                raise
            time.sleep(2 ** attempt)


def paginate(route):
    return [item for page in api(route, "--paginate", "--slurp") for item in page]


def release(create=False, *, tag=TAG, target=None, title=None, body=None):
    pinned = {"rh-literal-kernel-v1": 453307898, "rh-literal-audit-v1": 453326245}
    if tag in pinned:
        result = api(f"repos/{REPO}/releases/{pinned[tag]}")
        if result["tag_name"] != tag or result["author"]["login"] != "github-actions[bot]":
            raise RuntimeError("unexpected edition release identity")
        return result
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


def upload_asset(release_id, path):
    if REPO.casefold() != EXPECTED_REPO.casefold():
        raise RuntimeError("unexpected upload repository")
    route = f"/repos/{REPO}/releases/{int(release_id)}/assets?name={quote(path.name, safe='')}"
    headers = {"Authorization": "Bearer " + os.environ["GH_TOKEN"], "Content-Type": "application/octet-stream",
               "Content-Length": str(path.stat().st_size), "User-Agent": "rh-translation-publisher",
               "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"}
    connection = http.client.HTTPSConnection("uploads.github.com", timeout=150)
    try:
        with path.open("rb") as source:
            connection.request("POST", route, body=source, headers=headers)
        response = connection.getresponse()
        body = response.read()
        if response.status != 201:
            raise RuntimeError(f"GitHub release asset {response.status}: {body[:400]!r}")
        return json.loads(body)
    finally:
        connection.close()


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
            receipt = upload_asset(rel["id"], path)
            if matches(receipt, sha, size):
                assets[path.name] = receipt
                return receipt
        except (http.client.HTTPException, OSError, RuntimeError) as exc:
            if attempt == 4:
                raise RuntimeError(f"upload failed for {path.name}: {exc}") from exc
        assets.update(listing(rel["id"]))
        if matches(assets.get(path.name), sha, size):
            return assets[path.name]
        time.sleep(2 ** attempt)
    raise RuntimeError("release asset could not be verified")


def write_json(path, data):
    Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                          encoding="utf-8")
