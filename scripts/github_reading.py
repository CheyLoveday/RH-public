"""Generate the GitHub view of the one manuscript in this repository."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE = Path("papers/type-i-torsion/manuscript/paper.md")
OUTPUT = SOURCE.with_name("paper_github.md")


def generate(raw: bytes) -> str:
    marker, metadata, body = raw.decode("utf-8").split("---\n", 2)
    if marker:
        raise ValueError("The manuscript must start with YAML metadata.")
    fields = dict(re.findall(r'^([a-z]+): (".*")$', metadata, re.MULTILINE))
    title, author, date = (json.loads(fields[key]) for key in ("title", "author", "date"))
    body = re.sub(
        r"^(#{2,6} .+?) \{#([a-z0-9-]+)\}$",
        lambda match: f'<a name="{match[2]}"></a>\n\n{match[1]}',
        body,
        flags=re.MULTILINE,
    )
    math = re.compile(r"(?P<display>\$\$[\s\S]*?\$\$)|(?P<inline>\$[^$\n]+\$)")

    def github_math(match: re.Match[str]) -> str:
        tex = match[0].replace(r"\operatorname{", r"\mathrm{")
        if match["display"]:
            return "\n" + tex + "\n"
        return "$`" + tex[1:-1] + "`$"

    body = math.sub(github_math, body)
    digest = hashlib.sha256(raw).hexdigest()
    return (
        f"# {title}\n\n{author} · {date}\n\n"
        "> Generated GitHub reading copy. Edit the [Pandoc source](paper.md).\n"
        f"> Source: `{SOURCE}`. SHA-256: `{digest}`.\n"
        "> Generate from the repository root with `python3 scripts/github_reading.py`.\n\n"
        f"{body.strip()}\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Compare with the committed copy.")
    args = parser.parse_args()
    expected = generate((ROOT / SOURCE).read_bytes()).encode("utf-8")
    output = ROOT / OUTPUT
    if args.check:
        if output.read_bytes() != expected:
            raise SystemExit("The generated reading copy differs. Run make reading.")
        print("The reading copy matches a fresh generation.")
    else:
        output.write_bytes(expected)


if __name__ == "__main__":
    main()
