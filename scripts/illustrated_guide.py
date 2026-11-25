"""Generate the standalone reading view of the Type I explanation."""

from __future__ import annotations

import argparse
import hashlib
import html
import re
import subprocess
from pathlib import Path
from urllib.parse import urljoin, urlsplit


ROOT = Path(__file__).resolve().parent.parent
SOURCE = Path("papers/type-i-torsion/reading/EXPLAINED.md")
OUTPUT = SOURCE.with_name("EXPLAINED_ILLUSTRATED.html")
TEMPLATE = Path("scripts/illustrated_guide.html")
PUBLIC_SOURCE = f"https://github.com/CheyLoveday/RH-public/blob/main/{SOURCE}"


def public_link(match: re.Match[str]) -> str:
    href = html.unescape(match[1])
    if href.startswith(("#", "//")) or urlsplit(href).scheme:
        return match[0]
    return f'href="{html.escape(urljoin(PUBLIC_SOURCE, href), quote=True)}"'


def generate(raw: bytes) -> bytes:
    result = subprocess.run(
        [
            "pandoc", "--from=gfm+tex_math_dollars", "--to=html5",
            "--standalone", "--mathml", "--section-divs", "--wrap=none",
            f"--template={TEMPLATE}", "--metadata=pagetitle:Why one extra power of p survives",
            f"--variable=source_path:{SOURCE}",
            f"--variable=source_sha:{hashlib.sha256(raw).hexdigest()}",
        ],
        cwd=ROOT,
        input=raw,
        capture_output=True,
        check=True,
    )
    return re.sub(r'href="([^"]+)"', public_link, result.stdout.decode()).encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Compare with the recorded view.")
    args = parser.parse_args()
    expected = generate((ROOT / SOURCE).read_bytes())
    if args.check:
        if (ROOT / OUTPUT).read_bytes() != expected:
            raise SystemExit("The illustrated guide differs from a fresh generation. Run make guide.")
        print("The illustrated guide matches a fresh generation.")
    else:
        (ROOT / OUTPUT).write_bytes(expected)


if __name__ == "__main__":
    main()
