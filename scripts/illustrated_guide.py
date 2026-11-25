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
REPOSITORY = "https://github.com/CheyLoveday/RH-public"


def public_link(match: re.Match[str], ref: str) -> str:
    href = html.unescape(match[1])
    if ref != "main" and href == REPOSITORY:
        href = f"{REPOSITORY}/tree/{ref}"
    elif ref != "main" and href.startswith((f"{REPOSITORY}/blob/main/", f"{REPOSITORY}/tree/main/")):
        href = href.replace("/main/", f"/{ref}/", 1)
    elif href.startswith(("#", "//")) or urlsplit(href).scheme:
        return match[0]
    else:
        href = urljoin(f"{REPOSITORY}/blob/{ref}/{SOURCE}", href)
    return f'href="{html.escape(href, quote=True)}"'


def generate(raw: bytes, ref: str) -> bytes:
    command = "python3 scripts/illustrated_guide.py"
    if ref != "main":
        command += f" --revision {ref} --output {OUTPUT.name}"
    sections = []
    if b"\n## How to find the separating row\n" in raw:
        sections.append("--variable=row_discovery:true")
    result = subprocess.run(
        [
            "pandoc", "--from=gfm+tex_math_dollars", "--to=html5",
            "--standalone", "--mathml", "--section-divs", "--wrap=none",
            f"--template={TEMPLATE}", "--metadata=pagetitle:Why one extra power of p survives",
            f"--variable=source_path:{SOURCE}",
            f"--variable=source_sha:{hashlib.sha256(raw).hexdigest()}",
            f"--variable=generation_command:{command}",
            *sections,
        ],
        cwd=ROOT,
        input=raw,
        capture_output=True,
        check=True,
    )
    return re.sub(r'href="([^"]+)"', lambda match: public_link(match, ref), result.stdout.decode()).encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Compare with the recorded view.")
    parser.add_argument("--revision", help="Read the guide source and pin repository links at this full commit SHA.")
    parser.add_argument("--output", type=Path, help="Separate HTML output path for a pinned edition.")
    args = parser.parse_args()
    output = ROOT / OUTPUT
    ref = args.revision or "main"
    if args.revision is not None:
        if not re.fullmatch(r"[0-9a-f]{40}", args.revision):
            parser.error("--revision must be a full lowercase commit SHA")
        if args.output is None or args.output.resolve() == output.resolve():
            parser.error("--revision requires --output outside the maintained reading edition")
        output = args.output
        try:
            raw = subprocess.run(
                ["git", "show", f"{ref}:{SOURCE.as_posix()}"],
                cwd=ROOT,
                capture_output=True,
                check=True,
            ).stdout
        except subprocess.CalledProcessError:
            parser.error(f"guide source unavailable at {ref}")
    else:
        if args.output is not None:
            parser.error("--output requires --revision")
        raw = (ROOT / SOURCE).read_bytes()
    expected = generate(raw, ref)
    if args.check:
        if output.read_bytes() != expected:
            raise SystemExit("The illustrated guide differs from a fresh generation.")
        print("The illustrated guide matches a fresh generation.")
    else:
        output.write_bytes(expected)


if __name__ == "__main__":
    main()
