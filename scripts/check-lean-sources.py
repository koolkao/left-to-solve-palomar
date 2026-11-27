#!/usr/bin/env python3
"""Check Palomar's source requirements for EVERY .lean file in this repository.

Palomar scans every regular .lean file of a submitted repository, including unused files and
contained projects: each must start with the `module` header (ordinary comments may precede it;
`lakefile.lean` is exempt from the header but not from the line cap), have at most 10,000 physical
lines, be valid UTF-8 and not be a symbolic link. `.git` and `.lake` directories are skipped, as
Palomar does. Each Challenge.lean must also stay within 1,000 lines and 100 KiB (a warning above
300 lines or 32 KiB).

The header and line rules follow PalomarRegistry/PalomarTemplate scripts/check-lean-sources.py
(Apache-2.0), which mirrors PalomarSubmission/scripts/source_requirements.py.

Usage: python3 scripts/check-lean-sources.py [root]   (default: the repository root)
Prints one line per file and exits 1 on any violation.
"""
import os
import re
import sys
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"α-κμ-ωΑ-ΟΡ-΢Τ-Ω"
    r"ϊ-ϻἀ-῾℀-⅏\U0001d49c-\U0001d59f"
    r"À-ÖØ-öø-ſ"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?₀-₉ₐ-ₜᵢ-ᵪⱼ"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def has_module_header(text: str) -> bool:
    """True if the first token after whitespace and ordinary comments is the keyword `module`."""
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_files(root: Path):
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            n for n in subdirectories
            if n not in {".git", ".lake"} and not (Path(directory) / n).is_symlink()
        )
        for name in sorted(names):
            if name.endswith(".lean"):
                yield Path(directory) / name


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parents[1])
    failed = False
    count = 0
    for path in lean_files(root):
        count += 1
        rel = path.relative_to(root)
        if path.is_symlink():
            print(f"FAIL {rel}: symbolic link")
            failed = True
            continue
        try:
            raw = path.read_bytes()
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            print(f"FAIL {rel}: not UTF-8")
            failed = True
            continue
        lines = physical_lines(text)
        problems = []
        if path.name != "lakefile.lean" and not has_module_header(text):
            problems.append("no `module` header")
        if lines > 10_000:
            problems.append(f"{lines} lines > 10,000")
        if path.name == "Challenge.lean":
            if lines > 1000 or len(raw) > 100 * 1024:
                problems.append("Challenge over 1,000 lines or 100 KiB")
            elif lines > 300 or len(raw) > 32 * 1024:
                print(f"WARN {rel}: Challenge over 300 lines or 32 KiB")
        if problems:
            print(f"FAIL {rel}: " + "; ".join(problems))
            failed = True
        else:
            print(f"ok   {rel} ({lines} lines)")
    if count == 0:
        print("FAIL: no .lean files found")
        failed = True
    print(f"{count} .lean files checked: " + ("FAILED" if failed else "all pass"))
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
