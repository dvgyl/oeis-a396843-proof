#!/usr/bin/env python3
"""Bind final PDFs/TeX to existing visual and semantic review records.

Requires PyMuPDF (import fitz) for document inspection. This program does not
perform or invent a visual review: it requires the authoring groups' completed
page-review records, checks their hashes, and adds independent file-identity,
page-count, and text-bound checks. Run before final formal verification.
"""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

import fitz

from verify_final_collection import EXPECTED_IDS


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    folder = root / "reproducibility/final_collection"
    qa_paths = [folder / (group + "_pdf_qa.json") for group in ("original", "second", "recent")]
    records = {}
    for path in qa_paths:
        report = json.loads(path.read_text())
        if report.get("status") != "passed":
            raise ValueError(f"Unfinished visual review: {path.name}")
        for item in report["entries"]:
            oeis_id = item["oeis_id"]
            if oeis_id in records:
                raise ValueError(f"Duplicate visual review: {oeis_id}")
            pages = item["pages"]
            visual = (report.get("all_final_pages_rendered_and_visually_inspected") or
                      item.get("all_pages_visually_inspected") or
                      item.get("pages_visually_reviewed") == list(range(1, pages + 1)))
            if not visual:
                raise ValueError(f"Incomplete visual review: {oeis_id}")
            pdf = root / "manuscripts" / (oeis_id + ".pdf")
            tex = root / "manuscripts" / (oeis_id + ".tex")
            pdf_hash, tex_hash = digest(pdf), digest(tex)
            if pdf_hash != item.get("pdf_sha256", item.get("sha256_pdf")):
                raise ValueError(f"PDF changed after visual review: {oeis_id}")
            if tex_hash != item.get("tex_sha256", item.get("sha256_tex")):
                raise ValueError(f"TeX changed after review: {oeis_id}")
            with fitz.open(pdf) as document:
                if len(document) != pages:
                    raise ValueError(f"Page count changed: {oeis_id}")
                text = " ".join(" ".join(page.get_text() for page in document).split())
                identity = all(s in text for s in (oeis_id, "ChatGPT", "Dev Goyal", "review", "pending"))
                if not identity:
                    raise ValueError(f"Missing entry identity or disclosure: {oeis_id}")
                outside = []
                for index, page in enumerate(document, 1):
                    for word in page.get_text("words"):
                        if word[0] < -0.5 or word[1] < -0.5 or word[2] > page.rect.width + 0.5 or word[3] > page.rect.height + 0.5:
                            outside.append({"page": index, "word": word[4]})
                if outside:
                    raise ValueError(f"Text outside page bounds: {oeis_id}: {outside}")
            records[oeis_id] = {
                "oeis_id": oeis_id, "pages": pages,
                "pdf_sha256": pdf_hash, "tex_sha256": tex_hash,
                "all_final_pages_visually_inspected": True,
                "source_id_and_disclosure_present": True,
                "out_of_page_words": 0,
                "group_quality_report": str(path.relative_to(root)),
            }
    if set(records) != EXPECTED_IDS:
        raise ValueError("Visual reports do not cover the exact final inventory")
    review_paths = [folder / name for name in (
        "second_review_of_original.md", "recent_review_of_second.md", "original_review_of_recent.md")]
    reviewed_files = {}
    for path in review_paths:
        review_text = path.read_text()
        matches = re.findall(
            r"^\| `((?:manuscripts|lean/Entries)/[^`]+)` \| `([0-9a-f]{64})` \|",
            review_text, re.MULTILINE)
        paired = re.findall(
            r"^\| (A\d{6}) \| `([0-9a-f]{64})` \| `([0-9a-f]{64})` \|",
            review_text, re.MULTILINE)
        for oeis_id, tex_hash, lean_hash in paired:
            matches.extend([(f"manuscripts/{oeis_id}.tex", tex_hash),
                            (f"lean/Entries/{oeis_id}.lean", lean_hash)])
        if not matches:
            raise ValueError(f"No source hashes in semantic review: {path.name}")
        for relative, expected in matches:
            if digest(root / relative) != expected:
                raise ValueError(f"Semantic review is stale: {relative}")
            reviewed_files[relative] = expected
    required_reviewed_files = {
        path for oeis_id in EXPECTED_IDS
        for path in (f"manuscripts/{oeis_id}.tex", f"lean/Entries/{oeis_id}.lean")
    }
    if not required_reviewed_files <= set(reviewed_files):
        raise ValueError("Some manuscript or entry interface lacks a current semantic review")
    checks = {
        "status": "all_individual_manuscripts_checked",
        "completed_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "review_status": "AI-assisted visual and semantic review; independent human review pending",
        "entry_count": len(records),
        "page_count": sum(item["pages"] for item in records.values()),
        "group_quality_reports": {str(path.relative_to(root)): digest(path) for path in qa_paths},
        "semantic_review_reports": {str(path.relative_to(root)): digest(path) for path in review_paths},
        "semantic_reviewed_files": {path: reviewed_files[path] for path in sorted(required_reviewed_files)},
        "entries": [records[key] for key in sorted(records)],
    }
    (root / "validation/manuscript_checks.json").write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps({key: checks[key] for key in ("status", "entry_count", "page_count")}, indent=2))


if __name__ == "__main__":
    main()
