#!/usr/bin/env python3
"""Cross-check formal source interval clauses against the frozen ELF declaration.

This is an independently executable trust-boundary check of source constants,
not a proof of a HOL/ELF parser or physical loading. Live HOL separately audits
the exact expanded definitions and proves their reference-image consequences.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
FB = ROOT / "development/approved-plan/loaded-witness/full-binding/definitions-v2.ml"
CLW = ROOT / "development/approved-plan/cleanse/loaded-witness/definitions-v1.ml"
LW = ROOT / "development/approved-plan/loaded-witness/definitions-v3.ml"
DECLARATION = ROOT / "development/approved-plan/cleanse/interface/declared-cleanse-postimage-v1.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def equations(path):
    return dict(re.findall(r"let\s+(\w+)\s*=\s*new_definition\s*`([^`]+)`;;",
                           path.read_text()))


def intervals(term):
    return [[int(lo, 16), int(hi, 16)] for lo, hi in re.findall(
        r"(0x[0-9a-f]+)\s*<=\s*a\s*/\\\s*a\s*<\s*(0x[0-9a-f]+)", term)]


def normalized(term):
    return re.sub(r"\s+", "", term)


def crosscheck():
    fb, lw, clw = equations(FB), equations(LW), equations(CLW)
    d = json.loads(DECLARATION.read_text())
    segments = d["segments"]
    bias = d["load_bias"]
    if bias != 0x10000000 or len(segments) != 4 or d["permission_granule"] != 4096:
        raise ValueError("Unexpected frozen image model")
    immutable = [s["loaded_file_interval"] for s in segments[:3]]
    if intervals(fb["fb_immutable"]) != immutable:
        raise ValueError("Immutable formal byte intervals differ from declared PT_LOAD")
    for s in segments[:3]:
        e = s["elf"]
        if e["flags"] & 2 or e["file_offset"] != e["vaddr"] or e["file_size"] != e["memory_size"]:
            raise ValueError("Immutable address-minus-bias source-offset recipe is invalid")
        if s["loaded_file_interval"] != [bias + e["vaddr"], bias + e["vaddr"] + e["file_size"]]:
            raise ValueError("Immutable declared file-backed address interval mismatch")
    fourth = segments[3]
    initialized_rw = [fourth["loaded_file_interval"][0], fourth["initial_zero_fill_interval"][1]]
    if not fourth["elf"]["flags"] & 2 or intervals(fb["fb_initialized_rw"]) != [initialized_rw]:
        raise ValueError("Full initialized-RW formal exception differs from declared fourth memory interval")
    expected_reference = """fb_reference_image (file_bytes:num->byte) (initial_rw:int64->byte)
        (padding:int64->byte) (a:int64) =
        if fb_immutable (val a) then file_bytes (val a-0x10000000)
        else if fb_initialized_rw (val a) then initial_rw a else padding a"""
    if normalized(fb["fb_reference_image"]) != normalized(expected_reference):
        raise ValueError("Reference function has an unexpected source/RW/padding clause")
    expected_full = """fb_full_image file_bytes initial_rw padding (image:int64->byte) <=>
        !a. lw_image_domain (val(a:int64)) ==> image a =
            fb_reference_image file_bytes initial_rw padding a"""
    if normalized(fb["fb_full_image"]) != normalized(expected_full):
        raise ValueError("Whole-image predicate no longer quantifies every declared page byte")
    pages = [s["mapped_page_interval"] for s in segments]
    if any(lo % 4096 or hi % 4096 for lo, hi in pages) or any(
            pages[i][1] != pages[i + 1][0] for i in range(3)):
        raise ValueError("Contiguous page union recipe no longer applies")
    whole = [pages[0][0], pages[-1][1]]
    if intervals(lw["lw_image_domain"]) != [whole]:
        raise ValueError("Formal whole-image page domain mismatch")
    rx = [s["mapped_page_interval"] for s in segments if s["elf"]["flags"] & 1]
    if intervals(lw["lw_image_execute"]) != rx:
        raise ValueError("Formal RX pages differ from PT_LOAD executable pages")
    rw = d["postinit_writable_page_intervals"]
    if intervals(lw["lw_image_write"]) != rw:
        raise ValueError("Formal writable pages differ from declared post-RELRO pages")
    relro = d["relro_readonly_page_interval"]
    if (len(rw) != 1 or relro != [pages[3][0], rw[0][0]] or rw[0][1] != pages[3][1] or
            relro[0] % 4096 or relro[1] % 4096):
        raise ValueError("RELRO and RW page partition mismatch")
    entry = bias + d["target_region"]["elf_vaddr"]
    if entry != 0x102417d0 or d["target_region"]["file_offset"] != 0x2417d0:
        raise ValueError("Frozen target address/offset mismatch")
    if "word(0x102417d0+i)" not in normalized(clw["clw_reference_code"]):
        raise ValueError("Formal code slice address differs from declared entry")
    if "file_bytes(0x2417d0+i)" not in normalized(clw["clw_file_code"]):
        raise ValueError("Formal file slice offset differs from actual final ELF")
    if intervals(fb["fb_tls_page"]) != [[0x500000, 0x501000]]:
        raise ValueError("Unexpected literal TLS page")
    if not (0x501000 <= whole[0] or whole[1] <= 0x500000):
        raise ValueError("TLS page overlaps the library image")
    return {"status": "PASS_FORMAL_SOURCE_IMAGE_INTERVAL_CROSSCHECK", "formal_parser_proof": False,
            "human_review": "PENDING", "source_hashes": {str(f.relative_to(ROOT)): sha(f)
                for f in [FB, LW, CLW, DECLARATION, Path(__file__)]},
            "immutable_file_backed_byte_intervals": immutable,
            "initialized_rw_byte_interval_including_RELRO_and_BSS": initialized_rw,
            "whole_mapped_page_interval": whole, "executable_page_intervals": rx,
            "post_RELRO_writable_page_intervals": rw, "RELRO_readonly_page_interval": relro,
            "fixed_public_entry": entry, "exact_final_file_offset": 0x2417d0,
            "padding_clause": "All other declared mapped page bytes are stable public padding",
            "trust_boundary": "HOL proves the source predicates; this Python extraction and the ELF declaration remain unverified tooling"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = crosscheck()
    except (OSError, ValueError, KeyError) as e:
        raise SystemExit("Image clause crosscheck rejected: " + str(e))
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
