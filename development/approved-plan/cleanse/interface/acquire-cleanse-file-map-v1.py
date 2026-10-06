#!/usr/bin/env python3
"""Check the entire ELF map's external interpretation; no formal parser claim.

The mathematical file_bytes(k) is word(raw[k]) below len(raw), and word(0)
otherwise. This is a trusted artifact-acquisition boundary, not a HOL axiom or
a claim that the loader ran. Every invocation rehashes and reparses raw ELF.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
ARTIFACT = ROOT / "artifacts/baseline/libcrypto.so.3"
EXPECTED_SHA = "76dd3d93e5ee48950a92a58d59b94de8143847f91a80d9682c938767b991577d"
DECLARATION = ROOT / "development/approved-plan/cleanse/interface/declared-cleanse-postimage-v1.json"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def acquire(artifact=ARTIFACT):
    raw = artifact.read_bytes()
    if sha(raw) != EXPECTED_SHA:
        raise ValueError("Entire final ELF digest mismatch")
    if raw[:7] != b"\x7fELF\x02\x01\x01":
        raise ValueError("Expected ELF64 little-endian version 1")
    hdr = struct.unpack_from("<HHIQQQIHHHHHH", raw, 16)
    typ, machine, version, entry, phoff, shoff, flags, ehsize, phentsize, phnum, *_ = hdr
    if (typ, machine, version, ehsize, phentsize) != (3, 62, 1, 64, 56):
        raise ValueError("Unexpected frozen ELF ABI/header")
    if phoff + phentsize * phnum > len(raw):
        raise ValueError("Out-of-file program headers")
    declaration = json.loads(DECLARATION.read_text())
    segments = []
    for idx in range(phnum):
        pt, perm, off, va, pa, fs, ms, align = struct.unpack_from(
            "<IIQQQQQQ", raw, phoff + idx * phentsize)
        if pt == 1:
            if off + fs > len(raw) or fs > ms:
                raise ValueError("Invalid loadable segment extent")
            segments.append({"type": pt, "flags": perm, "file_offset": off,
                             "vaddr": va, "paddr": pa, "file_size": fs,
                             "memory_size": ms, "align": align})
    expected = [{k: d["elf"][k] for k in segments[0]}
                for d in declaration["segments"]]
    if segments != expected:
        raise ValueError("Frozen declared PT_LOAD headers mismatch")
    target = declaration["target_region"]
    covers = [s for s in segments if s["vaddr"] <= target["elf_vaddr"] and
              target["elf_vaddr"] + 97 <= s["vaddr"] + s["file_size"]]
    if len(covers) != 1:
        raise ValueError("Target must belong to exactly one file-backed segment")
    segment = covers[0]
    file_offset = segment["file_offset"] + target["elf_vaddr"] - segment["vaddr"]
    if file_offset != 0x2417d0 or target["file_offset"] != file_offset:
        raise ValueError("Code VA to final-file offset mismatch")
    code = raw[file_offset:file_offset + 97]
    literal_src = (ROOT / "proofs/qualification/openssl_bytes.ml").read_text()
    match = re.search(r"let openssl_cleanse_mc = new_definition\s*`([^`]+)`", literal_src)
    if match is None:
        raise ValueError("Exact HOL code definition absent")
    literal = bytes(int(x, 16) for x in re.findall(r"word (0x[0-9a-f]+)", match[1]))
    if len(literal) != 97 or code != literal:
        raise ValueError("Actual whole-file map does not satisfy frozen clw_file_code")
    if code.hex() != target["bytes_hex"] or sha(code) != target["bytes_sha256"]:
        raise ValueError("Declared code slice mismatch")
    relocs = json.loads((ROOT / declaration["relocations"]["inventory"]).read_text())
    # The canonical inventory uses either a record containing relocations or
    # a raw list. Its digest is checked independently before interpretation.
    reloc_raw = (ROOT / declaration["relocations"]["inventory"]).read_bytes()
    if sha(reloc_raw) != declaration["relocations"]["sha256"]:
        raise ValueError("Frozen relocation inventory drift")
    records = relocs if isinstance(relocs, list) else relocs.get("relocations", [])
    if not records or len(records) != declaration["relocations"]["count"]:
        raise ValueError("Frozen relocation record count mismatch")
    if set(r["type"] for r in records) != {1, 6, 7, 8}:
        raise ValueError("Unqualified relocation width")
    if any(r["offset"] < target["elf_vaddr"] + 97 and
           target["elf_vaddr"] < r["offset"] + 8 for r in records):
        raise ValueError("Relocation overlaps target code")
    bias = declaration["load_bias"]
    if bias != 0x10000000:
        raise ValueError("Load bias differs from frozen image predicate")
    segments_record = []
    for n, (s, declared) in enumerate(zip(segments, declaration["segments"])):
        interval = [bias + s["vaddr"], bias + s["vaddr"] + s["memory_size"]]
        file_interval = [s["file_offset"], s["file_offset"] + s["file_size"]]
        if declared["source_file_interval"] != file_interval:
            raise ValueError("Declared raw segment file interval mismatch")
        if declared["loaded_file_interval"] != [interval[0], interval[0] + s["file_size"]]:
            raise ValueError("Declared loaded segment file interval mismatch")
        if declared["initial_zero_fill_interval"] != [interval[0] + s["file_size"], interval[1]]:
            raise ValueError("Declared initial zero-fill interval mismatch")
        page_interval = [interval[0] // 4096 * 4096,
                         ((interval[1] + 4095) // 4096) * 4096]
        if page_interval != declared["mapped_page_interval"]:
            raise ValueError("Declared segment page interval mismatch")
        segments_record.append({"index": n, **s, "source_file_interval": file_interval,
                                "source_segment_sha256": sha(raw[s["file_offset"]:s["file_offset"] + s["file_size"]]),
                                "mapped_page_interval": page_interval,
                                "initialized_memory_interval": interval,
                                "binding_clause": "immutable_raw_file" if n < 3 else
                                    "explicit_public_post_initialization_RW_map_including_RELRO"})
    return {"schema_version": 1, "status": "PASS_TRUSTED_WHOLE_FILE_MAP_ACQUISITION",
            "artifact_path": str(artifact.relative_to(ROOT)), "artifact_sha256": sha(raw),
            "file_length": len(raw), "file_map_interpretation":
                "file_bytes(k)=word(raw[k]) for k<file_length; word(0) otherwise",
            "file_map_bytes_are_the_complete_artifact": True,
            "formal_parser_or_loader_proof": False, "human_review": "PENDING",
            "segments": segments_record, "clw_file_code_external_check": True,
            "code_file_offset": file_offset, "code_elf_vaddr": target["elf_vaddr"],
            "code_loaded_address": bias + target["elf_vaddr"], "code_bytes": 97,
            "code_sha256": sha(code), "relocation_overlap": False,
            "rw_initialization_and_page_padding": "explicit_stable_public_parameters",
            "declaration_sha256": sha(DECLARATION.read_bytes()),
            "acquisition_program_sha256": sha(Path(__file__).read_bytes())}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        help="Save the acquisition record (read-only verification by default)")
    args = parser.parse_args()
    try:
        result = acquire()
    except (OSError, ValueError, KeyError, struct.error) as e:
        raise SystemExit("Full-file map acquisition rejected: " + str(e))
    result_json = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result_json)
    print(result_json, end="")


if __name__ == "__main__":
    main()
