#!/usr/bin/env python3
"""Read-only C1 ELF/GNU/formal-source crosscheck; a trusted tooling boundary."""
import hashlib, json, re, struct, types
from pathlib import Path
PARSER_SHA = "6f35da09dea20999a64f5698618b369822c3eac60ebe7d6b161021206f163cff"
OWN = "development/approved-plan/reusable-assurance-v1"
BIAS = 0x21000000

def sha(data):
    return hashlib.sha256(data).hexdigest()

def compact(text):
    return re.sub(r"\s+", "", text)

def crosscheck(root, gnu_output):
    parser = root / "scripts/inventory.py"
    if sha(parser.read_bytes()) != PARSER_SHA:
        raise ValueError("Pinned ELF parser changed")
    module = types.ModuleType("c1_fresh_pinned_elf")
    module.__file__ = str(parser)
    exec(compile(parser.read_bytes(), str(parser), "exec"), module.__dict__)
    artifact = root / OWN / "c1/artifact"
    inventory = json.loads((artifact / "inventory-v1.json").read_text())
    elf = module.ELF(artifact / "compiled-v1/c1.so")
    if elf.sha256 != inventory["artifact_sha256"] or elf.type != 3 or elf.machine != 62:
        raise ValueError("C1 artifact/hash/ET_DYN/x86-64 mismatch")
    symbol, = [s for s in elf.symbols if s["table"] == ".dynsym" and s["name"] == "c1_crypto_buffers_equal"]
    entry = symbol["vaddr"]
    _, code = elf.extract(entry, symbol["size"])
    if entry != 0x1110 or len(code) != 22 or code != (artifact / "caller.bin").read_bytes():
        raise ValueError("Caller final ELF/extracted symbol mismatch")
    if code.hex() != inventory["caller"]["bytes_hex"] or sha(code) != inventory["caller"]["bytes_sha256"]:
        raise ValueError("Caller acquired byte pin changed")
    rows = []
    for line in (gnu_output / "disassembly.txt").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) < 3: continue
        match = re.fullmatch(r"\s*([0-9a-f]+):", fields[0])
        if not match: continue
        va = int(match[1], 16)
        if not entry <= va < entry + len(code): continue
        raw = bytes.fromhex(fields[1])
        if raw != code[va-entry:va-entry+len(raw)]:
            raise ValueError("Fresh GNU disassembly bytes disagree with ELF")
        rows.append((va, raw, fields[2].strip().split(None, 1)[0]))
    if [r[2] for r in rows] != ["sub", "call", "test", "sete", "add", "movzx", "ret"]:
        raise ValueError("Fresh GNU caller instruction profile mismatch")
    if sum(len(r[1]) for r in rows) != len(code) or rows[1][0] != 0x1114:
        raise ValueError("GNU symbol coverage/call offset mismatch")
    call_disp = struct.unpack_from("<i", rows[1][1], 1)[0]
    plt_va = rows[1][0] + 5 + call_disp
    _, plt = elf.extract(plt_va, 16)
    if plt_va != 0x1030 or plt[:2] != b"\xff\x25":
        raise ValueError("Actual reached PLT is not the frozen prefix")
    got_va = plt_va + 6 + struct.unpack_from("<i", plt, 2)[0]
    if got_va != 0x3fd8 or plt[:6] != (artifact / "plt-prefix.bin").read_bytes():
        raise ValueError("PLT prefix/GOT derivation mismatch")
    relocation, = [r for r in elf.relocations if r["offset"] == got_va]
    crypto, = [s for s in elf.symbols if s["table"] == ".dynsym" and s["name"] == "CRYPTO_memcmp"]
    if relocation["type"] != 7 or relocation["symbol"] != "CRYPTO_memcmp" or crypto["version"] != "OPENSSL_3.0.0":
        raise ValueError("CRYPTO_memcmp relocation/version mismatch")
    if any(r["type"] not in (6, 7, 8) for r in elf.relocations):
        raise ValueError("Unexpected relocation kind")
    if not any(d["tag"] == 30 and d["value"] & 8 for d in elf.dynamic):
        raise ValueError("C1 is missing DT_BIND_NOW")
    readelf = (gnu_output / "readelf.txt").read_text()
    if "Advanced Micro Devices X86-64" not in readelf or "BIND_NOW" not in readelf:
        raise ValueError("Fresh GNU ELF machine/eager-binding mismatch")
    if not re.search(r"^0*" + f"{got_va:x}" + r"\s+\w+\s+R_X86_64_JUMP_SLOT\s+\w+\s+CRYPTO_memcmp@OPENSSL_3\.0\.0\s+\+\s+0\s*$", readelf, re.M):
        raise ValueError("Fresh GNU relocation/version mismatch")
    def gnu_headers(kind):
        parsed = []
        for line in readelf.splitlines():
            fields = line.split()
            if not fields or fields[0] != kind: continue
            parsed.append(dict(file_offset=int(fields[1], 16), vaddr=int(fields[2], 16),
                paddr=int(fields[3], 16), file_size=int(fields[4], 16),
                memory_size=int(fields[5], 16), align=int(fields[-1], 16),
                flags=sum(n for letter, n in [("R",4),("W",2),("E",1)]
                          if letter in "".join(fields[6:-1]))))
        return parsed
    for label, kind in [("LOAD", 1), ("GNU_RELRO", 0x6474e552)]:
        expected_headers = [{k: p[k] for k in ["file_offset", "vaddr", "paddr", "file_size", "memory_size", "align", "flags"]}
                            for p in elf.ph if p["type"] == kind]
        if gnu_headers(label) != expected_headers:
            raise ValueError("Fresh GNU/independent ELF image-header mismatch: " + label)
    for r in elf.relocations:
        if any(r["offset"] < a+n and a < r["offset"]+8 for a, n in [(entry, len(code)), (plt_va, 16)]):
            raise ValueError("Relocation overlaps proved instruction bytes")
    section_checks = {}
    for section in [".text", ".plt"]:
        actual = elf.bytes(elf.byname[section])
        fresh = (gnu_output / ("gnu-" + section[1:] + ".bin")).read_bytes()
        if actual != fresh: raise ValueError("Fresh GNU/independent ELF section mismatch")
        section_checks[section] = {"length": len(actual), "sha256": sha(actual)}
    loads, immutable, initialized, flags = [], [], [], {}
    for segment in elf.ph:
        if segment["type"] != 1: continue
        lo = BIAS + segment["vaddr"]
        hi = lo + segment["memory_size"]
        if segment["file_size"] > segment["memory_size"]:
            raise ValueError("PT_LOAD file/memory extent mismatch")
        if segment["flags"] & 2:
            initialized.append([lo, hi])
        else:
            if segment["file_offset"] != segment["vaddr"]:
                raise ValueError("Formal immutable file-map correspondence mismatch")
            immutable.append([lo, lo + segment["file_size"]])
        loads.append(segment)
        for page in range(lo//4096*4096, (hi+4095)//4096*4096, 4096):
            flags[page] = flags.get(page, 0) | segment["flags"]
    relro, = [p for p in elf.ph if p["type"] == 0x6474e552]
    for page in range((BIAS+relro["vaddr"])//4096*4096,
                      (BIAS+relro["vaddr"]+relro["memory_size"])//4096*4096, 4096):
        flags[page] &= ~2
    def merge(pages):
        spans = []
        for page in sorted(pages):
            if spans and spans[-1][1] == page: spans[-1][1] = page + 4096
            else: spans.append([page, page + 4096])
        return spans
    if any(not value & 4 for value in flags.values()):
        raise ValueError("Formal mapped image assumes read permission on every page")
    mapped = merge(flags)
    execute = merge(p for p, f in flags.items() if f & 1)
    write = merge(p for p, f in flags.items() if f & 2)
    definitions = json.loads((root / OWN / "c1/contract/expected-terms-v1.json").read_text())["definitions-v1.ml"]
    for name, raw in [("c1_crypto_caller_mc", code), ("c1_crypto_plt_prefix", plt[:6])]:
        expected = name + ":byte list = [" + ";".join(f"word 0x{b:02x}" for b in raw) + "]"
        if compact(definitions[name]) != compact(expected):
            raise ValueError("Formal byte-array literal/actual final ELF mismatch: " + name)
    def interval(lo, hi):
        return f"0x{lo:x}<=a /\\ a<0x{hi:x}"
    for name, spans in [("c1_image_domain", mapped), ("c1_image_execute", execute),
                        ("c1_image_write", write), ("c1_immutable", immutable),
                        ("c1_initialized_rw", initialized)]:
        body = interval(*spans[0]) if len(spans) == 1 else " \\/ ".join("(" + interval(*s) + ")" for s in spans)
        if compact(definitions[name]) != compact(name + " a <=> " + body):
            raise ValueError("Formal image interval mismatch: " + name)
    if immutable != inventory["image"]["immutable_file_backed_intervals"] or initialized != inventory["image"]["initialized_rw_intervals"]:
        raise ValueError("Inventory/image source intervals mismatch")
    return dict(status="PASS_FRESH_TRUSTED_C1_BYTES_LINKAGE_IMAGE_SOURCE_CROSSCHECK_NOT_PROOF",
                artifact_sha256=elf.sha256, caller_sha256=sha(code), plt_prefix_sha256=sha(plt[:6]),
                fresh_GNU=True, section_crosschecks=section_checks, immutable=immutable,
                GNU_program_headers_relocations_version_checked=True,
                initialized_rw=initialized, mapped=mapped, executable=execute, writable=write,
                actual_call_target=BIAS+plt_va, actual_got_slot=BIAS+got_va,
                declared_postinitialization_supplier_target=0x10241840,
                parser_loader_physical_ISA_proof=False, target_routine_executed=False)
