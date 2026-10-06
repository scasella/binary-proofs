#!/usr/bin/env python3
"""Pinned C1 source/literal/load-graph checks; no proof-success assertion."""
import argparse, hashlib, json, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
OWN = "development/approved-plan/reusable-assurance-v1"
CONTRACT = OWN + "/c1/contract"
CONTRACT_HASHES = {
    "definitions-v1.ml": "ce661d9fc1e2a865ef85c7afa8cc49dd1fc4d2e5813cd90e12b6fe645687ea5b",
    "statements-v1.ml": "f78c781adb2d667119db49601c56dfc0b44dd622947181606218658479e624b9",
    "expected-terms-v1.json": "94a347b1f071bffa0e977240789b7f27e4d926637e1384ad75dea0acb2c7c5bc",
}
CONTRACT_FREEZE_SHA = "70b0c20b37e210d78d415c71953292afc889c78ea9757025d9d74d5a049f2a98"
ARTIFACT_INPUTS = {
    "inventory-v1.json": "70f6fcd526fa336f4c2b4278c25bd2578a30f5def43aa73e69953fddbef0430f",
    "compiled-v1/c1.so": "0ede476eef3a8f059aef0b93b36d4669647ae8ee3455fb076559b3e7bdf3d787",
    "caller.bin": "523a5ad18d6236eaae39114b3b3ed7b71a4d71592ca4ef410d994f90aa18cb33",
    "plt-prefix.bin": "1e593d19790a007d6f3773070559a53fa4fa65da6d44d76306dd9679ed79b458",
    "c1.c": "bc775373daf3bda37825c55c8a5e73c4de23cdbc73bcedce2aa95e0212edb349",
    "build-v1.sh": "f105d2d0b92c2b5df00bf00c7e9c39f9c8dabd8d65a245584c4becb2b8fef99c",
}
E5_EXPECTED = OWN + "/generic/e5-expanded-definition-expectations-v1.json"
E5_EXPECTED_SHA = "4db786306f9496bee4fbb30bfb953f7f224a6c74975b749b64178c00bcb599ed"
SUPPLIER_INDEX = "development/approved-plan/clients-e3/opaque-supplier-v1/source-index-v1.json"
SUPPLIER_INDEX_SHA = "0381c183d1d86da7b4b030224281c1668379f3b7c52154843e1afd20ac206905"
PUBLIC = "development/approved-plan/clients-e3/public-inputs-v1"
PUBLIC_FILES = {"code-length-exports-v1.ml", "generic-checked-step-v1.ml"}
ROOT_FORMAL_LOADERS = {"development-loader-v2.ml", "development-loader-v3.ml", "development-loader-v4.ml"}
HELPER_FREEZES = {
    "c1/completion/literal-freeze-v1.json": "5eaa25720f9c4a2e21ba28ffbb1a794bf2bbe2db50d83fa935ceece095f81b4f",
    "c1/continuation/tail-freeze-v1.json": "7db9b6dd99f074f3ea9d8eb13fbc442e8cf57107301cccdf1b45dd9ce5529218",
    "c1/witnesses/freeze-v2.json": "b43f439fd8f3ee96df5c519291042ef1f35562fdd14651075790dbe11462f72e",
}
WORK_GENERIC = {
    "development/approved-plan/clients-e3/secret-v1/" + name
    for name in ["generic-span-statements-v1.ml", "generic-span-proof-attempt3.ml",
                 "generic-four-frame-statements-v1.ml", "generic-four-frame-proof-attempt1.ml"]
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def checked(root, name, digest=None):
    rel = Path(name)
    if rel.is_absolute() or ".." in rel.parts or not rel.parts:
        raise ValueError("Unsafe source path: " + name)
    for i in range(len(rel.parts) + 1):
        if root.joinpath(*rel.parts[:i]).is_symlink():
            raise ValueError("Symlink source path: " + name)
    p = root / rel
    if not p.is_file() or (digest is not None and sha(p) != digest):
        raise ValueError("Missing or changed frozen input: " + name)
    return p

def anchors(root):
    freeze = json.loads(checked(root, CONTRACT + "/freeze-v1.json", CONTRACT_FREEZE_SHA).read_text())
    for name, digest in freeze["files"].items(): checked(root, CONTRACT + "/" + name, digest)
    for name, digest in ARTIFACT_INPUTS.items(): checked(root, OWN + "/c1/artifact/" + name, digest)
    for name, digest in CONTRACT_HASHES.items():
        checked(root, CONTRACT + "/" + name, digest)
    j = json.loads(checked(root, CONTRACT + "/expected-terms-v1.json").read_text())
    if len(j["statements-v1.ml"]) != 7:
        raise ValueError("Original C1 seven-target registry mismatch")
    # Exact source literals must match the separately frozen expected JSON.
    for filename, pattern in [
        ("definitions-v1.ml", r"let\s+(\w+)\s*=\s*new_definition\s*\x60([^\x60]*)\x60;;"),
        ("statements-v1.ml", r"let\s+(\w+)\s*=\s*\x60([^\x60]*)\x60;;"),
    ]:
        pairs = re.findall(pattern, (root / CONTRACT / filename).read_text(), re.S)
        if len(pairs) != len(dict(pairs)) or dict(pairs) != j[filename]:
            raise ValueError("Frozen C1 literal/source mismatch: " + filename)
    e5 = json.loads(checked(root, E5_EXPECTED, E5_EXPECTED_SHA).read_text())
    if len(e5["rows"]) != 7:
        raise ValueError("Frozen E5 definition count mismatch")
    for row in e5["rows"]:
        if hashlib.sha256(row["equation"].encode()).hexdigest() != row["equation_sha256"]:
            raise ValueError("E5 literal digest mismatch")
    checked(root, SUPPLIER_INDEX, SUPPLIER_INDEX_SHA)
    return j, e5

def tokens(text):
    """Only lex comments, strings and identifiers needed for static imports."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith("(*", i): depth, i = depth + 1, i + 2
                elif text.startswith("*)", i): depth, i = depth - 1, i + 2
                else: i += 1
            if depth: raise ValueError("Unclosed OCaml comment")
        elif text[i] == '"':
            i += 1
            value = ""
            while i < len(text) and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                    if i >= len(text): raise ValueError("Unclosed string")
                    value += "\\" + text[i]
                else: value += text[i]
                i += 1
            if i == len(text): raise ValueError("Unclosed OCaml string")
            i += 1
            out.append(("string", value))
        elif text[i].isalpha() or text[i] == "_":
            m = re.match(r"[A-Za-z_][A-Za-z_0-9']*", text[i:])
            out.append(("identifier", m.group()))
            i += len(m.group())
        else: i += 1
    return out

def definition_literals(source):
    pairs = re.findall(r"let\s+(\w+)\s*=\s*(?:new_definition|new_recursive_definition\s+\w+)\s*\x60([^\x60]*)\x60;;", source, re.S)
    count = sum(k == "identifier" and v in ("new_definition", "new_recursive_definition")
                for k, v in tokens(source))
    if count != len(pairs) or len(pairs) != len(dict(pairs)):
        raise ValueError("Untracked/dynamic/duplicate definition construction")
    return dict(pairs)

def helper_anchors(root):
    """Use the existing independent pre-proof freezes, never the proof text."""
    receipts = {name: json.loads(checked(root, OWN + "/" + name, digest).read_text())
                for name, digest in HELPER_FREEZES.items()}
    definitions, files = {}, {OWN + "/" + n: d for n, d in HELPER_FREEZES.items()}
    for lane, receipt_name, source_name, expected_key in [
        ("c1/completion", "c1/completion/literal-freeze-v1.json", "definitions-v1.ml", "expected_definitions"),
        ("c1/continuation", "c1/continuation/tail-freeze-v1.json", "tail-definitions-v1.ml", None),
        ("c1/witnesses", "c1/witnesses/freeze-v2.json", "definitions-v2.ml", "expanded_definitions"),
    ]:
        freeze = receipts[receipt_name]
        source_path = OWN + "/" + lane + "/" + source_name
        files[source_path] = freeze["files"][source_name]
        source_defs = definition_literals(checked(root, source_path, files[source_path]).read_text())
        if lane == "c1/completion":
            expected_path = OWN + "/" + lane + "/expected-v1.json"
            files[expected_path] = freeze["files"]["expected-v1.json"]
            expected = json.loads(checked(root, expected_path, files[expected_path]).read_text())[expected_key]
        elif expected_key:
            expected = freeze[expected_key]
        else:
            # The original tail freeze fixes the complete definition file bytes.
            expected = source_defs
        if source_defs != expected or len(source_defs) != (10 if lane.endswith("witnesses") else 2):
            raise ValueError("Pre-proof helper definition mismatch: " + lane)
        for name, literal in source_defs.items():
            if name in definitions: raise ValueError("Duplicate helper definition anchor")
            definitions[name] = literal
    witness = receipts["c1/witnesses/freeze-v2.json"]
    stm_path = OWN + "/c1/witnesses/statements-v1.ml"
    files[stm_path] = witness["files"]["statements-v1.ml"]
    pairs = re.findall(r"let\s+(\w+)\s*=\s*\x60([^\x60]*)\x60;;",
                       checked(root, stm_path, files[stm_path]).read_text(), re.S)
    if len(pairs) != 21 or len(dict(pairs)) != 21 or dict(pairs) != witness["literal_targets"]:
        raise ValueError("All 21 pre-proof nonvacuity witness literals are required")
    if witness["seven_cases_unchanged"] is not True or witness["main_c1_pre_unchanged"] is not True:
        raise ValueError("Changed witness cases or full caller precondition")
    return definitions, witness["literal_targets"], files

def resolve_import(name):
    if name.startswith("/reuse/"):
        leaf = name[len("/reuse/"):]
        if not leaf.startswith(("generic/", "linkage/", "c1/")) and leaf not in ROOT_FORMAL_LOADERS:
            raise ValueError("New caller import is outside its formal source lanes: " + name)
        return OWN + "/" + leaf
    if name.startswith("/client-public/"):
        leaf = name[len("/client-public/"):]
        if leaf not in PUBLIC_FILES:
            raise ValueError("Unapproved former-client public import: " + name)
        return PUBLIC + "/" + leaf
    if name.startswith("/work/"):
        rel = name[len("/work/"):]
        if rel.startswith(OWN + "/"):
            return resolve_import("/reuse/" + rel[len(OWN)+1:])
        if rel not in WORK_GENERIC:
            raise ValueError("New C1 graph imports opaque implementation/former caller: " + name)
        return rel
    raise ValueError("Import has no reviewed mount mapping: " + name)

def load_graph(root, loader):
    if not loader.startswith(OWN + "/"):
        raise ValueError("C1 loader must belong to the new workstream")
    graph, active = {}, set()
    def visit(name):
        if name in active: raise ValueError("Import cycle: " + name)
        if name in graph: return
        active.add(name)
        p = checked(root, name)
        source = p.read_text()
        if re.search(r"(?m)^\s*#\s*(?:use|load)\b", source):
            raise ValueError("Untracked toplevel import directive: " + name)
        imports, aliases, ts = [], [], tokens(source)
        for i, (kind, value) in enumerate(ts):
            if kind == "identifier" and value in ("new_axiom", "mk_thm", "Obj"):
                raise ValueError("Unreviewed theorem/axiom bypass in C1 source: " + name)
            if kind == "identifier" and value in ("use_file", "use_file_no_raise", "Toploop", "Topdirs", "Dynlink"):
                raise ValueError("Untracked direct/dynamic loader in C1 source: " + name)
            if kind == "identifier" and value in ("needs", "loadt", "load_on_path"):
                if value == "load_on_path" or i + 1 == len(ts) or ts[i+1][0] != "string":
                    raise ValueError("Dynamic import is outside the closed graph: " + name)
                imports.append(resolve_import(ts[i+1][1]))
                aliases.append(ts[i+1][1])
        graph[name] = {"sha256": sha(p), "imports": imports, "import_mount_paths": aliases}
        for dependency in imports: visit(dependency)
        active.remove(name)
    visit(loader)
    return graph

def registry(root, mapping, graph=None):
    contract, e5 = anchors(root)
    literals = contract["statements-v1.ml"]
    if set(mapping) != set(literals) or len(set(mapping.values())) != 7:
        raise ValueError("Theorem map must cover the unchanged original seven targets uniquely")
    if any(not re.fullmatch(r"[A-Z][A-Za-z_0-9]*", v) for v in mapping.values()):
        raise ValueError("Unsafe theorem binding name")
    objects = [
        dict(name=mapping[target], target=target, category="original_c1", literal=literal,
             expected_literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),
             comparison="raw_closed_aconv")
        for target, literal in sorted(literals.items())
    ]
    helpers, witnesses, helper_files = helper_anchors(root)
    objects += [
        dict(name=target.removesuffix("_statement").upper(), target=target,
             category="nonvacuity_witness", literal=literal,
             expected_literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),
             comparison="raw_closed_aconv")
        for target, literal in sorted(witnesses.items())
    ]
    definitions = [
        dict(name=name, literal=literal,
             expected_literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),
             comparison="SPEC_ALL_closed_type_variable_alpha_only")
        for name, literal in sorted(contract["definitions-v1.ml"].items())
    ]
    definitions += [
        dict(name=row["name"], literal=row["equation"],
             expected_literal_sha256=row["equation_sha256"],
             comparison=row["check_mode"])
        for row in e5["rows"]
    ]
    definitions += [
        dict(name=name, literal=literal,
             expected_literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),
             comparison="SPEC_ALL_closed_type_variable_alpha_only")
        for name, literal in sorted(helpers.items())
    ]
    if len({r["name"] for r in objects + definitions}) != len(objects + definitions):
        raise ValueError("Overlapping theorem/definition binding names")
    if graph is not None:
        actual = {}
        for filename in graph:
            if not filename.startswith(OWN + "/"): continue
            for name, literal in definition_literals(checked(root, filename).read_text()).items():
                if name in actual: raise ValueError("Duplicate definition construction in load graph: " + name)
                actual[name] = literal
        expected = {r["name"]: r["literal"] for r in definitions}
        if actual != expected:
            raise ValueError("Closed graph contains missing/changed/unanchored definitions: " +
                             repr(sorted(set(actual) ^ set(expected))))
    return dict(schema="c1-fresh-exact-registry-v1", objects=objects,
                definitions=definitions, original_target_count=7,
                witness_target_count=21, nonvacuity_case_count=7,
                c1_definition_count=len(contract["definitions-v1.ml"]),
                e5_definition_count=7, helper_definition_count=14,
                helper_anchor_inputs=helper_files, caller_acceptance=False)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--loader", required=True)
    args = parser.parse_args()
    anchors(args.source_root.resolve())
    graph = load_graph(args.source_root.resolve(), args.loader)
    print(json.dumps(dict(status="PASS_SOURCE_AND_CLOSED_LOAD_GRAPH_NOT_PROOF",
                         loader=args.loader, graph=graph, caller_acceptance=False), indent=2))
