#!/usr/bin/env python3
"""Compare observed automation tables; do not infer a theorem dependency graph."""
import argparse, collections, datetime, hashlib, json
from pathlib import Path

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def key(row): return json.dumps(row, sort_keys=True, separators=(",", ":"))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    before, after = [json.loads(path.read_text()) for path in [args.before, args.after]]
    if any(item["schema"] != "c1-ambient-automation-snapshot-v1" for item in [before, after]):
        raise ValueError("Unexpected ambient snapshot schema")
    if before["label"] != "before-supplier" or after["label"] != "after-supplier-before-caller":
        raise ValueError("Snapshot boundaries are not the requested supplier interval")
    rows = {}
    keywords = ["crypto", "memcmp", "cleanse"]
    addresses = ["0x10241840", str(0x10241840)]
    for table in ["basic_rewrites", "basic_congruences", "basic_conversions"]:
        old = collections.Counter(map(key, before[table])); new = collections.Counter(map(key, after[table]))
        added = [json.loads(row) for row, count in (new-old).items() for _ in range(count)]
        removed = [json.loads(row) for row, count in (old-new).items() for _ in range(count)]
        family = [row for row in after[table] if any(word in key(row).lower() for word in keywords)]
        concrete = [row for row in after[table] if any(address in key(row).lower() for address in addresses)]
        rows[table] = dict(before_count=len(before[table]), after_count=len(after[table]),
            added_count=len(added), removed_count=len(removed), sequence_changed=before[table]!=after[table],
            added_rows=added, removed_rows=removed, visible_crypto_cleanse_family_rows=family,
            visible_canonical_crypto_address_rows=concrete)
    result = dict(schema="c1-successor-ambient-automation-observation-v1",
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        before={"path":str(args.before), "sha256":sha(args.before)},
        after={"path":str(args.after), "sha256":sha(args.after)}, tables=rows,
        axioms_exactly_unchanged=before["axioms"]==after["axioms"],
        before_axiom_count=len(before["axioms"]), after_axiom_count=len(after["axioms"]),
        visible_keyword_policy=keywords, visible_address_policy=addresses,
        conversion_closure_dependencies_observable=False, tactic_closure_dependencies_observable=False,
        all_ambient_named_theorems_enumerated=False, formal_dependency_isolation=False,
        semantic_theorem_sensitivity=False,
        scope="Observed ordered basic rewrite/congruence/conversion tables only; no kernel proof dependency claim")
    with args.output.open("x") as stream: stream.write(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(dict(status="AMBIENT_TABLE_OBSERVATION_RECORDED_NOT_DEPENDENCY_PROOF",
        result_sha256=sha(args.output), tables={name:{k:v for k,v in row.items() if not k.endswith("rows")}
        for name,row in rows.items()}, axioms_exactly_unchanged=result["axioms_exactly_unchanged"]), indent=2))

if __name__ == "__main__": main()
