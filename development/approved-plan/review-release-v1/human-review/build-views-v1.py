#!/usr/bin/env python3
"""Copy literal and expanded accepted evidence into an additive review view.

This is documentation extraction, not a proof or an acceptance driver.
It never writes to accepted inputs. All new outputs use exclusive creation.
"""
import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.source_root.resolve()
    dest = root / "development/approved-plan/review-release-v1/human-review"
    sources = {}

    def source(path):
        p = root / path
        sources[path] = {"path": path, "sha256": sha(p), "bytes": p.stat().st_size}
        return p

    def readjson(path):
        return json.loads(source(path).read_text())

    def literals(path, definitions=False):
        text = source(path).read_text()
        middle = r"new_definition\s*" if definitions else ""
        return dict(re.findall(r"let\s+(\w+)\s*=\s*" + middle + r"`([\s\S]*?)`;;", text))

    cases = {
        "C1": {
            "statements": "development/approved-plan/reusable-assurance-v1/c1/contract/statements-v1.ml",
            "definitions": "development/approved-plan/reusable-assurance-v1/c1/contract/definitions-v1.ml",
            "audit": "development/approved-plan/reusable-assurance-c1-successor-v1/runs/c1-fresh-final-v3/runtime/c1-live-audit-v1.json",
            "gate": "development/approved-plan/reusable-assurance-c1-successor-v1/runs/c1-fresh-final-v3/root-full-acceptance-v1.json",
        },
        "C2": {
            "statements": "development/approved-plan/reusable-assurance-c2-v1/spec/statements-v1.ml",
            "definitions": "development/approved-plan/reusable-assurance-c2-v1/spec/definitions-v1.ml",
            "audit": "development/approved-plan/reusable-assurance-c2-v1/runs/c2-fresh-final-v1/runtime/c2-live-audit-v1.json",
            "gate": "development/approved-plan/reusable-assurance-c2-v1/runs/c2-root-full-acceptance-final-v1.json",
        },
        "C3": {
            "statements": "development/approved-plan/held-out-transfer-v1/c3/contract/statements-v1.ml",
            "definitions": "development/approved-plan/held-out-transfer-v1/c3/contract/definitions-v2.ml",
            "audit": "development/approved-plan/c3-successor-v1/runs/fresh-final-v1/runtime/c3-live-audit-v1.json",
            "gate": "development/approved-plan/c3-successor-v1/results/complete-gate-final-v1.json",
        },
    }
    rows = {}
    md = ["# Literal caller contracts and access/frame predicates", "",
          "Human review: **PENDING**. This view copies frozen statements and definitions without changing them. It is documentation, not a new acceptance input. `contracts-and-rules-v1.json` retains the exact accepted live conclusions and expanded terms, with source digests. The original sources and complete gates remain controlling.", ""]
    for case, config in cases.items():
        audit = readjson(config["audit"])
        gate = readjson(config["gate"])
        assert gate["full_" + case + "_acceptance"] is True
        assert gate["human_review"] == "PENDING"
        assert audit["axioms_unchanged"] is True
        assert set(audit["standard_axioms"]) == {"INFINITY_AX", "SELECT_AX", "ETA_AX"}
        statements = literals(config["statements"])
        defs = literals(config["definitions"], True)
        assert len(statements) == 7, (case, len(statements))
        target_rows = [r for r in audit["rows"] if r["kind"] == "object"][:7]
        assert all(r["literal_match"] and r["expanded_match"] and
                   r["hypothesis_count"] == 0 and r["free_variable_count"] == 0
                   and r["new_axioms"] == 0 for r in target_rows)
        rows[case] = {
            "source": config,
            "accepted_package_status": gate["status"],
            "literal_frozen_statements": statements,
            "literal_frozen_caller_definitions": defs,
            "accepted_live_target_rows": target_rows,
            "accepted_live_definition_rows": [r for r in audit["rows"] if r["kind"] == "definition"],
            "entry_witnesses_are_not_execution": True,
        }
        md += ["## " + case, "", "Controlling frozen sources: `" + config["statements"] + "` and `" + config["definitions"] + "`.", ""]
        for name, term in statements.items():
            md += ["### " + name, "", "```text", term, "```", ""]
        prefix = case.lower()
        wanted = [prefix + s for s in ["_pre", "_allowed_read", "_allowed_write", "_allowed_fetch", "_frame", "_scalar_post", "_public_post", "_step_policy", "_got"]]
        if case == "C1":
            wanted += ["c1_call_slot", "c1_crypto_ready"]
        else:
            wanted += [prefix + "_scratch", prefix + "_equal"]
        if case == "C3":
            wanted += ["c3_cleansed_memory", "c3_result", "c3_crypto_ready"]
        for name in wanted:
            assert name in defs, name
            md += ["### " + name, "", "```text", defs[name], "```", ""]

    generic_path = "development/approved-plan/held-out-transfer-v1/human-review/live-generic-rules-v1.json"
    generic = readjson(generic_path)
    exports = generic["rows"][0]["actual_live_formal_exports"]
    assert len(exports) == 34
    for row in generic["rows"]:
        assert row["hypotheses_zero"] and row["frees_zero"] and row["standard3_unchanged"]
    assert [x["conclusion"] for x in exports] == [x["conclusion"] for x in generic["rows"][1]["actual_live_formal_exports"]]
    supplier = {}
    runtime = "development/approved-plan/c3-successor-v1/runs/fresh-final-v1/runtime/"
    for name in ["e3-interface.json", "public-interface-audit.json", "public-trace-audit.json", "cleanse-interface.json", "full-binding-audit.json"]:
        supplier[name] = readjson(runtime + name)

    common = {}
    common_sources = {
        "development/approved-plan/assurance/path.ml": ["assurance_checked_run", "assurance_step_policy", "assurance_zero_step"],
        "development/approved-plan/assurance/policy.ml": ["assurance_canonical48", "assurance_region", "assurance_span_ok", "assurance_event_policy", "assurance_fetch_policy"],
        "development/approved-plan/assurance/correspondence.ml": ["assurance_actual_ret"],
        "development/approved-plan/reusable-assurance-v1/generic/e5-definitions-v1.ml": ["e5_normal_flags", "e5_rf_clear", "e5_rf_retired_step", "e5_rf_retired_extended_step", "e5_normal_step_policy", "e5_normal_environment", "e5_rf_checked_run"],
    }
    for path, names in common_sources.items():
        text = source(path).read_text()
        for name in names:
            pattern = r"let\s+" + name + r"\s*=\s*(?:new_definition|new_recursive_definition\s+num_RECURSION)\s*`([\s\S]*?)`;;"
            match = re.search(pattern, text)
            assert match, (path, name)
            common[name] = {"source": path, "literal_equation": match[1]}

    for path in [
        "TRUST.md", "development/approved-plan/TRUST-E2-v2.md", "spec/e5/CLAIM-CHANGES-v1.md",
        "development/approved-plan/normal-entry-e5-v1/PHYSICAL-DOMAIN-v1.md",
        "development/approved-plan/held-out-transfer-v1/layer/CLASS-AND-EXTENSION-POINTS-v1.md",
        "development/approved-plan/held-out-transfer-v1/layer/PUBLIC-SURFACE-v1.md",
        "development/approved-plan/held-out-transfer-v1/layer/freeze-v1.json",
        "development/approved-plan/held-out-transfer-v1/layer/exports-v1.json",
        "development/approved-plan/held-out-transfer-v1/layer/dependencies-v1.json",
        "development/approved-plan/c3-successor-v1/proofs/final-mov2-site-v2.ml",
        "development/approved-plan/c3-successor-v1/proofs/final-return-site-steps-v7.ml",
        "development/approved-plan/c3-successor-v1/status/selected-reuse-account-v1.json",
        "development/approved-plan/c3-successor-v1/results/dependency-map-v2.json",
        "development/approved-plan/c3-successor-v1/diagnostics/transport-final-selected-graph-review-v2.json",
    ]:
        source(path)

    review = {
        "schema": "review-release-literal-expanded-view-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "human_review": "PENDING",
        "view_is_acceptance_input": False,
        "view_is_independent_replay": False,
        "cases": rows,
        "common_literal_definitions": common,
        "candidate_live_exports": exports,
        "candidate_regression_source": generic_path,
        "supplier_live_views": supplier,
        "source_map": sorted(sources.values(), key=lambda x: x["path"]),
        "opacity": "Inspection-qualified source discipline; ambient theorem namespace and supplier code definitions remain accessible. No formal derivation/capability isolation claimed.",
    }
    for filename, content in [
        ("contracts-and-rules-v1.json", json.dumps(review, indent=2) + "\n"),
        ("LITERAL-CONTRACTS-v1.md", "\n".join(md) + "\n"),
        ("source-map-v1.json", json.dumps({"schema": "review-source-map-v1", "human_review": "PENDING", "rows": review["source_map"]}, indent=2) + "\n"),
    ]:
        with (dest / filename).open("x") as f:
            f.write(content)
    print(json.dumps({"status": "DOCUMENTATION_EXTRACTION_COMPLETE_NOT_PROOF_ACCEPTANCE", "cases": list(cases), "candidate_exports": len(exports), "source_count": len(sources)}, indent=2))


if __name__ == "__main__":
    main()
