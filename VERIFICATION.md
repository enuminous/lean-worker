# Reproducible Lean verification

Use the committed toolchain and dependency manifest. The workflow restores
applicable caches, builds the configured library, and audits every safe
declaration defined in the project modules listed in `Audit.lean`, including
private declarations. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/test_axiom_audit.py
```

The rejection controls inject a public axiom, private axiom and placeholder proof
and require the audit to fail for the intended reason.
Native proof evaluation is also rejected.

The successful job summary records the exact commit and workflow run. Source
declarations and hypotheses determine the mathematical scope; a successful
build does not validate a broader empirical or scientific interpretation.

## Explicit correction of a false bound

The former `output_bounded` claimed that **every** arbitrary `ExecResult` had
at most 5000 characters of output. The record imposed no such restriction, so
that statement was false. `arbitrary_result_not_bounded` supplies a checked
counterexample. The replacement theorem quantifies results produced by
`makeResult`, which is the intended construction guarantee.

The old truncator also appended three dots after taking 5000 characters,
exceeding its own limit. The result now contains at most the limit and records
truncation in the existing Boolean flag. The bound counts Unicode characters,
not UTF-8 bytes. This behavior and theorem-scope change is intentional and is
not presented as a proof of the old statement.

The two Twin placeholders were constant-record equalities and are now proved by
reflexivity. These equalities do not certify live telemetry, provenance, or
runtime enforcement; the model remains conditional on the supplied records.

The former sponsor-persistence equation referred to a nonexistent field of
`Environment`. Its replacement checks only the supplied sponsor record's Boolean
flag; persistence of the running infrastructure is not established. The model
consistency proposition now states the equalities themselves, instead of using
proof terms where propositions were required. These typing and scope corrections
are explicit, and the external-world claims remain outside the formal model.
