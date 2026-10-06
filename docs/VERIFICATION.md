# Build and verification

The environment is pinned to Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
python3 scripts/fetch_cache.py
python3 scripts/verify.py --sequential
```

Run from the repository root with elan and Python 3 installed. The verifier:

1. Checks the compiler version, dependency pins and forbidden proof constructs.
2. Builds all 370 supported GS modules and the `GSChecked` entry point.
3. Imports the complete supported library and audits every safe kernel
   declaration, including private and generated declarations.
4. Traverses transitive axiom dependencies, permitting only `propext`,
   `Classical.choice` and `Quot.sound`.
5. Matches the original nonmanifold and cone specifications to their proofs,
   and rejects proof/configuration changes during verification.

Generated logs and reports go to `.lake/verification/full/`, outside the
version-controlled sources. The GitHub Actions workflow runs the same check.

For a selected module and its complete local import closure:

```sh
python3 scripts/verify_scope.py GS.UnitarySharing.GradientSection
```

The scoped report is written to `.lake/verification/scoped/`. A scoped check
does not cover unrelated modules. `python3 scripts/audit_source.py` performs
only a static inventory and writes to `.lake/verification/source/`.

The experimental SU files are excluded from the supported build. Definitions
ending in `Goal` specify propositions; theorems taking such propositions as
hypotheses do not prove those hypotheses. Consult [RESULTS.md](RESULTS.md) for
the exact unconditional results and conditional interfaces.

## CI diagnostics

The GitHub workflow builds project modules in dependency order with
`--sequential`, which limits concurrent project elaboration on hosted runners.
Every compiler message is streamed into the Actions step and saved under
`.lake/verification/full/`. A failed run uploads those diagnostics as a
short-lived Actions artifact; no generated report belongs in Git.

A red workflow summary or an exit code alone does not identify a proof error.
Open the failed build step and inspect the first Lean error and its module.
The local environment must match both `lean-toolchain` and `lake-manifest.json`.
