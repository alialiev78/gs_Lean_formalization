# Publishing the GS formalization

This is the full Lean 4.19.0 development accompanying Ali Aliev and Maxim
Rakhuba, *Riemannian Structure and Optimization for a Class of Low-Parametric
Orthogonal Matrices*, [arXiv:2609.27982](https://arxiv.org/abs/2609.27982).
The [coverage map](PAPER_COVERAGE.md) distinguishes the paper's results,
additional developments and omissions. The README's ChatGPT acknowledgement
and the applicable source and dependency licenses must remain in the release.
No development transcripts or historical verification logs are required.

## 1. Publish or update the GitHub repository

The existing repository is
[alialiev78/gs_Lean_formalization](https://github.com/alialiev78/gs_Lean_formalization).
For a new checkout:

```sh
git clone https://github.com/alialiev78/gs_Lean_formalization.git
cd gs_Lean_formalization
```

Extract the release archive to a temporary directory. Copy the **contents** of
its `gs_lean4` directory into the repository root, replacing the corresponding
files. Include `.github/workflows/lean.yml` and `.gitignore`; graphical file
managers may hide them. Keep the repository's `.git` directory. Do not upload
the ZIP as the repository's only file and do not introduce an extra directory
above `lean-toolchain` and `lakefile.lean`.

Inspect and commit the changes:

```sh
git status --short
git diff --stat
git diff -- README.md LICENSE .github/workflows/lean.yml
git add README.md LICENSE lean-toolchain lakefile.lean lake-manifest.json
git add GS*.lean GS docs scripts experimental .github .gitignore
git status --short
git commit -m "Prepare reproducible publication build"
git push origin main
```

Stage any other intended root source files shown by `git status`. Do not stage
`.lake/`, compiler outputs, downloaded dependencies or temporary logs.
GitHub Desktop can perform the same steps: open the clone, copy the files,
review the Changes tab, commit and push.

## 2. Verify the exact public commit

Install elan and Python 3. The project chooses its own pinned toolchain; do not
run `lake update` simply to repair a failed build, because it changes dependency
versions.

```sh
python3 scripts/fetch_cache.py
python3 scripts/verify.py --sequential
```

The workflow runs the same verification on `ubuntu-24.04`, builds local modules
in dependency order and restricts Lean worker threads. It audits the transitive
axioms of all supported kernel declarations. Experimental SU files remain
outside the supported build. The check must finish successfully before the
release is described as verified.

On GitHub, open **Actions → Lean checked formalization → the latest run →
check**. Wait for all required steps to pass. If the run fails, expand
**Build supported modules and audit axioms**, read the first actual Lean or
Python error, and download the `lean-diagnostics-…` artifact from the run page.
It contains the current status and individual build logs. These artifacts are
short-lived diagnostics and are not committed to the repository.

An `exit code 1` summary alone does not identify the cause. A Node.js deprecation
warning from a completed checkout step is not itself a proof failure. The
workflow pins a current checkout action and a fixed Ubuntu image to remove
those unrelated migration warnings.

After a green run, record its commit:

```sh
git rev-parse HEAD
```

A GitHub release is optional. If desired, tag the checked commit and attach the
source ZIP as a release asset; the repository must still contain the unpacked
sources.

## 3. Palomar is a separate verification target

The Palomar policy consulted on 2026-10-05 requires Lean **4.35.0-rc2 or later**,
new-module-system source files, a compact independent `Challenge.lean`, a
complete `Solution.lean`, `comparator.json`, and `formalization.yaml`.
This complete Lean 4.19 project is **not** directly eligible under that policy.
Adding metadata does not migrate its proofs or make it pass Comparator.

The accompanying `gs_algebra_palomar.zip` is a separate project for a first,
focused registration: two-factor orthogonalization, three-factor
orthogonalization and the four-factor counterexample. It contains their proof
sources locally, uses the required newer toolchain and has its own submission
instructions. Its claims do not cover this repository's geometry, topology,
unitary extensions or optimization library.

For a future whole-library registration, port and verify the complete source
set, construct suitable independent statement files, and update the scope
metadata. Current Palomar source rules also cover unused experimental `.lean`
files in a submitted repository; merely excluding them from a build is not
a module-system migration.

## Policy references

- [Contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Editorial floor](https://palomar-registry.org/about#editorial-floor)
- [Submission procedure](https://palomar-registry.org/how-to-submit)
- [Accepted toolchains](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json)
- [Current template](https://github.com/PalomarRegistry/PalomarTemplate)

Recheck these live requirements immediately before submitting. Passing the
mechanical checks is necessary but does not guarantee editorial acceptance.
