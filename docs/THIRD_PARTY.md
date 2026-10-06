# Third-party proofs and attribution

The proof dependency is mathlib, pinned by `lean-toolchain`, `lakefile.lean` and
`lake-manifest.json` to Lean 4.19.0 and the corresponding mathlib revision.

The project also contains source ports needed by the topological argument:

| Source | Local location | Attribution |
| --- | --- | --- |
| Scarf and Brouwer proof from `math-xmum/Brouwer`, commit `c938f0f2b355adc9f07666c1c2c4002100406923` | `GS/Topology/Brouwer/` | [Provenance](../GS/Topology/Brouwer/PROVENANCE.md) and [MIT licence](../GS/Topology/Brouwer/THIRD_PARTY_LICENSE.txt) |
| Mathlib-derived homotopy support | `GS/Topology/SingularHomotopy*.lean` | Individual source headers and [Apache 2.0 licence](../GS/Topology/THIRD_PARTY_LICENSE_APACHE_2_0.txt) |

The root [MIT License](../LICENSE) covers the project code. Reused sources
retain their existing copyright headers and applicable licenses. Keep the
adjacent license and provenance files when redistributing those sources.
The project license does not relicense the paper or dependencies.
