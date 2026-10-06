# Source and license

The Scarf and simplex Brouwer modules are adapted from
[math-xmum/Brouwer](https://github.com/math-xmum/Brouwer), commit
`c938f0f2b355adc9f07666c1c2c4002100406923` (2025-11-23), for Lean/mathlib
4.19.0. Copyright notices and the upstream MIT license are retained in
[THIRD_PARTY_LICENSE.txt](THIRD_PARTY_LICENSE.txt).

The proof uses finite indexed-order counting and an analytic limit to
establish a fixed point for every continuous self-map of
`stdSimplex ℝ (Fin n)` for positive `n`.
