module

public import GS.CS.Angles
public import GS.CS.Bridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complete cosine-sine decomposition and scalar GS exhaustion

These are unconditional existence theorems. The proof constructs a common
spectral basis, completes normalized nonzero columns to orthonormal bases,
and recovers the remaining orthogonal complement. Singular values zero and
one, repeated singular values, and dimension zero are included.
-/

noncomputable section
open Matrix
namespace GS.Results.CosineSine

/-- Complete real cosine-sine decomposition in the classical angle form. -/
theorem square {p : ℕ}
    (Q : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ) (hQ : Orthogonal Q) :
    ∃ (U₁ U₂ V₁ V₂ : Mat p) (θ : Fin p → ℝ),
      Orthogonal U₁ ∧ Orthogonal U₂ ∧ Orthogonal V₁ ∧ Orthogonal V₂ ∧
      (∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi / 2) ∧
      Q = CS.split U₁ U₂ * CS.csMatrix (Real.cos ∘ θ) (Real.sin ∘ θ) *
        CS.split V₁ V₂ := CS.exists_square_cs_angles Q hQ

/-- The original three-factor scalar GS family with block sizes `p,2,p`
is exactly the full orthogonal group in dimension `2p`. -/
theorem scalar_exhaustion {p : ℕ} {M : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ M ↔ Orthogonal M :=
  CS.inA3Orth_scalar_two_iff

/-- Set equality version of scalar exhaustion, including `p=0`. -/
theorem scalar_family_eq_orthogonal (p : ℕ) :
    {M : Mat (2*p) | InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ M} = {M | Orthogonal M} :=
  CS.scalar_three_factor_family_eq_orthogonal p

end GS.Results.CosineSine
