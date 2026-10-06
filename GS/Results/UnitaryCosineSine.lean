module

public import GS.UnitaryCS.Angles
public import GS.UnitaryCS.Bridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complete unitary cosine-sine decomposition and exact scalar GS exhaustion

All existence statements are unconditional. The proof constructs a Hermitian
spectral basis, completes every prescribed normalized nonzero column, and
recovers the complementary columns using unitarity. Zero and unit singular
values, repeated singular values, and dimension zero are included.
-/

noncomputable section
open Matrix GS.UnitaryGeometry
namespace GS.Results.UnitaryCosineSine

/-- Complete complex cosine-sine decomposition with real angles in [0, pi/2]. -/
theorem square {p : ℕ}
    (Q : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℂ)
    (hQ : Qᴴ * Q = 1 ∧ Q * Qᴴ = 1) :
    ∃ (U₁ U₂ V₁ V₂ : CMat p) (θ : Fin p → ℝ),
      Unitary U₁ ∧ Unitary U₂ ∧ Unitary V₁ ∧ Unitary V₂ ∧
      (∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi / 2) ∧
      Q = UnitaryCS.split U₁ U₂ *
        UnitaryCS.csMatrix (Real.cos ∘ θ) (Real.sin ∘ θ) *
        UnitaryCS.split V₁ V₂ := UnitaryCS.exists_square_cs_angles Q hQ

/-- The original three-factor scalar GS family with block sizes p,2,p
equals the full unitary group in dimension 2p, for the specified shuffle. -/
theorem scalar_exhaustion {p : ℕ} {M : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ M ↔ Unitary M :=
  UnitaryCS.inA3Unitary_scalar_two_iff

/-- Set equality, including p = 0. -/
theorem scalar_family_eq_unitary (p : ℕ) :
    {M : CMat (2*p) | CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ M} = {M | Unitary M} :=
  UnitaryCS.scalar_three_factor_family_eq_unitary p

end GS.Results.UnitaryCosineSine
