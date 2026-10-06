module

public import GS.Unitary.PointGenerators

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A polynomial extension of the intrinsic unitary tangent projector

On every two-factor unitary orbit, the previously constructed real-Frobenius
projector agrees with an explicit polynomial expression in the base matrix
and ambient direction. Its ambient extension is jointly smooth and does not
use factor representatives. Arbitrary independent overlap is allowed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryManifold
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem leftPointProjection_residual_normal (b : Fin n → ℕ) (X Z C : CMat n)
    (hX : Unitary X) (hC : C ∈ supportedSkewSpace b) :
    cFrobInner (Z-leftPointProjection b X Z) (C*X) = 0 := by
  have he : Z-leftPointProjection b X Z = (Z*Xᴴ-blockSkew b (Z*Xᴴ))*X := by
    simp only [leftPointProjection, Matrix.sub_mul, Matrix.mul_assoc, hX.1,
      Matrix.mul_one]
  rw [he, cFrobInner_right_unitary X hX]
  exact maskedSkewHermitian_residual_orthogonal (Z*Xᴴ) C hC.1 hC.2

theorem rightPointProjection_residual_normal (b : Fin n → ℕ) (X Z Ω : CMat n)
    (hX : Unitary X) (hΩ : Ω ∈ supportedSkewSpace b) :
    cFrobInner (Z-rightPointProjection b X Z) (X*Ω) = 0 := by
  have he : Z-rightPointProjection b X Z = X*(Xᴴ*Z-blockSkew b (Xᴴ*Z)) := by
    simp only [rightPointProjection, Matrix.mul_sub, ← Matrix.mul_assoc, hX.2,
      Matrix.one_mul]
  rw [he, cFrobInner_left_unitary X hX]
  exact maskedSkewHermitian_residual_orthogonal (Xᴴ*Z) Ω hΩ.1 hΩ.2

/-- Exact equality with the existing orthogonal projector, not a new tangent definition. -/
theorem polynomialPointProjection_eq (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R) :
    let X := L*cPermMatrix σ*R
    polynomialPointProjection b₁ b₂ X Z = pointProjection b₁ b₂ X Z := by
  dsimp only
  symm
  let X := L*cPermMatrix σ*R
  have hX : Unitary X := (hL.mul (cPerm_unitary σ)).mul hR
  apply pointProjection_unique_normal
  · apply (mem_pointTangentSpace_iff b₁ b₂ X _).mpr
    refine ⟨balancedLeft b₁ b₂ X Z, ⟨balancedLeft_supported _ _ _ _,balancedLeft_skew _ _ _ _⟩,
      balancedRight b₁ b₂ X Z, ⟨balancedRight_supported _ _ _ _,balancedRight_skew _ _ _ _⟩, ?_⟩
    exact balanced_reconstruct_polynomial b₁ b₂ σ L R Z hsL hsR hL hR
  · intro W hW
    obtain ⟨C,hC,Ω,hΩ,rfl⟩ := (mem_pointTangentSpace_iff b₁ b₂ X W).mp hW
    rw [cFrobInner_add_right]
    have hl : cFrobInner (Z-polynomialPointProjection b₁ b₂ X Z) (C*X) = 0 := by
      have he : Z-polynomialPointProjection b₁ b₂ X Z =
          (Z-leftPointProjection b₂ X Z) -
            (rightPointProjection b₁ X Z-leftPointProjection b₂ X (rightPointProjection b₁ X Z)) := by
        unfold polynomialPointProjection
        abel
      rw [he,cFrobInner_sub_left,leftPointProjection_residual_normal b₂ X Z C hX hC,
        leftPointProjection_residual_normal b₂ X (rightPointProjection b₁ X Z) C hX hC]
      ring
    have hr : cFrobInner (Z-polynomialPointProjection b₁ b₂ X Z) (X*Ω) = 0 := by
      have he : Z-polynomialPointProjection b₁ b₂ X Z =
          (Z-rightPointProjection b₁ X Z) -
            (leftPointProjection b₂ X Z-rightPointProjection b₁ X (leftPointProjection b₂ X Z)) := by
        unfold polynomialPointProjection
        have hc : leftPointProjection b₂ X (rightPointProjection b₁ X Z) =
            rightPointProjection b₁ X (leftPointProjection b₂ X Z) :=
          pointProjectors_commute b₁ b₂ σ L R Z hsL hsR hL hR
        rw [hc]
        abel
      rw [he,cFrobInner_sub_left,rightPointProjection_residual_normal b₁ X Z Ω hX hΩ,
        rightPointProjection_residual_normal b₁ X (leftPointProjection b₂ X Z) Ω hX hΩ]
      ring
    exact by rw [hl,hr,add_zero]

theorem polynomialPointProjection_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun p : CMat n × CMat n => polynomialPointProjection b₁ b₂ p.1 p.2) := by
  have hl := contDiff_leftPointProjection b₂ (n := n) contDiff_fst contDiff_snd
  have hr := contDiff_rightPointProjection b₁ (n := n) contDiff_fst contDiff_snd
  exact (hl.add hr).sub (contDiff_leftPointProjection b₂ contDiff_fst hr)

end GS.UnitaryGeometry
