module

public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Frobenius

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The real Frobenius metric on unitary generator images

The cross term is retained unless an explicit orthogonality hypothesis removes
it. In particular, complex block generators can share imaginary diagonal
directions. The exact kernel formulas below account for this overlap.
-/

noncomputable section
open Matrix

namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem cFrobInner_boundary (L R : CMat n) (hL : Unitary L) (hR : Unitary R)
    (A B : CMat n) : cFrobInner (L*A*R) (L*B*R) = cFrobInner A B := by
  rw [cFrobInner_right_unitary _ hR, cFrobInner_left_unitary _ hL]

theorem cFrobSq_boundary (L R : CMat n) (hL : Unitary L) (hR : Unitary R)
    (A : CMat n) : cFrobSq (L*A*R) = cFrobSq A :=
  cFrobInner_boundary L R hL hR A A

theorem cFrobInner_conjugate (P : CMat n) (hP : Unitary P) (A B : CMat n) :
    cFrobInner (P*A*Pᴴ) (P*B*Pᴴ) = cFrobInner A B :=
  cFrobInner_boundary P Pᴴ hP hP.conjTranspose A B

theorem cFrobSq_conjugate (P : CMat n) (hP : Unitary P) (A : CMat n) :
    cFrobSq (P*A*Pᴴ) = cFrobSq A :=
  cFrobInner_conjugate P hP A A

/-- Cancellation of both unitary boundary factors. -/
theorem unitary_boundary_cancel (L R A : CMat n) (hL : Unitary L) (hR : Unitary R) :
    Lᴴ*(L*A*R)*Rᴴ = A := by
  calc
    Lᴴ*(L*A*R)*Rᴴ = (Lᴴ*L)*A*(R*Rᴴ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hL.1,hR.2]; simp

theorem unitary_boundary_zero_iff (L R A : CMat n)
    (hL : Unitary L) (hR : Unitary R) : L*A*R = 0 ↔ A = 0 := by
  constructor
  · intro h
    have he := unitary_boundary_cancel L R A hL hR
    rw [h] at he
    simpa using he.symm
  · rintro rfl; simp

/-- Pulling back an ambient vector is adjoint to applying the boundaries. -/
theorem cFrobInner_pullback (L R A Z : CMat n) :
    cFrobInner (L*A*R) Z = cFrobInner A (Lᴴ*Z*Rᴴ) := by
  calc
    cFrobInner (L*A*R) Z = cFrobInner (L*A*R)ᴴ Zᴴ :=
      (cFrobInner_conjTranspose _ _).symm
    _ = cFrobInner ((L*A)ᴴ) (R*Zᴴ) := by
      rw [Matrix.conjTranspose_mul, cFrobInner_mul_left,
        Matrix.conjTranspose_conjTranspose]
    _ = cFrobInner (L*A) (Z*Rᴴ) := by
      rw [← cFrobInner_conjTranspose (L*A) (Z*Rᴴ)]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = cFrobInner A (Lᴴ*Z*Rᴴ) := by
      rw [cFrobInner_mul_left, Matrix.mul_assoc]

/-- Exact four-term metric in the two generator parameters. -/
theorem tangentParam_inner (B₂ P B₁ C Ω D Ξ : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    cFrobInner (tangentParam B₂ P B₁ C Ω) (tangentParam B₂ P B₁ D Ξ) =
      cFrobInner C D + cFrobInner C (P*Ξ*Pᴴ) +
      cFrobInner (P*Ω*Pᴴ) D + cFrobInner Ω Ξ := by
  rw [tangentParam_factored _ _ _ _ _ hP, tangentParam_factored _ _ _ _ _ hP,
    cFrobInner_boundary _ _ h₂ (hP.mul h₁), cFrobInner_add_left,
    cFrobInner_add_right, cFrobInner_add_right, cFrobInner_conjugate _ hP]
  ring

/-- The quadratic form includes the full overlap cross term. -/
theorem tangentParam_frobSq_cross (B₂ P B₁ C Ω : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    cFrobSq (tangentParam B₂ P B₁ C Ω) =
      cFrobSq C + 2*cFrobInner C (P*Ω*Pᴴ) + cFrobSq Ω := by
  rw [tangentParam_factored _ _ _ _ _ hP,
    cFrobSq_boundary _ _ h₂ (hP.mul h₁), cFrobSq_add, cFrobSq_conjugate _ hP]

/-- Orthogonal generator directions have additive squared Frobenius norm. -/
theorem tangentParam_frobSq (B₂ P B₁ C Ω : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁)
    (hcross : cFrobInner C (P*Ω*Pᴴ) = 0) :
    cFrobSq (tangentParam B₂ P B₁ C Ω) = cFrobSq C + cFrobSq Ω := by
  rw [tangentParam_frobSq_cross _ _ _ _ _ h₂ hP h₁, hcross]
  ring

theorem tangentParam_eq_zero_iff_core (B₂ P B₁ C Ω : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    tangentParam B₂ P B₁ C Ω = 0 ↔ C + P*Ω*Pᴴ = 0 := by
  rw [tangentParam_factored _ _ _ _ _ hP]
  exact unitary_boundary_zero_iff _ _ _ h₂ (hP.mul h₁)

/-- Exact overlap kernel, with no disjointness assumption. -/
theorem tangentCore_eq_zero_iff (P C Ω : CMat n) (hP : Unitary P) :
    C + P*Ω*Pᴴ = 0 ↔ Ω = -(Pᴴ*C*P) := by
  constructor
  · intro h
    have hc : P*Ω*Pᴴ = -C := (add_eq_zero_iff_eq_neg').mp h
    calc
      Ω = Pᴴ*(P*Ω*Pᴴ)*P :=
        by simpa using (unitary_boundary_cancel P Pᴴ Ω hP hP.conjTranspose).symm
      _ = -(Pᴴ*C*P) := by rw [hc]; simp
  · rintro rfl
    have hc : P*(Pᴴ*C*P)*Pᴴ = C :=
      by simpa using unitary_boundary_cancel Pᴴ P C hP.conjTranspose hP
    rw [Matrix.mul_neg, Matrix.neg_mul, hc]
    simp

theorem tangentParam_eq_zero_iff (B₂ P B₁ C Ω : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    tangentParam B₂ P B₁ C Ω = 0 ↔ Ω = -(Pᴴ*C*P) := by
  rw [tangentParam_eq_zero_iff_core _ _ _ _ _ h₂ hP h₁,
    tangentCore_eq_zero_iff _ _ _ hP]

theorem tangentParam_frobSq_eq_zero_iff (B₂ P B₁ C Ω : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    cFrobSq (tangentParam B₂ P B₁ C Ω) = 0 ↔ Ω = -(Pᴴ*C*P) := by
  rw [cFrobSq_eq_zero_iff, tangentParam_eq_zero_iff _ _ _ _ _ h₂ hP h₁]

theorem mem_tangentCoreMap_ker_iff (block₁ block₂ : Fin n → ℕ) (P : CMat n)
    (hP : Unitary P) (v : supportedSkewSpace block₂ × supportedSkewSpace block₁) :
    v ∈ LinearMap.ker (tangentCoreMap block₁ block₂ P) ↔
      v.2.val = -(Pᴴ*v.1.val*P) :=
  tangentCore_eq_zero_iff P v.1.val v.2.val hP

theorem mem_tangentParamMap_ker_iff (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁)
    (v : supportedSkewSpace block₂ × supportedSkewSpace block₁) :
    v ∈ LinearMap.ker (tangentParamMap block₁ block₂ B₂ P B₁) ↔
      v.2.val = -(Pᴴ*v.1.val*P) :=
  tangentParam_eq_zero_iff B₂ P B₁ v.1.val v.2.val h₂ hP h₁

/-- The generator ambiguity is independent of the two unitary boundary factors. -/
theorem tangentParamMap_ker_eq_core (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n)
    (h₂ : Unitary B₂) (hP : Unitary P) (h₁ : Unitary B₁) :
    LinearMap.ker (tangentParamMap block₁ block₂ B₂ P B₁) =
      LinearMap.ker (tangentCoreMap block₁ block₂ P) := by
  ext v
  rw [mem_tangentParamMap_ker_iff _ _ _ _ _ h₂ hP h₁,
    mem_tangentCoreMap_ker_iff _ _ _ hP]

end GS.UnitaryGeometry
