module

public import GS.Continuation.ExponentialBasics
public import GS.Extensions.GeodesicNormal

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Concrete exponential curves for m=2

The matrix exponential curves satisfy their defining ODEs, preserve
orthogonality, and have normal acceleration under the stated hypotheses.

This is NOT an assertion that the singular general m=3 family has geodesics.
Nor is the explicit generator image defined to be a manifold tangent space.
The embedded-orbit theorem and the intrinsic/extrinsic geodesic bridge remain
separate obligations.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def gsExpLeft (B₂ C : Mat n) (t : ℝ) : Mat n := B₂ * expLine C t

def gsExpRight (B₁ Ω : Mat n) (t : ℝ) : Mat n := expLine Ω t * B₁

def gsExpCurve (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  product2 (gsExpLeft B₂ C t) P (gsExpRight B₁ Ω t)

def gsExpVelocity (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t) (C + P * Ω * Pᵀ)

def gsExpAcceleration (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    (accelerationCore C (P * Ω * Pᵀ))

@[simp] theorem gsExpLeft_zero (B₂ C : Mat n) : gsExpLeft B₂ C 0 = B₂ := by
  simp only [gsExpLeft, expLine_zero, Matrix.mul_one]

@[simp] theorem gsExpRight_zero (B₁ Ω : Mat n) : gsExpRight B₁ Ω 0 = B₁ := by
  simp only [gsExpRight, expLine_zero, Matrix.one_mul]

@[simp] theorem gsExpCurve_zero (B₂ P B₁ C Ω : Mat n) :
    gsExpCurve B₂ P B₁ C Ω 0 = product2 B₂ P B₁ := by
  simp only [gsExpCurve, gsExpLeft_zero, gsExpRight_zero]

theorem gsExpLeft_supported {block : Fin n → ℕ} (B₂ C : Mat n)
    (hB₂ : Supported block B₂) (hC : Supported block C) (t : ℝ) :
    Supported block (gsExpLeft B₂ C t) := hB₂.mul (expLine_supported hC t)

theorem gsExpRight_supported {block : Fin n → ℕ} (B₁ Ω : Mat n)
    (hB₁ : Supported block B₁) (hΩ : Supported block Ω) (t : ℝ) :
    Supported block (gsExpRight B₁ Ω t) := (expLine_supported hΩ t).mul hB₁

theorem gsExpLeft_orthogonal (B₂ C : Mat n) (hB₂ : Orthogonal B₂)
    (hC : IsSkew C) (t : ℝ) : Orthogonal (gsExpLeft B₂ C t) :=
  hB₂.mul (expLine_orthogonal hC t)

theorem gsExpRight_orthogonal (B₁ Ω : Mat n) (hB₁ : Orthogonal B₁)
    (hΩ : IsSkew Ω) (t : ℝ) : Orthogonal (gsExpRight B₁ Ω t) :=
  (expLine_orthogonal hΩ t).mul hB₁

theorem gsExpCurve_orthogonal (B₂ P B₁ C Ω : Mat n)
    (hB₂ : Orthogonal B₂) (hP : Orthogonal P) (hB₁ : Orthogonal B₁)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    Orthogonal (gsExpCurve B₂ P B₁ C Ω t) :=
  ((gsExpLeft_orthogonal B₂ C hB₂ hC t).mul hP).mul
    (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t)

/-- The explicit curve stays in the unchanged InA2Orth definition for all t. -/
theorem gsExpCurve_inA2Orth (b₁ b₂ : ℕ) (B₂ P B₁ C Ω : Mat n)
    (hs₂ : BlockDiagonal b₂ B₂) (hs₁ : BlockDiagonal b₁ B₁)
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hsC : BlockDiagonal b₂ C) (hsΩ : BlockDiagonal b₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    InA2Orth b₁ b₂ P (gsExpCurve B₂ P B₁ C Ω t) := by
  refine ⟨gsExpRight B₁ Ω t, gsExpLeft B₂ C t, ?_, ?_, ?_, ?_, rfl⟩
  · exact gsExpRight_supported B₁ Ω hs₁ hsΩ t
  · exact gsExpLeft_supported B₂ C hs₂ hsC t
  · exact gsExpRight_orthogonal B₁ Ω hB₁ hΩ t
  · exact gsExpLeft_orthogonal B₂ C hB₂ hC t

theorem gsExpLeft_hasDerivAt (B₂ C : Mat n) (t : ℝ) :
    HasDerivAt (gsExpLeft B₂ C) (gsExpLeft B₂ C t * C) t := by
  unfold gsExpLeft
  simpa only [ Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    hasDerivAt_matrix_mul (hasDerivAt_const t B₂) (hasDerivAt_expLine C t)

theorem gsExpRight_hasDerivAt (B₁ Ω : Mat n) (t : ℝ) :
    HasDerivAt (gsExpRight B₁ Ω) (Ω * gsExpRight B₁ Ω t) t := by
  unfold gsExpRight
  simpa only [ Matrix.mul_zero, add_zero, Matrix.mul_assoc] using
    hasDerivAt_matrix_mul (hasDerivAt_expLine_left Ω t) (hasDerivAt_const t B₁)

/-- The carrier P exp(t Omega) B1 has the constant left generator P Omega P^T. -/
theorem gsExpCarrier_hasDerivAt (P B₁ Ω : Mat n) (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P * gsExpRight B₁ Ω s)
      ((P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t)) t := by
  have he : (P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t) =
      P * (Ω * gsExpRight B₁ Ω t) := by
    calc
      _ = P * Ω * (Pᵀ * P) * gsExpRight B₁ Ω t := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP.1]; simp [Matrix.mul_assoc]
  rw [he]
  simpa only [Matrix.zero_mul, zero_add] using
    hasDerivAt_matrix_mul (hasDerivAt_const t P) (gsExpRight_hasDerivAt B₁ Ω t)

theorem gsExpCurve_hasDerivAt (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpCurve B₂ P B₁ C Ω) (gsExpVelocity B₂ P B₁ C Ω t) t := by
  change HasDerivAt (fun s : ℝ => product2 (gsExpLeft B₂ C s) P (gsExpRight B₁ Ω s))
    (gsExpVelocity B₂ P B₁ C Ω t) t
  have he := product_curve_velocity (gsExpLeft B₂ C)
    (fun s : ℝ => P * gsExpRight B₁ Ω s) C (P * Ω * Pᵀ) t
    (gsExpLeft_hasDerivAt B₂ C t) (gsExpCarrier_hasDerivAt P B₁ Ω hP t)
  simpa only [gsExpCurve, product2, gsExpVelocity, Matrix.mul_assoc] using he

theorem gsExpVelocity_hasDerivAt (B₂ P B₁ C Ω : Mat n)
    (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpVelocity B₂ P B₁ C Ω) (gsExpAcceleration B₂ P B₁ C Ω t) t := by
  exact product_curve_acceleration (gsExpLeft B₂ C)
    (fun s : ℝ => P * gsExpRight B₁ Ω s) C (P * Ω * Pᵀ) t
    (gsExpLeft_hasDerivAt B₂ C t) (gsExpCarrier_hasDerivAt P B₁ Ω hP t)

theorem gsExpVelocity_eq_tangentParam (B₂ P B₁ C Ω : Mat n)
    (hP : Orthogonal P) (t : ℝ) :
    gsExpVelocity B₂ P B₁ C Ω t =
      tangentParam (gsExpLeft B₂ C t) P (gsExpRight B₁ Ω t) C Ω :=
  (tangentParam_factored _ _ _ _ _ hP).symm

theorem gsExpVelocity_zero (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) :
    gsExpVelocity B₂ P B₁ C Ω 0 = tangentParam B₂ P B₁ C Ω := by
  rw [gsExpVelocity_eq_tangentParam B₂ P B₁ C Ω hP,
    gsExpLeft_zero, gsExpRight_zero]

/-- An actual all-real curve, with the expected initial velocity. -/
theorem gsExpCurve_initial_derivative (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) :
    HasDerivAt (gsExpCurve B₂ P B₁ C Ω) (tangentParam B₂ P B₁ C Ω) 0 := by
  simpa only [gsExpVelocity_zero B₂ P B₁ C Ω hP] using
    gsExpCurve_hasDerivAt B₂ P B₁ C Ω hP 0

/-- All prescribed supported-skew directions really are velocities of curves
inside the original GS set; this is stronger than merely naming a linear space. -/
theorem exists_curve_of_twoFactorDirection (b₁ b₂ : ℕ)
    (B₂ P B₁ X : Mat n) (hP : Orthogonal P)
    (hs₂ : BlockDiagonal b₂ B₂) (hs₁ : BlockDiagonal b₁ B₁)
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hX : TwoFactorDirection (fun i => i.val / b₁) (fun i => i.val / b₂) B₂ P B₁ X) :
    ∃ γ : ℝ → Mat n, γ 0 = product2 B₂ P B₁ ∧
      (∀ t, InA2Orth b₁ b₂ P (γ t)) ∧ HasDerivAt γ X 0 := by
  obtain ⟨C, Ω, hsC, hC, hsΩ, hΩ, rfl⟩ := hX
  exact ⟨gsExpCurve B₂ P B₁ C Ω, gsExpCurve_zero B₂ P B₁ C Ω,
    gsExpCurve_inA2Orth b₁ b₂ B₂ P B₁ C Ω hs₂ hs₁ hB₂ hB₁ hsC hsΩ hC hΩ,
    gsExpCurve_initial_derivative B₂ P B₁ C Ω hP⟩

/-- Normality to the FULL explicit generator image at each current pair of
factors, not just to the initial generator image. No ODE assumptions remain. -/
theorem gsExpCurve_acceleration_normal (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ C Ω : Mat n)
    (hab : OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm))
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hsC : Supported block₂ C) (hsΩ : Supported block₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) (X : Mat n)
    (hX : TwoFactorDirection block₁ block₂ (gsExpLeft B₂ C t)
      (permMatrix σ) (gsExpRight B₁ Ω t) X) :
    frobInner (gsExpAcceleration B₂ (permMatrix σ) B₁ C Ω t) X = 0 := by
  let P := permMatrix σ
  obtain ⟨D, E, hsD, hD, hsE, hE, rfl⟩ := hX
  rw [tangentParam_factored _ _ _ _ _ (perm_orthogonal σ)]
  exact lifted_acceleration_normal hab (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    C (P * Ω * Pᵀ) D (P * E * Pᵀ)
    (gsExpLeft_orthogonal B₂ C hB₂ hC t)
    ((perm_orthogonal σ).mul (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t))
    hsC ((supported_perm_conjugate_iff block₁ σ Ω).mpr hsΩ)
    hsD ((supported_perm_conjugate_iff block₁ σ E).mpr hsE)
    hC (conjugate_skew P Ω hΩ) hD (conjugate_skew P E hE)

/-- Constant Frobenius speed does not require disjoint supports. In the overlap
case the fixed squared speed includes the cross term between the generators. -/
theorem gsExpCurve_constant_speed_general (B₂ P B₁ C Ω : Mat n)
    (hB₂ : Orthogonal B₂) (hP : Orthogonal P) (hB₁ : Orthogonal B₁)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    frobSq (gsExpVelocity B₂ P B₁ C Ω t) = frobSq (C + P * Ω * Pᵀ) := by
  exact lift_frobInner (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    (C + P * Ω * Pᵀ) (C + P * Ω * Pᵀ)
    (gsExpLeft_orthogonal B₂ C hB₂ hC t)
    (hP.mul (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t))

/-- Constant Frobenius speed in the nonoverlap regime. -/
theorem gsExpCurve_constant_speed (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ C Ω : Mat n)
    (hab : OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm))
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hsC : Supported block₂ C) (hsΩ : Supported block₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    frobSq (gsExpVelocity B₂ (permMatrix σ) B₁ C Ω t) = frobSq C + frobSq Ω := by
  rw [gsExpVelocity_eq_tangentParam _ _ _ _ _ (perm_orthogonal σ)]
  apply tangentParam_frobSq
    _ _ _ _ _ (gsExpLeft_orthogonal B₂ C hB₂ hC t) (perm_orthogonal σ)
    (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t)
  exact frobInner_disjoint_supported_skew hab C _ hsC
    ((supported_perm_conjugate_iff block₁ σ Ω).mpr hsΩ)
    (conjugate_skew _ Ω hΩ)

end GS.Continuation
