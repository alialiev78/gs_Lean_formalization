module

public import GS.Unitary.PointGenerators
public import GS.UnitaryManifold.UnitCayley
public import GS.UnitaryManifold.OrbitTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical, point-only unitary Cayley step

The value is a formula in the base matrix, ambient direction, and time. Factor
representatives occur only in proofs of membership. Balanced skew-Hermitian
generators ensure all denominators are invertible for every real time.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ}

def pointCayleyStep (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) (t : ℝ) : CMat n :=
  unitCayley (t • balancedLeft b₁ b₂ X Z) * X *
    unitCayley (t • balancedRight b₁ b₂ X Z)

@[simp] theorem pointCayleyStep_zero_time (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    pointCayleyStep b₁ b₂ X Z 0 = X := by simp [pointCayleyStep]

@[simp] theorem pointCayleyStep_zero_vector (b₁ b₂ : Fin n → ℕ) (X : CMat n) (t : ℝ) :
    pointCayleyStep b₁ b₂ X 0 t = X := by simp [pointCayleyStep]

/-- An explicit witness for preservation of the original group orbit. -/
def pointStepFactors {b₁ b₂ : Fin n → ℕ} (g : FactorGroup b₁ b₂)
    (X Z : CMat n) (t : ℝ) : FactorGroup b₁ b₂ :=
  (⟨unitCayley (t • balancedLeft b₁ b₂ X Z),
      unitCayley_supported _ _ ((balancedLeft_supported _ _ _ _).real_smul t)
        (skewHermitian_real_smul t (balancedLeft_skew _ _ _ _)),
      unitCayley_unitary _ (skewHermitian_real_smul t (balancedLeft_skew _ _ _ _))⟩ * g.1,
   ⟨(unitCayley (t • balancedRight b₁ b₂ X Z))ᴴ,
      (unitCayley_supported _ _ ((balancedRight_supported _ _ _ _).real_smul t)
        (skewHermitian_real_smul t (balancedRight_skew _ _ _ _))).conjTranspose,
      (unitCayley_unitary _ (skewHermitian_real_smul t (balancedRight_skew _ _ _ _))).conjTranspose⟩ * g.2)

theorem pointStepFactors_value {b₁ b₂ : Fin n → ℕ} (g : FactorGroup b₁ b₂)
    (P X Z : CMat n) (t : ℝ) (hg : g • P = X) :
    pointStepFactors g X Z t • P = pointCayleyStep b₁ b₂ X Z t := by
  let U := unitCayley (t • balancedLeft b₁ b₂ X Z)
  let V := unitCayley (t • balancedRight b₁ b₂ X Z)
  change (U * g.1.val) * P * (Vᴴ * g.2.val)ᴴ = U * X * V
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (U * g.1.val) * P * (g.2.valᴴ * V) = U * (g.1.val * P * g.2.valᴴ) * V := by
      simp only [Matrix.mul_assoc]
    _ = U * X * V := by rw [show g.1.val * P * g.2.valᴴ = X from hg]

/-- Feasibility for every step size uses no choice of preferred factors. -/
theorem pointCayleyStep_mem_orbit (b₁ b₂ : Fin n → ℕ) (P X Z : CMat n)
    (hX : X ∈ MulAction.orbit (FactorGroup b₁ b₂) P) (t : ℝ) :
    pointCayleyStep b₁ b₂ X Z t ∈ MulAction.orbit (FactorGroup b₁ b₂) P := by
  obtain ⟨g, hg⟩ := hX
  exact ⟨pointStepFactors g X Z t, pointStepFactors_value g P X Z t hg⟩

/-- Changing a matrix presentation cannot change the value of the update. -/
theorem pointCayleyStep_of_product_eq (b₁ b₂ : Fin n → ℕ)
    (L R L' R' P P' Z : CMat n) (t : ℝ) (h : L * P * R = L' * P' * R') :
    pointCayleyStep b₁ b₂ (L * P * R) Z t =
      pointCayleyStep b₁ b₂ (L' * P' * R') Z t := by rw [h]

/-- The whole ambient formula is jointly smooth. -/
theorem pointCayleyStep_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun p : (CMat n × CMat n) × ℝ =>
      pointCayleyStep b₁ b₂ p.1.1 p.1.2 p.2) := by
  have hl : ContDiff ℝ ⊤ (fun p : (CMat n × CMat n) × ℝ =>
      p.2 • balancedLeft b₁ b₂ p.1.1 p.1.2) :=
    contDiff_snd.smul ((balancedLeft_smooth b₁ b₂).comp contDiff_fst)
  have hr : ContDiff ℝ ⊤ (fun p : (CMat n × CMat n) × ℝ =>
      p.2 • balancedRight b₁ b₂ p.1.1 p.1.2) :=
    contDiff_snd.smul ((balancedRight_smooth b₁ b₂).comp contDiff_fst)
  exact smooth_matrix_product
    (smooth_matrix_product (unitCayley_smooth_comp _ hl (fun p =>
      skewHermitian_real_smul _ (balancedLeft_skew _ _ _ _))) contDiff_fst.fst)
    (unitCayley_smooth_comp _ hr (fun p =>
      skewHermitian_real_smul _ (balancedRight_skew _ _ _ _)))

/-- The derivative is computed before imposing the tangent reconstruction identity. -/
theorem pointCayleyStep_initial_velocity (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    HasDerivAt (pointCayleyStep b₁ b₂ X Z)
      (balancedLeft b₁ b₂ X Z * X + X * balancedRight b₁ b₂ X Z) 0 := by
  have hl := unitCayley_line_derivative (balancedLeft b₁ b₂ X Z) (balancedLeft_skew _ _ _ _)
  have hr := unitCayley_line_derivative (balancedRight b₁ b₂ X Z) (balancedRight_skew _ _ _ _)
  have hd := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hl (hasDerivAt_const 0 X)) hr
  unfold pointCayleyStep
  simpa only [zero_smul, unitCayley_zero, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_zero, add_zero] using hd

/-- Exact first-order identity for every true tangent matrix, allowing overlap. -/
theorem pointCayleyStep_tangent_derivative (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R)
    (hZ : Z ∈ pointTangentSpace b₁ b₂ (L * cPermMatrix σ * R)) :
    HasDerivAt (pointCayleyStep b₁ b₂ (L * cPermMatrix σ * R) Z) Z 0 := by
  have hd := pointCayleyStep_initial_velocity b₁ b₂ (L * cPermMatrix σ * R) Z
  rw [balanced_reconstruct_tangent b₁ b₂ σ L R Z hsL hsR hL hR hZ] at hd
  exact hd

end GS.UnitaryManifold
