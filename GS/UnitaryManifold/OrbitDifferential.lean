module

public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The derivative of the actual complex matrix orbit parametrization. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Exact Frechet derivative of the actual matrix-valued orbit chart at its
centre. The coefficients reflect the chosen Cayley convention. -/
theorem orbitParam_fderiv_zero (g : FactorGroup block₁ block₂) (P : CMat n)
    (v : PairModel block₁ block₂) :
    fderiv ℝ (orbitParam g P) 0 v =
      GS.UnitaryGeometry.tangentParam g.1.val P g.2.valᴴ ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := chartInv_line_hasDerivAt_zero g.1 v.1
  have hdR := hasDerivAt_matrix_conjTranspose (chartInv_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (g.2.val * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * g.2.valᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (GS.UnitaryGeometry.tangentParam g.1.val P g.2.valᴴ ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, GS.UnitaryGeometry.product2, zero_smul,
      chartInv_zero, GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Prod.smul_fst, Prod.smul_snd] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The derivative range equals the existing real-linear generator space. -/
theorem orbitParam_fderiv_zero_range (g : FactorGroup block₁ block₂) (P X : CMat n) :
    (∃ v : PairModel block₁ block₂, fderiv ℝ (orbitParam g P) 0 v = X) ↔
      X ∈ GS.UnitaryGeometry.tangentParamSpace block₁ block₂ g.1.val P g.2.valᴴ := by
  rw [GS.UnitaryGeometry.mem_tangentParamSpace_iff]
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let c : Model block₂ := (-2 : ℝ) • v.1
    let w : Model block₁ := (2 : ℝ) • v.2
    exact ⟨c.val, c.property, w.val, w.property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, rfl⟩
    let c : Model block₂ := ⟨C, hC⟩
    let w : Model block₁ := ⟨Ω, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero]
    change GS.UnitaryGeometry.tangentParam g.1.val P g.2.valᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul]

end GS.UnitaryManifold
