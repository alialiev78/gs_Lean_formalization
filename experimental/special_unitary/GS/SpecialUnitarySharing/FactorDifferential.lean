module

public import GS.SpecialUnitarySharing.FactorCharts
public import GS.SpecialUnitarySharing.Directions
public import GS.SpecialUnitarySharing.Orbit
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual SU shared factor differential

Differentiate the globally defined exponential reconstruction.  Its range is
the full blockwise trace-free generator image.  Every vector in its kernel
exponentiates to an actual stabilizer, with no discrete-stabilizer assumption.
The scale -2 is retained to match the existing coordinate interfaces.
-/
set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open GS.SpecialUnitarySharing.Orbit
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {right left : Pattern n}

/-- Total reconstruction in the genuine shared product group. -/
def factorLift (g : SpecialFactors right left) (v : PairGenerator right left) :
    SpecialFactors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : SpecialFactors right left) : factorLift g 0 = g := by
  exact Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift (g : SpecialFactors right left) : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk
    ((continuous_reconstruct g.2).comp continuous_snd)

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (g : SpecialFactors right left) (P : CMat n) (v : PairGenerator right left) :
    CMat n := factorLift g v • P

@[simp] theorem orbitParam_zero (g : SpecialFactors right left) (P : CMat n) :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth (g : SpecialFactors right left) (P : CMat n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  change ContDiffAt ℝ ⊤ (fun w : PairGenerator right left =>
    SpecialFactor.matrix (reconstruct g.1 w.1) * P *
      (SpecialFactor.matrix (reconstruct g.2 w.2))ᴴ) v
  exact smooth_mul_at
    (smooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst)
      contDiffAt_const)
    (smooth_conjTranspose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

/-- The genuine exponential line derivative in the original matrix topology. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern n} (Q : SpecialFactor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => SpecialFactor.matrix (reconstruct Q (t • v)))
      ((-2 : ℝ) • (SpecialFactor.matrix Q * v.val)) 0 := by
  have he := unitaryExpParam_line_deriv s (generatorInclusion s v)
  have hp := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) (SpecialFactor.matrix Q)) he
  simpa only [reconstruct_matrix, unitaryExpParam, generatorInclusion_val,
    Submodule.coe_smul, Matrix.zero_mul, zero_add, Matrix.mul_smul] using hp

/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero (g : SpecialFactors right left) (P : CMat n)
    (v : PairGenerator right left) :
    fderiv ℝ (orbitParam g P) 0 v =
      tangentParam (SpecialFactor.matrix g.1) P (SpecialFactor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := GS.UnitaryManifold.hasDerivAt_matrix_conjTranspose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (SpecialFactor.matrix g.2 * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * (SpecialFactor.matrix g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.1.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (tangentParam (SpecialFactor.matrix g.1) P (SpecialFactor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, product2, zero_smul,
      reconstruct_zero, tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range (g : SpecialFactors right left) (P Y : CMat n) :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pointDirections right left (g • P) := by
  change (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pointDirections right left (product2 (SpecialFactor.matrix g.1) P (SpecialFactor.matrix g.2)ᴴ)
  rw [← sharedDirection_iff_pointDirections P (SpecialFactor.matrix g.1)
    (SpecialFactor.matrix g.2)ᴴ Y (SpecialFactor.matrix_special g.1).1
    (GS.UnitarySharing.shared_factor_conjTranspose (SpecialFactor.matrix_special g.2).1)]
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let C : Generator left := (-2 : ℝ) • v.1
    let Ω : Generator right := (2 : ℝ) • v.2
    exact ⟨C.val, C.property, Ω.val, Ω.property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    let c : Generator left := ⟨C, hC⟩
    let w : Generator right := ⟨Ω, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero, hY]
    change tangentParam (SpecialFactor.matrix g.1) P (SpecialFactor.matrix g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, tangentParam]

theorem orbitParam_kernel_iff_intertwine (P : CMat n) (v : PairGenerator right left) :
    fderiv ℝ (orbitParam (1 : SpecialFactors right left) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change tangentParam (1 : CMat n) P (1 : CMat n)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
      simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg,
        neg_smul, neg_add_rev, neg_neg] using h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro h
    rw [h, ← add_smul]
    norm_num

/-- The entire linear kernel integrates to actual SU stabilizer elements.
Only this direction is needed for the local product and orbit atlas. -/
theorem factorLift_stabilizes_of_kernel (P : CMat n) (v : PairGenerator right left)
    (hv : fderiv ℝ (orbitParam (1 : SpecialFactors right left) P) 0 v = 0) :
    factorLift (1 : SpecialFactors right left) v • P = P := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  have his : ((-2 : ℝ) • v.1.val) * P = P * ((-2 : ℝ) • v.2.val) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hi]
  have he := cMatrixExp_intertwine _ _ P his
  have hu := cMatrixExp_unitary ((-2 : ℝ) • v.2.val)
    ((specialSkewSpace right).smul_mem (-2 : ℝ) v.2.property).1.2.1
  change SpecialFactor.matrix (reconstruct 1 v.1) * P *
    (SpecialFactor.matrix (reconstruct 1 v.2))ᴴ = P
  simp only [reconstruct_matrix, SpecialFactor.matrix_one, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, hu.2, Matrix.mul_one]

end GS.SpecialUnitarySharing
