module

public import GS.SharedGeometry.FactorCharts
public import GS.SharedGeometry.Directions
public import GS.OverlapGeometry.KernelCayley

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual shared orbit differential and its stabilizer kernel

Differentiate the concrete Cayley factor parametrization, retaining the -2
and +2 coefficients of the existing Cayley convention.  Its range is exactly
the point-based shared direction space.  At the identity, its entire kernel
integrates to the actual shared stabilizer; conversely every stabilizer element
in this Cayley chart comes from that kernel.

These are coordinate differentials of an actual smooth factor map.  No atlas
or manifold tangent space on its orbit image is introduced in this module.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts GS.Extensions
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- Total reconstruction in the genuine shared product group. -/
def factorLift (g : Factors right left) (v : PairGenerator right left) :
    Factors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : Factors right left) : factorLift g 0 = g := by
  exact Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift (g : Factors right left) : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk
    ((continuous_reconstruct g.2).comp continuous_snd)

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (g : Factors right left) (P : Mat n) (v : PairGenerator right left) :
    Mat n := factorLift g v • P

@[simp] theorem orbitParam_zero (g : Factors right left) (P : Mat n) :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth (g : Factors right left) (P : Mat n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  change ContDiffAt ℝ ⊤ (fun w : PairGenerator right left =>
    Factor.matrix (reconstruct g.1 w.1) * P *
      (Factor.matrix (reconstruct g.2 w.2))ᵀ) v
  exact smooth_mul_at
    (smooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst)
      contDiffAt_const)
    (smooth_transpose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

/-- Reuse the checked ambient Cayley derivative without changing its proof. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern n} (Q : Factor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => Factor.matrix (reconstruct Q (t • v)))
      ((-2 : ℝ) • (Factor.matrix Q * v.val)) 0 :=
  GS.ManifoldCompletion.chartInv_line_hasDerivAt_zero Q.val
    ⟨v.val, v.property.1, v.property.2.1⟩

/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero (g : Factors right left) (P : Mat n)
    (v : PairGenerator right left) :
    fderiv ℝ (orbitParam g P) 0 v =
      tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᵀ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := hasDerivAt_matrix_transpose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (Factor.matrix g.2 * v.2.val))ᵀ =
      (2 : ℝ) • (v.2.val * (Factor.matrix g.2)ᵀ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᵀ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, product2, zero_smul, Prod.smul_fst, Prod.smul_snd,
      reconstruct_zero, tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range (g : Factors right left) (P Y : Mat n) :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pointDirections right left (g • P) := by
  change (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pointDirections right left (product2 (Factor.matrix g.1) P (Factor.matrix g.2)ᵀ)
  rw [← sharedDirection_iff_pointDirections P (Factor.matrix g.1)
    (Factor.matrix g.2)ᵀ Y (Factor.matrix_shared g.1)
    (shared_factor_transpose (Factor.matrix_shared g.2))]
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
    change tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᵀ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, tangentParam]

theorem orbitParam_kernel_iff_intertwine (P : Mat n) (v : PairGenerator right left) :
    fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change tangentParam (1 : Mat n) P (1 : Mat n)ᵀ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [tangentParam, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    ext i j
    have he := congrFun (congrFun h i) j
    change (-2 : ℝ) * (v.1.val * P) i j + 2 * (P * v.2.val) i j = 0 at he
    linarith
  · intro h
    rw [h]
    ext i j
    change (-2 : ℝ) * (P * v.2.val) i j + 2 * (P * v.2.val) i j = 0
    ring

/-- Both implications hold for the entire Cayley parameter domain.  Thus the
continuous shared stabilizer is handled by its true linear kernel in this chart. -/
theorem factorLift_stabilizes_iff_kernel (P : Mat n) (v : PairGenerator right left) :
    factorLift (1 : Factors right left) v • P = P ↔
      fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 := by
  rw [orbitParam_kernel_iff_intertwine]
  have hA := admissible_of_isSkew v.1.val v.1.property.2.1
  have hB := admissible_of_isSkew v.2.val v.2.property.2.1
  have ho := cayley_orthogonal v.2.val v.2.property.2.1 hB
  simp only [factorLift, action_apply, reconstruct_matrix, Prod.fst_one, Prod.snd_one, Factor.matrix_one,
    Matrix.one_mul]
  change cayley v.1.val * P * (cayley v.2.val)ᵀ = P ↔ _
  constructor
  · intro h
    have he := congrArg (fun Y : Mat n => Y * cayley v.2.val) h
    have hi : cayley v.1.val * P = P * cayley v.2.val := by
      simpa only [Matrix.mul_assoc, ho.1, Matrix.mul_one] using he
    have hc := GS.OverlapGeometry.cayley_intertwine
      (cayley v.1.val) (cayley v.2.val) P
      (admissible_cayley v.1.val hA) (admissible_cayley v.2.val hB) hi
    simpa only [cayley_involutive v.1.val hA, cayley_involutive v.2.val hB] using hc
  · intro h
    rw [GS.OverlapGeometry.cayley_intertwine v.1.val v.2.val P hA hB h,
      Matrix.mul_assoc, ho.2, Matrix.mul_one]

end GS.SharedGeometry
