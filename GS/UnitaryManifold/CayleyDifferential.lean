module

public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The exact real differential of the unitary Cayley reconstruction. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Filter
open scoped Topology
namespace GS.UnitaryManifold
variable {n : ℕ} {block : Fin n → ℕ}

/-- Obtain the derivative from the identity c(A)(1+A)=1-A, rather than using
an unverified formula for differentiation of matrix inverse. -/
theorem chartInv_line_hasDerivAt_zero (Q : BlockU block) (v : Model block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 := by
    have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hi.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : CMat n) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : CMat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : CMat n) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : CMat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t
    change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]
    rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    have hz : V = -(Q.val * v.val) - Q.val * v.val := eq_sub_of_add_eq hv
    rw [hz, neg_smul, two_smul]
    abel
  rwa [he] at hd


/-- Differentiating the local left inverse gives a split-injective derivative. -/
theorem chart_differential_left_inverse (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) :
    (fderiv ℝ (chartMap Q) (chartInv Q x)).comp (fderiv ℝ (chartInv Q) x) =
      ContinuousLinearMap.id ℝ (Model block) := by
  have hi : DifferentiableAt ℝ (chartInv Q) x :=
    (chartInv_smooth_at Q x hx).differentiableAt (by simp)
  have hm : DifferentiableAt ℝ (chartMap Q) (chartInv Q x) := by
    apply (chartMap_smooth_at Q _ _).differentiableAt (by simp)
    rw [centered_chartInv]
    exact admissible_cayley x.val hx
  have he : (fun y => chartMap Q (chartInv Q y)) =ᶠ[𝓝 x] (fun y => y) := by
    filter_upwards [(parameterDomain_open block).mem_nhds hx] with y hy
    exact chartMap_chartInv Q y hy
  have hcomp := hm.hasFDerivAt.comp x hi.hasFDerivAt
  have hid := (hasFDerivAt_id (𝕜 := ℝ) x).congr_of_eventuallyEq he
  exact hcomp.unique hid

theorem chartInv_fderiv_injective (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) :
    Function.Injective (fderiv ℝ (chartInv Q) x) := by
  intro v w hvw
  have hv := congrArg (fun L : Model block →L[ℝ] Model block => L v)
    (chart_differential_left_inverse Q x hx)
  have hw := congrArg (fun L : Model block →L[ℝ] Model block => L w)
    (chart_differential_left_inverse Q x hx)
  have he := congrArg (fun z => fderiv ℝ (chartMap Q) (chartInv Q x) z) hvw
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    hv.symm.trans (he.trans hw)


end GS.UnitaryManifold
