module

public import GS.CayleyCharts.Transitions
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Injective chart differentials and actual velocities in BlockO

The differential below is mathlib's fderiv. It is not defined to be a chosen
matrix formula. The range is characterized using actual HasDerivAt curves
which stay in the original block-orthogonal set near the base time.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction Filter
open scoped Topology
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

/-- Differentiating the local left inverse gives a split-injective derivative. -/
theorem chart_differential_left_inverse (Q : BlockO block) (x : Model block)
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

theorem chartInv_fderiv_injective (Q : BlockO block) (x : Model block)
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

/-- Every coordinate velocity is realized by a genuine differentiable matrix
curve, orthogonal and block-supported in an actual time neighbourhood. -/
theorem chart_velocity_realized (Q : BlockO block) (x v : Model block)
    (hx : x ∈ parameterDomain block) :
    ∃ A : ℝ → Mat n,
      A 0 = chartInv Q x ∧
      HasDerivAt A (fderiv ℝ (chartInv Q) x v) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), Supported block (A t) ∧ Orthogonal (A t)) := by
  let line : ℝ → Model block := fun t => x + t • v
  have hline : HasDerivAt line v 0 := by
    simpa [line, Pi.add_def] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hi := (chartInv_smooth_at Q x hx).differentiableAt (by simp)
  refine ⟨fun t => chartInv Q (line t), by simp [line], ?_, ?_⟩
  · have hif : HasFDerivAt (chartInv Q)
        (fderiv ℝ (chartInv Q) x) (line 0) := by
      simpa [line] using hi.hasFDerivAt
    simpa only [Function.comp_def] using hif.comp_hasDerivAt 0 hline
  · have he : ∀ᶠ t in 𝓝 (0 : ℝ), line t ∈ parameterDomain block :=
      hline.continuousAt.eventually (by simpa [line] using (parameterDomain_open block).mem_nhds hx)
    filter_upwards [he] with t ht
    exact ⟨chartInv_supported Q (line t) ht, chartInv_orthogonal Q (line t) ht⟩

/-- Recovery applies to arbitrary differentiable ambient curves in BlockO;
no differentiability of a previously chosen factorization is assumed. -/
theorem chart_recovers_curve_velocity (Q U : BlockO block) (hU : U ∈ chartSource Q)
    {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hA : HasDerivAt A V t) (hbase : A t = U.val)
    (hvalid : ∀ᶠ s in 𝓝 t, Supported block (A s) ∧ Orthogonal (A s)) :
    fderiv ℝ (chartInv Q) (chartMap Q U.val)
      (fderiv ℝ (chartMap Q) U.val V) = V := by
  have hm : DifferentiableAt ℝ (chartMap Q) U.val :=
    (chartMap_smooth_at Q U.val hU).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (chartInv Q) (chartMap Q U.val) :=
    (chartInv_smooth_at Q _ (chartMap_mem_domain Q U hU)).differentiableAt (by simp)
  have hsource : ∀ᶠ s in 𝓝 t, admissible (Q.valᵀ * A s) := by
    have hpoint : ContinuousAt (fun s => Q.valᵀ * A s) t :=
      (continuous_matrix_product
        (continuous_fst : Continuous (fun p : Mat n × Mat n => p.1))
        (continuous_snd : Continuous (fun p : Mat n × Mat n => p.2))).continuousAt.comp
          (continuousAt_const.prodMk hA.continuousAt)
    exact hpoint.eventually (by simpa only [hbase, Filter.Eventually, Set.setOf_mem_eq] using admissible_open.mem_nhds hU)
  have he : (fun s => chartInv Q (chartMap Q (A s))) =ᶠ[𝓝 t] A := by
    filter_upwards [hvalid, hsource] with s hs hd
    exact chartInv_chartMap Q ⟨A s, hs⟩ hd
  have hmAt : HasFDerivAt (chartMap Q) (fderiv ℝ (chartMap Q) U.val) (A t) := by
    simpa only [hbase] using hm.hasFDerivAt
  have hmA : HasDerivAt (fun s => chartMap Q (A s))
      (fderiv ℝ (chartMap Q) U.val V) t := hmAt.comp_hasDerivAt t hA
  have hiAt : HasFDerivAt (chartInv Q)
      (fderiv ℝ (chartInv Q) (chartMap Q U.val)) (chartMap Q (A t)) := by
    simpa only [hbase] using hi.hasFDerivAt
  have hiA := hiAt.comp_hasDerivAt t hmA
  exact hiA.unique (hA.congr_of_eventuallyEq he)

/-- A precise curve-based tangent statement. This is NOT yet an IsManifold
instance or an identification with mathlib's TangentSpace type. -/
theorem chart_range_iff_curve_velocity (Q U : BlockO block)
    (hU : U ∈ chartSource Q) (V : Mat n) :
    (∃ v : Model block, fderiv ℝ (chartInv Q) (chartMap Q U.val) v = V) ↔
    (∃ A : ℝ → Mat n, A 0 = U.val ∧ HasDerivAt A V 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), Supported block (A t) ∧ Orthogonal (A t))) := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨A, hA0, hd, he⟩ := chart_velocity_realized Q (chartMap Q U.val) v
      (chartMap_mem_domain Q U hU)
    refine ⟨A, ?_, ?_, he⟩
    · rw [hA0, chartInv_chartMap Q U hU]
    · simpa only [hv] using hd
  · rintro ⟨A, hA0, hd, he⟩
    exact ⟨fderiv ℝ (chartMap Q) U.val V,
      chart_recovers_curve_velocity Q U hU hd hA0 he⟩

end GS.CayleyCharts
