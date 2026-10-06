module

public import GS.RiemannianCompletion.ChartMetric
public import GS.Extensions.FiniteTopology
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual fibrewise continuous bilinear metric, with topology compatibility

The codomain is the standard space of continuous linear maps. Bounds are proved
in the ORIGINAL chart norm, which is not redefined to be a Frobenius norm.
The metric is continuous on each fibre and compatible with its existing
topology. `GS.GlobalGeometry.TangentBundleMetric` proves smooth metric evaluation
on the actual total tangent bundle. Mathlib v4.19 has no `RiemannianMetric`
structure to register; the intrinsic path distance is not constructed here.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open GS.RiemannianCompletion
open scoped Manifold Topology
namespace GS.GlobalGeometry
variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

-- The library tangent space is the chart model, but intentionally does not
-- expose its norm through global instances. Use the existing chart norm
-- locally; its topology is the library tangent-space topology.
local instance tangentSpaceChartNormedAddCommGroup
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedAddCommGroup (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (NormedAddCommGroup (PairModel b₁ b₂))

local instance tangentSpaceChartNormedSpace
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedSpace ℝ (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (NormedSpace ℝ (PairModel b₁ b₂))

local instance tangentSpaceChartFiniteDimensional
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    FiniteDimensional ℝ (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (FiniteDimensional ℝ (PairModel b₁ b₂))

/-- Bundle metric coefficients in the standard nested continuous-linear-map type. -/
def tangentMetricCLM (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X →L[ℝ]
      TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (tangentMetric σ X v).toContinuousLinearMap
      map_add' := by
        intro v w
        ext u
        exact tangentPairing_add_left σ X v w u
      map_smul' := by
        intro a v
        ext u
        exact tangentPairing_smul_left σ X a v u }

@[simp] theorem tangentMetricCLM_apply (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :
    tangentMetricCLM σ X v w = tangentPairing σ X v w := rfl

theorem tangentMetricCLM_continuous_diag (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    Continuous (fun v => tangentMetricCLM σ X v v) := by
  exact (tangentMetricCLM σ X).continuous.clm_apply continuous_id

/-- This is an inequality for the original entrywise matrix norm, not a
claim that it equals the Frobenius norm. -/
theorem matrix_norm_le_one_of_frobSq_le_one (A : Mat n) (h : frobSq A ≤ 1) :
    ‖A‖ ≤ 1 := by
  change ‖(A : Fin n → Fin n → ℝ)‖ ≤ 1
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro j
  have he := abs_entry_le_of_frobSq_le (η := (1:ℝ)) (by simpa using h) i j
  simpa only [Real.norm_eq_abs, abs_one] using he

theorem tangentMetric_unitBall_norm_bound (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X)
    (hv : tangentMetricCLM σ X v v < 1) : ‖v‖ ≤ 1 := by
  rw [tangentMetricCLM_apply, tangentPairing_self_coordinates] at hv
  have hl : frobSq v.1.val ≤ 1 := by
    nlinarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
  have hr : frobSq v.2.val ≤ 1 := by
    nlinarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
  change max ‖v.1.val‖ ‖v.2.val‖ ≤ 1
  exact max_le (matrix_norm_le_one_of_frobSq_le_one _ hl)
    (matrix_norm_le_one_of_frobSq_le_one _ hr)

theorem tangentMetric_unitBall_vonNBounded
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    Bornology.IsVonNBounded ℝ {v | tangentMetricCLM σ X v v < 1} := by
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  exact ⟨1, fun v hv => tangentMetric_unitBall_norm_bound σ X v hv⟩

/-- Fibrewise compatibility data, using standard types only. This theorem
is not relabelled as a smooth RiemannianBundle instance. -/
theorem tangentMetric_compatible_data (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    (∀ v w, tangentMetricCLM σ X v w = tangentMetricCLM σ X w v) ∧
    (∀ v, v ≠ 0 → 0 < tangentMetricCLM σ X v v) ∧
    ContinuousAt (fun v => tangentMetricCLM σ X v v) 0 ∧
    Bornology.IsVonNBounded ℝ {v | tangentMetricCLM σ X v v < 1} := by
  exact ⟨tangentPairing_symm σ X, tangentPairing_pos σ X,
    (tangentMetricCLM_continuous_diag σ X).continuousAt,
    tangentMetric_unitBall_vonNBounded σ X⟩

end GS.GlobalGeometry
