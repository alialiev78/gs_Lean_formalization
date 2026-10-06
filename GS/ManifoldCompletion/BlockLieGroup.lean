module

public import GS.ManifoldCompletion.FactorCoordinates
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The checked block atlas is a Lie group atlas

This file connects the existing smooth matrix formulas to ContMDiff on the
actual BlockO manifold. It does not use an unconstructed manifold structure on
an orbit. Matrix multiplication is treated as a polynomial map for the entrywise
norm; no NormedRing instance for that norm is assumed.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block : Fin n → ℕ}

/-- The inclusion of the actual block group into matrices is manifold-smooth.
In a source chart it is the already checked rational map chartInv. -/
theorem blockO_val_contMDiff (block : Fin n → ℕ) :
    ContMDiff (𝓘(ℝ, Model block)) (𝓘(ℝ, Mat n)) ⊤
      (fun Q : BlockO block => Q.val) := by
  intro Q
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤
    (fun x : Model block => (blockChartInverse Q x).val)
    (Set.range (id : Model block → Model block)) (chartMap Q Q.val)
  simpa only [Function.comp_def,blockChartInverse_val_everywhere] using
    ((chartInv_smooth Q).contDiffAt :
      ContDiffAt ℝ ⊤ (chartInv Q) (chartMap Q Q.val)).contDiffWithinAt

section Source
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Ambient smoothness of a map valued in BlockO implies manifold smoothness
for this specific atlas. This is proved using its explicit forward chart. -/
theorem contMDiffAt_blockO_of_val {f : M → BlockO block} {x : M}
    (hf : ContMDiffAt I (𝓘(ℝ, Mat n)) ⊤ (fun y => (f y).val) x) :
    ContMDiffAt I (𝓘(ℝ, Model block)) ⊤ f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  change ContMDiffAt I (𝓘(ℝ, Model block)) ⊤
    (fun y => chartMap (f x) (f y).val) x
  exact ContDiffAt.comp_contMDiffAt (I := I)
    (g := chartMap (f x)) (f := fun y => (f y).val)
    (chartMap_smooth_at (f x) (f x).val (base_mem_chartSource (f x))) hf

/-- A practical global criterion; not a new definition of ContMDiff. -/
theorem contMDiff_blockO_of_val {f : M → BlockO block}
    (hf : ContMDiff I (𝓘(ℝ, Mat n)) ⊤ (fun y => (f y).val)) :
    ContMDiff I (𝓘(ℝ, Model block)) ⊤ f := by
  intro x
  exact contMDiffAt_blockO_of_val (hf x)

/-- The converse follows from the independently proved smooth inclusion. -/
theorem contMDiff_blockO_iff_val {f : M → BlockO block} :
    ContMDiff I (𝓘(ℝ, Model block)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, Mat n)) ⊤ (fun y => (f y).val) := by
  constructor
  · intro hf
    exact (blockO_val_contMDiff block).comp hf
  · exact contMDiff_blockO_of_val
end Source

/-- Joint smoothness of multiplication into the actual BlockO manifold. -/
theorem blockO_mul_contMDiff (block : Fin n → ℕ) :
    ContMDiff ((𝓘(ℝ, Model block)).prod (𝓘(ℝ, Model block)))
      (𝓘(ℝ, Model block)) ⊤ (fun p : BlockO block × BlockO block => p.1 * p.2) := by
  apply contMDiff_blockO_of_val
  have hl : ContMDiff ((𝓘(ℝ, Model block)).prod (𝓘(ℝ, Model block)))
      (𝓘(ℝ, Mat n)) ⊤ (fun p : BlockO block × BlockO block => p.1.val) :=
    (blockO_val_contMDiff block).comp contMDiff_fst
  have hr : ContMDiff ((𝓘(ℝ, Model block)).prod (𝓘(ℝ, Model block)))
      (𝓘(ℝ, Mat n)) ⊤ (fun p : BlockO block × BlockO block => p.2.val) :=
    (blockO_val_contMDiff block).comp contMDiff_snd
  have hm : ContDiff ℝ ⊤ (fun t : Mat n × Mat n => t.1 * t.2) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_mul_at contDiffAt_fst contDiffAt_snd)
  simpa only [Function.comp_def,blockO_mul_val] using hm.comp_contMDiff (hl.prodMk_space hr)

/-- Inversion is transpose, not matrix nonsingularInverse. -/
theorem blockO_inv_contMDiff (block : Fin n → ℕ) :
    ContMDiff (𝓘(ℝ, Model block)) (𝓘(ℝ, Model block)) ⊤
      (fun Q : BlockO block => Q⁻¹) := by
  apply contMDiff_blockO_of_val
  have ht : ContDiff ℝ ⊤ (fun X : Mat n => Xᵀ) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_transpose_at contDiffAt_id)
  simpa only [Function.comp_def,blockO_inv_val] using ht.comp_contMDiff (blockO_val_contMDiff block)

instance blockOContMDiffMul (block : Fin n → ℕ) :
    ContMDiffMul (𝓘(ℝ, Model block)) ⊤ (BlockO block) where
  toIsManifold := blockOIsManifold block
  contMDiff_mul := blockO_mul_contMDiff block

/-- Genuine mathlib class, with the inherited topology and checked Cayley
manifold instance. No additional Lie-group axioms are declared. -/
instance blockOLieGroup (block : Fin n → ℕ) :
    LieGroup (𝓘(ℝ, Model block)) ⊤ (BlockO block) where
  toContMDiffMul := blockOContMDiffMul block
  contMDiff_inv := blockO_inv_contMDiff block

/-- The global inverse Cayley parametrization is manifold-smooth too. -/
theorem blockChartInverse_contMDiff (Q : BlockO block) :
    ContMDiff (𝓘(ℝ, Model block)) (𝓘(ℝ, Model block)) ⊤ (blockChartInverse Q) := by
  apply contMDiff_blockO_of_val
  simpa only [Function.comp_def,blockChartInverse_val_everywhere] using (chartInv_smooth Q).contMDiff

/-- Ordinary finite-dimensional and countability hypotheses are actually
available for BlockO; LieGroup alone does not encode them. -/
theorem block_group_separation (block : Fin n → ℕ) :
    CompactSpace (BlockO block) ∧ SecondCountableTopology (BlockO block) ∧
      T2Space (BlockO block) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GS.ManifoldCompletion
