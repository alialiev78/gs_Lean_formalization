module

public import GS.CayleyCharts.Transitions
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Cayley atlas on the original block orthogonal group

The topology is the existing matrix subtype topology. This module packages
the explicit charts and checked transition formulas into mathlib structures.
It does not transfer a topology or assume that the group is a manifold.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction Filter Set
open scoped Topology Manifold
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

/-- A total extension of the inverse chart. Its value outside the chart target
is immaterial to a partial homeomorphism. -/
def blockChartInverse (Q : BlockO block) (x : Model block) : BlockO block :=
  by
    classical
    exact if hx : x ∈ parameterDomain block then reconstructBlock Q ⟨x, hx⟩ else Q

theorem blockChartInverse_of_mem (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) :
    blockChartInverse Q x = reconstructBlock Q ⟨x, hx⟩ := by
  simp [blockChartInverse, hx]

theorem blockChartInverse_val (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) :
    (blockChartInverse Q x).val = chartInv Q x := by
  rw [blockChartInverse_of_mem Q x hx]
  rfl

/-- A genuine partial homeomorphism with the prescribed open source and target. -/
def blockPartialChart (Q : BlockO block) :
    OpenPartialHomeomorph (BlockO block) (Model block) where
  toFun U := chartMap Q U.val
  invFun := blockChartInverse Q
  source := chartSource Q
  target := parameterDomain block
  map_source' U hU := chartMap_mem_domain Q U hU
  map_target' x hx := by
    rw [blockChartInverse_of_mem Q x hx]
    exact reconstruct_mem_source Q ⟨x, hx⟩
  left_inv' U hU := by
    apply Subtype.ext
    rw [blockChartInverse_val Q _ (chartMap_mem_domain Q U hU)]
    exact chartInv_chartMap Q U hU
  right_inv' x hx := by
    rw [blockChartInverse_val Q x hx]
    exact chartMap_chartInv Q x hx
  open_source := chartSource_open Q
  open_target := parameterDomain_open block
  continuousOn_toFun := by
    intro U hU
    exact ((chartMap_smooth_at Q U.val hU).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hc : Continuous (fun x : parameterDomain block => reconstructBlock Q x) :=
      (continuous_chartInv_restrict Q).subtype_mk _
    exact hc.congr (fun x => (blockChartInverse_of_mem Q x.val x.property).symm)

@[simp] theorem blockPartialChart_source (Q : BlockO block) :
    (blockPartialChart Q).source = chartSource Q := rfl

@[simp] theorem blockPartialChart_target (Q : BlockO block) :
    (blockPartialChart Q).target = parameterDomain block := rfl

/-- Every point is covered, using its own centred Cayley chart. -/
instance blockOChartedSpace (block : Fin n → ℕ) :
    ChartedSpace (Model block) (BlockO block) where
  atlas := Set.range blockPartialChart
  chartAt := blockPartialChart
  mem_chart_source Q := base_mem_chartSource Q
  chart_mem_atlas Q := ⟨Q, rfl⟩

/-- Transition regularity for the actual partial homeomorphisms, including
their exact domains. -/
theorem blockPartialChart_transition_smooth (Q V : BlockO block) :
    ContDiffOn ℝ ⊤ ((blockPartialChart Q).symm.trans (blockPartialChart V))
      ((blockPartialChart Q).symm.trans (blockPartialChart V)).source := by
  intro x hx
  change x ∈ parameterDomain block ∧ blockChartInverse Q x ∈ chartSource V at hx
  have ht : x ∈ transitionDomain Q V := by
    refine ⟨hx.1, ?_⟩
    have hv := hx.2
    change admissible (V.valᵀ * (blockChartInverse Q x).val) at hv
    rwa [blockChartInverse_val Q x hx.1] at hv
  have he : (fun y => chartMap V (blockChartInverse Q y).val) =ᶠ[𝓝 x]
      transition Q V := by
    filter_upwards [(parameterDomain_open block).mem_nhds hx.1] with y hy
    rw [blockChartInverse_val Q y hy]
    rfl
  exact ((transition_smooth_at Q V x ht).congr_of_eventuallyEq he).contDiffWithinAt

/-- The block orthogonal group is a manifold in its original topology.
In mathlib 4.19, regularity `⊤` is analytic, hence in particular smooth. -/
instance blockOIsManifold (block : Fin n → ℕ) :
    IsManifold (𝓘(ℝ, Model block)) ⊤ (BlockO block) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range blockPartialChart at he
  change e' ∈ Set.range blockPartialChart at he'
  obtain ⟨Q, rfl⟩ := he
  obtain ⟨V, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using blockPartialChart_transition_smooth Q V

end GS.CayleyCharts
