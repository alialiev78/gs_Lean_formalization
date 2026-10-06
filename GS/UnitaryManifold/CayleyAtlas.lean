module

public import GS.UnitaryManifold.CayleyCharts
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Cayley atlas on supported unitary matrices

The charts retain the original complex matrix subtype topology. Their model
space consists of supported skew-Hermitian matrices, regarded as a real vector
space. All overlap patterns are allowed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Filter Set
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} {block : Fin n → ℕ}

/-- Every unitary block matrix is covered by its own centered Cayley chart. -/
instance blockUChartedSpace (block : Fin n → ℕ) :
    ChartedSpace (Model block) (BlockU block) where
  atlas := Set.range blockPartialChart
  chartAt := blockPartialChart
  mem_chart_source Q := base_mem_chartSource Q
  chart_mem_atlas Q := ⟨Q, rfl⟩

/-- Transition regularity is proved for the actual partial homeomorphisms. -/
theorem blockPartialChart_transition_smooth (Q V : BlockU block) :
    ContDiffOn ℝ ⊤ ((blockPartialChart Q).symm.trans (blockPartialChart V))
      ((blockPartialChart Q).symm.trans (blockPartialChart V)).source := by
  intro x hx
  change x ∈ parameterDomain block ∧ blockChartInverse Q x ∈ chartSource V at hx
  have hv : admissible (V.valᴴ * chartInv Q x) := hx.2
  exact ((chartMap_smooth_at V (chartInv Q x) hv).comp x
    (chartInv_smooth Q).contDiffAt).contDiffWithinAt

/-- A genuine manifold in the original subtype topology. Mathlib regularity
`⊤` is real analytic, and therefore implies smoothness. -/
instance blockUIsManifold (block : Fin n → ℕ) :
    IsManifold (𝓘(ℝ, Model block)) ⊤ (BlockU block) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range blockPartialChart at he
  change e' ∈ Set.range blockPartialChart at he'
  obtain ⟨Q, rfl⟩ := he
  obtain ⟨V, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using blockPartialChart_transition_smooth Q V

end GS.UnitaryManifold
