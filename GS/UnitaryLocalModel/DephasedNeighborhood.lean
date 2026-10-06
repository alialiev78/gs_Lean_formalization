module

public import GS.UnitaryLocalModel.DephasedChart
public import GS.UnitaryLocalModel.ZeroLevelChart

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Open-neighbourhood coverage of the dephased unitary chart

The chart image is an open neighbourhood in the full dephased slice, with
its inherited matrix topology. The inverse is the continuous restriction
of the actual implicit-function chart; no coverage assumption is imposed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def dephasedBase (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : DephasedUnitary Q o :=
  ⟨Q, (by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ),
    anchorPositive_self Q.val o hQ⟩

def dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

theorem base_mem_dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedBase Q o hQ ∈ dephasedChartSource Q o hQ :=
  base_mem_unitaryConstraintChart_source Q o hQ

def dephasedCoordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2

theorem unitaryConstraintChart_of_dephased (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    unitaryConstraintChart Q o hQ A.val = (0, dephasedCoordinates Q o hQ A) := by
  apply Prod.ext
  · rw [unitaryConstraintChart_fst Q o hQ A.val hA]
    exact A.property.1
  · rfl

theorem dephasedCoordinates_mem (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedCoordinates Q o hQ A ∈ dephasedChartDomain Q o hQ := by
  have h := (unitaryConstraintChart Q o hQ).map_source hA
  rwa [unitaryConstraintChart_of_dephased Q o hQ A hA] at h

theorem dephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedParametrization Q o hQ (dephasedCoordinates Q o hQ A) = A.val.val := by
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_of_dephased Q o hQ A hA,
    (unitaryConstraintChart Q o hQ).left_inv hA]

/-- Every point of an open neighbourhood in the full dephased slice is attained. -/
theorem dephasedParametrization_covers_neighborhood (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ∃ V : Set (DephasedUnitary Q o), IsOpen V ∧ dephasedBase Q o hQ ∈ V ∧
      ∀ A ∈ V, ∃ y ∈ dephasedChartDomain Q o hQ,
        dephasedParametrization Q o hQ y = A.val.val := by
  refine ⟨dephasedChartSource Q o hQ, dephasedChartSource_open Q o hQ,
    base_mem_dephasedChartSource Q o hQ, ?_⟩
  intro A hA
  exact ⟨dephasedCoordinates Q o hQ A, dephasedCoordinates_mem Q o hQ A hA,
    dephasedParametrization_coordinates Q o hQ A hA⟩

/-- The actual homeomorphism between open subsets of the inherited slice
and the real constraint kernel. -/
def dephasedChartHomeomorph (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedChartSource Q o hQ ≃ₜ dephasedChartDomain Q o hQ :=
  zeroLevelHomeomorph (unitaryConstraintChart Q o hQ)
    (fun A => anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o)
    (by
      intro A hA
      rw [unitaryConstraintChart_fst Q o hQ A hA]
      have hp := ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).2.2
      simp only [hp, and_true])

/-- All assertions required for the local-model parametrization are proved
for this concrete chart, including full-neighbourhood coverage. -/
theorem dephased_chart_exists (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ∃ U : Set (DephasedModel Q o), ∃ ψ : DephasedModel Q o → CMat q,
      IsOpen U ∧ (0 : DephasedModel Q o) ∈ U ∧ ψ 0 = Q.val ∧
      ContinuousOn ψ U ∧ Set.InjOn ψ U ∧
      (∀ y ∈ U, Unitary (ψ y) ∧
        (∀ i, ∃ r : ℝ, 0 < r ∧ ψ y i o / Q.val i o = r) ∧
        (∀ j, ∃ r : ℝ, 0 < r ∧ ψ y o j / Q.val o j = r)) ∧
      ∃ V : Set (DephasedUnitary Q o), IsOpen V ∧ dephasedBase Q o hQ ∈ V ∧
        ∀ A ∈ V, ∃ y ∈ U, ψ y = A.val.val := by
  refine ⟨dephasedChartDomain Q o hQ, dephasedParametrization Q o hQ,
    dephasedChartDomain_open Q o hQ, zero_mem_dephasedChartDomain Q o hQ,
    dephasedParametrization_zero Q o hQ, dephasedParametrization_continuousOn Q o hQ,
    dephasedParametrization_injectiveOn Q o hQ, ?_,
    dephasedParametrization_covers_neighborhood Q o hQ⟩
  intro y hy
  exact ⟨dephasedParametrization_unitary Q o hQ y,
    (dephased_constraints_iff Q.val _ o).mp (dephasedParametrization_constraints Q o hQ y hy)⟩

end GS.UnitaryLocalModel
