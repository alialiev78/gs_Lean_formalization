module

public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.DephasedDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Standard real coordinates for the dephased unitary chart

The kernel chart is transported by a genuine continuous linear equivalence
to `Fin ((q - 1)^2) → ℝ`. No norm-preserving identification is asserted.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

/-- A continuous linear coordinate identification with the computed dimension. -/
def dephasedCoordinateEquiv (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    DephasedModel Q o ≃L[ℝ] (Fin ((q-1)^2) → ℝ) := by
  letI : Module.Free ℝ (DephasedModel Q o) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (DephasedModel Q o))
  let b : Module.Basis (Fin ((q-1)^2)) ℝ (DephasedModel Q o) :=
    Module.finBasisOfFinrankEq ℝ (DephasedModel Q o) (finrank_dephasedModel Q o hQ)
  let e : DephasedModel Q o ≃ₗ[ℝ] (Fin ((q-1)^2) → ℝ) := b.equivFun
  exact LinearEquiv.toContinuousLinearEquiv
    (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q-1)^2) → ℝ) e

def euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (Fin ((q-1)^2) → ℝ) :=
  (dephasedCoordinateEquiv Q o hQ).symm ⁻¹' dephasedChartDomain Q o hQ

def euclideanDephasedParametrization (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : Fin ((q-1)^2) → ℝ) : CMat q :=
  dephasedParametrization Q o hQ ((dephasedCoordinateEquiv Q o hQ).symm x)

def euclideanDephasedCoordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) : Fin ((q-1)^2) → ℝ :=
  dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)

theorem euclideanDephasedDomain_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (euclideanDephasedDomain Q o hQ) :=
  (dephasedChartDomain_open Q o hQ).preimage (dephasedCoordinateEquiv Q o hQ).symm.continuous

theorem zero_mem_euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    (0 : Fin ((q-1)^2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (dephasedCoordinateEquiv Q o hQ).symm 0 ∈ dephasedChartDomain Q o hQ
  simpa using zero_mem_dephasedChartDomain Q o hQ

@[simp] theorem euclideanDephasedParametrization_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  simp [euclideanDephasedParametrization]

theorem euclideanDephasedParametrization_continuousOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  (dephasedParametrization_continuousOn Q o hQ).comp
    (dephasedCoordinateEquiv Q o hQ).symm.continuous.continuousOn (fun _ h => h)

theorem euclideanDephasedParametrization_injectiveOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := by
  intro x hx y hy he
  apply (dephasedCoordinateEquiv Q o hQ).symm.injective
  exact dephasedParametrization_injectiveOn Q o hQ hx hy he

/-- The local homeomorphism in the standard real coordinate space. -/
def euclideanDephasedChartHomeomorph (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedChartSource Q o hQ ≃ₜ euclideanDephasedDomain Q o hQ :=
  (dephasedChartHomeomorph Q o hQ).trans
    ((dephasedCoordinateEquiv Q o hQ).toHomeomorph.subtype
      (fun x => by simp [euclideanDephasedDomain]))

theorem euclideanDephasedCoordinates_mem (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedCoordinates Q o hQ A ∈ euclideanDephasedDomain Q o hQ := by
  change (dephasedCoordinateEquiv Q o hQ).symm
    (dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)) ∈ dephasedChartDomain Q o hQ
  simpa using dephasedCoordinates_mem Q o hQ A hA

theorem euclideanDephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedParametrization Q o hQ (euclideanDephasedCoordinates Q o hQ A) = A.val.val := by
  simpa [euclideanDephasedParametrization, euclideanDephasedCoordinates] using
    dephasedParametrization_coordinates Q o hQ A hA

/-- A concrete Euclidean chart, with positivity and full relative-neighbourhood coverage. -/
theorem euclidean_dephased_chart_exists (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ∃ U : Set (Fin ((q-1)^2) → ℝ), ∃ ψ : (Fin ((q-1)^2) → ℝ) → CMat q,
      IsOpen U ∧ (0 : Fin ((q-1)^2) → ℝ) ∈ U ∧ ψ 0 = Q.val ∧
      ContinuousOn ψ U ∧ Set.InjOn ψ U ∧
      (∀ y ∈ U, Unitary (ψ y) ∧
        (∀ i, ∃ r : ℝ, 0 < r ∧ ψ y i o / Q.val i o = r) ∧
        (∀ j, ∃ r : ℝ, 0 < r ∧ ψ y o j / Q.val o j = r)) ∧
      ∃ V : Set (DephasedUnitary Q o), IsOpen V ∧ dephasedBase Q o hQ ∈ V ∧
        ∀ A ∈ V, ∃ y ∈ U, ψ y = A.val.val := by
  refine ⟨euclideanDephasedDomain Q o hQ, euclideanDephasedParametrization Q o hQ,
    euclideanDephasedDomain_open Q o hQ, zero_mem_euclideanDephasedDomain Q o hQ,
    euclideanDephasedParametrization_zero Q o hQ,
    euclideanDephasedParametrization_continuousOn Q o hQ,
    euclideanDephasedParametrization_injectiveOn Q o hQ, ?_,
    dephasedChartSource Q o hQ, dephasedChartSource_open Q o hQ,
    base_mem_dephasedChartSource Q o hQ, ?_⟩
  · intro y hy
    exact ⟨dephasedParametrization_unitary Q o hQ _,
      (dephased_constraints_iff Q.val _ o).mp (dephasedParametrization_constraints Q o hQ _ hy)⟩
  · intro A hA
    exact ⟨euclideanDephasedCoordinates Q o hQ A,
      euclideanDephasedCoordinates_mem Q o hQ A hA,
      euclideanDephasedParametrization_coordinates Q o hQ A hA⟩

end GS.UnitaryLocalModel
