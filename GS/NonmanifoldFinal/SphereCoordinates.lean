module

public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.Topology.EuclideanSphere

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Identify the explicit auxiliary sphere with a genuine Euclidean unit sphere

The plain finite function type has its default sup norm. EuclideanSpace carries
its L2 norm. The homeomorphism below explicitly passes through EuclideanSpace.equiv
and proves the norm-square identity; it does not identify these two norms.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
open scoped BigOperators
namespace GS.NonmanifoldFinal

variable {ι : Type*} [Fintype ι]


/-- Free coordinates together with the two Gram coordinates. -/
def planeEuclideanHomeomorph : PlaneSpace ι ≃ₜ EuclideanSpace ℝ (ι ⊕ Fin 2) :=
  sumCoordinates.trans (EuclideanSpace.equiv (ι ⊕ Fin 2) ℝ).symm.toHomeomorph

theorem planeEuclidean_norm_sq (p : PlaneSpace ι) :
    ‖planeEuclideanHomeomorph p‖ ^ 2 = planeEnergy p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : ι ⊕ Fin 2, (Sum.elim p.1 p.2 i) ^ 2) = planeEnergy p
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, planeEnergy, vectorSq, planeSq]

/-- A genuine homeomorphism, including the unit-radius condition on both sides. -/
def planeSphereHomeomorph : PlaneSphere ι ≃ₜ UnitSphere (ι ⊕ Fin 2) :=
  (planeEuclideanHomeomorph (ι := ι)).subtype (by
    intro p
    simp only [Metric.mem_sphere, dist_zero_right]
    have hsq := planeEuclidean_norm_sq p
    constructor <;> intro hp <;>
      nlinarith [norm_nonneg (planeEuclideanHomeomorph p)])

/-- Ambient dimension; the sphere dimension is one less. -/
theorem sphere_ambient_dimension :
    Fintype.card (ι ⊕ Fin 2) = Fintype.card ι + 2 := by simp

/-- A homeomorphism between L2 coordinate spaces induced by a finite reindexing. -/
def reindexEuclidean {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν) :
    EuclideanSpace ℝ κ ≃ₜ EuclideanSpace ℝ ν :=
  ((EuclideanSpace.equiv κ ℝ).toHomeomorph.trans (reindexReal e)).trans
    (EuclideanSpace.equiv ν ℝ).symm.toHomeomorph

theorem reindexEuclidean_norm_sq {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ≃ ν) (x : EuclideanSpace ℝ κ) :
    ‖reindexEuclidean e x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ j : ν, (x (e.symm j))^2) = ∑ i : κ, (x i)^2
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

def reindexUnitSphere {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν) :
    UnitSphere κ ≃ₜ UnitSphere ν :=
  (reindexEuclidean e).subtype (by
    intro x
    simp only [Metric.mem_sphere, dist_zero_right]
    have hsq := reindexEuclidean_norm_sq e x
    constructor <;> intro hx <;>
      nlinarith [norm_nonneg x, norm_nonneg (reindexEuclidean e x)])

/-- The auxiliary sphere is exactly a standard Fin-indexed sphere. -/
def planeSphereFinHomeomorph :
    PlaneSphere ι ≃ₜ UnitSphere (Fin (Fintype.card ι + 2)) :=
  planeSphereHomeomorph.trans (reindexUnitSphere
    ((Fintype.equivFin (ι ⊕ Fin 2)).trans
      (Equiv.cast (congrArg Fin (sphere_ambient_dimension (ι := ι))))))

end GS.NonmanifoldFinal
