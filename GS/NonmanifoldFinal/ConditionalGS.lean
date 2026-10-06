module

public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.Specifications

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Exact final GS reduction -- CONDITIONAL, not the finished theorem

The sole additional hypothesis is the old, unchanged, standalone
GS.Specifications.ConeProductNonManifoldGoal. It is not proved in this file.
All GS-specific local coverage, membership, coordinate, and chart transport
steps are supplied by the imported, compiler-checked proof scripts.
This declaration must NEVER be reported as an
unconditional proof of GS.Specifications.NonManifoldGoal.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

/-- The original cone goal applies to the actual independent GS coordinates. -/
theorem model_not_euclidean_of_cone_goal
    (hCone : GS.Specifications.ConeProductNonManifoldGoal)
    (q : ℕ) (hq : 3 ≤ q) : ¬ EuclideanAt (modelCoordinatesZero q) := by
  intro hModel
  let d := Fintype.card (UpperIndex q)
  let e := Fintype.card (FreeIndex q)
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  have hzero : ((0,0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by
    simp [S]
  let h : ModelCoordinates q ≃ₜ S := (modelToFin q).trans flattenConeProduct
  have hpoint : h (modelCoordinatesZero q) = ⟨(0,0),hzero⟩ := by
    change flattenConeProduct (modelToFin q (modelCoordinatesZero q)) = _
    rw [modelToFin_zero]
    rfl
  have hLocal : EuclideanAt (⟨(0,0),hzero⟩ : S) := by
    rw [← hpoint]
    exact (euclideanAt_homeomorph h (modelCoordinatesZero q)).mp hModel
  exact hCone d e (model_width_ge_three q hq)
    ((euclideanAtSubset_iff S (0,0) hzero).mpr hLocal)

/-- Exact implication between the two PRE-EXISTING specifications.
The cone obstruction remains a named, explicit argument. -/
theorem original_nonManifold_of_cone_goal
    (hCone : GS.Specifications.ConeProductNonManifoldGoal) :
    GS.Specifications.NonManifoldGoal := by
  intro q hq Q₀ hQ₀ _hdet hentries hEuclidean
  obtain ⟨g⟩ := original_pointed_open_model (by omega) Q₀ hQ₀ hentries
  have hFamily : EuclideanAt (familyBase Q₀ hQ₀) :=
    (euclideanAtSubset_iff (localFamily q) (basePoint Q₀)
      (familyBase Q₀ hQ₀).property).mp hEuclidean
  exact model_not_euclidean_of_cone_goal hCone q hq
    ((euclideanAt_pointedOpenModel g).mp hFamily)

end GS.NonmanifoldFinal
