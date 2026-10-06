module

public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.RestrictedNonmanifold.Specification
public import GS.RestrictedNonmanifold.SkewDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Conditional reduction of the restricted target to odd-width cones

`OddConeNonManifoldGoal` is the topological cone specification, now proved by
`GS.NonmanifoldTopology.oddConeNonManifold` in the final closure module.
This file supplies its conditional reduction. The implication below
uses the proved parity of the actual independent skew-coordinate index to
restrict the remaining cone obstruction to odd widths at least three.

The original matrix family, its induced topology, and the arbitrary number
of free Euclidean coordinates are retained throughout the reduction.
-/

noncomputable section

open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion GS.NonmanifoldObstruction
open GS.NonmanifoldFinal

namespace GS.Specifications

/-- The topological obstruction for odd-width rank-one cone products,
proved in `GS.NonmanifoldClosure.TopologicalClosure`. -/
def OddConeNonManifoldGoal : Prop :=
  ∀ (d e : ℕ), 3 ≤ d → Odd d →
    ¬ EuclideanAtSubset
      ({p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | Matrix.rank p.2 ≤ 1})
      (0, 0)

/-- The original cone target implies the explicitly narrowed cone target. -/
theorem oddConeNonManifold_of_general (h : ConeProductNonManifoldGoal) :
    OddConeNonManifoldGoal := by
  intro d e hd _hodd
  exact h d e hd

end GS.Specifications

namespace GS.RestrictedNonmanifold

/-- Conditional obstruction for the actual local coordinate space. -/
theorem model_not_euclidean_of_odd_cone_goal
    (hCone : GS.Specifications.OddConeNonManifoldGoal)
    (q : ℕ) (hq : 3 ≤ q) (hmod : q % 4 = 2 ∨ q % 4 = 3) :
    ¬ EuclideanAt (modelCoordinatesZero q) := by
  intro hModel
  let d := Fintype.card (UpperIndex q)
  let e := Fintype.card (FreeIndex q)
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  have hzero : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by
    simp [S]
  let h : ModelCoordinates q ≃ₜ S := (modelToFin q).trans flattenConeProduct
  have hpoint : h (modelCoordinatesZero q) = ⟨(0, 0), hzero⟩ := by
    change flattenConeProduct (modelToFin q (modelCoordinatesZero q)) = _
    rw [modelToFin_zero]
    rfl
  have hLocal : EuclideanAt (⟨(0, 0), hzero⟩ : S) := by
    rw [← hpoint]
    exact (euclideanAt_homeomorph h (modelCoordinatesZero q)).mp hModel
  exact hCone d e (model_width_ge_three q hq)
    (odd_card_upperIndex_of_mod_four q hmod)
    ((euclideanAtSubset_iff S (0, 0) hzero).mpr hLocal)

/-- The restricted matrix-family conclusion follows from the odd-width cone
obstruction. This intermediate theorem keeps its argument explicit. -/
theorem restricted_nonManifold_of_odd_cone_goal
    (hCone : GS.Specifications.OddConeNonManifoldGoal) :
    GS.Specifications.RestrictedNonManifoldGoal := by
  intro q hq hmod Q₀ hQ₀ _hdet hentries hEuclidean
  obtain ⟨g⟩ := original_pointed_open_model (by omega) Q₀ hQ₀ hentries
  have hFamily : EuclideanAt (familyBase Q₀ hQ₀) :=
    (euclideanAtSubset_iff (localFamily q) (basePoint Q₀)
      (familyBase Q₀ hQ₀).property).mp hEuclidean
  exact model_not_euclidean_of_odd_cone_goal hCone q hq hmod
    ((euclideanAt_pointedOpenModel g).mp hFamily)

end GS.RestrictedNonmanifold
