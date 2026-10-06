module

public import GS.Specifications
public import GS.RestrictedNonmanifold.Parity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# The explicitly narrowed manuscript target

The user chose to restrict the manuscript theorem to q >= 3 with q modulo 4
equal to 2 or 3. The original all-q target is preserved in GS.Specifications;
it has not been silently weakened. This file specifies the restricted target
and proves its logical relation to the stronger target. The unconditional
proofs of both targets are now in `GS.NonmanifoldClosure.TopologicalClosure`.
-/

noncomputable section
namespace GS.Specifications

/-- Topological target for the restricted manuscript theorem (p = 2),
proved by `GS.NonmanifoldTopology.restrictedNonManifold`.
It uses the original matrix family and the original induced-topology notion. -/
def RestrictedNonManifoldGoal : Prop :=
  ∀ (q : ℕ), 3 ≤ q → (q % 4 = 2 ∨ q % 4 = 3) → ∀ (Q₀ : Mat q),
    Orthogonal Q₀ → Q₀.det = 1 → (∀ i j, Q₀ i j ≠ 0) →
      ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀)

/-- A proved implication between targets; the stronger target is an explicit
hypothesis and is not asserted here. -/
theorem restrictedNonManifold_of_general (h : NonManifoldGoal) :
    RestrictedNonManifoldGoal := by
  intro q hq _hmod Q₀ horth hdet hentries
  exact h q hq Q₀ horth hdet hentries

end GS.Specifications
