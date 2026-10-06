module

public import GS.Revision.M4Polynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# An open set excluded from the four-factor orthogonal class

The exact negative polynomial margin gives a nonempty open excluded set. This
is a qualitative robust obstruction. The numerical Frobenius-distance lower
bound discussed in the mathematical notes is NOT formalized in this module.

-/
noncomputable section
open GS GS.M4
namespace GS.Revision.M4

def score (A : Mat 6) : ℝ := obstructionPolynomial (absDetBlock A)

theorem continuous_score : Continuous score := by
  unfold score obstructionPolynomial absDetBlock detBlock
  fun_prop

def excludedSet : Set (Mat 6) := {A | score A < 0}

theorem excludedSet_open : IsOpen excludedSet := by
  exact isOpen_lt continuous_score continuous_const

theorem Q_mem_excludedSet : Q ∈ excludedSet := by
  change obstructionPolynomial (absDetBlock Q) < 0
  rw [value_at_Q]
  norm_num

theorem excludedSet_excludes (A : Mat 6) (hA : A ∈ excludedSet) :
    ¬ InA4Orth 2 2 2 2 P P P A := negative_excludes A hA

/-- No factorization-existence or continuity assumption is supplied by the caller. -/
theorem open_exclusion_neighborhood :
    ∃ U : Set (Mat 6), IsOpen U ∧ Q ∈ U ∧
      ∀ A ∈ U, ¬ InA4Orth 2 2 2 2 P P P A :=
  ⟨excludedSet, excludedSet_open, Q_mem_excludedSet, excludedSet_excludes⟩

end GS.Revision.M4
