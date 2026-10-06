module

public import Mathlib.Tactic.Abel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Algebraic invariance of the corrected three-factor exponential word

The evaluator is arbitrary.  Consequently this lemma applies to the matrix
exponential without making any analytic assertion about that exponential.
The geometric geodesic theorem and the phase projection identities are separate.
-/

namespace GS.SharedGeodesics

variable {A : Type*} [Ring A]

/-- The corrected word in common matrix coordinates. -/
def correctedWord (E : A → A) (C D U V : A) : A :=
  E (C + U) * E (-(U + V)) * E (D + V)

/-- A stabilizer shift changes the two initial generators and phase corrections
in opposite directions.  Each argument of the corrected word is unchanged. -/
theorem correctedWord_gauge_invariant (E : A → A) (C D U V K : A) :
    correctedWord E (C + K) (D - K) (U - K) (V + K) =
      correctedWord E C D U V := by
  have h₁ : (C + K) + (U - K) = C + U := by abel
  have h₂ : (U - K) + (V + K) = U + V := by abel
  have h₃ : (D - K) + (V + K) = D + V := by abel
  simp only [correctedWord, h₁, h₂, h₃]

/-- The initial matrix velocity is unchanged by the same gauge shift. -/
theorem generatorSum_gauge_invariant (C D K : A) :
    (C + K) + (D - K) = C + D := by
  abel

/-- Without phase overlap the corrected word reduces to two factors. -/
theorem correctedWord_zero_phase (E : A → A) (hE : E 0 = 1) (C D : A) :
    correctedWord E C D 0 0 = E C * E D := by
  simp [correctedWord, hE]

end GS.SharedGeodesics
