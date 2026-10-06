module

public import GS.UnitarySharing.Directions
public import GS.Unitary.PhaseKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A phase-kernel regression for complete-block unitary sharing

Repeating whole blocks does not remove the common scalar phase. The actual
spatial synthesis map has a nonzero kernel in positive dimension, for every
carrier, including carriers with no off-diagonal overlap. This is why the
unitary atlas uses a horizontal complement rather than the orthogonal
no-overlap injectivity argument.
-/
set_option autoImplicit false
noncomputable section
open Matrix GS GS.UnitaryGeometry
namespace GS.UnitarySharing
variable {n : ℕ}

/-- Multiplying every repeated identity block by the same phase respects ties. -/
theorem phaseGenerator_tied (b : ℕ) (τ : ℕ → ℕ) :
    TiedEntries b τ (phaseGenerator n) := by
  intro i j i' j' h h' hτ hi hj
  have he := TiedEntries.one (n := n) b τ i j i' j' h h' hτ hi hj
  change Complex.I * (1 : CMat n) i j = Complex.I * (1 : CMat n) i' j'
  exact congrArg (fun z : ℂ => Complex.I * z) he

theorem phaseGenerator_mem_shared (s : Pattern n) :
    phaseGenerator n ∈ sharedSkewSpace s.size s.label :=
  ⟨phaseGenerator_supported s.block, phaseGenerator_skewHermitian n,
    phaseGenerator_tied s.size s.label⟩

/-- Opposite physical scalar phases, with the requested block constraints. -/
def sharedPhasePair (right left : Pattern n) : PairGenerator right left :=
  (⟨phaseGenerator n, phaseGenerator_mem_shared left⟩,
   ⟨-phaseGenerator n,
     (sharedSkewSpace right.size right.label).neg_mem
       (phaseGenerator_mem_shared right)⟩)

theorem sharedPhasePair_ne_zero (right left : Pattern n) (hn : 0 < n) :
    sharedPhasePair right left ≠ 0 := by
  intro h
  have he := congrArg (fun v : PairGenerator right left => v.1.val) h
  exact phaseGenerator_ne_zero hn he

/-- Cancellation requires no invertibility or unitarity of the carrier. -/
theorem sharedPhasePair_in_kernel (right left : Pattern n) (X : CMat n) :
    pointMap right left X (sharedPhasePair right left) = 0 := by
  change phaseGenerator n * X + X * (-phaseGenerator n) = 0
  simp [phaseGenerator, Matrix.mul_smul, Matrix.smul_mul]

theorem pointMap_not_injective (right left : Pattern n) (X : CMat n)
    (hn : 0 < n) : ¬Function.Injective (pointMap right left X) := by
  intro hi
  apply sharedPhasePair_ne_zero right left hn
  apply hi
  rw [sharedPhasePair_in_kernel, map_zero]

end GS.UnitarySharing
