module

public import GS.Geodesics.BracketGeometry
public import GS.OverlapGeometry.GeodesicDynamics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact cancellation in the balanced overlap equation

The two exclusive generators evolve by opposite half-commutators with the
intersection generator. Their actual moving-generator acceleration has only
a symmetric square and a Frobenius-normal exclusive commutator left over.
This proves the zero projected-acceleration equation algebraically, without
assuming it as a differential-equation premise.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.OverlapGeometry

namespace GS.Geodesics
variable {n : ℕ}

def balancedGeneratorLeft (A Z : Mat n) : Mat n := A + (1/2 : ℝ) • Z
def balancedGeneratorRight (B Z : Mat n) : Mat n := B + (1/2 : ℝ) • Z
def balancedDerivativeLeft (A Z : Mat n) : Mat n :=
  (1/2 : ℝ) • generatorBracket Z A
def balancedDerivativeRight (B Z : Mat n) : Mat n :=
  (-1/2 : ℝ) • generatorBracket Z B

theorem balanced_bracket_identity (A B Z : Mat n) :
    generatorBracket (balancedGeneratorLeft A Z) (balancedGeneratorRight B Z) =
      generatorBracket A B - balancedDerivativeLeft A Z - balancedDerivativeRight B Z := by
  simp only [balancedGeneratorLeft, balancedGeneratorRight,
    balancedDerivativeLeft, balancedDerivativeRight, generatorBracket,
    Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The cancellation leaves a symmetric square and one exclusive commutator. -/
theorem balanced_acceleration_identity (A B Z : Mat n) :
    movingAccelerationCore (balancedGeneratorLeft A Z) (balancedGeneratorRight B Z)
      (balancedDerivativeLeft A Z) (balancedDerivativeRight B Z) =
      (A+B+Z)*(A+B+Z) + generatorBracket A B := by
  rw [movingAccelerationCore_eq, balanced_bracket_identity]
  have he : balancedGeneratorLeft A Z + balancedGeneratorRight B Z = A+B+Z := by
    simp only [balancedGeneratorLeft, balancedGeneratorRight]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  abel

theorem balanced_derivative_left_supported {a b : Fin n → ℕ} {A Z : Mat n}
    (hA : ExclusiveSupport a b A) (hZa : Supported a Z) (hZb : Supported b Z) :
    Supported a (balancedDerivativeLeft A Z) :=
  (intersection_commutator_exclusive hZa hZb hA).1.smul (1/2)

theorem balanced_derivative_right_supported {a b : Fin n → ℕ} {B Z : Mat n}
    (hB : ExclusiveSupport b a B) (hZa : Supported a Z) (hZb : Supported b Z) :
    Supported b (balancedDerivativeRight B Z) :=
  (intersection_commutator_exclusive hZb hZa hB).1.smul (-1/2)

theorem balanced_derivative_left_skew {A Z : Mat n}
    (hA : IsSkew A) (hZ : IsSkew Z) : IsSkew (balancedDerivativeLeft A Z) :=
  isSkew_smul _ (commutator_isSkew hZ hA)

theorem balanced_derivative_right_skew {B Z : Mat n}
    (hB : IsSkew B) (hZ : IsSkew Z) : IsSkew (balancedDerivativeRight B Z) :=
  isSkew_smul _ (commutator_isSkew hZ hB)

/-- Zero tangential acceleration for the balanced generator evolution. -/
theorem balanced_acceleration_masked_zero {a b : Fin n → ℕ} {A B Z : Mat n}
    (hA : ExclusiveSupport a b A) (hB : ExclusiveSupport b a B)
    (hkA : IsSkew A) (hkB : IsSkew B) (hkZ : IsSkew Z) :
    maskedSkew (fun i j => a i = a j ∨ b i = b j)
      (movingAccelerationCore (balancedGeneratorLeft A Z) (balancedGeneratorRight B Z)
        (balancedDerivativeLeft A Z) (balancedDerivativeRight B Z)) = 0 := by
  rw [balanced_acceleration_identity, maskedSkew_add]
  have hs : (A+B+Z)ᵀ = -(A+B+Z) := isSkew_add (isSkew_add hkA hkB) hkZ
  rw [maskedSkew_symmetric_zero _ _ (skew_square_symmetric _ hs)]
  change 0 + maskedSkew (fun i j => a i = a j ∨ b i = b j) (A*B-B*A) = 0
  rw [exclusive_commutator_maskedSkew_zero hA hB, add_zero]

/-- The fixed-coordinate overlap geodesic residual is actually zero. -/
theorem balanced_geodesicResidual_zero
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (A B Z : Mat n)
    (hA : ExclusiveSupport b₂ (b₁ ∘ σ.symm) A)
    (hB : ExclusiveSupport (b₁ ∘ σ.symm) b₂ B)
    (hZa : Supported b₂ Z) (hZb : Supported (b₁ ∘ σ.symm) Z)
    (hkA : IsSkew A) (hkB : IsSkew B) (hkZ : IsSkew Z) :
    geodesicResidual b₁ b₂ σ (balancedGeneratorLeft A Z) (balancedGeneratorRight B Z)
      (balancedDerivativeLeft A Z) (balancedDerivativeRight B Z) = 0 := by
  have hC : IsSkew (balancedGeneratorLeft A Z) :=
    isSkew_add hkA (isSkew_smul (1/2) hkZ)
  have hK : IsSkew (balancedGeneratorRight B Z) :=
    isSkew_add hkB (isSkew_smul (1/2) hkZ)
  rw [← movingAccelerationCore_projection b₁ b₂ σ
    (balancedGeneratorLeft A Z) (balancedGeneratorRight B Z)
    (balancedDerivativeLeft A Z) (balancedDerivativeRight B Z) hC hK
    (balanced_derivative_left_supported hA hZa hZb)
    (balanced_derivative_right_supported hB hZa hZb)
    (balanced_derivative_left_skew hkA hkZ)
    (balanced_derivative_right_skew hkB hkZ)]
  have hz := balanced_acceleration_masked_zero hA hB hkA hkB hkZ
  ext i j
  have he := congrFun (congrFun hz i) j
  by_cases hij : tangentUnion b₁ b₂ σ i j
  · have hij' : b₂ i = b₂ j ∨ (b₁ ∘ σ.symm) i = (b₁ ∘ σ.symm) j := hij
    simpa only [maskedSkew, mask, if_pos hij, if_pos hij', Matrix.zero_apply] using he
  · simp only [maskedSkew, mask, if_neg hij, Matrix.zero_apply]

end GS.Geodesics
