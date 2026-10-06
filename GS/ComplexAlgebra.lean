module

public import GS.Core
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Definitions and basic algebra for the unitary extension.
No assertion about the SU overlap projection is made here.
 -/

noncomputable section
open Matrix
namespace GS

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ*A=1 ∧ A*Aᴴ=1

def SpecialUnitary {n : ℕ} (A : CMat n) : Prop := Unitary A ∧ A.det=1

def SpecialOrthogonal {n : ℕ} (A : Mat n) : Prop := Orthogonal A ∧ A.det=1

def IsSkewHermitian {n : ℕ} (A : CMat n) : Prop := Aᴴ = -A

def skewHermitianPart {n : ℕ} (A : CMat n) : CMat n :=
  (1/2 : ℂ) • (A-Aᴴ)

def tracelessPart {n : ℕ} (A : CMat n) : CMat n :=
  A - (A.trace/(n : ℂ)) • (1 : CMat n)

namespace Unitary
variable {n : ℕ} {A B : CMat n}

theorem one : Unitary (1 : CMat n) := by constructor <;> simp

theorem conjTranspose (h : Unitary A) : Unitary Aᴴ := by
  constructor
  · simpa using h.2
  · simpa using h.1

theorem mul (hA : Unitary A) (hB : Unitary B) : Unitary (A*B) := by
  constructor
  · calc
      (A*B)ᴴ*(A*B) = Bᴴ*(Aᴴ*A)*B := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hA.1]; simpa using hB.1
  · calc
      (A*B)*(A*B)ᴴ = A*(B*Bᴴ)*Aᴴ := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hB.2]; simpa using hA.2

end Unitary
end GS
