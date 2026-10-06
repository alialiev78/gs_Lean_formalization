module

public import GS.Unitary.Factorization
public import GS.NonmanifoldCompletion.BlockRealization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Row-block Gram invariants for the unitary three-factor family

The Gram matrices of all two-by-two blocks in a fixed block row commute.
The assertion permits zero entries and does not require generic factors.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryNonmanifold
open GS.UnitaryGeometry

def cBlock {q : ℕ} (M : CMat (q*2)) (i j : Fin q) : CMat 2 :=
  fun a b => M (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))

def diagTwo (a b : ℂ) : CMat 2 := Matrix.diagonal ![a,b]

def BlockSandwich {q : ℕ} (M : CMat (q*2)) : Prop :=
  ∃ (L R : Fin q → CMat 2) (A B : CMat q),
    (∀ i, Unitary (L i)) ∧ (∀ j, Unitary (R j)) ∧
    Unitary A ∧ Unitary B ∧
    ∀ i j, cBlock M i j = L i * diagTwo (A i j) (B i j) * R j

def rowGram {q : ℕ} (M : CMat (q*2)) (i j : Fin q) : CMat 2 :=
  cBlock M i j * (cBlock M i j)ᴴ

theorem diagonal_gram_commute (d e : Fin 2 → ℂ) :
    ((diagonal d * (diagonal d)ᴴ) * (diagonal e * (diagonal e)ᴴ)) =
      ((diagonal e * (diagonal e)ᴴ) * (diagonal d * (diagonal d)ᴴ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq]
    ring
  · simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, h]

theorem sandwich_gram (L D R : CMat 2) (hR : Unitary R) :
    (L * D * R) * (L * D * R)ᴴ = L * (D * Dᴴ) * Lᴴ := by
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = L * D * (R * Rᴴ) * Dᴴ * Lᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR.2]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem conjugate_commute (L D E : CMat 2) (hL : Unitary L)
    (hDE : D * E = E * D) :
    (L * D * Lᴴ) * (L * E * Lᴴ) =
      (L * E * Lᴴ) * (L * D * Lᴴ) := by
  calc
    _ = L * D * (Lᴴ * L) * E * Lᴴ := by simp only [Matrix.mul_assoc]
    _ = L * (D * E) * Lᴴ := by rw [hL.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = L * (E * D) * Lᴴ := by rw [hDE]
    _ = L * E * (Lᴴ * L) * D * Lᴴ := by rw [hL.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem blockSandwich_row_gram_commute {q : ℕ} {M : CMat (q*2)}
    (hM : BlockSandwich M) (i j k : Fin q) :
    rowGram M i j * rowGram M i k = rowGram M i k * rowGram M i j := by
  rcases hM with ⟨L,R,A,B,hL,hR,_,_,he⟩
  unfold rowGram
  rw [he i j, he i k, sandwich_gram _ _ _ (hR j), sandwich_gram _ _ _ (hR k)]
  exact conjugate_commute _ _ _ (hL i)
    (diagonal_gram_commute ![A i j,B i j] ![A i k,B i k])

end GS.UnitaryNonmanifold
