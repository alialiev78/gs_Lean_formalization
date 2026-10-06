module

public import GS.UnitaryCS.Thin

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The complete complex square cosine-sine decomposition

The thin decomposition is completed using the unitary complement. No
invertibility or distinctness is imposed on the singular values.
-/

noncomputable section
open Matrix
namespace GS.UnitaryCS

@[simp] theorem conjTranspose_realDiagonal {n : ℕ} (d : Fin n → ℝ) :
    (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

@[simp] theorem star_real_function {n : ℕ} (d : Fin n → ℝ) :
    star (fun i => (d i : ℂ)) = fun i => (d i : ℂ) := by ext i; simp

def split {n : ℕ} (A B : CMat n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks A 0 0 B

@[simp] theorem split_mul {n : ℕ} (A B C D : CMat n) :
    split A B * split C D = split (A * C) (B * D) := by
  simp [split, Matrix.fromBlocks_multiply]

@[simp] theorem split_conjTranspose {n : ℕ} (A B : CMat n) :
    (split A B)ᴴ = split Aᴴ Bᴴ := by simp [split, Matrix.fromBlocks_conjTranspose]

@[simp] theorem split_one (n : ℕ) : split (1 : CMat n) 1 = 1 := Matrix.fromBlocks_one

theorem split_unitary {n : ℕ} {A B : CMat n}
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (split A B) := by
  constructor <;> simp [hA.1, hA.2, hB.1, hB.2]

/-- Canonical CS matrix, with the upper-right sine block negative. -/
def csMatrix {n : ℕ} (c s : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks (diagonal (fun i => (c i : ℂ))) (-diagonal (fun i => (s i : ℂ))) (diagonal (fun i => (s i : ℂ))) (diagonal (fun i => (c i : ℂ)))

theorem csMatrix_unitary {n : ℕ} (c s : Fin n → ℝ)
    (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) : IsUnitary (csMatrix c s) := by
  apply IsUnitary.of_conjTranspose_mul
  rw [csMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases hij : i = j
  all_goals simp [Matrix.diagonal_conjTranspose, Matrix.conjTranspose_neg,
    Matrix.diagonal_mul_diagonal, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.diagonal_apply, Matrix.one_apply, hij]
  all_goals try ring1
  all_goals
    have hc : (c j : ℂ)^2 + (s j : ℂ)^2 = 1 := by exact_mod_cast h j
    linear_combination hc

/-- Every square complex unitary matrix has a complete cosine-sine
decomposition into two unitary blocks on each side and a canonical CS
matrix in the middle. The result includes all degenerate singular values. -/
theorem exists_square_cs {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hQ : IsUnitary Q) :
    ∃ (U₁ U₂ V₁ V₂ : CMat n) (c s : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V₁ ∧ IsUnitary V₂ ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      Q = split U₁ U₂ * csMatrix c s * split V₁ V₂ := by
  let A := Q.toBlocks₁₁
  let B := Q.toBlocks₁₂
  let C := Q.toBlocks₂₁
  let D := Q.toBlocks₂₂
  have hblocks : Q = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Q).symm
  have hfirst : Aᴴ * A + Cᴴ * C = 1 := by
    have hh := congrArg Matrix.toBlocks₁₁ hQ.1
    simpa [hblocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  obtain ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, hcs, he₁, he₂⟩ :=
    exists_thin_cs A C hfirst
  let L := split U₁ U₂
  let T := split V (1 : CMat n)
  let K := csMatrix c s
  let E := U₁ᴴ * B
  let F := U₂ᴴ * D
  let R := fromBlocks (diagonal (fun i => (c i : ℂ))) E (diagonal (fun i => (s i : ℂ))) F
  have hL : IsUnitary L := split_unitary hU₁ hU₂
  have hT : IsUnitary T := split_unitary hV IsUnitary.one
  have hK : IsUnitary K := csMatrix_unitary c s (fun i => (hcs i).2.2)
  have hleft₁ : U₁ᴴ * (A * V) = diagonal (fun i => (c i : ℂ)) := by
    rw [he₁, ← Matrix.mul_assoc, hU₁.1, Matrix.one_mul]
  have hleft₂ : U₂ᴴ * (C * V) = diagonal (fun i => (s i : ℂ)) := by
    rw [he₂, ← Matrix.mul_assoc, hU₂.1, Matrix.one_mul]
  have hR : R = Lᴴ * Q * T := by
    rw [hblocks]
    simp [R, L, T, split, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.mul_assoc, hleft₁, hleft₂, E, F]
  have hRo : IsUnitary R := by rw [hR]; exact (hL.conjTranspose.mul hQ).mul hT
  let H := Kᴴ * R
  have hHo : IsUnitary H := hK.conjTranspose.mul hRo
  let X := diagonal (fun i => (c i : ℂ)) * E + diagonal (fun i => (s i : ℂ)) * F
  let W := -diagonal (fun i => (s i : ℂ)) * E + diagonal (fun i => (c i : ℂ)) * F
  have hH : H = fromBlocks 1 X 0 W := by
    change Kᴴ * R = _
    dsimp [K, R, csMatrix, X, W]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      by_cases hij : i = j
      all_goals simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply, Matrix.one_apply, hij]
      have hc : (c j : ℂ)^2 + (s j : ℂ)^2 = 1 := by exact_mod_cast (hcs j).2.2
      linear_combination hc
    · simp [star_real_function]
    · ext i j
      simp [Matrix.diagonal_conjTranspose, Matrix.conjTranspose_neg, Matrix.neg_mul,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      split_ifs <;> ring
    · simp [Pi.star_def]
  have hX : X = 0 := by
    have hh := congrArg Matrix.toBlocks₁₂ hHo.1
    simpa [hH, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hH' : H = split 1 W := by simpa [split, hX] using hH
  have hW : IsUnitary W := by
    apply IsUnitary.of_conjTranspose_mul
    have hh := congrArg Matrix.toBlocks₂₂ hHo.1
    simpa [hH', split, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hKR : R = K * split 1 W := by
    rw [← hH']
    change R = K * (Kᴴ * R)
    rw [← Matrix.mul_assoc, hK.2, Matrix.one_mul]
  refine ⟨U₁, U₂, Vᴴ, W, c, s, hU₁, hU₂, GS.Unitary.conjTranspose hV, hW, hcs, ?_⟩
  calc
    Q = L * R * Tᴴ := by
      rw [hR]
      calc
        Q = (L * Lᴴ) * Q * (T * Tᴴ) := by rw [hL.2, hT.2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = L * K * (split (1 : CMat n) W * Tᴴ) := by rw [hKR]; simp only [Matrix.mul_assoc]
    _ = _ := by simp [T, L, K]

end GS.UnitaryCS
