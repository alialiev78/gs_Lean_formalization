module

public import GS.CS.Thin

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The complete real square cosine-sine decomposition

The thin decomposition is completed using the orthogonal complement. No
invertibility or distinctness is imposed on the singular values.
-/

noncomputable section
open Matrix
namespace GS.CS

def split {n : ℕ} (A B : Mat n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks A 0 0 B

@[simp] theorem split_mul {n : ℕ} (A B C D : Mat n) :
    split A B * split C D = split (A * C) (B * D) := by
  simp [split, Matrix.fromBlocks_multiply]

@[simp] theorem split_transpose {n : ℕ} (A B : Mat n) :
    (split A B)ᵀ = split Aᵀ Bᵀ := by simp [split, Matrix.fromBlocks_transpose]

@[simp] theorem split_one (n : ℕ) : split (1 : Mat n) 1 = 1 := Matrix.fromBlocks_one

theorem split_orthogonal {n : ℕ} {A B : Mat n}
    (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (split A B) := by
  constructor <;> simp [hA.1, hA.2, hB.1, hB.2]

/-- Canonical CS matrix, with the upper-right sine block negative. -/
def csMatrix {n : ℕ} (c s : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks (diagonal c) (-diagonal s) (diagonal s) (diagonal c)

theorem csMatrix_orthogonal {n : ℕ} (c s : Fin n → ℝ)
    (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) : Orthogonal (csMatrix c s) := by
  apply Orthogonal.of_transpose_mul
  rw [csMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases hij : i = j
  all_goals simp [Matrix.diagonal_transpose, Matrix.transpose_neg,
    Matrix.diagonal_mul_diagonal, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.diagonal_apply, Matrix.one_apply, hij]
  all_goals nlinarith [h j]

/-- Every square real orthogonal matrix has a complete cosine-sine
decomposition into two orthogonal blocks on each side and a canonical CS
matrix in the middle. The result includes all degenerate singular values. -/
theorem exists_square_cs {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hQ : Orthogonal Q) :
    ∃ (U₁ U₂ V₁ V₂ : Mat n) (c s : Fin n → ℝ),
      Orthogonal U₁ ∧ Orthogonal U₂ ∧ Orthogonal V₁ ∧ Orthogonal V₂ ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      Q = split U₁ U₂ * csMatrix c s * split V₁ V₂ := by
  let A := Q.toBlocks₁₁
  let B := Q.toBlocks₁₂
  let C := Q.toBlocks₂₁
  let D := Q.toBlocks₂₂
  have hblocks : Q = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Q).symm
  have hfirst : Aᵀ * A + Cᵀ * C = 1 := by
    have hh := congrArg Matrix.toBlocks₁₁ hQ.1
    simpa [hblocks, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  obtain ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, hcs, he₁, he₂⟩ :=
    exists_thin_cs A C hfirst
  let L := split U₁ U₂
  let T := split V (1 : Mat n)
  let K := csMatrix c s
  let E := U₁ᵀ * B
  let F := U₂ᵀ * D
  let R := fromBlocks (diagonal c) E (diagonal s) F
  have hL : Orthogonal L := split_orthogonal hU₁ hU₂
  have hT : Orthogonal T := split_orthogonal hV Orthogonal.one
  have hK : Orthogonal K := csMatrix_orthogonal c s (fun i => (hcs i).2.2)
  have hleft₁ : U₁ᵀ * (A * V) = diagonal c := by
    rw [he₁, ← Matrix.mul_assoc, hU₁.1, Matrix.one_mul]
  have hleft₂ : U₂ᵀ * (C * V) = diagonal s := by
    rw [he₂, ← Matrix.mul_assoc, hU₂.1, Matrix.one_mul]
  have hR : R = Lᵀ * Q * T := by
    rw [hblocks]
    simp [R, L, T, split, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.mul_assoc, hleft₁, hleft₂, E, F]
  have hRo : Orthogonal R := by rw [hR]; exact (hL.transpose.mul hQ).mul hT
  let H := Kᵀ * R
  have hHo : Orthogonal H := hK.transpose.mul hRo
  let X := diagonal c * E + diagonal s * F
  let W := -diagonal s * E + diagonal c * F
  have hH : H = fromBlocks 1 X 0 W := by
    change Kᵀ * R = _
    dsimp [K, R, csMatrix, X, W]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      by_cases hij : i = j
      all_goals simp [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply, Matrix.one_apply, hij]
      nlinarith [(hcs j).2.2]
    · simp
    · ext i j
      simp [Matrix.diagonal_transpose, Matrix.transpose_neg, Matrix.neg_mul,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      split_ifs <;> ring
    · simp
  have hX : X = 0 := by
    have hh := congrArg Matrix.toBlocks₁₂ hHo.1
    simpa [hH, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hH' : H = split 1 W := by simpa [split, hX] using hH
  have hW : Orthogonal W := by
    apply Orthogonal.of_transpose_mul
    have hh := congrArg Matrix.toBlocks₂₂ hHo.1
    simpa [hH', split, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hKR : R = K * split 1 W := by
    rw [← hH']
    change R = K * (Kᵀ * R)
    rw [← Matrix.mul_assoc, hK.2, Matrix.one_mul]
  refine ⟨U₁, U₂, Vᵀ, W, c, s, hU₁, hU₂, hV.transpose, hW, hcs, ?_⟩
  calc
    Q = L * R * Tᵀ := by
      rw [hR]
      calc
        Q = (L * Lᵀ) * Q * (T * Tᵀ) := by rw [hL.2, hT.2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = L * K * (split (1 : Mat n) W * Tᵀ) := by rw [hKR]; simp only [Matrix.mul_assoc]
    _ = _ := by simp [T, L, K]

end GS.CS
