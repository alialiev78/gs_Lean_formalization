module

public import GS.Unitary.Factorization
public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Entrywise extension from real orthogonal to complex unitary matrices -/

noncomputable section
open Matrix
namespace GS.UnitaryGeometry

/-- Entrywise scalar extension of real matrices. -/
def ofRealMatrix {n : ℕ} (A : Mat n) : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_apply {n : ℕ} (A : Mat n) (i j : Fin n) :
    ofRealMatrix A i j = (A i j : ℂ) := rfl

@[simp] theorem ofRealMatrix_mul {n : ℕ} (A B : Mat n) :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one {n : ℕ} :
    ofRealMatrix (1 : Mat n) = 1 := by
  exact map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose {n : ℕ} (A : Mat n) :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  ext i j
  simp [ofRealMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem ofRealMatrix_unitary {n : ℕ} {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) := by
  constructor
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.1
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.2

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) := by
  intro i j hij
  simp [h i j hij]


@[simp] theorem ofRealMatrix_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ofRealMatrix (permMatrix σ) = cPermMatrix σ := by
  ext i j
  simp [ofRealMatrix, cPermMatrix, permMatrix]

theorem ofRealMatrix_inA3Unitary {n : ℕ} {b₁ b₂ b₃ : ℕ} {P₁ P₂ A : Mat n}
    (h : InA3Orth b₁ b₂ b₃ P₁ P₂ A) :
    CInA3Unitary b₁ b₂ b₃ (ofRealMatrix P₁) (ofRealMatrix P₂) (ofRealMatrix A) := by
  rcases h with ⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,ho₁,ho₂,ho₃,he⟩
  refine ⟨ofRealMatrix B₁,ofRealMatrix B₂,ofRealMatrix B₃,
    ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃,ofRealMatrix_unitary ho₁,
    ofRealMatrix_unitary ho₂,ofRealMatrix_unitary ho₃,?_⟩
  simpa only [GS.product3, product3, ofRealMatrix_mul] using congrArg ofRealMatrix he

end GS.UnitaryGeometry
