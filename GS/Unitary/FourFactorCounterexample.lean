module

public import GS.Unitary.FourFactor

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact complex four-factor counterexample

The certified real matrix is embedded entrywise into the complex matrices.
Its determinant-modulus table is unchanged, so the universal unitary
obstruction rules out complex factors as well as real factors.
-/

noncomputable section
open Matrix
namespace GS.UnitaryFour
open GS.UnitaryGeometry

theorem ofRealMatrix_inA4 {n : ℕ} {b₁ b₂ b₃ b₄ : ℕ} {P₁ P₂ P₃ A : Mat n}
    (h : InA4 b₁ b₂ b₃ b₄ P₁ P₂ P₃ A) :
    CInA4 b₁ b₂ b₃ b₄ (ofRealMatrix P₁) (ofRealMatrix P₂)
      (ofRealMatrix P₃) (ofRealMatrix A) := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,he⟩
  refine ⟨ofRealMatrix B₁,ofRealMatrix B₂,ofRealMatrix B₃,ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃,ofRealMatrix_blockDiagonal hb₄,?_⟩
  simpa only [GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using
    congrArg ofRealMatrix he

@[simp] theorem normDetBlock_ofRealMatrix (A : Mat 6) :
    normDetBlock (ofRealMatrix A) = GS.M4.absDetBlock A := by
  funext i j
  simp only [normDetBlock, detBlock, ofRealMatrix_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- The permutation is the same prescribed perfect shuffle as in the real example. -/
theorem P_eq_cPermMatrix : P = cPermMatrix GS.M4.permutation := by
  ext i j
  rw [P, GS.M4.P_is_permutation]
  simp [ofRealMatrix, cPermMatrix, permMatrix]

theorem P_unitary : Unitary P := ofRealMatrix_unitary GS.M4.P_orthogonal

/-- The explicit algebraic matrix, now considered over ℂ. -/
def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem Q_unitary : Unitary Q := ofRealMatrix_unitary GS.M4.Q_orthogonal

theorem Q_mem_A4 : CInA4 2 2 2 2 P P P Q :=
  ofRealMatrix_inA4 GS.M4.Q_mem_A4

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := by
  intro h
  have hden : normDetBlock Q 2 1 * normDetBlock Q 1 0 * normDetBlock Q 1 1 ≠ 0 := by
    simpa only [Q, normDetBlock_ofRealMatrix] using GS.M4.obstruction_denominator_nonzero
  have hn := necessaryCondition Q h hden
  have hr : GS.M4.determinantObstruction GS.M4.Q := by
    simpa only [determinantObstruction, Q, normDetBlock_ofRealMatrix,
      GS.M4.determinantObstruction] using hn
  exact GS.M4.Q_violates_determinantObstruction hr

/-- Unconditional insufficiency of four unitary block factors in the fixed GS family. -/
theorem counterexample : CInA4 2 2 2 2 P P P Q ∧ Unitary Q ∧
    ¬ CInA4Unitary 2 2 2 2 P P P Q :=
  ⟨Q_mem_A4, Q_unitary, Q_not_mem_A4Unitary⟩

theorem inA4Unitary_implies_inA4_and_unitary {n : ℕ}
    {b₁ b₂ b₃ b₄ : ℕ} {P₁ P₂ P₃ A : CMat n}
    (hP₁ : Unitary P₁) (hP₂ : Unitary P₂) (hP₃ : Unitary P₃)
    (h : CInA4Unitary b₁ b₂ b₃ b₄ P₁ P₂ P₃ A) :
    CInA4 b₁ b₂ b₃ b₄ P₁ P₂ P₃ A ∧ Unitary A := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,hu₁,hu₂,hu₃,hu₄,rfl⟩
  exact ⟨⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,rfl⟩,
    (((((hu₄.mul hP₃).mul hu₃).mul hP₂).mul hu₂).mul hP₁).mul hu₁⟩

/-- Strict inclusion, rather than only failure of a chosen factorization. -/
theorem strictInclusion :
    {A : CMat 6 | CInA4Unitary 2 2 2 2 P P P A} ⊂
      {A : CMat 6 | CInA4 2 2 2 2 P P P A ∧ Unitary A} := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro A hA
    exact inA4Unitary_implies_inA4_and_unitary P_unitary P_unitary P_unitary hA
  · intro he
    have hm : Q ∈ {A : CMat 6 | CInA4 2 2 2 2 P P P A ∧ Unitary A} :=
      ⟨Q_mem_A4,Q_unitary⟩
    rw [← he] at hm
    exact Q_not_mem_A4Unitary hm

end GS.UnitaryFour
