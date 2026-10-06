module

public import GS.LieAction.CompactQuotient
public import GS.Shuffle
public import GS.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))

theorem common_matrix_diagonal (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) {T : Mat n}
    (h₁ : Supported block₁ T) (h₂ : Supported (fun i => block₂ (σ i)) T) :
    T = Matrix.diagonal (fun i => T i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have ht : T i j = 0 := by
      by_cases h : block₁ i = block₁ j
      · have h' : block₂ (σ i) ≠ block₂ (σ j) := by
          intro h''
          exact hij (hn (Prod.ext h h''))
        exact h₂ i j h'
      · exact h₁ i j h
    simpa [Matrix.diagonal, hij] using ht

theorem commonRight_diagonal (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (T : commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ)) :
    T.val.val = Matrix.diagonal (fun i => T.val.val i i) :=
  common_matrix_diagonal σ hn T.val.property.1
    ((commonRight_mem_iff σ T.val).mp T.property)

theorem orthogonal_diagonal_sign {T : Mat n} (hT : Orthogonal T)
    (hd : T = Matrix.diagonal (fun i => T i i)) (i : Fin n) :
    T i i = 1 ∨ T i i = -1 := by
  have he := congrArg (fun A : Mat n => (Aᵀ * A) i i) hd
  have hg : (Tᵀ * T) i i = 1 := by rw [hT.1]; simp
  change (Tᵀ * T) i i = _ at he
  rw [he] at hg
  have hs : T i i * T i i = 1 := by
    simpa [Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply] using hg
  have hz : (T i i - 1) * (T i i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · left; linarith
  · right; linarith

/-- Explicit parameterization by n Boolean signs. -/
def signMatrix (ε : Fin n → Bool) : Mat n :=
  Matrix.diagonal (fun i => if ε i then (1 : ℝ) else -1)

theorem signMatrix_supported (block : Fin n → ℕ) (ε : Fin n → Bool) :
    Supported block (signMatrix ε) := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (congrArg block h)
  simp [signMatrix, Matrix.diagonal, hne]

theorem signMatrix_orthogonal (ε : Fin n → Bool) : Orthogonal (signMatrix ε) := by
  apply GS.Orthogonal.of_transpose_mul
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : ε i <;>
      simp [signMatrix, Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply, h]
  · simp [signMatrix, Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, hij, Ne.symm hij]

def commonFromSigns (σ : Equiv.Perm (Fin n)) (ε : Fin n → Bool) :
    commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) :=
  ⟨⟨signMatrix ε, signMatrix_supported block₁ ε, signMatrix_orthogonal ε⟩,
    (common_support_iff σ (signMatrix ε)).mpr (signMatrix_supported _ ε)⟩

def signsFromCommon (σ : Equiv.Perm (Fin n))
    (T : commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ)) :
    Fin n → Bool := fun i => decide (T.val.val i i = 1)

theorem signMatrix_recovers_common (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (T : commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ)) :
    signMatrix (signsFromCommon σ T) = T.val.val := by
  have hd := commonRight_diagonal σ hn T
  ext i j
  by_cases hij : i = j
  · subst j
    rcases orthogonal_diagonal_sign T.val.property.2 hd i with h | h
    · norm_num [signMatrix, signsFromCommon, h]
    · norm_num [signMatrix, signsFromCommon, h]
  · have ht : T.val.val i j = 0 := by
      have h := congrFun (congrFun hd i) j
      simpa [Matrix.diagonal, hij] using h
    simp [signMatrix, Matrix.diagonal, hij, ht]

/-- A set equivalence is enough for the exact stabilizer cardinality. -/
def commonSignsEquiv (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) ≃
      (Fin n → Bool) where
  toFun := signsFromCommon σ
  invFun := commonFromSigns σ
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    exact signMatrix_recovers_common σ hn T
  right_inv ε := by
    funext i
    cases h : ε i <;> norm_num [signsFromCommon, commonFromSigns, signMatrix, h]

def stabilizerSignsEquiv (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    PointStabilizer block₁ block₂ (permMatrix σ) ≃ (Fin n → Bool) :=
  (stabilizerRightEquiv (permMatrix σ) (perm_orthogonal σ)).toEquiv.trans
    (commonSignsEquiv σ hn)

theorem stabilizer_finite (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    Finite (PointStabilizer block₁ block₂ (permMatrix σ)) :=
  Finite.of_injective (stabilizerSignsEquiv σ hn) (stabilizerSignsEquiv σ hn).injective

theorem stabilizer_card (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    Nat.card (PointStabilizer block₁ block₂ (permMatrix σ)) = 2 ^ n := by
  calc
    _ = Nat.card (Fin n → Bool) := Nat.card_congr (stabilizerSignsEquiv σ hn)
    _ = 2 ^ n := by simp

/-- Each actual fibre, not just the fibre at P, has the same sign ambiguity. -/
def fibreStabilizerEquiv (P : Mat n) (g : FactorGroup block₁ block₂) :
    {h : FactorGroup block₁ block₂ //
      orbitMap block₁ block₂ P h = orbitMap block₁ block₂ P g} ≃
      PointStabilizer block₁ block₂ P where
  toFun h := ⟨g⁻¹ * h.val, (orbit_fibre_iff P g h.val).mp h.property.symm⟩
  invFun k := ⟨g * k.val, by
    change (g * k.val) • P = g • P
    rw [mul_smul, show k.val • P = P from k.property]⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

theorem fibre_card (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂) :
    Nat.card {h : FactorGroup block₁ block₂ //
      orbitMap block₁ block₂ (permMatrix σ) h =
      orbitMap block₁ block₂ (permMatrix σ) g} = 2 ^ n := by
  rw [Nat.card_congr (fibreStabilizerEquiv (permMatrix σ) g)]
  exact stabilizer_card σ hn

/-- The scalar non-overlap argument already checked in GS.Shuffle identifies
the two labels in shuffled coordinates. -/
theorem quotient_remainder_labels_injective (b k : ℕ) (hb : 0 < b) (hbk : b ≤ k) :
    Function.Injective (fun i : Fin n => (i.val / b, i.val % k)) := by
  intro i j hij
  apply Fin.ext
  exact GS.no_offdiagonal_overlap i.val j.val b k hb hbk
    (congrArg Prod.fst hij) (congrArg Prod.snd hij)

/-- The manuscript's k₁ ≥ b₂ condition implies the exact support condition.
The hypothesis hσ fixes the documented scalar convention for perfect shuffle;
it is not an assumption about a stabilizer, derivative, or factorization. -/
theorem perfectShuffle_noOverlap (b₁ k₁ b₂ : ℕ) (hN : n = k₁ * b₁)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (σ i).val = (i.val % b₁) * k₁ + i.val / b₁) :
    NoOffDiagonalOverlap (fun i : Fin n => i.val / b₁)
      (fun i : Fin n => i.val / b₂) σ := by
  have hmod : ∀ i : Fin n, (σ i).val % k₁ = i.val / b₁ := by
    intro i
    have hq : i.val / b₁ < k₁ := by
      apply (Nat.div_lt_iff_lt_mul hb₁).mpr
      simpa only [hN] using i.isLt
    rw [hσ]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hq]
  intro i j hij
  have h₁ := congrArg Prod.fst hij
  have h₂ := congrArg Prod.snd hij
  apply σ.injective
  apply Fin.ext
  exact GS.no_offdiagonal_overlap (σ i).val (σ j).val b₂ k₁ hb₂ hbk h₂
    (by rw [hmod i, hmod j]; exact h₁)

/-- No common skew generator survives when off-diagonal overlap is absent. -/
theorem common_skew_eq_zero (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) {T : Mat n}
    (h₁ : Supported block₁ T) (h₂ : Supported (fun i => block₂ (σ i)) T)
    (hsk : IsSkew T) : T = 0 := by
  have hd := common_matrix_diagonal σ hn h₁ h₂
  ext i j
  by_cases hij : i = j
  · subst j
    have hs := congrFun (congrFun hsk i) i
    change T i i = -T i i at hs
    change T i i = 0
    linarith
  · have hs := congrFun (congrFun hd i) j
    simpa [Matrix.diagonal, hij] using hs

end GS.LieAction
