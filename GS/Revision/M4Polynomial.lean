module

public import GS.M4Necessary

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A denominator-free obstruction for the actual four-factor architecture

Revision of the determinant obstruction in the manuscript. Unlike
`GS.M4.necessaryCondition`, the main theorem below has NO nonzero-denominator
hypothesis. The proof is algebraic and includes degenerate blocks; it does not
appeal to a density argument.

-/
noncomputable section
open Matrix GS GS.M4
namespace GS.Revision.M4

/-- A polynomial in the nine *absolute block determinants*. As a function of
matrix entries this is continuous and semialgebraic, not generally polynomial,
because `absDetBlock` contains absolute values. -/
def obstructionPolynomial (d : Mat 3) : ℝ :=
  d 1 1 * (d 2 1 - d 0 2 * d 1 0) * (d 1 0 - d 0 2 * d 2 1)
    - d 0 0 * d 2 2 * d 1 0 * d 2 1

/-- The denominator-cleared expression factors even when some entries vanish. -/
theorem canonical_factorization (a b e f : Fin 3 → ℝ) :
    obstructionPolynomial (canonicalDetTable a b e f) =
      (canonicalDetTable a b e f 1 1 *
       canonicalDetTable a b e f 2 1 *
       canonicalDetTable a b e f 1 0) *
      ((1 - (b 0)^2 * (e 1)^2) * (1 - (a 1)^2 * (f 2)^2)
        - (b 1)^2 * (f 1)^2) := by
  simp [obstructionPolynomial, canonicalDetTable]
  ring

/-- Necessity for the canonical determinant table. Nonnegativity hypotheses
are essential here: the table represents absolute entries of orthogonal blocks. -/
theorem canonical_nonnegative (a b e f : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (he : ∀ i, 0 ≤ e i) (hf : ∀ i, 0 ≤ f i)
    (hW : ∀ i, (a i)^2 + (b i)^2 = 1)
    (hY : ∀ i, (e i)^2 + (f i)^2 = 1) :
    0 ≤ obstructionPolynomial (canonicalDetTable a b e f) := by
  have hb0 : (b 0)^2 ≤ 1 := by nlinarith [hW 0, sq_nonneg (a 0)]
  have hf2 : (f 2)^2 ≤ 1 := by nlinarith [hY 2, sq_nonneg (e 2)]
  have hgap : 0 ≤ (1 - (b 0)^2 * (e 1)^2) *
      (1 - (a 1)^2 * (f 2)^2) - (b 1)^2 * (f 1)^2 :=
    sub_nonneg.mpr (scalar_obstruction (a 1) (b 0) (e 1) (f 2)
      (b 1) (f 1) (hW 1) (hY 1) hb0 hf2)
  have h11 : 0 ≤ canonicalDetTable a b e f 1 1 := by
    change 0 ≤ b 2 * b 0 * f 0 * f 2
    exact mul_nonneg (mul_nonneg (mul_nonneg (hb 2) (hb 0)) (hf 0)) (hf 2)
  have h21 : 0 ≤ canonicalDetTable a b e f 2 1 := by
    change 0 ≤ a 1 * a 2 * f 2 * e 0
    exact mul_nonneg (mul_nonneg (mul_nonneg (ha 1) (ha 2)) (hf 2)) (he 0)
  have h10 : 0 ≤ canonicalDetTable a b e f 1 0 := by
    change 0 ≤ a 2 * b 0 * e 0 * e 1
    exact mul_nonneg (mul_nonneg (mul_nonneg (ha 2) (hb 0)) (he 0)) (he 1)
  rw [canonical_factorization]
  exact mul_nonneg (mul_nonneg (mul_nonneg h11 h21) h10) hgap

theorem core_nonnegative (W Y : Fin 3 → Mat 2)
    (hW : ∀ i, Orthogonal (W i)) (hY : ∀ i, Orthogonal (Y i)) :
    0 ≤ obstructionPolynomial (absDetBlock (P * assemble W * P * assemble Y * P)) := by
  rw [core_absDetTable W Y hW hY]
  apply canonical_nonnegative
  · intro i; exact abs_nonneg _
  · intro i; exact abs_nonneg _
  · intro i; exact abs_nonneg _
  · intro i; exact abs_nonneg _
  · intro i; exact (orthogonal2_abs (W i) (hW i)).2.2
  · intro i; exact (orthogonal2_abs (Y i) (hY i)).2.2

/-- Universal necessity for the original concrete m=4 matrix class.
There is no assumption that the block determinants are nonzero. -/
theorem necessary (A : Mat 6) (h : InA4Orth 2 2 2 2 P P P A) :
    0 ≤ obstructionPolynomial (absDetBlock A) := by
  rcases h with ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄,
    ho₁, ho₂, ho₃, ho₄, he⟩
  let C₀ := P * B₃ * P * B₂ * P
  have he' : A = B₄ * C₀ * B₁ := by
    rw [he]
    simp only [product4, C₀, Matrix.mul_assoc]
  have hd : absDetBlock A = absDetBlock C₀ := by
    funext i j
    rw [he']
    exact absDetBlock_outer B₄ C₀ B₁ hb₄ hb₁ ho₄ ho₁ i j
  rw [hd]
  have hb₂' := block_diagonal_decompose B₂ hb₂
  have hb₃' := block_diagonal_decompose B₃ hb₃
  have hcore : C₀ = P * assemble (fun i => block2 B₃ i i) * P *
      assemble (fun i => block2 B₂ i i) * P := by
    dsimp [C₀]
    conv_lhs => rw [hb₂', hb₃']
  rw [hcore]
  exact core_nonnegative _ _ (block2_orthogonal B₃ hb₃ ho₃)
    (block2_orthogonal B₂ hb₂ ho₂)

/-- Exact margin for the witness already constructed in M4Certificate. -/
theorem value_at_Q : obstructionPolynomial (absDetBlock Q) = -(891 / 65536 : ℝ) := by
  rw [absDetTable_Q]
  change (3 / 8 : ℝ) * (3 * root6 / 16 - (3 / 8) * (3 * root6 / 16)) *
      (3 * root6 / 16 - (3 / 8) * (3 * root6 / 16)) -
      (3 * root6 / 16) * (3 * root6 / 16) *
      (3 * root6 / 16) * (3 * root6 / 16) = -(891 / 65536 : ℝ)
  have h : root6^2 = 6 := root6_sq
  calc
    _ = (675 / 131072 : ℝ) * root6^2 - (81 / 65536 : ℝ) * (root6^2)^2 := by ring
    _ = _ := by rw [h]; norm_num

theorem negative_excludes (A : Mat 6)
    (h : obstructionPolynomial (absDetBlock A) < 0) :
    ¬ InA4Orth 2 2 2 2 P P P A := by
  intro hA
  exact (not_lt_of_ge (necessary A hA)) h

/-- A second route to the old counterexample, now with a polynomial margin. -/
theorem counterexample_with_margin :
    InA4 2 2 2 2 P P P Q ∧ Orthogonal Q ∧
    ¬ InA4Orth 2 2 2 2 P P P Q ∧
    obstructionPolynomial (absDetBlock Q) = -(891 / 65536 : ℝ) := by
  refine ⟨Q_mem_A4, Q_orthogonal, ?_, value_at_Q⟩
  apply negative_excludes
  rw [value_at_Q]
  norm_num

end GS.Revision.M4
