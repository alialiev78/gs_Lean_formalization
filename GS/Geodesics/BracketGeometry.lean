module

public import GS.Extensions.GeodesicNormal

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The bracket geometry of two overlapping block algebras

The generators exclusive to one block algebra are orthogonal to the entire
other block algebra. Their mixed products vanish on the union of both block
patterns. In particular, their commutator is Frobenius normal to the sum of
the two generator spaces. Commutators with intersection generators preserve
the exclusive spaces. No nonoverlap assumption is used.
-/

noncomputable section
open Matrix GS GS.Extensions
open scoped BigOperators

namespace GS.Geodesics
variable {n : ℕ}

/-- Entries inside every block of the specified partition vanish. -/
def ZeroOnBlocks (b : Fin n → ℕ) (A : Mat n) : Prop :=
  ∀ i j, b i = b j → A i j = 0

/-- Support in the first partition, with the intersection entries removed. -/
def ExclusiveSupport (a b : Fin n → ℕ) (A : Mat n) : Prop :=
  Supported a A ∧ ZeroOnBlocks b A

theorem zeroOnBlocks_frobInner_zero {b : Fin n → ℕ} {A B : Mat n}
    (hA : ZeroOnBlocks b A) (hB : Supported b B) : frobInner A B = 0 := by
  apply frobInner_eq_zero_of_disjoint
  intro i j
  by_cases h : b i = b j
  · exact Or.inl (hA i j h)
  · exact Or.inr (hB i j h)

theorem exclusive_frobInner_zero {a b : Fin n → ℕ} {A B : Mat n}
    (hA : ExclusiveSupport a b A) (hB : Supported b B) : frobInner A B = 0 :=
  zeroOnBlocks_frobInner_zero hA.2 hB

/-- Multiplication by a supported matrix preserves the complementary zero pattern. -/
theorem zeroOnBlocks_mul_left {b : Fin n → ℕ} {H A : Mat n}
    (hH : Supported b H) (hA : ZeroOnBlocks b A) : ZeroOnBlocks b (H * A) := by
  intro i j hij
  change (∑ k, H i k * A k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : b i = b k
  · rw [hA k j (hik.symm.trans hij), mul_zero]
  · rw [hH i k hik, zero_mul]

theorem zeroOnBlocks_mul_right {b : Fin n → ℕ} {A H : Mat n}
    (hA : ZeroOnBlocks b A) (hH : Supported b H) : ZeroOnBlocks b (A * H) := by
  intro i j hij
  change (∑ k, A i k * H k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : b k = b j
  · rw [hA i k (hij.trans hkj.symm), zero_mul]
  · rw [hH k j hkj, mul_zero]

theorem zeroOnBlocks_sub {b : Fin n → ℕ} {A B : Mat n}
    (hA : ZeroOnBlocks b A) (hB : ZeroOnBlocks b B) : ZeroOnBlocks b (A-B) := by
  intro i j hij
  change A i j - B i j = 0
  rw [hA i j hij, hB i j hij, sub_self]

/-- Intersection generators preserve each exclusive space under the bracket. -/
theorem intersection_commutator_exclusive {a b : Fin n → ℕ} {H A : Mat n}
    (hHa : Supported a H) (hHb : Supported b H)
    (hA : ExclusiveSupport a b A) : ExclusiveSupport a b (H*A-A*H) := by
  refine ⟨?_, zeroOnBlocks_sub (zeroOnBlocks_mul_left hHb hA.2)
    (zeroOnBlocks_mul_right hA.2 hHb)⟩
  simpa only [sub_eq_add_neg] using
    (hHa.mul hA.1).add (hA.1.mul hHa).neg

theorem exclusive_commutator_intersection {a b : Fin n → ℕ} {A H : Mat n}
    (hA : ExclusiveSupport a b A)
    (hHa : Supported a H) (hHb : Supported b H) :
    ExclusiveSupport a b (A*H-H*A) := by
  refine ⟨?_, zeroOnBlocks_sub (zeroOnBlocks_mul_right hA.2 hHb)
    (zeroOnBlocks_mul_left hHb hA.2)⟩
  simpa only [sub_eq_add_neg] using
    (hA.1.mul hHa).add (hHa.mul hA.1).neg

/-- Every mixed product entry on either original block pattern is zero. -/
theorem exclusive_mul_zero_on_union {a b : Fin n → ℕ} {A B : Mat n}
    (hA : ExclusiveSupport a b A) (hB : ExclusiveSupport b a B)
    (i j : Fin n) (hij : a i = a j ∨ b i = b j) : (A*B) i j = 0 := by
  change (∑ k, A i k * B k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  rcases hij with ha | hb
  · by_cases hik : a i = a k
    · rw [hB.2 k j (hik.symm.trans ha), mul_zero]
    · rw [hA.1 i k hik, zero_mul]
  · by_cases hkj : b k = b j
    · rw [hA.2 i k (hb.trans hkj.symm), zero_mul]
    · rw [hB.1 k j hkj, mul_zero]

theorem exclusive_commutator_zero_on_union {a b : Fin n → ℕ} {A B : Mat n}
    (hA : ExclusiveSupport a b A) (hB : ExclusiveSupport b a B)
    (i j : Fin n) (hij : a i = a j ∨ b i = b j) :
    (A*B-B*A) i j = 0 := by
  change (A*B) i j - (B*A) i j = 0
  rw [exclusive_mul_zero_on_union hA hB i j hij,
    exclusive_mul_zero_on_union hB hA i j hij.symm, sub_self]

theorem exclusive_commutator_maskedSkew_zero {a b : Fin n → ℕ} {A B : Mat n}
    (hA : ExclusiveSupport a b A) (hB : ExclusiveSupport b a B) :
    maskedSkew (fun i j => a i = a j ∨ b i = b j) (A*B-B*A) = 0 := by
  ext i j
  by_cases hij : a i = a j ∨ b i = b j
  · have hji : a j = a i ∨ b j = b i := hij.elim
      (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    simp [maskedSkew, mask, hij, skew,
      exclusive_commutator_zero_on_union hA hB i j hij,
      exclusive_commutator_zero_on_union hA hB j i hji]
  · simp [maskedSkew, mask, hij]

/-- Frobenius normality against the full sum, even before skewness is imposed. -/
theorem exclusive_commutator_normal {a b : Fin n → ℕ} {A B D E : Mat n}
    (hA : ExclusiveSupport a b A) (hB : ExclusiveSupport b a B)
    (hD : Supported a D) (hE : Supported b E) :
    frobInner (A*B-B*A) (D+E) = 0 := by
  rw [frobInner_add_right]
  have hd : frobInner (A*B-B*A) D = 0 := by
    apply zeroOnBlocks_frobInner_zero _ hD
    intro i j hij
    exact exclusive_commutator_zero_on_union hA hB i j (Or.inl hij)
  have he : frobInner (A*B-B*A) E = 0 := by
    apply zeroOnBlocks_frobInner_zero _ hE
    intro i j hij
    exact exclusive_commutator_zero_on_union hA hB i j (Or.inr hij)
  rw [hd, he, add_zero]

theorem commutator_isSkew {A B : Mat n} (hA : IsSkew A) (hB : IsSkew B) :
    IsSkew (A*B-B*A) := by
  unfold IsSkew at *
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, hA, hB,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

end GS.Geodesics
