module

public import GS.Unitary.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Real-Frobenius projection onto supported traceless skew-Hermitian matrices.
Masks in this module contain every diagonal entry; this is essential for the
trace correction to preserve support. No special-unitary quotient claim is made. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem trace_skewHermitian_conj {A : CMat n} (hA : IsSkewHermitian A) :
    star A.trace = -A.trace := by
  rw [← Matrix.trace_conjTranspose, hA, Matrix.trace_neg]

theorem tracelessPart_trace (A : CMat n) : (tracelessPart A).trace = 0 := by
  by_cases hn : n=0
  · subst n; simp [Matrix.trace]
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [tracelessPart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      div_mul_cancel₀ _ hc]

theorem tracelessPart_fixed {A : CMat n} (hA : A.trace = 0) : tracelessPart A = A := by
  simp [tracelessPart, hA]

theorem tracelessPart_isSkewHermitian {A : CMat n} (hA : IsSkewHermitian A) :
    IsSkewHermitian (tracelessPart A) := by
  have ht := trace_skewHermitian_conj hA
  change Aᴴ = -A at hA
  simp only [tracelessPart, IsSkewHermitian, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_div₀, star_natCast,
    ht, hA, neg_div, neg_smul]
  abel

def tracelessSkewHermitianSpace : Submodule ℝ (CMat n) where
  carrier := {A | IsSkewHermitian A ∧ A.trace=0}
  zero_mem' := ⟨skewHermitian_zero, by simp⟩
  add_mem' := by
    rintro A B ⟨hkA,htA⟩ ⟨hkB,htB⟩
    exact ⟨skewHermitian_add hkA hkB, by simp [Matrix.trace_add, htA, htB]⟩
  smul_mem' := by
    rintro a A ⟨hkA,htA⟩
    exact ⟨skewHermitian_real_smul a hkA, by simp [Matrix.trace_smul, htA]⟩

theorem tracelessPart_add (A B : CMat n) :
    tracelessPart (A+B) = tracelessPart A + tracelessPart B := by
  simp only [tracelessPart, Matrix.trace_add, add_div, add_smul]
  abel

theorem tracelessPart_real_smul (a : ℝ) (A : CMat n) :
    tracelessPart (a • A) = a • tracelessPart A := by
  ext i j
  simp only [tracelessPart, Matrix.trace_smul, Matrix.sub_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul]
  ring

def tracelessPartMap : CMat n →ₗ[ℝ] CMat n where
  toFun := tracelessPart
  map_add' := tracelessPart_add
  map_smul' := tracelessPart_real_smul

/-- Scalar identity matrices are orthogonal to every trace-zero matrix. -/
theorem cFrobInner_scalar_one_of_trace_zero (a : ℂ) (X : CMat n) (hX : X.trace=0) :
    cFrobInner (a • (1 : CMat n)) X = 0 := by
  simp [cFrobInner_eq_re_trace, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.trace_smul, hX]

def maskedTracelessSkewHermitian (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CMat n := tracelessPart (maskedSkewHermitian p A)

def maskedTracelessSkewHermitianMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    CMat n →ₗ[ℝ] CMat n := tracelessPartMap.comp (maskedSkewHermitianMap p)

theorem tracelessPart_hasSupport {p : Fin n → Fin n → Prop}
    (hp : ∀ i, p i i) {A : CMat n} (hA : CHasSupport p A) :
    CHasSupport p (tracelessPart A) := by
  intro i j hij
  have hne : i ≠ j := by intro he; subst j; exact hij (hp i)
  simp [tracelessPart, Matrix.one_apply, hne, hA i j hij]

theorem maskedTracelessSkewHermitian_mem {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A : CMat n) :
    CHasSupport p (maskedTracelessSkewHermitian p A) ∧
    IsSkewHermitian (maskedTracelessSkewHermitian p A) ∧
    (maskedTracelessSkewHermitian p A).trace=0 := by
  exact ⟨tracelessPart_hasSupport hdiag (maskedSkewHermitian_hasSupport _ _),
    tracelessPart_isSkewHermitian (maskedSkewHermitian_isSkewHermitian hp A),
    tracelessPart_trace _⟩

theorem maskedTracelessSkewHermitian_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    {A : CMat n} (hs : CHasSupport p A) (hk : IsSkewHermitian A) (ht : A.trace=0) :
    maskedTracelessSkewHermitian p A = A := by
  rw [maskedTracelessSkewHermitian, maskedSkewHermitian_fixed hs hk, tracelessPart_fixed ht]

theorem maskedTracelessSkewHermitian_residual_orthogonal
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (A X : CMat n) (hs : CHasSupport p X) (hk : IsSkewHermitian X) (ht : X.trace=0) :
    cFrobInner (A-maskedTracelessSkewHermitian p A) X = 0 := by
  have he : A-maskedTracelessSkewHermitian p A = (A-maskedSkewHermitian p A) +
      ((maskedSkewHermitian p A).trace/(n : ℂ)) • (1 : CMat n) := by
    unfold maskedTracelessSkewHermitian tracelessPart
    abel
  rw [he, cFrobInner_add_left, maskedSkewHermitian_residual_orthogonal A X hs hk,
    cFrobInner_scalar_one_of_trace_zero _ X ht, add_zero]

theorem maskedTracelessSkewHermitian_pythagorean
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A X : CMat n)
    (hs : CHasSupport p X) (hk : IsSkewHermitian X) (ht : X.trace=0) :
    cFrobSq (A-X) = cFrobSq (A-maskedTracelessSkewHermitian p A) +
      cFrobSq (maskedTracelessSkewHermitian p A-X) := by
  let Y := maskedTracelessSkewHermitian p A
  obtain ⟨hsY,hkY,htY⟩ := maskedTracelessSkewHermitian_mem hp hdiag A
  have hsd : CHasSupport p (Y-X) := by
    intro i j hij
    change maskedTracelessSkewHermitian p A i j-X i j = 0
    rw [hsY i j hij, hs i j hij, sub_self]
  have hkd : IsSkewHermitian (Y-X) := skewHermitianSpace.sub_mem hkY hk
  have htd : (Y-X).trace=0 := by simp [Matrix.trace_sub, Y, htY, ht]
  have ho := maskedTracelessSkewHermitian_residual_orthogonal A (Y-X) hsd hkd htd
  have he : A-X = (A-Y)+(Y-X) := by abel
  rw [he, cFrobSq_add, ho]
  ring

theorem maskedTracelessSkewHermitian_minimizes
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A X : CMat n)
    (hs : CHasSupport p X) (hk : IsSkewHermitian X) (ht : X.trace=0) :
    cFrobSq (A-maskedTracelessSkewHermitian p A) ≤ cFrobSq (A-X) := by
  rw [maskedTracelessSkewHermitian_pythagorean hp hdiag A X hs hk ht]
  exact le_add_of_nonneg_right (cFrobSq_nonneg _)

theorem maskedTracelessSkewHermitian_unique_minimizer
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A X : CMat n)
    (hs : CHasSupport p X) (hk : IsSkewHermitian X) (ht : X.trace=0)
    (he : cFrobSq (A-X) = cFrobSq (A-maskedTracelessSkewHermitian p A)) :
    X=maskedTracelessSkewHermitian p A := by
  rw [maskedTracelessSkewHermitian_pythagorean hp hdiag A X hs hk ht] at he
  have hz : cFrobSq (maskedTracelessSkewHermitian p A-X)=0 := by linarith
  exact (sub_eq_zero.mp ((cFrobSq_eq_zero_iff _).mp hz)).symm

@[simp] theorem maskedTracelessSkewHermitian_idempotent
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A : CMat n) :
    maskedTracelessSkewHermitian p (maskedTracelessSkewHermitian p A) =
      maskedTracelessSkewHermitian p A := by
  obtain ⟨hs,hk,ht⟩ := maskedTracelessSkewHermitian_mem hp hdiag A
  exact maskedTracelessSkewHermitian_fixed hs hk ht

theorem maskedTracelessSkewHermitian_fixed_iff
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A : CMat n) :
    maskedTracelessSkewHermitian p A = A ↔
      CHasSupport p A ∧ IsSkewHermitian A ∧ A.trace=0 := by
  constructor
  · intro h
    rw [← h]
    exact maskedTracelessSkewHermitian_mem hp hdiag _
  · rintro ⟨hs,hk,ht⟩
    exact maskedTracelessSkewHermitian_fixed hs hk ht

end GS.UnitaryGeometry
