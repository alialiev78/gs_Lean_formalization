module

public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Actual least-squares projection in the real Frobenius geometry onto
symmetric masks of skew-Hermitian matrices, including the imaginary diagonal. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem skewHermitianPart_eq_real_smul (A : CMat n) :
    skewHermitianPart A = (1/2 : ℝ) • (A-Aᴴ) := by
  ext i j
  simp [skewHermitianPart, Complex.real_smul]

theorem isSkewHermitian_skewHermitianPart (A : CMat n) :
    IsSkewHermitian (skewHermitianPart A) := by
  rw [skewHermitianPart_eq_real_smul]
  unfold IsSkewHermitian
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg]
  congr 1
  abel

theorem skewHermitianPart_fixed {A : CMat n} (h : IsSkewHermitian A) :
    skewHermitianPart A = A := by
  change Aᴴ = -A at h
  ext i j
  simp only [skewHermitianPart, h, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
    smul_eq_mul]
  ring

theorem skewHermitianPart_add (A B : CMat n) :
    skewHermitianPart (A+B) = skewHermitianPart A + skewHermitianPart B := by
  simp only [skewHermitianPart_eq_real_smul, Matrix.conjTranspose_add]
  have he : A+B-(Aᴴ+Bᴴ) = (A-Aᴴ)+(B-Bᴴ) := by abel
  rw [he, smul_add]
theorem skewHermitianPart_real_smul (a : ℝ) (A : CMat n) :
    skewHermitianPart (a • A) = a • skewHermitianPart A := by
  simp only [skewHermitianPart_eq_real_smul, Matrix.conjTranspose_smul, star_trivial,
    ← smul_sub, smul_smul]
  rw [mul_comm]

def skewHermitianPartMap : CMat n →ₗ[ℝ] CMat n where
  toFun := skewHermitianPart
  map_add' := skewHermitianPart_add
  map_smul' := skewHermitianPart_real_smul

theorem cMask_isSkewHermitian {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) {A : CMat n} (hA : IsSkewHermitian A) :
    IsSkewHermitian (cMask p A) := by
  change Aᴴ = -A at hA
  change (cMask p A)ᴴ = -cMask p A
  rw [cMask_conjTranspose hp, hA]
  ext i j; by_cases h : p i j <;> simp [cMask, h]

def maskedSkewHermitian (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CMat n := cMask p (skewHermitianPart A)

def maskedSkewHermitianMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    CMat n →ₗ[ℝ] CMat n where
  toFun := maskedSkewHermitian p
  map_add' A B := by
    simp only [maskedSkewHermitian, skewHermitianPart_add, cMask_add]
  map_smul' a A := by
    simp only [maskedSkewHermitian, skewHermitianPart_real_smul, cMask_real_smul,
      RingHom.id_apply]

theorem cMask_inner_of_supported {p : Fin n → Fin n → Prop} [DecidableRel p]
    (A X : CMat n) (hX : CHasSupport p X) : cFrobInner (cMask p A) X = cFrobInner A X := by
  unfold cFrobInner
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  by_cases h : p i j
  · simp [cMask, h]
  · simp [cMask, h, hX i j h]

theorem skewHermitianPart_inner_of_isSkewHermitian (A X : CMat n)
    (hX : IsSkewHermitian X) : cFrobInner (skewHermitianPart A) X = cFrobInner A X := by
  have ht : cFrobInner Aᴴ X = -cFrobInner A X := by
    calc
      cFrobInner Aᴴ X = cFrobInner A Xᴴ := by
        simpa using (cFrobInner_conjTranspose Aᴴ X).symm
      _ = cFrobInner A (-X) := by rw [hX]
      _ = -cFrobInner A X := by
        rw [cFrobInner_comm A (-X), cFrobInner_neg_left, cFrobInner_comm X A]
  rw [skewHermitianPart_eq_real_smul, cFrobInner_real_smul_left, cFrobInner_sub_left, ht]
  ring

theorem maskedSkewHermitian_residual_orthogonal {p : Fin n → Fin n → Prop} [DecidableRel p]
    (A X : CMat n) (hX : CHasSupport p X) (hk : IsSkewHermitian X) :
    cFrobInner (A-maskedSkewHermitian p A) X = 0 := by
  unfold maskedSkewHermitian
  rw [cFrobInner_sub_left, cMask_inner_of_supported _ _ hX,
    skewHermitianPart_inner_of_isSkewHermitian _ _ hk, sub_self]

theorem maskedSkewHermitian_hasSupport (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CHasSupport p (maskedSkewHermitian p A) := cMask_hasSupport _ _
theorem maskedSkewHermitian_isSkewHermitian {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) : IsSkewHermitian (maskedSkewHermitian p A) :=
  cMask_isSkewHermitian hp (isSkewHermitian_skewHermitianPart A)

theorem maskedSkewHermitian_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    {A : CMat n} (hs : CHasSupport p A) (hk : IsSkewHermitian A) :
    maskedSkewHermitian p A = A := by
  rw [maskedSkewHermitian, skewHermitianPart_fixed hk, cMask_fixed hs]
@[simp] theorem maskedSkewHermitian_idempotent {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) :
    maskedSkewHermitian p (maskedSkewHermitian p A) = maskedSkewHermitian p A :=
  maskedSkewHermitian_fixed (maskedSkewHermitian_hasSupport _ _)
    (maskedSkewHermitian_isSkewHermitian hp _)

theorem maskedSkewHermitian_pythagorean {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A X : CMat n) (hs : CHasSupport p X) (hk : IsSkewHermitian X) :
    cFrobSq (A-X) = cFrobSq (A-maskedSkewHermitian p A) +
      cFrobSq (maskedSkewHermitian p A-X) := by
  let Y := maskedSkewHermitian p A
  have hsY := maskedSkewHermitian_hasSupport p A
  have hkY := maskedSkewHermitian_isSkewHermitian hp A
  have hsd : CHasSupport p (Y-X) := by
    intro i j hij
    change maskedSkewHermitian p A i j-X i j = 0
    rw [hsY i j hij, hs i j hij, sub_self]
  have hkd : IsSkewHermitian (Y-X) := skewHermitianSpace.sub_mem hkY hk
  have ho := maskedSkewHermitian_residual_orthogonal A (Y-X) hsd hkd
  have he : A-X = (A-Y)+(Y-X) := by abel
  rw [he, cFrobSq_add, ho]
  ring

theorem maskedSkewHermitian_minimizes {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A X : CMat n) (hs : CHasSupport p X) (hk : IsSkewHermitian X) :
    cFrobSq (A-maskedSkewHermitian p A) ≤ cFrobSq (A-X) := by
  rw [maskedSkewHermitian_pythagorean hp A X hs hk]
  exact le_add_of_nonneg_right (cFrobSq_nonneg _)

theorem maskedSkewHermitian_unique_minimizer {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A X : CMat n) (hs : CHasSupport p X) (hk : IsSkewHermitian X)
    (he : cFrobSq (A-X) = cFrobSq (A-maskedSkewHermitian p A)) :
    X = maskedSkewHermitian p A := by
  rw [maskedSkewHermitian_pythagorean hp A X hs hk] at he
  have hz : cFrobSq (maskedSkewHermitian p A-X) = 0 := by linarith
  exact (sub_eq_zero.mp ((cFrobSq_eq_zero_iff _).mp hz)).symm

theorem maskedSkewHermitian_fixed_iff {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) :
    maskedSkewHermitian p A = A ↔ CHasSupport p A ∧ IsSkewHermitian A := by
  constructor
  · intro h
    rw [← h]
    exact ⟨maskedSkewHermitian_hasSupport _ _, maskedSkewHermitian_isSkewHermitian hp _⟩
  · rintro ⟨hs,hk⟩; exact maskedSkewHermitian_fixed hs hk

/-- Skew-Hermitian diagonal entries have zero real part, but need not vanish. -/
theorem isSkewHermitian_diagonal_re_zero {A : CMat n} (hA : IsSkewHermitian A) (i : Fin n) :
    (A i i).re = 0 := by
  have he := congrArg Complex.re (congrFun (congrFun hA i) i)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
    Complex.conj_re, Complex.neg_re] at he
  linarith
end GS.UnitaryGeometry
