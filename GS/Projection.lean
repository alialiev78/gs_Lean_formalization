module

public import GS.Frobenius

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Frobenius projections in the two-factor calculation

Theorems concern the explicit linear spaces of supported skew matrices. The
identification of these spaces with a manifold tangent bundle is a SEPARATE
obligation in `Specifications.lean`.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsSkew (A : Matrix ι ι ℝ) : Prop := Aᵀ = -A

def skew (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j - A j i) / 2

def symmPart (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j + A j i) / 2

/-- Support masks are predicates on ordered pairs, not matrix inverses. -/
def mask (p : ι → ι → Prop) [DecidableRel p] (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if p i j then A i j else 0

def HasSupport (p : ι → ι → Prop) (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, ¬p i j → A i j = 0

def MaskSymmetric (p : ι → ι → Prop) : Prop := ∀ i j, p i j ↔ p j i

def maskedSkew (p : ι → ι → Prop) [DecidableRel p]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := mask p (skew A)

theorem isSkew_skew (A : Matrix ι ι ℝ) : IsSkew (skew A) := by
  ext i j
  change (A j i - A i j) / 2 = -((A i j - A j i) / 2)
  ring

theorem skew_of_isSkew {A : Matrix ι ι ℝ} (hA : IsSkew A) : skew A = A := by
  ext i j
  have he : A j i = -A i j := congrFun (congrFun hA i) j
  change (A i j - A j i) / 2 = A i j
  rw [he]
  ring

theorem skew_eq_smul (A : Matrix ι ι ℝ) : skew A = (1 / 2 : ℝ) • (A - Aᵀ) := by
  ext i j
  change (A i j - A j i) / 2 = (1 / 2 : ℝ) * (A i j - A j i)
  ring

theorem symm_add_skew (A : Matrix ι ι ℝ) : symmPart A + skew A = A := by
  ext i j
  change (A i j + A j i) / 2 + (A i j - A j i) / 2 = A i j
  ring

theorem isSkew_diagonal_zero {A : Matrix ι ι ℝ} (hA : IsSkew A) (i : ι) :
    A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun hA i) i
  linarith

theorem mask_hasSupport (p : ι → ι → Prop) [DecidableRel p] (A : Matrix ι ι ℝ) :
    HasSupport p (mask p A) := by
  intro i j hij
  simp [mask, hij]

theorem mask_fixed {p : ι → ι → Prop} [DecidableRel p] {A : Matrix ι ι ℝ}
    (hA : HasSupport p A) : mask p A = A := by
  ext i j
  by_cases h : p i j
  · simp [mask, h]
  · simp [mask, h, hA i j h]

theorem mask_idempotent (p : ι → ι → Prop) [DecidableRel p] (A : Matrix ι ι ℝ) :
    mask p (mask p A) = mask p A := mask_fixed (mask_hasSupport p A)

theorem mask_isSkew {p : ι → ι → Prop} [DecidableRel p]
    (hp : MaskSymmetric p) {A : Matrix ι ι ℝ} (hA : IsSkew A) :
    IsSkew (mask p A) := by
  ext i j
  have he : A j i = -A i j := congrFun (congrFun hA i) j
  by_cases h : p i j
  · have h' : p j i := (hp i j).mp h
    simp [mask, h, h', he]
  · have h' : ¬p j i := fun h' => h ((hp i j).mpr h')
    simp [mask, h, h']

theorem mask_inner_of_supported {p : ι → ι → Prop} [DecidableRel p]
    (A X : Matrix ι ι ℝ) (hX : HasSupport p X) :
    frobInner (mask p A) X = frobInner A X := by
  unfold frobInner
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : p i j
  · simp [mask, h]
  · simp [mask, h, hX i j h]

theorem skew_inner_of_isSkew (A X : Matrix ι ι ℝ) (hX : IsSkew X) :
    frobInner (skew A) X = frobInner A X := by
  have ht : frobInner Aᵀ X = -frobInner A X := by
    calc
      frobInner Aᵀ X = frobInner A Xᵀ := by
        simpa using (frobInner_transpose Aᵀ X).symm
      _ = frobInner A (-X) := by rw [hX]
      _ = -frobInner A X := by
        rw [frobInner_comm A (-X), frobInner_neg_left, frobInner_comm X A]
  rw [skew_eq_smul, frobInner_smul_left, frobInner_sub_left, ht]
  ring

/-- Normal equation, with the actual finite Frobenius inner product. -/
theorem maskedSkew_residual_orthogonal {p : ι → ι → Prop} [DecidableRel p]
    (A X : Matrix ι ι ℝ) (hX : HasSupport p X) (hskew : IsSkew X) :
    frobInner (A - maskedSkew p A) X = 0 := by
  unfold maskedSkew
  rw [frobInner_sub_left, mask_inner_of_supported _ _ hX,
    skew_inner_of_isSkew _ _ hskew]
  ring

/-- Least-squares optimality (not merely a formula for a candidate). -/
theorem maskedSkew_minimizes {p : ι → ι → Prop} [DecidableRel p]
    (hp : MaskSymmetric p) (A X : Matrix ι ι ℝ)
    (hX : HasSupport p X) (hskew : IsSkew X) :
    frobSq (A - maskedSkew p A) ≤ frobSq (A - X) := by
  let Y := maskedSkew p A
  have hsY : HasSupport p Y := mask_hasSupport p (skew A)
  have hkY : IsSkew Y := mask_isSkew hp (isSkew_skew A)
  have hs : HasSupport p (Y - X) := by
    intro i j hij
    change Y i j - X i j = 0
    rw [hsY i j hij, hX i j hij, sub_self]
  have hk : IsSkew (Y - X) := by
    unfold IsSkew at *
    rw [Matrix.transpose_sub, hkY, hskew]
    abel
  have ho : frobInner (A - Y) (Y - X) = 0 :=
    maskedSkew_residual_orthogonal A (Y - X) hs hk
  have he : A - X = (A - Y) + (Y - X) := by abel
  rw [he, frobSq_add, ho]
  have hn := frobSq_nonneg (Y - X)
  dsimp [Y] at *
  linarith

/-- Pointwise equal splitting in the overlap has minimal parameter norm. -/
theorem overlap_half_minimal (a c w : ℝ) (h : c + w = a) :
    (a / 2)^2 + (a / 2)^2 ≤ c^2 + w^2 := by
  rw [← h]
  nlinarith [sq_nonneg (c - w)]

theorem overlap_half_unique (a c w : ℝ) (h : c + w = a)
    (hmin : c^2 + w^2 = (a / 2)^2 + (a / 2)^2) :
    c = a / 2 ∧ w = a / 2 := by
  have he : (c - w)^2 = 0 := by
    rw [← h] at hmin
    nlinarith
  have hw : c - w = 0 := (sq_eq_zero_iff).mp he
  constructor <;> linarith

/-- The two coordinates of a support-union decomposition. -/
def splitLeft (p q : ι → ι → Prop) [DecidableRel p] [DecidableRel q]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if p i j then (if q i j then skew A i j / 2 else skew A i j) else 0

def splitRight (p q : ι → ι → Prop) [DecidableRel p] [DecidableRel q]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if q i j then (if p i j then skew A i j / 2 else skew A i j) else 0

theorem split_sum (p q : ι → ι → Prop) [DecidableRel p] [DecidableRel q]
    (A : Matrix ι ι ℝ) :
    splitLeft p q A + splitRight p q A = maskedSkew (fun i j => p i j ∨ q i j) A := by
  classical
  ext i j
  by_cases hp : p i j <;> by_cases hq : q i j <;>
    simp [splitLeft, splitRight, maskedSkew, mask, hp, hq] <;> ring

/-- If the second factor is written in old coordinates, its mask is conjugated too. -/
theorem conjugated_mask_apply (σ : Equiv.Perm ι) (p : ι → ι → Prop)
    [DecidableRel p] (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * mask p A * (permMatrix σ)ᵀ) i j =
      if p (σ.symm i) (σ.symm j) then A (σ.symm i) (σ.symm j) else 0 := by
  rw [perm_conjugate_apply]
  rfl

end GS
