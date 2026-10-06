module

public import GS.Unitary.Support

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Permutations act by unitary simultaneous relabeling of complex entries. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {n : ℕ}

def cPermMatrix (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0

@[simp] theorem mul_cPerm_apply (A : CMat n) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (A*cPermMatrix σ) i j = A i (σ j) := by simp [Matrix.mul_apply, cPermMatrix]
@[simp] theorem cPerm_mul_apply (σ : Equiv.Perm (Fin n)) (A : CMat n) (i j : Fin n) :
    (cPermMatrix σ*A) i j = A (σ.symm i) j := by
  rw [Matrix.mul_apply]
  calc
    (∑ k, cPermMatrix σ i k*A k j) = cPermMatrix σ i (σ.symm i)*A (σ.symm i) j := by
      apply Finset.sum_eq_single (σ.symm i)
      · intro k hk hki
        have hik : i ≠ σ k := by
          intro h; apply hki; simpa using (congrArg σ.symm h).symm
        simp [cPermMatrix, hik]
      · simp
    _ = A (σ.symm i) j := by simp [cPermMatrix]
@[simp] theorem cPerm_conjTranspose (σ : Equiv.Perm (Fin n)) :
    (cPermMatrix σ)ᴴ = cPermMatrix σ.symm := by
  ext i j
  have he : j = σ i ↔ i = σ.symm j := by
    constructor
    · intro h; simpa using (congrArg σ.symm h).symm
    · intro h; simpa using (congrArg σ h).symm
  simp [cPermMatrix, Matrix.conjTranspose_apply, he]
theorem cPerm_unitary (σ : Equiv.Perm (Fin n)) : Unitary (cPermMatrix σ) := by
  constructor <;> ext i j <;>
    simp [cPerm_conjTranspose, cPerm_mul_apply, cPermMatrix, Matrix.one_apply]
theorem cPerm_conjugate_apply (σ : Equiv.Perm (Fin n)) (A : CMat n) (i j : Fin n) :
    (cPermMatrix σ*A*(cPermMatrix σ)ᴴ) i j = A (σ.symm i) (σ.symm j) := by simp

theorem cSupported_perm_conjugate_iff (block : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CSupported (block ∘ σ.symm) (cPermMatrix σ*A*(cPermMatrix σ)ᴴ) ↔ CSupported block A := by
  constructor
  · intro h i j hij
    have hz := h (σ i) (σ j) (by simpa using hij)
    simpa using hz
  · intro h i j hij
    simpa using h (σ.symm i) (σ.symm j) hij

theorem cSupported_perm_back {block : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
    {R : CMat n} (hR : CSupported (fun i => block (σ i)) R) :
    CSupported block (cPermMatrix σ*R*(cPermMatrix σ)ᴴ) := by
  intro i j hij
  rw [cPerm_conjugate_apply]
  apply hR
  simpa only [Equiv.apply_symm_apply] using hij

theorem cPermuted_gram_supported {block : Fin n → ℕ} {B : CMat n}
    (hB : CSupported block B) (σ : Equiv.Perm (Fin n)) :
    CSupported (fun i => block (σ i)) ((cPermMatrix σ)ᴴ*Bᴴ*B*cPermMatrix σ) := by
  have hh : CSupported block (Bᴴ*B) := hB.conjTranspose.mul hB
  intro i j hij
  have he : ((cPermMatrix σ)ᴴ*Bᴴ*B*cPermMatrix σ) i j = (Bᴴ*B) (σ i) (σ j) := by
    rw [cPerm_conjTranspose]
    simpa only [Matrix.mul_assoc, cPerm_conjTranspose, Equiv.symm_symm] using
      cPerm_conjugate_apply σ.symm (Bᴴ*B) i j
  rw [he]
  exact hh _ _ hij

theorem cPerm_trans_matrix (σ τ : Equiv.Perm (Fin n)) :
    cPermMatrix (σ.trans τ) = cPermMatrix τ*cPermMatrix σ := by
  ext i j
  rw [cPerm_mul_apply]
  change (if i=τ (σ j) then (1:ℂ) else 0) =
    (if τ.symm i=σ j then (1:ℂ) else 0)
  by_cases h : i=τ (σ j)
  · subst i; simp
  · have hn : τ.symm i ≠ σ j := by
      intro hh; apply h; simpa using congrArg τ hh
    simp [h,hn]
@[simp] theorem cPerm_refl : cPermMatrix (Equiv.refl (Fin n)) = 1 := by
  ext i j; simp [cPermMatrix, Matrix.one_apply]
end GS.UnitaryGeometry
