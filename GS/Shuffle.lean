module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Perfect shuffle, expressed using pair coordinates before flattening.
The pair (r,s) is the manuscript's scalar coordinate r*b+s.
 -/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

/-- Row-major flattening of a coordinate pair. -/
def flatIndex {k b : ℕ} (r : Fin k) (s : Fin b) : Fin (k*b) :=
  ⟨r.val * b + s.val, by
    have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt r.isLt)
    nlinarith [s.isLt]⟩

/-- In pair coordinates, perfect shuffle is simply (r,s) -> (s,r). -/
def shuffleEquiv (k b : ℕ) : (Fin k × Fin b) ≃ (Fin b × Fin k) := Equiv.prodComm _ _

theorem shuffle_flat_value {k b : ℕ} (r : Fin k) (s : Fin b) :
    (flatIndex (shuffleEquiv k b (r,s)).1 (shuffleEquiv k b (r,s)).2).val = s.val*k+r.val := rfl

/-- This is literal conjugation by the coordinate permutation, in entry form. -/
def shuffleConjugate {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ) :
    Matrix (Fin b × Fin k) (Fin b × Fin k) ℝ :=
  fun i j => A (i.2,i.1) (j.2,j.1)

/-- Explicit block-diagonal embedding, useful also for shared blocks. -/
def blockMatrix {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) ℝ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

/-- The diagonal blocks in the shuffled view become diagonal small matrices. -/
theorem shuffle_block_entry {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) ℝ)
    (s t : Fin b) (r v : Fin k) :
    shuffleConjugate (blockMatrix B) (s,r) (t,v) =
      if r = v then B r s t else 0 := rfl

/-- Explicit Kronecker product, to keep the index convention independent of notation. -/
def kron {a b : ℕ} (U : Mat a) (W : Mat b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℝ :=
  fun i j => U i.1 j.1 * W i.2 j.2

theorem shuffle_kron {k b : ℕ} (U : Mat k) (W : Mat b) :
    shuffleConjugate (kron U W) = kron W U := by
  ext i j
  exact mul_comm _ _

theorem shuffle_twice {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ) :
    shuffleConjugate (shuffleConjugate A) = A := by
  ext i j
  rcases i with ⟨r,s⟩
  rcases j with ⟨v,t⟩
  rfl

/-- A scalar-index consequence used in the nonoverlap condition.
Two coordinates in one b-sized interval, congruent modulo k>=b, coincide. -/
theorem no_offdiagonal_overlap (i j b k : ℕ) (hb : 0 < b) (hbk : b ≤ k)
    (hblock : i / b = j / b) (hmod : i % k = j % k) : i = j := by
  have hi := Nat.mod_lt i hb
  have hj := Nat.mod_lt j hb
  have hiB := Nat.mod_add_div i b
  have hjB := Nat.mod_add_div j b
  rw [hblock] at hiB
  have hij : i < j + b := by omega
  have hji : j < i + b := by omega
  have hiK := Nat.mod_add_div i k
  have hjK := Nat.mod_add_div j k
  rw [hmod] at hiK
  rcases lt_trichotomy (i / k) (j / k) with hq | hq | hq
  · have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hq)
    simp only [Nat.mul_succ, Nat.mul_add, Nat.mul_one] at hm
    omega
  · rw [hq] at hiK
    omega
  · have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hq)
    simp only [Nat.mul_succ, Nat.mul_add, Nat.mul_one] at hm
    omega

/-- Exact overlap predicate printed in the manuscript. -/
def OverlapIndex (b₂ k₁ i j : ℕ) : Prop :=
  i ≠ j ∧ i / b₂ = j / b₂ ∧ i % k₁ = j % k₁

end GS
