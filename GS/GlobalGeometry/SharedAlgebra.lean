module

public import GS.GlobalGeometry.ExactSharing
public import GS.Continuation.ExponentialBasics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Algebra and exponential closure of actual tied blocks

Full physical blocks have identical local index sets. This gives closure of
actual entry sharing under multiplication and under the matrix exponential.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation Filter
open scoped BigOperators Topology

namespace GS.GlobalGeometry

variable {n b : ℕ} {τ : ℕ → ℕ} {A B C : Mat n}

namespace TiedEntries

theorem zero (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (0 : Mat n) := by
  intro i j i' j' _ _ _ _ _
  rfl

theorem one (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (1 : Mat n) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by
    constructor
    · intro h
      subst j
      apply Fin.ext
      have hm : i'.val % b = j'.val % b := hi.symm.trans hj
      have hdi := Nat.mod_add_div i'.val b
      have hdj := Nat.mod_add_div j'.val b
      rw [hm, hij'] at hdi
      omega
    · intro h
      subst j'
      apply Fin.ext
      have hm : i.val % b = j.val % b := hi.trans hj.symm
      have hdi := Nat.mod_add_div i.val b
      have hdj := Nat.mod_add_div j.val b
      rw [hm, hij] at hdi
      omega
  simp only [Matrix.one_apply, he]

theorem add (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A + B) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.add_apply, hA i j i' j' h h' hτ hi hj,
    hB i j i' j' h h' hτ hi hj]

theorem smul (a : ℝ) (hA : TiedEntries b τ A) : TiedEntries b τ (a • A) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.smul_apply, hA i j i' j' h h' hτ hi hj]

theorem neg (hA : TiedEntries b τ A) : TiedEntries b τ (-A) := by
  simpa only [neg_one_smul] using hA.smul (-1)

theorem transpose (hA : TiedEntries b τ A) : TiedEntries b τ Aᵀ := by
  intro i j i' j' h h' hτ hi hj
  exact hA j i j' i' h.symm h'.symm (by simpa only [← h, ← h'] using hτ) hj hi

end TiedEntries

/-- The index with prescribed local coordinate in the physical block of `i`. -/
def localBlockIndex (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) : Fin n :=
  ⟨i.val / b * b + k.val, by
    have hin : i.val / b < n / b := (Nat.div_lt_iff_lt_mul hb).mpr (by
      simpa only [Nat.div_mul_cancel hbn] using i.isLt)
    calc
      i.val / b * b + k.val < i.val / b * b + b := Nat.add_lt_add_left k.isLt _
      _ = (i.val / b + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n / b * b := Nat.mul_le_mul_right b hin
      _ = n := Nat.div_mul_cancel hbn⟩

@[simp] theorem localBlockIndex_div (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val / b = i.val / b := by
  change (i.val / b * b + k.val) / b = i.val / b
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt k.isLt, Nat.zero_add]

@[simp] theorem localBlockIndex_mod (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val % b = k.val := by
  simp [localBlockIndex, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

/-- Matrix multiplication within a full physical block is a sum over its local
coordinates. -/
theorem mul_apply_localBlockIndex (hb : 0 < b) (hbn : b ∣ n)
    (hA : BlockDiagonal b A) (i j : Fin n) :
    (A * B) i j = ∑ k : Fin b,
      A i (localBlockIndex hb hbn i k) * B (localBlockIndex hb hbn i k) j := by
  classical
  rw [Matrix.mul_apply]
  let s : Finset (Fin n) := Finset.univ.filter (fun k => k.val / b = i.val / b)
  have hrestrict : (∑ k : Fin n, A i k * B k j) = ∑ k ∈ s, A i k * B k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    have hk' : i.val / b ≠ k.val / b := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
        eq_comm] using hk
    rw [hA i k hk', zero_mul]
  rw [hrestrict]
  apply Finset.sum_bij (fun k _ => (⟨k.val % b, Nat.mod_lt _ hb⟩ : Fin b))
  · intro k hk
    exact Finset.mem_univ _
  · intro k hk l hl he
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have hl' : l.val / b = i.val / b := (Finset.mem_filter.mp hl).2
    have he' : k.val % b = l.val % b := congrArg Fin.val he
    apply Fin.ext
    have hkd := Nat.mod_add_div k.val b
    have hld := Nat.mod_add_div l.val b
    rw [hk', he'] at hkd
    rw [hl'] at hld
    omega
  · intro k _
    refine ⟨localBlockIndex hb hbn i k, ?_, ?_⟩
    · simp [s]
    · exact Fin.ext (localBlockIndex_mod hb hbn i k)
  · intro k hk
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have he : localBlockIndex hb hbn i ⟨k.val % b, Nat.mod_lt _ hb⟩ = k := by
      apply Fin.ext
      simp only [localBlockIndex, ← hk']
      exact Nat.div_add_mod' _ _
    rw [he]

namespace TiedEntries

theorem mul (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (_hBs : BlockDiagonal b B)
    (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A * B) := by
  intro i j i' j' hij hij' hτ hi hj
  rw [mul_apply_localBlockIndex hb hbn hAs, mul_apply_localBlockIndex hb hbn hAs]
  apply Finset.sum_congr rfl
  intro k _
  have hleft : A i (localBlockIndex hb hbn i k) =
      A i' (localBlockIndex hb hbn i' k) := by
    apply hA
    · simp
    · simp
    · exact hτ
    · exact hi
    · simp
  have hright : B (localBlockIndex hb hbn i k) j =
      B (localBlockIndex hb hbn i' k) j' := by
    apply hB
    · simpa using hij
    · simpa using hij'
    · simpa using hτ
    · simp
    · exact hj
  rw [hleft, hright]

theorem pow (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (hA : TiedEntries b τ A) (k : ℕ) :
    TiedEntries b τ (A ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using TiedEntries.one b τ
  | succ k ih =>
    simpa only [pow_succ] using
      TiedEntries.mul hb hbn (supported_pow hAs k) hAs ih hA

theorem sum {α : Type*} (s : Finset α) (F : α → Mat n)
    (hF : ∀ a ∈ s, TiedEntries b τ (F a)) : TiedEntries b τ (∑ a ∈ s, F a) := by
  classical
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  exact hF a ha i j i' j' h h' hτ hi hj

end TiedEntries

theorem isClosed_tiedEntries (b : ℕ) (τ : ℕ → ℕ) :
    IsClosed {A : Mat n | TiedEntries b τ A} := by
  simp only [TiedEntries, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun i' => isClosed_iInter fun j' =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_eq (by fun_prop) (by fun_prop)

/-- Actual tied entries pass from finite powers to their convergent exponential
series, because the equalities of entries form a closed subspace. -/
theorem matrixExp_tied (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (hA : TiedEntries b τ A) :
    TiedEntries b τ (matrixExp A) := by
  let F : Finset ℕ → Mat n := fun s => ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k
  have hlim : Tendsto F atTop (𝓝 (matrixExp A)) := matrixExp_hasSum A
  apply (isClosed_tiedEntries b τ).mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro s
  exact TiedEntries.sum s _ (fun k _ => (TiedEntries.pow hb hbn hAs hA k).smul _)

theorem expLine_tied (hb : 0 < b) (hbn : b ∣ n)
    (hCs : BlockDiagonal b C) (hC : TiedEntries b τ C) (t : ℝ) :
    TiedEntries b τ (expLine C t) :=
  matrixExp_tied hb hbn (Supported.smul t hCs) (hC.smul t)

/-- Supported tied matrices form a concrete real submodule. -/
def sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | BlockDiagonal b A ∧ TiedEntries b τ A}
  zero_mem' := ⟨Supported.zero, TiedEntries.zero b τ⟩
  add_mem' := fun hA hB => ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  smul_mem' := fun a _ hA => ⟨Supported.smul a hA.1, hA.2.smul a⟩

theorem isClosed_sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) :
    IsClosed (sharedMatrixSpace (n := n) b τ : Set (Mat n)) :=
  (isClosed_supported n _).inter (isClosed_tiedEntries b τ)

theorem one_mem_sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) :
    (1 : Mat n) ∈ sharedMatrixSpace b τ :=
  ⟨Supported.one, TiedEntries.one b τ⟩

theorem mul_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hB : B ∈ sharedMatrixSpace b τ) :
    A * B ∈ sharedMatrixSpace b τ :=
  ⟨hA.1.mul hB.1, TiedEntries.mul hb hbn hA.1 hB.1 hA.2 hB.2⟩

theorem transpose_mem_sharedMatrixSpace (hA : A ∈ sharedMatrixSpace b τ) :
    Aᵀ ∈ sharedMatrixSpace b τ :=
  ⟨hA.1.transpose, hA.2.transpose⟩

theorem expLine_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hC : C ∈ sharedMatrixSpace b τ) (t : ℝ) :
    expLine C t ∈ sharedMatrixSpace b τ :=
  ⟨expLine_supported hC.1 t, expLine_tied hb hbn hC.1 hC.2 t⟩

end GS.GlobalGeometry
