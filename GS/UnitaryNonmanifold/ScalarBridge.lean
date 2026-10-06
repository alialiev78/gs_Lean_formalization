module

public import GS.UnitaryNonmanifold.BlockInvariant

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact scalar perfect-shuffle description of the unitary block family

This file identifies the block description with the original three-factor
family using its prescribed scalar shuffle, including degenerate entries.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryNonmanifold
open GS.UnitaryGeometry

/-- Unitarity with arbitrary finite row and column index types. -/
abbrev MatrixUnitary {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℂ) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace MatrixUnitary
variable {α : Type*} [Fintype α] [DecidableEq α] {A B : Matrix α α ℂ}
theorem conjTranspose (h : MatrixUnitary A) : MatrixUnitary Aᴴ := by
  constructor
  · simpa using h.2
  · simpa using h.1

theorem mul (hA : MatrixUnitary A) (hB : MatrixUnitary B) : MatrixUnitary (A*B) := by
  constructor
  · calc
      (A*B)ᴴ*(A*B) = Bᴴ*(Aᴴ*A)*B := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hA.1]; simpa using hB.1
  · calc
      (A*B)*(A*B)ᴴ = A*(B*Bᴴ)*Aᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hB.2]; simpa using hA.2
end MatrixUnitary

def blockMatrix {k b : ℕ} (B : Fin k → CMat b) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

def localFamily (q : ℕ) : Set (CMat (q*2)) :=
  let P := cPermMatrix (scalarShuffle q 2)
  {M | CInA3Unitary 2 q 2 P Pᴴ M}

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Pull back both matrix indices along an equivalence. -/
def pullMatrix (e : β ≃ α) (A : Matrix α α ℂ) : Matrix β β ℂ :=
  fun i j => A (e i) (e j)

@[simp] theorem pullMatrix_conjTranspose (e : β ≃ α) (A : Matrix α α ℂ) :
    pullMatrix e Aᴴ = (pullMatrix e A)ᴴ := rfl

@[simp] theorem pullMatrix_one (e : β ≃ α) :
    pullMatrix e (1 : Matrix α α ℂ) = 1 := by
  ext i j
  simp [pullMatrix, Matrix.one_apply, e.injective.eq_iff]

theorem pullMatrix_mul (e : β ≃ α) (A B : Matrix α α ℂ) :
    pullMatrix e (A*B) = pullMatrix e A * pullMatrix e B := by
  classical
  ext i j
  change (∑ k : α, A (e i) k * B k (e j)) =
    ∑ k : β, A (e i) (e k) * B (e k) (e j)
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

theorem pullMatrix_unitary (e : β ≃ α) {A : Matrix α α ℂ}
    (hA : MatrixUnitary A) : MatrixUnitary (pullMatrix e A) := by
  constructor
  · rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.1, pullMatrix_one]
  · rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.2, pullMatrix_one]

end Relabel

/-- Flatten the pair-indexed matrix using the SAME equivalence as originalF. -/
def flattenBlocks {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ) : CMat (k*b) :=
  pullMatrix finProdFinEquiv.symm A

@[simp] theorem flattenBlocks_apply {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ)
    (i j : Fin k × Fin b) :
    flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks,pullMatrix]

theorem flattenBlocks_mul {k b : ℕ}
    (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ) :
    flattenBlocks (A*B) = flattenBlocks A * flattenBlocks B :=
  pullMatrix_mul _ A B

/-- Blocks are indexed by the quotient in the original CBlockDiagonal predicate. -/
theorem flat_block_label {k b : ℕ} (p : Fin k × Fin b) :
    (finProdFinEquiv p).val / b = p.1.val := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  change (p.2.val + b * p.1.val) / b = p.1.val
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]

theorem flatten_blockDiagonal {k b : ℕ} (B : Fin k → CMat b) :
    CBlockDiagonal b (flattenBlocks (blockMatrix B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  have hxy : x.1 ≠ y.1 := by
    intro h
    have hi := flat_block_label x
    have hj := flat_block_label y
    simp only [x,y,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  exact if_neg hxy

@[simp] theorem blockMatrix_conjTranspose {k b : ℕ} (B : Fin k → CMat b) :
    (blockMatrix B)ᴴ = blockMatrix (fun i => (B i)ᴴ) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j
  · subst j; simp [blockMatrix]
  · simp [blockMatrix, h, Ne.symm h]

@[simp] theorem blockMatrix_mul {k b : ℕ} (B C : Fin k → CMat b) :
    blockMatrix B * blockMatrix C = blockMatrix (fun i => B i * C i) := by
  classical
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j
  · subst j
    simp [Matrix.mul_apply,blockMatrix,Fintype.sum_prod_type]
  · simp [Matrix.mul_apply,blockMatrix,Fintype.sum_prod_type,h]

@[simp] theorem blockMatrix_one (k b : ℕ) :
    blockMatrix (fun _ : Fin k => (1 : CMat b)) = 1 := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hi : i=j <;> by_cases ha : a=c <;>
    simp [blockMatrix, Matrix.one_apply, hi, ha]

theorem blockMatrix_unitary {k b : ℕ} (B : Fin k → CMat b)
    (hB : ∀ i, MatrixUnitary (B i)) : MatrixUnitary (blockMatrix B) := by
  constructor
  · rw [blockMatrix_conjTranspose,blockMatrix_mul]
    have he : (fun i => (B i)ᴴ * B i) = (fun _ => (1 : CMat b)) :=
      funext (fun i => (hB i).1)
    rw [he,blockMatrix_one]
  · rw [blockMatrix_conjTranspose,blockMatrix_mul]
    have he : (fun i => B i * (B i)ᴴ) = (fun _ => (1 : CMat b)) :=
      funext (fun i => (hB i).2)
    rw [he,blockMatrix_one]

/-- The central conjugate, displayed in q-by-q blocks of size two. -/
def centralPair {q : ℕ} (A B : CMat q) :
    Matrix (Fin q × Fin 2) (Fin q × Fin 2) ℂ :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks {q : ℕ} (A B : CMat q) :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A,B]) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [centralPair,pullMatrix,blockMatrix,diagTwo]

theorem centralPair_unitary {q : ℕ} (A B : CMat q)
    (hA : MatrixUnitary A) (hB : MatrixUnitary B) : MatrixUnitary (centralPair A B) := by
  rw [centralPair_as_blocks]
  apply pullMatrix_unitary
  apply blockMatrix_unitary
  intro i
  fin_cases i
  · exact hA
  · exact hB

/-- Scalar middle factor, constructed by conjugation with the specified shuffle. -/
def shuffledMiddle {q : ℕ} (A B : CMat q) : CMat (q*2) :=
  let P := cPermMatrix (scalarShuffle q 2)
  P * flattenBlocks (centralPair A B) * Pᴴ

/-- The shuffle makes the inner pair coordinate the consecutive block label. -/
theorem shuffle_block_label {q : ℕ} (i : Fin (q*2)) :
    (scalarShuffle q 2 i).val / q = (finProdFinEquiv.symm i).2.val := by
  let p := finProdFinEquiv.symm i
  have hh := flat_block_label (p.2,p.1)
  have hcast {m n : ℕ} (h : m = n) (a : Fin m) :
      (cast (congrArg Fin h) a).val = a.val := by
    cases h
    rfl
  change (cast (congrArg Fin (Nat.mul_comm 2 q))
    (finProdFinEquiv (p.2,p.1))).val / q = p.2.val
  rw [hcast (Nat.mul_comm 2 q)]
  exact hh

theorem shuffledMiddle_blockDiagonal {q : ℕ} (A B : CMat q) :
    CBlockDiagonal q (shuffledMiddle A B) := by
  intro i j hij
  let σ := scalarShuffle q 2
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := shuffle_block_label (σ.symm i)
    have hj := shuffle_block_label (σ.symm j)
    simp only [σ,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  change (cPermMatrix σ * flattenBlocks (centralPair A B) * (cPermMatrix σ)ᴴ) i j = 0
  rw [cPerm_conjugate_apply]
  change diagTwo (A x.1 y.1) (B x.1 y.1) x.2 y.2 = 0
  have hdiag (a b : Fin 2) (hab : a ≠ b) (s t : ℂ) : diagTwo s t a b = 0 := by
    fin_cases a <;> fin_cases b <;> simp_all [diagTwo]
  exact hdiag x.2 y.2 hxy _ _

theorem small_block_sandwich {q : ℕ} (U V : Fin q → CMat 2) (A B : CMat q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i,a) (j,b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by
  classical
  simp [Matrix.mul_apply, blockMatrix, centralPair, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]

/-- Every unitary small-block sandwich belongs to the original scalar family. -/
theorem block_sandwich_mem_localFamily {q : ℕ} (U V : Fin q → CMat 2)
    (A B : CMat q) (hU : ∀ i, MatrixUnitary (U i)) (hV : ∀ j, MatrixUnitary (V j))
    (hA : MatrixUnitary A) (hB : MatrixUnitary B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ localFamily q := by
  let P := cPermMatrix (scalarShuffle q 2)
  let C := flattenBlocks (centralPair A B)
  have hP : MatrixUnitary P := cPerm_unitary _
  have hC : MatrixUnitary C := pullMatrix_unitary _ (centralPair_unitary A B hA hB)
  refine ⟨flattenBlocks (blockMatrix V), shuffledMiddle A B,
    flattenBlocks (blockMatrix U), flatten_blockDiagonal V,
    shuffledMiddle_blockDiagonal A B, flatten_blockDiagonal U,
    pullMatrix_unitary _ (blockMatrix_unitary V hV),
    (hP.mul hC).mul hP.conjTranspose,
    pullMatrix_unitary _ (blockMatrix_unitary U hU), ?_⟩
  change flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) =
    flattenBlocks (blockMatrix U) * Pᴴ * (P*C*Pᴴ) * P * flattenBlocks (blockMatrix V)
  rw [flattenBlocks_mul,flattenBlocks_mul]
  change flattenBlocks (blockMatrix U) * C * flattenBlocks (blockMatrix V) = _
  symm
  calc
    flattenBlocks (blockMatrix U) * Pᴴ * (P*C*Pᴴ) * P *
        flattenBlocks (blockMatrix V) =
        flattenBlocks (blockMatrix U) * (Pᴴ*P) * C * (Pᴴ*P) *
          flattenBlocks (blockMatrix V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP.1,Matrix.mul_one,Matrix.mul_one]


section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem pullMatrix_symm (e : β ≃ α) (A : Matrix α α ℂ) :
    pullMatrix e.symm (pullMatrix e A) = A := by
  ext i j
  simp [pullMatrix]

end Relabel

def unflattenBlocks {k b : ℕ} (A : CMat (k*b)) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ := pullMatrix finProdFinEquiv A

@[simp] theorem flatten_unflatten {k b : ℕ} (A : CMat (k*b)) :
    flattenBlocks (unflattenBlocks A) = A := by
  exact pullMatrix_symm finProdFinEquiv A

@[simp] theorem unflatten_flatten {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ) :
    unflattenBlocks (flattenBlocks A) = A := by
  exact pullMatrix_symm finProdFinEquiv.symm A

/-- Extract the consecutive diagonal blocks without any choice. -/
def flatBlocks {k b : ℕ} (A : CMat (k*b)) (i : Fin k) : CMat b :=
  fun a c => A (finProdFinEquiv (i,a)) (finProdFinEquiv (i,c))

theorem unflatten_supported {k b : ℕ} (A : CMat (k*b)) (hA : CBlockDiagonal b A) :
    unflattenBlocks A = blockMatrix (flatBlocks A) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hij : i=j
  · subst j
    simp [unflattenBlocks,pullMatrix,blockMatrix,flatBlocks]
  · change A (finProdFinEquiv (i,a)) (finProdFinEquiv (j,c)) =
      (if i=j then _ else 0)
    rw [if_neg hij]
    apply hA
    change (finProdFinEquiv (i,a)).val / b ≠ (finProdFinEquiv (j,c)).val / b
    rw [flat_block_label,flat_block_label]
    exact fun h => hij (Fin.ext h)

theorem flatten_extracted_blocks {k b : ℕ} (A : CMat (k*b))
    (hA : CBlockDiagonal b A) : flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_supported A hA,flatten_unflatten]

theorem blockMatrix_unitary_component {k b : ℕ} (B : Fin k → CMat b)
    (hB : MatrixUnitary (blockMatrix B)) (i : Fin k) : MatrixUnitary (B i) := by
  constructor
  · have he := hB.1
    rw [blockMatrix_conjTranspose,blockMatrix_mul] at he
    ext a c
    have hh := congrFun (congrFun he (i,a)) (i,c)
    simpa [blockMatrix,Matrix.one_apply] using hh
  · have he := hB.2
    rw [blockMatrix_conjTranspose,blockMatrix_mul] at he
    ext a c
    have hh := congrFun (congrFun he (i,a)) (i,c)
    simpa [blockMatrix,Matrix.one_apply] using hh

theorem flatBlocks_unitary {k b : ℕ} (A : CMat (k*b))
    (hs : CBlockDiagonal b A) (hA : MatrixUnitary A) (i : Fin k) :
    MatrixUnitary (flatBlocks A i) := by
  have h := pullMatrix_unitary finProdFinEquiv hA
  change MatrixUnitary (unflattenBlocks A) at h
  rw [unflatten_supported A hs] at h
  exact blockMatrix_unitary_component _ h i

theorem centralPair_unitary_components {q : ℕ} (A B : CMat q)
    (h : MatrixUnitary (centralPair A B)) : MatrixUnitary A ∧ MatrixUnitary B := by
  have hh := pullMatrix_unitary (Equiv.prodComm (Fin 2) (Fin q)) h
  have he : pullMatrix (Equiv.prodComm (Fin 2) (Fin q)) (centralPair A B) =
      blockMatrix ![A,B] := by
    ext ⟨a,i⟩ ⟨b,j⟩
    fin_cases a <;> fin_cases b <;>
      simp [pullMatrix,centralPair,blockMatrix,diagTwo]
  rw [he] at hh
  exact ⟨blockMatrix_unitary_component _ hh 0,
    blockMatrix_unitary_component _ hh 1⟩

theorem inverse_conjugate_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (D : CMat n) (i j : Fin n) :
    ((cPermMatrix σ)ᴴ * D * cPermMatrix σ) i j = D (σ i) (σ j) := by
  simp only [mul_cPerm_apply,cPerm_conjTranspose,cPerm_mul_apply,Equiv.symm_symm]

/-- Recover the two q-by-q middle blocks from the scalar supported factor. -/
theorem extract_middle_pair {q : ℕ} (D : CMat (q*2))
    (hs : CBlockDiagonal q D) (hD : MatrixUnitary D) :
    ∃ A B : CMat q, MatrixUnitary A ∧ MatrixUnitary B ∧
      flattenBlocks (centralPair A B) =
        (cPermMatrix (scalarShuffle q 2))ᴴ * D * cPermMatrix (scalarShuffle q 2) := by
  let σ := scalarShuffle q 2
  let P := cPermMatrix σ
  let C := unflattenBlocks (Pᴴ * D * P)
  have hentry (i j : Fin q) (a b : Fin 2) :
      C (i,a) (j,b) = D (σ (finProdFinEquiv (i,a))) (σ (finProdFinEquiv (j,b))) :=
    inverse_conjugate_apply σ D _ _
  have hcross (i j : Fin q) (a b : Fin 2) (hab : a≠b) : C (i,a) (j,b)=0 := by
    rw [hentry]
    apply hs
    have hi := shuffle_block_label (finProdFinEquiv (i,a))
    have hj := shuffle_block_label (finProdFinEquiv (j,b))
    simp only [Equiv.symm_apply_apply] at hi hj
    change (scalarShuffle q 2 (finProdFinEquiv (i,a))).val/q ≠
      (scalarShuffle q 2 (finProdFinEquiv (j,b))).val/q
    rw [hi,hj]
    exact fun h => hab (Fin.ext h)
  let A : CMat q := fun i j => C (i,0) (j,0)
  let B : CMat q := fun i j => C (i,1) (j,1)
  have he : C = centralPair A B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [centralPair,diagTwo,A,B,hcross]
  have hP : MatrixUnitary P := cPerm_unitary _
  have hC : MatrixUnitary C := pullMatrix_unitary _ ((hP.conjTranspose.mul hD).mul hP)
  rw [he] at hC
  obtain ⟨hA,hB⟩ := centralPair_unitary_components A B hC
  refine ⟨A,B,hA,hB,?_⟩
  rw [← he]
  exact flatten_unflatten _

/-- Exact block description of the original scalar-shuffle family. -/
theorem mem_localFamily_iff_block_sandwich {q : ℕ} (M : CMat (q*2)) :
    M ∈ localFamily q ↔
      ∃ (U V : Fin q → CMat 2) (A B : CMat q),
        (∀ i, MatrixUnitary (U i)) ∧ (∀ j, MatrixUnitary (V j)) ∧
        MatrixUnitary A ∧ MatrixUnitary B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  constructor
  · rintro ⟨B₁,B₂,B₃,hs₁,hs₂,hs₃,ho₁,ho₂,ho₃,hM⟩
    obtain ⟨A,B,hA,hB,hAB⟩ := extract_middle_pair B₂ hs₂ ho₂
    refine ⟨flatBlocks B₃,flatBlocks B₁,A,B,flatBlocks_unitary B₃ hs₃ ho₃,
      flatBlocks_unitary B₁ hs₁ ho₁,hA,hB,?_⟩
    rw [flattenBlocks_mul,flattenBlocks_mul,flatten_extracted_blocks B₃ hs₃,
      flatten_extracted_blocks B₁ hs₁,hAB,hM]
    simp only [GS.UnitaryGeometry.product3,Matrix.mul_assoc]
  · rintro ⟨U,V,A,B,hU,hV,hA,hB,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB


theorem mem_localFamily_iff_BlockSandwich {q : ℕ} (M : CMat (q*2)) :
    M ∈ localFamily q ↔ BlockSandwich M := by
  rw [mem_localFamily_iff_block_sandwich]
  constructor
  · rintro ⟨U,V,A,B,hU,hV,hA,hB,rfl⟩
    refine ⟨U,V,A,B,hU,hV,hA,hB,?_⟩
    intro i j
    ext a b
    change flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V)
      (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) = _
    rw [flattenBlocks_apply, small_block_sandwich]
  · rintro ⟨U,V,A,B,hU,hV,hA,hB,he⟩
    refine ⟨U,V,A,B,hU,hV,hA,hB,?_⟩
    ext a b
    obtain ⟨⟨i,c⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨j,d⟩,rfl⟩ := finProdFinEquiv.surjective b
    rw [flattenBlocks_apply,small_block_sandwich]
    exact congrFun (congrFun (he i j) c) d

theorem localFamily_row_gram_commute {q : ℕ} {M : CMat (q*2)}
    (hM : M ∈ localFamily q) (i j k : Fin q) :
    rowGram M i j * rowGram M i k = rowGram M i k * rowGram M i j :=
  blockSandwich_row_gram_commute ((mem_localFamily_iff_BlockSandwich M).mp hM) i j k

end GS.UnitaryNonmanifold
