module

public import GS.NonmanifoldCompletion.BlockRealization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Recovering the small blocks from the original scalar GS factors

This is the reverse direction of BlockRealization. The q-by-q grid formula
is proved equivalent to the original family, not adopted as a replacement
for that family. All statements include singular/zero matrix entries.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.NonmanifoldCompletion

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem pullMatrix_symm (e : β ≃ α) (A : Matrix α α ℝ) :
    pullMatrix e.symm (pullMatrix e A) = A := by
  ext i j
  simp [pullMatrix]

end Relabel

def unflattenBlocks {k b : ℕ} (A : Mat (k*b)) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ := pullMatrix finProdFinEquiv A

@[simp] theorem flatten_unflatten {k b : ℕ} (A : Mat (k*b)) :
    flattenBlocks (unflattenBlocks A) = A := by
  exact pullMatrix_symm finProdFinEquiv A

@[simp] theorem unflatten_flatten {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ) :
    unflattenBlocks (flattenBlocks A) = A := by
  exact pullMatrix_symm finProdFinEquiv.symm A

/-- Extract the consecutive diagonal blocks without any choice. -/
def flatBlocks {k b : ℕ} (A : Mat (k*b)) (i : Fin k) : Mat b :=
  fun a c => A (finProdFinEquiv (i,a)) (finProdFinEquiv (i,c))

theorem unflatten_supported {k b : ℕ} (A : Mat (k*b)) (hA : BlockDiagonal b A) :
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

theorem flatten_extracted_blocks {k b : ℕ} (A : Mat (k*b))
    (hA : BlockDiagonal b A) : flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_supported A hA,flatten_unflatten]

theorem blockMatrix_orthogonal_component {k b : ℕ} (B : Fin k → Mat b)
    (hB : Orthogonal (blockMatrix B)) (i : Fin k) : Orthogonal (B i) := by
  constructor
  · have he := hB.1
    rw [blockMatrix_transpose,blockMatrix_mul] at he
    ext a c
    have hh := congrFun (congrFun he (i,a)) (i,c)
    simpa [blockMatrix,Matrix.one_apply] using hh
  · have he := hB.2
    rw [blockMatrix_transpose,blockMatrix_mul] at he
    ext a c
    have hh := congrFun (congrFun he (i,a)) (i,c)
    simpa [blockMatrix,Matrix.one_apply] using hh

theorem flatBlocks_orthogonal {k b : ℕ} (A : Mat (k*b))
    (hs : BlockDiagonal b A) (hA : Orthogonal A) (i : Fin k) :
    Orthogonal (flatBlocks A i) := by
  have h := pullMatrix_orthogonal finProdFinEquiv hA
  change Orthogonal (unflattenBlocks A) at h
  rw [unflatten_supported A hs] at h
  exact blockMatrix_orthogonal_component _ h i

theorem centralPair_orthogonal_components {q : ℕ} (A B : Mat q)
    (h : Orthogonal (centralPair A B)) : Orthogonal A ∧ Orthogonal B := by
  have hh := pullMatrix_orthogonal (Equiv.prodComm (Fin 2) (Fin q)) h
  have he : pullMatrix (Equiv.prodComm (Fin 2) (Fin q)) (centralPair A B) =
      blockMatrix ![A,B] := by
    ext ⟨a,i⟩ ⟨b,j⟩
    fin_cases a <;> fin_cases b <;>
      simp [pullMatrix,centralPair,blockMatrix,diagTwo]
  rw [he] at hh
  exact ⟨blockMatrix_orthogonal_component _ hh 0,
    blockMatrix_orthogonal_component _ hh 1⟩

theorem inverse_conjugate_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (D : Mat n) (i j : Fin n) :
    ((permMatrix σ)ᵀ * D * permMatrix σ) i j = D (σ i) (σ j) := by
  simp only [mul_perm_apply,perm_transpose,perm_mul_apply,Equiv.symm_symm]

/-- Recover the two q-by-q middle blocks from the scalar supported factor. -/
theorem extract_middle_pair {q : ℕ} (D : Mat (q*2))
    (hs : BlockDiagonal q D) (hD : Orthogonal D) :
    ∃ A B : Mat q, Orthogonal A ∧ Orthogonal B ∧
      flattenBlocks (centralPair A B) =
        (permMatrix (scalarShuffle q 2))ᵀ * D * permMatrix (scalarShuffle q 2) := by
  let σ := scalarShuffle q 2
  let P := permMatrix σ
  let C := unflattenBlocks (Pᵀ * D * P)
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
  let A : Mat q := fun i j => C (i,0) (j,0)
  let B : Mat q := fun i j => C (i,1) (j,1)
  have he : C = centralPair A B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [centralPair,diagTwo,A,B,hcross]
  have hP : Orthogonal P := perm_orthogonal _
  have hC : Orthogonal C := pullMatrix_orthogonal _ ((hP.transpose.mul hD).mul hP)
  rw [he] at hC
  obtain ⟨hA,hB⟩ := centralPair_orthogonal_components A B hC
  refine ⟨A,B,hA,hB,?_⟩
  rw [← he]
  exact flatten_unflatten _

/-- Exact block description of the original scalar-shuffle family. -/
theorem mem_localFamily_iff_block_sandwich {q : ℕ} (M : Mat (q*2)) :
    M ∈ localFamily q ↔
      ∃ (U V : Fin q → Mat 2) (A B : Mat q),
        (∀ i, Orthogonal (U i)) ∧ (∀ j, Orthogonal (V j)) ∧
        Orthogonal A ∧ Orthogonal B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  constructor
  · rintro ⟨B₁,B₂,B₃,hs₁,hs₂,hs₃,ho₁,ho₂,ho₃,hM⟩
    obtain ⟨A,B,hA,hB,hAB⟩ := extract_middle_pair B₂ hs₂ ho₂
    refine ⟨flatBlocks B₃,flatBlocks B₁,A,B,flatBlocks_orthogonal B₃ hs₃ ho₃,
      flatBlocks_orthogonal B₁ hs₁ ho₁,hA,hB,?_⟩
    rw [flattenBlocks_mul,flattenBlocks_mul,flatten_extracted_blocks B₃ hs₃,
      flatten_extracted_blocks B₁ hs₁,hAB,hM]
    simp only [product3,Matrix.mul_assoc]
  · rintro ⟨U,V,A,B,hU,hV,hA,hB,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB

end GS.NonmanifoldCompletion
