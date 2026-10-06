module

public import GS.Extensions.FiniteTopology
public import GS.Extensions.ProjectionSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual compactness of orthogonal block factors and their matrix images

Compactness/closedness is not confused with smoothness.
The theorems apply to m=2 and m=3; m=3 can still be singular.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem orthogonal_entry_abs_le_one {A : Mat n} (hA : Orthogonal A) (i j : Fin n) :
    |A i j| ≤ 1 := by
  have hg := congrFun (congrFun hA.1 j) j
  have he : (∑ k : Fin n, A k j * A k j)=1 := by
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hg
  have hs : A i j * A i j ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A k j)) (Finset.mem_univ i)
  by_contra hn
  have hp : 0 < (|A i j|-1)*(|A i j|+1) := by
    apply mul_pos
    · linarith [lt_of_not_ge hn]
    · positivity
  nlinarith [sq_abs (A i j)]

 def blockOrthogonalSet (block : Fin n → ℕ) : Set (Mat n) :=
  {A | Supported block A ∧ Orthogonal A}

 theorem isCompact_blockOrthogonalSet (block : Fin n → ℕ) :
    IsCompact (blockOrthogonalSet block) := by
  letI : PartialOrder (Mat n) := inferInstanceAs (PartialOrder (Fin n → Fin n → ℝ))
  letI : CompactIccSpace (Mat n) :=
    inferInstanceAs (CompactIccSpace (Fin n → Fin n → ℝ))
  have hc : IsClosed (blockOrthogonalSet block) :=
    (isClosed_supported n block).inter (isClosed_orthogonal n)
  have hs : blockOrthogonalSet block ⊆
      Set.Icc (fun _ _ => (-1:ℝ)) (fun _ _ => (1:ℝ)) := by
    intro A hA
    refine ⟨?_,?_⟩ <;> intro i j
    · exact (abs_le.mp (orthogonal_entry_abs_le_one hA.2 i j)).1
    · exact (abs_le.mp (orthogonal_entry_abs_le_one hA.2 i j)).2
  exact isCompact_Icc.of_isClosed_subset hc hs

 theorem isCompact_A2Orth (b₁ b₂ : ℕ) (P : Mat n) :
    IsCompact {A : Mat n | InA2Orth b₁ b₂ P A} := by
  let S₁ := blockOrthogonalSet (fun i : Fin n => i.val/b₁)
  let S₂ := blockOrthogonalSet (fun i : Fin n => i.val/b₂)
  have hc : IsCompact (S₂ ×ˢ S₁) :=
    (isCompact_blockOrthogonalSet _).prod (isCompact_blockOrthogonalSet _)
  have he : (fun x : Mat n × Mat n => product2 x.1 P x.2) '' (S₂ ×ˢ S₁) =
      {A : Mat n | InA2Orth b₁ b₂ P A} := by
    ext A
    constructor
    · rintro ⟨⟨B₂,B₁⟩,⟨h₂,h₁⟩,he⟩
      exact ⟨B₁,B₂,h₁.1,h₂.1,h₁.2,h₂.2,he.symm⟩
    · rintro ⟨B₁,B₂,hb₁,hb₂,ho₁,ho₂,he⟩
      exact ⟨(B₂,B₁),⟨⟨hb₂,ho₂⟩,⟨hb₁,ho₁⟩⟩,he.symm⟩
  rw [← he]
  exact hc.image (product2_smooth P).continuous

 theorem isClosed_A2Orth (b₁ b₂ : ℕ) (P : Mat n) :
    IsClosed {A : Mat n | InA2Orth b₁ b₂ P A} :=
  (isCompact_A2Orth b₁ b₂ P).isClosed

 theorem isCompact_A3Orth (b₁ b₂ b₃ : ℕ) (P₁ P₂ : Mat n) :
    IsCompact {A : Mat n | InA3Orth b₁ b₂ b₃ P₁ P₂ A} := by
  let S₁ := blockOrthogonalSet (fun i : Fin n => i.val/b₁)
  let S₂ := blockOrthogonalSet (fun i : Fin n => i.val/b₂)
  let S₃ := blockOrthogonalSet (fun i : Fin n => i.val/b₃)
  have hc : IsCompact (S₃ ×ˢ (S₂ ×ˢ S₁)) :=
    (isCompact_blockOrthogonalSet _).prod
      ((isCompact_blockOrthogonalSet _).prod (isCompact_blockOrthogonalSet _))
  have he : (fun x : Mat n × Mat n × Mat n => product3 x.1 P₂ x.2.1 P₁ x.2.2) ''
      (S₃ ×ˢ (S₂ ×ˢ S₁)) = {A : Mat n | InA3Orth b₁ b₂ b₃ P₁ P₂ A} := by
    ext A
    constructor
    · rintro ⟨⟨B₃,B₂,B₁⟩,⟨h₃,h₂,h₁⟩,he⟩
      exact ⟨B₁,B₂,B₃,h₁.1,h₂.1,h₃.1,h₁.2,h₂.2,h₃.2,he.symm⟩
    · rintro ⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,ho₁,ho₂,ho₃,he⟩
      exact ⟨(B₃,B₂,B₁),⟨⟨hb₃,ho₃⟩,⟨hb₂,ho₂⟩,⟨hb₁,ho₁⟩⟩,he.symm⟩
  rw [← he]
  exact hc.image (product3_smooth P₂ P₁).continuous

 theorem isClosed_A3Orth (b₁ b₂ b₃ : ℕ) (P₁ P₂ : Mat n) :
    IsClosed {A : Mat n | InA3Orth b₁ b₂ b₃ P₁ P₂ A} :=
  (isCompact_A3Orth b₁ b₂ b₃ P₁ P₂).isClosed

end GS.Extensions
