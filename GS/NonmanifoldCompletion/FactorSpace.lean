module

public import GS.NonmanifoldCompletion.BlockExtraction
public import GS.Extensions.OrbitCompact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A compact parameter space whose image is exactly the original localFamily

This uses all orthogonal block factors, not a selected normal-form branch.
The equivalence with the scalar-shuffle definition is proved by extraction.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

/-- The order is (left outer blocks, first middle block, second middle block,
right outer blocks). It matches the finite compact product used below. -/
abbrev SmallBlockParameters (q : ℕ) :=
  (Fin q → Mat 2) × Mat q × Mat q × (Fin q → Mat 2)

def smallFactorSet (q : ℕ) : Set (SmallBlockParameters q) :=
  {p | (∀ i, Orthogonal (p.1 i)) ∧ Orthogonal p.2.1 ∧ Orthogonal p.2.2.1 ∧
    (∀ j, Orthogonal (p.2.2.2 j))}

def smallFactorMap {q : ℕ} (p : SmallBlockParameters q) : Mat (q*2) :=
  flattenBlocks (blockMatrix p.1 * centralPair p.2.1 p.2.2.1 * blockMatrix p.2.2.2)

theorem smallFactorMap_block {q : ℕ} (p : SmallBlockParameters q)
    (i j : Fin q) (a b : Fin 2) :
    smallFactorMap p (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      (p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j) a b := by
  rw [smallFactorMap,flattenBlocks_apply,small_block_sandwich]

theorem continuous_smallFactorMap (q : ℕ) : Continuous (@smallFactorMap q) := by
  have he : (@smallFactorMap q) = fun p i j =>
      let x : Fin q × Fin 2 := finProdFinEquiv.symm i
      let y : Fin q × Fin 2 := finProdFinEquiv.symm j
      (p.1 x.1 * diagTwo (p.2.1 x.1 y.1) (p.2.2.1 x.1 y.1) * p.2.2.2 y.1) x.2 y.2 := by
    funext p i j
    exact small_block_sandwich _ _ _ _ _ _ _ _
  rw [he]
  have hdiag (i j : Fin q) : Continuous (fun p : SmallBlockParameters q =>
      diagTwo (p.2.1 i j) (p.2.2.1 i j)) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    fin_cases a <;> fin_cases b <;> simp [diagTwo] <;> fun_prop
  fun_prop

theorem isClosed_smallFactorSet (q : ℕ) : IsClosed (smallFactorSet q) := by
  have hU : IsClosed {p : SmallBlockParameters q | ∀ i, Orthogonal (p.1 i)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => (isClosed_orthogonal 2).preimage (by fun_prop))
  have hA : IsClosed {p : SmallBlockParameters q | Orthogonal p.2.1} :=
    (isClosed_orthogonal q).preimage (by fun_prop)
  have hB : IsClosed {p : SmallBlockParameters q | Orthogonal p.2.2.1} :=
    (isClosed_orthogonal q).preimage (by fun_prop)
  have hV : IsClosed {p : SmallBlockParameters q | ∀ j, Orthogonal (p.2.2.2 j)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j => (isClosed_orthogonal 2).preimage (by fun_prop))
  exact hU.inter (hA.inter (hB.inter hV))

theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) := by
  letI : PartialOrder (Mat q) := inferInstanceAs (PartialOrder (Fin q → Fin q → ℝ))
  letI : CompactIccSpace (Mat q) := inferInstanceAs (CompactIccSpace (Fin q → Fin q → ℝ))
  letI : PartialOrder (Mat 2) := inferInstanceAs (PartialOrder (Fin 2 → Fin 2 → ℝ))
  letI : CompactIccSpace (Mat 2) := inferInstanceAs (CompactIccSpace (Fin 2 → Fin 2 → ℝ))
  let lo : SmallBlockParameters q :=
    (fun _ _ _ => -1,fun _ _ => -1,fun _ _ => -1,fun _ _ _ => -1)
  let hi : SmallBlockParameters q :=
    (fun _ _ _ => 1,fun _ _ => 1,fun _ _ => 1,fun _ _ _ => 1)
  have hsub : smallFactorSet q ⊆ Set.Icc lo hi := by
    rintro ⟨U,A,B,V⟩ ⟨hU,hA,hB,hV⟩
    have hu := fun i a b => abs_le.mp (orthogonal_entry_abs_le_one (hU i) a b)
    have ha := fun i j => abs_le.mp (orthogonal_entry_abs_le_one hA i j)
    have hb := fun i j => abs_le.mp (orthogonal_entry_abs_le_one hB i j)
    have hv := fun j a b => abs_le.mp (orthogonal_entry_abs_le_one (hV j) a b)
    exact ⟨⟨fun i a b => (hu i a b).1,fun i j => (ha i j).1,
        fun i j => (hb i j).1,fun j a b => (hv j a b).1⟩,
      ⟨fun i a b => (hu i a b).2,fun i j => (ha i j).2,
        fun i j => (hb i j).2,fun j a b => (hv j a b).2⟩⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_smallFactorSet q) hsub

/-- Crucially, this is the FULL GS image, not the small originalF image. -/
theorem image_smallFactorMap (q : ℕ) :
    (@smallFactorMap q) '' smallFactorSet q = localFamily q := by
  ext M
  constructor
  · rintro ⟨⟨U,A,B,V⟩,⟨hU,hA,hB,hV⟩,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB
  · intro hM
    obtain ⟨U,V,A,B,hU,hV,hA,hB,he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
    exact ⟨(U,A,B,V),⟨hU,hA,hB,hV⟩,he.symm⟩

/-- Extracting the actual scalar block equations at the marked image point. -/
theorem smallFactorMap_eq_base_blocks {q : ℕ} (Q₀ : Mat q)
    (p : SmallBlockParameters q) (he : smallFactorMap p=basePoint Q₀) (i j : Fin q) :
    p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j = Q₀ i j • (1 : Mat 2) := by
  ext a b
  have hh := congrFun (congrFun he (finProdFinEquiv (i,a))) (finProdFinEquiv (j,b))
  rw [smallFactorMap_block] at hh
  have hi : finProdFinEquiv.symm (finProdFinEquiv (i,a)) = (i,a) :=
    Equiv.symm_apply_apply _ _
  have hj : finProdFinEquiv.symm (finProdFinEquiv (j,b)) = (j,b) :=
    Equiv.symm_apply_apply _ _
  dsimp only [basePoint] at hh
  rw [hi,hj] at hh
  exact hh

end GS.NonmanifoldCompletion
