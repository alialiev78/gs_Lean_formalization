module

public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryManifold.BlockGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact full factor space for the unitary three-factor family

The parameter space contains all unitary outer and middle blocks. Its image
is exactly the original scalar-shuffle family, including degenerate blocks.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold

namespace GS.UnitaryLocalModel

/-- Parameters are ordered as left blocks, two middle blocks, and right blocks. -/
abbrev SmallBlockParameters (q : ℕ) :=
  (Fin q → CMat 2) × CMat q × CMat q × (Fin q → CMat 2)

def smallFactorSet (q : ℕ) : Set (SmallBlockParameters q) :=
  {p | (∀ i, GS.Unitary (p.1 i)) ∧ GS.Unitary p.2.1 ∧ GS.Unitary p.2.2.1 ∧
    (∀ j, GS.Unitary (p.2.2.2 j))}

def smallFactorMap {q : ℕ} (p : SmallBlockParameters q) : CMat (q*2) :=
  flattenBlocks (GS.UnitaryNonmanifold.blockMatrix p.1 * centralPair p.2.1 p.2.2.1 *
    GS.UnitaryNonmanifold.blockMatrix p.2.2.2)

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
  have hU : IsClosed {p : SmallBlockParameters q | ∀ i, GS.Unitary (p.1 i)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => GS.UnitaryManifold.closed_unitary.preimage (by fun_prop))
  have hA : IsClosed {p : SmallBlockParameters q | GS.Unitary p.2.1} :=
    GS.UnitaryManifold.closed_unitary.preimage (by fun_prop)
  have hB : IsClosed {p : SmallBlockParameters q | GS.Unitary p.2.2.1} :=
    GS.UnitaryManifold.closed_unitary.preimage (by fun_prop)
  have hV : IsClosed {p : SmallBlockParameters q | ∀ j, GS.Unitary (p.2.2.2 j)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j => GS.UnitaryManifold.closed_unitary.preimage (by fun_prop))
  exact hU.inter (hA.inter (hB.inter hV))

theorem isCompact_unitary_set (n : ℕ) : IsCompact {A : CMat n | GS.Unitary A} := by
  simpa [GS.UnitaryGeometry.CSupported] using
    GS.UnitaryManifold.compact_blockU_set (fun _ : Fin n => 0)

theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) := by
  have houter : IsCompact {U : Fin q → CMat 2 | ∀ i, GS.Unitary (U i)} :=
    isCompact_pi_infinite (fun _ => isCompact_unitary_set 2)
  exact houter.prod ((isCompact_unitary_set q).prod ((isCompact_unitary_set q).prod houter))

/-- Every original factorization is retained in this compact parameter space. -/
theorem image_smallFactorMap (q : ℕ) :
    (@smallFactorMap q) '' smallFactorSet q = GS.UnitaryNonmanifold.localFamily q := by
  ext M
  constructor
  · rintro ⟨⟨U,A,B,V⟩,⟨hU,hA,hB,hV⟩,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB
  · intro hM
    obtain ⟨U,V,A,B,hU,hV,hA,hB,he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
    exact ⟨(U,A,B,V),⟨hU,hA,hB,hV⟩,he.symm⟩

theorem isCompact_localFamily (q : ℕ) : IsCompact (GS.UnitaryNonmanifold.localFamily q) := by
  rw [← image_smallFactorMap]
  exact (isCompact_smallFactorSet q).image (continuous_smallFactorMap q)

/-- The corresponding compact subtype, for results stated using CompactSpace. -/
abbrev SmallFactorSpace (q : ℕ) := {p : SmallBlockParameters q // p ∈ smallFactorSet q}

instance smallFactorSpace_compactSpace (q : ℕ) : CompactSpace (SmallFactorSpace q) :=
  isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)

def smallFactorValue (q : ℕ) (p : SmallFactorSpace q) : CMat (q*2) :=
  smallFactorMap p.val

theorem continuous_smallFactorValue (q : ℕ) : Continuous (smallFactorValue q) :=
  (continuous_smallFactorMap q).comp continuous_subtype_val

theorem range_smallFactorValue (q : ℕ) :
    Set.range (smallFactorValue q) = GS.UnitaryNonmanifold.localFamily q := by
  rw [← image_smallFactorMap]
  ext M
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p.val,p.property,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

end GS.UnitaryLocalModel
