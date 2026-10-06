module

public import GS.Extensions.OrbitCompact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A compactness tool for neighbourhood coverage

Existing compactness proofs are reused, not replaced or duplicated.
The full-fibre lemma does NOT by itself close OriginalLocalCoverageGoal.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

/-- Specialization of the compact-factor-image theorem to the exact
localFamily used in the manuscript specifications. -/
theorem isCompact_localFamily (q : ℕ) : IsCompact (localFamily q) := by
  exact isCompact_A3Orth 2 q 2 (permMatrix (scalarShuffle q 2))
    (permMatrix (scalarShuffle q 2))ᵀ

theorem isClosed_localFamily (q : ℕ) : IsClosed (localFamily q) :=
  (isCompact_localFamily q).isClosed

/-- Every open set containing the FULL fibre over x captures a neighbourhood
of x inside the whole compact image. The full-fibre hypothesis is essential:
this lemma does not promote an arbitrary selected branch to a neighbourhood. -/
theorem compact_full_fibre_neighbourhood
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    [T2Space K] [T2Space X] (f : K → X) (hf : Continuous f)
    (s : Set K) (hs : IsCompact s) (U : Set K) (hU : IsOpen U) (x : X)
    (hfull : ∀ k ∈ s, f k = x → k ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ f '' s → y ∈ f '' (s ∩ U) := by
  have hc : IsCompact (s \ U) :=
    hs.of_isClosed_subset (hs.isClosed.inter hU.isClosed_compl) (fun _ h => h.1)
  have himg : IsClosed (f '' (s \ U)) := (hc.image hf).isClosed
  refine ⟨(f '' (s \ U))ᶜ, himg.isOpen_compl, ?_, ?_⟩
  · rintro ⟨k, hk, he⟩
    exact hk.2 (hfull k hk.1 he)
  · intro y hy
    rintro ⟨k, hk, rfl⟩
    refine ⟨k, ⟨hk, ?_⟩, rfl⟩
    by_contra hn
    exact hy ⟨k, ⟨hk, hn⟩, rfl⟩

end GS.Continuation
