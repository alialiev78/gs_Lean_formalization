module

public import GS.Nonmanifold.SkewCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The unbounded model containing the original g(K)

Two separate steps are constructed here:
* the original row-skew, anchored-coordinate model is homeomorphic to a
  product of unconstrained finite coordinate spaces and a genuine rank cone;
* for eta > 0 the original g(K_eta) contains a relative neighbourhood of zero
  in this unbounded model, with an explicit polynomial neighbourhood.

This is the g-side neighbourhood statement. It must not be confused with the
still-open f-side coverage of a neighbourhood in the entire GS matrix family.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
open scoped BigOperators
namespace GS.Nonmanifold

abbrev NonzeroIndex (q : ℕ) := {i : Fin q // i.val ≠ 0}

def packRight {q : ℕ} (r : Fin q → ℝ) : NonzeroIndex q → ℝ := fun j => r j.val

def unpackRight {q : ℕ} (x : NonzeroIndex q → ℝ) : Fin q → ℝ :=
  fun j => if h : j.val = 0 then 0 else x ⟨j,h⟩

theorem unpackRight_anchored {q : ℕ} (x : NonzeroIndex q → ℝ) :
    ∀ j : Fin q, j.val = 0 → unpackRight x j = 0 := by
  intro j hj
  simp [unpackRight, hj]

theorem pack_unpackRight {q : ℕ} (x : NonzeroIndex q → ℝ) :
    packRight (unpackRight x) = x := by
  funext j
  simp [packRight, unpackRight, j.property]

theorem unpack_packRight {q : ℕ} (r : Fin q → ℝ)
    (hr : ∀ j : Fin q, j.val = 0 → r j = 0) :
    unpackRight (packRight r) = r := by
  funext j
  by_cases hj : j.val = 0
  · simp [packRight, unpackRight, hj, hr j hj]
  · simp [packRight, unpackRight, hj]

theorem continuous_packRight (q : ℕ) : Continuous (@packRight q) := by
  unfold packRight
  fun_prop

theorem continuous_unpackRight (q : ℕ) : Continuous (@unpackRight q) := by
  apply continuous_pi
  intro j
  by_cases hj : j.val = 0
  · simp only [unpackRight, dif_pos hj]
    exact continuous_const
  · simp only [unpackRight, dif_neg hj]
    exact continuous_apply _

/-- The original image constraints with only the radius bounds removed. -/
def originalModelSet (q : ℕ) : Set (OriginalImageCoordinates q) :=
  {p | (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧ p.2.2.2.rank ≤ 1}

abbrev OriginalModel (q : ℕ) := ↥(originalModelSet q)

abbrev ModelCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (NonzeroIndex q → ℝ) × (UpperIndex q → ℝ) ×
    {Z : Matrix (Fin 2) (UpperIndex q) ℝ // Z.rank ≤ 1}

def encodeModel {q : ℕ} (p : OriginalModel q) : ModelCoordinates q :=
  (p.val.1, packRight p.val.2.1, packSkew p.val.2.2.1,
    ⟨packRows p.val.2.2.2, packRows_rank_le_one _ p.property.2.2.2⟩)

def decodeModel {q : ℕ} (p : ModelCoordinates q) : OriginalModel q :=
  ⟨(p.1, unpackRight p.2.1, unpackSkew p.2.2.1, unpackRows p.2.2.2.val),
    unpackRight_anchored _, unpackSkew_isSkew _, unpackRows_isSkew _,
    unpackRows_rank_le_one _ p.2.2.2.property⟩

theorem decode_encodeModel {q : ℕ} (p : OriginalModel q) :
    decodeModel (encodeModel p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨ell,r,c,W⟩,hr,hc,hW,hRank⟩
  change (ell, unpackRight (packRight r), unpackSkew (packSkew c),
    unpackRows (packRows W)) = (ell,r,c,W)
  rw [unpack_packRight r hr, unpack_packSkew hc, unpack_packRows W hW]

theorem encode_decodeModel {q : ℕ} (p : ModelCoordinates q) :
    encodeModel (decodeModel p) = p := by
  rcases p with ⟨ell,r,c,W⟩
  refine Prod.ext ?_ ?_
  · rfl
  apply Prod.ext
  · exact pack_unpackRight r
  · apply Prod.ext
    · exact pack_unpackSkew c
    · apply Subtype.ext
      exact pack_unpackRows W.val

theorem continuous_encodeModel (q : ℕ) : Continuous (@encodeModel q) := by
  unfold encodeModel packRight packSkew packRows
  fun_prop

theorem continuous_decodeModel (q : ℕ) : Continuous (@decodeModel q) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_fst
  · apply Continuous.prodMk
    · exact (continuous_unpackRight q).comp (by fun_prop)
    · apply Continuous.prodMk
      · exact (continuous_unpackSkew q).comp (by fun_prop)
      · exact (continuous_unpackRows q).comp (by fun_prop)

/-- Removes all redundant linear coordinates while preserving the induced topology. -/
def originalModelHomeomorph (q : ℕ) : OriginalModel q ≃ₜ ModelCoordinates q where
  toFun := encodeModel
  invFun := decodeModel
  left_inv := decode_encodeModel
  right_inv := encode_decodeModel
  continuous_toFun := continuous_encodeModel q
  continuous_invFun := continuous_decodeModel q

/-- A polynomial squared radius on the full ambient g-coordinate space. -/
def modelRadiusSq {q : ℕ} (p : OriginalImageCoordinates q) : ℝ :=
  (∑ i, p.1 i^2) + (∑ j, p.2.1 j^2) + frobSq p.2.2.1 + frobSq p.2.2.2

theorem continuous_modelRadiusSq (q : ℕ) : Continuous (@modelRadiusSq q) := by
  unfold modelRadiusSq frobSq frobInner
  fun_prop

theorem originalG_image_subset_model (q : ℕ) (η : ℝ) :
    originalG '' originalK q η ⊆ originalModelSet q := by
  rw [originalG_image_eq]
  rintro p ⟨hell,hr,hr0,hc,hcn,hW,hRank,hWn⟩
  exact ⟨hr0,hc,hW,hRank⟩

/-- An explicit small relative neighbourhood lies in the original compact image. -/
theorem small_modelRadius_mem_originalG {q : ℕ} {η : ℝ} (hη : 0 < η)
    (p : OriginalImageCoordinates q) (hp : p ∈ originalModelSet q)
    (hn : modelRadiusSq p < η^2) : p ∈ originalG '' originalK q η := by
  rw [originalG_image_eq]
  have hL : 0 ≤ ∑ i, p.1 i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hR : 0 ≤ ∑ j, p.2.1 j^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hc := frobSq_nonneg p.2.2.1
  have hW := frobSq_nonneg p.2.2.2
  have hC : frobSq p.2.2.1 ≤ η^2 := by dsimp [modelRadiusSq] at hn; linarith
  have hZ : frobSq p.2.2.2 ≤ η^2 := by dsimp [modelRadiusSq] at hn; linarith
  refine ⟨?_,?_,hp.1,hp.2.1,hC,hp.2.2.1,hp.2.2.2,hZ⟩
  · intro i
    have hs : p.1 i^2 ≤ ∑ k, p.1 k^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hh : p.1 i^2 < η^2 := by dsimp [modelRadiusSq] at hn; linarith
    have ha := abs_nonneg (p.1 i)
    nlinarith [sq_abs (p.1 i)]
  · intro j
    have hs : p.2.1 j^2 ≤ ∑ k, p.2.1 k^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hh : p.2.1 j^2 < η^2 := by dsimp [modelRadiusSq] at hn; linarith
    have ha := abs_nonneg (p.2.1 j)
    nlinarith [sq_abs (p.2.1 j)]

/-- This is genuine neighbourhood coverage on the model side, not on the GS side. -/
theorem originalG_image_contains_relative_neighbourhood (q : ℕ) (η : ℝ)
    (hη : 0 < η) :
    ∃ V : Set (OriginalImageCoordinates q), IsOpen V ∧
      (0,0,0,0) ∈ V ∧ V ∩ originalModelSet q ⊆ originalG '' originalK q η := by
  refine ⟨{p | modelRadiusSq p < η^2},
    isOpen_lt (continuous_modelRadiusSq q) continuous_const, ?_, ?_⟩
  · have hz : modelRadiusSq ((0,0,0,0) : OriginalImageCoordinates q) = 0 := by
      simp [modelRadiusSq, frobSq, frobInner]
    change modelRadiusSq ((0,0,0,0) : OriginalImageCoordinates q) < η^2
    rw [hz]
    exact sq_pos_of_pos hη
  · rintro p ⟨hn,hp⟩
    exact small_modelRadius_mem_originalG hη p hp hn

end GS.Nonmanifold
