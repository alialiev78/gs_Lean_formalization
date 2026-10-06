module

public import GS.Extensions.FiniteTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The original compact-domain construction

No polar-log replacement is made. The implication G-fibre => F-fibre is proved
from the actual definitions, including the collapsed circle. The converse is
not silently assumed proved: it is the sole hypothesis of the compact-image
homeomorphism below.
-/

noncomputable section
open Matrix
namespace GS.Extensions

 theorem rotation_zero : rotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, Matrix.one_apply]

 theorem rotation_transpose (t : ℝ) : (rotation t)ᵀ = rotation (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, Matrix.transpose_apply]

 theorem rotation_add (s t : ℝ) : rotation (s+t) = rotation s * rotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;>
    ring

 theorem matrixExp_zero (n : ℕ) : matrixExp (0 : Mat n) = 1 := by
  rw [matrixExp_eq_exp]
  simp

 theorem originalPsi_zero {q : ℕ} (Q₀ : Mat q) : originalPsi Q₀ 0 = Q₀ := by
  simp [originalPsi, matrixExp_zero]

 theorem originalF_zero_difference {q : ℕ} (Q₀ c : Mat q)
    (ell r : Fin q → ℝ) (u v : CircleVector) :
    originalF Q₀ (ell,r,c,0,u) = originalF Q₀ (ell,r,c,0,v) := by
  simp only [originalF, add_zero, sub_zero, middleBlock_equal]

 theorem originalF_simultaneous_neg {q : ℕ} (Q₀ c z : Mat q)
    (ell r : Fin q → ℝ) (u : CircleVector) :
    originalF Q₀ (ell,r,c,-z,-u) = originalF Q₀ (ell,r,c,z,u) := by
  simp only [originalF, sub_eq_add_neg, neg_neg, middleBlock_swap]

/-- One entire direction of the actual f/g fibre equivalence. This has no
smallness, injectivity-of-exp, coverage, or manifold hypothesis. -/
 theorem originalF_eq_of_originalG_eq {q : ℕ} (Q₀ : Mat q)
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : originalG (ell,r,c,z,u) = originalG (ell',r',c',w,v)) :
    originalF Q₀ (ell,r,c,z,u) = originalF Q₀ (ell',r',c',w,v) := by
  obtain ⟨he, hr, hc, hrest⟩ :=
    (originalG_fibres ell r ell' r' c z c' w u v hu hv).mp h
  subst ell'
  subst r'
  subst c'
  rcases hrest with ⟨hz,hw⟩ | ⟨huv,hzw⟩ | ⟨huv,hzw⟩
  · subst z
    subst w
    exact originalF_zero_difference Q₀ c ell r u v
  · subst u
    subst z
    rfl
  · subst u
    subst z
    exact originalF_simultaneous_neg Q₀ c w ell r v

 theorem originalF_eq_of_originalG_eq_on_K {q : ℕ} (Q₀ : Mat q) (η : ℝ)
    {p p' : OriginalParameters q} (hp : p ∈ originalK q η)
    (hp' : p' ∈ originalK q η) (h : originalG p = originalG p') :
    originalF Q₀ p = originalF Q₀ p' := by
  rcases p with ⟨ell,r,c,z,u⟩
  rcases p' with ⟨ell',r',c',w,v⟩
  exact originalF_eq_of_originalG_eq Q₀ ell r ell' r' c z c' w u v
    hp.2.2.2.2.2.2.2 hp'.2.2.2.2.2.2.2 h

/-- A fixed representative of the unit circle, only for marking the basepoint. -/
def circleBase : CircleVector := ![1,0]

 theorem circleBase_mem : OnCircle circleBase := by norm_num [circleBase, OnCircle]

 def originalBaseParameters (q : ℕ) : OriginalParameters q :=
  (0,0,0,0,circleBase)

 theorem originalBaseParameters_mem (q : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    originalBaseParameters q ∈ originalK q η := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, circleBase_mem⟩
  · intro i; simpa [originalBaseParameters] using hη
  · intro i; simpa [originalBaseParameters] using hη
  · intro i _; rfl
  · simp [originalBaseParameters, IsSkew]
  · simp [originalBaseParameters, IsSkew]
  · simpa [originalBaseParameters, frobSq, frobInner] using sq_nonneg η
  · simpa [originalBaseParameters, frobSq, frobInner] using sq_nonneg η

 theorem originalF_basePoint {q : ℕ} (Q₀ : Mat q) :
    originalF Q₀ (originalBaseParameters q) = basePoint Q₀ := by
  ext i j
  simp [originalF, originalBaseParameters, originalPsi_zero, rotation_zero,
    middleBlock_equal, basePoint, finProdFinEquiv]
  exact Or.inl rfl

 theorem originalG_basePoint (q : ℕ) :
    originalG (originalBaseParameters q) = (0,0,0,0) := by
  simp only [originalG, originalBaseParameters, Prod.mk.injEq, true_and]
  ext i j
  simp [GS.outer]

/-- Compactness and continuity are now discharged for the concrete domain and
maps. Only the genuinely missing reverse fibre implication is assumed. -/
 theorem original_compact_homeomorphism {q : ℕ} (Q₀ : Mat q) (η : ℝ)
    (hforward : ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' → originalG p = originalG p') :
    ∃ h : Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val) ≃ₜ
        Set.range (fun p : ↥(originalK q η) => originalG p.val),
      ∀ p : ↥(originalK q η),
        h ⟨originalF Q₀ p.val, ⟨p,rfl⟩⟩ = ⟨originalG p.val, ⟨p,rfl⟩⟩ := by
  letI : CompactSpace ↥(originalK q η) := isCompact_iff_compactSpace.mp (isCompact_originalK q η)
  apply exists_homeomorph_ranges_of_same_fibres
    (fun p : ↥(originalK q η) => originalF Q₀ p.val)
    (fun p : ↥(originalK q η) => originalG p.val)
    ((continuous_originalF Q₀).comp continuous_subtype_val)
    ((continuous_originalG q).comp continuous_subtype_val)
  intro p p'
  exact ⟨hforward p.val p.property p'.val p'.property,
    originalF_eq_of_originalG_eq_on_K Q₀ η p.property p'.property⟩

/-- The chosen basepoint lies in the actual compact parameterized image. This
is not a proof that the image contains a neighbourhood in the whole family. -/
 theorem basePoint_mem_originalF_image {q : ℕ} (Q₀ : Mat q) {η : ℝ} (hη : 0 ≤ η) :
    basePoint Q₀ ∈ originalF Q₀ '' originalK q η :=
  ⟨originalBaseParameters q, originalBaseParameters_mem q hη, originalF_basePoint Q₀⟩

end GS.Extensions
