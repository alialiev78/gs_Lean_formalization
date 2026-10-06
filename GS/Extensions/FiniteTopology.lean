module

public import GS.OriginalLocalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Finite-dimensional topology used by the original fibre proof

The argument uses coordinatewise compact intervals, not an identification of
mathlib's default matrix norm with the Frobenius norm.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 theorem continuous_frobInner :
    Continuous (fun p : Matrix ι κ ℝ × Matrix ι κ ℝ => frobInner p.1 p.2) := by
  unfold frobInner
  fun_prop

 theorem continuous_frobSq : Continuous (@frobSq ι κ _ _) := by
  unfold frobSq frobInner
  fun_prop

 theorem entry_sq_le_frobSq (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    A i j ^ 2 ≤ frobSq A := by
  classical
  have h₁ : A i j * A i j ≤ ∑ l, A i l * A i l :=
    Finset.single_le_sum (fun l _ => mul_self_nonneg (A i l)) (Finset.mem_univ j)
  have h₂ : (∑ l, A i l * A i l) ≤ ∑ r, ∑ l, A r l * A r l :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg (A r l)))
      (Finset.mem_univ i)
  simpa only [frobSq, frobInner, pow_two] using h₁.trans h₂

 theorem abs_entry_le_of_frobSq_le {A : Matrix ι κ ℝ} {η : ℝ}
    (h : frobSq A ≤ η^2) (i : ι) (j : κ) : |A i j| ≤ |η| := by
  have hs := (entry_sq_le_frobSq A i j).trans h
  by_contra hn
  have hn' : |η| < |A i j| := lt_of_not_ge hn
  have hp : 0 < (|A i j| - |η|) * (|A i j| + |η|) :=
    mul_pos (sub_pos.mpr hn') (by linarith [abs_nonneg η])
  nlinarith [sq_abs (A i j), sq_abs η]

 theorem onCircle_abs_le_one {u : CircleVector} (hu : OnCircle u) (i : Fin 2) :
    |u i| ≤ 1 := by
  have he : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
  have hs : u i ^ 2 ≤ 1 := by
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, id_eq] <;>
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  by_contra hn
  have hp : 0 < (|u i| - 1) * (|u i| + 1) :=
    mul_pos (by linarith [lt_of_not_ge hn]) (by positivity)
  nlinarith [sq_abs (u i)]

 theorem isClosed_isSkew (n : ℕ) : IsClosed {A : Mat n | IsSkew A} := by
  change IsClosed {A : Mat n | Aᵀ = -A}
  exact isClosed_eq (by fun_prop) (by fun_prop)

 theorem isClosed_supported (n : ℕ) (block : Fin n → ℕ) :
    IsClosed {A : Mat n | Supported block A} := by
  simp only [Supported, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

 theorem isClosed_orthogonal (n : ℕ) : IsClosed {A : Mat n | Orthogonal A} := by
  change IsClosed ({A : Mat n | Aᵀ * A = 1} ∩ {A : Mat n | A * Aᵀ = 1})
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)

 theorem isClosed_originalK (q : ℕ) (η : ℝ) : IsClosed (originalK q η) := by
  have hell : IsClosed {p : OriginalParameters q | ∀ i, |p.1 i| ≤ η} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)
  have hr : IsClosed {p : OriginalParameters q | ∀ j, |p.2.1 j| ≤ η} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const)
  have hr₀ : IsClosed {p : OriginalParameters q |
      ∀ j : Fin q, j.val = 0 → p.2.1 j = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j => isClosed_iInter
      (fun _ => isClosed_eq (by fun_prop) continuous_const))
  have hc : IsClosed {p : OriginalParameters q | IsSkew p.2.2.1} :=
    (isClosed_isSkew q).preimage (by fun_prop)
  have hz : IsClosed {p : OriginalParameters q | IsSkew p.2.2.2.1} :=
    (isClosed_isSkew q).preimage (by fun_prop)
  have hcn : IsClosed {p : OriginalParameters q | frobSq p.2.2.1 ≤ η^2} :=
    isClosed_le (continuous_frobSq.comp (by fun_prop)) continuous_const
  have hzn : IsClosed {p : OriginalParameters q | frobSq p.2.2.2.1 ≤ η^2} :=
    isClosed_le (continuous_frobSq.comp (by fun_prop)) continuous_const
  have hu : IsClosed {p : OriginalParameters q | OnCircle p.2.2.2.2} := by
    unfold OnCircle
    exact isClosed_eq (by fun_prop) continuous_const
  exact hell.inter (hr.inter (hr₀.inter (hc.inter (hz.inter
    (hcn.inter (hzn.inter hu))))))

/-- Actual compactness of the manuscript's parameter set, including its skew
constraints, Frobenius bounds, anchored right angle and circle. No compactness
or norm-equivalence hypothesis is passed to this theorem. -/
 theorem isCompact_originalK (q : ℕ) (η : ℝ) : IsCompact (originalK q η) := by
  letI : PartialOrder (Mat q) := inferInstanceAs (PartialOrder (Fin q → Fin q → ℝ))
  letI : CompactIccSpace (Mat q) :=
    inferInstanceAs (CompactIccSpace (Fin q → Fin q → ℝ))
  let ρ : ℝ := |η| + 1
  let lo : OriginalParameters q :=
    (fun _ => -ρ, fun _ => -ρ, fun _ _ => -ρ, fun _ _ => -ρ, fun _ => -ρ)
  let hi : OriginalParameters q :=
    (fun _ => ρ, fun _ => ρ, fun _ _ => ρ, fun _ _ => ρ, fun _ => ρ)
  have hsub : originalK q η ⊆ Set.Icc lo hi := by
    rintro ⟨ell, r, c, z, u⟩ hp
    rcases hp with ⟨hell, hr, hr₀, hc, hz, hcn, hzn, hu⟩
    have hη : η ≤ ρ := by dsimp [ρ]; linarith [le_abs_self η]
    have habsη : |η| ≤ ρ := by dsimp [ρ]; linarith
    have hone : (1 : ℝ) ≤ ρ := by dsimp [ρ]; linarith [abs_nonneg η]
    have he : ∀ i, -ρ ≤ ell i ∧ ell i ≤ ρ :=
      fun i => abs_le.mp ((hell i).trans hη)
    have hr' : ∀ i, -ρ ≤ r i ∧ r i ≤ ρ :=
      fun i => abs_le.mp ((hr i).trans hη)
    have hc' : ∀ i j, -ρ ≤ c i j ∧ c i j ≤ ρ :=
      fun i j => abs_le.mp ((abs_entry_le_of_frobSq_le hcn i j).trans habsη)
    have hz' : ∀ i j, -ρ ≤ z i j ∧ z i j ≤ ρ :=
      fun i j => abs_le.mp ((abs_entry_le_of_frobSq_le hzn i j).trans habsη)
    have hu' : ∀ i, -ρ ≤ u i ∧ u i ≤ ρ :=
      fun i => abs_le.mp ((onCircle_abs_le_one hu i).trans hone)
    exact ⟨⟨fun i => (he i).1, fun i => (hr' i).1,
      fun i j => (hc' i j).1, fun i j => (hz' i j).1, fun i => (hu' i).1⟩,
      ⟨fun i => (he i).2, fun i => (hr' i).2,
      fun i j => (hc' i j).2, fun i j => (hz' i j).2, fun i => (hu' i).2⟩⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_originalK q η) hsub

 theorem isCompact_originalF_image {q : ℕ} (Q₀ : Mat q) (η : ℝ) :
    IsCompact (originalF Q₀ '' originalK q η) :=
  (isCompact_originalK q η).image (continuous_originalF Q₀)

 theorem isCompact_originalG_image (q : ℕ) (η : ℝ) :
    IsCompact ((@originalG q) '' originalK q η) :=
  (isCompact_originalK q η).image (continuous_originalG q)

end GS.Extensions
