module

public import GS.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Sharing and scalar least squares

These are exact finite-dimensional least-squares identities. They do not assert
that an arbitrary combination of sharing and overlap can use a 1/2 mask.

-/

noncomputable section
open scoped BigOperators
namespace GS

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Expanding unique coordinates to all physical copies. -/
def expandSharing (τ : ι → κ) (θ : κ → ℝ) : ι → ℝ := θ ∘ τ

/-- The transpose of the expansion: sum over all copies, not their mean. -/
def accumulateSharing (τ : ι → κ) (g : ι → ℝ) (p : κ) : ℝ :=
  ∑ i, if τ i = p then g i else 0

/-- The exact algebraic adjoint identity underlying reverse-mode AD. -/
theorem sharing_adjoint (τ : ι → κ) (θ : κ → ℝ) (g : ι → ℝ) :
    (∑ i, expandSharing τ θ i * g i) = ∑ p, θ p * accumulateSharing τ g p := by
  classical
  calc
    (∑ i, expandSharing τ θ i * g i) =
        ∑ i, ∑ p, if τ i = p then θ p * g i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [expandSharing]
    _ = ∑ p, ∑ i, if τ i = p then θ p * g i else 0 := Finset.sum_comm
    _ = ∑ p, θ p * accumulateSharing τ g p := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [accumulateSharing, Finset.mul_sum, mul_ite]

/-- One tied scalar entry; the proof applies independently to each block entry. -/
def sampleMean (s : Finset ι) (a : ι → ℝ) : ℝ := (∑ i ∈ s, a i) / s.card

theorem centered_sum_eq_zero (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ) :
    (∑ i ∈ s, (a i - sampleMean s a)) = 0 := by
  have hn : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr hs))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold sampleMean
  field_simp [hn] <;> ring

theorem sampleMean_variance_identity (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (x : ℝ) :
    (∑ i ∈ s, (a i - x)^2) =
      (∑ i ∈ s, (a i - sampleMean s a)^2) + (s.card : ℝ) * (x - sampleMean s a)^2 := by
  let m := sampleMean s a
  have hc : (∑ i ∈ s, (a i - m)) = 0 := centered_sum_eq_zero s hs a
  calc
    (∑ i ∈ s, (a i - x)^2) =
        ∑ i ∈ s, ((a i - m)^2 - 2 * (x-m) * (a i-m) + (x-m)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, (a i - m)^2) + (s.card : ℝ) * (x-m)^2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hc, mul_zero, sub_zero,
        Finset.sum_const, nsmul_eq_mul]
    _ = _ := rfl

theorem sampleMean_minimizes (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (x : ℝ) :
    (∑ i ∈ s, (a i - sampleMean s a)^2) ≤ (∑ i ∈ s, (a i - x)^2) := by
  rw [sampleMean_variance_identity s hs a x]
  have hn : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (x - sampleMean s a)]

/-- A minimal two-copy model disproves exactness of overlap-only minimization. -/
theorem sharing_overlap_half_not_minimal :
    (1 - (1 : ℝ) - 0)^2 + (0 : ℝ)^2 <
      (1 - (1/2 : ℝ) - 1/2)^2 + (1/2 : ℝ)^2 := by
  norm_num

/-- Normal-equation characterization of least squares for an arbitrary linear
parameter expansion. No pseudo-inverse or rank assumption is hidden here. -/
theorem leastSquares_of_normal_equations
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] Matrix ι κ ℝ) (A : Matrix ι κ ℝ) (θ : E)
    (h : ∀ δ : E, frobInner (A - L θ) (L δ) = 0) (φ : E) :
    frobSq (A - L θ) ≤ frobSq (A - L φ) := by
  have he : A - L φ = (A - L θ) + L (θ - φ) := by
    rw [map_sub]
    abel
  rw [he, frobSq_add, h (θ - φ)]
  have hn := frobSq_nonneg (L (θ - φ))
  linarith

end GS
