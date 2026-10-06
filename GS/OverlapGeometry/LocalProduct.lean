module

public import GS.OverlapGeometry.KernelCayley
public import GS.OverlapGeometry.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Local horizontal--stabilizer factorization

Multiplication of two factor Cayley lifts has derivative addition at the
identity. Restricting the two inputs to complementary horizontal and kernel
subspaces therefore gives a genuine local inverse-function chart.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion GS.Extensions Filter Set
open scoped Topology Manifold

namespace GS.OverlapGeometry
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

theorem chartInv_fderiv_zero (Q : BlockO block) (v : Model block) :
    fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) := by
  have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (chartInv_line_hasDerivAt_zero Q v)

def blockProductCoordinates (block : Fin n → ℕ) (x : Model block × Model block) :
    Model block :=
  chartMap (1 : BlockO block)
    (chartInv (1 : BlockO block) x.1 * chartInv (1 : BlockO block) x.2)

@[simp] theorem blockProductCoordinates_zero (block : Fin n → ℕ) :
    blockProductCoordinates block 0 = 0 := by
  simp [blockProductCoordinates]
  exact chartMap_base (1 : BlockO block)

theorem blockProductCoordinates_smooth_zero (block : Fin n → ℕ) :
    ContDiffAt ℝ ⊤ (blockProductCoordinates block) 0 := by
  have hm := smooth_mul_at
    ((chartInv_smooth (1 : BlockO block)).contDiffAt.comp 0 contDiffAt_fst)
    ((chartInv_smooth (1 : BlockO block)).contDiffAt.comp 0 contDiffAt_snd)
  have hc := chartMap_smooth_at (1 : BlockO block) (1 : Mat n) (by
    change admissible ((1 : Mat n)ᵀ * 1)
    simpa using admissible_one (n := n))
  have hc' : ContDiffAt ℝ ⊤ (chartMap (1 : BlockO block))
      ((fun x : Model block × Model block => chartInv (1 : BlockO block) x.1 *
        chartInv (1 : BlockO block) x.2) 0) := by simpa using hc
  exact hc'.comp 0 hm

theorem blockProductCoordinates_fderiv_zero (block : Fin n → ℕ)
    (v : Model block × Model block) :
    fderiv ℝ (blockProductCoordinates block) 0 v = v.1 + v.2 := by
  have hd₁ := chartInv_line_hasDerivAt_zero (1 : BlockO block) v.1
  have hd₂ := chartInv_line_hasDerivAt_zero (1 : BlockO block) v.2
  have hp := hasDerivAt_matrix_mul hd₁ hd₂
  have hc := (chartMap_smooth_at (1 : BlockO block) (1 : Mat n) (by
    change admissible ((1 : Mat n)ᵀ * 1)
    simpa using admissible_one (n := n))).differentiableAt (by simp)
  have hd : HasDerivAt
      (fun t : ℝ => chartInv (1 : BlockO block) (t • v.1) *
        chartInv (1 : BlockO block) (t • v.2))
      (fderiv ℝ (chartInv (1 : BlockO block)) 0 (v.1 + v.2)) 0 := by
    rw [chartInv_fderiv_zero]
    simpa only [zero_smul, chartInv_zero, show (1 : BlockO block).val = (1 : Mat n) from rfl,
      Matrix.one_mul, Matrix.mul_one, Submodule.coe_add, smul_add] using hp
  have hinv := congrArg (fun D : Model block →L[ℝ] Model block => D (v.1 + v.2))
    (chart_differential_left_inverse (1 : BlockO block) 0 (zero_mem_parameterDomain block))
  have he : fderiv ℝ (chartMap (1 : BlockO block)) (1 : Mat n)
      (fderiv ℝ (chartInv (1 : BlockO block)) 0 (v.1 + v.2)) = v.1 + v.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      chartInv_zero, show (1 : BlockO block).val = (1 : Mat n) from rfl] using hinv
  have hactual : HasDerivAt (fun t : ℝ => blockProductCoordinates block (t • v))
      (v.1 + v.2) 0 := by
    have hh := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
    rw [he] at hh
    exact hh
  have hi := ((blockProductCoordinates_smooth_zero block).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique hactual

def factorProductCoordinates (block₁ block₂ : Fin n → ℕ)
    (x : PairModel block₁ block₂ × PairModel block₁ block₂) : PairModel block₁ block₂ :=
  (blockProductCoordinates block₂ (x.1.1, x.2.1),
    blockProductCoordinates block₁ (x.1.2, x.2.2))

theorem factorProductCoordinates_eq (x y : PairModel block₁ block₂) :
    factorProductCoordinates block₁ block₂ (x, y) =
      factorCoordinates (1 : FactorGroup block₁ block₂)
        (factorLift (1 : FactorGroup block₁ block₂) x *
          factorLift (1 : FactorGroup block₁ block₂) y) := by
  apply Prod.ext <;> change chartMap _ _ = chartMap _ _
  · rw [show ((factorLift (1 : FactorGroup block₁ block₂) x *
        factorLift (1 : FactorGroup block₁ block₂) y).1).val =
        (factorLift (1 : FactorGroup block₁ block₂) x).1.val *
        (factorLift (1 : FactorGroup block₁ block₂) y).1.val from rfl,
      factorLift_left_val, factorLift_left_val]
    rfl
  · rw [show ((factorLift (1 : FactorGroup block₁ block₂) x *
        factorLift (1 : FactorGroup block₁ block₂) y).2).val =
        (factorLift (1 : FactorGroup block₁ block₂) x).2.val *
        (factorLift (1 : FactorGroup block₁ block₂) y).2.val from rfl,
      factorLift_right_val, factorLift_right_val]
    rfl

@[simp] theorem factorProductCoordinates_zero (block₁ block₂ : Fin n → ℕ) :
    factorProductCoordinates block₁ block₂ 0 = 0 := by
  change (blockProductCoordinates _ 0, blockProductCoordinates _ 0) = (0, 0)
  simp only [blockProductCoordinates_zero]

theorem blockProductCoordinates_hasFDerivAt_zero (block : Fin n → ℕ) :
    HasFDerivAt (blockProductCoordinates block)
      (ContinuousLinearMap.fst ℝ (Model block) (Model block) +
        ContinuousLinearMap.snd ℝ (Model block) (Model block)) 0 := by
  have h := ((blockProductCoordinates_smooth_zero block).differentiableAt (by simp)).hasFDerivAt
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  exact (blockProductCoordinates_fderiv_zero block v).symm

def reorderLeft (block₁ block₂ : Fin n → ℕ) :
    (PairModel block₁ block₂ × PairModel block₁ block₂) →L[ℝ] (Model block₂ × Model block₂) :=
  ((ContinuousLinearMap.fst ℝ (Model block₂) (Model block₁)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.fst ℝ (Model block₂) (Model block₁)).comp
    (ContinuousLinearMap.snd ℝ _ _))

def reorderRight (block₁ block₂ : Fin n → ℕ) :
    (PairModel block₁ block₂ × PairModel block₁ block₂) →L[ℝ] (Model block₁ × Model block₁) :=
  ((ContinuousLinearMap.snd ℝ (Model block₂) (Model block₁)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.snd ℝ (Model block₂) (Model block₁)).comp
    (ContinuousLinearMap.snd ℝ _ _))

theorem factorProductCoordinates_smooth_zero (block₁ block₂ : Fin n → ℕ) :
    ContDiffAt ℝ ⊤ (factorProductCoordinates block₁ block₂) 0 := by
  have hl0 : ContDiffAt ℝ ⊤ (blockProductCoordinates block₂) (reorderLeft block₁ block₂ 0) :=
    by simpa using blockProductCoordinates_smooth_zero block₂
  have hr0 : ContDiffAt ℝ ⊤ (blockProductCoordinates block₁) (reorderRight block₁ block₂ 0) :=
    by simpa using blockProductCoordinates_smooth_zero block₁
  have hl := hl0.comp 0 (reorderLeft block₁ block₂).contDiff.contDiffAt
  have hr := hr0.comp 0 (reorderRight block₁ block₂).contDiff.contDiffAt
  exact hl.prodMk hr

theorem factorProductCoordinates_hasFDerivAt_zero (block₁ block₂ : Fin n → ℕ) :
    HasFDerivAt (factorProductCoordinates block₁ block₂)
      (ContinuousLinearMap.fst ℝ (PairModel block₁ block₂) (PairModel block₁ block₂) +
        ContinuousLinearMap.snd ℝ (PairModel block₁ block₂) (PairModel block₁ block₂)) 0 := by
  have hl0 : HasFDerivAt (blockProductCoordinates block₂)
      (ContinuousLinearMap.fst ℝ (Model block₂) (Model block₂) +
        ContinuousLinearMap.snd ℝ (Model block₂) (Model block₂)) (reorderLeft block₁ block₂ 0) :=
    by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero block₂
  have hr0 : HasFDerivAt (blockProductCoordinates block₁)
      (ContinuousLinearMap.fst ℝ (Model block₁) (Model block₁) +
        ContinuousLinearMap.snd ℝ (Model block₁) (Model block₁)) (reorderRight block₁ block₂ 0) :=
    by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero block₁
  have hl := hl0.comp 0 (reorderLeft block₁ block₂).hasFDerivAt
  have hr := hr0.comp 0 (reorderRight block₁ block₂).hasFDerivAt
  convert hl.prodMk hr using 1 <;> first | rfl | (ext v <;> rfl)

def sliceProduct (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (x : HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ) :
    PairModel block₁ block₂ :=
  factorProductCoordinates block₁ block₂ (x.1.val, x.2.val)

def sliceInclusion (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ) →L[ℝ]
      (PairModel block₁ block₂ × PairModel block₁ block₂) :=
  ((HorizontalModel block₁ block₂ σ).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((OrbitKernel block₁ block₂ σ).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem sliceProduct_zero (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    sliceProduct block₁ block₂ σ 0 = 0 := factorProductCoordinates_zero _ _

theorem sliceProduct_smooth_zero (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ContDiffAt ℝ ⊤ (sliceProduct block₁ block₂ σ) 0 := by
  have hf : ContDiffAt ℝ ⊤ (factorProductCoordinates block₁ block₂)
      (sliceInclusion block₁ block₂ σ 0) :=
    by simpa only [map_zero] using factorProductCoordinates_smooth_zero block₁ block₂
  exact ContDiffAt.comp
    (f := fun x : HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ =>
      sliceInclusion block₁ block₂ σ x)
    (g := factorProductCoordinates block₁ block₂) 0 hf
    (@ContinuousLinearMap.contDiff ℝ (HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ) (PairModel block₁ block₂ × PairModel block₁ block₂) _ _ _ _ _ ⊤
      (sliceInclusion block₁ block₂ σ)).contDiffAt

set_option synthInstance.maxHeartbeats 100000 in
theorem sliceProduct_hasFDerivAt_zero (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) :
    HasFDerivAt (sliceProduct block₁ block₂ σ)
      (horizontalKernelEquiv block₁ block₂ σ : _ →L[ℝ] _) 0 := by
  have hf : HasFDerivAt (factorProductCoordinates block₁ block₂)
      (ContinuousLinearMap.fst ℝ (PairModel block₁ block₂) (PairModel block₁ block₂) +
        ContinuousLinearMap.snd ℝ (PairModel block₁ block₂) (PairModel block₁ block₂))
      (sliceInclusion block₁ block₂ σ 0) := by
    simpa only [map_zero] using factorProductCoordinates_hasFDerivAt_zero block₁ block₂
  have hi : HasFDerivAt (sliceInclusion block₁ block₂ σ)
      (sliceInclusion block₁ block₂ σ) 0 :=
    @ContinuousLinearMap.hasFDerivAt ℝ _ (HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ) _ _ _ (PairModel block₁ block₂ × PairModel block₁ block₂) _ _ _
      (sliceInclusion block₁ block₂ σ) 0
  have hd := HasFDerivAt.comp
    (𝕜 := ℝ)
    (f := fun x : HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ =>
      sliceInclusion block₁ block₂ σ x)
    (g := factorProductCoordinates block₁ block₂) 0 hf hi
  convert hd using 1 <;> first | rfl | (ext v <;> rfl)

def sliceProductChart (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    OpenPartialHomeomorph (HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ)
      (PairModel block₁ block₂) :=
  (sliceProduct_smooth_zero block₁ block₂ σ).toOpenPartialHomeomorph _
    (sliceProduct_hasFDerivAt_zero block₁ block₂ σ) (by simp)

@[simp] theorem sliceProductChart_apply (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (x : HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ) :
    sliceProductChart block₁ block₂ σ x = sliceProduct block₁ block₂ σ x := rfl

theorem sliceProductChart_zero_mem_source (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : (0 : HorizontalModel block₁ block₂ σ × OrbitKernel block₁ block₂ σ)
      ∈ (sliceProductChart block₁ block₂ σ).source :=
  (sliceProduct_smooth_zero block₁ block₂ σ).mem_toOpenPartialHomeomorph_source _ (by simp)

end GS.OverlapGeometry
