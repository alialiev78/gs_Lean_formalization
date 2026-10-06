module

public import GS.SharedGeometry.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Local horizontal--stabilizer product for shared factors

The derivative of multiplication in the actual shared Cayley coordinates is
addition.  The horizontal/kernel splitting makes this derivative invertible,
so the inverse function theorem supplies the needed local product chart.
No product decomposition of the image is assumed.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.CayleyCharts GS.Extensions Filter Set
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} {s right left : Pattern n}

def blockProductCoordinates (s : Pattern n) (x : Generator s × Generator s) :
    Generator s :=
  factorCoordinates (1 : Factor s)
    (matrixReconstruct (1 : Factor s) x.1 * matrixReconstruct (1 : Factor s) x.2)

@[simp] theorem blockProductCoordinates_zero (s : Pattern n) :
    blockProductCoordinates s 0 = 0 := by
  simp only [blockProductCoordinates, Prod.fst_zero, Prod.snd_zero,
    matrixReconstruct_zero, Factor.matrix_one, Matrix.one_mul]
  simpa only [matrixReconstruct_zero, Factor.matrix_one] using
    factorCoordinates_matrixReconstruct (1 : Factor s) (0 : Generator s)

theorem blockProductCoordinates_smooth_zero (s : Pattern n) :
    ContDiffAt ℝ ⊤ (blockProductCoordinates s) 0 := by
  have hm := smooth_mul_at
    ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_fst)
    ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_snd)
  have hc := factorCoordinates_smooth_at (1 : Factor s) (1 : Mat n) (by
    change admissible ((1 : Mat n)ᵀ * 1)
    simpa using admissible_one (n := n))
  have hc' : ContDiffAt ℝ ⊤ (factorCoordinates (1 : Factor s))
      ((fun x : Generator s × Generator s => matrixReconstruct (1 : Factor s) x.1 *
        matrixReconstruct (1 : Factor s) x.2) 0) := by simpa using hc
  exact hc'.comp 0 hm

theorem blockProductCoordinates_fderiv_zero (s : Pattern n)
    (v : Generator s × Generator s) :
    fderiv ℝ (blockProductCoordinates s) 0 v = v.1 + v.2 := by
  have hd₁ := reconstruct_line_hasDerivAt_zero (1 : Factor s) v.1
  have hd₂ := reconstruct_line_hasDerivAt_zero (1 : Factor s) v.2
  have hp := hasDerivAt_matrix_mul hd₁ hd₂
  have hc := (factorCoordinates_smooth_at (1 : Factor s) (1 : Mat n) (by
    change admissible ((1 : Mat n)ᵀ * 1)
    simpa using admissible_one (n := n))).differentiableAt (by simp)
  have hd : HasDerivAt
      (fun t : ℝ => matrixReconstruct (1 : Factor s) (t • v.1) *
        matrixReconstruct (1 : Factor s) (t • v.2))
      (fderiv ℝ (matrixReconstruct (1 : Factor s)) 0 (v.1 + v.2)) 0 := by
    rw [matrixReconstruct_fderiv_zero]
    simpa only [matrixReconstruct, zero_smul, reconstruct_zero, matrixReconstruct_zero, Factor.matrix_one,
      Matrix.one_mul, Matrix.mul_one, Submodule.coe_add, smul_add] using hp
  have hinv := congrArg (fun D : Generator s →L[ℝ] Generator s => D (v.1 + v.2))
    (coordinateDerivative_reconstruct (1 : Factor s) 0)
  have he : fderiv ℝ (factorCoordinates (1 : Factor s)) (1 : Mat n)
      (fderiv ℝ (matrixReconstruct (1 : Factor s)) 0 (v.1 + v.2)) = v.1 + v.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      matrixReconstruct_zero, Factor.matrix_one] using hinv
  have hactual : HasDerivAt (fun t : ℝ => blockProductCoordinates s (t • v))
      (v.1 + v.2) 0 := by
    have hh := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
    rw [he] at hh
    exact hh
  have hi := ((blockProductCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique hactual

def factorProductCoordinates (right left : Pattern n)
    (x : PairGenerator right left × PairGenerator right left) : PairGenerator right left :=
  (blockProductCoordinates left (x.1.1, x.2.1),
    blockProductCoordinates right (x.1.2, x.2.2))

theorem factorProductCoordinates_eq (x y : PairGenerator right left) :
    factorProductCoordinates right left (x, y) =
      pairCoordinates (1 : Factors right left)
        (factorLift (1 : Factors right left) x *
          factorLift (1 : Factors right left) y) := rfl

@[simp] theorem factorProductCoordinates_zero (right left : Pattern n) :
    factorProductCoordinates right left 0 = 0 := by
  change (blockProductCoordinates _ 0, blockProductCoordinates _ 0) = (0, 0)
  simp only [blockProductCoordinates_zero]

theorem blockProductCoordinates_hasFDerivAt_zero (s : Pattern n) :
    HasFDerivAt (blockProductCoordinates s)
      (ContinuousLinearMap.fst ℝ (Generator s) (Generator s) +
        ContinuousLinearMap.snd ℝ (Generator s) (Generator s)) 0 := by
  have h := ((blockProductCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  exact (blockProductCoordinates_fderiv_zero s v).symm

def reorderLeft (right left : Pattern n) :
    (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator left × Generator left) :=
  ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

def reorderRight (right left : Pattern n) :
    (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator right × Generator right) :=
  ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

theorem factorProductCoordinates_smooth_zero (right left : Pattern n) :
    ContDiffAt ℝ ⊤ (factorProductCoordinates right left) 0 := by
  have hl0 : ContDiffAt ℝ ⊤ (blockProductCoordinates left) (reorderLeft right left 0) :=
    by simpa using blockProductCoordinates_smooth_zero left
  have hr0 : ContDiffAt ℝ ⊤ (blockProductCoordinates right) (reorderRight right left 0) :=
    by simpa using blockProductCoordinates_smooth_zero right
  have hl := hl0.comp 0 (reorderLeft right left).contDiff.contDiffAt
  have hr := hr0.comp 0 (reorderRight right left).contDiff.contDiffAt
  exact hl.prodMk hr

theorem factorProductCoordinates_hasFDerivAt_zero (right left : Pattern n) :
    HasFDerivAt (factorProductCoordinates right left)
      (ContinuousLinearMap.fst ℝ (PairGenerator right left) (PairGenerator right left) +
        ContinuousLinearMap.snd ℝ (PairGenerator right left) (PairGenerator right left)) 0 := by
  have hl0 : HasFDerivAt (blockProductCoordinates left)
      (ContinuousLinearMap.fst ℝ (Generator left) (Generator left) +
        ContinuousLinearMap.snd ℝ (Generator left) (Generator left)) (reorderLeft right left 0) :=
    by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero left
  have hr0 : HasFDerivAt (blockProductCoordinates right)
      (ContinuousLinearMap.fst ℝ (Generator right) (Generator right) +
        ContinuousLinearMap.snd ℝ (Generator right) (Generator right)) (reorderRight right left 0) :=
    by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero right
  have hl := hl0.comp 0 (reorderLeft right left).hasFDerivAt
  have hr := hr0.comp 0 (reorderRight right left).hasFDerivAt
  convert hl.prodMk hr using 1 <;> first | rfl | (ext v <;> rfl)

def sliceProduct (right left : Pattern n) (P : Mat n)
    (x : HorizontalModel right left P × OrbitKernel right left P) :
    PairGenerator right left :=
  factorProductCoordinates right left (x.1.val, x.2.val)

def sliceInclusion (right left : Pattern n) (P : Mat n) :
    (HorizontalModel right left P × OrbitKernel right left P) →L[ℝ]
      (PairGenerator right left × PairGenerator right left) :=
  ((HorizontalModel right left P).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((OrbitKernel right left P).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem sliceProduct_zero (right left : Pattern n) (P : Mat n) :
    sliceProduct right left P 0 = 0 := factorProductCoordinates_zero _ _

theorem sliceProduct_smooth_zero (right left : Pattern n) (P : Mat n) :
    ContDiffAt ℝ ⊤ (sliceProduct right left P) 0 := by
  have hf : ContDiffAt ℝ ⊤ (factorProductCoordinates right left)
      (sliceInclusion right left P 0) :=
    by simpa only [map_zero] using factorProductCoordinates_smooth_zero right left
  exact ContDiffAt.comp
    (f := fun x : HorizontalModel right left P × OrbitKernel right left P =>
      sliceInclusion right left P x)
    (g := factorProductCoordinates right left) 0 hf
    (@ContinuousLinearMap.contDiff ℝ (HorizontalModel right left P × OrbitKernel right left P) (PairGenerator right left × PairGenerator right left) _ _ _ _ _ ⊤
      (sliceInclusion right left P)).contDiffAt

set_option synthInstance.maxHeartbeats 100000 in
theorem sliceProduct_hasFDerivAt_zero (right left : Pattern n)
    (P : Mat n) :
    HasFDerivAt (sliceProduct right left P)
      (horizontalKernelEquiv right left P : _ →L[ℝ] _) 0 := by
  have hf : HasFDerivAt (factorProductCoordinates right left)
      (ContinuousLinearMap.fst ℝ (PairGenerator right left) (PairGenerator right left) +
        ContinuousLinearMap.snd ℝ (PairGenerator right left) (PairGenerator right left))
      (sliceInclusion right left P 0) := by
    simpa only [map_zero] using factorProductCoordinates_hasFDerivAt_zero right left
  have hi : HasFDerivAt (sliceInclusion right left P)
      (sliceInclusion right left P) 0 :=
    @ContinuousLinearMap.hasFDerivAt ℝ _ (HorizontalModel right left P × OrbitKernel right left P) _ _ _ (PairGenerator right left × PairGenerator right left) _ _ _
      (sliceInclusion right left P) 0
  have hd := HasFDerivAt.comp
    (𝕜 := ℝ)
    (f := fun x : HorizontalModel right left P × OrbitKernel right left P =>
      sliceInclusion right left P x)
    (g := factorProductCoordinates right left) 0 hf hi
  convert hd using 1 <;> first | rfl | (ext v <;> rfl)

def sliceProductChart (right left : Pattern n) (P : Mat n) :
    OpenPartialHomeomorph (HorizontalModel right left P × OrbitKernel right left P)
      (PairGenerator right left) :=
  (sliceProduct_smooth_zero right left P).toOpenPartialHomeomorph _
    (sliceProduct_hasFDerivAt_zero right left P) (by simp)

@[simp] theorem sliceProductChart_apply (right left : Pattern n)
    (P : Mat n) (x : HorizontalModel right left P × OrbitKernel right left P) :
    sliceProductChart right left P x = sliceProduct right left P x := rfl

theorem sliceProductChart_zero_mem_source (right left : Pattern n)
    (P : Mat n) : (0 : HorizontalModel right left P × OrbitKernel right left P)
      ∈ (sliceProductChart right left P).source :=
  (sliceProduct_smooth_zero right left P).mem_toOpenPartialHomeomorph_source _ (by simp)

end GS.SharedGeometry
