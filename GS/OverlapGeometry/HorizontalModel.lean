module

public import GS.ManifoldCompletion.OrbitDifferential
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A horizontal complement for the orbit differential

All finite-dimensional choices in this file are constructed from complements
of submodules. The horizontal restriction is injective and has a continuous
linear left inverse defined on the full ambient matrix space. No hypothesis
excluding overlap is used.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.CayleyCharts GS.LieAction GS.ManifoldCompletion

namespace GS.OverlapGeometry

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def horizontalComplement (D : E →L[ℝ] F) : Submodule ℝ E :=
  Classical.choose (LinearMap.ker D.toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (horizontalComplement D) (LinearMap.ker D.toLinearMap) :=
  (Classical.choose_spec (LinearMap.ker D.toLinearMap).exists_isCompl).symm

def complementKernelEquiv (D : E →L[ℝ] F) :
    (horizontalComplement D × (LinearMap.ker D.toLinearMap)) ≃L[ℝ] E :=
  (Submodule.prodEquivOfIsCompl _ _ (horizontalComplement_isCompl D)).toContinuousLinearEquiv

@[simp] theorem complementKernelEquiv_apply (D : E →L[ℝ] F)
    (x : horizontalComplement D × (LinearMap.ker D.toLinearMap)) :
    complementKernelEquiv D x = (x.1 : E) + (x.2 : E) := rfl

def horizontalRestriction (D : E →L[ℝ] F) : horizontalComplement D →L[ℝ] F :=
  D.comp (horizontalComplement D).subtypeL

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem horizontalRestriction_apply (D : E →L[ℝ] F)
    (x : horizontalComplement D) : horizontalRestriction D x = D x := rfl

theorem horizontalRestriction_injective (D : E →L[ℝ] F) :
    Function.Injective (horizontalRestriction D) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp (horizontalComplement_isCompl D).disjoint
    ((x : E) - (y : E)) ((horizontalComplement D).sub_mem x.property y.property)
  change D ((x : E) - (y : E)) = 0
  change D (x : E) = D (y : E) at h
  rw [map_sub, h, sub_self]

def horizontalRangeComplement (D : E →L[ℝ] F) : Submodule ℝ F :=
  Classical.choose (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRangeComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (LinearMap.range (horizontalRestriction D).toLinearMap) (horizontalRangeComplement D) :=
  Classical.choose_spec (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

/-- A linear left inverse on the whole target, including normal directions. -/
def horizontalLeftInverse (D : E →L[ℝ] F) : F →L[ℝ] horizontalComplement D :=
  (LinearMap.linearProjOfIsCompl (horizontalRangeComplement D)
    (horizontalRestriction D).toLinearMap (horizontalRestriction_injective D)
    (horizontalRangeComplement_isCompl D)).toContinuousLinearMap

@[simp] theorem horizontalLeftInverse_apply (D : E →L[ℝ] F)
    (x : horizontalComplement D) : horizontalLeftInverse D (D x) = x :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ x

theorem horizontalLeftInverse_comp (D : E →L[ℝ] F) :
    (horizontalLeftInverse D).comp (horizontalRestriction D) =
      ContinuousLinearMap.id ℝ (horizontalComplement D) := by
  apply ContinuousLinearMap.ext
  intro x
  exact horizontalLeftInverse_apply D x

theorem horizontalRestriction_range (D : E →L[ℝ] F) :
    (LinearMap.range (horizontalRestriction D).toLinearMap) = (LinearMap.range D.toLinearMap) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro y ⟨x, rfl⟩
    let z := (complementKernelEquiv D).symm x
    have he : (z.1 : E) + (z.2 : E) = x :=
      (complementKernelEquiv D).apply_symm_apply x
    have hk : D (z.2 : E) = 0 := z.2.property
    refine ⟨z.1, ?_⟩
    change D (z.1 : E) = D x
    rw [← he, map_add, hk, add_zero]

end Linear

variable {n : ℕ}

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    PairModel b₁ b₂ →L[ℝ] Mat n :=
  fderiv ℝ (orbitParam (1 : FactorGroup b₁ b₂) (permMatrix σ)) 0

abbrev OrbitKernel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  LinearMap.ker (orbitDerivative b₁ b₂ σ).toLinearMap

abbrev HorizontalModel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  horizontalComplement (orbitDerivative b₁ b₂ σ)

def horizontalKernelEquiv (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ) ≃L[ℝ] PairModel b₁ b₂ :=
  complementKernelEquiv (orbitDerivative b₁ b₂ σ)

def orbitHorizontalInverse (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    Mat n →L[ℝ] HorizontalModel b₁ b₂ σ :=
  horizontalLeftInverse (orbitDerivative b₁ b₂ σ)

@[simp] theorem orbitHorizontalInverse_derivative (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (h : HorizontalModel b₁ b₂ σ) :
    orbitHorizontalInverse b₁ b₂ σ (orbitDerivative b₁ b₂ σ h) = h :=
  horizontalLeftInverse_apply _ h

end GS.OverlapGeometry
