module

public import GS.UnitaryManifold.OrbitDifferential
public import GS.OverlapGeometry.HorizontalModel

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
open GS GS.UnitaryGeometry GS.OverlapGeometry

namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000

variable {n : ℕ}

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    PairModel b₁ b₂ →L[ℝ] CMat n :=
  fderiv ℝ (orbitParam (1 : FactorGroup b₁ b₂) (cPermMatrix σ)) 0

abbrev OrbitKernel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  LinearMap.ker (orbitDerivative b₁ b₂ σ).toLinearMap

abbrev HorizontalModel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    Submodule ℝ (PairModel b₁ b₂) :=
  horizontalComplement (orbitDerivative b₁ b₂ σ)

def horizontalKernelEquiv (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ) ≃L[ℝ] PairModel b₁ b₂ :=
  complementKernelEquiv (orbitDerivative b₁ b₂ σ)

def orbitHorizontalInverse (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    CMat n →L[ℝ] HorizontalModel b₁ b₂ σ :=
  horizontalLeftInverse (orbitDerivative b₁ b₂ σ)

@[simp] theorem orbitHorizontalInverse_derivative (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (h : HorizontalModel b₁ b₂ σ) :
    orbitHorizontalInverse b₁ b₂ σ (orbitDerivative b₁ b₂ σ h) = h :=
  horizontalLeftInverse_apply _ h

end GS.UnitaryManifold
