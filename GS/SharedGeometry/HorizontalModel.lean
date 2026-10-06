module

public import GS.SharedGeometry.FactorCoordinates
public import GS.OverlapGeometry.HorizontalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Horizontal coordinates for an actual shared orbit

The complement and its continuous ambient left inverse reuse the general
finite-dimensional constructions.  The differential is the actual derivative
of the shared factor map.  The carrier P need not be orthogonal.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.OverlapGeometry (horizontalComplement complementKernelEquiv horizontalLeftInverse
  horizontalLeftInverse_apply)
namespace GS.SharedGeometry
variable {n : ℕ}

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (right left : Pattern n) (P : Mat n) :
    PairGenerator right left →L[ℝ] Mat n :=
  fderiv ℝ (orbitParam (1 : Factors right left) P) 0

abbrev OrbitKernel (right left : Pattern n) (P : Mat n) :=
  LinearMap.ker (orbitDerivative right left P).toLinearMap

abbrev HorizontalModel (right left : Pattern n) (P : Mat n) :=
  horizontalComplement (orbitDerivative right left P)

def horizontalKernelEquiv (right left : Pattern n) (P : Mat n) :
    (HorizontalModel right left P × OrbitKernel right left P) ≃L[ℝ] PairGenerator right left :=
  complementKernelEquiv (orbitDerivative right left P)

def orbitHorizontalInverse (right left : Pattern n) (P : Mat n) :
    Mat n →L[ℝ] HorizontalModel right left P :=
  horizontalLeftInverse (orbitDerivative right left P)

@[simp] theorem orbitHorizontalInverse_derivative (right left : Pattern n)
    (P : Mat n) (h : HorizontalModel right left P) :
    orbitHorizontalInverse right left P (orbitDerivative right left P h) = h :=
  horizontalLeftInverse_apply _ h

end GS.SharedGeometry
