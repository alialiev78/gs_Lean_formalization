module

public import GS.Unitary.TracelessProjection
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Real-linear projection formulas are continuous and real analytic in the
ambient finite-dimensional matrix topology. This does not install a Frobenius
norm on the matrix type or assert a quotient manifold construction. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.UnitaryGeometry
variable {n : ℕ}

def maskedSkewHermitianContinuousMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    CMat n →L[ℝ] CMat n := (maskedSkewHermitianMap p).toContinuousLinearMap

def maskedTracelessSkewHermitianContinuousMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    CMat n →L[ℝ] CMat n := (maskedTracelessSkewHermitianMap p).toContinuousLinearMap

theorem maskedSkewHermitian_contDiff (p : Fin n → Fin n → Prop) [DecidableRel p] :
    ContDiff ℝ ⊤ (maskedSkewHermitian p) :=
  (maskedSkewHermitianContinuousMap p).contDiff

theorem maskedTracelessSkewHermitian_contDiff (p : Fin n → Fin n → Prop) [DecidableRel p] :
    ContDiff ℝ ⊤ (maskedTracelessSkewHermitian p) :=
  (maskedTracelessSkewHermitianContinuousMap p).contDiff
end GS.UnitaryGeometry
