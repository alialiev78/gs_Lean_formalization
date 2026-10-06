module

public import GS.UnitaryLocalModel.DephasedChart
public import GS.UnitaryManifold.Dimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The dephased chart has the expected real dimension `(q - 1)^2`. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryManifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

theorem finrank_anchorCoordinates (o : Fin q) :
    Module.finrank ℝ (AnchorCoordinates o) = q + (q-1) := by
  classical
  dsimp only [AnchorCoordinates]
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
  simp only [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Rank-nullity applied to the explicitly proved onto constraint derivative. -/
theorem finrank_dephasedModel (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Module.finrank ℝ (DephasedModel Q o) = (q-1)^2 := by
  have hd := LinearMap.finrank_range_add_finrank_ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)
  rw [anchorDerivative_range Q o hQ, finrank_top,
    finrank_anchorCoordinates o, finrank_fullModel q] at hd
  have hq : q - 1 + 1 = q := by have ho := o.isLt; omega
  change Module.finrank ℝ (LinearMap.ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)) = (q-1)^2
  nlinarith

end GS.UnitaryLocalModel
