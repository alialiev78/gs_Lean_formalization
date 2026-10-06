module

public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryNonmanifold.ScalarBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Algebra of the canonical anchor normalization

This file proves the exact dephased block formula, including the common
unitary basis and the fixed right anchor. Its row and column phase factors
are explicit. The identification with factors extracted continuously from the
matrix itself is the separate polar-normalization step.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def rowPhaseDiagonal (Q A B : CMat q) (o i : Fin q) : CMat 2 :=
  diagTwo (rowPhase Q A o i) (rowPhase Q B o i)

def colPhaseDiagonal (Q A B : CMat q) (o j : Fin q) : CMat 2 :=
  diagTwo (colPhase Q A o j) (colPhase Q B o j)

@[simp] theorem colPhaseDiagonal_anchor (Q A B : CMat q) (o : Fin q) :
    colPhaseDiagonal Q A B o o = rowPhaseDiagonal Q A B o o := rfl

theorem rowPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (rowPhaseDiagonal Q A B o i) := by
  apply diagonal_unitary_of_norm_one
  intro k
  fin_cases k
  · exact norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  · exact norm_phase (div_ne_zero (hb.1 i).2 (hb.1 i).1)

theorem colPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (colPhaseDiagonal Q A B o j) := by
  apply diagonal_unitary_of_norm_one
  intro k
  fin_cases k
  · exact norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  · exact norm_phase (div_ne_zero (hb.2 j).2 (hb.2 j).1)

def phaseGaugeLeft (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i : Fin q) : CMat 2 := U i * rowPhaseDiagonal Q A B o i * V o

def phaseGaugeRight (V : Fin q → CMat 2) (Q A B : CMat q)
    (o j : Fin q) : CMat 2 :=
  (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j

theorem phaseGaugeLeft_unitary (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (phaseGaugeLeft U V Q A B o i) :=
  ((hU i).mul (rowPhaseDiagonal_unitary ha hb i)).mul (hV o)

theorem phaseGaugeRight_unitary (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (phaseGaugeRight V Q A B o j) :=
  ((((hV o).conjTranspose).mul (rowPhaseDiagonal_unitary ha hb o).conjTranspose).mul
    (colPhaseDiagonal_unitary ha hb j)).mul (hV j)

theorem phaseGaugeRight_anchor (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : GS.Unitary (V o)) (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) :
    phaseGaugeRight V Q A B o o = 1 := by
  unfold phaseGaugeRight
  rw [colPhaseDiagonal_anchor]
  have hE := rowPhaseDiagonal_unitary ha hb o
  calc
    _ = (V o)ᴴ * ((rowPhaseDiagonal Q A B o o)ᴴ *
        rowPhaseDiagonal Q A B o o) * V o := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hE.1, Matrix.mul_one, hV.1]

theorem diagonal_dephasing_identity (Q A B : CMat q) (o i j : Fin q) :
    (rowPhaseDiagonal Q A B o i)ᴴ * diagTwo (A i j) (B i j) *
      (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o =
        diagTwo (dephase Q A o i j) (dephase Q B o i j) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rowPhaseDiagonal, colPhaseDiagonal, diagTwo, dephase,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem conjugate_sandwich_cancellation (U V S E F G D : CMat 2)
    (hU : GS.Unitary U) (hV : GS.Unitary V) :
    (U*E*S)ᴴ * (U*D*V) * (Sᴴ*Gᴴ*F*V)ᴴ = Sᴴ*(Eᴴ*D*Fᴴ*G)*S := by
  calc
    _ = Sᴴ*Eᴴ*(Uᴴ*U)*D*(V*Vᴴ)*Fᴴ*G*S := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = _ := by rw [hU.1,hV.2]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- After anchor phases are removed, every middle block uses the same basis. -/
theorem phase_normalization_block (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i j : Fin q) (hU : GS.Unitary (U i)) (hV : GS.Unitary (V j)) :
    (phaseGaugeLeft U V Q A B o i)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      (phaseGaugeRight V Q A B o j)ᴴ =
      (V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o := by
  unfold phaseGaugeLeft phaseGaugeRight
  rw [conjugate_sandwich_cancellation _ _ _ _ _ _ _ hU hV,
    diagonal_dephasing_identity]

end GS.UnitaryLocalModel
