module

public import GS.UnitaryLocalModel.NormalizationAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# All representatives of the scalar base fibre

Every factorization of the scalar-block base point has identity anchor gauges
and both dephased central matrices equal to the reference. This is a statement
about every representative of the full fibre, not a chosen factorization.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

theorem diagTwo_norms_of_unitary {a b : ℂ} (h : GS.Unitary (diagTwo a b)) :
    ‖a‖ = 1 ∧ ‖b‖ = 1 := by
  have ha : star a * a = 1 := by
    simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
      congrFun (congrFun h.1 0) 0
  have hb : star b * b = 1 := by
    simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
      congrFun (congrFun h.1 1) 1
  have hna := congrArg norm ha
  have hnb := congrArg norm hb
  simp only [norm_mul, norm_star, norm_one] at hna hnb
  constructor <;> nlinarith [norm_nonneg a, norm_nonneg b]

theorem phase_of_norm_one {a : ℂ} (ha : ‖a‖ = 1) : phase a = a := by
  simp [phase,ha]

theorem diagTwo_div (a b c : ℂ) :
    diagTwo (a/c) (b/c) = c⁻¹ • diagTwo a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTwo,div_eq_mul_inv,mul_comm]

theorem sandwich_div_of_scalar (U V : CMat 2) (a b c : ℂ) (hc : c ≠ 0)
    (he : U*diagTwo a b*V = c • (1 : CMat 2)) :
    U*diagTwo (a/c) (b/c)*V = 1 := by
  rw [diagTwo_div, Matrix.mul_smul, Matrix.smul_mul, he, smul_smul]
  simp [hc]

theorem diagonal_unitary_of_sandwich_one (U V : CMat 2) (a b : ℂ)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (he : U*diagTwo a b*V = 1) : GS.Unitary (diagTwo a b) := by
  have hd : diagTwo a b = Uᴴ * Vᴴ := by
    calc
      _ = Uᴴ*(U*diagTwo a b*V)*Vᴴ := by
        simp only [← Matrix.mul_assoc, hU.1, Matrix.one_mul]
        rw [Matrix.mul_assoc, hV.2, Matrix.mul_one]
      _ = _ := by rw [he,Matrix.mul_one]
  rw [hd]
  exact hU.conjTranspose.mul hV.conjTranspose

theorem sandwich_phase_of_scalar (U V : CMat 2) (a b c : ℂ)
    (hU : GS.Unitary U) (hV : GS.Unitary V) (hc : c ≠ 0)
    (he : U*diagTwo a b*V = c • (1 : CMat 2)) :
    U*diagTwo (phase (a/c)) (phase (b/c))*V = 1 := by
  have hs := sandwich_div_of_scalar U V a b c hc he
  obtain ⟨ha,hb⟩ := diagTwo_norms_of_unitary
    (diagonal_unitary_of_sandwich_one U V (a/c) (b/c) hU hV hs)
  rw [phase_of_norm_one ha, phase_of_norm_one hb]
  exact hs

theorem sandwich_entries_nonzero_of_scalar (U V : CMat 2) (a b c : ℂ)
    (hU : GS.Unitary U) (hV : GS.Unitary V) (hc : c ≠ 0)
    (he : U*diagTwo a b*V = c • (1 : CMat 2)) : a ≠ 0 ∧ b ≠ 0 := by
  obtain ⟨ha,hb⟩ := diagTwo_norms_of_unitary
    (diagonal_unitary_of_sandwich_one U V (a/c) (b/c) hU hV
      (sandwich_div_of_scalar U V a b c hc he))
  constructor
  · intro h
    simp [h] at ha
  · intro h
    simp [h] at hb

variable {q : ℕ}

theorem phaseGaugeRight_as_anchors (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o j : Fin q) (hU : GS.Unitary (U o)) :
    phaseGaugeRight V Q A B o j =
      (phaseGaugeLeft U V Q A B o o)ᴴ *
        (U o * colPhaseDiagonal Q A B o j * V j) := by
  unfold phaseGaugeLeft phaseGaugeRight
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ *
        ((U o)ᴴ*U o) * colPhaseDiagonal Q A B o j * V j := by
      rw [hU.1,Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem base_fibre_phase_gauges (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o : Fin q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    (∀ i, phaseGaugeLeft U V Q A B o i = 1) ∧
      (∀ j, phaseGaugeRight V Q A B o j = 1) := by
  have hl : ∀ i, phaseGaugeLeft U V Q A B o i = 1 := by
    intro i
    exact sandwich_phase_of_scalar (U i) (V o) (A i o) (B i o) (Q i o)
      (hU i) (hV o) (hQc i) (he i o)
  refine ⟨hl,?_⟩
  intro j
  rw [phaseGaugeRight_as_anchors U V Q A B o j (hU o),hl o]
  simp only [Matrix.conjTranspose_one,Matrix.one_mul]
  exact sandwich_phase_of_scalar (U o) (V j) (A o j) (B o j) (Q o j)
    (hU o) (hV j) (hQr j) (he o j)

theorem base_fibre_anchor_nonzero (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o : Fin q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    AnchorNonzero Q A o ∧ AnchorNonzero Q B o := by
  have hc := fun i => sandwich_entries_nonzero_of_scalar (U i) (V o)
    (A i o) (B i o) (Q i o) (hU i) (hV o) (hQc i) (he i o)
  have hr := fun j => sandwich_entries_nonzero_of_scalar (U o) (V j)
    (A o j) (B o j) (Q o j) (hU o) (hV j) (hQr j) (he o j)
  exact ⟨⟨fun i => ⟨hQc i,(hc i).1⟩,fun j => ⟨hQr j,(hr j).1⟩⟩,
    ⟨fun i => ⟨hQc i,(hc i).2⟩,fun j => ⟨hQr j,(hr j).2⟩⟩⟩

theorem base_fibre_dephased_middle (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o : Fin q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    dephase Q A o = Q ∧ dephase Q B o = Q := by
  obtain ⟨hl,hr⟩ := base_fibre_phase_gauges U V Q A B o hU hV hQc hQr he
  have hd (i j : Fin q) : diagTwo (dephase Q A o i j) (dephase Q B o i j) =
      Q i j • (1 : CMat 2) := by
    have hn := phase_normalization_block U V Q A B o i j (hU i) (hV j)
    rw [hl i,hr j,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one,he i j] at hn
    calc
      _ = V o * ((V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o) *
          (V o)ᴴ := by
        simp only [← Matrix.mul_assoc,(hV o).2,Matrix.one_mul]
        rw [Matrix.mul_assoc,(hV o).2,Matrix.mul_one]
      _ = _ := by
        rw [← hn,Matrix.mul_smul,Matrix.smul_mul]
        simp only [Matrix.mul_one,(hV o).2]
  constructor <;> ext i j
  · simpa [diagTwo] using congrFun (congrFun (hd i j) 0) 0
  · simpa [diagTwo] using congrFun (congrFun (hd i j) 1) 1

end GS.UnitaryLocalModel
