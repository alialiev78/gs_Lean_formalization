module

public import GS.UnitaryNonmanifold.ScalarBridge
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The two-sphere of unitary local axes

The real three-dimensional Pauli coordinates replace the real two-dimensional
reflection coordinates. Every point of the unit sphere gives a traceless
Hermitian involution. This algebra is used in the mathematical local model;
this module does not assert the existence of a local topological chart.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryLocalModel
open GS.UnitaryGeometry GS.UnitaryNonmanifold

abbrev AxisVector := Fin 3 → ℝ

def OnSphere (u : AxisVector) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

def pauli (u : AxisVector) : CMat 2 :=
  !![(u 0 : ℂ), (u 1 : ℂ) - Complex.I * (u 2 : ℂ);
      (u 1 : ℂ) + Complex.I * (u 2 : ℂ), -(u 0 : ℂ)]

theorem continuous_pauli : Continuous pauli := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> fun_prop

theorem pauli_injective : Function.Injective pauli := by
  intro u v h
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  have hu0 : u 0 = v 0 := by simpa [pauli] using congrArg Complex.re h00
  have hu1 : u 1 = v 1 := by simpa [pauli] using congrArg Complex.re h10
  have hu2 : u 2 = v 2 := by simpa [pauli] using congrArg Complex.im h10
  funext i
  fin_cases i <;> assumption

theorem pauli_conjTranspose (u : AxisVector) : (pauli u)ᴴ = pauli u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring

theorem pauli_trace (u : AxisVector) : Matrix.trace (pauli u) = 0 := by
  simp [Matrix.trace, pauli, Fin.sum_univ_two]

theorem pauli_square (u : AxisVector) :
    pauli u * pauli u = ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 : ℝ) : ℂ) •
      (1 : CMat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pauli_unitary {u : AxisVector} (hu : OnSphere u) : Unitary (pauli u) := by
  have hs : pauli u * pauli u = 1 := by
    rw [pauli_square, hu]
    simp
  constructor <;> rw [pauli_conjTranspose] <;> exact hs

theorem pauli_neg (u : AxisVector) : pauli (-u) = -pauli u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

/-- Every traceless Hermitian two-by-two matrix has unique real Pauli coordinates. -/
theorem exists_pauli_of_hermitian_traceless (H : CMat 2)
    (hH : Hᴴ = H) (ht : Matrix.trace H = 0) :
    ∃ u : AxisVector, pauli u = H := by
  let u : AxisVector := ![(H 0 0).re, (H 1 0).re, (H 1 0).im]
  have hd := congrFun (congrFun hH 0) 0
  have ho := congrFun (congrFun hH 0) 1
  have hdiag : (H 0 0).im = 0 := by
    have hh := congrArg Complex.im hd
    simp [Matrix.conjTranspose_apply] at hh
    linarith
  have htrace : H 1 1 = -H 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using ht
  refine ⟨u, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [pauli, u, hdiag]
  · have hh : H 0 1 = star (H 1 0) := ho.symm
    change pauli u 0 1 = H 0 1
    rw [hh]
    apply Complex.ext <;> simp [pauli, u]
  · apply Complex.ext <;> simp [pauli, u]
  · change pauli u 1 1 = H 1 1
    rw [htrace]
    apply Complex.ext <;> simp [pauli, u, hdiag]

/-- A traceless Hermitian involution is exactly a point of the Pauli sphere. -/
theorem exists_sphere_pauli (H : CMat 2)
    (hH : Hᴴ = H) (ht : Matrix.trace H = 0) (hs : H * H = 1) :
    ∃ u : AxisVector, OnSphere u ∧ pauli u = H := by
  obtain ⟨u, rfl⟩ := exists_pauli_of_hermitian_traceless H hH ht
  refine ⟨u, ?_, rfl⟩
  rw [pauli_square] at hs
  have he := congrArg Complex.re (congrFun (congrFun hs 0) 0)
  change u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, Complex.ofReal_re, Complex.one_re] using he

def middleBlock (a b : ℂ) (u : AxisVector) : CMat 2 :=
  ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • pauli u

theorem middleBlock_simultaneous_swap (a b : ℂ) (u : AxisVector) :
    middleBlock b a (-u) = middleBlock a b u := by
  rw [middleBlock, pauli_neg]
  ext i j
  simp [middleBlock]
  ring

theorem middleBlock_equal (a : ℂ) (u : AxisVector) :
    middleBlock a a u = a • (1 : CMat 2) := by
  simp [middleBlock]

end GS.UnitaryLocalModel
