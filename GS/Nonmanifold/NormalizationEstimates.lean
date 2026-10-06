module

public import GS.Continuation.ExponentialChart
public import GS.Continuation.ExponentialBasics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Concrete steps toward uniform coverage of the original family

These estimates formalize the normalized scalar error and the integer cocycle
in the manuscript. The existence of all normalized representatives and small
skew logarithms is still a separate obligation; this file does not assume a
local-coverage or nonmanifold theorem under another name.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.Nonmanifold

/-- The cosine estimate uses its positive branch explicitly. -/
theorem one_sub_cos_le_sin_sq (θ : ℝ) (hc : 0 ≤ Real.cos θ) :
    1 - Real.cos θ ≤ Real.sin θ^2 := by
  have hunit := Real.sin_sq_add_cos_sq θ
  have hle := Real.cos_le_one θ
  have hp : 0 ≤ Real.cos θ * (1-Real.cos θ) :=
    mul_nonneg hc (sub_nonneg.mpr hle)
  nlinarith

/-- A denominator-free bound, valid also for negative entries of Q0. -/
theorem normalized_scalar_error (a q θ ε : ℝ) (hε : 0 < ε)
    (hq : q ≠ 0) (hc : 0 ≤ Real.cos θ)
    (he : (a-q*Real.cos θ)^2 + 2*q^2*Real.sin θ^2 < ε^2) :
    2 * |q| * |a-q| < 2 * |q| * ε + ε^2 := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hs : 0 ≤ 2*q^2*Real.sin θ^2 := by positivity
  have hsmall : |a-q*Real.cos θ| < ε := by
    have ha := abs_nonneg (a-q*Real.cos θ)
    nlinarith [sq_abs (a-q*Real.cos θ)]
  have hcos := one_sub_cos_le_sin_sq θ hc
  have hdecomp : a-q = (a-q*Real.cos θ) + q*(Real.cos θ-1) := by ring
  have htriangle := abs_add_le (a-q*Real.cos θ) (q*(Real.cos θ-1))
  have hterm : |q*(Real.cos θ-1)| = |q| * (1-Real.cos θ) := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one θ))]
    ring
  rw [← hdecomp, hterm] at htriangle
  have hpre : |a-q| < ε + |q| * Real.sin θ^2 := by
    nlinarith [mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hcos)]
  have hmul : 2 * |q| * |a-q| < 2 * |q| * (ε + |q| * Real.sin θ^2) :=
    mul_lt_mul_of_pos_left hpre (by positivity)
  have hsq : |q|^2 * Real.sin θ^2 = q^2 * Real.sin θ^2 :=
    congrArg (fun x : ℝ => x * Real.sin θ^2) (sq_abs q)
  nlinarith [hsq, sq_nonneg (a-q*Real.cos θ)]

/-- Restoring the form printed in the manuscript. -/
theorem normalized_scalar_error_div (a q θ ε : ℝ) (hε : 0 < ε)
    (hq : q ≠ 0) (hc : 0 ≤ Real.cos θ)
    (he : (a-q*Real.cos θ)^2 + 2*q^2*Real.sin θ^2 < ε^2) :
    |a-q| < ε + ε^2/(2*|q|) := by
  have hh := normalized_scalar_error a q θ ε hε hq hc he
  have hd : 0 < 2*|q| := mul_pos (by norm_num) (abs_pos.mpr hq)
  have heq : ε + ε^2/(2*|q|) = (2 * |q| * ε+ε^2)/(2*|q|) := by
    field_simp [ne_of_gt hd] <;> ring
  rw [heq]
  apply (lt_div_iff₀ hd).2
  nlinarith [hh]

/-- A continuous integer-valued winding error cannot hide inside (-pi,pi). -/
theorem pi_integer_error_zero (n : ℤ) (δ : ℝ)
    (he : Real.pi*(n:ℝ)+δ=0) (hδ : |δ| < Real.pi) : n=0 := by
  have hp := Real.pi_pos
  have hbounds := abs_lt.mp hδ
  have hnlt : (n:ℝ) < 1 := by
    apply (mul_lt_mul_iff_right₀ hp).mp
    nlinarith
  have hngt : (-1:ℝ) < (n:ℝ) := by
    apply (mul_lt_mul_iff_right₀ hp).mp
    nlinarith
  have hnlt' : n < 1 := by exact_mod_cast hnlt
  have hngt' : (-1:ℤ) < n := by exact_mod_cast hngt
  omega

/-- The four small angles force the row/column integer cocycle to vanish. -/
theorem integer_angle_cocycle (n nrow ncol nbase : ℤ)
    (θ θrow θcol θbase : ℝ)
    (hθ : |θ| < Real.pi/4) (hr : |θrow| < Real.pi/4)
    (hc : |θcol| < Real.pi/4) (hb : |θbase| < Real.pi/4)
    (he : Real.pi*((n:ℝ)-(nrow:ℝ)-(ncol:ℝ)+(nbase:ℝ)) +
      θ-θrow-θcol+θbase=0) : n=nrow+ncol-nbase := by
  let δ := θ-θrow-θcol+θbase
  have hδ : |δ| < Real.pi := by
    have h1 := abs_sub θ θrow
    have h2 := abs_sub (θ-θrow) θcol
    have h3 := abs_add_le (θ-θrow-θcol) θbase
    dsimp [δ]
    linarith
  have hi : Real.pi*((n-nrow-ncol+nbase : ℤ):ℝ)+δ=0 := by
    push_cast
    dsimp [δ]
    linarith [he]
  have hz := pi_integer_error_zero (n-nrow-ncol+nbase) δ hi hδ
  omega

/-- Orthogonality of exp H forces H to be skew on a symmetric injectivity domain.
Only local injectivity is used; existence of H is not asserted here. -/
theorem skew_of_exp_orthogonal {q : ℕ} (V : Set (Mat q))
    (hinj : Set.InjOn (@matrixExp q) V) (H : Mat q)
    (ht : Hᵀ ∈ V) (hn : -H ∈ V) (hH : Orthogonal (matrixExp H)) : IsSkew H := by
  apply hinj ht hn
  rw [matrixExp_transpose]
  calc
    (matrixExp H)ᵀ = (matrixExp H)ᵀ * (matrixExp H * matrixExp (-H)) := by
      rw [matrixExp_mul_neg, Matrix.mul_one]
    _ = matrixExp (-H) := by rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]

/-- The symmetric chart restriction is built explicitly from the existing
inverse-function-theorem result, rather than passed as an extra assumption. -/
theorem exists_open_exp_skew_detection (q : ℕ) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0:Mat q) ∈ V ∧
      ∀ H ∈ V, Orthogonal (matrixExp H) → IsSkew H := by
  obtain ⟨U,hU,h0,hinj⟩ := exists_open_matrixExp_injective q
  let V : Set (Mat q) := (fun H : Mat q => Hᵀ) ⁻¹' U ∩
    (fun H : Mat q => -H) ⁻¹' U
  have hV : IsOpen V :=
    (hU.preimage (by fun_prop)).inter (hU.preimage (by fun_prop))
  refine ⟨V,hV,?_,?_⟩
  · exact ⟨by simpa using h0, by simpa using h0⟩
  · intro H hH ho
    exact skew_of_exp_orthogonal U hinj H hH.1 hH.2 ho

end GS.Nonmanifold
