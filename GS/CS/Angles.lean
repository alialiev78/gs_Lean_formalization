module

public import GS.CS.Square
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Angle form of the complete real square cosine-sine decomposition -/

noncomputable section
open Matrix
namespace GS.CS

theorem exists_angle_of_nonneg_unit {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi / 2 ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  refine ⟨Real.arccos c, Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr hc,
    Real.cos_arccos (by linarith) (by nlinarith [sq_nonneg s]), ?_⟩
  rw [Real.sin_arccos]
  have he : 1 - c ^ 2 = s ^ 2 := by linarith
  rw [he, Real.sqrt_sq hs]

/-- Classical angle form: every real orthogonal matrix of size `2n` has
two orthogonal `n`-by-`n` blocks on each side and diagonal sine/cosine blocks,
with every angle in the closed interval from zero to pi/2. -/
theorem exists_square_cs_angles {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hQ : Orthogonal Q) :
    ∃ (U₁ U₂ V₁ V₂ : Mat n) (θ : Fin n → ℝ),
      Orthogonal U₁ ∧ Orthogonal U₂ ∧ Orthogonal V₁ ∧ Orthogonal V₂ ∧
      (∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi / 2) ∧
      Q = split U₁ U₂ * csMatrix (Real.cos ∘ θ) (Real.sin ∘ θ) * split V₁ V₂ := by
  obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hQ⟩ :=
    exists_square_cs Q hQ
  have hangle (i : Fin n) := exists_angle_of_nonneg_unit (hcs i).1
    (hcs i).2.1 (hcs i).2.2
  choose θ hθ hθ' hc hs using hangle
  refine ⟨U₁, U₂, V₁, V₂, θ, hU₁, hU₂, hV₁, hV₂, fun i => ⟨hθ i, hθ' i⟩, ?_⟩
  have hc' : Real.cos ∘ θ = c := funext hc
  have hs' : Real.sin ∘ θ = s := funext hs
  rw [hc', hs']
  exact hQ

end GS.CS
