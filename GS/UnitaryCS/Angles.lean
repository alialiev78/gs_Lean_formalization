module

public import GS.UnitaryCS.Square
public import GS.CS.Angles
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Angle form of the complete complex square cosine-sine decomposition -/

noncomputable section
open Matrix
namespace GS.UnitaryCS

/-- Classical angle form: every complex unitary matrix of size `2n` has
two unitary `n`-by-`n` blocks on each side and diagonal sine/cosine blocks,
with every angle in the closed interval from zero to pi/2. -/
theorem exists_square_cs_angles {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hQ : IsUnitary Q) :
    ∃ (U₁ U₂ V₁ V₂ : CMat n) (θ : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V₁ ∧ IsUnitary V₂ ∧
      (∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi / 2) ∧
      Q = split U₁ U₂ * csMatrix (Real.cos ∘ θ) (Real.sin ∘ θ) * split V₁ V₂ := by
  obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hQ⟩ :=
    exists_square_cs Q hQ
  have hangle (i : Fin n) := GS.CS.exists_angle_of_nonneg_unit (hcs i).1
    (hcs i).2.1 (hcs i).2.2
  choose θ hθ hθ' hc hs using hangle
  refine ⟨U₁, U₂, V₁, V₂, θ, hU₁, hU₂, hV₁, hV₂, fun i => ⟨hθ i, hθ' i⟩, ?_⟩
  have hc' : Real.cos ∘ θ = c := funext hc
  have hs' : Real.sin ∘ θ = s := funext hs
  rw [hc', hs']
  exact hQ

end GS.UnitaryCS
