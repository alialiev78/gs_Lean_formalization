module

public import GS.Continuation.ExponentialCurves
public import GS.Continuation.AmbientProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Velocities of differentiable orthogonal factor curves

We prove both directions for curves whose two factors are differentiable.
We do NOT silently assume that every differentiable curve in the image has a
local differentiable factor lift. That last assertion, or an embedded-orbit
construction, is still required to identify the image with a manifold tangent
space in the usual differential-geometric sense.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/-- Differentiating actual zero entries preserves the specified block support. -/
theorem supported_curve_velocity (block : Fin n → ℕ)
    {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hd : HasDerivAt A V t) (hs : ∀ s, Supported block (A s)) :
    Supported block V := by
  intro i j hij
  have he : (fun s : ℝ => A s i j) = fun _ : ℝ => (0 : ℝ) :=
    funext (fun s => hs s i j hij)
  have hc := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
  rw [he] at hc
  exact hc.unique (hasDerivAt_const t 0)

/-- Right-translated velocity of an actual orthogonal curve is skew. -/
theorem orthogonal_curve_right_generator_skew {A : ℝ → Mat n}
    {V : Mat n} {t : ℝ} (hd : HasDerivAt A V t)
    (ho : ∀ s, Orthogonal (A s)) : IsSkew (V * (A t)ᵀ) := by
  have hk := orthogonal_curve_left_generator_skew hd ho
  have he : A t * ((A t)ᵀ * V) * (A t)ᵀ = V * (A t)ᵀ := by
    calc
      _ = (A t * (A t)ᵀ) * V * (A t)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(ho t).2]; simp
  rw [← he]
  exact conjugate_skew (A t) ((A t)ᵀ * V) hk

/-- Necessary generator condition for a differentiable product of actual
orthogonal block-factor curves. -/
theorem factor_curve_velocity_in_direction (block₁ block₂ : Fin n → ℕ)
    (P : Mat n) {A₂ A₁ : ℝ → Mat n} {V₂ V₁ : Mat n} {t : ℝ}
    (hd₂ : HasDerivAt A₂ V₂ t) (hd₁ : HasDerivAt A₁ V₁ t)
    (hs₂ : ∀ s, Supported block₂ (A₂ s))
    (hs₁ : ∀ s, Supported block₁ (A₁ s))
    (ho₂ : ∀ s, Orthogonal (A₂ s)) (ho₁ : ∀ s, Orthogonal (A₁ s)) :
    TwoFactorDirection block₁ block₂ (A₂ t) P (A₁ t)
      (V₂ * P * A₁ t + A₂ t * P * V₁) := by
  let C := (A₂ t)ᵀ * V₂
  let Ω := V₁ * (A₁ t)ᵀ
  have hv₂ : Supported block₂ V₂ := supported_curve_velocity block₂ hd₂ hs₂
  have hv₁ : Supported block₁ V₁ := supported_curve_velocity block₁ hd₁ hs₁
  refine ⟨C, Ω, (hs₂ t).transpose.mul hv₂,
    orthogonal_curve_left_generator_skew hd₂ ho₂,
    hv₁.mul (hs₁ t).transpose, orthogonal_curve_right_generator_skew hd₁ ho₁, ?_⟩
  have hc : A₂ t * C = V₂ := by
    dsimp [C]
    rw [← Matrix.mul_assoc, (ho₂ t).2, Matrix.one_mul]
  have hΩ : Ω * A₁ t = V₁ := by
    dsimp [Ω]
    rw [Matrix.mul_assoc, (ho₁ t).1, Matrix.mul_one]
  symm
  change A₂ t * C * P * A₁ t + A₂ t * P * Ω * A₁ t = _
  rw [hc, Matrix.mul_assoc (A₂ t * P) Ω (A₁ t), hΩ]

/-- The computed derivative, not merely a candidate polynomial, lies in the
supported-skew generator image. -/
theorem deriv_factor_curve_in_direction (block₁ block₂ : Fin n → ℕ)
    (P : Mat n) {A₂ A₁ : ℝ → Mat n} {V₂ V₁ : Mat n} {t : ℝ}
    (hd₂ : HasDerivAt A₂ V₂ t) (hd₁ : HasDerivAt A₁ V₁ t)
    (hs₂ : ∀ s, Supported block₂ (A₂ s))
    (hs₁ : ∀ s, Supported block₁ (A₁ s))
    (ho₂ : ∀ s, Orthogonal (A₂ s)) (ho₁ : ∀ s, Orthogonal (A₁ s)) :
    TwoFactorDirection block₁ block₂ (A₂ t) P (A₁ t)
      (deriv (fun s => product2 (A₂ s) P (A₁ s)) t) := by
  rw [(hasDerivAt_product2 P hd₂ hd₁).deriv]
  exact factor_curve_velocity_in_direction block₁ block₂ P hd₂ hd₁ hs₂ hs₁ ho₂ ho₁

/-- Explicit sufficiency with actual differentiable factors. The converse is
`factor_curve_velocity_in_direction`; no smooth lift theorem is hidden here. -/
theorem exists_factor_curves_of_direction (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) (hP : Orthogonal P)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁)
    (hX : TwoFactorDirection block₁ block₂ B₂ P B₁ X) :
    ∃ A₂ A₁ : ℝ → Mat n,
      A₂ 0 = B₂ ∧ A₁ 0 = B₁ ∧
      (∀ t, Supported block₂ (A₂ t) ∧ Orthogonal (A₂ t)) ∧
      (∀ t, Supported block₁ (A₁ t) ∧ Orthogonal (A₁ t)) ∧
      Differentiable ℝ A₂ ∧ Differentiable ℝ A₁ ∧
      HasDerivAt (fun t => product2 (A₂ t) P (A₁ t)) X 0 := by
  obtain ⟨C, Ω, hsC, hC, hsΩ, hΩ, rfl⟩ := hX
  refine ⟨gsExpLeft B₂ C, gsExpRight B₁ Ω,
    gsExpLeft_zero B₂ C, gsExpRight_zero B₁ Ω, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨gsExpLeft_supported B₂ C hs₂ hsC t, gsExpLeft_orthogonal B₂ C h₂ hC t⟩
  · intro t
    exact ⟨gsExpRight_supported B₁ Ω hs₁ hsΩ t, gsExpRight_orthogonal B₁ Ω h₁ hΩ t⟩
  · intro t
    exact (gsExpLeft_hasDerivAt B₂ C t).differentiableAt
  · intro t
    exact (gsExpRight_hasDerivAt B₁ Ω t).differentiableAt
  · exact gsExpCurve_initial_derivative B₂ P B₁ C Ω hP

/-- Concrete geodesic equation in extrinsic projector form. The derivatives of
the concrete curve and its velocity are established in ExponentialCurves.
Calling this an intrinsic geodesic still requires the manifold/tangent bridge. -/
theorem gsExpCurve_projected_acceleration_zero (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ C Ω : Mat n)
    (hab : OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm))
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁)
    (hsC : Supported block₂ C) (hsΩ : Supported block₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    pointProjection block₁ block₂ (gsExpCurve B₂ (permMatrix σ) B₁ C Ω t)
      (gsExpAcceleration B₂ (permMatrix σ) B₁ C Ω t) = 0 := by
  apply pointProjection_zero_of_normal block₁ block₂ σ
    (gsExpLeft B₂ C t) (gsExpRight B₁ Ω t) _
    (gsExpLeft_supported B₂ C hs₂ hsC t)
    (gsExpRight_supported B₁ Ω hs₁ hsΩ t)
    (gsExpLeft_orthogonal B₂ C h₂ hC t)
    (gsExpRight_orthogonal B₁ Ω h₁ hΩ t)
  intro Y hY
  exact gsExpCurve_acceleration_normal block₁ block₂ σ B₂ B₁ C Ω
    hab h₂ h₁ hsC hsΩ hC hΩ t Y hY

end GS.Continuation
