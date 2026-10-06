module

public import GS.GlobalGeometry.SharedAlgebra
public import GS.GlobalGeometry.SharedNormalEquations
public import GS.Continuation.FactorCurveVelocities

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual curves and feasible exponential updates with tied blocks

For full physical blocks (`0 < b` and `b ∣ n`), equal local block entries
are preserved by products, transposes and the matrix exponential.  Consequently
all shared generator directions are realized by differentiable curves of
actual tied orthogonal factors, and every differentiable factor curve has one
of these directions.

This identifies velocities of differentiable factor curves, rather than
assuming that every curve in the image admits a differentiable factor lift.
No smooth manifold assertion for an arbitrary shared image is made here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- An actual finite matrix factor with the specified physical block ties. -/
def SharedOrthogonalFactor (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  BlockDiagonal b A ∧ Orthogonal A ∧ TiedEntries b τ A

/-- Differentiation preserves equality of entries in tied physical blocks. -/
theorem tied_curve_velocity (b : ℕ) (τ : ℕ → ℕ)
    {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hd : HasDerivAt A V t) (ht : ∀ s, TiedEntries b τ (A s)) :
    TiedEntries b τ V := by
  intro i j i' j' h h' hτ hi hj
  have he : (fun s : ℝ => A s i j) = fun s => A s i' j' :=
    funext (fun s => ht s i j i' j' h h' hτ hi hj)
  have hd₁ := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
  have hd₂ := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i') j'
  rw [he] at hd₁
  exact hd₁.unique hd₂

/-- The left-trivialized generator of an actual tied orthogonal factor curve. -/
theorem shared_curve_left_generator (b : ℕ) (τ : ℕ → ℕ)
    (hb : 0 < b) (hbn : b ∣ n) {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hd : HasDerivAt A V t) (hA : ∀ s, SharedOrthogonalFactor b τ (A s)) :
    (A t)ᵀ * V ∈ sharedSkewSpace b τ := by
  have hv := supported_curve_velocity (fun i : Fin n => i.val / b) hd
    (fun s => (hA s).1)
  refine ⟨(hA t).1.transpose.mul hv,
    orthogonal_curve_left_generator_skew hd (fun s => (hA s).2.1), ?_⟩
  exact TiedEntries.mul hb hbn (hA t).1.transpose hv
    (hA t).2.2.transpose (tied_curve_velocity b τ hd (fun s => (hA s).2.2))

/-- The right-trivialized generator obeys the same concrete block ties. -/
theorem shared_curve_right_generator (b : ℕ) (τ : ℕ → ℕ)
    (hb : 0 < b) (hbn : b ∣ n) {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hd : HasDerivAt A V t) (hA : ∀ s, SharedOrthogonalFactor b τ (A s)) :
    V * (A t)ᵀ ∈ sharedSkewSpace b τ := by
  have hv := supported_curve_velocity (fun i : Fin n => i.val / b) hd
    (fun s => (hA s).1)
  refine ⟨hv.mul (hA t).1.transpose,
    orthogonal_curve_right_generator_skew hd (fun s => (hA s).2.1), ?_⟩
  exact TiedEntries.mul hb hbn hv (hA t).1.transpose
    (tied_curve_velocity b τ hd (fun s => (hA s).2.2)) (hA t).2.2.transpose

/-- The actual derivative of a tied factor product lies in the shared image. -/
theorem shared_factor_curve_velocity_in_direction (b₁ b₂ : ℕ)
    (τ₁ τ₂ : ℕ → ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n) (P : Mat n)
    {A₂ A₁ : ℝ → Mat n} {V₂ V₁ : Mat n} {t : ℝ}
    (hd₂ : HasDerivAt A₂ V₂ t) (hd₁ : HasDerivAt A₁ V₁ t)
    (hA₂ : ∀ s, SharedOrthogonalFactor b₂ τ₂ (A₂ s))
    (hA₁ : ∀ s, SharedOrthogonalFactor b₁ τ₁ (A₁ s)) :
    SharedDirection b₁ b₂ τ₁ τ₂ P (A₂ t) (A₁ t)
      (V₂ * P * A₁ t + A₂ t * P * V₁) := by
  let C := (A₂ t)ᵀ * V₂
  let Ω := V₁ * (A₁ t)ᵀ
  refine ⟨C, shared_curve_left_generator b₂ τ₂ hb₂ hbn₂ hd₂ hA₂,
    Ω, shared_curve_right_generator b₁ τ₁ hb₁ hbn₁ hd₁ hA₁, ?_⟩
  have hc : A₂ t * C = V₂ := by
    dsimp [C]
    rw [← Matrix.mul_assoc, (hA₂ t).2.1.2, Matrix.one_mul]
  have hΩ : Ω * A₁ t = V₁ := by
    dsimp [Ω]
    rw [Matrix.mul_assoc, (hA₁ t).2.1.1, Matrix.mul_one]
  rw [hc, Matrix.mul_assoc (A₂ t * P) Ω (A₁ t), hΩ]

/-- A finite exponential step preserves orthogonality, block support and
all ties, for every real step size. -/
theorem gsExpLeft_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B C : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hC : C ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpLeft B C t) := by
  refine ⟨gsExpLeft_supported B C hB.1 hC.1 t,
    gsExpLeft_orthogonal B C hB.2.1 hC.2.1 t, ?_⟩
  exact TiedEntries.mul hb hbn hB.1 (expLine_supported hC.1 t)
    hB.2.2 (expLine_tied hb hbn hC.1 hC.2.2 t)

theorem gsExpRight_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B Ω : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hΩ : Ω ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpRight B Ω t) := by
  refine ⟨gsExpRight_supported B Ω hB.1 hΩ.1 t,
    gsExpRight_orthogonal B Ω hB.2.1 hΩ.2.1 t, ?_⟩
  exact TiedEntries.mul hb hbn (expLine_supported hΩ.1 t) hB.1
    (expLine_tied hb hbn hΩ.1 hΩ.2.2 t) hB.2.2

/-- Velocities with actual differentiable tied factors and a fixed base pair. -/
def SharedFactorVelocity (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : Mat n) : Prop :=
  ∃ A₂ A₁ : ℝ → Mat n,
    A₂ 0 = L ∧ A₁ 0 = R ∧
    (∀ t, SharedOrthogonalFactor b₂ τ₂ (A₂ t)) ∧
    (∀ t, SharedOrthogonalFactor b₁ τ₁ (A₁ t)) ∧
    Differentiable ℝ A₂ ∧ Differentiable ℝ A₁ ∧
    HasDerivAt (fun t => product2 (A₂ t) P (A₁ t)) Y 0

/-- Every concrete shared generator direction is realized by the actual
matrix-exponential factor curves.  The converse is proved below. -/
theorem exists_shared_factor_curves_of_direction (b₁ b₂ : ℕ)
    (τ₁ τ₂ : ℕ → ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n) (P L R Y : Mat n)
    (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R)
    (hY : SharedDirection b₁ b₂ τ₁ τ₂ P L R Y) :
    SharedFactorVelocity b₁ b₂ τ₁ τ₂ P L R Y := by
  obtain ⟨C, hC, Ω, hΩ, rfl⟩ := hY
  refine ⟨gsExpLeft L C, gsExpRight R Ω, gsExpLeft_zero L C,
    gsExpRight_zero R Ω, gsExpLeft_shared b₂ τ₂ hb₂ hbn₂ L C hL hC,
    gsExpRight_shared b₁ τ₁ hb₁ hbn₁ R Ω hR hΩ, ?_, ?_, ?_⟩
  · intro t
    exact (gsExpLeft_hasDerivAt L C t).differentiableAt
  · intro t
    exact (gsExpRight_hasDerivAt R Ω t).differentiableAt
  · simpa only [gsExpLeft_zero, gsExpRight_zero, Matrix.mul_assoc] using
      hasDerivAt_product2 P (gsExpLeft_hasDerivAt L C 0) (gsExpRight_hasDerivAt R Ω 0)

/-- Exact equality between the shared image and actual differentiable factor
velocities.  No differentiable factorization of arbitrary image curves is
assumed or concluded. -/
theorem sharedFactorVelocity_iff_direction (b₁ b₂ : ℕ)
    (τ₁ τ₂ : ℕ → ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n) (P L R Y : Mat n)
    (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R) :
    SharedFactorVelocity b₁ b₂ τ₁ τ₂ P L R Y ↔
      SharedDirection b₁ b₂ τ₁ τ₂ P L R Y := by
  constructor
  · rintro ⟨A₂, A₁, h₂, h₁, hA₂, hA₁, hd₂, hd₁, hY⟩
    have he := hY.unique (hasDerivAt_product2 P (hd₂ 0).hasDerivAt (hd₁ 0).hasDerivAt)
    rw [he, ← h₂, ← h₁]
    exact shared_factor_curve_velocity_in_direction b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂ P
      (hd₂ 0).hasDerivAt (hd₁ 0).hasDerivAt hA₂ hA₁
  · exact exists_shared_factor_curves_of_direction b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂
      P L R Y hL hR

/-- The exact projection is the velocity of an actual feasible tied update. -/
theorem exactSharedProjection_is_factor_velocity (b₁ b₂ : ℕ)
    (τ₁ τ₂ : ℕ → ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n) (P L R Z : Mat n) (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R) :
    SharedFactorVelocity b₁ b₂ τ₁ τ₂ P L R
      (exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) :=
  exists_shared_factor_curves_of_direction b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂ P L R _ hL hR
    (exactSharedProjection_in_direction b₁ b₂ τ₁ τ₂ P L R Z hP hL.2.1 hR.2.1)

/-- The projection minimizes ambient Frobenius error over all actual
velocities of differentiable tied factor curves. -/
theorem exactSharedProjection_minimizes_factor_velocity (b₁ b₂ : ℕ)
    (τ₁ τ₂ : ℕ → ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n) (P L R Z Y : Mat n) (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R)
    (hY : SharedFactorVelocity b₁ b₂ τ₁ τ₂ P L R Y) :
    frobSq (Z - exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) ≤ frobSq (Z - Y) :=
  exactSharedProjection_minimizes b₁ b₂ τ₁ τ₂ P L R Z Y hP hL.2.1 hR.2.1
    ((sharedFactorVelocity_iff_direction b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂ P L R Y hL hR).mp hY)

end GS.GlobalGeometry
