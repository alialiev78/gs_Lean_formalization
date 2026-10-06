module

public import GS.Unitary.FrobeniusProjection
public import GS.Unitary.TangentMetric

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A point-only tangent projector for unitary two-factor families

The infinitesimal action space at X consists of C X + X Omega with supported
skew-Hermitian C and Omega. It uses the matrix X alone, without choosing a
factorization. Conjugation of the generators identifies this space with the
original factor differential at every supported unitary presentation. The
orthogonal projector is constructed using the real Frobenius inner product.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

def pointTangentSpace (b₁ b₂ : Fin n → ℕ) (X : CMat n) : Submodule ℝ (CMat n) :=
  tangentParamSpace b₁ b₂ 1 X 1

theorem mem_pointTangentSpace_iff (b₁ b₂ : Fin n → ℕ) (X Y : CMat n) :
    Y ∈ pointTangentSpace b₁ b₂ X ↔
      ∃ C ∈ supportedSkewSpace b₂, ∃ Ω ∈ supportedSkewSpace b₁,
        C * X + X * Ω = Y := by
  simp only [pointTangentSpace, mem_tangentParamSpace_iff, tangentParam,
    Matrix.one_mul, Matrix.mul_one]

/-- Equality is independent of the connector and of overlap between supports. -/
theorem pointTangentSpace_eq_tangentParamSpace (b₁ b₂ : Fin n → ℕ)
    (L P R : CMat n) (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R) :
    pointTangentSpace b₁ b₂ (L * P * R) = tangentParamSpace b₁ b₂ L P R := by
  ext Y
  rw [mem_pointTangentSpace_iff, mem_tangentParamSpace_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, rfl⟩
    refine ⟨Lᴴ * C * L, ?_, R * Ω * Rᴴ, ?_, ?_⟩
    · simpa using conjugate_mem_supportedSkewSpace b₂ Lᴴ C hsL.conjTranspose hC
    · exact conjugate_mem_supportedSkewSpace b₁ R Ω hsR hΩ
    · calc
        tangentParam L P R (Lᴴ * C * L) (R * Ω * Rᴴ) =
          (L * Lᴴ) * C * (L * P * R) + (L * P * R) * Ω * (Rᴴ * R) := by
            unfold tangentParam
            noncomm_ring
        _ = _ := by rw [hL.2, hR.1]; simp
  · rintro ⟨C, hC, Ω, hΩ, rfl⟩
    refine ⟨L * C * Lᴴ, conjugate_mem_supportedSkewSpace b₂ L C hsL hC,
      Rᴴ * Ω * R, ?_, ?_⟩
    · simpa using conjugate_mem_supportedSkewSpace b₁ Rᴴ Ω hsR.conjTranspose hΩ
    · calc
        (L * C * Lᴴ) * (L * P * R) + (L * P * R) * (Rᴴ * Ω * R) =
          L * C * (Lᴴ * L) * P * R + L * P * (R * Rᴴ) * Ω * R := by
            noncomm_ring
        _ = _ := by rw [hL.1, hR.2]; simp [tangentParam]

/-- Full real-Frobenius projection, including the common phase and overlap directions. -/
def pointProjection (b₁ b₂ : Fin n → ℕ) (X : CMat n) : CMat n →L[ℝ] CMat n :=
  cFrobProjection (pointTangentSpace b₁ b₂ X)

theorem pointProjection_mem (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    pointProjection b₁ b₂ X Z ∈ pointTangentSpace b₁ b₂ X :=
  cFrobProjection_mem _ _

theorem pointProjection_normal (b₁ b₂ : Fin n → ℕ) (X Z Y : CMat n)
    (hY : Y ∈ pointTangentSpace b₁ b₂ X) :
    cFrobInner (Z - pointProjection b₁ b₂ X Z) Y = 0 :=
  cFrobProjection_normal _ _ _ hY

theorem pointProjection_unique_normal (b₁ b₂ : Fin n → ℕ) (X Z Y : CMat n)
    (hY : Y ∈ pointTangentSpace b₁ b₂ X)
    (hn : ∀ W ∈ pointTangentSpace b₁ b₂ X, cFrobInner (Z - Y) W = 0) :
    pointProjection b₁ b₂ X Z = Y := cFrobProjection_unique_normal _ _ _ hY hn

theorem pointProjection_fixed_iff (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    pointProjection b₁ b₂ X Z = Z ↔ Z ∈ pointTangentSpace b₁ b₂ X :=
  cFrobProjection_fixed_iff _ _

@[simp] theorem pointProjection_idempotent (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    pointProjection b₁ b₂ X (pointProjection b₁ b₂ X Z) = pointProjection b₁ b₂ X Z :=
  cFrobProjection_idempotent _ _

theorem pointProjection_range (b₁ b₂ : Fin n → ℕ) (X : CMat n) :
    LinearMap.range (pointProjection b₁ b₂ X).toLinearMap = pointTangentSpace b₁ b₂ X := by
  ext Y
  constructor
  · rintro ⟨Z, rfl⟩
    exact pointProjection_mem b₁ b₂ X Z
  · intro hY
    exact ⟨Y, (pointProjection_fixed_iff b₁ b₂ X Y).mpr hY⟩

theorem pointProjection_self_adjoint (b₁ b₂ : Fin n → ℕ) (X Z W : CMat n) :
    cFrobInner (pointProjection b₁ b₂ X Z) W = cFrobInner Z (pointProjection b₁ b₂ X W) :=
  cFrobProjection_self_adjoint _ _ _

theorem pointProjection_pythagorean (b₁ b₂ : Fin n → ℕ) (X Z Y : CMat n)
    (hY : Y ∈ pointTangentSpace b₁ b₂ X) :
    cFrobSq (Z - Y) = cFrobSq (Z - pointProjection b₁ b₂ X Z) +
      cFrobSq (pointProjection b₁ b₂ X Z - Y) :=
  cFrobProjection_pythagorean _ _ _ hY

theorem pointProjection_minimizes (b₁ b₂ : Fin n → ℕ) (X Z Y : CMat n)
    (hY : Y ∈ pointTangentSpace b₁ b₂ X) :
    cFrobSq (Z - pointProjection b₁ b₂ X Z) ≤ cFrobSq (Z - Y) :=
  cFrobProjection_minimizes _ _ _ hY

/-- Projection computed from any supported unitary factors agrees with the point-only map. -/
theorem pointProjection_eq_factorProjection (b₁ b₂ : Fin n → ℕ)
    (L P R : CMat n) (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R) :
    pointProjection b₁ b₂ (L * P * R) = cFrobProjection (tangentParamSpace b₁ b₂ L P R) := by
  unfold pointProjection
  rw [pointTangentSpace_eq_tangentParamSpace b₁ b₂ L P R hsL hsR hL hR]

theorem factorProjection_independent (b₁ b₂ : Fin n → ℕ)
    (L P R L' P' R' : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R)
    (hsL' : CSupported b₂ L') (hsR' : CSupported b₁ R')
    (hL' : Unitary L') (hR' : Unitary R') (he : L * P * R = L' * P' * R') :
    cFrobProjection (tangentParamSpace b₁ b₂ L P R) =
      cFrobProjection (tangentParamSpace b₁ b₂ L' P' R') := by
  rw [← pointProjection_eq_factorProjection b₁ b₂ L P R hsL hsR hL hR,
    ← pointProjection_eq_factorProjection b₁ b₂ L' P' R' hsL' hsR' hL' hR', he]

end GS.UnitaryGeometry
