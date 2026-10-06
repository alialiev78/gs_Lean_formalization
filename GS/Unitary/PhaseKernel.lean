module

public import GS.Unitary.TangentMetric

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The unavoidable phase kernel of two unitary factors

The imaginary scalar matrix belongs to every block-supported skew-Hermitian
space. Opposite scalar phases in the two factors cancel, independently of
off-diagonal overlap. Consequently the raw pair of unitary generators never
parametrizes its image injectively in positive dimension.
-/

noncomputable section
open Matrix

namespace GS.UnitaryGeometry
variable {n : ℕ}

/-- The generator of the common scalar unitary phase. -/
def phaseGenerator (n : ℕ) : CMat n := Complex.I • (1 : CMat n)

theorem phaseGenerator_supported (block : Fin n → ℕ) :
    CSupported block (phaseGenerator n) :=
  CSupported.smul Complex.I CSupported.one

theorem phaseGenerator_skewHermitian (n : ℕ) :
    IsSkewHermitian (phaseGenerator n) := by
  simp [phaseGenerator, IsSkewHermitian, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I]

theorem phaseGenerator_mem (block : Fin n → ℕ) :
    phaseGenerator n ∈ supportedSkewSpace block :=
  ⟨phaseGenerator_supported block, phaseGenerator_skewHermitian n⟩

theorem phaseGenerator_ne_zero (hn : 0 < n) : phaseGenerator n ≠ 0 := by
  intro h
  have he := congrArg (fun A : CMat n => A ⟨0, hn⟩ ⟨0, hn⟩) h
  simp [phaseGenerator] at he

/-- Opposite scalar phases in the two concrete supported generator spaces. -/
def phaseKernelPair (block₁ block₂ : Fin n → ℕ) :
    supportedSkewSpace block₂ × supportedSkewSpace block₁ :=
  (⟨phaseGenerator n, phaseGenerator_mem block₂⟩,
   ⟨-phaseGenerator n, (supportedSkewSpace block₁).neg_mem (phaseGenerator_mem block₁)⟩)

theorem phaseKernelPair_ne_zero (block₁ block₂ : Fin n → ℕ) (hn : 0 < n) :
    phaseKernelPair block₁ block₂ ≠ 0 := by
  intro h
  have he := congrArg
    (fun v : supportedSkewSpace block₂ × supportedSkewSpace block₁ => v.1.val) h
  exact phaseGenerator_ne_zero hn he

theorem phaseGenerator_core_zero (P : CMat n) (hP : Unitary P) :
    phaseGenerator n + P * (-phaseGenerator n) * Pᴴ = 0 := by
  simp [phaseGenerator, Matrix.mul_smul, Matrix.smul_mul, hP.2]

theorem phaseKernelPair_mem_core_ker (block₁ block₂ : Fin n → ℕ)
    (P : CMat n) (hP : Unitary P) :
    phaseKernelPair block₁ block₂ ∈ LinearMap.ker (tangentCoreMap block₁ block₂ P) :=
  phaseGenerator_core_zero P hP

/-- Every positive-dimensional unitary two-factor core has a nonzero phase
kernel, including patterns with no off-diagonal overlap. -/
theorem tangentCoreMap_not_injective (block₁ block₂ : Fin n → ℕ)
    (P : CMat n) (hP : Unitary P) (hn : 0 < n) :
    ¬Function.Injective (tangentCoreMap block₁ block₂ P) := by
  intro hi
  apply phaseKernelPair_ne_zero block₁ block₂ hn
  apply hi
  have hk := phaseKernelPair_mem_core_ker block₁ block₂ P hP
  simpa using hk

theorem phaseKernelPair_mem_param_ker (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ : CMat n) (hP : Unitary P) :
    phaseKernelPair block₁ block₂ ∈
      LinearMap.ker (tangentParamMap block₁ block₂ B₂ P B₁) := by
  change tangentParam B₂ P B₁ (phaseGenerator n) (-phaseGenerator n) = 0
  rw [tangentParam_factored _ _ _ _ _ hP, phaseGenerator_core_zero P hP]
  simp

/-- Boundary factors cannot remove the common phase ambiguity. -/
theorem tangentParamMap_not_injective (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ : CMat n) (hP : Unitary P) (hn : 0 < n) :
    ¬Function.Injective (tangentParamMap block₁ block₂ B₂ P B₁) := by
  intro hi
  apply phaseKernelPair_ne_zero block₁ block₂ hn
  apply hi
  have hk := phaseKernelPair_mem_param_ker block₁ block₂ B₂ P B₁ hP
  simpa using hk

end GS.UnitaryGeometry
