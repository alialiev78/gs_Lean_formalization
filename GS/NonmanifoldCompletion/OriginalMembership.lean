module

public import GS.NonmanifoldCompletion.BlockRealization
public import GS.Continuation.PointedCompactImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Membership of the original exponential parametrization in the GS family

This closes an actual definition-level gap: originalF takes values in the
unchanged localFamily, with its scalar perfect shuffle and consecutive blocks.
The result holds for all skew c,z, not just on a sufficiently small compact K.
No manifold, local-coverage, or same-fibres assumption is used.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

private theorem skew_add {q : ℕ} {c z : Mat q} (hc : IsSkew c) (hz : IsSkew z) :
    IsSkew (c+z) := by
  change (c+z)ᵀ = -(c+z)
  rw [Matrix.transpose_add,hc,hz]
  abel

private theorem skew_sub {q : ℕ} {c z : Mat q} (hc : IsSkew c) (hz : IsSkew z) :
    IsSkew (c-z) := by
  change (c-z)ᵀ = -(c-z)
  rw [Matrix.transpose_sub,hc,hz]
  abel

/-- The middle q-by-q blocks are orthogonal globally in the skew coordinates. -/
theorem originalPsi_orthogonal {q : ℕ} (Q₀ H : Mat q)
    (hQ₀ : Orthogonal Q₀) (hH : IsSkew H) : Orthogonal (originalPsi Q₀ H) :=
  hQ₀.mul (matrixExp_orthogonal hH)

/-- Original f has a genuine three-factor GS representation without smallness. -/
theorem originalF_mem_localFamily {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    (ell r : Fin q → ℝ) (c z : Mat q) (u : CircleVector)
    (hc : IsSkew c) (hz : IsSkew z) (hu : OnCircle u) :
    originalF Q₀ (ell,r,c,z,u) ∈ localFamily q := by
  obtain ⟨S,hS,hdiag⟩ := exists_common_middle_diagonalizer u hu
  let A := originalPsi Q₀ (c+z)
  let B := originalPsi Q₀ (c-z)
  let U : Fin q → Mat 2 := fun i => rotation (ell i) * S
  let V : Fin q → Mat 2 := fun j => Sᵀ * rotation (r j)
  have hU : ∀ i, Orthogonal (U i) :=
    fun i => (rotation_orthogonal (ell i)).mul hS
  have hV : ∀ j, Orthogonal (V j) :=
    fun j => hS.transpose.mul (rotation_orthogonal (r j))
  have hA : Orthogonal A := originalPsi_orthogonal Q₀ (c+z) hQ₀ (skew_add hc hz)
  have hB : Orthogonal B := originalPsi_orthogonal Q₀ (c-z) hQ₀ (skew_sub hc hz)
  have he : originalF Q₀ (ell,r,c,z,u) =
      flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
    ext i j
    let x : Fin q × Fin 2 := finProdFinEquiv.symm i
    let y : Fin q × Fin 2 := finProdFinEquiv.symm j
    change (rotation (ell x.1) * middleBlock (A x.1 y.1) (B x.1 y.1) u *
      rotation (r y.1)) x.2 y.2 =
      (blockMatrix U * centralPair A B * blockMatrix V) x y
    rw [small_block_sandwich,hdiag]
    simp only [U,V,x,y,Matrix.mul_assoc]
  rw [he]
  exact block_sandwich_mem_localFamily U V A B hU hV hA hB

/-- Every point of every original K_eta maps into the original family. -/
theorem originalF_mem_of_mem_K {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    {η : ℝ} {p : OriginalParameters q} (hp : p ∈ originalK q η) :
    originalF Q₀ p ∈ localFamily q := by
  rcases p with ⟨ell,r,c,z,u⟩
  rcases hp with ⟨_hell,_hr,_hr0,hc,hz,_hc,_hz,hu⟩
  exact originalF_mem_localFamily Q₀ hQ₀ ell r c z u hc hz hu

/-- The original compact image is a subset of the actual three-factor class. -/
theorem originalF_image_subset_localFamily {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (η : ℝ) :
    originalF Q₀ '' originalK q η ⊆ localFamily q := by
  rintro M ⟨p,hp,rfl⟩
  exact originalF_mem_of_mem_K Q₀ hQ₀ hp

/-- In particular the distinguished base point belongs to the actual family. -/
theorem basePoint_mem_localFamily {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) :
    basePoint Q₀ ∈ localFamily q := by
  have h := originalF_mem_of_mem_K Q₀ hQ₀ (originalBaseParameters_mem q (le_refl (0:ℝ)))
  rwa [originalF_basePoint] at h

/-- The original f, now with its mathematically justified GS codomain. -/
def originalFIntoFamily {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (η : ℝ) :
    ↥(originalK q η) → ↥(localFamily q) :=
  fun p => ⟨originalF Q₀ p.val,originalF_mem_of_mem_K Q₀ hQ₀ p.property⟩

theorem continuous_originalFIntoFamily {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (η : ℝ) : Continuous (originalFIntoFamily Q₀ hQ₀ η) :=
  ((continuous_originalF Q₀).comp continuous_subtype_val).subtype_mk _

end GS.NonmanifoldCompletion
