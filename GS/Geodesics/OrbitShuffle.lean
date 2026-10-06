module

public import GS.Geodesics.OrbitBlock
public import GS.Geodesics.ShuffleCondition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix-orbit geodesics for the scalar shuffle

Here `k₁` is the number of right-layer blocks, and `b₁` is their size.
The exact original permutation is used. The inequality `b₂ ≤ k₁` is proved
sufficient, without assuming an injectivity, stabilizer or connection claim.

All statements concern the real orthogonal family with independent blocks.
No sharing constraint or special-unitary interpretation is introduced.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.Geodesics

section FixedDimension
variable (b₁ k₁ b₂ : ℕ)
local notation "rblock" => (fun i : Fin (k₁*b₁) => Fin.val i / b₁)
local notation "lblock" => (fun i : Fin (k₁*b₁) => Fin.val i / b₂)
local notation "shuffle" => scalarShuffle k₁ b₁
local instance : NormedSpace ℝ (HorizontalModel rblock lblock shuffle) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel rblock lblock shuffle)
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapChartedSpace rblock lblock shuffle
local instance : IsManifold (𝓘(ℝ, HorizontalModel rblock lblock shuffle)) ⊤
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapIsManifold rblock lblock shuffle

/-- The block exponentials stay in the original GS set for every real time. -/
theorem scalarShuffle_blockExpCurve_inA2Orth
    (g : FactorGroup rblock lblock) (C : Model lblock) (Ω : Model rblock) (t : ℝ) :
    InA2Orth b₁ b₂ (permMatrix shuffle)
      (blockExpCurve rblock lblock shuffle g C Ω t).val := by
  rw [blockExpCurve_val]
  exact gsExpCurve_inA2Orth b₁ b₂ _ _ _ _ _ g.1.property.1 g.2.property.1.transpose
    g.1.property.2 g.2.property.2.transpose C.property.1 Ω.property.1
    C.property.2 Ω.property.2 t

/-- The concrete all-time matrix-orbit curve has its actual stated first and
second derivatives, and zero induced-Frobenius covariant velocity. The only
structural inequality is the manuscript's `k₁ ≥ b₂`. -/
theorem scalarShuffle_blockExpCurve_geodesic
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁)
    (g : FactorGroup rblock lblock) (C : Model lblock) (Ω : Model rblock) (t : ℝ) :
    HasDerivAt (fun s => (blockExpCurve rblock lblock shuffle g C Ω s).val)
      (blockExpVelocity rblock lblock shuffle g C Ω t) t ∧
    HasDerivAt (blockExpVelocity rblock lblock shuffle g C Ω)
      (blockExpAcceleration rblock lblock shuffle g C Ω t) t ∧
    covariantAlong rblock lblock shuffle (blockExpCurve rblock lblock shuffle g C Ω)
      (blockExpVelocity rblock lblock shuffle g C Ω) t = 0 := by
  exact ⟨blockExpCurve_hasDerivAt rblock lblock shuffle g C Ω t,
    blockExpVelocity_hasDerivAt rblock lblock shuffle g C Ω t,
    blockExpCurve_covariantVelocity_zero rblock lblock shuffle
      (scalarShuffle_noOverlap b₁ k₁ b₂ hb₁ hb₂ hbk) g C Ω t⟩

/-- Every genuine initial tangent vector, rather than merely a supplied
generator pair, admits this explicit all-real geodesic construction. -/
theorem scalarShuffle_exists_blockExpCurve_of_tangent
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁)
    (X : MatrixOrbit rblock lblock (permMatrix shuffle))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel rblock lblock shuffle)) X) :
    ∃ (C : Model lblock) (Ω : Model rblock),
      blockExpCurve rblock lblock shuffle (preferredFactor shuffle X) C Ω 0 = X ∧
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel rblock lblock shuffle))
        (blockExpCurve rblock lblock shuffle (preferredFactor shuffle X) C Ω)
        0 (1 : ℝ) = v ∧
      ∀ t : ℝ,
        covariantAlong rblock lblock shuffle
          (blockExpCurve rblock lblock shuffle (preferredFactor shuffle X) C Ω)
          (blockExpVelocity rblock lblock shuffle (preferredFactor shuffle X) C Ω) t = 0 :=
  exists_blockExpCurve_of_tangent rblock lblock shuffle
    (scalarShuffle_noOverlap b₁ k₁ b₂ hb₁ hb₂ hbk) X v

end FixedDimension

section RegularBlocks
variable {n : ℕ} (b₁ k₁ b₂ k₂ : ℕ) (hN₁ : n = k₁*b₁)
local notation "rblock" => (fun i : Fin n => Fin.val i / b₁)
local notation "lblock" => (fun i : Fin n => Fin.val i / b₂)
local notation "shuffle" => scalarShuffleOfSize hN₁
local instance : NormedSpace ℝ (HorizontalModel rblock lblock shuffle) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel rblock lblock shuffle)
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapChartedSpace rblock lblock shuffle
local instance : IsManifold (𝓘(ℝ, HorizontalModel rblock lblock shuffle)) ⊤
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapIsManifold rblock lblock shuffle

/-- The regular-block formulation explicitly records both factorizations of
the ambient dimension. The proof also works for a final partial left block,
which is why the left divisibility hypothesis is not needed by the proof. -/
theorem regularScalarShuffle_blockExpCurve_geodesic
    (_hN₂ : n = k₂*b₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁)
    (g : FactorGroup rblock lblock) (C : Model lblock) (Ω : Model rblock) (t : ℝ) :
    HasDerivAt (fun s => (blockExpCurve rblock lblock shuffle g C Ω s).val)
      (blockExpVelocity rblock lblock shuffle g C Ω t) t ∧
    HasDerivAt (blockExpVelocity rblock lblock shuffle g C Ω)
      (blockExpAcceleration rblock lblock shuffle g C Ω t) t ∧
    covariantAlong rblock lblock shuffle (blockExpCurve rblock lblock shuffle g C Ω)
      (blockExpVelocity rblock lblock shuffle g C Ω) t = 0 := by
  exact ⟨blockExpCurve_hasDerivAt rblock lblock shuffle g C Ω t,
    blockExpVelocity_hasDerivAt rblock lblock shuffle g C Ω t,
    blockExpCurve_covariantVelocity_zero rblock lblock shuffle
      (scalarShuffleOfSize_noOverlap b₁ k₁ b₂ hN₁ hb₁ hb₂ hbk) g C Ω t⟩

end RegularBlocks
end GS.Geodesics
