module

public import GS.SharedGeometry.Connection
public import GS.Geodesics.OrbitBlock

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Orthogonal shared block geodesics in the actual matrix orbit

Complete physical blocks may be repeated arbitrarily within each layer.
Under no off-diagonal overlap, the block exponential is smooth in the actual
shared orbit, realizes every genuine initial tangent vector, has constant
physical Frobenius speed, and has zero induced covariant acceleration.

Normal acceleration in the independent family is reused only after proving
that every actual shared tangent is an independent generator direction. No
factor-lifting or tangent-surjectivity premise is supplied by the caller.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.SharedGeometry
open scoped Topology Manifold
namespace GS.SharedGeodesics
variable {n : ℕ} (right left : Pattern n) (σ : Equiv.Perm (Fin n))
local instance orthogonalNormedSpace : NormedSpace ℝ (HorizontalModel right left (permMatrix σ)) := Submodule.normedSpace _
local instance orthogonalChartedSpace : ChartedSpace (HorizontalModel right left (permMatrix σ))
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitChartedSpace right left (permMatrix σ)
local instance orthogonalIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) ⊤
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitIsManifold right left (permMatrix σ)

/-- Both physical factors obey their original sharing pattern at every time.
The second group coordinate is transposed to implement the L P R^T action. -/
def orthogonalExpFactors (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Factors right left :=
  (Factor.ofMatrix (gsExpLeft (Factor.matrix g.1) C.val t)
    (gsExpLeft_shared left.size left.label left.positive left.divides _ _
      (Factor.matrix_shared g.1) C.property t),
   Factor.ofMatrix (gsExpRight (Factor.matrix g.2)ᵀ Ω.val t)ᵀ
    (shared_factor_transpose
      (gsExpRight_shared right.size right.label right.positive right.divides _ _
        (shared_factor_transpose (Factor.matrix_shared g.2)) Ω.property t)))

def orthogonalExpCurve (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    MatrixOrbit right left (permMatrix σ) :=
  orbitMapToOrbit right left (permMatrix σ) (orthogonalExpFactors right left g C Ω t)

@[simp] theorem orthogonalExpCurve_val (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    (orthogonalExpCurve right left σ g C Ω t).val =
      gsExpCurve (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

@[simp] theorem orthogonalExpCurve_zero (g : Factors right left)
    (C : Generator left) (Ω : Generator right) :
    orthogonalExpCurve right left σ g C Ω 0 = orbitMapToOrbit right left (permMatrix σ) g := by
  apply Subtype.ext
  simp only [orthogonalExpCurve_val, gsExpCurve_zero]
  rfl

def orthogonalExpVelocity (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Mat n :=
  gsExpVelocity (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t

def orthogonalExpAcceleration (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Mat n :=
  gsExpAcceleration (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t

theorem orthogonalExpCurve_contMDiff (g : Factors right left)
    (C : Generator left) (Ω : Generator right) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) ⊤
      (orthogonalExpCurve right left σ g C Ω) := by
  apply (sharedOrbit_contMDiff_iff_contDiff right left (permMatrix σ) _).mpr
  simpa only [orthogonalExpCurve_val] using
    GS.Geodesics.gsExpCurve_contDiff (Factor.matrix g.1) (permMatrix σ)
      (Factor.matrix g.2)ᵀ C.val Ω.val

theorem orthogonalExpCurve_hasDerivAt (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    HasDerivAt (fun s => (orthogonalExpCurve right left σ g C Ω s).val)
      (orthogonalExpVelocity right left σ g C Ω t) t := by
  simpa only [orthogonalExpCurve_val, orthogonalExpVelocity] using
    gsExpCurve_hasDerivAt (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ
      C.val Ω.val (perm_orthogonal σ) t

theorem orthogonalExpVelocity_hasDerivAt (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    HasDerivAt (orthogonalExpVelocity right left σ g C Ω)
      (orthogonalExpAcceleration right left σ g C Ω t) t :=
  gsExpVelocity_hasDerivAt _ _ _ _ _ (perm_orthogonal σ) t

/-- The explicit velocity is the image of mathlib's genuine manifold derivative. -/
theorem orthogonalExpCurve_mfderiv_one (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    inclusionDifferential right left (permMatrix σ) (orthogonalExpCurve right left σ g C Ω t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left (permMatrix σ)))
        (orthogonalExpCurve right left σ g C Ω) t (1 : ℝ)) =
      orthogonalExpVelocity right left σ g C Ω t := by
  have hc := (orthogonalExpCurve_contMDiff right left σ g C Ω).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left (permMatrix σ)).mdifferentiable (by simp)
  have hh := mfderiv_comp_apply t (hi (orthogonalExpCurve right left σ g C Ω t))
    (hc t) (1 : ℝ)
  have hd : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Mat n))
      (fun s => (orthogonalExpCurve right left σ g C Ω s).val) t (1 : ℝ) =
      orthogonalExpVelocity right left σ g C Ω t := by
    rw [mfderiv_eq_fderiv]
    exact (orthogonalExpCurve_hasDerivAt right left σ g C Ω t).deriv
  exact hh.symm.trans hd

/-- Sharing only restricts the independent tangent image; it does not alter the
ambient acceleration formula. This proves normality against the FULL shared
manifold tangent image at the current time. -/
theorem orthogonalExpAcceleration_normal
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right)
    (t : ℝ) (Z : Mat n)
    (hZ : Z ∈ pointDirections right left (orthogonalExpCurve right left σ g C Ω t).val) :
    frobInner (orthogonalExpAcceleration right left σ g C Ω t) Z = 0 := by
  let L := gsExpLeft (Factor.matrix g.1) C.val t
  let R := gsExpRight (Factor.matrix g.2)ᵀ Ω.val t
  have hL := gsExpLeft_shared left.size left.label left.positive left.divides _ _
    (Factor.matrix_shared g.1) C.property t
  have hR := gsExpRight_shared right.size right.label right.positive right.divides _ _
    (shared_factor_transpose (Factor.matrix_shared g.2)) Ω.property t
  have hz : Z ∈ pointDirections right left (product2 L (permMatrix σ) R) := by
    simpa only [orthogonalExpCurve_val, gsExpCurve] using hZ
  obtain ⟨A, hA, B, hB, he⟩ :=
    (sharedDirection_iff_pointDirections (right := right) (left := left)
      (permMatrix σ) L R Z hL hR).mpr hz
  exact gsExpCurve_acceleration_normal right.block left.block σ _ _ _ _
    (GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint σ hno)
    (Factor.matrix_orthogonal g.1) (Factor.matrix_orthogonal g.2).transpose
    C.property.1 Ω.property.1 C.property.2.1 Ω.property.2.1 t Z
    ⟨A, B, hA.1, hA.2.1, hB.1, hB.2.1, he⟩

theorem orthogonalExpAcceleration_projected_zero
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right) (t : ℝ) :
    pointProjection right left (orthogonalExpCurve right left σ g C Ω t).val
      (orthogonalExpAcceleration right left σ g C Ω t) = 0 := by
  apply frobProjection_unique_normal
    (pointDirections right left (orthogonalExpCurve right left σ g C Ω t).val)
    (orthogonalExpAcceleration right left σ g C Ω t) 0 (Submodule.zero_mem _)
  intro Z hZ
  simpa only [sub_zero] using
    orthogonalExpAcceleration_normal right left σ hno g C Ω t Z hZ

theorem orthogonalExpCurve_covariantVelocity_zero
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right) (t : ℝ) :
    covariantAlong right left (permMatrix σ) (orthogonalExpCurve right left σ g C Ω)
      (orthogonalExpVelocity right left σ g C Ω) t = 0 := by
  apply inclusionDifferential_injective right left (permMatrix σ)
    (orthogonalExpCurve right left σ g C Ω t)
  rw [inclusion_covariantAlong,
    (orthogonalExpVelocity_hasDerivAt right left σ g C Ω t).deriv,
    orthogonalExpAcceleration_projected_zero right left σ hno, map_zero]

/-- Expanded physical Frobenius norms already include every repeated copy.
No assertion identifies this with the unweighted norm on unique blocks. -/
theorem orthogonalExpCurve_constant_speed
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right) (t : ℝ) :
    frobSq (orthogonalExpVelocity right left σ g C Ω t) = frobSq C.val + frobSq Ω.val :=
  gsExpCurve_constant_speed right.block left.block σ _ _ _ _
    (GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint σ hno)
    (Factor.matrix_orthogonal g.1) (Factor.matrix_orthogonal g.2).transpose
    C.property.1 Ω.property.1 C.property.2.1 Ω.property.2.1 t

/-- Every actual initial tangent vector has an all-real shared geodesic.
The coordinate pair is obtained from the proved tangent bridge, not assumed. -/
theorem exists_orthogonalExpCurve_of_tangent
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (X : MatrixOrbit right left (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) X) :
    ∃ (C : Generator left) (Ω : Generator right),
      orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω 0 = X ∧
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left (permMatrix σ)))
        (orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω)
        0 (1 : ℝ) = v ∧
      ∀ t : ℝ, covariantAlong right left (permMatrix σ)
        (orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω)
        (orthogonalExpVelocity right left σ (preferredFactor (permMatrix σ) X) C Ω) t = 0 := by
  let g := preferredFactor (permMatrix σ) X
  have hg : product2 (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ = X.val :=
    congrArg Subtype.val (preferredFactor_spec (permMatrix σ) X)
  have ht := (tangent_image_iff_sharedDirection right left (permMatrix σ) X
    (Factor.matrix g.1) (Factor.matrix g.2)ᵀ (inclusionDifferential right left (permMatrix σ) X v)
    (Factor.matrix_shared g.1) (shared_factor_transpose (Factor.matrix_shared g.2)) hg).mp ⟨v, rfl⟩
  obtain ⟨C, hC, Ω, hΩ, he⟩ := ht
  let c : Generator left := ⟨C, hC⟩
  let w : Generator right := ⟨Ω, hΩ⟩
  have hbase : orthogonalExpCurve right left σ g c w 0 = X := by
    rw [orthogonalExpCurve_zero]
    exact preferredFactor_spec (permMatrix σ) X
  refine ⟨c, w, hbase, ?_, ?_⟩
  · apply inclusionDifferential_injective right left (permMatrix σ) X
    have hd := orthogonalExpCurve_mfderiv_one right left σ g c w 0
    rw [hbase] at hd
    refine hd.trans ?_
    change gsExpVelocity _ _ _ C Ω 0 = _
    rw [gsExpVelocity_zero _ _ _ _ _ (perm_orthogonal σ)]
    exact he.symm
  · intro t
    exact orthogonalExpCurve_covariantVelocity_zero right left σ hno g c w t

end GS.SharedGeodesics
