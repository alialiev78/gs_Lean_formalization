module

public import GS.SharedGeometry.Factors
public import GS.GlobalGeometry.SharedDescent
public import GS.LieAction.CompactQuotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared matrix family as a compact homogeneous space

The action is L X R^T, with actual shared orthogonal factors.  Its orbit is
exactly the previously defined `InSharedA2Orth` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

instance factorsMulAction (right left : Pattern n) :
    MulAction (Factors right left) (Mat n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᵀ
  one_smul X := by
    change (1 : Mat n) * X * (1 : Mat n)ᵀ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᵀ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᵀ) *
        (Factor.matrix g.2)ᵀ
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : Mat n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᵀ := rfl

instance factorsContinuousSMul (right left : Pattern n) :
    ContinuousSMul (Factors right left) (Mat n) where
  continuous_smul := by
    change Continuous (fun p : Factors right left × Mat n =>
      Factor.matrix p.1.1 * p.2 * (Factor.matrix p.1.2)ᵀ)
    exact GS.LieAction.continuous_matrix_product
      (GS.LieAction.continuous_matrix_product
        (Factor.continuous_matrix.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (GS.LieAction.continuous_matrix_transpose
        (Factor.continuous_matrix.comp (continuous_snd.comp continuous_fst)))

def orbitMap (right left : Pattern n) (P : Mat n) : Factors right left → Mat n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern n) (P : Mat n) :=
  ↥(MulAction.orbit (Factors right left) P)

abbrev PointStabilizer (right left : Pattern n) (P : Mat n) :=
  MulAction.stabilizer (Factors right left) P

abbrev OrbitCosets (right left : Pattern n) (P : Mat n) :=
  Factors right left ⧸ PointStabilizer right left P

theorem continuous_orbitMap (P : Mat n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : Mat n) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InSharedA2Orth right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᵀ, Factor.matrix_shared g.1,
      shared_factor_transpose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᵀ (shared_factor_transpose hR)), ?_⟩
    simpa only [action_apply, Factor.matrix_ofMatrix, Matrix.transpose_transpose,
      product2] using hX.symm

theorem orbit_set_eq_inShared (P : Mat n) :
    MulAction.orbit (Factors right left) P =
      {X | InSharedA2Orth right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern n) (P : Mat n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : Mat n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : Mat n) :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem compact_matrixOrbit (P : Mat n) :
    IsCompact (MulAction.orbit (Factors right left) P) := by
  change IsCompact (Set.range (orbitMap right left P))
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_orbitMap (right := right) (left := left) P))

theorem closed_matrixOrbit (P : Mat n) :
    IsClosed (MulAction.orbit (Factors right left) P) := (compact_matrixOrbit P).isClosed

instance matrixOrbitCompactSpace (P : Mat n) : CompactSpace (MatrixOrbit right left P) :=
  isCompact_iff_compactSpace.mp (compact_matrixOrbit P)

theorem action_preserves_orthogonal (g : Factors right left) {X : Mat n}
    (hX : Orthogonal X) : Orthogonal (g • X) :=
  ((Factor.matrix_orthogonal g.1).mul hX).mul (Factor.matrix_orthogonal g.2).transpose

theorem matrixOrbit_orthogonal (P : Mat n) (hP : Orthogonal P)
    (X : MatrixOrbit right left P) : Orthogonal X.val := by
  obtain ⟨g, hg⟩ := X.property
  rw [← hg]
  exact action_preserves_orthogonal g hP

theorem action_frobInner (g : Factors right left) (X Y : Mat n) :
    frobInner (g • X) (g • Y) = frobInner X Y :=
  GS.LieAction.action_frobInner (g.1.val, g.2.val) X Y

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : Factors right left) : Mat n ≃ₗ[ℝ] Mat n :=
  GS.LieAction.actionLinearEquiv (g.1.val, g.2.val)

@[simp] theorem actionLinearEquiv_apply (g : Factors right left) (X : Mat n) :
    actionLinearEquiv g X = g • X := rfl

/-- The stabilizer is the genuine intersection of the two tied groups after
conjugation.  It need not be discrete or a coordinatewise diagonal group. -/
theorem stabilizer_iff (P : Mat n) (hP : Orthogonal P) (g : Factors right left) :
    g ∈ PointStabilizer right left P ↔
      Factor.matrix g.1 = P * Factor.matrix g.2 * Pᵀ :=
  GS.LieAction.stabilizer_iff P hP (g.1.val, g.2.val)

theorem pointStabilizer_isClosed (P : Mat n) :
    IsClosed (PointStabilizer right left P : Set (Factors right left)) :=
  isClosed_eq (continuous_orbitMap P) continuous_const

theorem orbit_fibre_iff (P : Mat n) (g h : Factors right left) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : Mat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm

def cosetEquivOrbit (P : Mat n) : OrbitCosets right left P ≃ MatrixOrbit right left P :=
  (MulAction.orbitEquivQuotientStabilizer (Factors right left) P).symm

@[simp] theorem cosetEquivOrbit_mk (P : Mat n) (g : Factors right left) :
    ((cosetEquivOrbit (right := right) (left := left) P)
      (g : OrbitCosets right left P)).val = g • P :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply (Factors right left) P g

theorem continuous_cosetEquivOrbit (P : Mat n) :
    Continuous (cosetEquivOrbit (right := right) (left := left) P) := by
  apply (QuotientGroup.isQuotientMap_mk (PointStabilizer right left P)).continuous_iff.mpr
  have he : (fun g : Factors right left =>
      cosetEquivOrbit P (g : OrbitCosets right left P)) = orbitMapToOrbit right left P := by
    funext g
    apply Subtype.ext
    exact cosetEquivOrbit_mk P g
  change Continuous (fun g : Factors right left =>
    cosetEquivOrbit P (g : OrbitCosets right left P))
  rw [he]
  exact continuous_orbitMapToOrbit P

/-- Both topologies are the pre-existing quotient/subspace topologies. -/
def quotientOrbitHomeomorph (P : Mat n) :
    OrbitCosets right left P ≃ₜ MatrixOrbit right left P := by
  let e := cosetEquivOrbit (right := right) (left := left) P
  have he : Continuous e := continuous_cosetEquivOrbit P
  have hi : Continuous e.symm := GS.continuous_descend_compact e (fun x => x) e.symm
    he continuous_id e.surjective (fun x => e.symm_apply_apply x)
  exact { toEquiv := e, continuous_toFun := he, continuous_invFun := hi }

theorem continuous_iff_after_orbitMap (P : Mat n)
    {Y : Type*} [TopologicalSpace Y] (f : MatrixOrbit right left P → Y) :
    Continuous f ↔ Continuous (f ∘ orbitMapToOrbit right left P) := by
  constructor
  · intro hf
    exact hf.comp (continuous_orbitMapToOrbit P)
  · intro hf
    exact GS.continuous_descend_compact (orbitMapToOrbit right left P)
      (f ∘ orbitMapToOrbit right left P) f (continuous_orbitMapToOrbit P) hf
      (surjective_orbitMapToOrbit P) (fun _ => rfl)

theorem closed_of_orbit_preimage_closed (P : Mat n)
    (s : Set (MatrixOrbit right left P))
    (hs : IsClosed (orbitMapToOrbit right left P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit right left P '' (orbitMapToOrbit right left P ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : Mat n) (s : Set (Factors right left)) :
    orbitMapToOrbit right left P ⁻¹' (orbitMapToOrbit right left P '' s) =
      ⋃ h : PointStabilizer right left P,
        (fun g : Factors right left => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap right left P g = orbitMap right left P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer right left P := ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change g * (g⁻¹ * h) ∈ s
    simpa only [mul_inv_cancel_left] using hh
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [mul_smul, show h.val • P = P from h.property]

/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap (P : Mat n) :
    IsOpenMap (orbitMapToOrbit right left P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit right left P ⁻¹'
      (orbitMapToOrbit right left P '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit right left P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

end GS.SharedGeometry
