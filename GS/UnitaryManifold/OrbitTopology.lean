module

public import GS.UnitaryManifold.Action
public import GS.CompactFibres
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact homogeneous quotient and open map for supported unitary factors

The orbit has its inherited complex matrix topology, treated as a real space.
The quotient and openness statements allow arbitrary overlap of block supports.
-/

noncomputable section
open Matrix
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

abbrev PointStabilizer (block₁ block₂ : Fin n → ℕ) (P : CMat n) :=
  MulAction.stabilizer (FactorGroup block₁ block₂) P

/-- The left factor is completely determined by the right factor at the
stabilizer. Both directions use the actual unitaryity equations. -/
theorem stabilizer_iff (P : CMat n) (hP : Unitary P)
    (g : FactorGroup block₁ block₂) :
    g ∈ PointStabilizer block₁ block₂ P ↔
      g.1.val = P * g.2.val * Pᴴ := by
  change g.1.val * P * g.2.valᴴ = P ↔ _
  constructor
  · intro hg
    calc
      g.1.val = (g.1.val * P * g.2.valᴴ) * g.2.val * Pᴴ := by
        symm
        calc
          _ = g.1.val * (P * (g.2.valᴴ * g.2.val) * Pᴴ) := by
            simp only [Matrix.mul_assoc]
          _ = g.1.val := by rw [g.2.property.2.1]; simp [hP.2]
      _ = P * g.2.val * Pᴴ := by rw [hg]
  · intro hg
    rw [hg]
    calc
      (P * g.2.val * Pᴴ) * P * g.2.valᴴ =
          P * g.2.val * (Pᴴ * P) * g.2.valᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hP.1]; simp [Matrix.mul_assoc, g.2.property.2.2]

/-- Fibres are right cosets of the actual stabilizer, with the convention
(g h) • P = g • (h • P). -/
theorem orbit_fibre_iff (P : CMat n) (g h : FactorGroup block₁ block₂) :
    orbitMap block₁ block₂ P g = orbitMap block₁ block₂ P h ↔
      g⁻¹ * h ∈ PointStabilizer block₁ block₂ P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : CMat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm

/-- Right factors whose conjugates also obey the left block constraints. -/
def commonRightSubgroup (block₁ block₂ : Fin n → ℕ) (P : CMat n)
    (hP : Unitary P) : Subgroup (BlockU block₁) where
  carrier := {T | CSupported block₂ (P * T.val * Pᴴ)}
  one_mem' := by simpa [hP.2] using (CSupported.one (block := block₂))
  mul_mem' := by
    intro A B hA hB
    change CSupported block₂ (P * (A.val * B.val) * Pᴴ)
    have he : P * (A.val * B.val) * Pᴴ =
        (P * A.val * Pᴴ) * (P * B.val * Pᴴ) := by
      calc
        _ = P * A.val * (Pᴴ * P) * B.val * Pᴴ := by
          rw [hP.1]; simp [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [he]
    exact hA.mul hB
  inv_mem' := by
    intro A hA
    change CSupported block₂ (P * A.valᴴ * Pᴴ)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hA.conjTranspose

/-- Construct a stabilizer element from its right component. -/
def stabilizerFromRight (P : CMat n) (hP : Unitary P)
    (T : commonRightSubgroup block₁ block₂ P hP) :
    PointStabilizer block₁ block₂ P := by
  let g : FactorGroup block₁ block₂ :=
    (⟨P * T.val.val * Pᴴ, T.property,
       (hP.mul T.val.property.2).mul hP.conjTranspose⟩, T.val)
  exact ⟨g, (stabilizer_iff P hP g).mpr rfl⟩

/-- Recover the common right factor from a stabilizer element. -/
def rightFromStabilizer (P : CMat n) (hP : Unitary P)
    (g : PointStabilizer block₁ block₂ P) :
    commonRightSubgroup block₁ block₂ P hP := by
  refine ⟨g.val.2, ?_⟩
  change CSupported block₂ (P * g.val.2.val * Pᴴ)
  rw [← (stabilizer_iff P hP g.val).mp g.property]
  exact g.val.1.property.1

/-- Algebraic stabilizer theorem with the right factor as coordinate. -/
def stabilizerRightEquiv (P : CMat n) (hP : Unitary P) :
    PointStabilizer block₁ block₂ P ≃*
      commonRightSubgroup block₁ block₂ P hP where
  toFun := rightFromStabilizer P hP
  invFun := stabilizerFromRight P hP
  left_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact ((stabilizer_iff P hP g.val).mp g.property).symm
    · rfl
  right_inv T := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- The stabilizer is closed in the compact topological factor group. -/
theorem closed_stabilizer (P : CMat n) :
    IsClosed (PointStabilizer block₁ block₂ P : Set (FactorGroup block₁ block₂)) := by
  change IsClosed {g : FactorGroup block₁ block₂ | g • P = P}
  exact isClosed_eq (continuous_orbitMap block₁ block₂ P) continuous_const

instance stabilizerCompactSpace (P : CMat n) :
    CompactSpace (PointStabilizer block₁ block₂ P) :=
  isCompact_iff_compactSpace.mp (closed_stabilizer P).isCompact

/-- The explicit group isomorphism is also a homeomorphism for the inherited
matrix topologies. It is not asserted to be a diffeomorphism here. -/
def stabilizerRightHomeomorph (P : CMat n) (hP : Unitary P) :
    PointStabilizer block₁ block₂ P ≃ₜ
      commonRightSubgroup block₁ block₂ P hP where
  toEquiv := (stabilizerRightEquiv P hP).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      have hT : Continuous (fun T : commonRightSubgroup block₁ block₂ P hP => T.val.val) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact continuous_matrix_product
        (continuous_matrix_product continuous_const hT) continuous_const
    · exact continuous_subtype_val

/-- Conjugating by a permutation transports the labels; it does not discard
any off-block constraint. -/
theorem common_support_iff (σ : Equiv.Perm (Fin n)) (T : CMat n) :
    CSupported block₂ (cPermMatrix σ * T * (cPermMatrix σ)ᴴ) ↔
      CSupported (fun i => block₂ (σ i)) T := by
  constructor
  · intro hs i j hij
    have he := hs (σ i) (σ j) hij
    simpa only [cPerm_conjugate_apply, Equiv.symm_apply_apply] using he
  · intro hs i j hij
    rw [cPerm_conjugate_apply]
    exact hs (σ.symm i) (σ.symm j) (by simpa using hij)

theorem commonRight_mem_iff (σ : Equiv.Perm (Fin n)) (T : BlockU block₁) :
    T ∈ commonRightSubgroup block₁ block₂ (cPermMatrix σ) (cPerm_unitary σ) ↔
      CSupported (fun i => block₂ (σ i)) T.val :=
  common_support_iff σ T.val

abbrev MatrixOrbit (block₁ block₂ : Fin n → ℕ) (P : CMat n) :=
  ↥(MulAction.orbit (FactorGroup block₁ block₂) P)

abbrev OrbitCosets (block₁ block₂ : Fin n → ℕ) (P : CMat n) :=
  FactorGroup block₁ block₂ ⧸ PointStabilizer block₁ block₂ P

def orbitMapToOrbit (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    FactorGroup block₁ block₂ → MatrixOrbit block₁ block₂ P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : CMat n) :
    Continuous (orbitMapToOrbit block₁ block₂ P) :=
  (continuous_orbitMap block₁ block₂ P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : CMat n) :
    Function.Surjective (orbitMapToOrbit block₁ block₂ P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem compact_matrixOrbit (P : CMat n) :
    IsCompact (MulAction.orbit (FactorGroup block₁ block₂) P) := by
  simpa only [orbit_eq_range, Set.image_univ] using
    (isCompact_univ.image (continuous_orbitMap block₁ block₂ P))

theorem closed_matrixOrbit (P : CMat n) :
    IsClosed (MulAction.orbit (FactorGroup block₁ block₂) P) :=
  (compact_matrixOrbit P).isClosed

instance matrixOrbitCompactSpace (P : CMat n) :
    CompactSpace (MatrixOrbit block₁ block₂ P) :=
  isCompact_iff_compactSpace.mp (compact_matrixOrbit P)

/-- Reuse mathlib rather than reprove the algebraic orbit-stabilizer theorem. -/
def cosetEquivOrbit (P : CMat n) :
    OrbitCosets block₁ block₂ P ≃ MatrixOrbit block₁ block₂ P :=
  (MulAction.orbitEquivQuotientStabilizer (FactorGroup block₁ block₂) P).symm

@[simp] theorem cosetEquivOrbit_mk (P : CMat n) (g : FactorGroup block₁ block₂) :
    ((cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P)
      (g : OrbitCosets block₁ block₂ P)).val = g • P := by
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply
    (FactorGroup block₁ block₂) P g

/-- Continuity out of the quotient is proved using its actual coinduced
(topological quotient) topology, without assuming that quotient is a manifold. -/
theorem continuous_cosetEquivOrbit (P : CMat n) :
    Continuous (cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P) := by
  have hc : Continuous (fun g : FactorGroup block₁ block₂ =>
      cosetEquivOrbit P (g : OrbitCosets block₁ block₂ P)) := by
    have he : (fun g : FactorGroup block₁ block₂ =>
        cosetEquivOrbit P (g : OrbitCosets block₁ block₂ P)) =
        orbitMapToOrbit block₁ block₂ P := by
      funext g
      apply Subtype.ext
      exact cosetEquivOrbit_mk P g
    rw [he]
    exact continuous_orbitMapToOrbit P
  exact (QuotientGroup.isQuotientMap_mk
    (PointStabilizer block₁ block₂ P)).continuous_iff.mpr hc

/-- A genuine homeomorphism of the standard quotient and subspace topologies. -/
def quotientOrbitHomeomorph (P : CMat n) :
    OrbitCosets block₁ block₂ P ≃ₜ MatrixOrbit block₁ block₂ P := by
  let e := cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P
  have he : Continuous e := continuous_cosetEquivOrbit P
  have hei : Continuous e.symm :=
    GS.continuous_descend_compact e (fun x => x) e.symm he continuous_id
      e.surjective (fun x => e.symm_apply_apply x)
  exact { toEquiv := e, continuous_toFun := he, continuous_invFun := hei }

@[simp] theorem quotientOrbitHomeomorph_mk (P : CMat n)
    (g : FactorGroup block₁ block₂) :
    ((quotientOrbitHomeomorph (block₁ := block₁) (block₂ := block₂) P)
      (g : OrbitCosets block₁ block₂ P)).val = g • P :=
  cosetEquivOrbit_mk P g

/-- The homogeneous-space statement in exactly the original CInA2Unitary set. -/
def quotientA2Homeomorph (b₁ b₂ : ℕ) (P : CMat n) :
    OrbitCosets (fun i : Fin n => i.val / b₁)
                (fun i : Fin n => i.val / b₂) P ≃ₜ
      {X : CMat n // CInA2Unitary b₁ b₂ P X} :=
  (quotientOrbitHomeomorph P).trans
    (Homeomorph.setCongr (orbit_set_eq_inA2Unitary b₁ b₂ P))

theorem quotientA2Homeomorph_mk (b₁ b₂ : ℕ) (P : CMat n)
    (g : FactorGroup (fun i : Fin n => i.val / b₁)
                    (fun i : Fin n => i.val / b₂)) :
    ((quotientA2Homeomorph b₁ b₂ P)
      (g : OrbitCosets (fun i : Fin n => i.val / b₁)
                      (fun i : Fin n => i.val / b₂) P)).val =
      g.1.val * P * g.2.valᴴ := by
  exact quotientOrbitHomeomorph_mk P g

/-- The orbit map detects continuity; this is its quotient-map property stated
without depending on the name of a version-specific IsQuotientMap class. -/
theorem continuous_iff_after_orbitMap (P : CMat n)
    {Y : Type*} [TopologicalSpace Y] (f : MatrixOrbit block₁ block₂ P → Y) :
    Continuous f ↔ Continuous (f ∘ orbitMapToOrbit block₁ block₂ P) := by
  constructor
  · intro hf
    exact hf.comp (continuous_orbitMapToOrbit P)
  · intro hf
    exact GS.continuous_descend_compact (orbitMapToOrbit block₁ block₂ P)
      (f ∘ orbitMapToOrbit block₁ block₂ P) f
      (continuous_orbitMapToOrbit P) hf (surjective_orbitMapToOrbit P) (fun _ => rfl)

theorem closed_of_orbit_preimage_closed (P : CMat n)
    (s : Set (MatrixOrbit block₁ block₂ P))
    (hs : IsClosed (orbitMapToOrbit block₁ block₂ P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit block₁ block₂ P ''
      (orbitMapToOrbit block₁ block₂ P ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : CMat n) (s : Set (FactorGroup block₁ block₂)) :
    orbitMapToOrbit block₁ block₂ P ⁻¹' (orbitMapToOrbit block₁ block₂ P '' s) =
      ⋃ h : PointStabilizer block₁ block₂ P,
        (fun g : FactorGroup block₁ block₂ => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap block₁ block₂ P g = orbitMap block₁ block₂ P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer block₁ block₂ P :=
      ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
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

/-- The orbit map is open onto its matrix orbit, including when the stabilizer
has positive dimension. This is stronger than compactness of its image. -/
theorem orbitMapToOrbit_isOpenMap (P : CMat n) :
    IsOpenMap (orbitMapToOrbit block₁ block₂ P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit block₁ block₂ P ⁻¹'
      (orbitMapToOrbit block₁ block₂ P '' s)) := by
    rw [orbit_saturation]
    apply isOpen_iUnion
    intro h
    exact hs.preimage (continuous_id.mul continuous_const)
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit block₁ block₂ P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

/-- Choose factor representatives without assuming continuity of this choice. -/
def preferredFactor (σ : Equiv.Perm (Fin n))
    (X : MatrixOrbit block₁ block₂ (cPermMatrix σ)) : FactorGroup block₁ block₂ :=
  Classical.choose (surjective_orbitMapToOrbit (cPermMatrix σ) X)

theorem preferredFactor_spec (σ : Equiv.Perm (Fin n))
    (X : MatrixOrbit block₁ block₂ (cPermMatrix σ)) :
    orbitMapToOrbit block₁ block₂ (cPermMatrix σ) (preferredFactor σ X) = X :=
  Classical.choose_spec (surjective_orbitMapToOrbit (cPermMatrix σ) X)

end GS.UnitaryManifold
