module

public import GS.NonmanifoldObstruction.HomogeneousRetraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Spherical sections in a punctured product, not just a punctured cone

The auxiliary sphere is the explicit unit sphere in (ι -> ℝ) x ℝ².
The corresponding product has the genuine rank-one cone as its last factor.
These maps do NOT delete the full singular stratum: (x,0) with x != 0
remains in the domain.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Nonmanifold
open scoped BigOperators Topology
namespace GS.NonmanifoldObstruction

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def vectorSq (x : ι → ℝ) : ℝ := ∑ i, x i^2

theorem vectorSq_nonneg (x : ι → ℝ) : 0 ≤ vectorSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem vectorSq_eq_zero_iff (x : ι → ℝ) : vectorSq x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hb : x i^2 ≤ vectorSq x :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [h] at hb
    change x i = 0
    nlinarith
  · rintro rfl
    simp [vectorSq]

theorem vectorSq_smul (t : ℝ) (x : ι → ℝ) : vectorSq (t • x) = t^2 * vectorSq x := by
  simp only [vectorSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem continuous_vectorSq : Continuous (@vectorSq ι _) := by
  unfold vectorSq
  fun_prop

abbrev PlaneSpace (ι : Type*) := (ι → ℝ) × CircleVector
abbrev ConeSpace (ι κ : Type*) [Fintype κ] [DecidableEq κ] := (ι → ℝ) × RankCone κ

def productZero : ConeSpace ι κ := (0, coneZero)

def planeEnergy (p : PlaneSpace ι) : ℝ := vectorSq p.1 + planeSq p.2

def coneEnergy (p : ConeSpace ι κ) : ℝ := vectorSq p.1 + frobSq p.2.val

theorem planeEnergy_nonneg (p : PlaneSpace ι) : 0 ≤ planeEnergy p :=
  add_nonneg (vectorSq_nonneg _) (planeSq_nonneg _)

theorem coneEnergy_nonneg (p : ConeSpace ι κ) : 0 ≤ coneEnergy p :=
  add_nonneg (vectorSq_nonneg _) (frobSq_nonneg _)

theorem planeEnergy_eq_zero_iff (p : PlaneSpace ι) : planeEnergy p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hx : vectorSq p.1 = 0 := by
      dsimp [planeEnergy] at h
      linarith [vectorSq_nonneg p.1, planeSq_nonneg p.2]
    have hy : planeSq p.2 = 0 := by
      dsimp [planeEnergy] at h
      linarith [vectorSq_nonneg p.1, planeSq_nonneg p.2]
    exact Prod.ext ((vectorSq_eq_zero_iff _).mp hx) ((planeSq_eq_zero_iff _).mp hy)
  · rintro rfl
    simp [planeEnergy, vectorSq, planeSq]

theorem coneEnergy_eq_zero_iff (p : ConeSpace ι κ) :
    coneEnergy p = 0 ↔ p = productZero := by
  constructor
  · intro h
    have hx : vectorSq p.1 = 0 := by
      dsimp [coneEnergy] at h
      linarith [vectorSq_nonneg p.1, frobSq_nonneg p.2.val]
    have hw : frobSq p.2.val = 0 := by
      dsimp [coneEnergy] at h
      linarith [vectorSq_nonneg p.1, frobSq_nonneg p.2.val]
    exact Prod.ext ((vectorSq_eq_zero_iff _).mp hx)
      (Subtype.ext ((frobSq_eq_zero_iff _).mp hw))
  · rintro rfl
    simp [coneEnergy, productZero, coneZero, vectorSq, frobSq, frobInner]

theorem planeEnergy_smul (t : ℝ) (p : PlaneSpace ι) :
    planeEnergy (t • p) = t^2 * planeEnergy p := by
  change vectorSq (t • p.1) + planeSq (t • p.2) = _
  rw [vectorSq_smul]
  simp only [planeSq, Pi.smul_apply, smul_eq_mul, planeEnergy]
  ring

theorem continuous_planeEnergy : Continuous (@planeEnergy ι _) := by
  unfold planeEnergy vectorSq planeSq
  fun_prop

theorem continuous_coneEnergy : Continuous (@coneEnergy ι κ _ _ _) := by
  exact (continuous_vectorSq.comp continuous_fst).add
    (continuous_frobSq.comp (continuous_subtype_val.comp continuous_snd))

def productRetraction (p : ConeSpace ι κ) : PlaneSpace ι := (p.1, coneToPlane p.2)

def productSection (d : ℕ) (p : PlaneSpace ι) : ConeSpace ι (Fin (d+2)) :=
  (p.1, planeToCone d p.2)

theorem continuous_productRetraction : Continuous (@productRetraction ι κ _ _) :=
  continuous_fst.prodMk (continuous_coneToPlane.comp continuous_snd)

theorem continuous_productSection (d : ℕ) : Continuous (@productSection ι d) :=
  continuous_fst.prodMk ((continuous_planeToCone d).comp continuous_snd)

@[simp] theorem productRetraction_section (d : ℕ) (p : PlaneSpace ι) :
    productRetraction (productSection d p) = p := by
  exact Prod.ext rfl (coneToPlane_planeToCone d p.2)

@[simp] theorem productSection_zero (d : ℕ) :
    productSection d (0 : PlaneSpace ι) = productZero := by
  exact Prod.ext rfl (planeToCone_zero d)

theorem productRetraction_energy (p : ConeSpace ι κ) :
    planeEnergy (productRetraction p) = coneEnergy p := by
  change vectorSq p.1 + planeSq (coneToPlane p.2) = _
  rw [coneToPlane_sq]
  rfl

theorem productSection_energy (d : ℕ) (p : PlaneSpace ι) :
    coneEnergy (productSection d p) = planeEnergy p := by
  change vectorSq p.1 + frobSq (planeToCone d p.2).val = _
  rw [planeToCone_sq]
  rfl

abbrev PlaneSphere (ι : Type*) [Fintype ι] := {p : PlaneSpace ι // planeEnergy p = 1}
abbrev PuncturedProduct (ι κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {p : ConeSpace ι κ // p ≠ productZero}

def productRadius (p : ConeSpace ι κ) : ℝ := Real.sqrt (coneEnergy p)

theorem productRadius_sq (p : ConeSpace ι κ) : productRadius p ^ 2 = coneEnergy p :=
  Real.sq_sqrt (coneEnergy_nonneg p)

theorem productRadius_pos (p : PuncturedProduct ι κ) : 0 < productRadius p.val := by
  apply Real.sqrt_pos.mpr
  exact lt_of_le_of_ne (coneEnergy_nonneg p.val)
    (Ne.symm (fun h => p.property ((coneEnergy_eq_zero_iff _).mp h)))

theorem continuous_productRadius : Continuous (@productRadius ι κ _ _ _) :=
  Real.continuous_sqrt.comp continuous_coneEnergy

/-- Defined on the puncture at the single marked point, including points (x,0). -/
def sphereProjection (p : PuncturedProduct ι κ) : PlaneSphere ι :=
  ⟨(productRadius p.val)⁻¹ • productRetraction p.val, by
    rw [planeEnergy_smul, productRetraction_energy, ← productRadius_sq]
    have hn := ne_of_gt (productRadius_pos p)
    field_simp [hn]⟩

theorem continuous_sphereProjection : Continuous (@sphereProjection ι κ _ _ _) := by
  apply Continuous.subtype_mk
  exact ((continuous_productRadius.comp continuous_subtype_val).inv₀
    (fun p => ne_of_gt (productRadius_pos p))).smul
    (continuous_productRetraction.comp continuous_subtype_val)

/-- A sphere of arbitrary positive radius in the full cone product. -/
def smallSphereSection (d : ℕ) (t : ℝ) (ht : 0 < t) (v : PlaneSphere ι) :
    PuncturedProduct ι (Fin (d+2)) :=
  ⟨productSection d (t • v.val), by
    intro hz
    have he : coneEnergy (productSection d (t • v.val)) = 0 :=
      (coneEnergy_eq_zero_iff _).mpr hz
    rw [productSection_energy, planeEnergy_smul, v.property, mul_one] at he
    nlinarith⟩

theorem smallSphereSection_energy (d : ℕ) (t : ℝ) (ht : 0<t) (v : PlaneSphere ι) :
    coneEnergy (smallSphereSection d t ht v).val = t^2 := by
  change coneEnergy (productSection d (t • v.val)) = _
  rw [productSection_energy, planeEnergy_smul, v.property, mul_one]

theorem smallSphereSection_radius (d : ℕ) (t : ℝ) (ht : 0<t) (v : PlaneSphere ι) :
    productRadius (smallSphereSection d t ht v).val = t := by
  have hs := productRadius_sq (smallSphereSection d t ht v).val
  rw [smallSphereSection_energy] at hs
  have hp := productRadius_pos (smallSphereSection d t ht v)
  nlinarith

theorem continuous_smallSphereSection (d : ℕ) (t : ℝ) (ht : 0<t) :
    Continuous (@smallSphereSection ι _ d t ht) := by
  apply Continuous.subtype_mk
  exact (continuous_productSection d).comp (continuous_subtype_val.const_smul t)

/-- This split identity is the input for the ordinary homology obstruction. -/
theorem sphereProjection_smallSphereSection (d : ℕ) (t : ℝ) (ht : 0<t)
    (v : PlaneSphere ι) : sphereProjection (smallSphereSection d t ht v) = v := by
  apply Subtype.ext
  change (productRadius (smallSphereSection d t ht v).val)⁻¹ •
    productRetraction (productSection d (t • v.val)) = v.val
  rw [smallSphereSection_radius, productRetraction_section, smul_smul,
    inv_mul_cancel₀ (ne_of_gt ht), one_smul]

end GS.NonmanifoldObstruction
