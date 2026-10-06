module

public import GS.CayleyCharts.Differential
public import GS.LieAction.LocalSheets

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Open finite-dimensional charts on the actual non-overlap GS orbit

This combines explicit Cayley charts with the previously defined local orbit
sheets. No alternative topology is imposed on the image. Inverse charts agree
with an explicit smooth matrix formula.

The final `IsManifold` wrapper and full compatibility of ORBIT chart changes
are not asserted here. Smooth transitions proved in Transitions.lean concern
the BLOCK GROUP, not automatically the orbit. This distinction matters.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction
namespace GS.CayleyCharts
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

abbrev PairModel (block₁ block₂ : Fin n → ℕ) := Model block₂ × Model block₁

def factorDomain (block₁ block₂ : Fin n → ℕ) : Set (PairModel block₁ block₂) :=
  parameterDomain block₂ ×ˢ parameterDomain block₁

def factorSource (g : FactorGroup block₁ block₂) : Set (FactorGroup block₁ block₂) :=
  chartSource g.1 ×ˢ chartSource g.2

def factorCoordinates (g h : FactorGroup block₁ block₂) : PairModel block₁ block₂ :=
  (chartMap g.1 h.1.val, chartMap g.2 h.2.val)

theorem factorDomain_open (block₁ block₂ : Fin n → ℕ) :
    IsOpen (factorDomain block₁ block₂) :=
  (parameterDomain_open block₂).prod (parameterDomain_open block₁)

theorem factorSource_open (g : FactorGroup block₁ block₂) : IsOpen (factorSource g) :=
  (chartSource_open g.1).prod (chartSource_open g.2)

@[simp] theorem self_mem_factorSource (g : FactorGroup block₁ block₂) :
    g ∈ factorSource g := ⟨base_mem_chartSource g.1, base_mem_chartSource g.2⟩

/-- Generic homeomorphism, using only inherited product/subtype topologies. -/
def setProductHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (t : Set Y) : (s ×ˢ t) ≃ₜ (s × t) where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun xy := ⟨(xy.1.val, xy.2.val), xy.1.property, xy.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def factorChartHomeomorph (g : FactorGroup block₁ block₂) :
    factorSource g ≃ₜ factorDomain block₁ block₂ :=
  (setProductHomeomorph (chartSource g.1) (chartSource g.2)).trans
    (((blockChartHomeomorph g.1).prodCongr (blockChartHomeomorph g.2)).trans
      (setProductHomeomorph (parameterDomain block₂) (parameterDomain block₁)).symm)

@[simp] theorem factorChartHomeomorph_apply (g : FactorGroup block₁ block₂)
    (h : factorSource g) : (factorChartHomeomorph g h).val = factorCoordinates g h.val := rfl

/-- Restrict to the genuine injectivity sheet from the group-action branch. -/
def smallFactorSource (g : FactorGroup block₁ block₂) : Set (factorSource g) :=
  {h | h.val ∈ translatedSheet g}

def smallFactorTarget (g : FactorGroup block₁ block₂) :
    Set (factorDomain block₁ block₂) := factorChartHomeomorph g '' smallFactorSource g

def orbitFactorSource (g : FactorGroup block₁ block₂) : Set (FactorGroup block₁ block₂) :=
  Subtype.val '' smallFactorSource g

def orbitParameterTarget (g : FactorGroup block₁ block₂) : Set (PairModel block₁ block₂) :=
  Subtype.val '' smallFactorTarget g

theorem smallFactorSource_open (g : FactorGroup block₁ block₂) :
    IsOpen (smallFactorSource g) :=
  (translatedSheet_open g).preimage continuous_subtype_val

theorem smallFactorTarget_open (g : FactorGroup block₁ block₂) :
    IsOpen (smallFactorTarget g) :=
  (factorChartHomeomorph g).isOpenMap _ (smallFactorSource_open g)

theorem orbitFactorSource_open (g : FactorGroup block₁ block₂) :
    IsOpen (orbitFactorSource g) :=
  (factorSource_open g).isOpenMap_subtype_val _ (smallFactorSource_open g)

theorem orbitParameterTarget_open (g : FactorGroup block₁ block₂) :
    IsOpen (orbitParameterTarget g) :=
  (factorDomain_open block₁ block₂).isOpenMap_subtype_val _ (smallFactorTarget_open g)

theorem orbitFactorSource_mem_iff (g h : FactorGroup block₁ block₂) :
    h ∈ orbitFactorSource g ↔ h ∈ factorSource g ∧ h ∈ translatedSheet g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, hu⟩
  · rintro ⟨hf, hs⟩
    exact ⟨⟨h, hf⟩, hs, rfl⟩

@[simp] theorem base_mem_orbitFactorSource (g : FactorGroup block₁ block₂) :
    g ∈ orbitFactorSource g :=
  (orbitFactorSource_mem_iff g g).mpr ⟨self_mem_factorSource g, mem_translatedSheet_self g⟩

def sourceFlatten (g : FactorGroup block₁ block₂) :
    smallFactorSource g ≃ₜ orbitFactorSource g :=
  homeomorphOnOpenInjectivitySet
    (Subtype.val : factorSource g → FactorGroup block₁ block₂)
    continuous_subtype_val (factorSource_open g).isOpenMap_subtype_val
    (smallFactorSource g) (smallFactorSource_open g)
    (fun _ _ _ _ h => Subtype.ext h)

def targetFlatten (g : FactorGroup block₁ block₂) :
    smallFactorTarget g ≃ₜ orbitParameterTarget g :=
  homeomorphOnOpenInjectivitySet
    (Subtype.val : factorDomain block₁ block₂ → PairModel block₁ block₂)
    continuous_subtype_val (factorDomain_open block₁ block₂).isOpenMap_subtype_val
    (smallFactorTarget g) (smallFactorTarget_open g)
    (fun _ _ _ _ h => Subtype.ext h)

def restrictedFactorChart (g : FactorGroup block₁ block₂) :
    smallFactorSource g ≃ₜ smallFactorTarget g :=
  homeomorphOnOpenInjectivitySet (factorChartHomeomorph g)
    (factorChartHomeomorph g).continuous (factorChartHomeomorph g).isOpenMap
    (smallFactorSource g) (smallFactorSource_open g)
    (fun _ _ _ _ h => (factorChartHomeomorph g).injective h)

def smallFactorChart (g : FactorGroup block₁ block₂) :
    orbitFactorSource g ≃ₜ orbitParameterTarget g :=
  (sourceFlatten g).symm.trans ((restrictedFactorChart g).trans (targetFlatten g))

theorem smallFactorChart_apply (g : FactorGroup block₁ block₂)
    (h : orbitFactorSource g) : (smallFactorChart g h).val = factorCoordinates g h.val := by
  let u := (sourceFlatten g).symm h
  have hu : u.val.val = h.val :=
    congrArg Subtype.val ((sourceFlatten g).apply_symm_apply h)
  change factorCoordinates g u.val.val = factorCoordinates g h.val
  rw [hu]

/-- Actual open subset of the actual matrix orbit. -/
def orbitChartSource (σ : Equiv.Perm (Fin n)) (g : FactorGroup block₁ block₂) :
    Set (MatrixOrbit block₁ block₂ (permMatrix σ)) :=
  orbitMapToOrbit block₁ block₂ (permMatrix σ) '' orbitFactorSource g

theorem orbitChartSource_open (σ : Equiv.Perm (Fin n)) (g : FactorGroup block₁ block₂) :
    IsOpen (orbitChartSource σ g) :=
  orbitMapToOrbit_isOpenMap (permMatrix σ) _ (orbitFactorSource_open g)

@[simp] theorem base_mem_orbitChartSource (σ : Equiv.Perm (Fin n))
    (g : FactorGroup block₁ block₂) :
    orbitMapToOrbit block₁ block₂ (permMatrix σ) g ∈ orbitChartSource σ g :=
  ⟨g, base_mem_orbitFactorSource g, rfl⟩

def restrictedOrbitHomeomorph (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂) :
    orbitFactorSource g ≃ₜ orbitChartSource σ g :=
  homeomorphOnOpenInjectivitySet
    (orbitMapToOrbit block₁ block₂ (permMatrix σ))
    (continuous_orbitMapToOrbit (permMatrix σ))
    (orbitMapToOrbit_isOpenMap (permMatrix σ))
    (orbitFactorSource g) (orbitFactorSource_open g)
    (fun a ha b hb he => orbit_injective_translatedSheet σ hn g
      ((orbitFactorSource_mem_iff g a).mp ha).2
      ((orbitFactorSource_mem_iff g b).mp hb).2
      (congrArg Subtype.val he))

/-- The target is an OPEN subset of the unconstrained finite-dimensional
real vector space PairModel. The topology on the orbit is not changed. -/
def orbitChartHomeomorph (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂) :
    orbitChartSource σ g ≃ₜ orbitParameterTarget g :=
  (restrictedOrbitHomeomorph σ hn g).symm.trans (smallFactorChart g)

def orbitParam (g : FactorGroup block₁ block₂) (P : Mat n)
    (x : PairModel block₁ block₂) : Mat n :=
  chartInv g.1 x.1 * P * (chartInv g.2 x.2)ᵀ

theorem orbitParameterTarget_in_domain (g : FactorGroup block₁ block₂)
    {x : PairModel block₁ block₂} (hx : x ∈ orbitParameterTarget g) :
    x ∈ factorDomain block₁ block₂ := by
  rcases hx with ⟨y, hy, rfl⟩
  exact y.property

theorem orbitParam_smooth_at (g : FactorGroup block₁ block₂) (P : Mat n)
    (x : PairModel block₁ block₂) (hx : x ∈ factorDomain block₁ block₂) :
    ContDiffAt ℝ ⊤ (orbitParam g P) x :=
  smooth_mul_at
    (smooth_mul_at ((chartInv_smooth_at g.1 x.1 hx.1).comp x contDiffAt_fst)
      contDiffAt_const)
    (smooth_transpose_at ((chartInv_smooth_at g.2 x.2 hx.2).comp x contDiffAt_snd))

theorem orbitParam_smooth_on (g : FactorGroup block₁ block₂) (P : Mat n) :
    ContDiffOn ℝ ⊤ (orbitParam g P) (orbitParameterTarget g) := by
  intro x hx
  exact (orbitParam_smooth_at g P x (orbitParameterTarget_in_domain g hx)).contDiffWithinAt

theorem orbitParam_on_factorCoordinates (g h : FactorGroup block₁ block₂)
    (P : Mat n) (hh : h ∈ factorSource g) :
    orbitParam g P (factorCoordinates g h) = h • P := by
  simp only [orbitParam, factorCoordinates, chartInv_chartMap g.1 h.1 hh.1,
    chartInv_chartMap g.2 h.2 hh.2, action_apply]

/-- The inverse homeomorphism is linked to the explicit smooth parametrization;
it is not just a homeomorphism obtained by an unrelated choice. -/
theorem orbitChartHomeomorph_inverse_matrix (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (x : orbitParameterTarget g) :
    (((orbitChartHomeomorph σ hn g).symm x).val).val = orbitParam g (permMatrix σ) x.val := by
  let h := (smallFactorChart g).symm x
  have hc : factorCoordinates g h.val = x.val := by
    rw [← smallFactorChart_apply g h]
    exact congrArg Subtype.val ((smallFactorChart g).apply_symm_apply x)
  change h.val • permMatrix σ = orbitParam g (permMatrix σ) x.val
  rw [← hc]
  exact (orbitParam_on_factorCoordinates g h.val (permMatrix σ)
    ((orbitFactorSource_mem_iff g h.val).mp h.property).1).symm

/-- Every point of the actual orbit has an open finite-dimensional model chart.
This is local Euclidean structure; it is deliberately not labeled IsManifold. -/
theorem orbit_has_open_model_charts (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    ∃ U : Set (MatrixOrbit block₁ block₂ (permMatrix σ)),
      ∃ V : Set (PairModel block₁ block₂),
        IsOpen U ∧ X ∈ U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit (permMatrix σ) X
  exact ⟨orbitChartSource σ g, orbitParameterTarget g, orbitChartSource_open σ g,
    base_mem_orbitChartSource σ g, orbitParameterTarget_open g,
    ⟨orbitChartHomeomorph σ hn g⟩⟩

end GS.CayleyCharts
