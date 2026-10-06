module

public import GS.GlobalGeometry.CayleyRetraction
public import GS.RiemannianCompletion.Gradient
public import GS.ManifoldCompletion.OrbitSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Cayley update on the genuine non-overlap orbit and in tangent charts

We prove a general criterion: a matrix-smooth map to the factor group induces
a manifold-smooth map to the orbit. A fixed stabilizer element, held constant
on a neighbourhood, supplies the proof; no smooth preferredFactor is assumed.
The new point-only update has globally smooth tangent-coordinate expressions
with values in the actual orbit. It is also defined for actual TangentSpace
vectors and has the correct actual matrix derivative at zero.

No generic mathlib Retraction structure or smooth total tangent-bundle section
is invented. The chart criterion is explicit; a final total-space registration
is listed separately. Overlap statements in CayleyRetraction remain independent
of this file's no-overlap manifold assumptions.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.GlobalGeometry
variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [hno : Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- The target is the actual orbit manifold, not the ambient matrix space. -/
theorem smooth_orbit_of_smooth_factors {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → FactorGroup b₁ b₂)
    (hL : ContDiff ℝ ⊤ (fun x => (f x).1.val))
    (hR : ContDiff ℝ ⊤ (fun x => (f x).2.val)) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,PairModel b₁ b₂)) ⊤
      (fun x => orbitMapToOrbit b₁ b₂ (permMatrix σ) (f x)) := by
  have hc : Continuous f :=
    (hL.continuous.subtype_mk _).prodMk (hR.continuous.subtype_mk _)
  intro x
  let h := preferredFactor σ (orbitMapToOrbit b₁ b₂ (permMatrix σ) (f x))
  let s : FactorGroup b₁ b₂ := (f x)⁻¹*h
  have hs : s ∈ PointStabilizer b₁ b₂ (permMatrix σ) := by
    apply (orbit_fibre_iff (permMatrix σ) (f x) h).mp
    exact congrArg Subtype.val
      (preferredFactor_spec σ (orbitMapToOrbit b₁ b₂ (permMatrix σ) (f x))).symm
  have hfix : s • permMatrix σ = permMatrix σ := hs
  have heq : f x*s=h := by simp [s]
  have hnear : ∀ᶠ y in 𝓝 x, f y*s ∈ orbitFactorSource h :=
    (hc.mul continuous_const).continuousAt.eventually
      ((orbitFactorSource_open h).mem_nhds (by
        change f x * s ∈ orbitFactorSource h
        rw [heq]; exact base_mem_orbitFactorSource h))
  have hcoords : (fun y => orbitCoordinates σ hno.out h
      (orbitMapToOrbit b₁ b₂ (permMatrix σ) (f y))) =ᶠ[𝓝 x]
      (fun y => factorCoordinates h (f y*s)) := by
    filter_upwards [hnear] with y hy
    have horbit : orbitMapToOrbit b₁ b₂ (permMatrix σ) (f y*s) =
        orbitMapToOrbit b₁ b₂ (permMatrix σ) (f y) := by
      apply Subtype.ext
      change (f y*s) • permMatrix σ = f y • permMatrix σ
      rw [mul_smul, hfix]
    rw [← horbit, orbitCoordinates_on_factors σ hno.out h _ hy]
  have hdom : f x*s ∈ factorSource h :=
    ((orbitFactorSource_mem_iff h (f x*s)).mp (by
      rw [heq]; exact base_mem_orbitFactorSource h)).1
  have hl : ContDiffAt ℝ ⊤ (fun y => chartMap h.1 ((f y).1.val*s.1.val)) x :=
    ContDiffAt.comp (f := fun y => (f y).1.val*s.1.val) (g := chartMap h.1) x
      (chartMap_smooth_at h.1 _ hdom.1)
      (smooth_mul_at hL.contDiffAt contDiffAt_const)
  have hr : ContDiffAt ℝ ⊤ (fun y => chartMap h.2 ((f y).2.val*s.2.val)) x :=
    ContDiffAt.comp (f := fun y => (f y).2.val*s.2.val) (g := chartMap h.2) x
      (chartMap_smooth_at h.2 _ hdom.2)
      (smooth_mul_at hR.contDiffAt contDiffAt_const)
  have hd : ContDiffAt ℝ ⊤ (fun y => factorCoordinates h (f y*s)) x := by
    simpa only [factorCoordinates, Prod.fst_mul, Prod.snd_mul, blockO_mul_val] using hl.prodMk hr
  rw [contMDiffAt_iff_target]
  refine ⟨((continuous_orbitMapToOrbit (permMatrix σ)).comp hc).continuousAt, ?_⟩
  change ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,PairModel b₁ b₂)) ⊤
    (fun y => orbitCoordinates σ hno.out h
      (orbitMapToOrbit b₁ b₂ (permMatrix σ) (f y))) x
  exact (contMDiffAt_iff_contDiffAt).mpr (hd.congr_of_eventuallyEq hcoords)

/-- All denominators are invertible because the arguments are skew. -/
def pointStepFactors (g : FactorGroup b₁ b₂) (X Z : Mat n) (t : ℝ) :
    FactorGroup b₁ b₂ :=
  (⟨unitCayley (t•balancedLeft b₁ b₂ X Z),
      unitCayley_supported _ _ ((balancedLeft_supported _ _ _ _).smul t)
        (isSkew_smul t (balancedLeft_skew _ _ _ _)),
      unitCayley_orthogonal _ (isSkew_smul t (balancedLeft_skew _ _ _ _))⟩ * g.1,
   ⟨(unitCayley (t•balancedRight b₁ b₂ X Z))ᵀ,
      (unitCayley_supported _ _ ((balancedRight_supported _ _ _ _).smul t)
        (isSkew_smul t (balancedRight_skew _ _ _ _))).transpose,
      (unitCayley_orthogonal _ (isSkew_smul t (balancedRight_skew _ _ _ _))).transpose⟩ * g.2)

theorem pointStepFactors_value (g : FactorGroup b₁ b₂) (X Z : Mat n) (t : ℝ)
    (hg : g • permMatrix σ = X) :
    pointStepFactors g X Z t • permMatrix σ = pointCayleyStep b₁ b₂ X Z t := by
  let U := unitCayley (t • balancedLeft b₁ b₂ X Z)
  let V := unitCayley (t • balancedRight b₁ b₂ X Z)
  change (U * g.1.val) * permMatrix σ * (Vᵀ * g.2.val)ᵀ = U * X * V
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (U * g.1.val) * permMatrix σ * (g.2.valᵀ * V) =
        U * (g.1.val * permMatrix σ * g.2.valᵀ) * V := by simp only [Matrix.mul_assoc]
    _ = U * X * V := by rw [show g.1.val * permMatrix σ * g.2.valᵀ = X from hg]

/-- A globally defined curve into the original orbit, indexed by an actual
TangentSpace vector. The factor choice is used only to certify membership. -/
def cayleyTangentStep (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ)
    (pointStepFactors (preferredFactor σ X) X.val (inclusionDifferential σ X v) t)

@[simp] theorem cayleyTangentStep_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) (t : ℝ) :
    (cayleyTangentStep σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential σ X v) t :=
  pointStepFactors_value σ _ _ _ t (congrArg Subtype.val (preferredFactor_spec σ X))

@[simp] theorem cayleyTangentStep_at_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) : cayleyTangentStep σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem cayleyTangentStep_zero_vector (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (t : ℝ) : cayleyTangentStep σ X 0 t=X := by
  apply Subtype.ext
  simp

theorem cayleyTangentStep_derivative (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :
    HasDerivAt (fun t => (cayleyTangentStep σ X v t).val)
      (inclusionDifferential σ X v) 0 := by
  have hd := pointCayleyStep_derivative b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ
    (inclusionDifferential σ X v)
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  dsimp only at hd
  have hfix : pointProjection b₁ b₂ X.val (inclusionDifferential σ X v) =
      inclusionDifferential σ X v :=
    (pointProjection_fixed_iff_tangent_image σ X _).mpr ⟨v,rfl⟩
  rw [preferredFactor_product σ X, hfix] at hd
  simpa only [cayleyTangentStep_val] using hd

/-- Standard tangent-chart input: base coordinates x and coordinate velocity v. -/
def chartStepFactors (g : FactorGroup b₁ b₂)
    (p : (PairModel b₁ b₂ × PairModel b₁ b₂) × ℝ) : FactorGroup b₁ b₂ :=
  pointStepFactors (factorLift g p.1.1) (orbitParam g (permMatrix σ) p.1.1)
    (fderiv ℝ (orbitParam g (permMatrix σ)) p.1.1 p.1.2) p.2

def chartCayleyUpdate (g : FactorGroup b₁ b₂)
    (p : (PairModel b₁ b₂ × PairModel b₁ b₂) × ℝ) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ) (chartStepFactors σ g p)

theorem chartCayleyUpdate_val (g : FactorGroup b₁ b₂)
    (p : (PairModel b₁ b₂ × PairModel b₁ b₂) × ℝ) :
    (chartCayleyUpdate σ g p).val =
      pointCayleyStep b₁ b₂ (orbitParam g (permMatrix σ) p.1.1)
        (fderiv ℝ (orbitParam g (permMatrix σ)) p.1.1 p.1.2) p.2 :=
  pointStepFactors_value σ (factorLift g p.1.1) (orbitParam g (permMatrix σ) p.1.1)
    (fderiv ℝ (orbitParam g (permMatrix σ)) p.1.1 p.1.2) p.2
    (factorLift_action g (permMatrix σ) p.1.1)

/-- Joint manifold smoothness in every tangent-coordinate parametrization,
with arbitrary real step length. This is stronger than ambient smoothness. -/
theorem chartCayleyUpdate_smooth (g : FactorGroup b₁ b₂) :
    ContMDiff (𝓘(ℝ,(PairModel b₁ b₂ × PairModel b₁ b₂) × ℝ))
      (𝓘(ℝ,PairModel b₁ b₂)) ⊤ (chartCayleyUpdate σ g) := by
  let E := (PairModel b₁ b₂ × PairModel b₁ b₂) × ℝ
  let X : E → Mat n := fun p => orbitParam g (permMatrix σ) p.1.1
  let Z : E → Mat n := fun p => fderiv ℝ (orbitParam g (permMatrix σ)) p.1.1 p.1.2
  have hX : ContDiff ℝ ⊤ X :=
    ContDiff.comp (g := orbitParam g (permMatrix σ)) (f := fun p : E => p.1.1)
      (orbitParam_smooth g _) contDiff_fst.fst
  have hZ : ContDiff ℝ ⊤ Z := by
    have hd := smooth_fderiv_of_smooth (orbitParam g (permMatrix σ)) (orbitParam_smooth g _)
    exact (ContDiff.comp (g := fderiv ℝ (orbitParam g (permMatrix σ)))
      (f := fun p : E => p.1.1) hd contDiff_fst.fst).clm_apply contDiff_fst.snd
  have ha : ContDiff ℝ ⊤ (fun p : E => p.2 • balancedLeft b₁ b₂ (X p) (Z p)) :=
    contDiff_snd.smul (ContDiff.comp
      (g := fun q : Mat n × Mat n => balancedLeft b₁ b₂ q.1 q.2)
      (f := fun p : E => (X p, Z p)) (balancedLeft_smooth b₁ b₂) (hX.prodMk hZ))
  have hb : ContDiff ℝ ⊤ (fun p : E => p.2 • balancedRight b₁ b₂ (X p) (Z p)) :=
    contDiff_snd.smul (ContDiff.comp
      (g := fun q : Mat n × Mat n => balancedRight b₁ b₂ q.1 q.2)
      (f := fun p : E => (X p, Z p)) (balancedRight_smooth b₁ b₂) (hX.prodMk hZ))
  have hca := unitCayley_smooth_comp _ ha (fun p => isSkew_smul _ (balancedLeft_skew _ _ _ _))
  have hcb := unitCayley_smooth_comp _ hb (fun p => isSkew_smul _ (balancedRight_skew _ _ _ _))
  apply smooth_orbit_of_smooth_factors σ (chartStepFactors σ g)
  · change ContDiff ℝ ⊤ (fun p : E =>
      unitCayley (p.2 • balancedLeft b₁ b₂ (X p) (Z p)) * (factorLift g p.1.1).1.val)
    simp only [factorLift_left_val]
    exact contDiff_matrix_mul hca (ContDiff.comp (g := chartInv g.1)
      (f := fun p : E => p.1.1.1) (chartInv_smooth g.1) contDiff_fst.fst.fst)
  · change ContDiff ℝ ⊤ (fun p : E =>
      (unitCayley (p.2 • balancedRight b₁ b₂ (X p) (Z p)))ᵀ * (factorLift g p.1.1).2.val)
    simp only [factorLift_right_val]
    exact contDiff_matrix_mul (contDiff_matrix_transpose hcb)
      (ContDiff.comp (g := chartInv g.2) (f := fun p : E => p.1.1.2)
        (chartInv_smooth g.2) contDiff_fst.fst.snd)

end GS.GlobalGeometry
