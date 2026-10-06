module

public import GS.SharedGeodesics.Orthogonal
public import GS.SharedGeometry.GeneratorAction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factor-independent orthogonal shared geodesics

First prove intertwining for the convergent matrix power series. Under
nonoverlap, the actual point synthesis is an isometry for the physical
(expanded-block) generator norm and hence injective. The spatial exponential
word then proves independence from both the factor representative and the
compatible initial generators. No uniqueness theorem for an assumed ODE is used.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry GS.SharedGeometry
open scoped Topology BigOperators Manifold
namespace GS.SharedGeodesics
variable {n : ℕ}

def mulLeftCLM (H : Mat n) : Mat n →L[ℝ] Mat n :=
  ({ toFun := fun A => H * A
     map_add' := Matrix.mul_add H
     map_smul' := by
       intro a A
       simp only [Matrix.mul_smul, RingHom.id_apply]
   } : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap

def mulRightCLM (H : Mat n) : Mat n →L[ℝ] Mat n :=
  ({ toFun := fun A => A * H
     map_add' := fun A B => Matrix.add_mul A B H
     map_smul' := by
       intro a A
       simp only [Matrix.smul_mul, RingHom.id_apply]
   } : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap

/-- Intertwining is passed through the actual convergent power series. -/
theorem matrixExp_intertwine (A B H : Mat n) (h : A * H = H * B) :
    matrixExp A * H = H * matrixExp B := by
  have hp : ∀ k : ℕ, A ^ k * H = H * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        A ^ (k + 1) * H = A * (A ^ k * H) := by rw [pow_succ', Matrix.mul_assoc]
        _ = A * (H * B ^ k) := by rw [ih]
        _ = H * B ^ (k + 1) := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, ← pow_succ']
  let F (s : Finset ℕ) : Mat n := ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k
  let G (s : Finset ℕ) : Mat n := ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • B ^ k
  have hF : Filter.Tendsto F Filter.atTop (𝓝 (matrixExp A)) := matrixExp_hasSum A
  have hG : Filter.Tendsto G Filter.atTop (𝓝 (matrixExp B)) := matrixExp_hasSum B
  have hf := (mulRightCLM H).continuous.continuousAt.tendsto.comp hF
  have hg := (mulLeftCLM H).continuous.continuousAt.tendsto.comp hG
  have he : (fun s => mulRightCLM H (F s)) = fun s => mulLeftCLM H (G s) := by
    funext s
    change mulRightCLM H (∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k) =
      mulLeftCLM H (∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • B ^ k)
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun W : Mat n => ((k.factorial : ℝ)⁻¹) • W) (hp k)
  have hf' : Filter.Tendsto (fun s => mulRightCLM H (F s)) Filter.atTop
      (𝓝 (matrixExp A * H)) := hf
  rw [he] at hf'
  exact tendsto_nhds_unique hf' hg

theorem expLine_intertwine (A B H : Mat n) (h : A * H = H * B) (t : ℝ) :
    expLine A t * H = H * expLine B t :=
  matrixExp_intertwine (t • A) (t • B) H (by
    rw [Matrix.smul_mul, Matrix.mul_smul, h])

theorem expLine_conjugate (L C : Mat n) (hL : Orthogonal L) (t : ℝ) :
    expLine (L * C * Lᵀ) t = L * expLine C t * Lᵀ := by
  have h : (L * C * Lᵀ) * L = L * C := by
    rw [Matrix.mul_assoc (L * C), hL.1, Matrix.mul_one]
  have he := congrArg (fun W : Mat n => W * Lᵀ)
    (expLine_intertwine (L * C * Lᵀ) C L h t)
  simpa only [Matrix.mul_assoc, hL.2, Matrix.mul_one] using he

variable {right left : Pattern n} (σ : Equiv.Perm (Fin n))

theorem pointMap_carrier_energy
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (v : PairGenerator right left) :
    frobSq (pointMap right left (permMatrix σ) v) = generatorEnergy v := by
  have hc := frobInner_disjoint_supported_skew
    (GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint σ hno)
    v.1.val (permMatrix σ * v.2.val * (permMatrix σ)ᵀ) v.1.property.1
    ((supported_perm_conjugate_iff right.block σ v.2.val).mpr v.2.property.1)
    (conjugate_skew _ _ v.2.property.2.1)
  have hn := tangentParam_frobSq 1 (permMatrix σ) 1 v.1.val v.2.val
    Orthogonal.one (perm_orthogonal σ) Orthogonal.one hc
  simpa only [tangentParam, Matrix.one_mul, Matrix.mul_one,
    pointMap, LinearMap.coe_mk, AddHom.coe_mk, generatorEnergy, generatorInner, frobSq] using hn

theorem pointMap_orbit_energy
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (v : PairGenerator right left) :
    frobSq (pointMap right left (g • permMatrix σ) v) = generatorEnergy v := by
  calc
    _ = frobSq (g • pointMap right left (permMatrix σ) (generatorAction g⁻¹ v)) := by
      rw [← pointMap_generatorAction, generatorAction_inverse_right]
    _ = frobSq (pointMap right left (permMatrix σ) (generatorAction g⁻¹ v)) :=
      action_frobInner g _ _
    _ = generatorEnergy (generatorAction g⁻¹ v) := pointMap_carrier_energy σ hno _
    _ = generatorEnergy v := generatorEnergy_action g⁻¹ v

/-- In the real no-overlap case the physical generator pair is unique at a point. -/
theorem pointMap_injective_noOverlap
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (X : MatrixOrbit right left (permMatrix σ)) :
    Function.Injective (pointMap right left X.val) := by
  obtain ⟨g, hg⟩ := X.property
  change g • permMatrix σ = X.val at hg
  intro v w h
  apply sub_eq_zero.mp
  apply (generatorEnergy_eq_zero_iff _).mp
  have hn := pointMap_orbit_energy σ hno g (v - w)
  rw [hg, map_sub, h, sub_self] at hn
  exact hn.symm.trans (by simp [frobSq])

def spatialExpWord (X : Mat n) (v : PairGenerator right left) (t : ℝ) : Mat n :=
  expLine v.1.val t * X * expLine v.2.val t

theorem orthogonalExpCurve_spatial_word (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    (orthogonalExpCurve right left σ g C Ω t).val =
      spatialExpWord (g • permMatrix σ) (generatorAction g (C, Ω)) t := by
  rw [orthogonalExpCurve_val]
  unfold spatialExpWord
  simp only [generatorAction_left, generatorAction_right, Prod.fst, Prod.snd,
    expLine_conjugate _ _ (Factor.matrix_orthogonal g.1),
    expLine_conjugate _ _ (Factor.matrix_orthogonal g.2), action_apply]
  symm
  calc
    _ = Factor.matrix g.1 * expLine C.val t *
        ((Factor.matrix g.1)ᵀ * Factor.matrix g.1) * permMatrix σ *
        ((Factor.matrix g.2)ᵀ * Factor.matrix g.2) * expLine Ω.val t * (Factor.matrix g.2)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [(Factor.matrix_orthogonal g.1).1, (Factor.matrix_orthogonal g.2).1]
      simp only [Matrix.mul_one, gsExpCurve, product2, gsExpLeft, gsExpRight, Matrix.mul_assoc]

theorem orthogonalExpVelocity_zero_spatial (g : Factors right left)
    (C : Generator left) (Ω : Generator right) :
    orthogonalExpVelocity right left σ g C Ω 0 =
      pointMap right left (g • permMatrix σ) (generatorAction g (C, Ω)) := by
  rw [pointMap_generatorAction]
  change gsExpVelocity _ _ _ _ _ 0 = _
  rw [gsExpVelocity_zero _ _ _ _ _ (perm_orthogonal σ)]
  simp only [pointMap, LinearMap.coe_mk, AddHom.coe_mk, action_apply,
    tangentParam, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Same matrix point and same actual initial matrix tangent give exactly the
same all-real curve, even when the factor representation is not unique. -/
theorem orthogonalExpCurve_factor_independent
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g h : Factors right left) (C C' : Generator left) (Ω Ω' : Generator right)
    (hbase : orbitMapToOrbit right left (permMatrix σ) g = orbitMapToOrbit right left (permMatrix σ) h)
    (hvel : orthogonalExpVelocity right left σ g C Ω 0 =
      orthogonalExpVelocity right left σ h C' Ω' 0) (t : ℝ) :
    orthogonalExpCurve right left σ g C Ω t = orthogonalExpCurve right left σ h C' Ω' t := by
  have hX : g • permMatrix σ = h • permMatrix σ := congrArg Subtype.val hbase
  have hv : generatorAction g (C, Ω) = generatorAction h (C', Ω') := by
    apply pointMap_injective_noOverlap σ hno (orbitMapToOrbit right left (permMatrix σ) g)
    change pointMap right left (g • permMatrix σ) _ = pointMap right left (g • permMatrix σ) _
    calc
      _ = orthogonalExpVelocity right left σ g C Ω 0 := (orthogonalExpVelocity_zero_spatial σ g C Ω).symm
      _ = orthogonalExpVelocity right left σ h C' Ω' 0 := hvel
      _ = pointMap right left (h • permMatrix σ) (generatorAction h (C', Ω')) :=
        orthogonalExpVelocity_zero_spatial σ h C' Ω'
      _ = _ := by rw [← hX]
  apply Subtype.ext
  rw [orthogonalExpCurve_spatial_word, orthogonalExpCurve_spatial_word, hX, hv]

end GS.SharedGeodesics
