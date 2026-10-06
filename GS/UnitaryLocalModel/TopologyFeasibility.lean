module

public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.AxisConjugation
public import GS.UnitaryLocalModel.FactorSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Feasibility and the distinguished point of the full local model

Every point of the compact normalized model is in the original scalar-shuffle
unitary family. The proof uses simultaneous diagonalization of the Pauli axis
and does not change the ambient matrix indexing or topology.
-/
noncomputable section
open Matrix GS GS.UnitaryManifold GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

/-- The scalar-block point associated with a middle unitary matrix. -/
def scalarBlockBase {q : ℕ} (Q : CMat q) : CMat (q*2) :=
  flattenBlockFamily (fun i j => Q i j • (1 : CMat 2))

/-- All outer factors at the scalar-block point are identities. -/
def identityOuter (q : ℕ) (o : Fin q) : OuterFactors q o :=
  (fun _ => 1,fun _ => 1)

@[simp] theorem identityOuter_left (q : ℕ) (o i : Fin q) :
    outerLeft (identityOuter q o) i = 1 := rfl

@[simp] theorem identityOuter_right (q : ℕ) (o j : Fin q) :
    outerRight (identityOuter q o) j = 1 := by
  unfold outerRight identityOuter
  split <;> rfl

/-- A fixed sphere representative of the collapsed central fibre. -/
def parameterZero (d : ℕ) : LocalParameters d := (0,0,![1,0,0])

theorem parameterZero_mem (d : ℕ) (r : ℝ) : parameterZero d ∈ localParameterBox d r := by
  simp [parameterZero,localParameterBox,localEnergy,OnSphere,sq_nonneg]

@[simp] theorem parameterCone_zero (d : ℕ) :
    parameterCone (parameterZero d) = coneCoordinatesZero d := by
  refine Prod.ext ?_ ?_
  · rfl
  · apply Subtype.ext
    ext i j
    simp [parameterCone,parameterZero,coneCoordinatesZero,sphereOuter]

def fullParameterZero (q d : ℕ) (o : Fin q) (r : ℝ) : FullCompactParameters q o d r :=
  (identityOuter q o,⟨parameterZero d,parameterZero_mem d r⟩)

@[simp] theorem fullCompactMiddle_zero {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :
    fullCompactMiddle ψ o r (fullParameterZero q d o r) = scalarBlockBase (ψ 0) := by
  unfold fullCompactMiddle fullBlockImage scalarBlockBase
  apply congrArg (@flattenBlockFamily q)
  funext i j
  simp [fullParameterZero,chartBlockFamily,parameterMiddle,chartMiddle,parameterZero,
    middleBlock_equal]

theorem fullBlockImage_mem_localFamily {q d : ℕ} {o : Fin q}
    (ψ : (Fin d → ℝ) → CMat q) (g : OuterFactors q o) (p : LocalParameters d)
    (hp : GS.Unitary (ψ (p.1+p.2.1))) (hm : GS.Unitary (ψ (p.1-p.2.1)))
    (hu : OnSphere p.2.2) :
    fullBlockImage ψ g p ∈ GS.UnitaryNonmanifold.localFamily q := by
  obtain ⟨S,hS,hdiag⟩ := middleBlock_unitary_diagonalization p.2.2 hu
  let v : SmallBlockParameters q :=
    (fun i => outerLeft g i*Sᴴ, ψ (p.1+p.2.1), ψ (p.1-p.2.1),
      fun j => S*outerRight g j)
  have hv : v ∈ smallFactorSet q :=
    ⟨fun i => (outerLeft_unitary g i).mul hS.conjTranspose,hp,hm,
      fun j => hS.mul (outerRight_unitary g j)⟩
  have he : smallFactorMap v = fullBlockImage ψ g p := by
    apply (blockFamilyHomeomorph q).symm.injective
    change extractBlockFamily (smallFactorMap v) = extractBlockFamily (fullBlockImage ψ g p)
    unfold fullBlockImage
    rw [extract_flattenBlockFamily]
    funext i j a b
    change smallFactorMap v (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) = _
    rw [smallFactorMap_block]
    change ((outerLeft g i*Sᴴ)*diagTwo (ψ (p.1+p.2.1) i j) (ψ (p.1-p.2.1) i j)*
      (S*outerRight g j)) a b =
      (outerLeft g i*middleBlock (ψ (p.1+p.2.1) i j) (ψ (p.1-p.2.1) i j) p.2.2*
        outerRight g j) a b
    rw [← hdiag]
    simp only [Matrix.mul_assoc]
  rw [← he, ← image_smallFactorMap]
  exact ⟨v,hv,rfl⟩

/-- Every compact-model matrix is feasible in the complete original family. -/
theorem fullCompactImage_subset_localFamily {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (U : Set (Fin d → ℝ))
    (hψ : ∀ x ∈ U, GS.Unitary (ψ x)) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    FullCompactImage ψ o r ⊆ GS.UnitaryNonmanifold.localFamily q := by
  rintro _ ⟨p,rfl⟩
  exact fullBlockImage_mem_localFamily ψ p.1 p.2.val
    (hψ _ (hargs _ p.2.property).1) (hψ _ (hargs _ p.2.property).2) p.2.property.2.2

theorem scalarBlockBase_mem_localFamily {q : ℕ} (Q : CMat q) (hQ : GS.Unitary Q)
    (o : Fin q) : scalarBlockBase Q ∈ GS.UnitaryNonmanifold.localFamily q := by
  have h := fullBlockImage_mem_localFamily (d := 0) (fun _ => Q)
    (identityOuter q o) (parameterZero 0) hQ hQ (by simp [parameterZero,OnSphere])
  have he := fullCompactMiddle_zero (d := 0) (fun _ => Q) o 0
  change fullBlockImage (fun _ => Q) (identityOuter q o) (parameterZero 0) = _ at he
  exact he ▸ h

end GS.UnitaryLocalModel
