module

public import GS.UnitaryLocalModel.TopologyCompact
public import GS.UnitaryManifold.BlockGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact outer coordinates for the unitary local model

All outer unitary factors are retained. Only the right anchor factor is fixed
to the identity. Their product with the compact middle-coordinate box is
compact, and the output is an actual scalar-indexed matrix in the original
ambient topology.
-/

noncomputable section
open Matrix GS GS.UnitaryManifold
namespace GS.UnitaryLocalModel

abbrev BlockFamily (q : ℕ) := Fin q → Fin q → CMat 2

def flattenBlockFamily {q : ℕ} (N : BlockFamily q) : CMat (q*2) :=
  fun i j =>
    let x := finProdFinEquiv.symm i
    let y := finProdFinEquiv.symm j
    N x.1 y.1 x.2 y.2

def extractBlockFamily {q : ℕ} (M : CMat (q*2)) : BlockFamily q :=
  fun i j a b => M (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))

@[simp] theorem extract_flattenBlockFamily {q : ℕ} (N : BlockFamily q) :
    extractBlockFamily (flattenBlockFamily N) = N := by
  funext i j a b
  simp [extractBlockFamily,flattenBlockFamily]

@[simp] theorem flatten_extractBlockFamily {q : ℕ} (M : CMat (q*2)) :
    flattenBlockFamily (extractBlockFamily M) = M := by
  ext i j
  change M (finProdFinEquiv (finProdFinEquiv.symm i))
    (finProdFinEquiv (finProdFinEquiv.symm j)) = M i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem continuous_flattenBlockFamily (q : ℕ) : Continuous (@flattenBlockFamily q) := by
  unfold flattenBlockFamily
  fun_prop

theorem continuous_extractBlockFamily (q : ℕ) : Continuous (@extractBlockFamily q) := by
  unfold extractBlockFamily
  fun_prop

/-- The block array and scalar matrix spaces have their unchanged topologies. -/
def blockFamilyHomeomorph (q : ℕ) : BlockFamily q ≃ₜ CMat (q*2) where
  toFun := flattenBlockFamily
  invFun := extractBlockFamily
  left_inv := extract_flattenBlockFamily
  right_inv := flatten_extractBlockFamily
  continuous_toFun := continuous_flattenBlockFamily q
  continuous_invFun := continuous_extractBlockFamily q

def asFullUnitary {n : ℕ} (U : CMat n) (hU : GS.Unitary U) :
    BlockU (fun _ : Fin n => 0) :=
  ⟨U,by intro i j h; exact (h rfl).elim,hU⟩

abbrev OuterFactors (q : ℕ) (o : Fin q) :=
  (Fin q → BlockU (fun _ : Fin 2 => 0)) ×
    ({j : Fin q // j ≠ o} → BlockU (fun _ : Fin 2 => 0))

def outerLeft {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) : CMat 2 :=
  (g.1 i).val

def outerRight {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) : CMat 2 :=
  if h : j = o then 1 else (g.2 ⟨j,h⟩).val

theorem outerLeft_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) :
    GS.Unitary (outerLeft g i) := (g.1 i).property.2

theorem outerRight_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) :
    GS.Unitary (outerRight g j) := by
  unfold outerRight
  split
  · exact GS.Unitary.one
  · exact (g.2 _).property.2

@[simp] theorem outerRight_anchor {q : ℕ} {o : Fin q} (g : OuterFactors q o) :
    outerRight g o = 1 := by simp [outerRight]

def outerOfMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) : OuterFactors q o :=
  (fun i => asFullUnitary (L i) (hL i), fun j => asFullUnitary (R j.val) (hR j.val))

@[simp] theorem outerLeft_ofMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) :
    outerLeft (outerOfMatrices (o := o) L R hL hR) = L := rfl

theorem outerRight_ofMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) (ho : R o = 1) :
    outerRight (outerOfMatrices (o := o) L R hL hR) = R := by
  funext j
  by_cases hj : j = o
  · subst j
    simp [outerRight,ho]
  · simp [outerRight,hj,outerOfMatrices,asFullUnitary]

theorem outerFactors_ext {q : ℕ} {o : Fin q} {g h : OuterFactors q o}
    (hL : outerLeft g = outerLeft h) (hR : outerRight g = outerRight h) : g = h := by
  apply Prod.ext
  · funext i
    exact Subtype.ext (congrFun hL i)
  · funext j
    apply Subtype.ext
    have hh := congrFun hR j.val
    simpa [outerRight,j.property] using hh

theorem continuous_outerLeft (q : ℕ) (o : Fin q) :
    Continuous (@outerLeft q o) := by
  unfold outerLeft
  fun_prop

theorem continuous_outerRight (q : ℕ) (o : Fin q) :
    Continuous (@outerRight q o) := by
  apply continuous_pi
  intro j
  by_cases hj : j = o
  · simp only [outerRight,dif_pos hj]
    exact continuous_const
  · simp only [outerRight,dif_neg hj]
    fun_prop

def chartBlockFamily {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q)
    (p : LocalParameters d) : BlockFamily q :=
  fun i j => parameterMiddle (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) p (i,j)

def fullBlockImage {q d : ℕ} {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d) : CMat (q*2) :=
  flattenBlockFamily (fun i j => outerLeft g i * chartBlockFamily ψ p i j * outerRight g j)

abbrev FullCompactParameters (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :=
  OuterFactors q o × localParameterBox d r

def fullCompactMiddle {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (p : FullCompactParameters q o d r) : CMat (q*2) :=
  fullBlockImage ψ p.1 p.2.val

abbrev FullCompactImage {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :=
  Set.range (fullCompactMiddle ψ o r)

instance fullCompactParameters_compactSpace (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :
    CompactSpace (FullCompactParameters q o d r) := by
  letI : CompactSpace (localParameterBox d r) :=
    isCompact_iff_compactSpace.mp (isCompact_localParameterBox d r)
  exact inferInstance

theorem continuous_fullCompactMiddle {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) (o : Fin q) (r : ℝ)
    (hψ : ContinuousOn ψ U)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    Continuous (fullCompactMiddle ψ o r) := by
  have hψ' : ContinuousOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U := by
    apply continuousOn_pi.mpr
    intro ij
    exact ((continuous_apply ij.2).comp (continuous_apply ij.1)).comp_continuousOn hψ
  have hm := continuous_parameterMiddle_on_box _ U hψ' r hargs
  apply (continuous_flattenBlockFamily q).comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_matrix_product
  · apply continuous_matrix_product
    · exact ((continuous_apply i).comp (continuous_outerLeft q o)).comp continuous_fst
    · exact ((continuous_apply (i,j)).comp hm).comp continuous_snd
  · exact ((continuous_apply j).comp (continuous_outerRight q o)).comp continuous_fst

end GS.UnitaryLocalModel
