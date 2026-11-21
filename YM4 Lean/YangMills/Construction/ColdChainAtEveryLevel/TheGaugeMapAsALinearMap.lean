import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOnAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GaugeMapLinear
open BlockAverages GaugeMap LatticeFractionalIntegration
variable {F : BlockFrame}
theorem adjointAction_linComb (g : UnitQuaternion) (a b : ℝ) (p q : ℍ[ℝ]) :
    adjointAction g (a • p + b • q) = a • adjointAction g p + b • adjointAction g q := by
  simp only [adjointAction, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (a : ℝ) (p : ℍ[ℝ]) :
    adjointAction g (a • p) = a • adjointAction g p := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_inv_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g⁻¹ (adjointAction g w) = w := by apply _root_.YangMills.Construction.CellBumps.adjointAction_inv_adjointAction <;> assumption
theorem re_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : (adjointAction g w).re = w.re := by apply _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re <;> assumption
section Paths
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem lineSum_linComb (a b : ℝ) (w w' : Lattice4 → Fin 4 → E) (y : Lattice4) (i : Fin 4) (n : ℤ) :
    lineSum (fun p q => a • w p q + b • w' p q) y i n = a • lineSum w y i n + b • lineSum w' y i n := by
  simp only [lineSum, Finset.sum_add_distrib, ← Finset.smul_sum, smul_sub]
  abel
theorem staircaseSum_linComb (a b : ℝ) (w w' : Lattice4 → Fin 4 → E) (u v : Lattice4) :
    staircaseSum (fun p q => a • w p q + b • w' p q) u v =
      a • staircaseSum w u v + b • staircaseSum w' u v := by
  simp only [staircaseSum, lineSum_linComb, Finset.sum_add_distrib, ← Finset.smul_sum]
theorem dyadicPathSum_linComb (a b : ℝ) (K : ℕ) (w w' : Lattice4 → Fin 4 → E) (x : Lattice4)
    (ω : StaircaseSample) :
    dyadicPathSum K (fun p q => a • w p q + b • w' p q) x ω =
      a • dyadicPathSum K w x ω + b • dyadicPathSum K w' x ω := by
  simp only [dyadicPathSum, staircaseSum_linComb, Finset.sum_add_distrib, ← Finset.smul_sum]
theorem randomPathMean_linComb (a b : ℝ) (l : ℕ) (c : Lattice4) (w w' : Lattice4 → Fin 4 → E)
    (x : Lattice4) :
    randomPathMean l c (fun p q => a • w p q + b • w' p q) x =
      a • randomPathMean l c w x + b • randomPathMean l c w' x := by
  simp only [randomPathMean, dyadicPathSum_linComb, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [smul_comm a, smul_comm b]
theorem randomPathMean_zero (l : ℕ) (c : Lattice4) (x : Lattice4) :
    randomPathMean l c (fun _ _ => (0 : E)) x = 0 := by
  have h := randomPathMean_linComb (0 : ℝ) 0 l c (fun _ _ => (0 : E)) (fun _ _ => (0 : E)) x
  simpa using h
end Paths
def quaternionReLinear : ℍ[ℝ] →ₗ[ℝ] ℝ where
  toFun q := q.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem re_randomPathMean (l : ℕ) (c : Lattice4) (w : Lattice4 → Fin 4 → ℍ[ℝ]) (x : Lattice4) :
    (randomPathMean l c w x).re = randomPathMean l c (fun p q => (w p q).re) x := by
  change quaternionReLinear (randomPathMean l c w x) =
    randomPathMean l c (fun p q => quaternionReLinear (w p q)) x
  simp only [randomPathMean, dyadicPathSum, staircaseSum, lineSum, map_smul, map_sum, map_sub]
variable (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
theorem localForm_linComb (a b : ℝ) (z : F.Cell) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    localForm S V R z (fun x i => a • u x i + b • u' x i) =
      fun x i => a • localForm S V R z u x i + b • localForm S V R z u' x i := by
  funext x i
  simp only [localForm]
  split_ifs
  · rw [adjointAction_linComb]
  · rw [adjointAction_linComb, neg_add, ← smul_neg, ← smul_neg, adjointAction_linComb]
theorem localPotential_linComb (a b : ℝ) (z : F.Cell) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    localPotential S V R z (fun x i => a • u x i + b • u' x i) =
      fun x => a • localPotential S V R z u x + b • localPotential S V R z u' x := by
  funext x
  simp only [localPotential, localForm_linComb, randomPathMean_linComb]
theorem localPotentialMean_linComb (a b : ℝ) (z : F.Cell) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    localPotentialMean S V R z (fun x i => a • u x i + b • u' x i) =
      a • localPotentialMean S V R z u + b • localPotentialMean S V R z u' := by
  simp only [localPotentialMean, localPotential_linComb, Finset.sum_add_distrib, ← Finset.smul_sum,
    smul_add]
  rw [smul_comm a, smul_comm b]
theorem gluedPotential_linComb (a b : ℝ) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    gluedPotential S V R (fun x i => a • u x i + b • u' x i) =
      fun s => a • gluedPotential S V R u s + b • gluedPotential S V R u' s := by
  funext s
  simp only [gluedPotential, localPotential_linComb, localPotentialMean_linComb]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have e : ∀ (p p' q q' : ℍ[ℝ]), a • p + b • p' - (a • q + b • q') = a • (p - q) + b • (p' - q') := by
    intro p p' q q'
    simp only [smul_sub]
    abel
  rw [e, adjointAction_linComb, smul_add, smul_comm (cellPartition S s z) a,
    smul_comm (cellPartition S s z) b]
theorem frameCellMean_linComb (a b : ℝ) (y : F.Cell) (ξ ξ' : F.Site 0 → ℍ[ℝ]) :
    frameCellMean S V y (fun x => a • ξ x + b • ξ' x) =
      a • frameCellMean S V y ξ + b • frameCellMean S V y ξ' := by
  simp only [frameCellMean, adjointAction_linComb, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [smul_comm a, smul_comm b]
theorem gaugeMap_linComb (a b : ℝ) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    gaugeMap S V R (fun x i => a • u x i + b • u' x i) =
      fun s => a • gaugeMap S V R u s + b • gaugeMap S V R u' s := by
  funext s
  simp only [gaugeMap, gluedPotential_linComb, frameCellMean_linComb]
  simp only [smul_sub, Finset.smul_sum]
  have e : ∀ y : F.Cell, normalizedBump S s y • adjointAction (frameChange S V y s)
        (a • frameCellMean S V y (gluedPotential S V R u) +
          b • frameCellMean S V y (gluedPotential S V R u')) =
      a • (normalizedBump S s y • adjointAction (frameChange S V y s)
          (frameCellMean S V y (gluedPotential S V R u))) +
        b • (normalizedBump S s y • adjointAction (frameChange S V y s)
          (frameCellMean S V y (gluedPotential S V R u'))) := by
    intro y
    rw [adjointAction_linComb, smul_add, smul_comm (normalizedBump S s y) a,
      smul_comm (normalizedBump S s y) b]
  simp only [e, Finset.sum_add_distrib]
  abel
theorem re_gaugeMap (u : F.Site 0 → Fin 4 → ℍ[ℝ]) (hu : ∀ x i, (u x i).re = 0) (s : F.Site 0) :
    (gaugeMap S V R u s).re = 0 := by
  have hform : ∀ z x i, (localForm S V R z u x i).re = 0 := by
    intro z x i
    simp only [localForm]
    rw [re_adjointAction]
    split_ifs
    · exact hu _ _
    · rw [Quaternion.re_neg, re_adjointAction, hu]
      simp
  have hpot : ∀ z x, (localPotential S V R z u x).re = 0 := by
    intro z x
    simp only [localPotential]
    rw [re_randomPathMean]
    simp only [hform]
    exact randomPathMean_zero _ _ _
  have hcen : ∀ z, (localPotentialMean S V R z u).re = 0 := by
    intro z
    change quaternionReLinear (localPotentialMean S V R z u) = 0
    simp only [localPotentialMean, map_smul, map_sum]
    change (_ : ℝ) • ∑ x ∈ cellOffsets F, (localPotential S V R z u x).re = 0
    simp [hpot]
  have hgl : ∀ s, (gluedPotential S V R u s).re = 0 := by
    intro s
    change quaternionReLinear (gluedPotential S V R u s) = 0
    simp only [gluedPotential, map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro z _
    change cellPartition S s z • (adjointAction _ _).re = 0
    rw [re_adjointAction, Quaternion.re_sub, hpot, hcen]
    simp
  have hme : ∀ y, (frameCellMean S V y (gluedPotential S V R u)).re = 0 := by
    intro y
    change quaternionReLinear (frameCellMean S V y (gluedPotential S V R u)) = 0
    simp only [frameCellMean, map_sum, map_smul]
    change (_ : ℝ) • ∑ x ∈ cellOffsets F, (adjointAction _ _).re = 0
    simp [re_adjointAction, hgl]
  change quaternionReLinear (gaugeMap S V R u s) = 0
  simp only [gaugeMap, map_sub, map_sum, map_smul]
  change (gluedPotential S V R u s).re - ∑ y ∈ S, normalizedBump S s y • (adjointAction _ _).re = 0
  simp [re_adjointAction, hgl, hme]
omit S V R in
theorem enclosingCell_cellCentre_add {j : ℕ} (hodd : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h) = z := by apply _root_.YangMills.Construction.CellBumps.enclosingCell_cellCentre_add <;> assumption
omit V R in
theorem patchOffset_mem_centredCube (hodd : Odd F.blockSide) (z : F.Cell) (x : Lattice4)
    (hx : x ∈ cellOffsets F) :
    (fun i => closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)) ∈
      centredCube (F.blockSide ^ (F.top - 0)) := by apply _root_.YangMills.Construction.CellBumps.signed_offset_mem_centredCube <;> assumption
omit V R in
theorem patchSite_mem_sitesOfCells (hodd : Odd F.blockSide) (z : F.Cell) (hz : z ∈ S) (x : Lattice4)
    (hx : x ∈ cellOffsets F) : patchSite S z x ∈ sitesOfCells S 0 := by
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨z, hz, _, patchOffset_mem_centredCube S hodd z x hx, rfl⟩
omit V R in
theorem enclosingCell_mem (hodd : Odd F.blockSide) (x : F.Site 0) (hx : x ∈ sitesOfCells S 0) :
    enclosingCell x ∈ S := by
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨z, hz, h, hh, rfl⟩ := hx
  rw [enclosingCell_cellCentre_add hodd z h hh]
  exact hz
theorem cellMeanFree_linComb (a b : ℝ) (ξ ξ' : F.Site 0 → ℍ[ℝ]) (h : CellMeanFree S V ξ)
    (h' : CellMeanFree S V ξ') : CellMeanFree S V (fun x => a • ξ x + b • ξ' x) := by
  intro y hy
  rw [frameCellMean_linComb, h y hy, h' y hy]
  simp
theorem cellMeanFree_congr (hodd : Odd F.blockSide) (ξ ξ' : F.Site 0 → ℍ[ℝ])
    (he : ∀ s ∈ sitesOfCells S 0, ξ s = ξ' s) (h : CellMeanFree S V ξ) : CellMeanFree S V ξ' := by
  intro y hy
  have := h y hy
  simp only [frameCellMean] at this ⊢
  rw [← this]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [he _ (patchSite_mem_sitesOfCells S hodd y hy x hx)]
open Classical in
def extendByZero (A : Finset (F.Site 0)) : (↥A → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) where
  toFun x y := if h : y ∈ A then x ⟨y, h⟩ else 0
  map_add' x x' := by
    funext y
    by_cases h : y ∈ A <;> simp [h]
  map_smul' c x := by
    funext y
    by_cases h : y ∈ A <;> simp [h]
def restrictToSites (A : Finset (F.Site 0)) : (F.Site 0 → ℍ[ℝ]) →ₗ[ℝ] (↥A → ℍ[ℝ]) where
  toFun g a := g a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def gaugeMapLinear : (F.Site 0 → Fin 4 → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) where
  toFun := gaugeMap S V R
  map_add' u u' := by
    have := gaugeMap_linComb S V R 1 1 u u'
    simp only [one_smul] at this
    exact this
  map_smul' c u := by
    have := gaugeMap_linComb S V R c 0 u u
    simp only [zero_smul, add_zero] at this
    exact this
def covariantDiffLinear : (F.Site 0 → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → Fin 4 → ℍ[ℝ]) where
  toFun := covariantDiff R
  map_add' ξ ξ' := by
    funext x i
    simp only [covariantDiff, Pi.add_apply, adjointAction_add]
    abel
  map_smul' c ξ := by
    funext x i
    simp only [covariantDiff, Pi.smul_apply, adjointAction_smul, RingHom.id_apply, smul_sub]
omit V in
theorem extendByZero_apply_mem (A : Finset (F.Site 0)) (x : ↥A → ℍ[ℝ]) (a : ↥A) :
    extendByZero A x a = x a := by
  simp [extendByZero]
theorem re_extendByZero (A : Finset (F.Site 0)) (x : ↥A → ℍ[ℝ]) (hx : ∀ a, (x a).re = 0)
    (y : F.Site 0) : (extendByZero A x y).re = 0 := by
  by_cases h : y ∈ A
  · exact (by simpa using extendByZero_apply_mem (F := F) A x ⟨y, h⟩ ▸ hx ⟨y, h⟩)
  · simp [extendByZero, h]
def meanFreeSubmodule (hodd : Odd F.blockSide) : Submodule ℝ (↥(sitesOfCells S 0) → ℍ[ℝ]) where
  carrier := {x | CellMeanFree S V (extendByZero _ x) ∧ ∀ a, (x a).re = 0}
  add_mem' := by
    intro x x' hx hx'
    refine ⟨?_, fun a => ?_⟩
    · have := cellMeanFree_linComb S V 1 1 _ _ hx.1 hx'.1
      simp only [one_smul] at this
      rw [map_add]
      exact this
    · have h1 := hx.2 a
      have h2 := hx'.2 a
      simp [h1, h2]
  zero_mem' := by
    refine ⟨?_, fun a => by simp⟩
    intro y _
    rw [map_zero]
    have := frameCellMean_linComb S V 0 0 y 0 0
    simp only [zero_smul, add_zero] at this
    exact this
  smul_mem' := by
    intro c x hx
    refine ⟨?_, fun a => ?_⟩
    · have := cellMeanFree_linComb S V c 0 _ _ hx.1 hx.1
      simp only [zero_smul, add_zero] at this
      rw [map_smul]
      exact this
    · have h1 := hx.2 a
      simp [h1]
end GaugeMapLinear
end YangMills.Construction
end
