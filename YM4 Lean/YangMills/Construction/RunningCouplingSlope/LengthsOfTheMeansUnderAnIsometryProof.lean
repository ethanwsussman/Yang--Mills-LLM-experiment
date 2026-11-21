import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometryProof
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.RunningCouplingSlope.LengthsOfTheMeansUnderAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SlopeCoefficient
open BlockAverages BlockAverages.ChartCoordinates LatticePaths
variable {F : BlockFrame}
private def linearPart (g : CubicSymmetry) (h : LatticeFractionalIntegration.Lattice4) :
    LatticeFractionalIntegration.Lattice4 := fun i => g.sign i * h (g.perm i)
private def inverse (g : CubicSymmetry) : CubicSymmetry :=
  ⟨g.perm⁻¹, fun i => g.sign (g.perm⁻¹ i), fun i => - (g.sign (g.perm⁻¹ i) * g.shift (g.perm⁻¹ i))⟩
private theorem star_sum_sum_eq {ι κ : Type} (s : Finset ι) (t : Finset κ) (f : ι → κ → ℍ[ℝ]) :
    star (∑ h ∈ s, ∑ π ∈ t, f h π) = ∑ h ∈ s, ∑ π ∈ t, star (f h π) := by
  simp [star_sum]
private theorem siteCoords_cast_self {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
private theorem sign_mul_self {g : CubicSymmetry} (hg : g.IsSymmetry F) (i : Fin 4) : g.sign i * g.sign i = 1 := by
  rcases hg.1 i with h | h <;> rw [h] <;> norm_num
private theorem actSite_add {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j)
    (h : LatticeFractionalIntegration.Lattice4) :
    g.actSite j (x + siteOfCoords j h) = g.actSite j x + siteOfCoords j (linearPart g h) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add <;> assumption
private theorem inverse_actSite {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j) :
    (inverse g).actSite j (g.actSite j x) = x := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_actSite <;> assumption
private theorem inverse_isSymmetry {g : CubicSymmetry} (hg : g.IsSymmetry F) : (inverse g).IsSymmetry F := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_isSymmetry <;> assumption
private theorem inverse_inverse {g : CubicSymmetry} (hg : g.IsSymmetry F) : inverse (inverse g) = g := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_symmInv <;> assumption
private def mapStep (g : CubicSymmetry) (st : PathStep) : PathStep :=
  (g.perm.symm st.1, if g.sign (g.perm.symm st.1) = 1 then st.2 else !st.2)
private theorem linearPart_stepDisplacement {g : CubicSymmetry} (hg : g.IsSymmetry F) (st : PathStep) :
    linearPart g (FlatPairing.stepDisplacement st) = FlatPairing.stepDisplacement (mapStep g st) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linearPart_stepDisplacement <;> assumption
private def pushForward (g : CubicSymmetry) {j : ℕ} (X : F.GaugeField j) : F.GaugeField j :=
  fun y i => linkValue X ((inverse g).actSite j y) (g.perm i, decide (g.sign i = 1))
section Sites
variable {g : CubicSymmetry} (hg : g.IsSymmetry F)
include hg
private theorem actSite_refineSite {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    g.actSite j (refineSite y) = refineSite (g.actSite (j + 1) y) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_refineSite <;> assumption
private theorem linearPart_mem_centredCube {M : ℕ} {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube M) : linearPart g h ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linearPart_mem_centredCube <;> assumption
private theorem actSite_mem_sitesOfCells {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') {j : ℕ}
    (hj : j ≤ F.top) {x : F.Site j} (hx : x ∈ sitesOfCells S j) : g.actSite j x ∈ sitesOfCells S' j := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_mem_sitesOfCells <;> assumption
end Sites
section Paths
variable {j : ℕ}
private theorem pathHolonomy_reversePath (X : F.GaugeField j) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X (x + siteOfCoords j (endpoint 0 l)) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.pathHolonomy_reversePath <;> assumption
end Paths
section Contours
variable {g : CubicSymmetry}
private theorem replicate_mapStep (hg : g.IsSymmetry F) (k : Fin 4) (x y : ℤ) (e : y = g.sign (g.perm.symm k) * x) :
    List.replicate x.natAbs (mapStep g (k, decide (0 ≤ x))) =
      List.replicate y.natAbs (g.perm.symm k, decide (0 ≤ y)) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.replicate_mapStep <;> assumption
private theorem map_axisPath (hg : g.IsSymmetry F) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_axisPath <;> assumption
private theorem map_reversePath (l : List PathStep) :
    (reversePath l).map (mapStep g) = reversePath (l.map (mapStep g)) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_reversePath <;> assumption
private theorem map_bondContour (hg : g.IsSymmetry F) (L : ℕ) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) ++
      List.replicate L (mapStep g (i, true)) ++ reversePath (axisPath (linearPart g h) (π.trans g.perm.symm)) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_bondContour <;> assumption
private theorem reversePath_bondContour (L : ℕ) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    reversePath (bondContour L h π i) = axisPath h π ++ List.replicate L (i, false) ++
      reversePath (axisPath h π) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.reversePath_bondContour <;> assumption
end Contours
section Bonds
variable {g : CubicSymmetry}
private def mapBond (g : CubicSymmetry) (j : ℕ) (c : F.Site j × Fin 4) : F.Site j × Fin 4 :=
  if g.sign (g.perm.symm c.2) = 1 then (g.actSite j c.1, g.perm.symm c.2)
  else (g.actSite j c.1 - unitStep j (g.perm.symm c.2), g.perm.symm c.2)
variable (hg : g.IsSymmetry F)
include hg
private theorem actSite_add_unitStep_of_pos {j : ℕ} (y : F.Site j) {i : Fin 4} (hs : g.sign (g.perm.symm i) = 1) :
    g.actSite j (y + unitStep j i) = g.actSite j y + unitStep j (g.perm.symm i) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add_unitStep_of_pos <;> assumption
private theorem actSite_add_unitStep_of_neg {j : ℕ} (y : F.Site j) {i : Fin 4} (hs : g.sign (g.perm.symm i) = -1) :
    g.actSite j (y + unitStep j i) = g.actSite j y - unitStep j (g.perm.symm i) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add_unitStep_of_neg <;> assumption
private theorem mapBond_mem {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') {j : ℕ} (hj : j ≤ F.top)
    {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) : mapBond g j c ∈ innerBonds S' j := by
  have h1 : c.1 ∈ sitesOfCells S j := (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  have h2 : c.1 + unitStep j c.2 ∈ sitesOfCells S j := (Finset.mem_filter.1 hc).2
  have m1 := actSite_mem_sitesOfCells hg hS hj h1
  have m2 := actSite_mem_sitesOfCells hg hS hj h2
  unfold mapBond
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · rw [if_pos hs]
    rw [actSite_add_unitStep_of_pos hg _ hs] at m2
    exact mem_innerBonds m1 m2
  · rw [if_neg (by rw [hs]; norm_num)]
    rw [actSite_add_unitStep_of_neg hg _ hs] at m2
    exact mem_innerBonds m2 (by rwa [sub_add_cancel])
private theorem inverse_mapBond {j : ℕ} (c : F.Site j × Fin 4) : mapBond (inverse g) j (mapBond g j c) = c := by
  obtain ⟨y, i⟩ := c
  have hp : (inverse g).perm.symm (g.perm.symm i) = i := by
    show g.perm (g.perm.symm i) = i
    simp
  have hsg : (inverse g).sign i = g.sign (g.perm.symm i) := rfl
  unfold mapBond
  rcases hg.1 (g.perm.symm i) with hs | hs
  · simp only [if_pos hs, hp, hsg, inverse_actSite hg]
  · simp only [if_neg (show ¬ g.sign (g.perm.symm i) = 1 by rw [hs]; norm_num), hp, hsg]
    rw [← actSite_add_unitStep_of_neg hg y hs, inverse_actSite hg]
    simp
private theorem mapBond_inverse {j : ℕ} (c : F.Site j × Fin 4) : mapBond g j (mapBond (inverse g) j c) = c := by
  have := inverse_mapBond (inverse_isSymmetry hg) c
  rwa [inverse_inverse hg] at this
private theorem sum_centredCube_linearPart {M : Type} [AddCommMonoid M] (L : ℕ)
    (f : LatticeFractionalIntegration.Lattice4 → Equiv.Perm (Fin 4) → M) :
    ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f (linearPart g h) (π.trans g.perm.symm) =
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.sum_centredCube_perm <;> assumption
private theorem pathHolonomy_bondContour {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j) (y : F.Site (j + 1))
    (L : ℕ) (h : LatticeFractionalIntegration.Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathHolonomy X (refineSite y) (bondContour L h π i) =
      pathHolonomy (pushForward g X) (refineSite (g.actSite (j + 1) y))
        (axisPath (linearPart g h) (π.trans g.perm.symm) ++ List.replicate L (mapStep g (i, true)) ++
          reversePath (axisPath (linearPart g h) (π.trans g.perm.symm))) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.pathHolonomy_bondContour <;> assumption
private theorem contourAverage_mapBond_of_pos {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (hs : g.sign (g.perm.symm c.2) = 1) :
    contourAverage (pushForward g X) (mapBond g (j + 1) c) = contourAverage X c := by
  have hb : mapBond g (j + 1) c = (g.actSite (j + 1) c.1, g.perm.symm c.2) := by
    unfold mapBond
    rw [if_pos hs]
  have hst : mapStep g (c.2, true) = (g.perm.symm c.2, true) := by
    simp [mapStep, hs]
  rw [hb]
  unfold contourAverage
  congr 1
  rw [← sum_centredCube_linearPart hg F.blockSide (fun h π => ((pathHolonomy (pushForward g X)
    (refineSite (g.actSite (j + 1) c.1)) (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) : ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst]
  rfl
private theorem contourAverage_mapBond_of_neg {j : ℕ} (hj : j + 1 ≤ F.top) (hL : 1 ≤ F.blockSide)
    (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (hs : g.sign (g.perm.symm c.2) = -1) :
    contourAverage (pushForward g X) (mapBond g (j + 1) c) = star (contourAverage X c) := by
  have hne : ¬ g.sign (g.perm.symm c.2) = 1 := by
    rw [hs]
    norm_num
  obtain ⟨b, hbdef⟩ : ∃ b, b = g.actSite (j + 1) c.1 - unitStep (j + 1) (g.perm.symm c.2) := ⟨_, rfl⟩
  have hb : mapBond g (j + 1) c = (b, g.perm.symm c.2) := by
    unfold mapBond
    rw [if_neg hne, hbdef]
  have hst : mapStep g (c.2, true) = (g.perm.symm c.2, false) := by
    simp [mapStep, hs]
  rw [hb]
  unfold contourAverage
  rw [quaternion_star_real_smul, star_sum_sum_eq]
  congr 1
  rw [← sum_centredCube_linearPart hg F.blockSide (fun h π => ((pathHolonomy (pushForward g X) (refineSite b)
    (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) : ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst, ← reversePath_bondContour]
  have hend : refineSite (g.actSite (j + 1) c.1) =
      refineSite b + siteOfCoords j
        (endpoint 0 (bondContour F.blockSide (linearPart g h) (π.trans g.perm.symm) (g.perm.symm c.2))) := by
    rw [(bondContour_spec _ _ hL (linearPart_mem_centredCube hg hh)).2]
    have e1 : g.actSite (j + 1) c.1 =
        b + siteOfCoords (j + 1) (LatticeFractionalIntegration.basisVector (g.perm.symm c.2)) := by
      rw [hbdef, ← unitStep_eq]
      abel
    rw [e1, refineSite_add j hj]
    congr 2
  rw [hend, pathHolonomy_reversePath, coe_unitQuaternion_inv, star_star]
private theorem sum_innerBonds_mapBond {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell}
    (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (inverse g).actSite F.top z ∈ S) {j : ℕ}
    (hj : j ≤ F.top) (f : F.Site j × Fin 4 → M) (f' : F.Site j × Fin 4 → M)
    (h : ∀ c ∈ innerBonds S j, f' (mapBond g j c) = f c) :
    ∑ c ∈ innerBonds S' j, f' c = ∑ c ∈ innerBonds S j, f c := by
  refine (Finset.sum_nbij' (mapBond g j) (mapBond (inverse g) j) (fun c hc => mapBond_mem hg hS hj hc)
    (fun c hc => mapBond_mem (inverse_isSymmetry hg) hS' hj hc) (fun c _ => inverse_mapBond hg c)
    (fun c _ => mapBond_inverse hg c) (fun c hc => (h c hc).symm)).symm
end Bonds
private theorem refineSite_eq_cellCentre (y : F.Site F.top) : refineSite (j := F.depth) y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem logContourLengthsSymmetric : LogContourLengthsSymmetric := by
  intro F W W' g γ hodd hs hg hγ hW
  have hall := ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs
  have h1 : ∀ z ∈ ColdStepAtMirrorFrames.finiteCells F, g.actSite F.top z ∈ ColdStepAtMirrorFrames.finiteCells F :=
    fun _ _ => hall _
  have h2 : ∀ z ∈ ColdStepAtMirrorFrames.finiteCells F,
      (inverse g).actSite F.top z ∈ ColdStepAtMirrorFrames.finiteCells F := fun _ _ => hall _
  have hmean : ∀ c : F.Site F.top × Fin 4, contourAverage (pushForward g W) c = contourAverage W' c := by
    intro c
    have e : pushForward g W = gaugeTransform γ W' := hW
    rw [e, GaugeMotions.contourAverage_gaugeTransform hodd le_rfl γ W' c, refineSite_eq_cellCentre,
      refineSite_eq_cellCentre, hγ, hγ]
    simp
  refine sum_innerBonds_mapBond hg h1 h2 (j := F.top) le_rfl _ _ fun c _ => ?_
  rw [← hmean]
  rcases hg.1 (g.perm.symm c.2) with hs' | hs'
  · rw [contourAverage_mapBond_of_pos hg le_rfl W c hs']
  · rw [contourAverage_mapBond_of_neg hg le_rfl hodd.pos W c hs', norm_star]
end YangMills.Construction.SlopeCoefficient
end
