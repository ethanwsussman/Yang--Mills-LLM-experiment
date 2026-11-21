import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometryProof
import YangMills.Construction.SummableBoundsOfTheFlow.EnergyUnderAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.EnergySymmetry
open BlockAverages BlockAverages.ChartCoordinates LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
private def linearPart (g : CubicSymmetry) (h : Lattice4) : Lattice4 := fun i => g.sign i * h (g.perm i)
private abbrev symmInv (g : CubicSymmetry) : CubicSymmetry :=
  symmetryInverse g
private theorem star_sum_sum {ι κ : Type} (s : Finset ι) (t : Finset κ) (f : ι → κ → ℍ[ℝ]) :
    star (∑ h ∈ s, ∑ π ∈ t, f h π) = ∑ h ∈ s, ∑ π ∈ t, star (f h π) := by
  simp [star_sum]
private theorem quaternion_re_mul_comm (p q : ℍ[ℝ]) : (p * q).re = (q * p).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
private theorem siteCoords_cast_self {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
private theorem sign_mul_self {g : CubicSymmetry} (hg : g.IsSymmetry F) (i : Fin 4) : g.sign i * g.sign i = 1 := by
  rcases hg.1 i with h | h <;> rw [h] <;> norm_num
private theorem actSite_add {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j) (h : Lattice4) :
    g.actSite j (x + siteOfCoords j h) = g.actSite j x + siteOfCoords j (linearPart g h) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add <;> assumption
private theorem symmInv_actSite {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j) :
    (symmInv g).actSite j (g.actSite j x) = x := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_actSite <;> assumption
private theorem symmInv_isSymmetry {g : CubicSymmetry} (hg : g.IsSymmetry F) : (symmInv g).IsSymmetry F := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_isSymmetry <;> assumption
private theorem symmInv_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) : symmInv (symmInv g) = g := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_symmInv <;> assumption
private theorem actSite_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (y : F.Site j) :
    g.actSite j ((symmInv g).actSite j y) = y := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_symmInv <;> assumption
private theorem actSite_injective {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) :
    Function.Injective (g.actSite (F := F) j) :=
  Function.LeftInverse.injective (symmInv_actSite hg j)
private def mapStep (g : CubicSymmetry) (st : PathStep) : PathStep :=
  (g.perm.symm st.1, if g.sign (g.perm.symm st.1) = 1 then st.2 else !st.2)
private theorem linearPart_stepDisplacement {g : CubicSymmetry} (hg : g.IsSymmetry F) (st : PathStep) :
    linearPart g (FlatPairing.stepDisplacement st) = FlatPairing.stepDisplacement (mapStep g st) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linearPart_stepDisplacement <;> assumption
private theorem perm_perm_symm (g : CubicSymmetry) (k : Fin 4) : g.perm (g.perm.symm k) = k := by simp
private theorem linkValue_transport {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j)
    (x : F.Site j) (st : PathStep) :
    linkValue (transportField g X) (g.actSite j x) (mapStep g st) = linkValue X x st := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linkValue_transportField <;> assumption
private theorem pathHolonomy_transport {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (transportField g X) (g.actSite j x) (l.map (mapStep g)) = pathHolonomy X x l := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.pathHolonomy_transportField <;> assumption
section Sites
variable {g : CubicSymmetry} (hg : g.IsSymmetry F)
include hg
private theorem actSite_refineSite {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    g.actSite j (refineSite y) = refineSite (g.actSite (j + 1) y) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_refineSite <;> assumption
private theorem linearPart_mem_centredCube {M : ℕ} {h : Lattice4} (hh : h ∈ centredCube M) :
    linearPart g h ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linearPart_mem_centredCube <;> assumption
private theorem linearPart_symmInv (h : Lattice4) : linearPart (symmInv g) (linearPart g h) = h := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.linearPart_symmInv <;> assumption
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
private theorem map_axisPath (hg : g.IsSymmetry F) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_axisPath <;> assumption
private theorem map_reversePath (l : List PathStep) :
    (reversePath l).map (mapStep g) = reversePath (l.map (mapStep g)) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_reversePath <;> assumption
private theorem map_bondContour (hg : g.IsSymmetry F) (L : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) ++
      List.replicate L (mapStep g (i, true)) ++ reversePath (axisPath (linearPart g h) (π.trans g.perm.symm)) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.map_bondContour <;> assumption
private theorem reversePath_bondContour (L : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
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
private theorem mapBond_symmInv_mapBond {j : ℕ} (c : F.Site j × Fin 4) : mapBond (symmInv g) j (mapBond g j c) = c := by
  obtain ⟨y, i⟩ := c
  have hp : (symmInv g).perm.symm (g.perm.symm i) = i := by
    show g.perm (g.perm.symm i) = i
    simp
  have hsg : (symmInv g).sign i = g.sign (g.perm.symm i) := rfl
  unfold mapBond
  rcases hg.1 (g.perm.symm i) with hs | hs
  · simp only [if_pos hs, hp, hsg, symmInv_actSite hg]
  · simp only [if_neg (show ¬ g.sign (g.perm.symm i) = 1 by rw [hs]; norm_num), hp, hsg]
    rw [← actSite_add_unitStep_of_neg hg y hs, symmInv_actSite hg]
    simp
private theorem mapBond_mapBond_symmInv {j : ℕ} (c : F.Site j × Fin 4) : mapBond g j (mapBond (symmInv g) j c) = c := by
  have := mapBond_symmInv_mapBond (symmInv_isSymmetry hg) c
  rwa [symmInv_symmInv hg] at this
private theorem sum_centredCube_linearPart {M : Type} [AddCommMonoid M] (L : ℕ)
    (f : Lattice4 → Equiv.Perm (Fin 4) → M) :
    ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f (linearPart g h) (π.trans g.perm.symm) =
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.sum_centredCube_perm <;> assumption
private theorem pathHolonomy_bondContour {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j) (y : F.Site (j + 1))
    (L : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathHolonomy X (refineSite y) (bondContour L h π i) =
      pathHolonomy (transportField g X) (refineSite (g.actSite (j + 1) y))
        (axisPath (linearPart g h) (π.trans g.perm.symm) ++ List.replicate L (mapStep g (i, true)) ++
          reversePath (axisPath (linearPart g h) (π.trans g.perm.symm))) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.pathHolonomy_bondContour <;> assumption
private theorem contourAverage_mapBond_of_pos {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (hs : g.sign (g.perm.symm c.2) = 1) :
    contourAverage (transportField g X) (mapBond g (j + 1) c) = contourAverage X c := by
  have hb : mapBond g (j + 1) c = (g.actSite (j + 1) c.1, g.perm.symm c.2) := by
    unfold mapBond
    rw [if_pos hs]
  have hst : mapStep g (c.2, true) = (g.perm.symm c.2, true) := by
    simp [mapStep, hs]
  rw [hb]
  unfold contourAverage
  congr 1
  rw [← sum_centredCube_linearPart hg F.blockSide (fun h π => ((pathHolonomy (transportField g X)
    (refineSite (g.actSite (j + 1) c.1)) (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) : ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst]
  rfl
private theorem contourAverage_mapBond_of_neg {j : ℕ} (hj : j + 1 ≤ F.top) (hL : 1 ≤ F.blockSide)
    (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (hs : g.sign (g.perm.symm c.2) = -1) :
    contourAverage (transportField g X) (mapBond g (j + 1) c) = star (contourAverage X c) := by
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
  rw [quaternion_star_real_smul, star_sum_sum]
  congr 1
  rw [← sum_centredCube_linearPart hg F.blockSide (fun h π => ((pathHolonomy (transportField g X) (refineSite b)
    (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) : ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst, ← reversePath_bondContour]
  have hend : refineSite (g.actSite (j + 1) c.1) =
      refineSite b + siteOfCoords j
        (endpoint 0 (bondContour F.blockSide (linearPart g h) (π.trans g.perm.symm) (g.perm.symm c.2))) := by
    rw [(bondContour_spec _ _ hL (linearPart_mem_centredCube hg hh)).2]
    have e1 : g.actSite (j + 1) c.1 = b + siteOfCoords (j + 1) (basisVector (g.perm.symm c.2)) := by
      rw [hbdef, ← unitStep_eq]
      abel
    rw [e1, refineSite_add j hj]
    congr 2
  rw [hend, pathHolonomy_reversePath, coe_unitQuaternion_inv, star_star]
private theorem transportField_mapBond_of_pos {j : ℕ} (X : F.GaugeField j) (c : F.Site j × Fin 4)
    (hs : g.sign (g.perm.symm c.2) = 1) :
    transportField g X (mapBond g j c).1 (mapBond g j c).2 = X c.1 c.2 := by
  have hb : mapBond g j c = (g.actSite j c.1, g.perm.symm c.2) := by
    unfold mapBond
    rw [if_pos hs]
  rw [hb]
  simp only [transportField, hs, decide_true, linkValue, if_true, symmInv_actSite hg, perm_perm_symm]
private theorem transportField_mapBond_of_neg {j : ℕ} (X : F.GaugeField j) (c : F.Site j × Fin 4)
    (hs : g.sign (g.perm.symm c.2) = -1) :
    transportField g X (mapBond g j c).1 (mapBond g j c).2 = (X c.1 c.2)⁻¹ := by
  have hne : ¬ g.sign (g.perm.symm c.2) = 1 := by
    rw [hs]
    norm_num
  have hb : mapBond g j c = (g.actSite j c.1 - unitStep j (g.perm.symm c.2), g.perm.symm c.2) := by
    unfold mapBond
    rw [if_neg hne]
  rw [hb]
  simp only [transportField, hne, decide_false, linkValue, Bool.false_eq_true, if_false, perm_perm_symm]
  rw [← actSite_add_unitStep_of_neg hg c.1 hs, symmInv_actSite hg]
  simp
private theorem blockFit_transport {j : ℕ} (hj : j + 1 ≤ F.top) (hL : 1 ≤ F.blockSide) (X : F.GaugeField j)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (transportField g X) (transportField g X') (mapBond g (j + 1) c) = blockFit X X' c := by
  unfold blockFit
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · rw [contourAverage_mapBond_of_pos hg hj X c hs, transportField_mapBond_of_pos hg X' c hs]
  · rw [contourAverage_mapBond_of_neg hg hj hL X c hs, transportField_mapBond_of_neg hg X' c hs, norm_star]
    congr 1
    rw [_root_.inv_inv, coe_unitQuaternion_inv, quaternion_re_mul_comm, ← Quaternion.re_star, star_mul, star_star]
private theorem sum_innerBonds_mapBond {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell}
    (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S) {j : ℕ} (hj : j ≤ F.top)
    (f : F.Site j × Fin 4 → M) (f' : F.Site j × Fin 4 → M) (h : ∀ c ∈ innerBonds S j, f' (mapBond g j c) = f c) :
    ∑ c ∈ innerBonds S' j, f' c = ∑ c ∈ innerBonds S j, f c := by
  refine (Finset.sum_nbij' (mapBond g j) (mapBond (symmInv g) j) (fun c hc => mapBond_mem hg hS hj hc)
    (fun c hc => mapBond_mem (symmInv_isSymmetry hg) hS' hj hc) (fun c _ => mapBond_symmInv_mapBond hg c)
    (fun c _ => mapBond_mapBond_symmInv hg c) (fun c hc => (h c hc).symm)).symm
end Bonds
section Loops
variable {j : ℕ}
private def plaquetteLoop (α β : Fin 4) : List PathStep := [(α, true), (β, true), (α, false), (β, false)]
private theorem re_coe_inv (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.TorusFields.re_unitQuaternion_inv <;> assumption
private theorem endpoint_plaquetteLoop (α β : Fin 4) : endpoint 0 (plaquetteLoop α β) = 0 := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.endpoint_plaquetteLoop <;> assumption
private theorem re_pathHolonomy_plaquetteLoop_swap (X : F.GaugeField j) (z : F.Site j) (α β : Fin 4) :
    ((pathHolonomy X z (plaquetteLoop α β) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy X z (plaquetteLoop β α) : UnitQuaternion) : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.re_pathHolonomy_plaquetteLoop_swap <;> assumption
private theorem re_pathHolonomy_rotate (X : F.GaugeField j) (z : F.Site j) (a : PathStep) (r : List PathStep)
    (hr : endpoint 0 (a :: r) = 0) :
    ((pathHolonomy X z (a :: r) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy X (z + stepDisplacement j a) (r ++ [a]) : UnitQuaternion) : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.re_pathHolonomy_rotate <;> assumption
end Loops
section Images
variable {g : CubicSymmetry}
private def mapCorner (g : CubicSymmetry) (j : ℕ) (x : F.Site j) (μ ν : Fin 4) : F.Site j :=
  g.actSite j x + (if g.sign (g.perm.symm μ) = 1 then 0 else - unitStep j (g.perm.symm μ)) +
    (if g.sign (g.perm.symm ν) = 1 then 0 else - unitStep j (g.perm.symm ν))
private theorem re_pathHolonomy_plaquetteLoop_transport (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j)
    (x : F.Site j) (μ ν : Fin 4) :
    ((pathHolonomy X x (plaquetteLoop μ ν) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy (transportField g X) (mapCorner g j x μ ν)
        (plaquetteLoop (g.perm.symm μ) (g.perm.symm ν)) : UnitQuaternion) : ℍ[ℝ]).re := by
  rw [← pathHolonomy_transport hg X (plaquetteLoop μ ν) x]
  generalize transportField g X = P
  rcases hg.1 (g.perm.symm μ) with h1 | h1 <;> rcases hg.1 (g.perm.symm ν) with h2 | h2
  · have e : (plaquetteLoop μ ν).map (mapStep g) = plaquetteLoop (g.perm.symm μ) (g.perm.symm ν) := by
      simp [plaquetteLoop, mapStep, h1, h2]
    rw [e]
    simp [mapCorner, h1, h2]
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, true) :: [(g.perm.symm ν, false),
        (g.perm.symm μ, false), (g.perm.symm ν, true)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : endpoint 0 ((g.perm.symm μ, true) :: [(g.perm.symm ν, false), (g.perm.symm μ, false),
        (g.perm.symm ν, true)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    have z2 : endpoint 0 ((g.perm.symm ν, false) :: [(g.perm.symm μ, false), (g.perm.symm ν, true),
        (g.perm.symm μ, true)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    have z3 : endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, true), (g.perm.symm μ, true),
        (g.perm.symm ν, false)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z2]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z3]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, true) + stepDisplacement j (g.perm.symm ν, false) +
        stepDisplacement j (g.perm.symm μ, false) = mapCorner g j x μ ν := by
      simp [mapCorner, stepDisplacement, h1, h2]
      abel
    rw [e2]
    exact re_pathHolonomy_plaquetteLoop_swap P _ _ _ |>.symm
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, false) :: [(g.perm.symm ν, true),
        (g.perm.symm μ, true), (g.perm.symm ν, false)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, true), (g.perm.symm μ, true),
        (g.perm.symm ν, false)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, false) = mapCorner g j x μ ν := by
      simp [mapCorner, stepDisplacement, h1, h2]
    rw [e2]
    exact re_pathHolonomy_plaquetteLoop_swap P _ _ _ |>.symm
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, false) :: [(g.perm.symm ν, false),
        (g.perm.symm μ, true), (g.perm.symm ν, true)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, false), (g.perm.symm μ, true),
        (g.perm.symm ν, true)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    have z2 : endpoint 0 ((g.perm.symm ν, false) :: [(g.perm.symm μ, true), (g.perm.symm ν, true),
        (g.perm.symm μ, false)]) = 0 := by
      funext i
      simp [endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z2]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, false) + stepDisplacement j (g.perm.symm ν, false) =
        mapCorner g j x μ ν := by
      simp [mapCorner, stepDisplacement, h1, h2]
    rw [e2]
    rfl
end Images
section Plaquettes
variable {g : CubicSymmetry}
private def mapPlaquette (g : CubicSymmetry) (j : ℕ) (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 × Fin 4 :=
  (mapCorner g j p.1 p.2.1 p.2.2, min (g.perm.symm p.2.1) (g.perm.symm p.2.2),
    max (g.perm.symm p.2.1) (g.perm.symm p.2.2))
private theorem plaquetteCorners_swap {j : ℕ} (z : F.Site j) (α β : Fin 4) :
    plaquetteCorners (z, α, β) = plaquetteCorners (z, β, α) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.plaquetteCorners_swap <;> assumption
section Sets
variable {A : Type} [AddCommGroup A] [DecidableEq A] (u a b : A)
private theorem corners_pos_pos : ({u + 0 + 0, u + 0 + 0 + a, u + 0 + 0 + b, u + 0 + 0 + a + b} : Finset A) =
    {u, u + a, u + b, u + a + b} := by
  simp
private theorem corners_pos_neg : ({u + 0 + -b, u + 0 + -b + a, u + 0 + -b + b, u + 0 + -b + a + b} : Finset A) =
    {u, u + a, u - b, u + a - b} := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.corner_set_pos_neg <;> assumption
private theorem corners_neg_pos : ({u + -a + 0, u + -a + 0 + a, u + -a + 0 + b, u + -a + 0 + a + b} : Finset A) =
    {u, u - a, u + b, u - a + b} := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.corner_set_neg_pos <;> assumption
private theorem corners_neg_neg :
    ({u + -a + -b, u + -a + -b + a, u + -a + -b + b, u + -a + -b + a + b} : Finset A) =
      {u, u - a, u - b, u - a - b} := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.corner_set_neg_neg <;> assumption
end Sets
variable (hg : g.IsSymmetry F)
include hg
private theorem re_plaquetteHolonomy_transport {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    ((plaquetteHolonomy (transportField g X) (mapPlaquette g j p) : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]).re := by
  obtain ⟨x, μ, ν⟩ := p
  have h := re_pathHolonomy_plaquetteLoop_transport hg X x μ ν
  show ((pathHolonomy (transportField g X) (mapCorner g j x μ ν)
    (plaquetteLoop (min (g.perm.symm μ) (g.perm.symm ν)) (max (g.perm.symm μ) (g.perm.symm ν))) :
      UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy X x (plaquetteLoop μ ν) : UnitQuaternion) : ℍ[ℝ]).re
  rw [h]
  rcases le_total (g.perm.symm μ) (g.perm.symm ν) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
  · rw [min_eq_right hle, max_eq_left hle]
    exact re_pathHolonomy_plaquetteLoop_swap _ _ _ _
private theorem plaquetteCorners_mapPlaquette {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteCorners (mapPlaquette g j p) = (plaquetteCorners p).image (g.actSite j) := by
  obtain ⟨x, μ, ν⟩ := p
  have hc : plaquetteCorners (mapPlaquette g j (x, μ, ν)) =
      plaquetteCorners (mapCorner g j x μ ν, g.perm.symm μ, g.perm.symm ν) := by
    simp only [mapPlaquette]
    rcases le_total (g.perm.symm μ) (g.perm.symm ν) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]
      exact plaquetteCorners_swap _ _ _
  rw [hc]
  simp only [plaquetteCorners, Finset.image_insert, Finset.image_singleton]
  rcases hg.1 (g.perm.symm μ) with h1 | h1 <;> rcases hg.1 (g.perm.symm ν) with h2 | h2
  · simp only [mapCorner, h1, h2, if_true]
    rw [actSite_add_unitStep_of_pos hg _ h1, actSite_add_unitStep_of_pos hg _ h2, actSite_add_unitStep_of_pos hg _ h2,
      actSite_add_unitStep_of_pos hg _ h1, corners_pos_pos]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [mapCorner, h1, h2, if_true, if_neg n2]
    rw [actSite_add_unitStep_of_pos hg _ h1, actSite_add_unitStep_of_neg hg _ h2, actSite_add_unitStep_of_neg hg _ h2,
      actSite_add_unitStep_of_pos hg _ h1, corners_pos_neg]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [mapCorner, h1, h2, if_true, if_neg n2]
    rw [actSite_add_unitStep_of_neg hg _ h1, actSite_add_unitStep_of_pos hg _ h2, actSite_add_unitStep_of_pos hg _ h2,
      actSite_add_unitStep_of_neg hg _ h1, corners_neg_pos]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [mapCorner, h1, h2, if_neg n2]
    rw [actSite_add_unitStep_of_neg hg _ h1, actSite_add_unitStep_of_neg hg _ h2, actSite_add_unitStep_of_neg hg _ h2,
      actSite_add_unitStep_of_neg hg _ h1, corners_neg_neg]
private theorem mapPlaquette_mem {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S')
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) : mapPlaquette g 0 p ∈ innerPlaquettes S' 0 := by
  have hf := Finset.mem_filter.1 hp
  have hsub : plaquetteCorners (mapPlaquette g 0 p) ⊆ sitesOfCells S' 0 := by
    rw [plaquetteCorners_mapPlaquette hg]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact actSite_mem_sitesOfCells hg hS (Nat.zero_le _) (hf.2.2 hx)
  have h0 : (mapPlaquette g 0 p).1 ∈ sitesOfCells S' 0 := hsub (by simp [plaquetteCorners])
  have hne : g.perm.symm p.2.1 ≠ g.perm.symm p.2.2 := fun e => (ne_of_lt hf.2.1) (g.perm.symm.injective e)
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h0, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩,
    ?_, hsub⟩
  exact min_lt_max.2 hne
private theorem mapPlaquette_inj {S : Finset F.Cell} {p q : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0)
    (hq : q ∈ innerPlaquettes S 0) (h : mapPlaquette g 0 p = mapPlaquette g 0 q) : p = q := by
  obtain ⟨x₁, μ₁, ν₁⟩ := p
  obtain ⟨x₂, μ₂, ν₂⟩ := q
  have l1 : μ₁ < ν₁ := (Finset.mem_filter.1 hp).2.1
  have l2 : μ₂ < ν₂ := (Finset.mem_filter.1 hq).2.1
  simp only [mapPlaquette, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  have key : (g.perm.symm μ₁ = g.perm.symm μ₂ ∧ g.perm.symm ν₁ = g.perm.symm ν₂) ∨
      (g.perm.symm μ₁ = g.perm.symm ν₂ ∧ g.perm.symm ν₁ = g.perm.symm μ₂) := by
    rcases le_total (g.perm.symm μ₁) (g.perm.symm ν₁) with a1 | a1 <;>
      rcases le_total (g.perm.symm μ₂) (g.perm.symm ν₂) with a2 | a2
    · rw [min_eq_left a1, min_eq_left a2] at h1
      rw [max_eq_right a1, max_eq_right a2] at h2
      exact Or.inl ⟨h1, h2⟩
    · rw [min_eq_left a1, min_eq_right a2] at h1
      rw [max_eq_right a1, max_eq_left a2] at h2
      exact Or.inr ⟨h1, h2⟩
    · rw [min_eq_right a1, min_eq_left a2] at h1
      rw [max_eq_left a1, max_eq_right a2] at h2
      exact Or.inr ⟨h2, h1⟩
    · rw [min_eq_right a1, min_eq_right a2] at h1
      rw [max_eq_left a1, max_eq_left a2] at h2
      exact Or.inl ⟨h2, h1⟩
  have inj := g.perm.symm.injective
  rcases key with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · obtain rfl := inj e1
    obtain rfl := inj e2
    simp only [mapCorner] at h0
    have := actSite_injective hg 0 (add_right_cancel (add_right_cancel h0))
    rw [this]
  · have e1' := inj e1
    have e2' := inj e2
    subst e1' e2'
    exact absurd l1 (not_lt.2 l2.le)
private theorem sum_innerPlaquettes_mapPlaquette {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell}
    (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S)
    (f f' : F.Site 0 × Fin 4 × Fin 4 → M) (h : ∀ p ∈ innerPlaquettes S 0, f' (mapPlaquette g 0 p) = f p) :
    ∑ q ∈ innerPlaquettes S' 0, f' q = ∑ p ∈ innerPlaquettes S 0, f p := by
  classical
  have i1 : Set.InjOn (mapPlaquette g 0) (innerPlaquettes S 0 : Set (F.Site 0 × Fin 4 × Fin 4)) :=
    fun p hp q hq e => mapPlaquette_inj hg hp hq e
  have i2 : Set.InjOn (mapPlaquette (symmInv g) 0) (innerPlaquettes S' 0 : Set (F.Site 0 × Fin 4 × Fin 4)) :=
    fun p hp q hq e => mapPlaquette_inj (symmInv_isSymmetry hg) hp hq e
  have c2 : (innerPlaquettes S' 0).card ≤ (innerPlaquettes S 0).card :=
    Finset.card_le_card_of_injOn _ (fun q hq => mapPlaquette_mem (symmInv_isSymmetry hg) hS' hq) i2
  have himg : (innerPlaquettes S 0).image (mapPlaquette g 0) = innerPlaquettes S' 0 := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact mapPlaquette_mem hg hS hp
    · rw [Finset.card_image_of_injOn i1]
      exact c2
  rw [← himg, Finset.sum_image i1]
  exact Finset.sum_congr rfl h
end Plaquettes
private theorem transportField_symmInv_transportField {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ}
    (X : F.GaugeField j) : transportField (symmInv g) (transportField g X) = X := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.transportField_symmInv <;> assumption
private theorem transportField_eq_of_transports {g : CubicSymmetry} (hg : g.IsSymmetry F)
    {V V' : F.GaugeField F.top} (hC : g.TransportsField V V') : transportField g V = V' := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.transportField_eq_of_transports <;> assumption
private theorem transportField_transportField_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ}
    (X : F.GaugeField j) : transportField g (transportField (symmInv g) X) = X := by
  have := transportField_symmInv_transportField (symmInv_isSymmetry hg) X
  rwa [symmInv_symmInv hg] at this
private theorem minimalAction_transport {g : CubicSymmetry} (hg : g.IsSymmetry F) (hodd : Odd F.blockSide)
    {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S)
    (a : ℝ) :
    ∀ (j : ℕ), j ≤ F.top → ∀ X : F.GaugeField j, minimalAction a S' j (transportField g X) = minimalAction a S j X := by
  intro j
  induction j with
  | zero =>
    intro _ X
    show wilsonAction S' (transportField g X) = wilsonAction S X
    exact sum_innerPlaquettes_mapPlaquette hg hS hS' _ _ fun p _ => by rw [re_plaquetteHolonomy_transport hg]
  | succ j ih =>
    intro hj X
    have hj' : j ≤ F.top := by omega
    show (⨅ W : F.GaugeField j, (minimalAction a S' j W +
        a * ∑ c ∈ innerBonds S' (j + 1), blockFit W (transportField g X) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W X c)
    let e : F.GaugeField j ≃ F.GaugeField j :=
      ⟨transportField g, transportField (symmInv g), transportField_symmInv_transportField hg,
        transportField_transportField_symmInv hg⟩
    rw [← e.iInf_comp]
    refine iInf_congr fun W => ?_
    show minimalAction a S' j (transportField g W) +
      a * ∑ c ∈ innerBonds S' (j + 1), blockFit (transportField g W) (transportField g X) c = _
    rw [ih hj' W, sum_innerBonds_mapBond hg hS hS' hj _ _ fun c _ => blockFit_transport hg hj hodd.pos _ _ c]
theorem blockEnergySymmetric : BlockEnergySymmetric := by
  intro F a S S' V V' g hodd hg hS hC
  have h1 : ∀ z ∈ S, g.actSite F.top z ∈ S' := fun z hz => (hS z).1 hz
  have h2 : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S := fun z hz => by
    rw [hS, actSite_symmInv hg]
    exact hz
  refine ⟨fun W => ?_, fun W' => ⟨transportField (symmInv g) W', transportField_transportField_symmInv hg W'⟩,
    fun W x k => ?_⟩
  · have hpush := transportField_eq_of_transports hg hC
    unfold blockEnergy
    rw [← hpush]
    show minimalAction a S' F.depth (transportField g W) +
      a * ∑ c ∈ innerBonds S' (F.depth + 1), blockFit (transportField g W) (transportField g V) c = _
    rw [minimalAction_transport hg hodd h1 h2 a F.depth (by simp [BlockFrame.top]) W,
      sum_innerBonds_mapBond hg h1 h2 (j := F.depth + 1) le_rfl _ _ fun c _ => blockFit_transport hg le_rfl hodd.pos _ _ c]
  · show linkValue (transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k
    have h := linkValue_transport hg W x (k, true)
    simpa [mapStep, CubicSymmetry.actStep, linkValue] using h
end YangMills.Construction.EnergySymmetry
end
