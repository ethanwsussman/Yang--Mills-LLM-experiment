import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABondProof
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAGauge
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace SymmetryTransport
variable {F : BlockFrame}
def linearPart (g : CubicSymmetry) (h : LatticeFractionalIntegration.Lattice4) :
    LatticeFractionalIntegration.Lattice4 := fun i => g.sign i * h (g.perm i)
def symmInv (g : CubicSymmetry) : CubicSymmetry :=
  ⟨g.perm⁻¹, fun i => g.sign (g.perm⁻¹ i), fun i => - (g.sign (g.perm⁻¹ i) * g.shift (g.perm⁻¹ i))⟩
theorem star_sum_sum_quaternion {ι κ : Type} (s : Finset ι) (t : Finset κ) (f : ι → κ → ℍ[ℝ]) :
    star (∑ h ∈ s, ∑ π ∈ t, f h π) = ∑ h ∈ s, ∑ π ∈ t, star (f h π) := by
  simp [star_sum]
theorem quaternion_re_mul_comm (p q : ℍ[ℝ]) : (p * q).re = (q * p).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem intCast_eq_of_symmetry {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (i i' : Fin 4) {a b : ℤ}
    (h : (a : ZMod (F.period j i')) = (b : ZMod (F.period j i'))) :
    (a : ZMod (F.period j i)) = (b : ZMod (F.period j i)) := by
  have e : F.period j i = F.period j i' := by
    simp only [BlockFrame.period]
    rw [hg.2 i i']
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  rwa [e]
theorem siteCoords_cast_self {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem sign_mul_self {g : CubicSymmetry} (hg : g.IsSymmetry F) (i : Fin 4) : g.sign i * g.sign i = 1 := by
  rcases hg.1 i with h | h <;> rw [h] <;> norm_num
theorem actSite_add {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j)
    (h : LatticeFractionalIntegration.Lattice4) :
    g.actSite j (x + siteOfCoords j h) = g.actSite j x + siteOfCoords j (linearPart g h) := by
  funext i
  have e := intCast_eq_of_symmetry hg j i (g.perm i) (siteCoords_add_cast x h (g.perm i))
  show ((g.sign i * siteCoords (x + siteOfCoords j h) (g.perm i) + (F.blockSide : ℤ) ^ (F.top - j) * g.shift i : ℤ) :
      ZMod (F.period j i)) =
    ((g.sign i * siteCoords x (g.perm i) + (F.blockSide : ℤ) ^ (F.top - j) * g.shift i : ℤ) : ZMod (F.period j i)) +
      ((g.sign i * h (g.perm i) : ℤ) : ZMod (F.period j i))
  push_cast at e ⊢
  rw [e]
  ring
theorem symmInv_actSite {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j) :
    (symmInv g).actSite j (g.actSite j x) = x := by
  funext i
  have hι : g.perm (g.perm⁻¹ i) = i := by simp
  have e0 : ((siteCoords (g.actSite j x) (g.perm⁻¹ i) : ℤ) : ZMod (F.period j (g.perm⁻¹ i))) =
      ((g.sign (g.perm⁻¹ i) * siteCoords x i + (F.blockSide : ℤ) ^ (F.top - j) * g.shift (g.perm⁻¹ i) : ℤ) :
        ZMod (F.period j (g.perm⁻¹ i))) := by
    rw [siteCoords_cast_self]
    show ((g.sign (g.perm⁻¹ i) * siteCoords x (g.perm (g.perm⁻¹ i)) +
      (F.blockSide : ℤ) ^ (F.top - j) * g.shift (g.perm⁻¹ i) : ℤ) : ZMod (F.period j (g.perm⁻¹ i))) = _
    rw [hι]
  have e := intCast_eq_of_symmetry hg j i (g.perm⁻¹ i) e0
  have hs : ((g.sign (g.perm⁻¹ i) : ℤ) : ZMod (F.period j i)) *
      ((g.sign (g.perm⁻¹ i) : ℤ) : ZMod (F.period j i)) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod (F.period j i))) (sign_mul_self hg (g.perm⁻¹ i))
    simpa using this
  show ((g.sign (g.perm⁻¹ i) * siteCoords (g.actSite j x) (g.perm⁻¹ i) + (F.blockSide : ℤ) ^ (F.top - j) *
      (- (g.sign (g.perm⁻¹ i) * g.shift (g.perm⁻¹ i))) : ℤ) : ZMod (F.period j i)) = x i
  push_cast at e ⊢
  rw [e, ← siteCoords_cast_self x i]
  linear_combination (((siteCoords x i : ℤ) : ZMod (F.period j i))) * hs
theorem symmInv_isSymmetry {g : CubicSymmetry} (hg : g.IsSymmetry F) : (symmInv g).IsSymmetry F :=
  ⟨fun i => hg.1 _, hg.2⟩
theorem symmInv_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) : symmInv (symmInv g) = g := by
  obtain ⟨p, s, t⟩ := g
  have hs := fun i => sign_mul_self (g := ⟨p, s, t⟩) hg i
  simp only [symmInv, _root_.inv_inv, Equiv.Perm.inv_def, Equiv.symm_symm] at hs ⊢
  have e : ∀ i, p.symm (p i) = i := fun i => p.symm_apply_apply i
  congr 1
  · funext i
    simp [e]
  · funext i
    simp only [e]
    have := hs i
    linear_combination (t i) * this
theorem actSite_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (y : F.Site j) :
    g.actSite j ((symmInv g).actSite j y) = y := by
  have := symmInv_actSite (symmInv_isSymmetry hg) j y
  rwa [symmInv_symmInv hg] at this
theorem actSite_injective {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) :
    Function.Injective (g.actSite (F := F) j) :=
  Function.LeftInverse.injective (symmInv_actSite hg j)
def mapStep (g : CubicSymmetry) (st : PathStep) : PathStep :=
  (g.perm.symm st.1, if g.sign (g.perm.symm st.1) = 1 then st.2 else !st.2)
theorem linearPart_stepDisplacement {g : CubicSymmetry} (hg : g.IsSymmetry F) (st : PathStep) :
    linearPart g (FlatPairing.stepDisplacement st) = FlatPairing.stepDisplacement (mapStep g st) := by
  obtain ⟨k, b⟩ := st
  funext i
  by_cases h : i = g.perm.symm k
  · subst h
    have hp : g.perm (g.perm.symm k) = k := by simp
    rcases hg.1 (g.perm.symm k) with hs | hs <;> cases b <;>
      simp [linearPart, FlatPairing.stepDisplacement, mapStep, LatticeFractionalIntegration.basisVector, hs, hp]
  · have hp : g.perm i ≠ k := fun e => h (by rw [← e]; simp)
    cases b <;> by_cases hs : g.sign (g.perm.symm k) = 1 <;>
      simp [linearPart, FlatPairing.stepDisplacement, mapStep, LatticeFractionalIntegration.basisVector, hs,
        Pi.single_eq_of_ne hp, Pi.single_eq_of_ne h]
theorem actSite_add_stepDisplacement {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j)
    (st : PathStep) :
    g.actSite j (x + stepDisplacement j st) = g.actSite j x + stepDisplacement j (mapStep g st) := by
  rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, ChartCoordinates.stepDisplacement_eq_siteOfCoords,
    actSite_add hg, linearPart_stepDisplacement hg]
def transportField (g : CubicSymmetry) {j : ℕ} (X : F.GaugeField j) : F.GaugeField j :=
  fun y i => linkValue X ((symmInv g).actSite j y) (g.perm i, decide (g.sign i = 1))
theorem perm_perm_symm (g : CubicSymmetry) (k : Fin 4) : g.perm (g.perm.symm k) = k := by simp
theorem linkValue_transportField {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j)
    (x : F.Site j) (st : PathStep) :
    linkValue (transportField g X) (g.actSite j x) (mapStep g st) = linkValue X x st := by
  obtain ⟨k, b⟩ := st
  have hk := perm_perm_symm g k
  set i := g.perm.symm k with hi
  have hpos : g.actSite j (x + unitStep j k) = g.actSite j x + stepDisplacement j (mapStep g (k, true)) := by
    have := actSite_add_stepDisplacement hg j x (k, true)
    simpa [stepDisplacement] using this
  have hneg : g.actSite j (x - unitStep j k) = g.actSite j x + stepDisplacement j (mapStep g (k, false)) := by
    have := actSite_add_stepDisplacement hg j x (k, false)
    simpa [stepDisplacement, sub_eq_add_neg] using this
  rcases hg.1 i with hs | hs
  · cases b
    · have e1 : mapStep g (k, false) = (i, false) := by
        simp [mapStep, ← hi, hs]
      have e2 : g.actSite j (x - unitStep j k) = g.actSite j x - unitStep j i := by
        rw [hneg, e1]
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e1]
      simp only [linkValue, Bool.false_eq_true, if_false, transportField, hk, hs, decide_true, if_true]
      rw [← e2, symmInv_actSite hg]
    · have e1 : mapStep g (k, true) = (i, true) := by
        simp [mapStep, ← hi, hs]
      rw [e1]
      simp only [linkValue, if_true, transportField, hk, hs, decide_true]
      rw [symmInv_actSite hg]
  · cases b
    · have e1 : mapStep g (k, false) = (i, true) := by
        simp [mapStep, ← hi, hs]
      rw [e1]
      simp only [linkValue, if_true, transportField, hk, hs]
      rw [symmInv_actSite hg]
      simp
    · have e1 : mapStep g (k, true) = (i, false) := by
        simp [mapStep, ← hi, hs]
      have e2 : g.actSite j (x + unitStep j k) = g.actSite j x - unitStep j i := by
        rw [hpos, e1]
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e1]
      simp only [linkValue, Bool.false_eq_true, if_false, transportField, hk, hs, if_true]
      rw [← e2, symmInv_actSite hg]
      simp
theorem pathHolonomy_transportField {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (transportField g X) (g.actSite j x) (l.map (mapStep g)) = pathHolonomy X x l := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [List.map_cons, pathHolonomy]
    rw [linkValue_transportField hg, ← actSite_add_stepDisplacement hg, ih]
section Sites
variable {g : CubicSymmetry} (hg : g.IsSymmetry F)
include hg
theorem actSite_cellCentre {j : ℕ} (hj : j ≤ F.top) (z : F.Cell) :
    g.actSite j (cellCentre j z) = cellCentre j (g.actSite F.top z) := by
  funext i
  have e1 := intCast_eq_of_symmetry hg j i (g.perm i) (siteCoords_cast (F := F) (j := j)
    (fun i => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i) (g.perm i))
  show ((g.sign i * siteCoords (cellCentre j z) (g.perm i) + (F.blockSide : ℤ) ^ (F.top - j) * g.shift i : ℤ) :
      ZMod (F.period j i)) =
    (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords (g.actSite F.top z) i : ℤ) : ZMod (F.period j i))
  have e3 : (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords (g.actSite F.top z) i : ℤ) : ZMod (F.period j i)) =
      (((F.blockSide : ℤ) ^ (F.top - j) * (g.sign i * siteCoords z (g.perm i) + g.shift i) : ℤ) :
        ZMod (F.period j i)) := by
    refine intCast_mul_eq_of_eq (period_eq_top_mul j hj i) ?_
    rw [siteCoords_cast_self]
    show ((g.sign i * siteCoords z (g.perm i) + (F.blockSide : ℤ) ^ (F.top - F.top) * g.shift i : ℤ) :
      ZMod (F.period F.top i)) = _
    simp
  rw [e3]
  have e4 : ((siteCoords (cellCentre j z) (g.perm i) : ℤ) : ZMod (F.period j i)) =
      (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords z (g.perm i) : ℤ) : ZMod (F.period j i)) := e1
  push_cast at e4 ⊢
  rw [e4]
  ring
theorem actSite_refineSite {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    g.actSite j (refineSite y) = refineSite (g.actSite (j + 1) y) := by
  funext i
  have e1 := intCast_eq_of_symmetry hg j i (g.perm i)
    (siteCoords_cast (F := F) (j := j) (fun i => (F.blockSide : ℤ) * siteCoords y i) (g.perm i))
  show ((g.sign i * siteCoords (refineSite y) (g.perm i) + (F.blockSide : ℤ) ^ (F.top - j) * g.shift i : ℤ) :
      ZMod (F.period j i)) =
    (((F.blockSide : ℤ) * siteCoords (g.actSite (j + 1) y) i : ℤ) : ZMod (F.period j i))
  have e3 : (((F.blockSide : ℤ) * siteCoords (g.actSite (j + 1) y) i : ℤ) : ZMod (F.period j i)) =
      (((F.blockSide : ℤ) * (g.sign i * siteCoords y (g.perm i) + (F.blockSide : ℤ) ^ (F.top - (j + 1)) *
        g.shift i) : ℤ) : ZMod (F.period j i)) := by
    refine intCast_mul_eq_of_eq (period_eq_succ_mul j hj i) ?_
    rw [siteCoords_cast_self]
    rfl
  rw [e3]
  have e4 : ((siteCoords (refineSite y) (g.perm i) : ℤ) : ZMod (F.period j i)) =
      (((F.blockSide : ℤ) * siteCoords y (g.perm i) : ℤ) : ZMod (F.period j i)) := e1
  have e5 : (F.blockSide : ℤ) ^ (F.top - j) = (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by
    have : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [e5]
  push_cast at e4 ⊢
  rw [e4]
  ring
theorem linearPart_mem_centredCube {M : ℕ} {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube M) :
    linearPart g h ∈ centredCube M := by
  rw [LatticePaths.mem_centredCube_iff] at hh ⊢
  intro i
  have h1 := hh (g.perm i)
  rcases hg.1 i with hs | hs <;> simp only [linearPart, hs] <;> constructor <;> linarith [h1.1, h1.2]
theorem linearPart_symmInv (h : LatticeFractionalIntegration.Lattice4) :
    linearPart (symmInv g) (linearPart g h) = h := by
  funext i
  have e : g.perm (g.perm⁻¹ i) = i := by simp
  have hs := sign_mul_self hg (g.perm⁻¹ i)
  show g.sign (g.perm⁻¹ i) * (g.sign (g.perm⁻¹ i) * h (g.perm (g.perm⁻¹ i))) = h i
  rw [e, ← mul_assoc, hs, one_mul]
theorem actSite_mem_sitesOfCells {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') {j : ℕ}
    (hj : j ≤ F.top) {x : F.Site j} (hx : x ∈ sitesOfCells S j) : g.actSite j x ∈ sitesOfCells S' j := by
  obtain ⟨z, hz, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  refine mem_sitesOfCells.2 ⟨_, hS z hz, linearPart g h, linearPart_mem_centredCube hg hh, ?_⟩
  rw [actSite_add hg, actSite_cellCentre hg hj]
theorem enclosingCell_actSite (hodd : Odd F.blockSide) {S : Finset F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells S j) :
    enclosingCell (g.actSite j x) = g.actSite F.top (enclosingCell x) := by
  obtain ⟨z, hz, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [actSite_add hg, actSite_cellCentre hg hj,
    LocalPartition.enclosingCell_cellCentre_add hodd _ _ (linearPart_mem_centredCube hg hh),
    LocalPartition.enclosingCell_cellCentre_add hodd _ _ hh]
end Sites
section Paths
theorem endpoint_zero_cons (st : PathStep) (r : List PathStep) :
    LatticePaths.endpoint 0 (st :: r) = LatticePaths.endpoint 0 r + FlatPairing.stepDisplacement st := by
  have h := LatticePaths.endpoint_add 0 (FlatPairing.stepDisplacement st) r
  show LatticePaths.endpoint (0 + FlatPairing.stepDisplacement st) r = _
  rw [h]
theorem endpoint_zero_reversePath (l : List PathStep) :
    LatticePaths.endpoint 0 (reversePath l) = - LatticePaths.endpoint 0 l := by
  have h1 := LatticePaths.endpoint_reversePath 0 l
  have h2 := LatticePaths.endpoint_add 0 (LatticePaths.endpoint 0 l) (reversePath l)
  rw [zero_add, h1] at h2
  rw [eq_neg_iff_add_eq_zero]
  exact h2.symm
variable {j : ℕ}
theorem add_siteOfCoords_endpoint_cons (x : F.Site j) (st : PathStep) (r : List PathStep) :
    x + siteOfCoords j (LatticePaths.endpoint 0 (st :: r)) =
      x + stepDisplacement j st + siteOfCoords j (LatticePaths.endpoint 0 r) := by
  rw [endpoint_zero_cons, siteOfCoords_add, ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc,
    add_comm (siteOfCoords j (LatticePaths.endpoint 0 r))]
theorem pathHolonomy_append (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + siteOfCoords j (LatticePaths.endpoint 0 l)) l' := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.pathHolonomy_append <;> assumption
theorem pathHolonomy_reversePath (X : F.GaugeField j) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X (x + siteOfCoords j (LatticePaths.endpoint 0 l)) (reversePath l) =
      (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.pathHolonomy_reversePath <;> assumption
end Paths
section Contours
variable {g : CubicSymmetry}
theorem replicate_mapStep (hg : g.IsSymmetry F) (k : Fin 4) (x y : ℤ) (e : y = g.sign (g.perm.symm k) * x) :
    List.replicate x.natAbs (mapStep g (k, decide (0 ≤ x))) =
      List.replicate y.natAbs (g.perm.symm k, decide (0 ≤ y)) := by
  subst e
  by_cases h0 : x = 0
  · subst h0
    simp
  · rcases hg.1 (g.perm.symm k) with hs | hs
    · rw [hs, one_mul]
      simp [mapStep, hs]
    · rw [hs, neg_one_mul, Int.natAbs_neg]
      have e2 : decide (0 ≤ -x) = !decide (0 ≤ x) := by
        by_cases h1 : 0 ≤ x
        · have h2 : ¬ 0 ≤ -x := by omega
          rw [decide_eq_true h1, decide_eq_false h2]
          rfl
        · have h2 : 0 ≤ -x := by omega
          rw [decide_eq_false h1, decide_eq_true h2]
          rfl
      rw [e2]
      simp [mapStep, hs]
theorem map_axisPath (hg : g.IsSymmetry F) (h : LatticeFractionalIntegration.Lattice4) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) := by
  unfold axisPath
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_replicate]
  have hp : g.perm (g.perm.symm (π k)) = π k := by simp
  have e : linearPart g h ((π.trans g.perm.symm) k) = g.sign (g.perm.symm (π k)) * h (π k) := by
    simp only [linearPart, Equiv.trans_apply, hp]
  exact replicate_mapStep hg (π k) _ _ e
theorem map_reversePath (l : List PathStep) :
    (reversePath l).map (mapStep g) = reversePath (l.map (mapStep g)) := by
  unfold reversePath
  simp only [List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun st _ => ?_
  simp only [Function.comp, mapStep]
  split_ifs <;> rfl
theorem map_bondContour (hg : g.IsSymmetry F) (L : ℕ) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).map (mapStep g) = axisPath (linearPart g h) (π.trans g.perm.symm) ++
      List.replicate L (mapStep g (i, true)) ++ reversePath (axisPath (linearPart g h) (π.trans g.perm.symm)) := by
  unfold bondContour
  rw [List.map_append, List.map_append, map_reversePath, map_axisPath hg, List.map_replicate]
theorem reversePath_bondContour (L : ℕ) (h : LatticeFractionalIntegration.Lattice4) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) :
    reversePath (bondContour L h π i) = axisPath h π ++ List.replicate L (i, false) ++
      reversePath (axisPath h π) := by
  unfold bondContour reversePath
  simp [List.reverse_append, List.map_append, List.map_reverse, List.reverse_reverse, Function.comp_def,
    List.reverse_replicate, List.map_replicate, List.append_assoc]
end Contours
section Bonds
variable {g : CubicSymmetry}
def mapBond (g : CubicSymmetry) (j : ℕ) (c : F.Site j × Fin 4) : F.Site j × Fin 4 :=
  if g.sign (g.perm.symm c.2) = 1 then (g.actSite j c.1, g.perm.symm c.2)
  else (g.actSite j c.1 - unitStep j (g.perm.symm c.2), g.perm.symm c.2)
variable (hg : g.IsSymmetry F)
include hg
theorem actSite_add_unitStep_of_pos {j : ℕ} (y : F.Site j) {i : Fin 4} (hs : g.sign (g.perm.symm i) = 1) :
    g.actSite j (y + unitStep j i) = g.actSite j y + unitStep j (g.perm.symm i) := by
  have := actSite_add_stepDisplacement hg j y (i, true)
  simpa [stepDisplacement, mapStep, hs] using this
theorem actSite_add_unitStep_of_neg {j : ℕ} (y : F.Site j) {i : Fin 4} (hs : g.sign (g.perm.symm i) = -1) :
    g.actSite j (y + unitStep j i) = g.actSite j y - unitStep j (g.perm.symm i) := by
  have := actSite_add_stepDisplacement hg j y (i, true)
  simpa [stepDisplacement, mapStep, hs, sub_eq_add_neg] using this
theorem mapBond_mem {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') {j : ℕ} (hj : j ≤ F.top)
    {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) : mapBond g j c ∈ innerBonds S' j := by
  have h1 : c.1 ∈ sitesOfCells S j := (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  have h2 : c.1 + unitStep j c.2 ∈ sitesOfCells S j := (Finset.mem_filter.1 hc).2
  have m1 := actSite_mem_sitesOfCells hg hS hj h1
  have m2 := actSite_mem_sitesOfCells hg hS hj h2
  unfold mapBond
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · rw [if_pos hs]
    rw [actSite_add_unitStep_of_pos hg _ hs] at m2
    exact ChartCoordinates.mem_innerBonds m1 m2
  · rw [if_neg (by rw [hs]; norm_num)]
    rw [actSite_add_unitStep_of_neg hg _ hs] at m2
    exact ChartCoordinates.mem_innerBonds m2 (by rwa [sub_add_cancel])
theorem symmInv_mapBond {j : ℕ} (c : F.Site j × Fin 4) : mapBond (symmInv g) j (mapBond g j c) = c := by
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
theorem mapBond_symmInv {j : ℕ} (c : F.Site j × Fin 4) : mapBond g j (mapBond (symmInv g) j c) = c := by
  have := symmInv_mapBond (symmInv_isSymmetry hg) c
  rwa [symmInv_symmInv hg] at this
theorem sum_centredCube_perm {M : Type} [AddCommMonoid M] (L : ℕ)
    (f : LatticeFractionalIntegration.Lattice4 → Equiv.Perm (Fin 4) → M) :
    ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f (linearPart g h) (π.trans g.perm.symm) =
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π := by
  refine Finset.sum_nbij' (linearPart g) (linearPart (symmInv g)) (fun h hh => linearPart_mem_centredCube hg hh)
    (fun h hh => linearPart_mem_centredCube (symmInv_isSymmetry hg) hh) (fun h _ => linearPart_symmInv hg h)
    (fun h _ => ?_) (fun h _ => ?_)
  · have := linearPart_symmInv (symmInv_isSymmetry hg) h
    rwa [symmInv_symmInv hg] at this
  · exact Fintype.sum_equiv (Equiv.mulLeft g.perm.symm) _ _ fun π => rfl
theorem pathHolonomy_bondContour {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j) (y : F.Site (j + 1)) (L : ℕ)
    (h : LatticeFractionalIntegration.Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathHolonomy X (refineSite y) (bondContour L h π i) =
      pathHolonomy (transportField g X) (refineSite (g.actSite (j + 1) y))
        (axisPath (linearPart g h) (π.trans g.perm.symm) ++ List.replicate L (mapStep g (i, true)) ++
          reversePath (axisPath (linearPart g h) (π.trans g.perm.symm))) := by
  rw [← map_bondContour hg, ← actSite_refineSite hg hj, pathHolonomy_transportField hg]
theorem contourAverage_transport_of_pos {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j)
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
  rw [← sum_centredCube_perm hg F.blockSide (fun h π => ((pathHolonomy (transportField g X)
    (refineSite (g.actSite (j + 1) c.1)) (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) :
      ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst]
  rfl
theorem contourAverage_transport_of_neg {j : ℕ} (hj : j + 1 ≤ F.top) (hL : 1 ≤ F.blockSide) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (hs : g.sign (g.perm.symm c.2) = -1) :
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
  rw [quaternion_star_real_smul, star_sum_sum_quaternion]
  congr 1
  rw [← sum_centredCube_perm hg F.blockSide (fun h π => ((pathHolonomy (transportField g X) (refineSite b)
    (bondContour F.blockSide h π (g.perm.symm c.2)) : UnitQuaternion) : ℍ[ℝ]))]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_bondContour hg hj X c.1 F.blockSide h π c.2, hst, ← reversePath_bondContour]
  have hend : refineSite (g.actSite (j + 1) c.1) =
      refineSite b + siteOfCoords j (LatticePaths.endpoint 0
        (bondContour F.blockSide (linearPart g h) (π.trans g.perm.symm) (g.perm.symm c.2))) := by
    rw [(LatticePaths.bondContour_spec _ _ hL (linearPart_mem_centredCube hg hh)).2]
    have e1 : g.actSite (j + 1) c.1 =
        b + siteOfCoords (j + 1) (LatticeFractionalIntegration.basisVector (g.perm.symm c.2)) := by
      rw [hbdef, ← unitStep_eq]
      abel
    rw [e1, refineSite_add j hj]
    congr 2
  rw [hend, pathHolonomy_reversePath, coe_unitQuaternion_inv, star_star]
theorem transportField_mapBond_of_pos {j : ℕ} (X : F.GaugeField j) (c : F.Site j × Fin 4)
    (hs : g.sign (g.perm.symm c.2) = 1) :
    transportField g X (mapBond g j c).1 (mapBond g j c).2 = X c.1 c.2 := by
  have hb : mapBond g j c = (g.actSite j c.1, g.perm.symm c.2) := by
    unfold mapBond
    rw [if_pos hs]
  rw [hb]
  simp only [transportField, hs, decide_true, linkValue, if_true, symmInv_actSite hg, perm_perm_symm]
theorem transportField_mapBond_of_neg {j : ℕ} (X : F.GaugeField j) (c : F.Site j × Fin 4)
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
theorem blockFit_transport {j : ℕ} (hj : j + 1 ≤ F.top) (hL : 1 ≤ F.blockSide) (X : F.GaugeField j)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (transportField g X) (transportField g X') (mapBond g (j + 1) c) = blockFit X X' c := by
  unfold blockFit
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · rw [contourAverage_transport_of_pos hg hj X c hs, transportField_mapBond_of_pos hg X' c hs]
  · rw [contourAverage_transport_of_neg hg hj hL X c hs, transportField_mapBond_of_neg hg X' c hs, norm_star]
    congr 1
    rw [_root_.inv_inv, coe_unitQuaternion_inv, quaternion_re_mul_comm, ← Quaternion.re_star, star_mul, star_star]
theorem bondWeight_transport (hodd : Odd F.blockSide) {S : Finset F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) (Y : F.Cell) [DecidableEq F.Cell] :
    ((if enclosingCell (mapBond g j c).1 = g.actSite F.top Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell ((mapBond g j c).1 + unitStep j (mapBond g j c).2) = g.actSite F.top Y
          then (1 / 2 : ℝ) else 0)) =
      (if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep j c.2) = Y then (1 / 2 : ℝ) else 0) := by
  have hb := ChartCoordinates.innerBonds_ends hc
  have e1 := enclosingCell_actSite hg hodd hj hb.1
  have e2 := enclosingCell_actSite hg hodd hj hb.2
  have inj := actSite_injective hg F.top
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · have hbm : mapBond g j c = (g.actSite j c.1, g.perm.symm c.2) := by
      unfold mapBond
      rw [if_pos hs]
    rw [actSite_add_unitStep_of_pos hg _ hs] at e2
    rw [hbm]
    simp only [e1, e2, inj.eq_iff]
  · have hne : ¬ g.sign (g.perm.symm c.2) = 1 := by
      rw [hs]
      norm_num
    have hbm : mapBond g j c = (g.actSite j c.1 - unitStep j (g.perm.symm c.2), g.perm.symm c.2) := by
      unfold mapBond
      rw [if_neg hne]
    rw [actSite_add_unitStep_of_neg hg _ hs] at e2
    rw [hbm]
    simp only [sub_add_cancel, e1, e2, inj.eq_iff]
    rw [add_comm]
theorem sum_innerBonds_transport {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell}
    (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S) {j : ℕ}
    (hj : j ≤ F.top) (f : F.Site j × Fin 4 → M) (f' : F.Site j × Fin 4 → M)
    (h : ∀ c ∈ innerBonds S j, f' (mapBond g j c) = f c) :
    ∑ c ∈ innerBonds S' j, f' c = ∑ c ∈ innerBonds S j, f c := by
  refine (Finset.sum_nbij' (mapBond g j) (mapBond (symmInv g) j) (fun c hc => mapBond_mem hg hS hj hc)
    (fun c hc => mapBond_mem (symmInv_isSymmetry hg) hS' hj hc) (fun c _ => symmInv_mapBond hg c)
    (fun c _ => mapBond_symmInv hg c) (fun c hc => (h c hc).symm)).symm
end Bonds
section Loops
variable {j : ℕ}
def plaquetteLoop (α β : Fin 4) : List PathStep := [(α, true), (β, true), (α, false), (β, false)]
theorem re_coe_inv (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.TorusFields.re_unitQuaternion_inv <;> assumption
theorem endpoint_plaquetteLoop (α β : Fin 4) : LatticePaths.endpoint 0 (plaquetteLoop α β) = 0 := by
  funext i
  simp [plaquetteLoop, LatticePaths.endpoint, FlatPairing.stepDisplacement]
theorem re_pathHolonomy_plaquetteLoop_swap (X : F.GaugeField j) (z : F.Site j) (α β : Fin 4) :
    ((pathHolonomy X z (plaquetteLoop α β) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy X z (plaquetteLoop β α) : UnitQuaternion) : ℍ[ℝ]).re := by
  have e : plaquetteLoop α β = reversePath (plaquetteLoop β α) := by
    simp [plaquetteLoop, reversePath]
  have h := pathHolonomy_reversePath X (plaquetteLoop β α) z
  rw [endpoint_plaquetteLoop, siteOfCoords_zero, add_zero, ← e] at h
  rw [h, re_coe_inv]
theorem re_coe_mul_comm (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]).re = ((b * a : UnitQuaternion) : ℍ[ℝ]).re := by
  simp only [Submonoid.coe_mul]
  exact quaternion_re_mul_comm _ _
theorem re_pathHolonomy_rotate (X : F.GaugeField j) (z : F.Site j) (a : PathStep) (r : List PathStep)
    (hr : LatticePaths.endpoint 0 (a :: r) = 0) :
    ((pathHolonomy X z (a :: r) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy X (z + stepDisplacement j a) (r ++ [a]) : UnitQuaternion) : ℍ[ℝ]).re := by
  have e : z + stepDisplacement j a + siteOfCoords j (LatticePaths.endpoint 0 r) = z := by
    rw [← add_siteOfCoords_endpoint_cons, hr, siteOfCoords_zero, add_zero]
  rw [pathHolonomy_append, e]
  simp only [pathHolonomy, mul_one]
  exact re_coe_mul_comm _ _
end Loops
section Images
variable {g : CubicSymmetry}
def imageCorner (g : CubicSymmetry) (j : ℕ) (x : F.Site j) (μ ν : Fin 4) : F.Site j :=
  g.actSite j x + (if g.sign (g.perm.symm μ) = 1 then 0 else - unitStep j (g.perm.symm μ)) +
    (if g.sign (g.perm.symm ν) = 1 then 0 else - unitStep j (g.perm.symm ν))
theorem re_pathHolonomy_image (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    ((pathHolonomy X x (plaquetteLoop μ ν) : UnitQuaternion) : ℍ[ℝ]).re =
      ((pathHolonomy (transportField g X) (imageCorner g j x μ ν)
        (plaquetteLoop (g.perm.symm μ) (g.perm.symm ν)) : UnitQuaternion) : ℍ[ℝ]).re := by
  rw [← pathHolonomy_transportField hg X (plaquetteLoop μ ν) x]
  generalize transportField g X = P
  rcases hg.1 (g.perm.symm μ) with h1 | h1 <;> rcases hg.1 (g.perm.symm ν) with h2 | h2
  · have e : (plaquetteLoop μ ν).map (mapStep g) = plaquetteLoop (g.perm.symm μ) (g.perm.symm ν) := by
      simp [plaquetteLoop, mapStep, h1, h2]
    rw [e]
    simp [imageCorner, h1, h2]
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, true) :: [(g.perm.symm ν, false),
        (g.perm.symm μ, false), (g.perm.symm ν, true)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : LatticePaths.endpoint 0 ((g.perm.symm μ, true) :: [(g.perm.symm ν, false), (g.perm.symm μ, false),
        (g.perm.symm ν, true)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    have z2 : LatticePaths.endpoint 0 ((g.perm.symm ν, false) :: [(g.perm.symm μ, false), (g.perm.symm ν, true),
        (g.perm.symm μ, true)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    have z3 : LatticePaths.endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, true), (g.perm.symm μ, true),
        (g.perm.symm ν, false)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z2]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z3]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, true) + stepDisplacement j (g.perm.symm ν, false) +
        stepDisplacement j (g.perm.symm μ, false) = imageCorner g j x μ ν := by
      simp [imageCorner, stepDisplacement, h1, h2]
      abel
    rw [e2]
    exact re_pathHolonomy_plaquetteLoop_swap P _ _ _ |>.symm
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, false) :: [(g.perm.symm ν, true),
        (g.perm.symm μ, true), (g.perm.symm ν, false)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : LatticePaths.endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, true), (g.perm.symm μ, true),
        (g.perm.symm ν, false)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, false) = imageCorner g j x μ ν := by
      simp [imageCorner, stepDisplacement, h1, h2, sub_eq_add_neg]
    rw [e2]
    exact re_pathHolonomy_plaquetteLoop_swap P _ _ _ |>.symm
  · have e : (plaquetteLoop μ ν).map (mapStep g) = (g.perm.symm μ, false) :: [(g.perm.symm ν, false),
        (g.perm.symm μ, true), (g.perm.symm ν, true)] := by
      simp [plaquetteLoop, mapStep, h1, h2]
    have z1 : LatticePaths.endpoint 0 ((g.perm.symm μ, false) :: [(g.perm.symm ν, false), (g.perm.symm μ, true),
        (g.perm.symm ν, true)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    have z2 : LatticePaths.endpoint 0 ((g.perm.symm ν, false) :: [(g.perm.symm μ, true), (g.perm.symm ν, true),
        (g.perm.symm μ, false)]) = 0 := by
      funext i
      simp [LatticePaths.endpoint, FlatPairing.stepDisplacement]
    rw [e, re_pathHolonomy_rotate P _ _ _ z1]
    simp only [List.cons_append, List.nil_append]
    rw [re_pathHolonomy_rotate P _ _ _ z2]
    simp only [List.cons_append, List.nil_append]
    have e2 : g.actSite j x + stepDisplacement j (g.perm.symm μ, false) + stepDisplacement j (g.perm.symm ν, false) =
        imageCorner g j x μ ν := by
      simp [imageCorner, stepDisplacement, h1, h2, sub_eq_add_neg]
    rw [e2]
    rfl
end Images
section Plaquettes
variable {g : CubicSymmetry}
def mapPlaquette (g : CubicSymmetry) (j : ℕ) (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 × Fin 4 :=
  (imageCorner g j p.1 p.2.1 p.2.2, min (g.perm.symm p.2.1) (g.perm.symm p.2.2),
    max (g.perm.symm p.2.1) (g.perm.symm p.2.2))
theorem plaquetteCorners_swap {j : ℕ} (z : F.Site j) (α β : Fin 4) :
    plaquetteCorners (z, α, β) = plaquetteCorners (z, β, α) := by
  ext y
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton]
  rw [add_right_comm z (unitStep j α) (unitStep j β)]
  tauto
section Sets
variable {A : Type} [AddCommGroup A] [DecidableEq A] (u a b : A)
theorem corner_set_pos_pos : ({u + 0 + 0, u + 0 + 0 + a, u + 0 + 0 + b, u + 0 + 0 + a + b} : Finset A) =
    {u, u + a, u + b, u + a + b} := by
  simp
theorem corner_set_pos_neg : ({u + 0 + -b, u + 0 + -b + a, u + 0 + -b + b, u + 0 + -b + a + b} : Finset A) =
    {u, u + a, u - b, u + a - b} := by
  have e1 : u + 0 + -b = u - b := by abel
  have e2 : u - b + a + b = u + a := by abel
  have e3 : u - b + a = u + a - b := by abel
  have e4 : u - b + b = u := by abel
  rw [e1, e2, e3, e4]
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
theorem corner_set_neg_pos : ({u + -a + 0, u + -a + 0 + a, u + -a + 0 + b, u + -a + 0 + a + b} : Finset A) =
    {u, u - a, u + b, u - a + b} := by
  have e1 : u + -a + 0 = u - a := by abel
  have e2 : u - a + a + b = u + b := by abel
  have e3 : u - a + a = u := by abel
  rw [e1, e2, e3]
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
theorem corner_set_neg_neg : ({u + -a + -b, u + -a + -b + a, u + -a + -b + b, u + -a + -b + a + b} : Finset A) =
    {u, u - a, u - b, u - a - b} := by
  have e1 : u + -a + -b = u - a - b := by abel
  have e2 : u - a - b + a + b = u := by abel
  have e3 : u - a - b + a = u - b := by abel
  have e4 : u - a - b + b = u - a := by abel
  rw [e1, e2, e3, e4]
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
end Sets
variable (hg : g.IsSymmetry F)
include hg
theorem re_plaquetteHolonomy_transport {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    ((plaquetteHolonomy (transportField g X) (mapPlaquette g j p) : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]).re := by
  obtain ⟨x, μ, ν⟩ := p
  have h := re_pathHolonomy_image hg X x μ ν
  show ((pathHolonomy (transportField g X) (imageCorner g j x μ ν)
    (plaquetteLoop (min (g.perm.symm μ) (g.perm.symm ν)) (max (g.perm.symm μ) (g.perm.symm ν))) :
      UnitQuaternion) : ℍ[ℝ]).re = ((pathHolonomy X x (plaquetteLoop μ ν) : UnitQuaternion) : ℍ[ℝ]).re
  rw [h]
  rcases le_total (g.perm.symm μ) (g.perm.symm ν) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
  · rw [min_eq_right hle, max_eq_left hle]
    exact re_pathHolonomy_plaquetteLoop_swap _ _ _ _
theorem plaquetteCorners_mapPlaquette {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteCorners (mapPlaquette g j p) = (plaquetteCorners p).image (g.actSite j) := by
  obtain ⟨x, μ, ν⟩ := p
  have hc : plaquetteCorners (mapPlaquette g j (x, μ, ν)) =
      plaquetteCorners (imageCorner g j x μ ν, g.perm.symm μ, g.perm.symm ν) := by
    simp only [mapPlaquette]
    rcases le_total (g.perm.symm μ) (g.perm.symm ν) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]
      exact plaquetteCorners_swap _ _ _
  rw [hc]
  simp only [plaquetteCorners, Finset.image_insert, Finset.image_singleton]
  rcases hg.1 (g.perm.symm μ) with h1 | h1 <;> rcases hg.1 (g.perm.symm ν) with h2 | h2
  · simp only [imageCorner, h1, h2, if_true]
    rw [actSite_add_unitStep_of_pos hg _ h1, actSite_add_unitStep_of_pos hg _ h2,
      actSite_add_unitStep_of_pos hg _ h2, actSite_add_unitStep_of_pos hg _ h1, corner_set_pos_pos]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [imageCorner, h1, h2, if_true, if_neg n2]
    rw [actSite_add_unitStep_of_pos hg _ h1, actSite_add_unitStep_of_neg hg _ h2,
      actSite_add_unitStep_of_neg hg _ h2, actSite_add_unitStep_of_pos hg _ h1, corner_set_pos_neg]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [imageCorner, h1, h2, if_true, if_neg n2]
    rw [actSite_add_unitStep_of_neg hg _ h1, actSite_add_unitStep_of_pos hg _ h2,
      actSite_add_unitStep_of_pos hg _ h2, actSite_add_unitStep_of_neg hg _ h1, corner_set_neg_pos]
  · have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [imageCorner, h1, h2, if_neg n2]
    rw [actSite_add_unitStep_of_neg hg _ h1, actSite_add_unitStep_of_neg hg _ h2,
      actSite_add_unitStep_of_neg hg _ h2, actSite_add_unitStep_of_neg hg _ h1, corner_set_neg_neg]
theorem mapPlaquette_mem {S S' : Finset F.Cell} (hS : ∀ z ∈ S, g.actSite F.top z ∈ S')
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
theorem mapPlaquette_injOn {S : Finset F.Cell} {p q : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0)
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
    simp only [imageCorner] at h0
    have := actSite_injective hg 0 (add_right_cancel (add_right_cancel h0))
    rw [this]
  · have e1' := inj e1
    have e2' := inj e2
    subst e1' e2'
    exact absurd l1 (not_lt.2 l2.le)
theorem sum_innerPlaquettes_transport {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell}
    (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S)
    (f f' : F.Site 0 × Fin 4 × Fin 4 → M) (h : ∀ p ∈ innerPlaquettes S 0, f' (mapPlaquette g 0 p) = f p) :
    ∑ q ∈ innerPlaquettes S' 0, f' q = ∑ p ∈ innerPlaquettes S 0, f p := by
  classical
  have i1 : Set.InjOn (mapPlaquette g 0) (innerPlaquettes S 0 : Set (F.Site 0 × Fin 4 × Fin 4)) :=
    fun p hp q hq e => mapPlaquette_injOn hg hp hq e
  have i2 : Set.InjOn (mapPlaquette (symmInv g) 0) (innerPlaquettes S' 0 : Set (F.Site 0 × Fin 4 × Fin 4)) :=
    fun p hp q hq e => mapPlaquette_injOn (symmInv_isSymmetry hg) hp hq e
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
theorem plaquetteWeight_transport (hodd : Odd F.blockSide) {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) (Y : F.Cell) [DecidableEq F.Cell] :
    (∑ x ∈ plaquetteCorners (mapPlaquette g 0 p),
        if enclosingCell x = g.actSite F.top Y then (1 / 4 : ℝ) else 0) =
      ∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0 := by
  have hf := Finset.mem_filter.1 hp
  have inj := actSite_injective hg F.top
  rw [plaquetteCorners_mapPlaquette hg, Finset.sum_image fun x _ y _ e => actSite_injective hg 0 e]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [enclosingCell_actSite hg hodd (Nat.zero_le _) (hf.2.2 hx)]
  simp only [inj.eq_iff]
end Plaquettes
def transportChain (g : CubicSymmetry) (X : F.FieldChain) : F.FieldChain := fun _ => transportField g (X _)
section Chains
variable {g : CubicSymmetry} (hg : g.IsSymmetry F) (hodd : Odd F.blockSide) {S S' : Finset F.Cell}
  (hS : ∀ z ∈ S, g.actSite F.top z ∈ S') (hS' : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S)
include hg hodd hS hS'
theorem chainAction_transport (a : ℝ) (X : F.FieldChain) :
    chainAction a S' (transportChain g X) = chainAction a S X := by
  have e0 : wilsonAction S' (transportChain g X 0) = wilsonAction S (X 0) :=
    sum_innerPlaquettes_transport hg hS hS' _ _ fun p _ => by
      rw [show transportChain g X 0 = transportField g (X 0) from rfl, re_plaquetteHolonomy_transport hg]
  have e1 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S' (j + 1),
        blockFit (transportChain g X j) (transportChain g X (j + 1)) c =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 ≤ F.top := Finset.mem_range.1 hj
    exact sum_innerBonds_transport hg hS hS' hj' _ _ fun c _ => blockFit_transport hg hj' hodd.pos _ _ c
  unfold chainAction
  rw [e0, e1]
theorem cellShare_transport (a : ℝ) (Y : F.Cell) (X : F.FieldChain) :
    cellShare a S' (g.actSite F.top Y) (transportChain g X) = cellShare a S Y X := by
  classical
  have e0 : ∑ p ∈ innerPlaquettes S' 0,
        (∑ x ∈ plaquetteCorners p, if enclosingCell x = g.actSite F.top Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (transportChain g X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes S 0, (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) :=
    sum_innerPlaquettes_transport hg hS hS' _ _ fun p hp => by
      rw [plaquetteWeight_transport hg hodd hp, show transportChain g X 0 = transportField g (X 0) from rfl,
        re_plaquetteHolonomy_transport hg]
  have e1 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S' (j + 1),
        ((if enclosingCell c.1 = g.actSite F.top Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = g.actSite F.top Y then (1 / 2 : ℝ) else 0)) *
        blockFit (transportChain g X j) (transportChain g X (j + 1)) c =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
            blockFit (X j) (X (j + 1)) c := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 ≤ F.top := Finset.mem_range.1 hj
    refine sum_innerBonds_transport hg hS hS' hj' _ _ fun c hc => ?_
    rw [bondWeight_transport hg hodd hj' hc, show transportChain g X j = transportField g (X j) from rfl,
      show transportChain g X (j + 1) = transportField g (X (j + 1)) from rfl, blockFit_transport hg hj' hodd.pos]
  unfold cellShare
  rw [e0, e1]
end Chains
theorem transportField_symmInv {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (X : F.GaugeField j) :
    transportField (symmInv g) (transportField g X) = X := by
  funext x i
  have e1 : (symmInv (symmInv g)).actSite j x = g.actSite j x := by rw [symmInv_symmInv hg]
  have e2 : ((symmInv g).perm i, decide ((symmInv g).sign i = 1)) = mapStep g (i, true) := by
    simp only [mapStep]
    show (g.perm⁻¹ i, decide (g.sign (g.perm⁻¹ i) = 1)) = (g.perm.symm i, _)
    have : g.perm⁻¹ i = g.perm.symm i := rfl
    rw [this]
    by_cases h : g.sign (g.perm.symm i) = 1 <;> simp [h]
  simp only [transportField] at *
  rw [e1, e2]
  exact linkValue_transportField hg X x (i, true)
theorem transportField_eq_of_transports {g : CubicSymmetry} (hg : g.IsSymmetry F) {V V' : F.GaugeField F.top}
    (hC : g.TransportsField V V') : transportField g V = V' := by
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x, y = g.actSite F.top x := ⟨(symmInv g).actSite F.top y, (actSite_symmInv hg _ y).symm⟩
  have hs0 : g.perm.symm (g.perm i) = i := by simp
  rcases hg.1 i with hs | hs
  · have h := hC x (g.perm i)
    simp only [CubicSymmetry.actStep, hs0, hs, decide_true, linkValue, if_true] at h
    simp only [transportField, hs, decide_true, linkValue, if_true, symmInv_actSite hg]
    exact h.symm
  · have h := hC (x - unitStep F.top (g.perm i)) (g.perm i)
    have e : g.actSite F.top x = g.actSite F.top (x - unitStep F.top (g.perm i)) - unitStep F.top i := by
      have := actSite_add_unitStep_of_neg hg (x - unitStep F.top (g.perm i)) (i := g.perm i) (by rw [hs0]; exact hs)
      rw [sub_add_cancel, hs0] at this
      exact this
    have n2 : ¬ (-1 : ℤ) = 1 := by norm_num
    simp only [CubicSymmetry.actStep, hs0, hs, n2, decide_false, linkValue, Bool.false_eq_true, if_false] at h
    rw [← e] at h
    simp only [transportField, hs, n2, decide_false, linkValue, Bool.false_eq_true, if_false, symmInv_actSite hg]
    rw [← h]
    simp
end SymmetryTransport
theorem symmetryInvarianceOfShare (hV : minimalChainExistenceStatement) : symmetryInvarianceOfShareStatement := by
  classical
  open SymmetryTransport in
  intro F a S S' V V' g ha hodd hg hS hC hone Y
  have hgi := symmInv_isSymmetry hg
  have h1 : ∀ z ∈ S, g.actSite F.top z ∈ S' := fun z hz => (hS z).1 hz
  have h2 : ∀ z ∈ S', (symmInv g).actSite F.top z ∈ S := fun z hz => by
    rw [hS, actSite_symmInv hg]
    exact hz
  have h4 : ∀ z ∈ S, (symmInv (symmInv g)).actSite F.top z ∈ S' := fun z hz => by
    rw [symmInv_symmInv hg]
    exact h1 z hz
  have hpush := transportField_eq_of_transports hg hC
  refine minimalCellShare_eq_of_chainMap (V := V) (V' := V') (transportChain g) (transportChain (symmInv g))
    (fun X hX => ?_) (fun X hX => ?_)
    (fun X _ => chainAction_transport hg hodd h1 h2 a X) (fun X _ => chainAction_transport hgi hodd h2 h4 a X)
    (fun X _ => ?_) ?_ (fun X hX => hone X hX Y)
  · show transportField g (X F.top) = V'
    rw [hX, hpush]
  · show transportField (symmInv g) (X F.top) = V
    rw [hX, ← hpush, transportField_symmInv hg]
  · have := cellShare_transport hgi hodd h2 h4 a (g.actSite F.top Y) X
    rwa [symmInv_actSite hg] at this
  · obtain ⟨X, hX, -⟩ := (hV F a S' ha).2.2.2 V'
    exact ⟨X, hX⟩
end YangMills.Construction.BlockAverages
end
