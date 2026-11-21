import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.ColdChainAtEveryLevel.ChainsAtTheSameOffsets
import YangMills.Construction.ColdChainAtEveryLevel.ChartOnComplexLines
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages.SameOffsetCharts
open LatticePaths ComplexChart.BlockGeometry ComplexLineChart SameOffsets LatticeFractionalIntegration
variable {F : BlockFrame}
section Formula
theorem isCrossingBond_of_add_basisVector_not_mem (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {y : F.Cell} {h : Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube F.blockSide) (hc : h + basisVector i ∉ centredCube F.blockSide) :
    IsCrossingBond (cellSite y h, i) ∧
      cellSite y h + unitStep F.depth i =
        cellSite (y + siteOfCoords F.top (basisVector i)) (h + basisVector i - (F.blockSide : ℤ) • basisVector i) ∧
      h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide := by
  obtain ⟨m, hm⟩ := id hodd
  have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  have hcube := (mem_centredCube_iff F.blockSide h).1 hh
  have hi : h i = ((F.blockSide : ℤ) - 1) / 2 := by
    by_contra hne
    apply hc
    rw [mem_centredCube_iff]
    intro μ
    have h1 := hcube μ
    by_cases hμ : μ = i
    · subst hμ
      have e : (h + basisVector μ) μ = h μ + 1 := by simp [basisVector]
      rw [e]
      omega
    · have e : (h + basisVector i) μ = h μ := by simp [basisVector, hμ]
      rw [e]
      exact h1
  set E := y + siteOfCoords F.top (basisVector i) with hE
  have h1c : h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff]
    intro μ
    have h1 := hcube μ
    by_cases hμ : μ = i
    · subst hμ
      have e : (h + basisVector μ - (F.blockSide : ℤ) • basisVector μ) μ = h μ + 1 - (F.blockSide : ℤ) := by
        simp [basisVector]
      rw [e]
      omega
    · have e : (h + basisVector i - (F.blockSide : ℤ) • basisVector i) μ = h μ := by simp [basisVector, hμ]
      rw [e]
      exact h1
  have hsite : cellSite y h + unitStep F.depth i = cellSite E (h + basisVector i - (F.blockSide : ℤ) • basisVector i) := by
    rw [hE, cellSite_add_basisVector, cellSite_add_unitStep, sub_add_cancel]
  have hcell : enclosingCell (cellSite y h + unitStep F.depth i) = E := by
    rw [hsite, enclosingCell_cellSite hodd E h1c]
  refine ⟨?_, hsite, h1c⟩
  unfold IsCrossingBond
  simp only [ne_eq]
  rw [hcell, enclosingCell_cellSite hodd y hh, hE]
  intro hEq
  have h0 : (siteOfCoords F.top (basisVector i) : F.Cell) = 0 := by simpa using hEq
  have h2 := congrFun h0 i
  have h3 := valMinAbs_cell_of_small hamb i (A := 1) (by norm_num)
  have h4 : ((siteOfCoords F.top (basisVector i) : F.Cell) i) = ((1 : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords, basisVector]
  rw [h4] at h2
  rw [h2] at h3
  simp at h3
theorem not_isCrossingBond_of_mem (hodd : Odd F.blockSide) {y : F.Cell} {h : Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube F.blockSide) (hc : h + basisVector i ∈ centredCube F.blockSide) :
    ¬ IsCrossingBond (cellSite y h, i) := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.not_isCrossingBond_offsetSite <;> assumption
open Classical in
theorem gaugedBondElement_of_inner (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (X : F.GaugeField F.depth) (k : F.Cell → UnitQuaternion) (V : F.GaugeField F.top)
    (y : F.Cell) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hc : h + basisVector i ∈ centredCube F.blockSide) :
    gaugedBondElement X k V (cellSite y h, i) =
      k y * pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * X (cellSite y h) i *
      (pathHolonomy X (cellCentre F.depth y) (axisPath (h + basisVector i) 1))⁻¹ * (k y)⁻¹ := by
  unfold gaugedBondElement treeHolonomy
  simp only
  rw [if_neg (not_isCrossingBond_of_mem hodd hh hc), cellSite_add_unitStep, enclosingCell_cellSite hodd y hc,
    enclosingCell_cellSite hodd y hh, cellOffset_cellSite hamb hodd y hh, cellOffset_cellSite hamb hodd y hc, mul_one]
open Classical in
theorem gaugedBondElement_of_crossing (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (X : F.GaugeField F.depth) (k : F.Cell → UnitQuaternion) (V : F.GaugeField F.top)
    (y : F.Cell) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hc : h + basisVector i ∉ centredCube F.blockSide) :
    gaugedBondElement X k V (cellSite y h, i) =
      k y * pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * X (cellSite y h) i *
      (pathHolonomy X (cellCentre F.depth (y + siteOfCoords F.top (basisVector i)))
        (axisPath (h + basisVector i - (F.blockSide : ℤ) • basisVector i) 1))⁻¹ *
      (k (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V y i)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := isCrossingBond_of_add_basisVector_not_mem (y := y) hamb hodd hh hc
  unfold gaugedBondElement treeHolonomy
  simp only
  rw [if_pos h1, h2, enclosingCell_cellSite hodd _ h3, enclosingCell_cellSite hodd y hh,
    cellOffset_cellSite hamb hodd y hh, cellOffset_cellSite hamb hodd _ h3]
end Formula
section Transfer
abbrev sameShapeFrame (F : BlockFrame) (sd : Fin 4 → ℕ) : BlockFrame := ⟨F.blockSide, F.depth, sd⟩
variable {sd : Fin 4 → ℕ} {Y : F.Cell} {Y' : (sameShapeFrame F sd).Cell} {D : Finset F.Cell}
theorem siteAtOffset_top_zero {G : BlockFrame} (Z : G.Cell) : siteAtOffset Z (G.depth + 1) 0 = Z := by
  simp only [siteAtOffset, siteOfCoords_zero, add_zero]
  exact cellCentre_top Z
theorem siteAtOffset_top {G : BlockFrame} (Z : G.Cell) (a : Lattice4) :
    siteAtOffset Z (G.depth + 1) a = Z + siteOfCoords G.top a := by
  simp only [siteAtOffset]
  rw [show cellCentre (G.depth + 1) Z = Z from cellCentre_top Z]
theorem isRegionOffset_cellSite (hodd : Odd F.blockSide) {y : F.Cell} (hy : y ∈ D) {a h : Lattice4}
    (hya : y = Y + siteOfCoords F.top a) (ha : ∀ i, |a i| ≤ 1) (hh : h ∈ centredCube F.blockSide) :
    IsRegionOffset Y D F.depth (scaleOffset F.blockSide a + h) := by
  have hj : F.depth + 1 ≤ F.top := le_rfl
  have hsite : siteAtOffset Y F.depth (scaleOffset F.blockSide a + h) = cellSite y h := by
    rw [siteAtOffset_add, ← refineSite_siteAtOffset hj, siteAtOffset_top, ← hya, refineSite_eq_cellCentre]
    rfl
  refine ⟨by rw [hsite]; exact cellSite_mem_sitesOfCells hy hh, fun i => ?_⟩
  have h1 := ((mem_centredCube_iff _ _).1 hh) i
  have h2 := ha i
  have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have e : (F.blockSide : ℤ) ^ (F.top - F.depth) = F.blockSide := by simp [BlockFrame.top]
  rw [e]
  simp only [Pi.add_apply, scaleOffset]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < (F.blockSide : ℤ))]
  have h3 : |h i| ≤ F.blockSide := by
    rw [abs_le]
    constructor <;> omega
  nlinarith
theorem isSmallOffset_top {a : Lattice4} (hodd : Odd F.blockSide) (ha : ∀ i, |a i| ≤ 1) :
    IsSmallOffset F (F.depth + 1) a := by
  intro i
  have h2 := ha i
  simp only [BlockFrame.top, Nat.sub_self, pow_zero]
  omega
set_option maxHeartbeats 1000000 in
theorem bondChartCoord_chartAtSameOffsets (hamb : IsAdmissibleAmbient F)
    (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) (hodd : Odd F.blockSide)
    (hD : IsNearCells Y D) (R : F.FieldChain) (R' : (sameShapeFrame F sd).FieldChain)
    (U' : ChainChart (sameShapeFrame F sd))
    (hR : ∀ j, j < F.top → AgreeOnRegion Y Y' D j (R j) (R' j)) (V : F.GaugeField F.top)
    (V' : (sameShapeFrame F sd).GaugeField (sameShapeFrame F sd).top) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) (hY : Y ∈ D)
    (hE : h + basisVector i ∉ centredCube F.blockSide → Y + siteOfCoords F.top (basisVector i) ∈ D)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (v' : (sameShapeFrame F sd).Site (sameShapeFrame F sd).top → Fin 4 → imaginaryQuaternions)
    (hv : h + basisVector i ∉ centredCube F.blockSide → rotatedField v V Y i = rotatedField v' V' Y' i) :
    bondChartCoord R V (cellSite Y h, i) (chartAtSameOffsets Y Y' U') v =
      bondChartCoord R' V'
        ((cellSite Y' h : (sameShapeFrame F sd).Site (sameShapeFrame F sd).depth), i) U' v' := by
  classical
  have hL : (sameShapeFrame F sd).blockSide = F.blockSide := rfl
  have hn : (sameShapeFrame F sd).top = F.top := rfl
  have hoddG : Odd (sameShapeFrame F sd).blockSide := hodd
  have hj : F.depth + 1 ≤ F.top := le_rfl
  have ht : F.depth < F.top := by simp [BlockFrame.top]
  set X := chartField R (chartAtSameOffsets Y Y' U') F.depth with hXd
  set X' := chartField R' U' F.depth with hX'd
  have hX : AgreeOnRegion Y Y' D F.depth X X' := chartField_agree hamb hodd hL hn hD R R' U' hR F.depth ht
  have hreg0 : IsRegionOffset Y D (F.depth + 1) (0 : Lattice4) := by
    refine ⟨?_, isSmallOffset_top hodd (by simp)⟩
    rw [siteAtOffset_top_zero]
    exact mem_sitesOfCells_top.2 hY
  have htree : ∀ {a g : Lattice4}, IsRegionOffset Y D (F.depth + 1) a → g ∈ centredCube F.blockSide →
      pathHolonomy X (cellCentre F.depth (siteAtOffset Y (F.depth + 1) a)) (axisPath g 1) =
        pathHolonomy X' (cellCentre (sameShapeFrame F sd).depth (siteAtOffset Y' (F.depth + 1) a))
          (axisPath g 1) := by
    intro a g ha hg
    rw [← refineSite_eq_cellCentre, ← refineSite_eq_cellCentre]
    exact pathHolonomy_refineSite_eq hL hj hj hX (allAlong_axisPath_region hamb hodd hj hD ha hg 1)
  have hlink : ∀ {a : Lattice4}, IsRegionOffset Y D (F.depth + 1) a →
      chartGauge R (chartAtSameOffsets Y Y' U') F.top (siteAtOffset Y (F.depth + 1) a) =
        chartGauge R' U' (sameShapeFrame F sd).top (siteAtOffset Y' (F.depth + 1) a) := fun ha =>
    chartGauge_eq_of_agree hamb hodd hL hn hD R R' U' hR ht ha
  have h0 : scaleOffset F.blockSide (0 : Lattice4) + h = h := by
    funext μ
    simp [scaleOffset]
  have hregh : IsRegionOffset Y D F.depth h := by
    have := isRegionOffset_cellSite (Y := Y) hodd hY (a := 0) (by simp [siteOfCoords_zero]) (by simp) hh
    rwa [h0] at this
  have ey : siteAtOffset Y (F.depth + 1) (0 : Lattice4) = Y := siteAtOffset_top_zero Y
  have ey' : siteAtOffset Y' (F.depth + 1) (0 : Lattice4) = Y' := siteAtOffset_top_zero Y'
  unfold bondChartCoord
  congr 1
  by_cases hc : h + basisVector i ∈ centredCube F.blockSide
  · have hregh' : IsRegionOffset Y D F.depth (h + basisVector i) := by
      have := isRegionOffset_cellSite (Y := Y) hodd hY (a := 0) (by simp [siteOfCoords_zero]) (by simp) hc
      rwa [show scaleOffset F.blockSide (0 : Lattice4) + (h + basisVector i) = h + basisVector i by
        funext μ
        simp [scaleOffset]] at this
    rw [gaugedBondElement_of_inner hamb hodd X _ _ Y hh hc,
      gaugedBondElement_of_inner (F := sameShapeFrame F sd) hamb' hoddG X' _ _ Y' hh hc]
    have t1 := htree hreg0 hh
    have t2 := htree hreg0 hc
    have l1 := hlink hreg0
    rw [ey, ey'] at t1 t2 l1
    rw [t1, t2, l1]
    have hb := hX h i hregh hregh'
    congr 3
  · obtain ⟨hcr, hs, h1c⟩ := isCrossingBond_of_add_basisVector_not_mem (y := Y) hamb hodd hh hc
    have hEm := hE hc
    set E := Y + siteOfCoords F.top (basisVector i) with hEd
    have hunit : ∀ μ, |basisVector i μ| ≤ 1 := fun μ => by
      by_cases hμ : μ = i
      · subst hμ
        simp [basisVector]
      · simp [basisVector, hμ]
    have hregE : IsRegionOffset Y D (F.depth + 1) (basisVector i) := by
      refine ⟨?_, isSmallOffset_top hodd hunit⟩
      rw [siteAtOffset_top]
      exact mem_sitesOfCells_top.2 hEm
    have hregh' : IsRegionOffset Y D F.depth (h + basisVector i) := by
      refine ⟨?_, fun μ => ?_⟩
      · have e1 : siteAtOffset Y F.depth (h + basisVector i) = cellSite Y h + unitStep F.depth i := by
          rw [siteAtOffset_add, unitStep_eq]
          rfl
        rw [e1, hs]
        exact cellSite_mem_sitesOfCells hEm h1c
      · have h1 := hregh.2 μ
        have h2 := ((mem_centredCube_iff _ _).1 hh) μ
        have h3 := hunit μ
        have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
        have e : (F.blockSide : ℤ) ^ (F.top - F.depth) = F.blockSide := by simp [BlockFrame.top]
        rw [e]
        simp only [Pi.add_apply]
        refine (abs_add_le _ _).trans_lt ?_
        have h4 : |h μ| ≤ F.blockSide := by
          rw [abs_le]
          constructor <;> omega
        omega
    rw [gaugedBondElement_of_crossing hamb hodd X _ _ Y hh hc,
      gaugedBondElement_of_crossing (F := sameShapeFrame F sd) hamb' hoddG X' _ _ Y' hh hc]
    have t1 := htree hreg0 hh
    have t2 := htree hregE h1c
    have l1 := hlink hreg0
    have l2 := hlink hregE
    rw [ey, ey'] at t1 l1
    rw [siteAtOffset_top, siteAtOffset_top] at t2 l2
    rw [t1, t2, l1, l2, hv hc]
    have hb := hX h i hregh hregh'
    congr 4
end Transfer
section Sites
variable {sd : Fin 4 → ℕ} {Y : F.Cell} {Y' : (sameShapeFrame F sd).Cell} {D : Finset F.Cell} {j : ℕ}
theorem exists_regionOffset_of_mem (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hj : j ≤ F.top)
    (hD : IsNearCells Y D) {x : F.Site j} (hx : x ∈ sitesOfCells D j) :
    ∃ a g : Lattice4, (∀ i, |a i| ≤ 1) ∧ Y + siteOfCoords F.top a ∈ D ∧
      g ∈ centredCube (F.blockSide ^ (F.top - j)) ∧
      x = siteAtOffset Y j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) ∧
      IsRegionOffset Y D j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := by
  obtain ⟨y, hy, g, hg, e⟩ := mem_sitesOfCells.1 hx
  obtain ⟨a, ha, rfl⟩ := hD y hy
  have e2 : x = siteAtOffset Y j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := by
    rw [e, cellCentre_add j hj, siteAtOffset_add]
    rfl
  refine ⟨a, g, ha, hy, hg, e2, by rw [← e2]; exact hx, fun i => ?_⟩
  set K : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hodd.pos)
  have hgc := (mem_centredCube_iff _ _).1 hg i
  have hcast : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = K := by
    rw [hK]
    push_cast
    rfl
  rw [hcast] at hgc
  have hgb : |g i| ≤ K := by
    rw [abs_le]
    constructor <;> omega
  have h1 := ha i
  simp only [Pi.add_apply]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < K)]
  nlinarith
theorem cellSupDist_add_le_one (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) {a : Lattice4}
    (ha : ∀ i, |a i| ≤ 1) :
    cellSupDist Y' (Y' + siteOfCoords (sameShapeFrame F sd).top a) ≤ 1 := by
  have h1 := cellSupDist_add_le hamb' (Y' + siteOfCoords (sameShapeFrame F sd).top a) (a := - a) (r := 1)
    (by norm_num) (fun i => by simpa using ha i)
  rwa [siteOfCoords_neg, add_neg_cancel_right] at h1
theorem siteAtSameOffset_mem_and_near (hamb : IsAdmissibleAmbient F)
    (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) (hodd : Odd F.blockSide) (hj : j ≤ F.top)
    (hD : IsNearCells Y D) {S' : Finset (sameShapeFrame F sd).Cell}
    (hS' : ∀ a : Lattice4, (∀ i, |a i| ≤ 1) → Y + siteOfCoords F.top a ∈ D →
      Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S')
    {x : F.Site j} (hx : x ∈ sitesOfCells D j) :
    siteAtSameOffset Y Y' x ∈ sitesOfCells S' j ∧ cellSupDist Y' (enclosingCell (siteAtSameOffset Y Y' x)) ≤ 3 := by
  obtain ⟨a, g, ha, hy, hg, e, hreg⟩ := exists_regionOffset_of_mem hamb hodd hj hD hx
  have hoddG : Odd (sameShapeFrame F sd).blockSide := hodd
  have e2 : siteAtSameOffset Y Y' x =
      cellCentre j (Y' + siteOfCoords (sameShapeFrame F sd).top a) + siteOfCoords j g := by
    have hc := cellCentre_add (F := sameShapeFrame F sd) j hj Y' a
    rw [e, siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hreg.2, hc, siteAtOffset_add]
    rfl
  refine ⟨mem_sitesOfCells.2 ⟨_, hS' a ha hy, g, hg, e2⟩, ?_⟩
  rw [e2, enclosingCell_cellCentre_add_siteOfCoords hoddG _ g hg]
  exact (cellSupDist_add_le_one hamb' ha).trans (by norm_num)
theorem siteAtSameOffset_add_unitStep (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hj : j ≤ F.top)
    (hD : IsNearCells Y D) {x : F.Site j} (hx : x ∈ sitesOfCells D j) (i : Fin 4) :
    siteAtSameOffset Y Y' (x + unitStep j i) = siteAtSameOffset Y Y' x + unitStep j i := by
  obtain ⟨a, g, -, -, -, e, hreg⟩ := exists_regionOffset_of_mem hamb hodd hj hD hx
  set p : Lattice4 := (fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g with hp
  have hs : IsSmallOffset F j (p + basisVector i) := fun μ => by
    have h1 := abs_offset_le_of_region hamb hodd hj hD hreg μ
    have hK : (1 : ℤ) ≤ (F.blockSide : ℤ) ^ (F.top - j) := one_le_pow₀ (by exact_mod_cast hodd.pos)
    have h3 : |basisVector i μ| ≤ 1 := by
      by_cases hμ : μ = i
      · subst hμ
        simp [basisVector]
      · simp [basisVector, hμ]
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans_lt ?_
    omega
  rw [e, siteAtOffset_add_unitStep, siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hs,
    siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hreg.2, siteAtOffset_add_unitStep]
theorem siteAtSameOffset_injOn (hamb : IsAdmissibleAmbient F) (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd))
    (hodd : Odd F.blockSide) (hj : j ≤ F.top) (hD : IsNearCells Y D) {x x' : F.Site j}
    (hx : x ∈ sitesOfCells D j) (hx' : x' ∈ sitesOfCells D j)
    (h : siteAtSameOffset Y Y' x = siteAtSameOffset Y Y' x') : x = x' := by
  obtain ⟨a, g, -, -, -, e, hreg⟩ := exists_regionOffset_of_mem hamb hodd hj hD hx
  obtain ⟨a', g', -, -, -, e', hreg'⟩ := exists_regionOffset_of_mem hamb hodd hj hD hx'
  rw [e, e', siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hreg.2,
    siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hreg'.2] at h
  have hoddG : 0 < (sameShapeFrame F sd).blockSide := hodd.pos
  have := siteAtOffset_inj_of_small (F := sameShapeFrame F sd) hamb' hoddG Y' hreg.2 hreg'.2 h
  rw [e, e', this]
theorem siteAtSameOffset_mem_bondsOver (hamb : IsAdmissibleAmbient F)
    (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) (hodd : Odd F.blockSide) (hj : j ≤ F.top)
    (hD : IsNearCells Y D) {S' : Finset (sameShapeFrame F sd).Cell}
    (hS' : ∀ a : Lattice4, (∀ i, |a i| ≤ 1) → Y + siteOfCoords F.top a ∈ D →
      Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S')
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds D j) :
    ((siteAtSameOffset Y Y' b.1, b.2) : (sameShapeFrame F sd).Site j × Fin 4) ∈
      bondsOver S' (cellBall S' Y' 3) j := by
  classical
  obtain ⟨h1, h2⟩ := mem_innerBonds_iff.1 hb
  obtain ⟨m1, d1⟩ := siteAtSameOffset_mem_and_near (Y' := Y') hamb hamb' hodd hj hD hS' h1
  obtain ⟨m2, -⟩ := siteAtSameOffset_mem_and_near (Y' := Y') hamb hamb' hodd hj hD hS' h2
  rw [siteAtSameOffset_add_unitStep hamb hodd hj hD h1] at m2
  have hoddG : Odd (sameShapeFrame F sd).blockSide := hodd
  unfold bondsOver
  simp only [Finset.mem_filter]
  refine ⟨mem_innerBonds_iff.2 ⟨m1, m2⟩, ?_⟩
  unfold cellBall
  simp only [Finset.mem_filter]
  exact ⟨enclosingCell_mem_of_mem_sitesOfCells hoddG m1, d1⟩
theorem finsetLpNorm_image {β γ : Type} [DecidableEq γ] (p : ℝ) (T : Finset β) (ψ : β → γ)
    (hψ : Set.InjOn ψ T) (f : γ → ℝ) : finsetLpNorm p (T.image ψ) f = finsetLpNorm p T (fun b => f (ψ b)) := by
  unfold finsetLpNorm
  rw [Finset.sum_image hψ]
theorem finsetLpNorm_fine_chartAtSameOffsets_le (hamb : IsAdmissibleAmbient F)
    (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) (hodd : Odd F.blockSide) (hD : IsNearCells Y D)
    {S' : Finset (sameShapeFrame F sd).Cell}
    (hS' : ∀ a : Lattice4, (∀ i, |a i| ≤ 1) → Y + siteOfCoords F.top a ∈ D →
      Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S')
    (R' : (sameShapeFrame F sd).FieldChain) (A' : ChainChart (sameShapeFrame F sd)) :
    finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(chartAtSameOffsets Y Y' A').fine b.1 b.2‖) ≤
      localNorm S' R' A' (oneSiteWeights (sameShapeFrame F sd)) Y' := by
  classical
  set ψ : F.Site 0 × Fin 4 → (sameShapeFrame F sd).Site 0 × Fin 4 :=
    fun b => (siteAtSameOffset Y Y' b.1, b.2) with hψ
  have hinj : Set.InjOn ψ (innerBonds D 0 : Set (F.Site 0 × Fin 4)) := by
    intro b hb b' hb' h
    have h' : ((siteAtSameOffset Y Y' b.1, b.2) : _ × Fin 4) = (siteAtSameOffset Y Y' b'.1, b'.2) := h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h'
    exact Prod.ext (siteAtSameOffset_injOn hamb hamb' hodd (Nat.zero_le _) hD (mem_innerBonds_iff.1 hb).1
      (mem_innerBonds_iff.1 hb').1 e1) e2
  have h1 := finsetLpNorm_image 4 (innerBonds D 0) ψ hinj (fun b' => ‖A'.fine b'.1 b'.2‖)
  have h2 := finsetLpNorm_fine_le_localNorm S' R' A' Y' (T := (innerBonds D 0).image ψ) (fun b' hb' => by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact siteAtSameOffset_mem_bondsOver hamb hamb' hodd (Nat.zero_le _) hD hS' hb)
  rw [h1] at h2
  exact h2
theorem finsetLpNorm_coarse_chartAtSameOffsets_le (hamb : IsAdmissibleAmbient F)
    (hamb' : IsAdmissibleAmbient (sameShapeFrame F sd)) (hodd : Odd F.blockSide) (hD : IsNearCells Y D)
    {S' : Finset (sameShapeFrame F sd).Cell}
    (hS' : ∀ a : Lattice4, (∀ i, |a i| ≤ 1) → Y + siteOfCoords F.top a ∈ D →
      Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S')
    (R' : (sameShapeFrame F sd).FieldChain) (A' : ChainChart (sameShapeFrame F sd)) {j : ℕ}
    (hj : j + 1 < F.top) :
    finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(chartAtSameOffsets Y Y' A').coarse j b.1 b.2‖) ≤
      localNorm S' R' A' (oneSiteWeights (sameShapeFrame F sd)) Y' := by
  classical
  set ψ : F.Site (j + 1) × Fin 4 → (sameShapeFrame F sd).Site (j + 1) × Fin 4 :=
    fun b => (siteAtSameOffset Y Y' b.1, b.2) with hψ
  have hinj : Set.InjOn ψ (innerBonds D (j + 1) : Set (F.Site (j + 1) × Fin 4)) := by
    intro b hb b' hb' h
    have h' : ((siteAtSameOffset Y Y' b.1, b.2) : _ × Fin 4) = (siteAtSameOffset Y Y' b'.1, b'.2) := h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h'
    exact Prod.ext (siteAtSameOffset_injOn hamb hamb' hodd hj.le hD (mem_innerBonds_iff.1 hb).1
      (mem_innerBonds_iff.1 hb').1 e1) e2
  have h1 := finsetLpNorm_image 2 (innerBonds D (j + 1)) ψ hinj (fun b' => ‖A'.coarse j b'.1 b'.2‖)
  have h2 := finsetLpNorm_coarse_le_localNorm S' R' A' Y' (j := j) hj (T := (innerBonds D (j + 1)).image ψ)
    (fun b' hb' => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
      exact siteAtSameOffset_mem_bondsOver hamb hamb' hodd hj.le hD hS' hb)
  rw [h1] at h2
  exact h2
end Sites
end YangMills.Construction.BlockAverages.SameOffsetCharts
end
