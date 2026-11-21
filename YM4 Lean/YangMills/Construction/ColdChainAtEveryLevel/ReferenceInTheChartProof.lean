import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.ReferenceChart
variable {F : BlockFrame}
section Log
theorem exists_expUnit_eq (g : UnitQuaternion) :
    ∃ w : imaginaryQuaternions, expUnit w = g ∧ ‖(w : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_expUnit_eq <;> assumption
end Log
section Paths
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_nil (j : ℕ) : pathDisplacement (F := F) j [] = 0 := rfl
theorem pathDisplacement_cons (j : ℕ) (st : PathStep) (l : List PathStep) :
    pathDisplacement (F := F) j (st :: l) = stepDisplacement j st + pathDisplacement j l := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathDisplacement_cons <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem stepDisplacement_reverse (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j (st.1, !st.2) = - stepDisplacement j st := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.stepDisplacement_flip <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem siteOfCoords_endpoint (j : ℕ) (u : LatticeFractionalIntegration.Lattice4) (l : List PathStep) :
    siteOfCoords (F := F) j (LatticePaths.endpoint u l) = siteOfCoords j u + pathDisplacement j l := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.siteOfCoords_endpoint <;> assumption
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (x : F.Site j) (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem linkValue_reverse {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
def AllSitesAlong {j : ℕ} (P : F.Site j → Prop) : F.Site j → List PathStep → Prop
  | x, [] => P x
  | x, st :: r => P x ∧ AllSitesAlong P (x + stepDisplacement j st) r
theorem AllSitesAlong.head {j : ℕ} {P : F.Site j → Prop} {x : F.Site j} {l : List PathStep}
    (h : AllSitesAlong P x l) : P x := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem allSitesAlong_of_allAlong {j : ℕ} (P : F.Site j → Prop) (x0 : F.Site j)
    {u : LatticeFractionalIntegration.Lattice4} {l : List PathStep}
    (h : LatticePaths.AllAlong (fun v => P (x0 + siteOfCoords j v)) u l) :
    AllSitesAlong P (x0 + siteOfCoords j u) l := by
  induction l generalizing u with
  | nil => exact h
  | cons st r ih =>
    refine ⟨h.1, ?_⟩
    have := ih h.2
    rwa [siteOfCoords_add, ← stepDisplacement_eq_siteOfCoords, ← add_assoc] at this
theorem norm_coe_mul_sub_coe_mul_le (a a' b b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - a'‖ + ‖(b : ℍ[ℝ]) - b'‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem norm_coe_inv_sub_coe_inv (a b : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - b‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_pathHolonomy_sub_le {j : ℕ} {P : F.Site j → Prop} {X Y : F.GaugeField j} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : ∀ x i, P x → P (x + unitStep j i) → ‖(X x i : ℍ[ℝ]) - (Y x i : ℍ[ℝ])‖ ≤ ε) :
    ∀ (l : List PathStep) (x : F.Site j), AllSitesAlong P x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy Y x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy]
  | cons st r ih =>
    intro x hx
    have hnext := AllSitesAlong.head hx.2
    have hstep : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue Y x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      obtain ⟨i, b⟩ := st
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        rw [norm_coe_inv_sub_coe_inv]
        have e1 : x + stepDisplacement j (i, false) = x - unitStep j i := by
          simp [stepDisplacement, sub_eq_add_neg]
        rw [e1] at hnext
        refine h _ i hnext ?_
        rw [sub_add_cancel]
        exact AllSitesAlong.head hx
      · simp only [linkValue, if_true]
        have e1 : x + stepDisplacement j (i, true) = x + unitStep j i := by
          simp [stepDisplacement]
        rw [e1] at hnext
        exact h x i (AllSitesAlong.head hx) hnext
    simp only [pathHolonomy]
    refine (norm_coe_mul_sub_coe_mul_le _ _ _ _).trans ?_
    have := ih _ hx.2
    simp only [List.length_cons]
    push_cast
    linarith
theorem pathHolonomy_one {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem norm_pathHolonomy_sub_one_le {j : ℕ} {P : F.Site j → Prop} {X : F.GaugeField j} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : ∀ x i, P x → P (x + unitStep j i) → ‖(X x i : ℍ[ℝ]) - 1‖ ≤ ε)
    (l : List PathStep) (x : F.Site j) (hx : AllSitesAlong P x l) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  have := norm_pathHolonomy_sub_le (X := X) (Y := fun _ _ => (1 : UnitQuaternion)) hε
    (fun y i h1 h2 => by simpa using h y i h1 h2) l x hx
  simpa [pathHolonomy_one] using this
end Paths
section Blocks
def blockSite (y : F.Cell) (h : LatticeFractionalIntegration.Lattice4) : F.Site F.depth :=
  cellCentre F.depth y + siteOfCoords F.depth h
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem mem_centredCube_top_iff (h : LatticeFractionalIntegration.Lattice4) :
    h ∈ centredCube (F.blockSide ^ (F.top - F.depth)) ↔ h ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_centredCube_top_iff <;> assumption
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_blockSite (hL : Odd F.blockSide) (y : F.Cell)
    {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (blockSite y h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem valMinAbs_siteOfCoords (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide)
    {A : LatticeFractionalIntegration.Lattice4} (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ))
    (i : Fin 4) : ((siteOfCoords F.depth A : F.Site F.depth) i).valMinAbs = A i := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.valMinAbs_siteOfCoords <;> assumption
theorem siteOfCoords_injOn_small (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide)
    {A B : LatticeFractionalIntegration.Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (hB : ∀ i, |B i| < 32 * (F.blockSide : ℤ))
    (h : (siteOfCoords F.depth A : F.Site F.depth) = siteOfCoords F.depth B) : A = B := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.siteOfCoords_injOn_small <;> assumption
theorem abs_lt_of_mem_centredCube (hL : 0 < F.blockSide) {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) : |h i| < 32 * (F.blockSide : ℤ) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.abs_lt_of_mem_centredCube <;> assumption
theorem cellOffset_blockSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell)
    {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide) :
    cellOffset (blockSite y h) = h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.cellOffset_blockPoint <;> assumption
theorem blockSite_add_unitStep (y : F.Cell) (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) :
    blockSite y h + unitStep F.depth i = blockSite y (h + LatticeFractionalIntegration.basisVector i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem blockSite_next_cell (y : F.Cell) (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) :
    blockSite (y + siteOfCoords F.top (LatticeFractionalIntegration.basisVector i)) h =
      blockSite y (h + (F.blockSide : ℤ) • LatticeFractionalIntegration.basisVector i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_neighbour <;> assumption
theorem blockSite_mem_sitesOfCells {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S)
    {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide) :
    blockSite y h ∈ sitesOfCells S F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_mem <;> assumption
theorem exists_blockSite {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ h ∈ centredCube F.blockSide, x = blockSite y h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_blockPoint <;> assumption
theorem mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ innerBonds S j ↔ b.1 ∈ sitesOfCells S j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_innerBonds <;> assumption
def treeGauge (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    UnitQuaternion :=
  k (enclosingCell x) * pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
theorem treeGauge_blockSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth)
    (y : F.Cell) {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide) :
    treeGauge k X (blockSite y h) = k y * pathHolonomy X (cellCentre F.depth y) (axisPath h 1) := by
  unfold treeGauge
  rw [enclosingCell_blockSite hodd y hh, cellOffset_blockSite hamb hodd y hh]
theorem pathDisplacement_axisPath (j : ℕ) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def blockLoop (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) : List PathStep :=
  axisPath h 1 ++ ((i, true) :: reversePath (axisPath (h + LatticeFractionalIntegration.basisVector i) 1))
theorem pathHolonomy_blockLoop (X : F.GaugeField F.depth) (y : F.Cell)
    (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) :
    pathHolonomy X (cellCentre F.depth y) (blockLoop h i) =
      pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * X (blockSite y h) i *
        (pathHolonomy X (cellCentre F.depth y)
          (axisPath (h + LatticeFractionalIntegration.basisVector i) 1))⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_blockLoop <;> assumption
theorem pathDisplacement_blockLoop (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) :
    pathDisplacement (F := F) F.depth (blockLoop h i) = 0 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathDisplacement_blockLoop <;> assumption
theorem mem_centredCube_of_between {L : ℕ} {h v : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube L) (hv : LatticePaths.BetweenOrigin h v) (hL : 1 ≤ L) :
    v ∈ centredCube L := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_centredCube_of_between <;> assumption
theorem allAlong_blockLoop {L : ℕ} (hL : 1 ≤ L) {h : LatticeFractionalIntegration.Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube L) (hh' : h + LatticeFractionalIntegration.basisVector i ∈ centredCube L) :
    LatticePaths.AllAlong (fun v => v ∈ centredCube L) 0 (blockLoop h i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.allAlong_blockLoop <;> assumption
theorem length_axisPath_le {L : ℕ} {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) : (axisPath h π).length ≤ 2 * (L - 1) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.length_axisPath_le <;> assumption
theorem length_blockLoop_le {L : ℕ} (hL : 1 ≤ L) {h : LatticeFractionalIntegration.Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube L) (hh' : h + LatticeFractionalIntegration.basisVector i ∈ centredCube L) :
    (blockLoop h i).length ≤ 5 * L := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.length_blockLoop_le <;> assumption
open LatticeFractionalIntegration (Lattice4 basisVector)
theorem norm_blockLoop_sub_one_le {R X : F.GaugeField F.depth} {g : F.Site F.depth → UnitQuaternion}
    {ε e : ℝ} (hε : 0 ≤ ε) (he : 0 ≤ e)
    (hL : 1 ≤ F.blockSide) {y : F.Cell} {P : F.Site F.depth → Prop}
    (hP : ∀ h ∈ centredCube F.blockSide, P (blockSite y h))
    (hXR : ∀ x i, P x → P (x + unitStep F.depth i) → ‖(X x i : ℍ[ℝ]) - (R x i : ℍ[ℝ])‖ ≤ ε)
    (hRf : ∀ x i, P x → P (x + unitStep F.depth i) →
      ‖((gaugeTransform g R x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hh' : h + basisVector i ∈ centredCube F.blockSide) :
    ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      5 * F.blockSide * (ε + e) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockLoop_norm_sub_one_le <;> assumption
theorem gaugeTransform_treeGauge_inner (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth)
    (y : F.Cell) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hh' : h + basisVector i ∈ centredCube F.blockSide) :
    gaugeTransform (treeGauge k X) X (blockSite y h) i =
      k y * pathHolonomy X (cellCentre F.depth y) (blockLoop h i) * (k y)⁻¹ := by
  unfold gaugeTransform
  rw [blockSite_add_unitStep, treeGauge_blockSite hamb hodd k X y hh,
    treeGauge_blockSite hamb hodd k X y hh', pathHolonomy_blockLoop]
  group
theorem axisPath_add_basisVector_of_nonneg {h : Lattice4} {i : Fin 4} (hl : ∀ l, i < l → h l = 0)
    (h0 : 0 ≤ h i) : axisPath (h + basisVector i) 1 = axisPath h 1 ++ [(i, true)] := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.axisPath_add_basisVector_of_nonneg <;> assumption
theorem axisPath_of_neg {h : Lattice4} {i : Fin 4} (hl : ∀ l, i < l → h l = 0) (h0 : h i < 0) :
    axisPath h 1 = axisPath (h + basisVector i) 1 ++ [(i, false)] := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.axisPath_of_neg <;> assumption
theorem pathHolonomy_blockLoop_tree (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4} {i : Fin 4}
    (hl : ∀ l, i < l → h l = 0) :
    pathHolonomy X (cellCentre F.depth y) (blockLoop h i) = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_blockLoop_tree <;> assumption
end Blocks
open LatticeFractionalIntegration (Lattice4 basisVector)
section Crossing
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
end Crossing
section Value
theorem pathDisplacement_replicate (j : ℕ) (n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) =
      siteOfCoords j ((n : ℤ) • FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathDisplacement_replicate <;> assumption
theorem crossing_bondContour (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth)
    (y : F.Cell) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide) :
    k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
        (k (y + siteOfCoords F.top (basisVector i)))⁻¹ =
      gaugeTransform (treeGauge k X) X (blockSite y h) i *
        pathHolonomy (gaugeTransform (treeGauge k X) X)
          (blockSite (y + siteOfCoords F.top (basisVector i))
            (h + basisVector i - (F.blockSide : ℤ) • basisVector i))
          (List.replicate (F.blockSide - 1) (i, true)) := by
  set E := y + siteOfCoords F.top (basisVector i) with hE
  set h1 := h + basisVector i - (F.blockSide : ℤ) • basisVector i with hh1
  have hpos := hodd.pos
  have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
    simp [FlatPairing.stepDisplacement]
  have e1 : blockSite y h + unitStep F.depth i = blockSite E h1 := by
    rw [hE, blockSite_next_cell, blockSite_add_unitStep, hh1, sub_add_cancel]
  have e2 : blockSite E h1 + pathDisplacement F.depth (List.replicate (F.blockSide - 1) (i, true)) =
      blockSite E h := by
    rw [pathDisplacement_replicate, e0]
    simp only [blockSite]
    rw [add_assoc, ← siteOfCoords_add]
    congr 2
    funext l
    have hc : ((F.blockSide - 1 : ℕ) : ℤ) = (F.blockSide : ℤ) - 1 := by
      omega
    simp only [hh1, hc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e3 : cellCentre F.depth y +
        pathDisplacement F.depth (axisPath h 1 ++ List.replicate F.blockSide (i, true)) =
      cellCentre F.depth E + pathDisplacement F.depth (axisPath h 1) := by
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate, e0]
    have := blockSite_next_cell y h i
    rw [← hE] at this
    simp only [blockSite] at this
    rw [this, siteOfCoords_add]
  have c1 : List.replicate F.blockSide ((i, true) : PathStep) =
      (i, true) :: List.replicate (F.blockSide - 1) (i, true) := by
    have : F.blockSide = (F.blockSide - 1) + 1 := by omega
    exact (congrArg (fun n => List.replicate n ((i, true) : PathStep)) this).trans
      (List.replicate_succ ..)
  have hc : pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) =
      pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * (X (blockSite y h) i *
        pathHolonomy X (blockSite E h1) (List.replicate (F.blockSide - 1) (i, true))) *
        (pathHolonomy X (cellCentre F.depth E) (axisPath h 1))⁻¹ := by
    unfold bondContour
    rw [pathHolonomy_append, e3, pathHolonomy_reversePath, pathHolonomy_append,
      pathDisplacement_axisPath, c1]
    simp only [pathHolonomy]
    have e4 : cellCentre F.depth y + siteOfCoords F.depth h + stepDisplacement F.depth (i, true) =
        blockSite E h1 := by
      rw [← e1]
      simp [stepDisplacement, blockSite]
    rw [e4]
    simp [linkValue, blockSite]
  rw [hc, pathHolonomy_gaugeTransform, e2]
  unfold gaugeTransform
  rw [e1, treeGauge_blockSite hamb hodd k X y hh, treeGauge_blockSite hamb hodd k X E hh]
  group
theorem bond_cases (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {y : F.Cell} {h : Lattice4}
    {i : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hb : blockSite y h + unitStep F.depth i ∈ sitesOfCells S F.depth) :
    (h + basisVector i ∈ centredCube F.blockSide ∧ ¬ IsCrossingBond (blockSite y h, i)) ∨
      (IsCrossingBond (blockSite y h, i) ∧ h i = ((F.blockSide : ℤ) - 1) / 2 ∧
        y + siteOfCoords F.top (basisVector i) ∈ S ∧
        h + basisVector i - (F.blockSide : ℤ) • basisVector i ∈ centredCube F.blockSide) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.bond_cases <;> assumption
theorem exists_chart_of_loops (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {V : F.GaugeField F.top}
    {X : F.GaugeField F.depth} {k : F.Cell → UnitQuaternion} {Nc Nx : ℝ} (hc0 : 0 ≤ Nc) (hx0 : 0 ≤ Nx)
    (hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc)
    (hNx : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      y + siteOfCoords F.top (basisVector i) ∈ S →
      ‖((k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (k (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nx) :
    ∃ w : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) ∧
      (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ 2 * (Nx + F.blockSide * Nc)) ∧
      AgreeOnBonds S F.depth (chartedField w V) (gaugeTransform (treeGauge k X) X) := by
  classical
  choose lg hlg1 hlg2 using exists_expUnit_eq
  set W := gaugeTransform (treeGauge k X) X with hW
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hinner : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((W (blockSite y h) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc := by
    intro y hy h i hh hh'
    rw [hW, gaugeTransform_treeGauge_inner hamb hodd k X y hh hh', norm_coe_conj_sub_one]
    exact hNc y hy h i hh hh'
  refine ⟨fun x i => if (x, i) ∈ chordBonds S then
      (if IsCrossingBond (x, i) then lg (W x i * (V (enclosingCell x) i)⁻¹) else lg (W x i)) else 0,
    fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · have : (b.1, b.2) ∉ chordBonds S := hb
    simp [this]
  · obtain ⟨x, i⟩ := b
    have hbb : (x, i) ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
    obtain ⟨hx1, hx2⟩ := mem_innerBonds.1 hbb
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockSite hx1
    simp only [hb, if_true]
    have hNnn : 0 ≤ Nx + F.blockSide * Nc := by positivity
    rcases bond_cases hamb hodd (i := i) hh hx2 with ⟨hc, hnc⟩ | ⟨hcr, hi, hE, h1c⟩
    · simp only [hnc, if_false]
      have := hlg2 (W (blockSite y h) i)
      have h2 := hinner y hy h i hh hc
      have h3 : Nc ≤ Nx + F.blockSide * Nc := by nlinarith
      exact this.trans (by linarith)
    · simp only [hcr, if_true]
      rw [enclosingCell_blockSite hodd y hh]
      set E := y + siteOfCoords F.top (basisVector i) with hEdef
      set h1 := h + basisVector i - (F.blockSide : ℤ) • basisVector i with hh1
      set H := pathHolonomy W (blockSite E h1) (List.replicate (F.blockSide - 1) (i, true)) with hH
      have hA := crossing_bondContour hamb hodd k X y hh (i := i)
      rw [← hEdef, ← hh1, ← hW, ← hH] at hA
      have hP : AllSitesAlong (fun x => ∃ u ∈ centredCube F.blockSide, x = blockSite E u) (blockSite E h1)
          (List.replicate (F.blockSide - 1) (i, true)) := by
        refine allSitesAlong_of_allAlong _ (cellCentre F.depth E)
          (LatticePaths.allAlong_replicate fun m hm => ⟨_, ?_, rfl⟩)
        have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
          simp [FlatPairing.stepDisplacement]
        rw [e0]
        obtain ⟨q, hq⟩ := id hodd
        have hM : ((F.blockSide : ℤ) - 1) / 2 = q := by omega
        have hc1 := (LatticePaths.mem_centredCube_iff F.blockSide h1).1 h1c
        rw [LatticePaths.mem_centredCube_iff]
        intro μ
        have h2 := hc1 μ
        by_cases hμ : μ = i
        · subst hμ
          have e : (h1 + (m : ℤ) • basisVector μ) μ = h1 μ + m := by simp [basisVector]
          have e' : h1 μ = h μ + 1 - (F.blockSide : ℤ) := by simp [hh1, basisVector]
          rw [e]
          omega
        · have e : (h1 + (m : ℤ) • basisVector i) μ = h1 μ := by simp [basisVector, hμ]
          rw [e]
          exact h2
      have hHs : ‖((H : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ (F.blockSide - 1 : ℕ) * Nc := by
        have := norm_pathHolonomy_sub_one_le
          (P := fun x => ∃ u ∈ centredCube F.blockSide, x = blockSite E u) (X := W) hc0
          (fun x l h1' h2' => by
            obtain ⟨u, hu, rfl⟩ := h1'
            obtain ⟨u', hu', e'⟩ := h2'
            have e1 : u + basisVector l = u' := by
              rw [blockSite_add_unitStep] at e'
              simp only [blockSite] at e'
              refine siteOfCoords_injOn_small hamb hodd.pos (fun μ => ?_)
                (abs_lt_of_mem_centredCube hodd.pos hu') (add_left_cancel e')
              have h1 := ((LatticePaths.mem_centredCube_iff F.blockSide u).1 hu) μ
              have hp : (1 : ℤ) ≤ (F.blockSide : ℤ) := by exact_mod_cast hodd.pos
              have h2 : |basisVector l μ| ≤ 1 := by
                by_cases hμ : μ = l
                · subst hμ
                  simp [basisVector]
                · simp [basisVector, hμ]
              have h3 := abs_le.1 h2
              rw [abs_lt]
              simp only [Pi.add_apply]
              constructor <;> omega
            exact hinner E hE u l hu (e1 ▸ hu')) _ _ hP
        simpa using this
      have hL1 : (((F.blockSide - 1 : ℕ) : ℝ)) ≤ F.blockSide := by
        exact_mod_cast Nat.sub_le _ _
      have hprod : ((W (blockSite y h) i * (V y i)⁻¹ : UnitQuaternion)) =
          ((k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) * (k E)⁻¹) *
              (V y i)⁻¹) *
            ((V y i) * H⁻¹ * (V y i)⁻¹) := by
        rw [hA]
        group
      have hs : ‖((W (blockSite y h) i * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          Nx + F.blockSide * Nc := by
        rw [hprod]
        refine (norm_coe_mul_sub_one_le _ _).trans ?_
        rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
        have := hNx y hy h i hh hE
        have h3 : ((F.blockSide - 1 : ℕ) : ℝ) * Nc ≤ F.blockSide * Nc :=
          mul_le_mul_of_nonneg_right hL1 hc0
        linarith
      exact (hlg2 _).trans (by linarith)
  · obtain ⟨x, i⟩ := b
    obtain ⟨hx1, hx2⟩ := mem_innerBonds.1 hb
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockSite hx1
    show chartedField _ V (blockSite y h) i = W (blockSite y h) i
    unfold chartedField
    rcases bond_cases hamb hodd (i := i) hh hx2 with ⟨hc, hnc⟩ | ⟨hcr, hi, hE, h1c⟩
    · rw [if_neg hnc]
      by_cases ht : IsAxialTreeBond (blockSite y h, i)
      · rw [if_pos ht, hW, gaugeTransform_treeGauge_inner hamb hodd k X y hh hc,
          pathHolonomy_blockLoop_tree]
        · simp
        · intro l hl
          have := ht.2 l hl
          rwa [cellOffset_blockSite hamb hodd y hh] at this
      · rw [if_neg ht]
        have hmem : (blockSite y h, i) ∈ chordBonds S :=
          Finset.mem_filter.2 ⟨hb, ht⟩
        simp only [hmem, if_true, hnc, if_false]
        exact hlg1 _
    · rw [if_pos hcr]
      have hmem : (blockSite y h, i) ∈ chordBonds S :=
        Finset.mem_filter.2 ⟨hb, fun ht => ht.1 hcr⟩
      simp only [hmem, if_true, hcr]
      rw [hlg1, enclosingCell_blockSite hodd y hh]
      group
end Value
section Patch
theorem baseSite_blockSite_mem_patch {S : Finset F.Cell} {y : F.Cell}
    (hsign : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (hodd : Odd F.blockSide) (hy : y ∈ S) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    baseSite (blockSite y h) ∈ (GaugeMap.patchDomain S y).image (GaugeMap.patchSite S y) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.baseSite_blockPoint_mem_patch <;> assumption
end Patch
section Main
theorem levelScale_depth_succ : levelScale F (F.depth + 1) = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.levelScale_top <;> assumption
theorem levelScale_depth_le_one (hL : 0 < F.blockSide) : levelScale F F.depth ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.levelScale_depth_le_one <;> assumption
end Main
theorem referenceChordNearOne (hB : referenceBoundsStatement) : referenceChordNearOneStatement := by
  classical
  obtain ⟨C, c0, L1, hC, hc0, hbd⟩ := hB
  refine ⟨max L1 1, fun L hL hge => ?_⟩
  have hL1 : L1 ≤ L := le_of_max_le_left hge
  have hLpos : 0 < L := hL.pos
  set Nc : ℝ := 5 * L * C with hNcdef
  set Nx : ℝ := 2 * C with hNxdef
  refine ⟨c0, 2 * (Nx + L * Nc), hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hs1 hcold b hb
  have hodd : Odd F.blockSide := hFL ▸ hL
  obtain ⟨b1, -, -, b4, b5, -⟩ := hbd F m S hodd (hFL ▸ hL1) hamb hm hreg s V hs hs1 hcold
  set R := referenceFieldChain S V with hRdef
  set Xf := R F.depth with hXf
  let kk : F.Cell → UnitQuaternion := fun _ => 1
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  have hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy Xf (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nc * s := by
    intro y hy h i hh hh'
    have hsign := (closedOrthant_spec hreg (by omega) y).1
    have := norm_blockLoop_sub_one_le (R := R F.depth) (X := Xf)
      (g := fun x => (GaugeMap.frameChange S V y (baseSite x))⁻¹)
      (ε := 0) (e := C * s) le_rfl (by positivity) hodd.pos (y := y)
      (P := fun x => x ∈ sitesOfCells S F.depth ∧
        baseSite x ∈ (GaugeMap.patchDomain S y).image (GaugeMap.patchSite S y))
      (fun u hu => ⟨blockSite_mem_sitesOfCells hy hu, baseSite_blockSite_mem_patch hsign hodd hy hu⟩)
      (fun x l h1 h2 => by simp [hXf])
      (fun x l h1 h2 => by
        have h3 := b1 F.depth (by simp [BlockFrame.top]) y hy (x, l)
          (mem_innerBonds.2 ⟨h1.1, h2.1⟩) h1.2 h2.2
        have h4 := levelScale_depth_le_one (F := F) hodd.pos
        have h5 : C * s * levelScale F F.depth ≤ C * s :=
          mul_le_of_le_one_right (by positivity) h4
        exact h3.trans h5) hh hh'
    rw [hLF] at this
    refine this.trans (le_of_eq ?_)
    simp only [hNcdef]
    ring
  have hNx : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      y + siteOfCoords F.top (basisVector i) ∈ S →
      ‖((kk y * pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (kk (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nx * s := by
    intro y hy h i hh hE
    set E := y + siteOfCoords F.top (basisVector i) with hEdef
    have hcb : ((y, i) : F.Site (F.depth + 1) × Fin 4) ∈ innerBonds S (F.depth + 1) :=
      mem_innerBonds.2 ⟨mem_sitesOfCells_top.2 hy, mem_sitesOfCells_top.2 hE⟩
    have h5 := b5 F.depth (by simp [BlockFrame.top]) (y, i) hcb h hh 1
    rw [levelScale_depth_succ, one_pow, mul_one, refineSite_eq_cellCentre] at h5
    have h4 := b4 (y, i) hcb
    set u := polarUnit (contourAverage (R F.depth) ((y, i) : F.Site (F.depth + 1) × Fin 4)) with hu
    have hRtop : R (F.depth + 1) = V := by
      simp only [hRdef, referenceFieldChain]
      exact Function.update_self _ _ _
    have hmis : referenceDefect R F.depth ((y, i) : F.Site (F.depth + 1) × Fin 4) = V y i * u⁻¹ := by
      simp only [referenceDefect, hRtop]
      rfl
    rw [hmis] at h4
    have hprod : kk y * pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (kk E)⁻¹ * (V y i)⁻¹ =
        (pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) * u⁻¹) *
          (V y i * u⁻¹)⁻¹ := by
      simp only [kk, hXf]
      group
    rw [hprod]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    have h6 : unitDeviation
        (pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) * u⁻¹) ≤
        C * s := h5
    have h7 : unitDeviation (V y i * u⁻¹) ≤ C * s := h4
    unfold unitDeviation at h6 h7
    simp only [hNxdef]
    linarith
  obtain ⟨w, h0, hwb, hsame⟩ := exists_chart_of_loops (V := V) (X := Xf) (k := kk) hamb hodd
    (by positivity : 0 ≤ Nc * s) (by positivity : 0 ≤ Nx * s) hNc hNx
  have hbs : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
  have h1 := hsame b hbs
  have hnt : ¬ IsAxialTreeBond b := (Finset.mem_filter.1 hb).2
  have hsize := hwb b hb
  have hel : expUnit (w b.1 b.2) = gaugedBondElement Xf kk V b := by
    obtain ⟨x, i⟩ := b
    simp only [chartedField, gaugeTransform, gaugedBondElement, treeHolonomy] at h1 ⊢
    have hg : ∀ u : F.Site F.depth, treeGauge kk Xf u =
        kk (enclosingCell u) *
          pathHolonomy Xf (cellCentre F.depth (enclosingCell u)) (axisPath (cellOffset u) 1) :=
      fun _ => rfl
    rw [hg, hg] at h1
    by_cases hcr : IsCrossingBond (x, i)
    · rw [if_pos hcr] at h1 ⊢
      rw [eq_mul_inv_iff_mul_eq.2 h1]
      group
    · rw [if_neg hcr, if_neg hnt] at h1
      rw [if_neg hcr, h1]
      group
  have hfin : ‖((gaugedBondElement Xf kk V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(w b.1 b.2 : ℍ[ℝ])‖ := by
    rw [← hel]
    exact norm_exp_sub_one_le (w b.1 b.2).2
  refine hfin.trans (hsize.trans (le_of_eq ?_))
  rw [hLF]
  ring
end YangMills.Construction.BlockAverages.ReferenceChart
end
