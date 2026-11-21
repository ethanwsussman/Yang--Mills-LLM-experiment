import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATopProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.ChartOfTheCriticalField
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.CriticalFieldChart
open LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
section Logarithm
theorem exists_expUnit_eq (g : UnitQuaternion) :
    ∃ w : imaginaryQuaternions, expUnit w = g ∧ ‖(w : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_expUnit_eq <;> assumption
end Logarithm
section Paths
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_nil (j : ℕ) : pathDisplacement (F := F) j [] = 0 := rfl
theorem pathDisplacement_cons (j : ℕ) (st : PathStep) (l : List PathStep) :
    pathDisplacement (F := F) j (st :: l) = stepDisplacement j st + pathDisplacement j l := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathDisplacement_cons <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem stepDisplacement_flip (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j (st.1, !st.2) = - stepDisplacement j st := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.stepDisplacement_flip <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem siteOfCoords_endpoint (j : ℕ) (u : Lattice4) (l : List PathStep) :
    siteOfCoords (F := F) j (endpoint u l) = siteOfCoords j u + pathDisplacement j l := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.siteOfCoords_endpoint <;> assumption
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
theorem linkValue_flip {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
def SitesAlong {j : ℕ} (P : F.Site j → Prop) : F.Site j → List PathStep → Prop
  | x, [] => P x
  | x, st :: r => P x ∧ SitesAlong P (x + stepDisplacement j st) r
theorem SitesAlong.head {j : ℕ} {P : F.Site j → Prop} {x : F.Site j} {l : List PathStep}
    (h : SitesAlong P x l) : P x := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem sitesAlong_of_allAlong {j : ℕ} (P : F.Site j → Prop) (x0 : F.Site j) {u : Lattice4}
    {l : List PathStep} (h : AllAlong (fun v => P (x0 + siteOfCoords j v)) u l) :
    SitesAlong P (x0 + siteOfCoords j u) l := by
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
    ∀ (l : List PathStep) (x : F.Site j), SitesAlong P x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy Y x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy]
  | cons st r ih =>
    intro x hx
    have hnext := SitesAlong.head hx.2
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
        exact SitesAlong.head hx
      · simp only [linkValue, if_true]
        have e1 : x + stepDisplacement j (i, true) = x + unitStep j i := by
          simp [stepDisplacement]
        rw [e1] at hnext
        exact h x i (SitesAlong.head hx) hnext
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
    (l : List PathStep) (x : F.Site j) (hx : SitesAlong P x l) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  have := norm_pathHolonomy_sub_le (X := X) (Y := fun _ _ => (1 : UnitQuaternion)) hε
    (fun y i h1 h2 => by simpa using h y i h1 h2) l x hx
  simpa [pathHolonomy_one] using this
end Paths
section Blocks
def blockSite (y : F.Cell) (h : Lattice4) : F.Site F.depth :=
  cellCentre F.depth y + siteOfCoords F.depth h
theorem mem_centredCube_top_iff (h : Lattice4) :
    h ∈ centredCube (F.blockSide ^ (F.top - F.depth)) ↔ h ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_centredCube_top_iff <;> assumption
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_blockSite (hL : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : enclosingCell (blockSite y h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem valMinAbs_siteOfCoords (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {A : Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (i : Fin 4) :
    ((siteOfCoords F.depth A : F.Site F.depth) i).valMinAbs = A i := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.valMinAbs_siteOfCoords <;> assumption
theorem siteOfCoords_injOn_small (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {A B : Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (hB : ∀ i, |B i| < 32 * (F.blockSide : ℤ))
    (h : (siteOfCoords F.depth A : F.Site F.depth) = siteOfCoords F.depth B) : A = B := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.siteOfCoords_injOn_small <;> assumption
theorem abs_lt_of_mem_centredCube (hL : 0 < F.blockSide) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) : |h i| < 32 * (F.blockSide : ℤ) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.abs_lt_of_mem_centredCube <;> assumption
theorem cellOffset_blockSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) : cellOffset (blockSite y h) = h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.cellOffset_blockPoint <;> assumption
theorem blockSite_add_unitStep (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    blockSite y h + unitStep F.depth i = blockSite y (h + basisVector i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem blockSite_neighbour (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    blockSite (y + siteOfCoords F.top (basisVector i)) h =
      blockSite y (h + (F.blockSide : ℤ) • basisVector i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_neighbour <;> assumption
theorem blockSite_mem_sitesOfCells {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : blockSite y h ∈ sitesOfCells S F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_mem <;> assumption
theorem exists_blockSite_eq {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ h ∈ centredCube F.blockSide, x = blockSite y h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_blockPoint <;> assumption
theorem mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ innerBonds S j ↔ b.1 ∈ sitesOfCells S j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_innerBonds <;> assumption
def treeGauge (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    UnitQuaternion :=
  k (enclosingCell x) * pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
theorem treeGauge_blockSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) :
    treeGauge k X (blockSite y h) = k y * pathHolonomy X (cellCentre F.depth y) (axisPath h 1) := by
  unfold treeGauge
  rw [enclosingCell_blockSite hodd y hh, cellOffset_blockSite hamb hodd y hh]
theorem axisPath_zero (π : Equiv.Perm (Fin 4)) : axisPath (0 : Lattice4) π = [] := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.axisPath_zero <;> assumption
theorem zero_mem_centredCube (hL : 0 < F.blockSide) : (0 : Lattice4) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.zero_mem_centredCube <;> assumption
theorem treeGauge_cellCentre (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) :
    treeGauge k X (cellCentre F.depth y) = k y := by
  have e : cellCentre F.depth y = blockSite y 0 := by simp [blockSite, siteOfCoords_zero]
  rw [e, treeGauge_blockSite hamb hodd k X y (zero_mem_centredCube hodd.pos), axisPath_zero]
  simp [pathHolonomy]
theorem pathDisplacement_axisPath (j : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def blockLoop (h : Lattice4) (i : Fin 4) : List PathStep :=
  axisPath h 1 ++ ((i, true) :: reversePath (axisPath (h + basisVector i) 1))
theorem pathHolonomy_blockLoop (X : F.GaugeField F.depth) (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    pathHolonomy X (cellCentre F.depth y) (blockLoop h i) =
      pathHolonomy X (cellCentre F.depth y) (axisPath h 1) * X (blockSite y h) i *
        (pathHolonomy X (cellCentre F.depth y) (axisPath (h + basisVector i) 1))⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_blockLoop <;> assumption
theorem pathDisplacement_blockLoop (h : Lattice4) (i : Fin 4) :
    pathDisplacement (F := F) F.depth (blockLoop h i) = 0 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathDisplacement_blockLoop <;> assumption
theorem mem_centredCube_of_between {L : ℕ} {h v : Lattice4} (hh : h ∈ centredCube L)
    (hv : BetweenOrigin h v) (hL : 1 ≤ L) : v ∈ centredCube L := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_centredCube_of_between <;> assumption
theorem allAlong_blockLoop {L : ℕ} (hL : 1 ≤ L) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hh' : h + basisVector i ∈ centredCube L) :
    AllAlong (fun v => v ∈ centredCube L) 0 (blockLoop h i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.allAlong_blockLoop <;> assumption
theorem length_axisPath_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).length ≤ 2 * (L - 1) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.length_axisPath_le <;> assumption
theorem length_blockLoop_le {L : ℕ} (hL : 1 ≤ L) {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hh' : h + basisVector i ∈ centredCube L) : (blockLoop h i).length ≤ 5 * L := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.length_blockLoop_le <;> assumption
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
    (k : F.Cell → UnitQuaternion) (X : F.GaugeField F.depth) (y : F.Cell) {h : Lattice4} {i : Fin 4}
    (hh : h ∈ centredCube F.blockSide) (hh' : h + basisVector i ∈ centredCube F.blockSide) :
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
section Crossing
theorem norm_coe_mul_inv_sub_one (a b : UnitQuaternion) :
    ‖((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem norm_polarUnit_sub_le {a b : ℍ[ℝ]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖((polarUnit a : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit b : UnitQuaternion) : ℍ[ℝ])‖ ≤
      2 * ‖a - b‖ / ‖b‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.polarUnit_dist_le <;> assumption
theorem norm_contourAverage_sub_le {X Y : F.GaugeField F.depth} {c : F.Site (F.depth + 1) × Fin 4} {B : ℝ}
    (hodd : Odd F.blockSide)
    (h : ∀ u ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤ B)
    (hB : 0 ≤ B) :
    ‖contourAverage X c - contourAverage Y c‖ ≤ B := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.contourAverage_dist_le <;> assumption
theorem norm_bondContour_holonomy_sub_le {S : Finset F.Cell} {X R : F.GaugeField F.depth} {ε : ℝ}
    (hε : 0 ≤ ε) (hodd : Odd F.blockSide)
    (hXR : ∀ b ∈ innerBonds S F.depth, ‖(X b.1 b.2 : ℍ[ℝ]) - (R b.1 b.2 : ℍ[ℝ])‖ ≤ ε)
    {y : F.Cell} {i : Fin 4}
    (hy : y ∈ S) (hE : y + siteOfCoords F.top (basisVector i) ∈ S) {u : Lattice4}
    (hu : u ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ‖((pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide u π i) : UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy R (cellCentre F.depth y) (bondContour F.blockSide u π i) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      5 * F.blockSide * ε := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.bondContour_dist_le <;> assumption
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem polarUnit_conj {q : ℍ[ℝ]} (hq : q ≠ 0) (a b : UnitQuaternion) :
    polarUnit ((a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])) = a * polarUnit q * b⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.polarUnit_conj <;> assumption
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
    rw [hE, blockSite_neighbour, blockSite_add_unitStep, hh1, sub_add_cancel]
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
    have := blockSite_neighbour y h i
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
theorem exists_chart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {V : F.GaugeField F.top}
    {X : F.GaugeField F.depth} {k : F.Cell → UnitQuaternion} {Nc Nx : ℝ} (hc0 : 0 ≤ Nc) (hx0 : 0 ≤ Nx)
    (hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy X (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Nc)
    (hNx : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      y + siteOfCoords F.top (basisVector i) ∈ S →
      ‖((k y * pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (k (y + siteOfCoords F.top (basisVector i)))⁻¹ * (V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nx) :
    ∃ w : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) ∧
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
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockSite_eq hx1
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
      have hP : SitesAlong (fun x => ∃ u ∈ centredCube F.blockSide, x = blockSite E u) (blockSite E h1)
          (List.replicate (F.blockSide - 1) (i, true)) := by
        refine sitesAlong_of_allAlong _ (cellCentre F.depth E)
          (allAlong_replicate fun m hm => ⟨_, ?_, rfl⟩)
        have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
          simp [FlatPairing.stepDisplacement]
        rw [e0]
        obtain ⟨q, hq⟩ := id hodd
        have hM : ((F.blockSide : ℤ) - 1) / 2 = q := by omega
        have hc1 := (mem_centredCube_iff F.blockSide h1).1 h1c
        rw [mem_centredCube_iff]
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
              have h1 := ((mem_centredCube_iff F.blockSide u).1 hu) μ
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
    obtain ⟨y, hy, h, hh, rfl⟩ := exists_blockSite_eq hx1
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
section Energy
def partialGaugedAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) (j : ℕ) : ℝ :=
  wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
    gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c
theorem wilsonAction_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ U) = wilsonAction S U := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.wilsonAction_gaugeTransform <;> assumption
theorem blockFit_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (γ : F.Site j → UnitQuaternion) (k : F.Site (j + 1) → UnitQuaternion)
    (hγ : ∀ y, γ (refineSite y) = k y)
    (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (gaugeTransform γ X) X' c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.blockFit_gaugeTransform_eq <;> assumption
theorem minimalAction_step_le (hG : gaugeCovarianceStatement) (a : ℝ) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) {j : ℕ} (hj : j < F.top)
    (ih : ∀ (X : F.FieldChain) (k : F.SiteGauge), minimalAction a S j (X j) ≤ partialGaugedAction a S X k j)
    (ha : 0 ≤ a) (X : F.FieldChain) (k : F.SiteGauge) (γ : F.Site j → UnitQuaternion)
    (hγd : ∀ y, γ (refineSite y) = k (j + 1) y) :
    minimalAction a S j (gaugeTransform γ (X j)) +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit (gaugeTransform γ (X j)) (X (j + 1)) c ≤
      partialGaugedAction a S X k (j + 1) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.minimalAction_step_le <;> assumption
theorem minimalAction_le_partial (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement)
    (a : ℝ) (ha : 0 ≤ a) (hL : 0 < F.blockSide) (S : Finset F.Cell) :
    ∀ j, j ≤ F.top → ∀ (X : F.FieldChain) (k : F.SiteGauge),
      minimalAction a S j (X j) ≤ partialGaugedAction a S X k j := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.minimalAction_le_partialGaugedAction <;> assumption
theorem plaquetteHolonomy_congr (S : Finset F.Cell) {j : ℕ} (X X' : F.GaugeField j)
    (h : AgreeOnBonds S j X X')
    (p : F.Site j × Fin 4 × Fin 4) (hp : p ∈ innerPlaquettes S j) :
    plaquetteHolonomy X p = plaquetteHolonomy X' p := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.plaquetteHolonomy_congr <;> assumption
theorem minimalAction_congr (a : ℝ) (S : Finset F.Cell) :
    ∀ (j : ℕ) (A B : F.GaugeField j), AgreeOnBonds S j A B → minimalAction a S j A = minimalAction a S j B
  | 0, A, B, h => by
    simp only [minimalAction, wilsonAction]
    exact Finset.sum_congr rfl fun p hp => by rw [plaquetteHolonomy_congr S A B h p hp]
  | j + 1, A, B, h => by
    simp only [minimalAction]
    refine iInf_congr fun W => ?_
    have : ∑ c ∈ innerBonds S (j + 1), blockFit W A c = ∑ c ∈ innerBonds S (j + 1), blockFit W B c :=
      Finset.sum_congr rfl fun c hc => by
        unfold blockFit
        rw [h c hc]
    rw [this]
end Energy
section Bounds
theorem distFromOne_le_of_quartic {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {θ E : ℝ}
    (hE : 0 ≤ E) (hL : 0 < F.blockSide)
    (hq : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - F.depth) →
      localQuarticSum S R U F.depth p r ≤
        E ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - F.depth)) ^ (4 * θ))
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S F.depth) :
    normSubOne (chartField R U F.depth b.1 b.2 * (R F.depth b.1 b.2)⁻¹) ≤ E := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.normSubOne_le_of_quartic <;> assumption
theorem distFromOne_blockMisfit_le {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {V : F.GaugeField F.top} {E : ℝ} (hE : 0 ≤ E)
    (hm : ∀ z : F.Cell, cellMisfitSum S R U V F.depth 2 z ≤
      (E * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth)) ^ 2)
    {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ innerBonds S (F.depth + 1)) :
    normSubOne (chartBondMisfit R U V F.depth c) ≤ E := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.normSubOne_misfit_le <;> assumption
theorem baseSite_blockSite_mem_patch {S : Finset F.Cell} {y : F.Cell}
    (hsign : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (hodd : Odd F.blockSide) (hy : y ∈ S) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    baseSite (blockSite y h) ∈ (GaugeMap.patchDomain S y).image (GaugeMap.patchSite S y) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.baseSite_blockPoint_mem_patch <;> assumption
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V (F.depth + 1) = V := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.chartChain_top <;> assumption
theorem chartChain_depth (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.depth = chartField R U F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.chartChain_depth <;> assumption
theorem levelScale_depth_succ : levelScale F (F.depth + 1) = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.levelScale_top <;> assumption
theorem levelScale_depth_le_one (hL : 0 < F.blockSide) : levelScale F F.depth ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.levelScale_depth_le_one <;> assumption
end Bounds
theorem criticalFieldChart (hB : referenceBoundsStatement) (hG : gaugeCovarianceStatement)
    (hV : minimalChainExistenceStatement) : criticalFieldChartStatement := by
  classical
  intro a θ del Ca ha _ _ _ _ _
  obtain ⟨C, c0, L1, hC, hc0, hbd⟩ := hB
  refine ⟨max L1 1, fun L hL hge C₁ hC₁ => ?_⟩
  have hL1 : L1 ≤ L := le_of_max_le_left hge
  have hLpos : 0 < L := hL.pos
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  set Nc : ℝ := 5 * L * (C₁ + C) with hNcdef
  set Nx : ℝ := 25 * L * C₁ + C + C₁ with hNxdef
  have hNc0 : 0 < Nc := by positivity
  have hNx0 : 0 < Nx := by positivity
  refine ⟨min c0 (min 1 (min (1 / (2 * C)) (1 / (20 * L * C₁)))), 2 * (Nx + L * Nc),
    lt_min hc0 (lt_min one_pos (lt_min (by positivity) (by positivity))), by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold U hU
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hs1 : s ≤ c0 := hsσ.trans (min_le_left _ _)
  have hs2 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : s ≤ 1 / (2 * C) :=
    hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : s ≤ 1 / (20 * L * C₁) :=
    hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCs : 2 * C * s ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hs3
    linarith
  have hLCs : 20 * L * C₁ * s ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hs4
    linarith
  obtain ⟨b1, -, -, -, b5, b6⟩ := hbd F m S hodd (hFL ▸ hL1) hamb hm hreg s V hs hs1 hcold
  set R := referenceFieldChain S V with hRdef
  set Xf := chartField R U F.depth with hXf
  set kk : F.Cell → UnitQuaternion := chartGauge R U F.top with hkk
  set ε : ℝ := C₁ * s with hεdef
  have hε : 0 ≤ ε := by positivity
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  have hXR : ∀ b ∈ innerBonds S F.depth, ‖(Xf b.1 b.2 : ℍ[ℝ]) - (R F.depth b.1 b.2 : ℍ[ℝ])‖ ≤ ε := by
    intro b hb
    have := distFromOne_le_of_quartic (U := U) hε hodd.pos
      (fun p r h1 h2 => hU.quartic F.depth p r (by simp [BlockFrame.top]) h1 h2) hb
    rw [← norm_coe_mul_inv_sub_one]
    exact this
  have hNc : ∀ y ∈ S, ∀ (h : Lattice4) (i : Fin 4), h ∈ centredCube F.blockSide →
      h + basisVector i ∈ centredCube F.blockSide →
      ‖((pathHolonomy Xf (cellCentre F.depth y) (blockLoop h i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Nc * s := by
    intro y hy h i hh hh'
    have hsign := (closedOrthant_spec hreg (by omega) y).1
    have := norm_blockLoop_sub_one_le (R := R F.depth) (X := Xf)
      (g := fun x => (GaugeMap.frameChange S V y (baseSite x))⁻¹)
      (ε := ε) (e := C * s) hε (by positivity) hodd.pos (y := y)
      (P := fun x => x ∈ sitesOfCells S F.depth ∧
        baseSite x ∈ (GaugeMap.patchDomain S y).image (GaugeMap.patchSite S y))
      (fun u hu => ⟨blockSite_mem_sitesOfCells hy hu, baseSite_blockSite_mem_patch hsign hodd hy hu⟩)
      (fun x l h1 h2 => hXR (x, l) (mem_innerBonds.2 ⟨h1.1, h2.1⟩))
      (fun x l h1 h2 => by
        have h3 := b1 F.depth (by simp [BlockFrame.top]) y hy (x, l) (mem_innerBonds.2 ⟨h1.1, h2.1⟩)
          h1.2 h2.2
        have h4 := levelScale_depth_le_one (F := F) hodd.pos
        have h5 : C * s * levelScale F F.depth ≤ C * s :=
          mul_le_of_le_one_right (by positivity) h4
        exact h3.trans h5) hh hh'
    rw [hLF] at this
    refine this.trans (le_of_eq ?_)
    simp only [hNcdef, hεdef]
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
    set cmX := contourAverage Xf ((y, i) : F.Site (F.depth + 1) × Fin 4) with hcmX
    set cmR := contourAverage (R F.depth) ((y, i) : F.Site (F.depth + 1) × Fin 4) with hcmR
    set B : ℝ := 5 * F.blockSide * ε with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hB4 : B ≤ 1 / 4 := by
      simp only [hBdef, hεdef, hLF]
      nlinarith
    have hclose : ‖cmX - cmR‖ ≤ B := by
      refine norm_contourAverage_sub_le hodd (fun u hu π => ?_) hB0
      have := norm_bondContour_holonomy_sub_le hε hodd hXR hy hE hu π
      rw [← refineSite_eq_cellCentre] at this
      exact this
    have h5 := b5 F.depth (by simp [BlockFrame.top]) (y, i) hcb h hh 1
    have h6 := (b6 F.depth (by simp [BlockFrame.top]) (y, i) hcb).2
    rw [levelScale_depth_succ, one_pow, mul_one] at h5 h6
    have hnR : 1 / 2 ≤ ‖cmR‖ := by
      have : C * s ^ 2 ≤ 1 / 2 := by nlinarith
      linarith
    have hR0 : cmR ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnR
      linarith
    have hX0 : cmX ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg] at hclose
      linarith
    have hu := norm_polarUnit_sub_le hX0 hR0
    have hu2 : ‖((polarUnit cmX : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ])‖ ≤
        4 * B := by
      refine hu.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (cmX - cmR)]
    have hcc := norm_bondContour_holonomy_sub_le hε hodd hXR hy hE hh 1
    have h5' : ‖((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
          UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ])‖ ≤ C * s := by
      rw [← norm_coe_mul_inv_sub_one, ← refineSite_eq_cellCentre]
      exact h5
    have hhu : ‖((pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
        (polarUnit cmX)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * B + C * s := by
      rw [norm_coe_mul_inv_sub_one]
      have t1 := norm_sub_le_norm_sub_add_norm_sub
        ((pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) : UnitQuaternion) : ℍ[ℝ])
        ((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
          UnitQuaternion) : ℍ[ℝ])
        ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])
      have t2 := norm_sub_le_norm_sub_add_norm_sub
        ((pathHolonomy (R F.depth) (cellCentre F.depth y) (bondContour F.blockSide h 1 i) :
          UnitQuaternion) : ℍ[ℝ])
        ((polarUnit cmR : UnitQuaternion) : ℍ[ℝ]) ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])
      have t3 : ‖((polarUnit cmR : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit cmX : UnitQuaternion) : ℍ[ℝ])‖ ≤
          4 * B := by
        rw [norm_sub_rev]
        exact hu2
      linarith
    have hmis := distFromOne_blockMisfit_le (U := U) (V := V) hε
      (fun z => (hU.misfits_on_cells F.depth z (by simp [BlockFrame.top])).2) hcb
    have hfm : polarUnit (gaugedContourAverage (chartChain R U V F.depth) (chartGauge R U (F.depth + 1))
        ((y, i) : F.Site (F.depth + 1) × Fin 4)) = kk y * polarUnit cmX * (kk E)⁻¹ := by
      rw [chartChain_depth, ← polarUnit_conj hX0]
      rfl
    have hM : normSubOne (chartBondMisfit R U V F.depth ((y, i) : F.Site (F.depth + 1) × Fin 4)) =
        ‖((V y i * (kk y * polarUnit cmX * (kk E)⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      unfold chartBondMisfit
      rw [hfm, chartChain_top]
      rfl
    rw [hM] at hmis
    have hprod : kk y * pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
          (kk E)⁻¹ * (V y i)⁻¹ =
        (kk y * (pathHolonomy Xf (cellCentre F.depth y) (bondContour F.blockSide h 1 i) *
            (polarUnit cmX)⁻¹) * (kk y)⁻¹) *
          (V y i * (kk y * polarUnit cmX * (kk E)⁻¹)⁻¹)⁻¹ := by
      group
    rw [hprod]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    have e5 : 5 * B + C * s + ε = Nx * s := by
      simp only [hBdef, hεdef, hNxdef, hLF]
      ring
    linarith
  obtain ⟨w, h0, hb, hsame⟩ := exists_chart (V := V) (X := Xf) (k := kk) hamb hodd
    (by positivity : 0 ≤ Nc * s) (by positivity : 0 ≤ Nx * s) hNc hNx
  set γ := treeGauge kk Xf with hγ
  have hcent : ∀ y : F.Cell, γ (cellCentre F.depth y) = kk y :=
    fun y => treeGauge_cellCentre hamb hodd kk Xf y
  refine ⟨w, γ, h0, fun b hb' => ?_, hsame, ?_, fun z _ => hcent z⟩
  · refine (hb b hb').trans (le_of_eq ?_)
    rw [hLF]
    ring
  · have hzero : ∀ b ∈ innerBonds S F.depth, ‖((chartedField w V b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((gaugeTransform γ Xf b.1 b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ 0 := by
      intro b hb'
      rw [hsame b hb', sub_self, norm_zero]
    have hfit : ∑ c ∈ innerBonds S (F.depth + 1), blockFit (chartedField w V) V c =
        ∑ c ∈ innerBonds S (F.depth + 1), blockFit (gaugeTransform γ Xf) V c := by
      refine Finset.sum_congr rfl fun c hc => ?_
      obtain ⟨y, i⟩ := c
      obtain ⟨hc1, hc2⟩ := mem_innerBonds.1 hc
      have hy : y ∈ S := mem_sitesOfCells_top.1 hc1
      have hE : y + siteOfCoords F.top (basisVector i) ∈ S := mem_sitesOfCells_top.1 hc2
      have hm0 : contourAverage (chartedField w V) ((y, i) : F.Site (F.depth + 1) × Fin 4) =
          contourAverage (gaugeTransform γ Xf) ((y, i) : F.Site (F.depth + 1) × Fin 4) := by
        have := norm_contourAverage_sub_le (X := chartedField w V) (Y := gaugeTransform γ Xf)
          (c := ((y, i) : F.Site (F.depth + 1) × Fin 4)) (B := 0) hodd (fun u hu π => by
            have h1 := norm_bondContour_holonomy_sub_le le_rfl hodd hzero hy hE hu π
            rw [mul_zero, ← refineSite_eq_cellCentre] at h1
            exact h1) le_rfl
        exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
      unfold blockFit
      rw [hm0]
    have hstep := minimalAction_step_le hG a hodd.pos S (j := F.depth) (by simp [BlockFrame.top])
      (fun X k => minimalAction_le_partial hG hV a ha.le hodd.pos S F.depth (by simp [BlockFrame.top]) X k)
      ha.le (chartChain R U V) (chartGauge R U) γ (fun y => by
        rw [refineSite_eq_cellCentre]
        exact hcent y)
    rw [chartChain_depth, chartChain_top] at hstep
    unfold blockEnergy
    rw [minimalAction_congr a S F.depth _ _ hsame, hfit]
    exact hstep
end YangMills.Construction.BlockAverages.CriticalFieldChart
end
