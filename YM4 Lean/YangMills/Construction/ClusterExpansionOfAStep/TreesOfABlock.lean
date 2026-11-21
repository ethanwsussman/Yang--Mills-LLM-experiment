import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts
namespace BlockTrees
section Paths
variable {F : BlockFrame} {j : ℕ}
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_append (l l' : List PathStep) :
    (pathDisplacement j (l ++ l') : F.Site j) = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathHolonomy_append (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_replicate (k : ℕ) (st : PathStep) :
    (pathDisplacement j (List.replicate k st) : F.Site j) = k • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem pathHolonomy_singleton (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    pathHolonomy X x [st] = linkValue X x st := by
  simp [pathHolonomy]
theorem pathHolonomy_line_succ (X : F.GaugeField j) (i : Fin 4) (a : ℤ) (P : List PathStep) (c : F.Site j) :
    pathHolonomy X c (P ++ List.replicate (a + 1).natAbs (i, decide (0 ≤ a + 1))) =
      pathHolonomy X c (P ++ List.replicate a.natAbs (i, decide (0 ≤ a))) *
        X (c + pathDisplacement j (P ++ List.replicate a.natAbs (i, decide (0 ≤ a)))) i := by
  by_cases ha : 0 ≤ a
  · have h1 : (a + 1).natAbs = a.natAbs + 1 := by omega
    have d1 : decide (0 ≤ a + 1) = true := decide_eq_true (by omega)
    have d2 : decide (0 ≤ a) = true := decide_eq_true ha
    rw [h1, d1, d2, List.replicate_succ', ← List.append_assoc, pathHolonomy_append, pathHolonomy_singleton]
    simp [linkValue]
  · have hb : a.natAbs = (a + 1).natAbs + 1 := by omega
    have d2 : decide (0 ≤ a) = false := decide_eq_false ha
    rw [hb, d2, List.replicate_succ', ← List.append_assoc]
    have hcase : pathHolonomy X c (P ++ List.replicate (a + 1).natAbs (i, decide (0 ≤ a + 1))) =
        pathHolonomy X c (P ++ List.replicate (a + 1).natAbs (i, false)) := by
      by_cases h0 : a + 1 = 0
      · simp [h0]
      · have : decide (0 ≤ a + 1) = false := decide_eq_false (by omega)
        rw [this]
    set Q := P ++ List.replicate (a + 1).natAbs (i, false) with hQd
    have hQ : pathHolonomy X c (Q ++ [(i, false)]) =
        pathHolonomy X c Q * linkValue X (c + pathDisplacement j Q) (i, false) := by
      rw [pathHolonomy_append, pathHolonomy_singleton]
    have hs : (pathDisplacement j (Q ++ [(i, false)]) : F.Site j) = pathDisplacement j Q - BlockAverages.unitStep j i := by
      rw [pathDisplacement_append]
      simp [pathDisplacement, stepDisplacement, sub_eq_add_neg]
    rw [hcase, hQ, hs]
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [← add_sub_assoc c, mul_assoc]
    simp
theorem nsmul_stepDisplacement_line (a : ℤ) (i : Fin 4) :
    (a.natAbs • stepDisplacement j (i, decide (0 ≤ a)) : F.Site j) = siteOfCoords j (Pi.single i a) := by
  funext l
  by_cases hl : l = i
  · subst hl
    by_cases h0 : 0 ≤ a
    · have e : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg h0
      have : ((a.natAbs : ℕ) : ZMod (F.period j l)) = ((a : ℤ) : ZMod (F.period j l)) := by
        rw [← e]; simp
      simp [stepDisplacement, h0, BlockAverages.unitStep, siteOfCoords, this]
    · have e : (a.natAbs : ℤ) = -a := by omega
      have : ((a.natAbs : ℕ) : ZMod (F.period j l)) = ((-a : ℤ) : ZMod (F.period j l)) := by
        rw [← e]; simp
      simp [stepDisplacement, h0, BlockAverages.unitStep, siteOfCoords, this]
  · have hs : ∀ b : Bool, (stepDisplacement j (i, b) : F.Site j) l = 0 := by
      intro b
      cases b <;> simp [stepDisplacement, BlockAverages.unitStep, siteOfCoords, hl]
    simp [hs, siteOfCoords, hl]
def axisSegment (h : Fin 4 → ℤ) (i : Fin 4) : List PathStep :=
  List.replicate (h i).natAbs (i, decide (0 ≤ h i))
theorem axisPath_eq_segments (h : Fin 4 → ℤ) :
    axisPath h 1 = axisSegment h 0 ++ (axisSegment h 1 ++ (axisSegment h 2 ++ axisSegment h 3)) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_one_eq <;> assumption
theorem pathDisplacement_axisPath (h : Fin 4 → ℤ) : (pathDisplacement j (axisPath h 1) : F.Site j) = siteOfCoords j h := by
  rw [axisPath_eq_segments]
  simp only [axisSegment, pathDisplacement_append, pathDisplacement_replicate, nsmul_stepDisplacement_line]
  rw [← siteOfCoords_add, ← siteOfCoords_add, ← siteOfCoords_add]
  congr 1
  funext l
  fin_cases l <;> simp
theorem pathHolonomy_axisPath_add_single (X : F.GaugeField j) (c : F.Site j) (o : Fin 4 → ℤ) (i : Fin 4)
    (hz : ∀ l, i < l → o l = 0) :
    pathHolonomy X c (axisPath (o + Pi.single i 1) 1) =
      pathHolonomy X c (axisPath o 1) * X (c + siteOfCoords j o) i := by
  set o' := o + Pi.single i (1 : ℤ) with ho'
  have hother : ∀ l, l ≠ i → o' l = o l := fun l hl => by simp [ho', Pi.single_eq_of_ne hl]
  have hsame : o' i = o i + 1 := by simp [ho']
  have hP : ∃ P : List PathStep,
      axisPath o 1 = P ++ List.replicate (o i).natAbs (i, decide (0 ≤ o i)) ∧
      axisPath o' 1 = P ++ List.replicate (o i + 1).natAbs (i, decide (0 ≤ o i + 1)) := by
    have e : ∀ h : Fin 4 → ℤ, axisPath h 1 = axisSegment h 0 ++ (axisSegment h 1 ++ (axisSegment h 2 ++ axisSegment h 3)) :=
      axisPath_eq_segments
    have zl : ∀ l, i < l → axisSegment o l = [] := fun l hl => by simp [axisSegment, hz l hl]
    have zl' : ∀ l, i < l → axisSegment o' l = [] := fun l hl => by
      simp [axisSegment, hother l (ne_of_gt hl), hz l hl]
    have el : ∀ l, l ≠ i → axisSegment o' l = axisSegment o l := fun l hl => by
      simp [axisSegment, hother l hl]
    have ei' : axisSegment o' i = List.replicate (o i + 1).natAbs (i, decide (0 ≤ o i + 1)) := by
      simp [axisSegment, hsame]
    have ei : axisSegment o i = List.replicate (o i).natAbs (i, decide (0 ≤ o i)) := rfl
    fin_cases i
    · refine ⟨[], ?_, ?_⟩
      · rw [e, zl 1 (by decide), zl 2 (by decide), zl 3 (by decide)]
        simpa using ei
      · rw [e, zl' 1 (by decide), zl' 2 (by decide), zl' 3 (by decide)]
        simpa using ei'
    · refine ⟨axisSegment o 0, ?_, ?_⟩
      · rw [e, zl 2 (by decide), zl 3 (by decide)]
        simpa using ei
      · rw [e, zl' 2 (by decide), zl' 3 (by decide), el 0 (by decide)]
        simpa using ei'
    · refine ⟨axisSegment o 0 ++ axisSegment o 1, ?_, ?_⟩
      · rw [e, zl 3 (by decide)]
        simpa using ei
      · rw [e, zl' 3 (by decide), el 0 (by decide), el 1 (by decide)]
        simpa using ei'
    · refine ⟨axisSegment o 0 ++ (axisSegment o 1 ++ axisSegment o 2), ?_, ?_⟩
      · rw [e]
        simpa using ei
      · rw [e, el 0 (by decide), el 1 (by decide), el 2 (by decide)]
        simpa using ei'
  obtain ⟨P, h1, h2⟩ := hP
  rw [h2, pathHolonomy_line_succ, ← h1, pathDisplacement_axisPath]
end Paths
section Cells
variable {F : BlockFrame}
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) : enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem top_sub_depth : F.top - F.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem mem_centredCube_top {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) : h ∈ centredCube (F.blockSide ^ (F.top - F.depth)) := by
  rw [top_sub_depth, pow_one]
  exact hh
theorem period_depth (i : Fin 4) : ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * F.blockSide := by
  simp [BlockFrame.period]
theorem eq_cellCentre_add_cellOffset (x : F.Site F.depth) :
    x = cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) := by
  funext i
  have : (siteOfCoords F.depth (cellOffset x) : F.Site F.depth) i = (x - cellCentre F.depth (enclosingCell x)) i := by
    simp [siteOfCoords, cellOffset]
  simp [this]
theorem two_mul_abs_lt_of_mem_centredCube {L : ℕ} (hL : Odd L) {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) (i : Fin 4) :
    2 * |h i| < L := by
  have hi := Fintype.mem_piFinset.1 hh i
  rw [Finset.mem_Icc] at hi
  obtain ⟨m, hm⟩ := hL
  have : ((L : ℤ) - 1) / 2 = m := by omega
  rw [this] at hi
  have h1 : |h i| ≤ m := abs_le.mpr hi
  omega
theorem mem_centredCube_iff {L : ℕ} {h : Fin 4 → ℤ} : h ∈ centredCube L ↔ ∀ i, |h i| ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem two_mul_blockSide_le_period (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    2 * (F.blockSide : ℤ) ≤ ((F.period F.depth i : ℕ) : ℤ) := by
  rw [period_depth]
  have h1 : (2 : ℤ) ≤ F.extent i := by exact_mod_cast hs i
  nlinarith
theorem cellOffset_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) : cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem cellOffset_mem_centredCube (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    cellOffset x ∈ centredCube F.blockSide := by
  rw [mem_centredCube_iff]
  intro i
  obtain ⟨m, hm⟩ := hL
  have hmd : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  rw [hmd]
  set u : ℤ := siteCoords x i with hu
  set q : ℤ := (u + m) / F.blockSide with hq
  set ρ' : ℤ := (u + m) % F.blockSide with hρ
  have hLpos : (0 : ℤ) < F.blockSide := by omega
  have hρ0 : 0 ≤ ρ' := Int.emod_nonneg _ hLpos.ne'
  have hρ1 : ρ' < F.blockSide := Int.emod_lt_of_pos _ hLpos
  have hdecomp : u + m = F.blockSide * q + ρ' := (Int.mul_ediv_add_emod _ _).symm
  have hcell : (enclosingCell x : F.Cell) i = ((q : ℤ) : ZMod (F.period F.top i)) := by
    unfold enclosingCell
    simp only [siteOfCoords, top_sub_depth, pow_one]
    rw [hmd]
  have hper2 : ((F.period F.top i : ℕ) : ℤ) = (F.extent i : ℤ) := by
    simp [BlockFrame.period]
  have hcoord : ((siteCoords (enclosingCell x : F.Cell) i : ℤ) : ZMod (F.period F.top i)) = ((q : ℤ) : ZMod (F.period F.top i)) := by
    unfold siteCoords
    rw [ZMod.intCast_zmod_cast, hcell]
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcoord
  rw [hper2] at he
  have hcentre : ((cellCentre F.depth (enclosingCell x) : F.Site F.depth) i) =
      (((F.blockSide : ℤ) * (q - (F.extent i : ℤ) * e) : ℤ) : ZMod (F.period F.depth i)) := by
    have : siteCoords (enclosingCell x : F.Cell) i = q - (F.extent i : ℤ) * e := by linarith
    simp only [cellCentre, siteOfCoords, top_sub_depth, pow_one, this]
  have hxi : x i = ((u : ℤ) : ZMod (F.period F.depth i)) := by
    rw [hu]
    unfold siteCoords
    exact (ZMod.intCast_zmod_cast (x i)).symm
  have hdiff : ((x - cellCentre F.depth (enclosingCell x) : F.Site F.depth) i) = ((ρ' - m : ℤ) : ZMod (F.period F.depth i)) := by
    rw [Pi.sub_apply, hxi, hcentre, ← Int.cast_sub]
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    rw [period_depth]
    refine ⟨-e, ?_⟩
    have : u = F.blockSide * q + ρ' - m := by linarith
    rw [this]
    ring
  have hoff : cellOffset x i = ρ' - m := by
    unfold cellOffset
    rw [hdiff]
    apply valMinAbs_intCast_of_small
    right
    have h2 := two_mul_blockSide_le_period ⟨m, hm⟩ hs i
    have : |ρ' - m| ≤ m := abs_le.mpr ⟨by omega, by omega⟩
    omega
  rw [hoff]
  exact abs_le.mpr ⟨by omega, by omega⟩
theorem cellOffset_add_unitStep (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4)
    (hc : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x) :
    cellOffset (x + BlockAverages.unitStep F.depth i) = cellOffset x + Pi.single i 1 := by
  have h1 := eq_cellCentre_add_cellOffset x
  have h2 := eq_cellCentre_add_cellOffset (x + BlockAverages.unitStep F.depth i)
  rw [hc] at h2
  have h3 : (siteOfCoords F.depth (cellOffset (x + BlockAverages.unitStep F.depth i)) : F.Site F.depth) =
      siteOfCoords F.depth (cellOffset x) + siteOfCoords F.depth (Pi.single i 1) := by
    have : cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset (x + BlockAverages.unitStep F.depth i)) =
        cellCentre F.depth (enclosingCell x) + (siteOfCoords F.depth (cellOffset x) + siteOfCoords F.depth (Pi.single i 1)) := by
      rw [← h2, ← add_assoc, ← h1]
      rfl
    exact add_left_cancel this
  funext l
  have h4 := congrFun h3 l
  simp only [siteOfCoords, Pi.add_apply] at h4
  rw [← Int.cast_add] at h4
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h4
  have b1 := two_mul_abs_lt_of_mem_centredCube hL (cellOffset_mem_centredCube hL hs x) l
  have b2 := two_mul_abs_lt_of_mem_centredCube hL (cellOffset_mem_centredCube hL hs (x + BlockAverages.unitStep F.depth i)) l
  have b3 := two_mul_blockSide_le_period hL hs l
  have hsingle : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
    by_cases hl : l = i
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  have hLpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  set d := cellOffset x l + (Pi.single i (1 : ℤ) : Fin 4 → ℤ) l -
    cellOffset (x + BlockAverages.unitStep F.depth i) l with hd
  have hdz : d = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd (m := ((F.period F.depth l : ℕ) : ℤ)) ⟨e, he⟩
    obtain ⟨p1, p2⟩ := abs_le.mp (le_refl |cellOffset x l|)
    obtain ⟨p3, p4⟩ := abs_le.mp (le_refl |cellOffset (x + BlockAverages.unitStep F.depth i) l|)
    obtain ⟨p5, p6⟩ := abs_le.mp hsingle
    rw [abs_lt]
    constructor <;> omega
  simp only [Pi.add_apply]
  omega
theorem axialGauge_add_unitStep (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (W : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4)
    (ht : IsAxialTreeBond (x, i)) : axialGauge 1 W (x + BlockAverages.unitStep F.depth i) = axialGauge 1 W x * W x i := by
  have hc : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := not_not.mp ht.1
  unfold axialGauge
  rw [hc, cellOffset_add_unitStep hL hs x i hc, pathHolonomy_axisPath_add_single W _ _ i ht.2, ← eq_cellCentre_add_cellOffset]
theorem pathHolonomy_axisPath_congr (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (W W' : F.GaugeField F.depth) (c : F.Cell)
    (h : ∀ x i, enclosingCell x = c → IsAxialTreeBond (x, i) → W x i = W' x i) (k : ℕ) :
    ∀ o, o ∈ centredCube F.blockSide → ∑ l, (o l).natAbs = k →
      pathHolonomy W (cellCentre F.depth c) (axisPath o 1) = pathHolonomy W' (cellCentre F.depth c) (axisPath o 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro o ho hk
    by_cases h0 : o = 0
    · subst h0
      have e0 : axisPath (0 : Fin 4 → ℤ) 1 = [] := by
        simp [axisPath, List.finRange_succ, List.flatMap_cons]
      rw [e0]
      rfl
    obtain ⟨i, hi, hmax⟩ : ∃ i, o i ≠ 0 ∧ ∀ l, i < l → o l = 0 := by
      have hne : (Finset.univ.filter fun l => o l ≠ 0).Nonempty := by
        by_contra hcon
        apply h0
        funext l
        by_contra hl
        exact hcon ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hl⟩⟩
      refine ⟨(Finset.univ.filter fun l => o l ≠ 0).max' hne, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
      · intro l hl
        by_contra hol
        exact absurd (Finset.le_max' _ l (by simp [hol])) (not_le.mpr hl)
    have hside (p : Fin 4 → ℤ) (hp : p ∈ centredCube F.blockSide) (hp' : p + Pi.single i 1 ∈ centredCube F.blockSide)
        (hz : ∀ l, i < l → p l = 0) :
        W (cellCentre F.depth c + siteOfCoords F.depth p) i = W' (cellCentre F.depth c + siteOfCoords F.depth p) i := by
      apply h _ _ (enclosingCell_cellCentre_add hL c p (mem_centredCube_top hp))
      refine ⟨?_, ?_⟩
      · show ¬ ¬ _
        rw [not_not, enclosingCell_cellCentre_add hL c p (mem_centredCube_top hp)]
        have : (cellCentre F.depth c + siteOfCoords F.depth p + BlockAverages.unitStep F.depth i : F.Site F.depth) =
            cellCentre F.depth c + siteOfCoords F.depth (p + Pi.single i 1) := by
          rw [siteOfCoords_add, add_assoc]
          rfl
        rw [this]
        exact enclosingCell_cellCentre_add hL c _ (mem_centredCube_top hp')
      · intro l hl
        show cellOffset (cellCentre F.depth c + siteOfCoords F.depth p : F.Site F.depth) l = 0
        rw [cellOffset_cellCentre_add hL hs c p hp]
        exact hz l hl
    have hsum (p : Fin 4 → ℤ) (hlt : (p i).natAbs < (o i).natAbs) (hoth : ∀ l, l ≠ i → p l = o l) :
        ∑ l, (p l).natAbs < k := by
      rw [← hk]
      apply Finset.sum_lt_sum
      · intro l _
        by_cases hl : l = i
        · subst hl; exact hlt.le
        · rw [hoth l hl]
      · exact ⟨i, Finset.mem_univ _, hlt⟩
    have hmem (p : Fin 4 → ℤ) (hlt : (p i).natAbs < (o i).natAbs) (hoth : ∀ l, l ≠ i → p l = o l) :
        p ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff] at ho ⊢
      intro l
      by_cases hl : l = i
      · subst hl
        have := ho l
        have e1 : |p l| = ((p l).natAbs : ℤ) := Int.abs_eq_natAbs _
        have e2 : |o l| = ((o l).natAbs : ℤ) := Int.abs_eq_natAbs _
        omega
      · rw [hoth l hl]
        exact ho l
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · set p := o + Pi.single i (1 : ℤ) with hp
      have hpi : p i = o i + 1 := by simp [hp]
      have hoth : ∀ l, l ≠ i → p l = o l := fun l hl => by simp [hp, Pi.single_eq_of_ne hl]
      have hlt : (p i).natAbs < (o i).natAbs := by omega
      have t := pathHolonomy_axisPath_add_single W (cellCentre F.depth c) o i hmax
      have t' := pathHolonomy_axisPath_add_single W' (cellCentre F.depth c) o i hmax
      have e := ih _ (hsum p hlt hoth) p (hmem p hlt hoth) rfl
      rw [← hp] at t t'
      rw [t, t', hside o ho (hmem p hlt hoth) hmax] at e
      exact mul_right_cancel e
    · set p := o - Pi.single i (1 : ℤ) with hp
      have hpi : p i = o i - 1 := by simp [hp]
      have hoth : ∀ l, l ≠ i → p l = o l := fun l hl => by simp [hp, Pi.single_eq_of_ne hl]
      have hlt : (p i).natAbs < (o i).natAbs := by omega
      have hz : ∀ l, i < l → p l = 0 := fun l hl => by
        rw [hoth l (ne_of_gt hl)]
        exact hmax l hl
      have hback : p + Pi.single i 1 = o := by simp [hp]
      have t := pathHolonomy_axisPath_add_single W (cellCentre F.depth c) p i hz
      have t' := pathHolonomy_axisPath_add_single W' (cellCentre F.depth c) p i hz
      rw [hback] at t t'
      rw [t, t', ih _ (hsum p hlt hoth) p (hmem p hlt hoth) rfl,
        hside p (hmem p hlt hoth) (by rw [hback]; exact ho) hz]
theorem axialGauge_congr (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (W W' : F.GaugeField F.depth) (x : F.Site F.depth)
    (h : ∀ z i, enclosingCell z = enclosingCell x → IsAxialTreeBond (z, i) → W z i = W' z i) :
    axialGauge 1 W x = axialGauge 1 W' x :=
  pathHolonomy_axisPath_congr hL hs W W' (enclosingCell x) h _ _ (cellOffset_mem_centredCube hL hs x) rfl
end Cells
section Haar
instance instSecondCountableTopologyUnitQuaternion : SecondCountableTopology UnitQuaternion :=
  TopologicalSpace.Subtype.secondCountableTopology _
theorem expUnit_coe (w : imaginaryQuaternions) : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) =
    ((Real.cos ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) :=
  Quaternion.exp_of_re_eq_zero _ w.2
theorem expUnit_re (w : imaginaryQuaternions) : ((expUnit w : UnitQuaternion) : ℍ[ℝ]).re = Real.cos ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.re_coe_expUnit <;> assumption
theorem norm_le_of_expUnit_eq {w w' : imaginaryQuaternions} (h : expUnit w = expUnit w') (hw : ‖(w : ℍ[ℝ])‖ < Real.pi) :
    ‖(w : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := Real.strictAntiOn_cos ⟨norm_nonneg (w' : ℍ[ℝ]), (hlt.trans hw).le⟩
    ⟨norm_nonneg (w : ℍ[ℝ]), hw.le⟩ hlt
  have h2 := congrArg (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re) h
  simp only [expUnit_re] at h2
  linarith
theorem eq_of_expUnit_eq {w w' : imaginaryQuaternions} (h : expUnit w = expUnit w') (hw : ‖(w : ℍ[ℝ])‖ < Real.pi)
    (hw' : ‖(w' : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ])‖) : w = w' := by
  have hab : ‖(w' : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := le_antisymm hw' (norm_le_of_expUnit_eq h hw)
  by_cases h0 : ‖(w : ℍ[ℝ])‖ = 0
  · have a1 : (w : ℍ[ℝ]) = 0 := norm_eq_zero.mp h0
    have a2 : (w' : ℍ[ℝ]) = 0 := norm_eq_zero.mp (hab.trans h0)
    exact Subtype.ext (a1.trans a2.symm)
  · have hp : 0 < ‖(w : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hs : Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖ ≠ 0 :=
      div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hp hw).ne' h0
    have h2 := congrArg (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ])) h
    simp only [expUnit_coe, hab] at h2
    exact Subtype.ext (smul_right_injective _ hs (add_left_cancel h2))
theorem minimalLog_expUnit {w : imaginaryQuaternions} (hw : ‖(w : ℍ[ℝ])‖ < Real.pi) : minimalLog (expUnit w) = w := by apply _root_.YangMills.Construction.GaugeFixing.minimalLog_expUnit <;> assumption
end Haar
section Points
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖(toImaginary v : ℍ[ℝ])‖ = ‖v‖ := by
  have h1 : ‖(toImaginary v : ℍ[ℝ])‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [toImaginary, Fin.sum_univ_three]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
theorem toImaginary_toCoords (w : imaginaryQuaternions) : toImaginary (toCoords w) = w := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  apply Subtype.ext
  ext <;> simp [toImaginary, toCoords, hw]
theorem toImaginary_sub (a b : EuclideanSpace ℝ (Fin 3)) : (toImaginary (a - b) : ℍ[ℝ]) = (toImaginary a : ℍ[ℝ]) - (toImaginary b : ℍ[ℝ]) := by
  ext
  · show (0 : ℝ) = 0 - 0
    simp
  · show (a - b) 0 = a 0 - b 0
    simp
  · show (a - b) 1 = a 1 - b 1
    simp
  · show (a - b) 2 = a 2 - b 2
    simp
theorem toImaginary_injective {a b : EuclideanSpace ℝ (Fin 3)} (h : toImaginary a = toImaginary b) : a = b := by
  have h1 : ‖a - b‖ = 0 := by
    rw [← norm_toImaginary, toImaginary_sub, h]
    simp
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)
end Points
section Transfer
variable {L n : ℕ}
theorem intCast_cast_intCast_cast {m k : ℕ} (hm : m = k) [NeZero m] (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod k).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.WeightedResponses.intCast_cast_intCast_cast_of_eq <;> assumption
theorem intCast_cast_add {P M : ℕ} (h : P = M) [NeZero M] (a b : ZMod M) :
    ((((a + b).cast : ℤ)) : ZMod P) = (((a.cast : ℤ)) : ZMod P) + ((b.cast : ℤ) : ZMod P) := by
  subst h
  simp
theorem intCast_cast_intCast {P M : ℕ} (h : P = M) [NeZero M] (z : ℤ) :
    ((((z : ZMod M).cast : ℤ)) : ZMod P) = (z : ZMod P) := by
  subst h
  simp
theorem cast_intCast_cast {P M : ℕ} (h : P = M) [NeZero M] (a : ZMod M) :
    (ZMod.cast (((a.cast : ℤ)) : ZMod P) : ℤ) = a.cast := by
  subst h
  simp
theorem stepBlockFrame_period_zero (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by apply _root_.YangMills.Construction.BlockOffsets.period_zero <;> assumption
theorem stepBlockFrame_period_one (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by apply _root_.YangMills.Construction.BlockOffsets.period_one <;> assumption
theorem readAtLevel_torusSiteInFrame {m : ℕ} [NeZero m] (F : BlockFrame) (j : ℕ) (hper : ∀ i, F.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) : readAtLevel F j W (torusSiteInFrame F j x) i = W x i := by
  have : (fun k => ((siteCoords (torusSiteInFrame F j x : F.Site j) k : ℤ) : ZMod m)) = x := by
    funext k
    exact intCast_cast_intCast_cast (hper k).symm (x k)
  unfold readAtLevel
  rw [this]
theorem torusSiteInFrame_surjective {m : ℕ} [NeZero m] (F : BlockFrame) (j : ℕ) (hper : ∀ i, F.period j i = m) (z : F.Site j) :
    ∃ x : TorusSite m, torusSiteInFrame F j x = z := by
  have hne : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    rw [hper]
    exact NeZero.ne m⟩
  refine ⟨fun k => (((z k).cast : ℤ) : ZMod m), ?_⟩
  funext i
  have := hne i
  exact intCast_cast_intCast_cast (hper i) (z i)
theorem torusSiteInFrame_injective {m : ℕ} [NeZero m] (F : BlockFrame) (j : ℕ) (hper : ∀ i, F.period j i = m) :
    Function.Injective (torusSiteInFrame (n := m) F j) := by
  intro x y h
  funext k
  have h1 := congrFun h k
  have h2 := intCast_cast_intCast_cast (hper k).symm (x k)
  have h3 := intCast_cast_intCast_cast (hper k).symm (y k)
  unfold torusSiteInFrame siteOfCoords at h1
  simp only at h1
  rw [← h2, ← h3, h1]
variable [NeZero L] [NeZero n]
theorem torusSiteInFrame_add (x y : TorusSite (n * L)) :
    torusSiteInFrame (stepBlockFrame L n) 0 (x + y) =
      torusSiteInFrame (stepBlockFrame L n) 0 x + torusSiteInFrame (stepBlockFrame L n) 0 y := by
  funext i
  exact intCast_cast_add (stepBlockFrame_period_zero i) (x i) (y i)
theorem torusSiteInFrame_unitStep (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 0 (TorusFields.unitStep (n * L) i) = BlockAverages.unitStep (F := stepBlockFrame L n) 0 i := by
  funext k
  have e : (TorusFields.unitStep (n * L) i) k = (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod (n * L)) := by
    by_cases hk : k = i
    · subst hk
      simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, Pi.single_eq_of_ne hk]
  show ((ZMod.cast (TorusFields.unitStep (n * L) i k) : ℤ) : ZMod ((stepBlockFrame L n).period 0 k)) = _
  rw [e]
  exact intCast_cast_intCast (stepBlockFrame_period_zero k) _
theorem enclosingCell_torusSiteInFrame (x : TorusSite (n * L)) :
    enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x) = torusSiteInFrame (stepBlockFrame L n) 1 (parentBlock L x) := by
  funext i
  have hc : siteCoords (torusSiteInFrame (stepBlockFrame L n) 0 x : (stepBlockFrame L n).Site 0) i = (x i).cast :=
    cast_intCast_cast (stepBlockFrame_period_zero i) (x i)
  have hone : (stepBlockFrame L n).top - 0 = 1 := by simp [stepBlockFrame, BlockFrame.top]
  show (((siteCoords (torusSiteInFrame (stepBlockFrame L n) 0 x : (stepBlockFrame L n).Site 0) i +
      ((L : ℤ) ^ ((stepBlockFrame L n).top - 0) - 1) / 2) / (L : ℤ) ^ ((stepBlockFrame L n).top - 0) : ℤ) :
        ZMod ((stepBlockFrame L n).period 1 i)) =
    ((ZMod.cast (parentBlock L x i) : ℤ) : ZMod ((stepBlockFrame L n).period 1 i))
  rw [hc, hone, pow_one]
  exact (intCast_cast_intCast (stepBlockFrame_period_one i) _).symm
theorem readAtLevel_enclosingCell (V : TorusField n) (x : TorusSite (n * L)) (i : Fin 4) :
    readAtLevel (stepBlockFrame L n) 1 V (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x)) i = V (parentBlock L x) i := by
  rw [enclosingCell_torusSiteInFrame]
  exact readAtLevel_torusSiteInFrame _ 1 stepBlockFrame_period_one V _ i
def blockGauge (L : ℕ) {n : ℕ} (W : TorusField (n * L)) (x : TorusSite (n * L)) : UnitQuaternion :=
  axialGauge 1 (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 x)
theorem blockGauge_add_unitStep (hL : Odd L) (hn : 2 ≤ n) (W : TorusField (n * L)) (x : TorusSite (n * L)) (i : Fin 4)
    (ht : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)) :
    blockGauge L W (x + TorusFields.unitStep (n * L) i) = blockGauge L W x * W x i := by
  have h := axialGauge_add_unitStep (F := stepBlockFrame L n) hL (fun _ => hn) (readAtLevel (stepBlockFrame L n) 0 W)
    (torusSiteInFrame (stepBlockFrame L n) 0 x) i ht
  unfold blockGauge
  rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
  rw [readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W x i] at h
  exact h
theorem blockGauge_congr (hL : Odd L) (hn : 2 ≤ n) (W W' : TorusField (n * L)) (x : TorusSite (n * L))
    (h : ∀ z i, parentBlock L z = parentBlock L x →
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 z, i) → W z i = W' z i) :
    blockGauge L W x = blockGauge L W' x := by
  unfold blockGauge
  apply axialGauge_congr (F := stepBlockFrame L n) hL (fun _ => hn)
  intro z i hc ht
  obtain ⟨y, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame L n) 0 stepBlockFrame_period_zero z
  rw [readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W y i,
    readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W' y i]
  apply h y i _ ht
  exact torusSiteInFrame_injective (stepBlockFrame L n) 1 stepBlockFrame_period_one
    ((enclosingCell_torusSiteInFrame y).symm.trans (hc.trans (enclosingCell_torusSiteInFrame x)))
theorem pathHolonomy_of_forall_eq_one {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (hX : ∀ x i, X x i = 1) (l : List PathStep) :
    ∀ x, pathHolonomy X x l = 1 := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, ih, mul_one, linkValue]
    split_ifs <;> simp [hX]
omit [NeZero L] [NeZero n] in
theorem blockGauge_of_forall_eq_one (W : TorusField (n * L)) (hW : ∀ x i, W x i = 1) (x : TorusSite (n * L)) : blockGauge L W x = 1 := by
  unfold blockGauge axialGauge
  exact pathHolonomy_of_forall_eq_one _ (fun z i => hW _ i) _ _
omit [NeZero L] [NeZero n] in
theorem blockGauge_of_cellOffset_eq_zero (W : TorusField (n * L)) (x : TorusSite (n * L))
    (h : cellOffset (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x) = 0) : blockGauge L W x = 1 := by
  unfold blockGauge axialGauge
  rw [h]
  have e0 : axisPath (0 : Fin 4 → ℤ) 1 = [] := by
    simp [axisPath, List.finRange_succ, List.flatMap_cons]
  rw [e0]
  rfl
theorem measurable_link {α : Type} (x : α) (i : Fin 4) :
    Measurable fun X : α → Fin 4 → UnitQuaternion => X x i :=
  (measurable_pi_apply i).comp (measurable_pi_apply x)
theorem measurable_pathHolonomy {F : BlockFrame} {j : ℕ} (l : List PathStep) :
    ∀ x : F.Site j, Measurable fun X : F.GaugeField j => pathHolonomy X x l := by
  induction l with
  | nil => intro x; exact measurable_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    refine Measurable.mul ?_ (ih _)
    unfold linkValue
    by_cases hs : st.2 = true
    · simp only [hs, if_true]
      exact measurable_link _ _
    · simp only [hs, Bool.false_eq_true, if_false]
      exact (measurable_link _ _).inv
omit [NeZero L] [NeZero n] in
theorem measurable_blockGauge (x : TorusSite (n * L)) : Measurable fun W : TorusField (n * L) => blockGauge L W x := by
  unfold blockGauge axialGauge
  have h := measurable_pathHolonomy (F := stepBlockFrame L n) (j := 0)
    (axisPath (cellOffset (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x)) 1)
    (cellCentre (stepBlockFrame L n).depth (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x)))
  refine h.comp ?_
  refine measurable_pi_lambda _ fun z => measurable_pi_lambda _ fun i => ?_
  exact measurable_link _ _
theorem chartCoord_eq_minimalLog (ℓ : StepParameters) (V : TorusField n) (W' : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side)) (u : UnitQuaternion)
    (hW : open Classical in W' b.1 b.2 = (blockGauge ℓ.side W' b.1)⁻¹ *
      (if IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
        then u * V (parentBlock ℓ.side b.1) b.2 else u) * blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2)) :
    chartCoord ℓ V W' b = minimalLog u := by
  classical
  have hg : gaugeTransform (axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W')) (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1) b.2 =
      (if IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
        then u * V (parentBlock ℓ.side b.1) b.2 else u) := by
    unfold BlockAverages.gaugeTransform
    have e2 : axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1 + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) 0 b.2) =
        blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) := by
      unfold blockGauge
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e1 : axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W') (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1) =
        blockGauge ℓ.side W' b.1 := rfl
    rw [readAtLevel_torusSiteInFrame (stepBlockFrame ℓ.side n) 0 stepBlockFrame_period_zero W' b.1 b.2, hW]
    erw [e1, e2]
    group
  unfold chartCoord bondCoordinate
  by_cases hc : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
  · rw [if_pos hc]
    simp only
    rw [if_pos hc] at hg
    erw [hg, readAtLevel_enclosingCell]
    simp
  · rw [if_neg hc]
    simp only
    rw [if_neg hc] at hg
    erw [hg]
open Classical in
theorem chartCoord_eq (ℓ : StepParameters) (V : TorusField n) (W' : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side)) :
    chartCoord ℓ V W' b = minimalLog
      (if IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
        then blockGauge ℓ.side W' b.1 * W' b.1 b.2 * (blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2))⁻¹ * (V (parentBlock ℓ.side b.1) b.2)⁻¹
        else blockGauge ℓ.side W' b.1 * W' b.1 b.2 * (blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2))⁻¹) := by
  have hg : gaugeTransform (axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W')) (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1) b.2 =
      blockGauge ℓ.side W' b.1 * W' b.1 b.2 * (blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2))⁻¹ := by
    unfold BlockAverages.gaugeTransform
    have e2 : axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1 + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) 0 b.2) =
        blockGauge ℓ.side W' (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) := by
      unfold blockGauge
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e1 : axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) 0 W') (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1) =
        blockGauge ℓ.side W' b.1 := rfl
    rw [readAtLevel_torusSiteInFrame (stepBlockFrame ℓ.side n) 0 stepBlockFrame_period_zero W' b.1 b.2]
    erw [e1, e2]
  unfold chartCoord bondCoordinate
  by_cases hc : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
  · rw [if_pos hc, if_pos hc]
    simp only
    erw [hg, readAtLevel_enclosingCell]
  · rw [if_neg hc, if_neg hc]
    simp only
    erw [hg]
end Transfer
end BlockTrees
end YangMills.Construction
end
