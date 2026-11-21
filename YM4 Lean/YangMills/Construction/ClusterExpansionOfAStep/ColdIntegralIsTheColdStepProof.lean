import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.CountOfTheChartBondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfALevelIsTheShareBelow
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.LogAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
namespace ColdImage
namespace EvaluationMaps
theorem cast_intCast_of_eq (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    toTorusSite m (torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    torusSiteInFrame H j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x + y) = torusSiteInFrame H j x + torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    torusSiteInFrame H j (-x) = - torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x - y) = torusSiteInFrame H j x - torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusField m) : TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W
        (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (l : List PathStep) :
    pathHolonomy (readAtLevel H j W) (torusSiteInFrame H j x) l = torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + torusSiteInFrame H j x = torusSiteInFrame H j
        (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [torusSiteInFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, torusSiteInFrame_neg j hm, torusSiteInFrame_unitStep j hm, add_comm]
      · simp [stepDisplacement, torusSiteInFrame_unitStep j hm, add_comm]
    simp only [pathHolonomy, torusPathHolonomy]
    rw [add_comm (torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm,
        readAtLevel_torusSiteInFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) :
    H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem cast_intCast_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m)
    (k : Fin 4) : siteCoords (torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  cast_intCast_cast_of_eq _ _ (hm k) (x k)
def blockCentre (L : ℕ) (Y : TorusSite n) : TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    enclosingCell (torusSiteInFrame H H.depth x) =
      torusSiteInFrame H H.top (parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.depth (period_depth hs) x k
  show ((((siteCoords (torusSiteInFrame H H.depth x) k +
    ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
    (H.blockSide : ℤ) ^ (H.top - H.depth) : ℤ)) : ZMod (H.period H.top k)) = _
  rw [h1, he, pow_one]
  exact (cast_intCast_of_eq _ _ (period_top hs k) _).symm
theorem torusSiteInFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_torusSiteInFrame j hm x, h, toTorusSite_torusSiteInFrame j hm y]
theorem isCrossingBond_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsCrossingBond (F := H) (torusSiteInFrame H H.depth x, i) ↔
      parentBlock H.blockSide (x + TorusFields.unitStep _ i) ≠ parentBlock H.blockSide x := by
  unfold IsCrossingBond
  show enclosingCell (torusSiteInFrame H H.depth x + BlockAverages.unitStep H.depth i) ≠
    enclosingCell (torusSiteInFrame H H.depth x) ↔ _
  rw [← torusSiteInFrame_unitStep H.depth (period_depth hs),
    ← torusSiteInFrame_add H.depth (period_depth hs), enclosingCell_torusSiteInFrame hs,
    enclosingCell_torusSiteInFrame hs]
  exact not_congr (torusSiteInFrame_injective H.top (period_top hs)).eq_iff
theorem cellCentre_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusSite n) :
    cellCentre H.depth (torusSiteInFrame H H.top Y) =
      torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.top (period_top hs) Y k
  show (((H.blockSide : ℤ) ^ (H.top - H.depth) * siteCoords (torusSiteInFrame H H.top Y) k : ℤ) :
    ZMod (H.period H.depth k)) = _
  rw [h1, he, pow_one]
  exact (cast_intCast_of_eq _ _ (period_depth hs k) _).symm
theorem refineSite_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusSite n) :
    refineSite (j := H.depth) (torusSiteInFrame H H.top Y) =
      torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by
  funext k
  have h1 := siteCoords_torusSiteInFrame (H := H) H.top (period_top hs) Y k
  show (((H.blockSide : ℤ) * siteCoords (torusSiteInFrame H H.top Y) k : ℤ) :
    ZMod (H.period H.depth k)) = _
  rw [h1]
  exact (cast_intCast_of_eq _ _ (period_depth hs k) _).symm
theorem valMinAbs_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P))).valMinAbs = a.valMinAbs := by
  subst h; simp
def blockOffset (L : ℕ) (x : TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - blockCentre L (parentBlock L x)) k).valMinAbs
theorem cellOffset_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    cellOffset (torusSiteInFrame H H.depth x) = blockOffset H.blockSide x := by
  funext k
  unfold cellOffset blockOffset
  rw [enclosingCell_torusSiteInFrame hs, cellCentre_torusSiteInFrame hs,
    ← torusSiteInFrame_sub H.depth (period_depth hs)]
  exact valMinAbs_cast_of_eq _ _ (period_depth hs k) _
def IsBlockTreeBond (L : ℕ) (x : TorusSite (n * L)) (i : Fin 4) : Prop :=
  parentBlock L (x + TorusFields.unitStep _ i) = parentBlock L x ∧ ∀ l, i < l → blockOffset L x l = 0
theorem isAxialTreeBond_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (torusSiteInFrame H H.depth x, i) ↔ IsBlockTreeBond H.blockSide x i := by
  unfold IsAxialTreeBond IsBlockTreeBond
  rw [isCrossingBond_iff hs, cellOffset_torusSiteInFrame hs]
  simp
def blockContourAverage (L : ℕ) (W : TorusField (n * L)) (Y : TorusSite n) (i : Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    ((torusPathHolonomy W (blockCentre L Y) (bondContour L h π i) : UnitQuaternion) : ℍ[ℝ])
theorem contourAverage_readAtLevel (hs : ∀ i, H.extent i = n) (W : TorusField (n * H.blockSide))
    (Y : TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) (readAtLevel H H.depth W) (torusSiteInFrame H H.top Y, i) =
      blockContourAverage H.blockSide W Y i := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage blockContourAverage
  simp only [refineSite_torusSiteInFrame hs, pathHolonomy_readAtLevel H.depth (period_depth hs)]
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem contourMean_of_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide)
    (J₀ : ℕ) (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    contourMean J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) W c := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.contourMean_empty <;> assumption
theorem contourFit_of_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide)
    (J₀ : ℕ) (W : H.GaugeField H.depth) (V : H.GaugeField H.top) (c : H.Cell × Fin 4) :
    contourFit J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W V c =
      blockFit (j := H.depth) W V c := by
  unfold contourFit blockFit
  rw [contourMean_of_no_lumps hs hn hL]
end Plain
section Field
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev stepTorusFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
abbrev twoLevelFrame (R : StepSetup) (n : ℕ) : BlockFrame := stepBlockFrame R.params.side n
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
theorem mem_chartBonds_iff (b : TorusBond (n * R.params.side)) :
    b ∈ chartBonds R.params.side n ↔ ¬ IsBlockTreeBond R.params.side b.1 b.2 := by
  unfold chartBonds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (isAxialTreeBond_iff (H := twoLevelFrame R n) (fun _ => rfl) b.1 b.2)
theorem mem_finiteCells (z : (stepTorusFrame R n).Cell) : z ∈ finiteCells (stepTorusFrame R n) := by
  have h : ∀ i, NeZero ((stepTorusFrame R n).period (stepTorusFrame R n).top i) := fun i =>
    ⟨by rw [period_top (n := n) (fun _ => rfl) i]; exact NeZero.ne n⟩
  have hf : Finite (stepTorusFrame R n).Cell := by
    show Finite ((i : Fin 4) → ZMod ((stepTorusFrame R n).period (stepTorusFrame R n).top i))
    infer_instance
  unfold finiteCells
  rw [dif_pos hf]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem mem_innerBonds_depth (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : (stepTorusFrame R n).Site (stepTorusFrame R n).depth × Fin 4) :
    b ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth := by
  have hc : ∀ x : (stepTorusFrame R n).Site (stepTorusFrame R n).depth,
      x ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth :=
    hcov (stepTorusFrame R n) hodd (fun _ => Nat.pos_of_ne_zero (NeZero.ne n))
  unfold innerBonds
  simp [hc]
theorem chordBonds_mem_iff (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : TorusBond (n * R.params.side)) :
    (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth b.1, b.2) ∈
        chordBonds (finiteCells (stepTorusFrame R n)) ↔
      b ∈ chartBonds R.params.side n := by
  rw [mem_chartBonds_iff]
  simp only [chordBonds, Finset.mem_filter]
  constructor
  · intro h
    exact fun h2 => h.2 ((isAxialTreeBond_iff (H := stepTorusFrame R n) (fun _ => rfl) b.1 b.2).2 h2)
  · intro h
    exact ⟨mem_innerBonds_depth hcov hodd _,
      fun h2 => h ((isAxialTreeBond_iff (H := stepTorusFrame R n) (fun _ => rfl) b.1 b.2).1 h2)⟩
def chartBondsEquivChord (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) :
    ↥(chartBonds R.params.side n) ≃ ↥(chordBonds (finiteCells (stepTorusFrame R n))) where
  toFun b := ⟨(torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth b.1.1, b.1.2),
    (chordBonds_mem_iff hcov hodd b.1).2 b.2⟩
  invFun k := ⟨(toTorusSite (n * R.params.side) k.1.1, k.1.2), by
    rw [← chordBonds_mem_iff hcov hodd]
    have h : torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth
        (toTorusSite (n * R.params.side) k.1.1) = k.1.1 :=
      torusSiteInFrame_toTorusSite _ (period_depth (n := n) fun _ => rfl) _
    rw [h]
    exact k.2⟩
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · exact toTorusSite_torusSiteInFrame _ (period_depth (n := n) fun _ => rfl) _
    · rfl
  right_inv k := by
    apply Subtype.ext
    apply Prod.ext
    · exact torusSiteInFrame_toTorusSite _ (period_depth (n := n) fun _ => rfl) _
    · rfl
def freeBondsEquivChord (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n) :
    ↥(coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (stepTorusFrame R n))) :=
  chartBondsEquivChord hcov hodd
def toStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) : StepVariable (finiteCells (stepTorusFrame R n)) :=
  fun k => η ((freeBondsEquivChord hcov hodd V).symm k)
theorem toStepVariable_apply (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free)
    (b : ↥(coldChartSetting R V).free) :
    toStepVariable hcov hodd V η (freeBondsEquivChord hcov hodd V b) = η b := by
  simp [toStepVariable]
theorem stepCoordinates_toStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (h : (x, i) ∈ (coldChartSetting R V).free) :
    stepCoordinates (toStepVariable hcov hodd V η)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x) i =
      toImaginary (η ⟨(x, i), h⟩) := by
  unfold stepCoordinates
  rw [dif_pos ((chordBonds_mem_iff hcov hodd (x, i)).2 h)]
  exact congrArg toImaginary (toStepVariable_apply hcov hodd V η ⟨(x, i), h⟩)
abbrev topField (V : TorusField n) : (stepTorusFrame R n).GaugeField (stepTorusFrame R n).top :=
  readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).top V
theorem readAtLevel_field (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) :
    readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth ((coldChartSetting R V).field η) =
      fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable hcov hodd V η) := by
  have hlow : ∀ i, (stepTorusFrame R n).period (stepTorusFrame R n).depth i = n * R.params.side :=
    period_depth (H := stepTorusFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * R.params.side),
      torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := stepTorusFrame R n) _ hlow
    ((coldChartSetting R V).field η) x i).trans ?_
  unfold fieldAboveFrame chartedField
  by_cases hb : (x, i) ∈ (coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := stepTorusFrame R n)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x, i) := fun h2 =>
      ((mem_chartBonds_iff (R := R) (x, i)).1 hb)
        ((isAxialTreeBond_iff (H := stepTorusFrame R n) (fun _ => rfl) x i).1 h2)
    have hfr : (coldChartSetting R V).frame (x, i) =
        ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x, i) (topField V) := rfl
    have hw : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable hcov hodd V η)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x) i =
        (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := by
      unfold coordsAboveFrame
      rw [stepCoordinates_toStepVariable hcov hodd V η x i hb, hfr]
    have hcr : IsCrossingBond (F := twoLevelFrame R n) (torusSiteInFrame (twoLevelFrame R n) 0 x, i) ↔
        IsCrossingBond (F := stepTorusFrame R n)
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x, i) :=
      (isCrossingBond_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).trans
        (isCrossingBond_iff (H := stepTorusFrame R n) (fun _ => rfl) x i).symm
    have hcell : topField (R := R) V
        (enclosingCell (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x)) i =
        V (parentBlock R.params.side x) i := by
      have h0 : enclosingCell (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x) =
          torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top (parentBlock R.params.side x) :=
        enclosingCell_torusSiteInFrame (H := stepTorusFrame R n) (n := n) (fun _ => rfl) x
      rw [h0]
      exact readAtLevel_torusSiteInFrame _
        (period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl) V _ i
    have hfield : (coldChartSetting R V).field η x i =
        chartLink (coldChartSetting R V) x i
          ((coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw]
    unfold chartLink
    have h1 : gaugeAt (R := R) (coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := stepTorusFrame R n)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x, i)
    · rw [if_pos (hcr.2 hc), if_pos hc, hcell]
      rfl
    · rw [if_neg (fun h => hc (hcr.1 h)), if_neg hc, if_neg htree]
  · have hfield : (coldChartSetting R V).field η x i = (coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsBlockTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_chartBonds_iff (R := R) (x, i)).2 h)
    have htree := (isAxialTreeBond_iff (H := stepTorusFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := stepTorusFrame R n)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Field
section Cost
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem plaquetteDefect_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p = curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
omit [NeZero n] in
theorem stepHotLumps_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
omit [NeZero n] in
theorem torusHotSites_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem thickening_empty (m : ℕ) : thickening m (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
def blockFitOnTorus (L : ℕ) (W : TorusField (n * L)) (V : TorusField n) (Y : TorusSite n)
    (i : Fin 4) : ℝ :=
  ‖blockContourAverage L W Y i‖ - (blockContourAverage L W Y i * ((V Y i)⁻¹ : UnitQuaternion)).re
omit [NeZero n] in
theorem blockFit_readAtLevel {H : BlockFrame} (hs : ∀ i, H.extent i = n)
    (W : TorusField (n * H.blockSide)) (V : TorusField n) (Y : TorusSite n) (i : Fin 4) :
    blockFit (j := H.depth) (readAtLevel H H.depth W) (readAtLevel H H.top V)
        (torusSiteInFrame H H.top Y, i) = blockFitOnTorus H.blockSide W V Y i := by
  unfold blockFit blockFitOnTorus
  rw [contourAverage_readAtLevel hs]
  have h := readAtLevel_torusSiteInFrame (H := H) H.top (period_top hs) V Y i
  simp only [h]
theorem bondFit_of_isCold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side)
    (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) (V : TorusField n) (c : TorusBond n) :
    bondFit ℓ W V (fun y => cellCentre 0 y) c = blockFitOnTorus ℓ.side W V c.1 c.2 := by
  unfold bondFit
  rw [stepHotLumps_eq_empty ℓ W hW]
  have h := contourFit_of_no_lumps (H := stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  refine h.trans ?_
  exact blockFit_readAtLevel (H := stepBlockFrame ℓ.side n) (fun _ => rfl) W V c.1 c.2
theorem meanNorm_of_isCold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side)
    (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) (c : TorusBond n) :
    meanNorm ℓ W (fun y => cellCentre 0 y) c = ‖blockContourAverage ℓ.side W c.1 c.2‖ := by
  unfold meanNorm
  rw [stepHotLumps_eq_empty ℓ W hW]
  have h := contourMean_of_no_lumps (H := stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  exact (congrArg norm h).trans
    (congrArg _ (contourAverage_readAtLevel (H := stepBlockFrame ℓ.side n) (fun _ => rfl) W c.1 c.2))
end Cost
section Sums
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem mem_sitesOfCells_top (z : (stepTorusFrame R n).Cell) :
    z ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top := by
  unfold sitesOfCells
  refine Finset.mem_biUnion.2 ⟨z, _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells z, Finset.mem_image.2 ⟨0, ?_, ?_⟩⟩
  · simp [centredCube]
    rfl
  · funext k
    show (((R.params.side : ℤ) ^ ((stepTorusFrame R n).top - (stepTorusFrame R n).top) *
      siteCoords z k : ℤ) : ZMod ((stepTorusFrame R n).period (stepTorusFrame R n).top k)) +
      (((0 : Fin 4 → ℤ) k : ℤ) : ZMod ((stepTorusFrame R n).period (stepTorusFrame R n).top k)) = z k
    simp [siteCoords]
theorem mem_innerBonds_top (c : (stepTorusFrame R n).Site (stepTorusFrame R n).top × Fin 4) :
    c ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top := by
  unfold innerBonds
  simp [mem_sitesOfCells_top]
omit [NeZero n] in
theorem unitStep_ne_zero (hn : 2 ≤ n) (i : Fin 4) : TorusFields.unitStep n i ≠ 0 := by
  intro h
  have h1 := congrFun h i
  have : Fact (1 < n) := ⟨hn⟩
  simp [TorusFields.unitStep] at h1
omit [NeZero n] in
theorem unitStep_top_ne_zero (hn : 2 ≤ n) (i : Fin 4) :
    BlockAverages.unitStep (F := stepTorusFrame R n) (stepTorusFrame R n).top i ≠ 0 := by
  intro h
  have hm := period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl
  apply unitStep_ne_zero hn i
  apply torusSiteInFrame_injective (H := stepTorusFrame R n) _ hm
  rw [torusSiteInFrame_unitStep _ hm, h]
  have h2 := torusSiteInFrame_add (H := stepTorusFrame R n) _ hm (0 : TorusSite n) 0
  have h3 : torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top (0 : TorusSite n) = 0 := by
    simpa using h2.symm
  exact h3.symm
open Classical in
theorem sum_bonds_touching (hn : 2 ≤ n)
    (g : (stepTorusFrame R n).Site (stepTorusFrame R n).top × Fin 4 → ℝ)
    (Y : (stepTorusFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (stepTorusFrame R n).top c.2 = Y), g c =
      ∑ i : Fin 4, (g (Y, i) + g (Y - BlockAverages.unitStep (stepTorusFrame R n).top i, i)) := by
  have hS : (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (stepTorusFrame R n).top c.2 = Y) =
      (Finset.univ : Finset (Fin 4)).biUnion
        (fun i => ({(Y, i), (Y - BlockAverages.unitStep (stepTorusFrame R n).top i, i)} : Finset _)) := by
    ext ⟨z, i⟩
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, h | h⟩
      · exact ⟨i, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨i, Or.inr ⟨by rw [← h]; simp, rfl⟩⟩
    · rintro ⟨k, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩
      · exact ⟨mem_innerBonds_top _, Or.inl h1⟩
      · exact ⟨mem_innerBonds_top _, Or.inr (by rw [h1]; simp)⟩
  rw [hS, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    apply Finset.sum_pair
    intro h
    apply unitStep_top_ne_zero (R := R) hn i
    have h1 : Y = Y - BlockAverages.unitStep (stepTorusFrame R n).top i := congrArg Prod.fst h
    exact sub_eq_self.1 h1.symm
  · intro i _ k _ hik
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    apply hik
    have e1 : c.2 = i := by rcases h1 with rfl | rfl <;> rfl
    have e2 : c.2 = k := by rcases h2 with rfl | rfl <;> rfl
    exact e1.symm.trans e2
open Classical in
theorem sum_bonds_starting (g : (stepTorusFrame R n).Site (stepTorusFrame R n).top × Fin 4 → ℝ)
    (Y : (stepTorusFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
        (fun c => c.1 = Y), g c =
      ∑ i : Fin 4, g (Y, i) := by
  symm
  apply Finset.sum_nbij (fun i => (Y, i))
  · intro i _
    exact Finset.mem_filter.2 ⟨mem_innerBonds_top _, rfl⟩
  · intro i _ k _ h
    exact congrArg Prod.snd h
  · rintro ⟨z, i⟩ h
    have h1 := (Finset.mem_filter.1 h).2
    exact ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), by simp at h1; simp [h1]⟩
  · intro i _
    rfl
open Classical in
theorem sum_sites_in_cell (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (stepTorusFrame R n).Site (stepTorusFrame R n).depth → ℝ) (Y : TorusSite n) :
    ∑ y ∈ (sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth).filter
        (fun y => enclosingCell y = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y),
        g y =
      ∑ x ∈ sitesInBlocks R.params.side {Y},
        g (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x) := by
  have hlow : ∀ i, (stepTorusFrame R n).period (stepTorusFrame R n).depth i = n * R.params.side :=
    period_depth (H := stepTorusFrame R n) (n := n) fun _ => rfl
  have hc : ∀ x : (stepTorusFrame R n).Site (stepTorusFrame R n).depth,
      x ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth :=
    hcov (stepTorusFrame R n) hodd (fun _ => Nat.pos_of_ne_zero (NeZero.ne n))
  have hcell : ∀ x : TorusSite (n * R.params.side),
      enclosingCell (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x) =
      torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top (parentBlock R.params.side x) :=
    enclosingCell_torusSiteInFrame (H := stepTorusFrame R n) (n := n) (fun _ => rfl)
  symm
  apply Finset.sum_nbij (fun x => torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x)
  · intro x hx
    have h1 : parentBlock R.params.side x = Y := by simpa [sitesInBlocks] using hx
    refine Finset.mem_filter.2 ⟨hc _, ?_⟩
    rw [hcell, h1]
  · intro x _ x' _ h
    exact torusSiteInFrame_injective _ hlow h
  · intro y hy
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    refine ⟨toTorusSite (n * R.params.side) y, ?_, torusSiteInFrame_toTorusSite _ hlow y⟩
    have h2 : torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth
        (toTorusSite (n * R.params.side) y) = y :=
      torusSiteInFrame_toTorusSite _ hlow y
    have h3 := hcell (toTorusSite (n * R.params.side) y)
    rw [h2, h1] at h3
    have h4 := torusSiteInFrame_injective _
      (period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl) h3
    simp [sitesInBlocks, ← h4]
  · intro x _
    rfl
theorem sum_finiteCells (g : (stepTorusFrame R n).Cell → ℝ) :
    ∑ Z ∈ finiteCells (stepTorusFrame R n), g Z =
      ∑ Y : TorusSite n, g (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) := by
  have htop : ∀ i, (stepTorusFrame R n).period (stepTorusFrame R n).top i = n :=
    period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl
  symm
  apply Finset.sum_nbij (fun Y => torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
  · intro Y _
    exact _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells _
  · intro x _ x' _ h
    exact torusSiteInFrame_injective _ htop h
  · intro y _
    exact ⟨toTorusSite n y, Finset.mem_coe.2 (Finset.mem_univ _), torusSiteInFrame_toTorusSite _ htop y⟩
  · intro x _
    rfl
end Sums
section Read
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem torusSiteInFrame_sub_unitStep (Y : TorusSite n) (i : Fin 4) :
    torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y -
        BlockAverages.unitStep (stepTorusFrame R n).top i =
      torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top (Y - TorusFields.unitStep n i) := by
  have hm := period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl
  rw [torusSiteInFrame_sub _ hm, torusSiteInFrame_unitStep _ hm]
theorem blockCost_eq_cellEnergyShare (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (hn : 2 ≤ n) (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (hsh : ∀ y, levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      minimalSiteShare (F := stepTorusFrame R n) R.params.coupling
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth y)
        (readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth W))
    (V : TorusField n) (w : (stepTorusFrame R n).Site (stepTorusFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (hX : chartedField w (topField (R := R) V) = readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth W)
    (Y : TorusSite n) :
    blockCost R.params R.depth W V (fun y => cellCentre 0 y) Y =
      cellEnergyShare R.params.coupling
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) w (topField V) := by
  unfold blockCost cellEnergyShare
  rw [torusHotSites_eq_empty R.params W hW, thickening_empty, Finset.sdiff_empty, hX]
  congr 1
  · rw [sum_sites_in_cell hcov hodd]
    exact Finset.sum_congr rfl fun y _ => hsh y
  · congr 1
    rw [sum_bonds_touching hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := blockFit_readAtLevel (H := stepTorusFrame R n) (n := n) (fun _ => rfl) W V Y i
    have e2 := blockFit_readAtLevel (H := stepTorusFrame R n) (n := n) (fun _ => rfl) W V
      (Y - TorusFields.unitStep n i) i
    rw [torusSiteInFrame_sub_unitStep, bondFit_of_isCold R.params hodd W hW,
      bondFit_of_isCold R.params hodd W hW]
    exact congrArg₂ (· + ·) e1.symm e2.symm
end Read
section Pointwise
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem localDensity_cast (g : LocalDensity) (P m : ℕ) (hP : P = m) {H : BlockFrame} {j : ℕ}
    (y : H.Site j) (X : H.GaugeField j) :
    g P (toTorusSite P y) (restrictToTorus P X) = g m (toTorusSite m y) (restrictToTorus m X) := by
  subst hP; rfl
theorem restrictToTorus_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) : restrictToTorus m (readAtLevel H j W) = W := by
  funext x i
  exact readAtLevel_torusSiteInFrame j hm W x i
omit [NeZero n] in
theorem localFamilyOfDensity_readAtLevel (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    localFamilyOfDensity g (stepTorusFrame R n)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x)
        (readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth W) =
      g (n * R.params.side) x W := by
  have hlow : ∀ i, (stepTorusFrame R n).period (stepTorusFrame R n).depth i = n * R.params.side :=
    period_depth (H := stepTorusFrame R n) (n := n) fun _ => rfl
  unfold localFamilyOfDensity
  rw [localDensity_cast g _ (n * R.params.side) (hlow 0), toTorusSite_torusSiteInFrame _ hlow,
    restrictToTorus_readAtLevel hlow]
omit [NeZero n] in
theorem subtractTrivial_readAtLevel (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    ColdStepAtMirrorFrames.subtractTrivial (localFamilyOfDensity g) (stepTorusFrame R n)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth x)
        (readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth W) =
      centered g (n * R.params.side) x W := by
  unfold ColdStepAtMirrorFrames.subtractTrivial centered
  have h := localFamilyOfDensity_readAtLevel (R := R) (n := n) g x (trivialField _)
  rw [localFamilyOfDensity_readAtLevel, ← h]
  rfl
theorem isHullState_empty (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (r : ℕ) : IsHullState R.params r W ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.isHullState_empty <;> assumption
theorem blockDensityAt_eq_cellCentredExpansion (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (hrow : R.HasExpansions) (hn₀ : R.params.n₀ ≤ n) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free)
    (hW : IsCold R.params.threshold ((coldChartSetting R V).field η)) (Y : TorusSite n) :
    (coldChartSetting R V).blockDensityAt Y η =
      cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
        (toStepVariable hcov hodd V η) (topField V) := by
  unfold cellCentredExpansion
  rw [sum_sites_in_cell hcov hodd]
  unfold ChartSetting.blockDensityAt ChartSetting.blockDensity
  refine Finset.sum_congr rfl fun x _ => ?_
  have hb : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Nat.dvd_mul_left _ _, by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hn₀⟩
  have h1 := hrow.2.empty (n * R.params.side) hb ((coldChartSetting R V).field η)
    (coldChartSetting R V).labelling x (isHullState_empty _ hW _)
  refine h1.trans ?_
  unfold centredExpansion
  rw [← readAtLevel_field hcov hodd V η]
  exact (subtractTrivial_readAtLevel R.density x _).symm
end Pointwise
section Context
open Filter Topology
structure ColdTopData (R : StepSetup) (n : ℕ) [NeZero n] (lam : ℝ) (V : TorusField n) : Prop where
  cover : BlocksCoverLowerLevel
  side_odd : Odd R.params.side
  two_le : 2 ≤ n
  coupling_nonneg : 0 ≤ R.params.coupling
  n₀_le : R.params.n₀ ≤ n
  ballRadius_pos : 0 < R.ballRadius
  expansions : R.HasExpansions
  weyl : WeylIntegrationFormula
  shares_sum : sumCellSharesEqAction
  fixed : stepIntegralInFixedVariables
  isCold : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) →
    IsCold R.params.threshold ((coldChartSetting R V).field η)
  share_eq : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ y,
    levelShare R.params.coupling R.params.side R.depth Finset.univ y ((coldChartSetting R V).field η) =
      minimalSiteShare (F := stepTorusFrame R n) R.params.coupling
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth y)
        (readAtLevel (stepTorusFrame R n) (stepTorusFrame R n).depth ((coldChartSetting R V).field η))
  frame_norm_lt : ∀ b ∈ chordBonds (finiteCells (stepTorusFrame R n)),
    ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach b
      (topField (R := R) V)‖ + R.ballRadius < Real.pi
  freeBond_card : ∀ Y, ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side
  regular : ∃ M, IsRegularStep R.params.coupling R.anchorRadius R.ballRadius lam R.coupling M
    R.frameReach R.barrierFn (localFamilyOfDensity R.density) (topField (R := R) V)
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
theorem toImaginary_zero : toImaginary 0 = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem toImaginary_toCoords (w : imaginaryQuaternions) : toImaginary (toCoords w) = w := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem coordNorm_eq (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := norm_toImaginary v
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_zero_pos <;> assumption
theorem haarRadialDensity_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < Real.pi) : 0 < haarRadialDensity u := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_pos <;> assumption
abbrev frameCoords (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (stepTorusFrame R n).Site (stepTorusFrame R n).depth → Fin 4 → imaginaryQuaternions :=
  coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
    (toStepVariable c.cover c.side_odd V η)
theorem frameCoords_freeBond (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (b : ↥(coldChartSetting R V).free) :
    frameCoords c η (freeBondsEquivChord c.cover c.side_odd V b).1.1
        (freeBondsEquivChord c.cover c.side_odd V b).1.2 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by
  unfold frameCoords coordsAboveFrame
  have h := stepCoordinates_toStepVariable c.cover c.side_odd V η b.1.1 b.1.2 b.2
  have e : (freeBondsEquivChord c.cover c.side_odd V b).1 =
      (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth b.1.1, b.1.2) := rfl
  simp only [e]
  rw [h]
  rfl
theorem enclosingCell_freeBond_iff (c : ColdTopData R n lam V) (b : ↥(coldChartSetting R V).free)
    (Y : TorusSite n) :
    enclosingCell (freeBondsEquivChord c.cover c.side_odd V b).1.1 =
        torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y ↔
      bondBlock (R := R) b.1 = Y := by
  have h0 : enclosingCell (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth b.1.1) =
      torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top (parentBlock R.params.side b.1.1) :=
    enclosingCell_torusSiteInFrame (H := stepTorusFrame R n) (n := n) (fun _ => rfl) b.1.1
  show enclosingCell (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).depth b.1.1) = _ ↔
    parentBlock R.params.side b.1.1 = Y
  rw [h0]
  exact (torusSiteInFrame_injective _ (period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl)).eq_iff
theorem blockCostAt_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    (coldChartSetting R V).blockCostAt Y η =
      cellEnergyShare R.params.coupling (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
        (frameCoords c η) (topField V) :=
  blockCost_eq_cellEnergyShare c.cover c.side_odd c.two_le _ (c.isCold η hη) (c.share_eq η hη) V
    (frameCoords c η) (readAtLevel_field c.cover c.side_odd V η).symm Y
theorem totalCost_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).totalCost η = chartedEnergy R.params.coupling (frameCoords c η) (topField V) := by
  have h := (c.shares_sum (stepTorusFrame R n) R.params.coupling (frameCoords c η) (topField V)
    c.coupling_nonneg c.side_odd (fun _ => c.two_le)).2
  rw [← h, sum_finiteCells]
  exact Finset.sum_congr rfl fun Y _ => blockCostAt_eq c η hη Y
theorem blockGaussian_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (Y : TorusSite n) :
    (coldChartSetting R V).blockGaussian lam Y η =
      cellQuadratic lam R.coupling (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
        (toStepVariable c.cover c.side_odd V η) := by
  unfold ChartSetting.blockGaussian cellQuadratic ChartSetting.freeBondsOf
  rw [← Equiv.sum_comp (freeBondsEquivChord c.cover c.side_odd V), Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : bondBlock (R := R) b.1 = Y
  · rw [if_pos hb, if_pos ((enclosingCell_freeBond_iff c b Y).2 hb), toStepVariable_apply]
  · rw [if_neg hb, if_neg (fun h => hb ((enclosingCell_freeBond_iff c b Y).1 h))]
theorem cutoffProduct_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (coldChartSetting R V).cutoffProduct η =
      cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) := by
  unfold ChartSetting.cutoffProduct cutoffWeight
  rw [← Equiv.prod_comp (freeBondsEquivChord c.cover c.side_odd V)]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [toStepVariable_apply]
  have h : coordNorm (η b) = ‖η b‖ := norm_toImaginary (η b)
  rw [h]
end Context
section Exponent
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
def blockConstant (R : StepSetup) : ℝ :=
  4 * logPartitionGap (R.params.coupling * R.coupling) +
    (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0)
theorem logPartitionGap_meanNorm (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) (i : Fin 4) :
    logPartitionGap (R.params.coupling * R.coupling *
        meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i)) =
      haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (toStepVariable c.cover c.side_odd V η))
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y, i) +
        logPartitionGap (R.params.coupling * R.coupling) := by
  have h1 : meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i) =
      ‖blockContourAverage R.params.side ((coldChartSetting R V).field η) Y i‖ :=
    meanNorm_of_isCold R.params c.side_odd _ (c.isCold η hη) (Y, i)
  have h2 : _root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepTorusFrame R n).depth)
      (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable c.cover c.side_odd V η))
      (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y, i) =
        blockContourAverage R.params.side ((coldChartSetting R V).field η) Y i := by
    rw [← readAtLevel_field c.cover c.side_odd V η]
    exact contourAverage_readAtLevel (H := stepTorusFrame R n) (n := n) (fun _ => rfl) _ Y i
  unfold haarGapExcess
  rw [h1, h2, c.weyl.2.2, c.weyl.2.2]
  ring
theorem log_haarLogDensity_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (b : ↥(coldChartSetting R V).free) :
    Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) =
      haarLogRatio (frameCoords c η (freeBondsEquivChord c.cover c.side_odd V b).1.1
          (freeBondsEquivChord c.cover c.side_odd V b).1.2) +
        Real.log (haarRadialDensity 0) := by
  rw [frameCoords_freeBond]
  have h1 : ((coldChartSetting R V).frame b.1 + toImaginary (η b) : imaginaryQuaternions) =
      toImaginary (toCoords ((coldChartSetting R V).frame b.1) + η b) := by
    rw [toImaginary_add, toImaginary_toCoords]
  have h2 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ < Real.pi := by
    have h3 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ ≤
        ‖toCoords ((coldChartSetting R V).frame b.1)‖ + ‖η b‖ := norm_add_le _ _
    have h4 : ‖toCoords ((coldChartSetting R V).frame b.1)‖ = ‖(coldChartSetting R V).frame b.1‖ := by
      rw [← norm_toImaginary, toImaginary_toCoords]
    have h5 := c.frame_norm_lt _ (freeBondsEquivChord c.cover c.side_odd V b).2
    have h6 : ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
        (freeBondsEquivChord c.cover c.side_odd V b).1 (topField (R := R) V)‖ =
        ‖(coldChartSetting R V).frame b.1‖ := rfl
    have h7 := hη b
    linarith
  have hp := haarRadialDensity_pos (norm_nonneg _) h2
  have h0 := haarRadialDensity_zero_pos
  unfold haarLogRatio
  rw [h1, norm_toImaginary, Real.log_div hp.ne' h0.ne']
  have e : haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b) =
      haarRadialDensity ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ := rfl
  rw [e]
  ring
open Classical in
theorem logJacobianAt_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    (coldChartSetting R V).logJacobianAt Y η = blockConstant R +
      (∑ e ∈ (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
          (fun e => e.1 = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y),
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (toStepVariable c.cover c.side_odd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (stepTorusFrame R n))),
        if enclosingCell k.1.1 = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y then
          haarLogRatio (frameCoords c η k.1.1 k.1.2) else 0 := by
  unfold ChartSetting.logJacobianAt ChartSetting.logJacobian
  rw [sum_bonds_starting, ← Equiv.sum_comp (freeBondsEquivChord c.cover c.side_odd V)]
  simp only [logPartitionGap_meanNorm c η hη Y]
  rw [Finset.sum_add_distrib]
  have h2 : ∀ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then
        Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) else 0) =
      (if enclosingCell (freeBondsEquivChord c.cover c.side_odd V b).1.1 =
          torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y then
        haarLogRatio (frameCoords c η (freeBondsEquivChord c.cover c.side_odd V b).1.1
          (freeBondsEquivChord c.cover c.side_odd V b).1.2) else 0) +
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) := by
    intro b
    by_cases hb : bondBlock (R := R) b.1 = Y
    · rw [if_pos hb, if_pos hb, if_pos ((enclosingCell_freeBond_iff c b Y).2 hb),
        log_haarLogDensity_eq c η hη]
    · rw [if_neg hb, if_neg hb, if_neg (fun h => hb ((enclosingCell_freeBond_iff c b Y).1 h))]
      simp
  have h3 : ∑ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) =
      (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := c.freeBond_card Y
    unfold ChartSetting.freeBondsOf at this
    rw [this]
  simp only [h2]
  rw [Finset.sum_add_distrib, h3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold blockConstant
  push_cast
  ring
end Exponent
section Slope
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
omit [NeZero n] in
theorem stepCoordinates_linear (v τ : ℝ) (w w' : StepVariable (finiteCells (stepTorusFrame R n)))
    (z : (stepTorusFrame R n).Site (stepTorusFrame R n).depth) (i : Fin 4) :
    stepCoordinates (v • w + τ • w') z i = v • stepCoordinates w z i + τ • stepCoordinates w' z i := by
  unfold stepCoordinates
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, toImaginary_add, toImaginary_smul]
  · simp
omit [NeZero n] in
theorem stepCoordinates_smul (v : ℝ) (w : StepVariable (finiteCells (stepTorusFrame R n)))
    (z : (stepTorusFrame R n).Site (stepTorusFrame R n).depth) (i : Fin 4) :
    stepCoordinates (v • w) z i = v • stepCoordinates w z i := by
  unfold stepCoordinates
  split_ifs with h
  · simp only [Pi.smul_apply, toImaginary_smul]
  · simp
theorem toStepVariable_linear (c : ColdTopData R n lam V) (v τ : ℝ)
    (η ξ : FreeCoords (coldChartSetting R V).free) :
    toStepVariable c.cover c.side_odd V (v • η + τ • ξ) =
      v • toStepVariable c.cover c.side_odd V η + τ • toStepVariable c.cover c.side_odd V ξ := rfl
theorem stepCoordinates_restrictToBond (c : ColdTopData R n lam V)
    (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free)
    (z : (stepTorusFrame R n).Site (stepTorusFrame R n).depth) (i : Fin 4) :
    stepCoordinates (toStepVariable c.cover c.side_odd V ((coldChartSetting R V).restrictToBond b η)) z i =
      if (z, i) = (freeBondsEquivChord c.cover c.side_odd V b).1 then toImaginary (η b) else 0 := by
  unfold stepCoordinates
  split_ifs with h1 h2 h2
  · have hk : (⟨(z, i), h1⟩ : ↥(chordBonds (finiteCells (stepTorusFrame R n)))) =
        freeBondsEquivChord c.cover c.side_odd V b :=
      Subtype.ext h2
    rw [hk, toStepVariable_apply]
    unfold ChartSetting.restrictToBond
    simp
  · have hk : (freeBondsEquivChord c.cover c.side_odd V).symm ⟨(z, i), h1⟩ ≠ b := by
      intro h
      apply h2
      have := congrArg (freeBondsEquivChord c.cover c.side_odd V) h
      rw [Equiv.apply_symm_apply] at this
      exact congrArg Subtype.val this
    have : toStepVariable c.cover c.side_odd V ((coldChartSetting R V).restrictToBond b η)
        ⟨(z, i), h1⟩ = 0 := by
      unfold toStepVariable ChartSetting.restrictToBond
      simp [hk]
    rw [this, toImaginary_zero]
  · exact absurd (h2 ▸ (freeBondsEquivChord c.cover c.side_odd V b).2) h1
  · rfl
theorem deriv_totalCost_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (b : ↥(coldChartSetting R V).free) :
    deriv (fun τ : ℝ =>
        (coldChartSetting R V).totalCost (v • η + τ • (coldChartSetting R V).restrictToBond b η)) 0 =
      chartedSlope R.params.coupling
        (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
          (v • toStepVariable c.cover c.side_odd V η)) (topField V)
        (freeBondsEquivChord c.cover c.side_odd V b).1
        (toImaginary (toStepVariable c.cover c.side_odd V η (freeBondsEquivChord c.cover c.side_odd V b))) := by
  unfold chartedSlope
  apply Filter.EventuallyEq.deriv_eq
  have hball : ∀ᶠ τ : ℝ in 𝓝 0, ∀ b',
      ‖(v • η + τ • (coldChartSetting R V).restrictToBond b η) b'‖ < R.ballRadius := by
    rw [Filter.eventually_all]
    intro b'
    have hc : Continuous fun τ : ℝ =>
        ‖(v • η + τ • (coldChartSetting R V).restrictToBond b η) b'‖ := by
      simp only [Pi.add_apply, Pi.smul_apply]
      fun_prop
    have h0 : ‖(v • η + (0 : ℝ) • (coldChartSetting R V).restrictToBond b η) b'‖ < R.ballRadius := by
      simp only [zero_smul, add_zero, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hv.1]
      have h1 := hη b'
      have h2 := norm_nonneg (η b')
      nlinarith [hv.1, hv.2]
    exact (hc.tendsto 0).eventually_lt_const h0
  filter_upwards [hball] with τ hτ
  rw [totalCost_eq c _ hτ]
  congr 1
  funext z i
  rw [Function.update_apply]
  have hw : frameCoords c (v • η + τ • (coldChartSetting R V).restrictToBond b η) z i =
      coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
          (v • toStepVariable c.cover c.side_odd V η) z i +
        τ • (if (z, i) = (freeBondsEquivChord c.cover c.side_odd V b).1 then toImaginary (η b) else 0) := by
    unfold frameCoords coordsAboveFrame
    rw [toStepVariable_linear c, stepCoordinates_linear, stepCoordinates_restrictToBond c,
      stepCoordinates_smul, add_assoc]
  rw [hw]
  by_cases h1 : z = (freeBondsEquivChord c.cover c.side_odd V b).1.1
  · subst h1
    rw [if_pos rfl, Function.update_apply]
    by_cases h2 : i = (freeBondsEquivChord c.cover c.side_odd V b).1.2
    · subst h2
      rw [if_pos rfl, if_pos rfl, toStepVariable_apply]
    · rw [if_neg h2, if_neg (fun h => h2 (congrArg Prod.snd h))]
      simp
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Prod.fst h))]
    simp
end Slope
section Means
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
open Classical in
theorem cellExponent_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    cellExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V)
        (toStepVariable c.cover c.side_odd V η) =
      (coldChartSetting R V).blockInteraction Y η - (coldChartSetting R V).logJacobianAt Y 0 +
        blockConstant R := by
  have h1 : ∑ k : ↥(chordBonds (finiteCells (stepTorusFrame R n))),
      (if enclosingCell k.1.1 = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y then
        ∫ v in (0 : ℝ)..1, chartedSlope R.params.coupling
          (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (v • toStepVariable c.cover c.side_odd V η)) (topField V) k.1
          (toImaginary (toStepVariable c.cover c.side_odd V η k)) else 0) =
      ∑ b ∈ (coldChartSetting R V).freeBondsOf Y, ∫ v in (0 : ℝ)..1,
        deriv (fun τ : ℝ =>
          (coldChartSetting R V).totalCost (v • η + τ • (coldChartSetting R V).restrictToBond b η)) 0 := by
    rw [← Equiv.sum_comp (freeBondsEquivChord c.cover c.side_odd V)]
    unfold ChartSetting.freeBondsOf
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : bondBlock (R := R) b.1 = Y
    · rw [if_pos hb, if_pos ((enclosingCell_freeBond_iff c b Y).2 hb)]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le zero_le_one] at hv
      exact (deriv_totalCost_eq c η hη v hv b).symm
    · rw [if_neg hb, if_neg (fun h => hb ((enclosingCell_freeBond_iff c b Y).1 h))]
  unfold cellExponent ChartSetting.blockInteraction
  rw [h1, logJacobianAt_eq c η hη Y]
  ring
abbrev stepBalls (R : StepSetup) (n : ℕ) : Set (StepVariable (finiteCells (stepTorusFrame R n))) :=
  openBallProduct (stepTorusFrame R n) R.ballRadius
theorem toStepVariable_mem (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) : toStepVariable c.cover c.side_odd V η ∈ stepBalls R n :=
  fun k => hη _
theorem norm_lt_of_toStepVariable_mem (c : ColdTopData R n lam V)
    (η : FreeCoords (coldChartSetting R V).free)
    (h : toStepVariable c.cover c.side_odd V η ∈ stepBalls R n) : ∀ b, ‖η b‖ < R.ballRadius := by
  intro b
  have := h (freeBondsEquivChord c.cover c.side_odd V b)
  rwa [toStepVariable_apply] at this
def IsBoundedOnBalls (R : StepSetup) (n : ℕ) (g : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ) :
    Prop :=
  ∃ (g' : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ) (K : ℝ), Measurable g' ∧
    (∀ k, |g' k| ≤ K) ∧ ∀ k ∈ stepBalls R n, g k = g' k
omit [NeZero n] in
theorem IsBoundedOnBalls.add {g h : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) (hh : IsBoundedOnBalls R n h) :
    IsBoundedOnBalls R n fun k => g k + h k := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  obtain ⟨h', K', h4, h5, h6⟩ := hh
  refine ⟨fun k => g' k + h' k, K + K', h1.add h4, fun k => ?_,
    fun k hk => by simp only [h3 k hk, h6 k hk]⟩
  exact (abs_add_le _ _).trans (add_le_add (h2 k) (h5 k))
omit [NeZero n] in
theorem IsBoundedOnBalls.mul {g h : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) (hh : IsBoundedOnBalls R n h) :
    IsBoundedOnBalls R n fun k => g k * h k := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  obtain ⟨h', K', h4, h5, h6⟩ := hh
  refine ⟨fun k => g' k * h' k, K * K', h1.mul h4, fun k => ?_,
    fun k hk => by simp only [h3 k hk, h6 k hk]⟩
  rw [abs_mul]
  exact mul_le_mul (h2 k) (h5 k) (abs_nonneg _) ((abs_nonneg _).trans (h2 k))
omit [NeZero n] in
theorem IsBoundedOnBalls.const (a : ℝ) : IsBoundedOnBalls R n fun _ => a :=
  ⟨fun _ => a, |a|, measurable_const, fun _ => le_rfl, fun _ _ => rfl⟩
omit [NeZero n] in
theorem IsBoundedOnBalls.neg {g : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) : IsBoundedOnBalls R n fun k => - g k := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  exact ⟨fun k => - g' k, K, h1.neg, fun k => by rw [abs_neg]; exact h2 k,
    fun k hk => by simp only [h3 k hk]⟩
omit [NeZero n] in
theorem IsBoundedOnBalls.exp {g : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) : IsBoundedOnBalls R n fun k => Real.exp (g k) := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  refine ⟨fun k => Real.exp (g' k), Real.exp K, Real.measurable_exp.comp h1, fun k => ?_,
    fun k hk => by simp only [h3 k hk]⟩
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (h2 k))
theorem IsBoundedOnBalls.sum {β : Type} (s : Finset β)
    {g : β → StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : ∀ i ∈ s, IsBoundedOnBalls R n (g i)) : IsBoundedOnBalls R n fun k => ∑ i ∈ s, g i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsBoundedOnBalls.const (R := R) (n := n) 0
  | insert a s ha ih =>
    have h1 := (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using h1
end Means
section Laws
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem measurable_indicator_openBallProduct {F : BlockFrame} {ρ : ℝ}
    {g : StepVariable (finiteCells F) → ℝ} (hg : ContinuousOn g (openBallProduct F ρ)) :
    Measurable ((openBallProduct F ρ).indicator g) := by apply _root_.YangMills.SharedProofs.p50454 <;> assumption
omit [NeZero n] in
theorem isBoundedOnBalls_of {g : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hc : ContinuousOn g (stepBalls R n)) (hb : ∀ η ∈ stepBalls R n, |g η| ≤ M) :
    IsBoundedOnBalls R n g := by
  refine ⟨(stepBalls R n).indicator g, M, measurable_indicator_openBallProduct hc, fun k => ?_,
    fun k hk => ?_⟩
  · by_cases h : k ∈ stepBalls R n
    · rw [Set.indicator_of_mem h]; exact hb k h
    · rw [Set.indicator_of_notMem h]; simpa using hM
  · rw [Set.indicator_of_mem hk]
omit [NeZero n] in
theorem IsBoundedOnBalls.congr {g h : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) (e : ∀ k ∈ stepBalls R n, g k = h k) : IsBoundedOnBalls R n h := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  exact ⟨g', K, h1, h2, fun k hk => (e k hk).symm.trans (h3 k hk)⟩
theorem integral_toStepVariable (c : ColdTopData R n lam V)
    (h : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ) :
    ∫ η : FreeCoords (coldChartSetting R V).free, h (toStepVariable c.cover c.side_odd V η) =
      ∫ k, h k := by
  have mp := volume_measurePreserving_piCongrLeft
    (fun _ : ↥(chordBonds (finiteCells (stepTorusFrame R n))) => EuclideanSpace ℝ (Fin 3))
    (freeBondsEquivChord c.cover c.side_odd V)
  have e : ∀ η : FreeCoords (coldChartSetting R V).free, toStepVariable c.cover c.side_odd V η =
      (MeasurableEquiv.piCongrLeft
        (fun _ : ↥(chordBonds (finiteCells (stepTorusFrame R n))) => EuclideanSpace ℝ (Fin 3))
        (freeBondsEquivChord c.cover c.side_odd V)) η := by
    intro η
    funext k
    obtain ⟨b, rfl⟩ := (freeBondsEquivChord c.cover c.side_odd V).surjective k
    rw [toStepVariable_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp only [e]
  exact mp.integral_comp' h
section Regular
variable {M : ℝ}
  (hreg : IsRegularStep R.params.coupling R.anchorRadius R.ballRadius lam R.coupling M R.frameReach
    R.barrierFn (localFamilyOfDensity R.density) (topField (R := R) V))
include hreg
theorem cutoffWeight_toStepVariable_eq_zero (c : ColdTopData R n lam V)
    (η : FreeCoords (coldChartSetting R V).free) (h : ¬ ∀ b, ‖η b‖ < R.ballRadius) :
    cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) = 0 :=
  hreg.cutoffWeight_eq_zero_of_not_mem _ fun h2 => h (norm_lt_of_toStepVariable_mem c η h2)
theorem integrable_cutoffWeight_mul {g : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hg : IsBoundedOnBalls R n g) :
    Integrable fun k => cutoffWeight R.ballRadius R.barrierFn k * g k := by
  obtain ⟨g', K, h1, h2, h3⟩ := hg
  have e : (fun k => cutoffWeight R.ballRadius R.barrierFn k * g k) =
      fun k => cutoffWeight R.ballRadius R.barrierFn k * g' k := by
    funext k
    by_cases hk : k ∈ stepBalls R n
    · rw [h3 k hk]
    · rw [hreg.cutoffWeight_eq_zero_of_not_mem k hk]; simp
  rw [e]
  refine (hreg.integrable_cutoffWeight.mul_const K).mono'
    (hreg.measurable_cutoffWeight.mul h1).aestronglyMeasurable (Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hreg.cutoffWeight_nonneg k)]
  exact mul_le_mul_of_nonneg_left (h2 k) (hreg.cutoffWeight_nonneg k)
theorem integral_cutoffWeight_mul_exp_pos {Ψ : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hΨ : IsBoundedOnBalls R n Ψ) :
    0 < ∫ k, cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k) := by
  obtain ⟨g', K, h1, h2, h3⟩ := id hΨ
  have hi := integrable_cutoffWeight_mul hreg hΨ.neg.exp
  have hle : ∫ k : StepVariable (finiteCells (stepTorusFrame R n)),
      cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- K) ≤
      ∫ k, cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k) := by
    refine integral_mono (hreg.integrable_cutoffWeight.mul_const _) hi fun k => ?_
    by_cases hk : k ∈ stepBalls R n
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hreg.cutoffWeight_nonneg k)
      rw [h3 k hk]
      have := le_abs_self (g' k)
      have := h2 k
      linarith
    · simp [hreg.cutoffWeight_eq_zero_of_not_mem k hk]
  rw [integral_mul_const] at hle
  exact lt_of_lt_of_le (mul_pos hreg.integral_cutoffWeight_pos (Real.exp_pos _)) hle
theorem weightedMean_eq_cutoffMean (c : ColdTopData R n lam V)
    {Ψ H : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hΨ : IsBoundedOnBalls R n Ψ) (hH : IsBoundedOnBalls R n H) (e c0 : ℝ) (hc0 : c0 ≠ 0)
    (d G : FreeCoords (coldChartSetting R V).free → ℝ)
    (hd : ∀ η, d η = c0 * (cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) *
      Real.exp (- Ψ (toStepVariable c.cover c.side_odd V η))))
    (hG : ∀ η, (∀ b, ‖η b‖ < R.ballRadius) → G η = H (toStepVariable c.cover c.side_odd V η) + e) :
    weightedMean d G = cutoffMean R.ballRadius R.barrierFn Ψ H + e := by
  have hm := integral_cutoffWeight_mul_exp_pos hreg hΨ
  have hi1 : Integrable fun k =>
      H k * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k)) := by
    have := integrable_cutoffWeight_mul hreg (hH.mul hΨ.neg.exp)
    refine this.congr (Eventually.of_forall fun k => ?_)
    simp only
    ring
  have hi2 := integrable_cutoffWeight_mul hreg hΨ.neg.exp
  have h1 : ∫ η, G η * d η =
      c0 * ((∫ k, H k * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k))) +
        e * ∫ k, cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k)) := by
    let Fn : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ := fun k =>
      c0 * (H k * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k)) +
        e * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k)))
    have pt : ∀ η, G η * d η = Fn (toStepVariable c.cover c.side_odd V η) := by
      intro η
      by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
      · simp only [Fn]
        rw [hG η hη, hd η]
        ring
      · simp only [Fn]
        rw [hd η, cutoffWeight_toStepVariable_eq_zero hreg c η hη]
        simp
    refine (integral_congr_ae (Eventually.of_forall pt)).trans
      ((integral_toStepVariable c Fn).trans ?_)
    simp only [Fn]
    rw [integral_const_mul, integral_add hi1 (hi2.const_mul e), integral_const_mul]
  have h2 : ∫ η, d η = c0 * ∫ k, cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k) := by
    refine (integral_congr_ae (Eventually.of_forall hd)).trans
      ((integral_toStepVariable c
        (fun k => c0 * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- Ψ k)))).trans ?_)
    rw [integral_const_mul]
  unfold weightedMean cutoffMean
  rw [h1, h2]
  field_simp
end Regular
end Laws
section Final
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
abbrev exponentAt (R : StepSetup) (n : ℕ) (ν : ℝ) (V : TorusField n) :
    StepVariable (finiteCells (stepTorusFrame R n)) → ℝ :=
  stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
    (localFamilyOfDensity R.density) ν (topField V)
def exponentShift (R : StepSetup) (V : TorusField n) : ℝ :=
  ∑ Y : TorusSite n, ((coldChartSetting R V).logJacobianAt Y 0 - blockConstant R)
theorem exponentAt_eq (ν : ℝ) (k : StepVariable (finiteCells (stepTorusFrame R n))) :
    exponentAt R n ν V k = exponentAt R n 0 V k -
      ν * ∑ y ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density)
          y k (topField V) := by
  unfold exponentAt stepExponent
  ring
theorem sum_cellCentredExpansion (c : ColdTopData R n lam V) (k : StepVariable (finiteCells (stepTorusFrame R n))) :
    ∑ Z ∈ finiteCells (stepTorusFrame R n),
        cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
          (localFamilyOfDensity R.density) Z k (topField V) =
      ∑ y ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach
          (localFamilyOfDensity R.density) y k (topField V) := by
  unfold cellCentredExpansion
  exact Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells _) _
theorem sum_cellQuadratic (lam' : ℝ) (k : StepVariable (finiteCells (stepTorusFrame R n))) :
    ∑ Z ∈ finiteCells (stepTorusFrame R n), cellQuadratic lam' R.coupling Z k =
      totalQuadratic lam' R.coupling k := by
  classical
  unfold cellQuadratic totalQuadratic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (enclosingCell b.1.1)]
  · simp
  · intro Y _ hY
    simp [Ne.symm hY]
  · intro h
    exact absurd (_root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells _) h
section Regular
variable {M : ℝ}
  (hreg : IsRegularStep R.params.coupling R.anchorRadius R.ballRadius lam R.coupling M R.frameReach
    R.barrierFn (localFamilyOfDensity R.density) (topField (R := R) V))
include hreg
theorem isBoundedOnBalls_cellExponent (Z : (stepTorusFrame R n).Cell) :
    IsBoundedOnBalls R n
      (cellExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach Z (topField V)) :=
  isBoundedOnBalls_of hreg.bound_nonneg (hreg.continuousOn_cellExponent Z) (hreg.abs_cellExponent_le Z)
theorem isBoundedOnBalls_cellQuadratic (Z : (stepTorusFrame R n).Cell) :
    IsBoundedOnBalls R n (cellQuadratic lam R.coupling Z) :=
  isBoundedOnBalls_of hreg.bound_nonneg (hreg.continuousOn_cellQuadratic Z) (hreg.abs_cellQuadratic_le Z)
theorem isBoundedOnBalls_cellCentredExpansion (Z : (stepTorusFrame R n).Cell) :
    IsBoundedOnBalls R n fun k => cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
      (localFamilyOfDensity R.density) Z k (topField V) :=
  isBoundedOnBalls_of hreg.bound_nonneg (hreg.continuousOn_cellCentredExpansion Z)
    (hreg.abs_cellCentredExpansion_le Z)
theorem isBoundedOnBalls_exponentAt_zero : IsBoundedOnBalls R n (exponentAt R n 0 V) :=
  (IsBoundedOnBalls.sum _ fun Z _ => isBoundedOnBalls_cellExponent hreg Z).congr
    fun k hk => (hreg.stepExponent_eq_sum k hk).symm
theorem isBoundedOnBalls_totalQuadratic : IsBoundedOnBalls R n (totalQuadratic lam R.coupling) :=
  (IsBoundedOnBalls.sum _ fun Z _ => isBoundedOnBalls_cellQuadratic hreg Z).congr
    fun k _ => sum_cellQuadratic lam k
theorem isBoundedOnBalls_exponentAt (c : ColdTopData R n lam V) (ν : ℝ) :
    IsBoundedOnBalls R n (exponentAt R n ν V) := by
  have h1 := (IsBoundedOnBalls.sum (finiteCells (stepTorusFrame R n))
    fun Z _ => isBoundedOnBalls_cellCentredExpansion hreg Z)
  have h2 := (isBoundedOnBalls_exponentAt_zero hreg).add ((IsBoundedOnBalls.const (-ν)).mul h1)
  refine h2.congr fun k _ => ?_
  rw [exponentAt_eq ν k, sum_cellCentredExpansion c k]
  ring
theorem isBoundedOnBalls_segment (τ : ℝ) :
    IsBoundedOnBalls R n fun k => τ * exponentAt R n 0 V k + (1 - τ) * totalQuadratic lam R.coupling k :=
  ((IsBoundedOnBalls.const τ).mul (isBoundedOnBalls_exponentAt_zero hreg)).add
    ((IsBoundedOnBalls.const (1 - τ)).mul (isBoundedOnBalls_totalQuadratic hreg))
theorem totalInteraction_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).totalInteraction η =
      exponentAt R n 0 V (toStepVariable c.cover c.side_odd V η) + exponentShift R V := by
  have h := hreg.stepExponent_eq_sum (toStepVariable c.cover c.side_odd V η) (toStepVariable_mem c η hη)
  have h2 := sum_finiteCells (R := R) (n := n) fun Z =>
    cellExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach Z (topField V)
      (toStepVariable c.cover c.side_odd V η)
  show _ = stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
    (localFamilyOfDensity R.density) 0 (topField V) (toStepVariable c.cover c.side_odd V η) + _
  rw [h, h2]
  unfold ChartSetting.totalInteraction exponentShift
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [cellExponent_eq c η hη Y]
  ring
theorem interpolatedDensity_eq (c : ColdTopData R n lam V) (τ : ℝ)
    (η : FreeCoords (coldChartSetting R V).free) :
    (coldChartSetting R V).interpolatedDensity lam τ η = Real.exp (-(τ * exponentShift R V)) *
      (cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) *
        Real.exp (-(τ * exponentAt R n 0 V (toStepVariable c.cover c.side_odd V η) +
          (1 - τ) * totalQuadratic lam R.coupling (toStepVariable c.cover c.side_odd V η)))) := by
  unfold ChartSetting.interpolatedDensity
  rw [cutoffProduct_eq c]
  by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
  · have h1 : ∑ Y : TorusSite n, (coldChartSetting R V).blockGaussian lam Y η =
        totalQuadratic lam R.coupling (toStepVariable c.cover c.side_odd V η) := by
      rw [← sum_cellQuadratic lam, sum_finiteCells]
      exact Finset.sum_congr rfl fun Y _ => blockGaussian_eq c η Y
    rw [totalInteraction_eq hreg c η hη, h1, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  · rw [cutoffWeight_toStepVariable_eq_zero hreg c η hη]
    simp
theorem perturbedDensity_eq (c : ColdTopData R n lam V) (ν : ℝ)
    (η : FreeCoords (coldChartSetting R V).free) :
    (coldChartSetting R V).perturbedDensity ν η = Real.exp (- exponentShift R V) *
      (cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) *
        Real.exp (- exponentAt R n ν V (toStepVariable c.cover c.side_odd V η))) := by
  unfold ChartSetting.perturbedDensity
  rw [cutoffProduct_eq c]
  by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
  · have h1 : ∑ Y : TorusSite n, (coldChartSetting R V).blockDensityAt Y η =
        ∑ y ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth,
          centredExpansion false R.params.coupling R.anchorRadius R.frameReach
            (localFamilyOfDensity R.density) y (toStepVariable c.cover c.side_odd V η) (topField V) := by
      rw [← sum_cellCentredExpansion c, sum_finiteCells]
      exact Finset.sum_congr rfl fun Y _ =>
        blockDensityAt_eq_cellCentredExpansion c.cover c.side_odd c.expansions c.n₀_le V η (c.isCold η hη) Y
    rw [totalInteraction_eq hreg c η hη, h1, exponentAt_eq ν, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  · rw [cutoffWeight_toStepVariable_eq_zero hreg c η hη]
    simp
theorem weightedMean_interpolated (c : ColdTopData R n lam V) (τ : ℝ) (Y : TorusSite n) :
    weightedMean ((coldChartSetting R V).interpolatedDensity lam τ)
        (fun η => (coldChartSetting R V).blockInteraction Y η -
          (coldChartSetting R V).blockGaussian lam Y η) =
      cutoffMean R.ballRadius R.barrierFn
          (fun k => τ * exponentAt R n 0 V k + (1 - τ) * totalQuadratic lam R.coupling k)
          (fun k => cellExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
              (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) k -
            cellQuadratic lam R.coupling (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) k) +
        ((coldChartSetting R V).logJacobianAt Y 0 - blockConstant R) := by
  refine weightedMean_eq_cutoffMean hreg c (isBoundedOnBalls_segment hreg τ)
    ((isBoundedOnBalls_cellExponent hreg _).add
      ((IsBoundedOnBalls.const (-1)).mul (isBoundedOnBalls_cellQuadratic hreg _)) |>.congr
        fun k _ => by ring)
    _ _ (Real.exp_pos _).ne' _ _ (fun η => interpolatedDensity_eq hreg c τ η) fun η hη => ?_
  rw [cellExponent_eq c η hη Y, blockGaussian_eq c η Y]
  ring
theorem weightedMean_perturbed (c : ColdTopData R n lam V) (ν : ℝ) (Y : TorusSite n) :
    weightedMean ((coldChartSetting R V).perturbedDensity ν) ((coldChartSetting R V).blockDensityAt Y) =
      cutoffMean R.ballRadius R.barrierFn (exponentAt R n ν V)
        (fun k => cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
          (localFamilyOfDensity R.density)
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) k (topField V)) := by
  have h := weightedMean_eq_cutoffMean hreg c (isBoundedOnBalls_exponentAt hreg c ν)
    (isBoundedOnBalls_cellCentredExpansion hreg
      (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y))
    0 _ (Real.exp_pos (- exponentShift R V)).ne' ((coldChartSetting R V).perturbedDensity ν)
    ((coldChartSetting R V).blockDensityAt Y)
    (fun η => perturbedDensity_eq hreg c ν η) fun η hη => ?_
  · simpa using h
  · rw [add_zero]
    exact blockDensityAt_eq_cellCentredExpansion c.cover c.side_odd c.expansions c.n₀_le V η (c.isCold η hη) Y
end Regular
end Final
section Close
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
section Regular
variable {M : ℝ}
  (hreg : IsRegularStep R.params.coupling R.anchorRadius R.ballRadius lam R.coupling M R.frameReach
    R.barrierFn (localFamilyOfDensity R.density) (topField (R := R) V))
include hreg
theorem continuous_cutoffMean_segment {H : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ}
    (hH : IsBoundedOnBalls R n H) :
    Continuous fun τ : ℝ =>
      cutoffMean R.ballRadius R.barrierFn
        (fun k => τ * exponentAt R n 0 V k + (1 - τ) * totalQuadratic lam R.coupling k) H := by
  obtain ⟨B, KB, hB1, hB2, hB3⟩ := isBoundedOnBalls_exponentAt_zero hreg
  obtain ⟨A, KA, hA1, hA2, hA3⟩ := isBoundedOnBalls_totalQuadratic hreg
  obtain ⟨H', KH, hH1, hH2, hH3⟩ := hH
  have key : ∀ (G : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ) (KG : ℝ), Measurable G →
      (∀ k, |G k| ≤ KG) → Continuous fun τ : ℝ =>
        ∫ k, cutoffWeight R.ballRadius R.barrierFn k *
          (G k * Real.exp (-(τ * B k + (1 - τ) * A k))) := by
    intro G KG hG hGK
    rw [continuous_iff_continuousAt]
    intro τ₀
    apply continuousAt_of_dominated
      (bound := fun k => cutoffWeight R.ballRadius R.barrierFn k *
        (KG * Real.exp ((|τ₀| + 1) * KB + (|τ₀| + 2) * KA)))
    · refine Eventually.of_forall fun τ => ?_
      exact (hreg.measurable_cutoffWeight.mul (hG.mul (Real.measurable_exp.comp
        ((hB1.const_mul τ).add (hA1.const_mul (1 - τ))).neg))).aestronglyMeasurable
    · have hb : Metric.ball τ₀ 1 ∈ 𝓝 τ₀ := Metric.ball_mem_nhds _ one_pos
      filter_upwards [hb] with τ hτ
      refine Eventually.of_forall fun k => ?_
      have hτ' : |τ - τ₀| < 1 := by simpa [Real.dist_eq] using hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hreg.cutoffWeight_nonneg k), abs_mul,
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (hreg.cutoffWeight_nonneg k)
      have hK : 0 ≤ KG := (abs_nonneg _).trans (hGK k)
      refine mul_le_mul (hGK k) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hK
      have h1 : |τ| ≤ |τ₀| + 1 := by
        have := abs_sub_abs_le_abs_sub τ τ₀
        linarith
      have h2 : |1 - τ| ≤ |τ₀| + 2 := by
        have := abs_sub 1 τ
        simp only [abs_one] at this
        linarith
      have hKB : 0 ≤ KB := (abs_nonneg _).trans (hB2 k)
      have hKA : 0 ≤ KA := (abs_nonneg _).trans (hA2 k)
      have h3 : |τ * B k + (1 - τ) * A k| ≤ (|τ₀| + 1) * KB + (|τ₀| + 2) * KA := by
        calc |τ * B k + (1 - τ) * A k| ≤ |τ * B k| + |(1 - τ) * A k| := abs_add_le _ _
          _ = |τ| * |B k| + |1 - τ| * |A k| := by rw [abs_mul, abs_mul]
          _ ≤ (|τ₀| + 1) * KB + (|τ₀| + 2) * KA := by
            gcongr
            · exact hB2 k
            · exact hA2 k
      have := neg_abs_le (τ * B k + (1 - τ) * A k)
      linarith
    · exact hreg.integrable_cutoffWeight.mul_const _
    · refine Eventually.of_forall fun k => ?_
      have : Continuous fun τ : ℝ =>
          cutoffWeight R.ballRadius R.barrierFn k * (G k * Real.exp (-(τ * B k + (1 - τ) * A k))) := by
        fun_prop
      exact this.continuousAt
  have hnum : ∀ τ : ℝ, ∫ k, H k * (cutoffWeight R.ballRadius R.barrierFn k *
      Real.exp (-(τ * exponentAt R n 0 V k + (1 - τ) * totalQuadratic lam R.coupling k))) =
      ∫ k, cutoffWeight R.ballRadius R.barrierFn k *
        (H' k * Real.exp (-(τ * B k + (1 - τ) * A k))) := by
    intro τ
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    by_cases hk : k ∈ stepBalls R n
    · simp only
      rw [hH3 k hk, hB3 k hk, hA3 k hk]
      ring
    · simp only
      rw [hreg.cutoffWeight_eq_zero_of_not_mem k hk]
      simp
  have hden : ∀ τ : ℝ, ∫ k, cutoffWeight R.ballRadius R.barrierFn k *
      Real.exp (-(τ * exponentAt R n 0 V k + (1 - τ) * totalQuadratic lam R.coupling k)) =
      ∫ k, cutoffWeight R.ballRadius R.barrierFn k *
        ((1 : ℝ) * Real.exp (-(τ * B k + (1 - τ) * A k))) := by
    intro τ
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    by_cases hk : k ∈ stepBalls R n
    · simp only
      rw [hB3 k hk, hA3 k hk]
      ring
    · simp only
      rw [hreg.cutoffWeight_eq_zero_of_not_mem k hk]
      simp
  have hne : ∀ τ : ℝ, ∫ k, cutoffWeight R.ballRadius R.barrierFn k *
      ((1 : ℝ) * Real.exp (-(τ * B k + (1 - τ) * A k))) ≠ 0 := by
    intro τ
    rw [← hden τ]
    exact (integral_cutoffWeight_mul_exp_pos hreg (isBoundedOnBalls_segment hreg τ)).ne'
  have := (key H' KH hH1 hH2).div (key (fun _ => 1) 1 measurable_const (by simp)) hne
  refine this.congr fun τ => ?_
  unfold cutoffMean
  rw [hnum, hden]
  rfl
end Regular
theorem cellsOfSites_univ :
    cellsOfSites (stepTorusFrame R n) (Finset.univ : Finset (TorusSite n)) =
      finiteCells (stepTorusFrame R n) := by
  have htop : ∀ i, (stepTorusFrame R n).period (stepTorusFrame R n).top i = n :=
    period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl
  ext z
  constructor
  · intro _
    exact _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells z
  · intro _
    exact Finset.mem_image.2 ⟨toTorusSite n z, Finset.mem_univ _, torusSiteInFrame_toTorusSite _ htop z⟩
theorem levelShare_top (Y : TorusSite n) :
    levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V =
      minimalCellShare R.params.coupling (finiteCells (stepTorusFrame R n))
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField (R := R) V) := by
  show minimalCellShare R.params.coupling (cellsOfSites (stepTorusFrame R n) Finset.univ) _ _ = _
  rw [cellsOfSites_univ]
  rfl
theorem coordsAboveFrame_zero :
    coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0 =
      fun z i => ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
        (z, i) (topField (R := R) V) := by
  funext z i
  unfold coordsAboveFrame stepCoordinates
  by_cases h : (z, i) ∈ chordBonds (finiteCells (stepTorusFrame R n))
  · simp [h, toImaginary_zero]
  · simp [h]
theorem toStepVariable_zero (c : ColdTopData R n lam V) : toStepVariable c.cover c.side_odd V 0 = 0 := rfl
theorem coldLocalDensity_eq (c : ColdTopData R n lam V) (Y : TorusSite n) :
    (coldChartSetting R V).blockActivity lam Y +
        R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V -
        R.coldBlockConstant lam =
      interactionDensity false R.params.coupling R.anchorRadius R.ballRadius lam R.coupling R.frameReach
          R.barrierFn (localFamilyOfDensity R.density)
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) +
        expansionDensity false R.params.coupling R.anchorRadius R.ballRadius R.coupling R.frameReach R.barrierFn
          (localFamilyOfDensity R.density)
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) +
        frameDensity false R.params.coupling R.anchorRadius R.coupling R.frameReach
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) := by
  obtain ⟨M, hreg⟩ := c.regular
  have h0 : ∀ b : ↥(coldChartSetting R V).free,
      ‖(0 : FreeCoords (coldChartSetting R V).free) b‖ < R.ballRadius := by
    intro b
    simpa using c.ballRadius_pos
  have hH : IsBoundedOnBalls R n (fun k => cellExponent false R.params.coupling R.anchorRadius
      R.coupling R.frameReach (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
        (topField V) k -
      cellQuadratic lam R.coupling (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) k) :=
    ((isBoundedOnBalls_cellExponent hreg _).add
      ((IsBoundedOnBalls.const (-1)).mul (isBoundedOnBalls_cellQuadratic hreg _))).congr
        fun k _ => by ring
  have hU : ∫ τ in (0 : ℝ)..1, weightedMean ((coldChartSetting R V).interpolatedDensity lam τ)
        (fun η => (coldChartSetting R V).blockInteraction Y η -
          (coldChartSetting R V).blockGaussian lam Y η) =
      - interactionDensity false R.params.coupling R.anchorRadius R.ballRadius lam R.coupling
          R.frameReach R.barrierFn (localFamilyOfDensity R.density)
          (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) +
        ((coldChartSetting R V).logJacobianAt Y 0 - blockConstant R) := by
    simp only [weightedMean_interpolated hreg c]
    rw [intervalIntegral.integral_add ((continuous_cutoffMean_segment hreg hH).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const]
    unfold interactionDensity
    simp
  have hS : ∫ ν in (0 : ℝ)..1, weightedMean ((coldChartSetting R V).perturbedDensity ν)
        ((coldChartSetting R V).blockDensityAt Y) =
      expansionDensity false R.params.coupling R.anchorRadius R.ballRadius R.coupling R.frameReach R.barrierFn
        (localFamilyOfDensity R.density)
        (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y) (topField V) := by
    simp only [weightedMean_perturbed hreg c]
    rfl
  have hC : (coldChartSetting R V).blockCostAt Y 0 = cellEnergyShare R.params.coupling
      (torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y)
      (fun z i => ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
        (z, i) (topField (R := R) V))
      (topField V) := by
    rw [blockCostAt_eq c 0 h0 Y]
    unfold frameCoords
    rw [toStepVariable_zero c, coordsAboveFrame_zero]
  unfold ChartSetting.blockActivity frameDensity StepSetup.coldBlockConstant
  rw [hU, hS, hC, levelShare_top, c.freeBond_card Y]
  unfold blockConstant
  ring
end Close
section Image
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
open Classical in
theorem sum_bonds_by_cell (g : (stepTorusFrame R n).Site (stepTorusFrame R n).top × Fin 4 → ℝ) :
    ∑ Y : TorusSite n, ∑ e ∈ (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
        (fun e => e.1 = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y), g e =
      ∑ e ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top, g e := by
  rw [← sum_finiteCells (R := R) (n := n) (fun Z =>
    ∑ e ∈ (innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top).filter
      (fun e => e.1 = Z), g e)]
  exact Finset.sum_fiberwise_of_maps_to (fun e _ => _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells e.1) g
open Classical in
theorem sum_chordBonds_by_cell (h : ↥(chordBonds (finiteCells (stepTorusFrame R n))) → ℝ) :
    ∑ Y : TorusSite n, ∑ k : ↥(chordBonds (finiteCells (stepTorusFrame R n))),
        (if enclosingCell k.1.1 = torusSiteInFrame (stepTorusFrame R n) (stepTorusFrame R n).top Y then
          h k else 0) = ∑ k, h k := by
  rw [← sum_finiteCells (R := R) (n := n) (fun Z => ∑ k : ↥(chordBonds (finiteCells (stepTorusFrame R n))),
    if enclosingCell k.1.1 = Z then h k else 0), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq, if_pos (_root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells _)]
theorem sum_blockConstant (c : ColdTopData R n lam V) :
    ∑ _Y : TorusSite n, blockConstant R =
      (∑ _e ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top,
          haarGap (R.params.coupling * R.coupling)) +
        ∑ _k : ↥(chordBonds (finiteCells (stepTorusFrame R n))), Real.log (haarRadialDensity 0) := by
  classical
  have h1 : ∑ _e ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top,
      haarGap (R.params.coupling * R.coupling) =
      ∑ _Y : TorusSite n, 4 * logPartitionGap (R.params.coupling * R.coupling) := by
    rw [← sum_bonds_by_cell (R := R) (n := n) fun _ => haarGap (R.params.coupling * R.coupling)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [sum_bonds_starting (R := R) (n := n) (fun _ => haarGap (R.params.coupling * R.coupling)),
      c.weyl.2.2]
    simp
  have h2 : ∑ _k : ↥(chordBonds (finiteCells (stepTorusFrame R n))), Real.log (haarRadialDensity 0) =
      ∑ _Y : TorusSite n, (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0) := by
    rw [← Equiv.sum_comp (freeBondsEquivChord c.cover c.side_odd V) fun _ => Real.log (haarRadialDensity 0),
      ← Finset.sum_fiberwise Finset.univ (fun b : ↥(coldChartSetting R V).free => bondBlock (R := R) b.1)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    have := c.freeBond_card Y
    unfold ChartSetting.freeBondsOf at this
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
  rw [h1, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => rfl
theorem potential_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).potential η = exponentAt R n 1 V (toStepVariable c.cover c.side_odd V η) +
      R.coupling * chartedEnergy R.params.coupling
        (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
        (topField (R := R) V) - ∑ _Y : TorusSite n, blockConstant R := by
  classical
  have h1 : ∑ Y : TorusSite n, blockCost R.params R.depth ((coldChartSetting R V).field η)
      (coldChartSetting R V).coarse (coldChartSetting R V).bases Y =
      chartedEnergy R.params.coupling (frameCoords c η) (topField V) := totalCost_eq c η hη
  have h2 : ∑ Y : TorusSite n, (coldChartSetting R V).blockDensity ((coldChartSetting R V).field η) Y =
      ∑ y ∈ sitesOfCells (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) y
          (toStepVariable c.cover c.side_odd V η) (topField V) := by
    rw [← sum_cellCentredExpansion c, sum_finiteCells]
    exact Finset.sum_congr rfl fun Y _ =>
      blockDensityAt_eq_cellCentredExpansion c.cover c.side_odd c.expansions c.n₀_le V η (c.isCold η hη) Y
  have h3 : ∑ Y : TorusSite n, (coldChartSetting R V).logJacobian ((coldChartSetting R V).field η) η Y =
      (∑ _Y : TorusSite n, blockConstant R) +
      (∑ e ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top,
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (toStepVariable c.cover c.side_odd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (stepTorusFrame R n))), haarLogRatio (frameCoords c η k.1.1 k.1.2) := by
    rw [← sum_bonds_by_cell, ← sum_chordBonds_by_cell, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Y _ => logJacobianAt_eq c η hη Y
  unfold ChartSetting.potential
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3]
  unfold exponentAt stepExponent
  ring
theorem mul_exp_rearrange (r E x S G Lg : ℝ) :
    r * Real.exp (-(E + x * S - (G + Lg))) =
      Real.exp G * Real.exp Lg * Real.exp (- x * S) * (r * Real.exp (- E)) := by
  have h : Real.exp (-(E + x * S - (G + Lg))) =
      Real.exp G * Real.exp Lg * Real.exp (- x * S) * Real.exp (- E) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h]
  ring
theorem coldImageIntegral_eq (c : ColdTopData R n lam V) :
    ∫ η, (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η) =
      coldStepIntegral R n V := by
  obtain ⟨M, hreg⟩ := c.regular
  have hfix := c.fixed (stepTorusFrame R n) R.params.coupling R.anchorRadius R.ballRadius R.coupling
    R.frameReach R.barrierFn (localFamilyOfDensity R.density) (topField V) c.side_odd
    (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) c.frame_norm_lt
  have hprod : (∏ _b : ↥(chordBonds (finiteCells (stepTorusFrame R n))), haarRadialDensity 0) =
      Real.exp (∑ _b : ↥(chordBonds (finiteCells (stepTorusFrame R n))), Real.log (haarRadialDensity 0)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun _ _ => (Real.exp_log haarRadialDensity_zero_pos).symm
  rw [hprod] at hfix
  let Cst : ℝ := Real.exp (∑ _c ∈ innerBonds (finiteCells (stepTorusFrame R n)) (stepTorusFrame R n).top,
      haarGap (R.params.coupling * R.coupling)) *
    Real.exp (∑ _b : ↥(chordBonds (finiteCells (stepTorusFrame R n))), Real.log (haarRadialDensity 0)) *
    Real.exp (- R.coupling * chartedEnergy R.params.coupling
      (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
      (topField (R := R) V))
  let Fn : StepVariable (finiteCells (stepTorusFrame R n)) → ℝ := fun k =>
    Cst * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- exponentAt R n 1 V k))
  have pt : ∀ η, (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η) =
      Fn (toStepVariable c.cover c.side_odd V η) := by
    intro η
    simp only [Fn, Cst]
    rw [cutoffProduct_eq c]
    by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
    · rw [potential_eq c η hη, sum_blockConstant c]
      exact mul_exp_rearrange _ _ _ _ _ _
    · rw [cutoffWeight_toStepVariable_eq_zero hreg c η hη]
      simp
  refine (integral_congr_ae (Eventually.of_forall pt)).trans ((integral_toStepVariable c Fn).trans ?_)
  simp only [Fn]
  rw [integral_const_mul]
  unfold coldStepIntegral
  exact hfix.symm
end Image
theorem card_freeBondsOf (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (hcount : ChartBondCountPerBlock) (hodd : Odd R.params.side) (hn : 2 ≤ n) (Y : TorusSite n) :
    ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side := by
  classical
  rw [← hcount R.params.side n hodd hn Y]
  unfold ChartSetting.freeBondsOf
  refine Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_filter.2 ⟨b.2, (Finset.mem_filter.1 hb).2⟩
  · intro b _ b' _ h
    exact Subtype.ext h
  · intro b hb
    have h := Finset.mem_filter.1 hb
    exact ⟨⟨b, h.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2⟩, rfl⟩
end EvaluationMaps
open EvaluationMaps in
theorem coldImage_factors_through_coldStep (hcold : ColdChartSettingIsCold)
    (hshare : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hcount : ChartBondCountPerBlock)
    (hrow : ColdExpansionRegular) (hweyl : WeylIntegrationFormula)
    (hsum : sumCellSharesEqAction) (hfix : stepIntegralInFixedVariables)
    (hcov : BlocksCoverLowerLevel) : ColdImageFactorsThroughColdStep := by
  intro T hT hC
  obtain ⟨y₁, hy₁⟩ := hcold T hT
  refine ⟨max y₁ (max T.yC T.floorMin), fun y hy R hR n _ hn V hV => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyC : T.yC ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy0 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hcoldR : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) →
      IsCold T.threshold ((coldChartSetting R V).field η) := by
    intro η hη x μ ν hμ
    have h1 := hy₁ y hy1 R hR n hn V hV η
      (fun b => (by simpa [coordNorm_eq] using (hη b).le)) x μ ν hμ
    linarith
  obtain ⟨cn, nss, hties, hall⟩ := hC
  obtain ⟨-, e_lam, e_ρ, -, -, -, -, -⟩ := hties
  have hD := hall y hyC
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have h1 : ℓ = T.stepParameters y := hR.params_eq
  have h2 : ρA = T.ρA := hR.anchorRadius_eq
  have h3 : p = T.cutoff := hR.barrierFn_eq
  have hx : y ≤ x := hR.le_coupling
  have hstep := hR.isStep
  subst h1 h2 h3
  have hfits := hT.fits y hy0
  have hbelow := hrow (T.stepParameters y) t x D f hfits rfl hstep.1.1
  have hden := hD t x hx (localFamilyOfDensity f) hbelow
  set R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩ with hRdef
  have hL4 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hoddR : Odd R.params.side := hT.L_odd
  have hcoldV : IsSmallCurvature (9 / 8 * T.threshold) (topField (R := R) V) := by
    intro q hq
    rw [plaquetteDefect_readAtLevel (period_top (H := stepTorusFrame R n) (n := n) fun _ => rfl)]
    exact hV _ _ _ hq
  have htop : IsCubicTopTorus T.side t T.n₀ (stepTorusFrame R n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  obtain ⟨hfr, M, hreg⟩ := hden.regular (stepTorusFrame R n) htop (topField (R := R) V) hcoldV
  rw [show (T.stepParamsAt cn nss y).chainParams = cn from rfl] at hfr hreg
  rw [e_ρ] at hfr hreg
  rw [e_lam] at hreg
  have c : ColdTopData R n T.lam V :=
    { cover := hcov
      side_odd := hoddR
      two_le := hn2
      coupling_nonneg := by have := hT.a_ge; show (0 : ℝ) ≤ T.coupling; linarith
      n₀_le := hn
      ballRadius_pos := by have := hT.σ_pos; show (0 : ℝ) < T.threshold / 64; positivity
      expansions := hstep.1
      weyl := hweyl
      shares_sum := hsum
      fixed := hfix
      isCold := hcoldR
      share_eq := fun η hη y' => hshare T hT t n hn _ (hcoldR η hη) y'
      frame_norm_lt := hfr
      freeBond_card := card_freeBondsOf R V hcount hoddR hn2
      regular := ⟨M, hreg⟩ }
  refine ⟨?_, fun Y => ?_⟩
  · unfold coldImageIntegral
    rw [coldImageIntegral_eq c]
  · have h := coldLocalDensity_eq c Y
    unfold coldLocalDensity
    rw [dif_neg (NeZero.ne n)]
    exact h
end ColdImage
end YangMills.Construction
end
