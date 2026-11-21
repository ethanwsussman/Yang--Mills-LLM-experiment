import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.RunningCouplingSlope.ColdImageOnASmallTorus
import YangMills.Construction.RunningCouplingSlope.ColdSettingIsColdOnASmallTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
namespace SmallTorusImage
theorem cast_cast_intCast (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_inFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    toTorusSite m (torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem inFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    torusSiteInFrame H j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem inFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x + y) = torusSiteInFrame H j x + torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem inFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem inFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    torusSiteInFrame H j (-x) = - torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem inFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x - y) = torusSiteInFrame H j x - torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, inFrame_add j hm, inFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusField m) : TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_inFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m) (x : TorusSite m)
    (i : Fin 4) : readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (l : List PathStep) :
    pathHolonomy (readAtLevel H j W) (torusSiteInFrame H j x) l = torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + torusSiteInFrame H j x = torusSiteInFrame H j
        (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [inFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, inFrame_neg j hm, inFrame_unitStep j hm, add_comm]
      · simp [stepDisplacement, inFrame_unitStep j hm, add_comm]
    simp only [pathHolonomy, torusPathHolonomy]
    rw [add_comm (torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      rw [← inFrame_unitStep j hm, ← inFrame_sub j hm, readAtLevel_inFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_inFrame j hm]
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem cast_cast_cast (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_inFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) (k : Fin 4) :
    siteCoords (torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  cast_cast_cast _ _ (hm k) (x k)
def blockCentre (L : ℕ) (Y : TorusSite n) : TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_inFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    enclosingCell (torusSiteInFrame H H.depth x) = torusSiteInFrame H H.top (parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_inFrame (H := H) H.depth (period_depth hs) x k
  show ((((siteCoords (torusSiteInFrame H H.depth x) k + ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
    (H.blockSide : ℤ) ^ (H.top - H.depth) : ℤ)) : ZMod (H.period H.top k)) = _
  rw [h1, he, pow_one]
  exact (cast_cast_intCast _ _ (period_top hs k) _).symm
theorem inFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_inFrame j hm x, h, toTorusSite_inFrame j hm y]
theorem isCrossingBond_inFrame_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsCrossingBond (F := H) (torusSiteInFrame H H.depth x, i) ↔
      parentBlock H.blockSide (x + TorusFields.unitStep _ i) ≠ parentBlock H.blockSide x := by
  unfold IsCrossingBond
  show enclosingCell (torusSiteInFrame H H.depth x + BlockAverages.unitStep H.depth i) ≠
    enclosingCell (torusSiteInFrame H H.depth x) ↔ _
  rw [← inFrame_unitStep H.depth (period_depth hs), ← inFrame_add H.depth (period_depth hs),
    enclosingCell_inFrame hs, enclosingCell_inFrame hs]
  exact not_congr (inFrame_injective H.top (period_top hs)).eq_iff
theorem refineSite_inFrame (hs : ∀ i, H.extent i = n) (Y : TorusSite n) :
    refineSite (j := H.depth) (torusSiteInFrame H H.top Y) =
      torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.refineSite_torusSiteInFrame <;> assumption
def blockOffset (L : ℕ) (x : TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - blockCentre L (parentBlock L x)) k).valMinAbs
def IsBlockTreeBond (L : ℕ) (x : TorusSite (n * L)) (i : Fin 4) : Prop :=
  parentBlock L (x + TorusFields.unitStep _ i) = parentBlock L x ∧ ∀ l, i < l → blockOffset L x l = 0
theorem isAxialTreeBond_inFrame_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (torusSiteInFrame H H.depth x, i) ↔ IsBlockTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
def blockContourAverage (L : ℕ) (W : TorusField (n * L)) (Y : TorusSite n) (i : Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    ((torusPathHolonomy W (blockCentre L Y) (bondContour L h π i) : UnitQuaternion) : ℍ[ℝ])
theorem contourAverage_inFrame (hs : ∀ i, H.extent i = n) (W : TorusField (n * H.blockSide))
    (Y : TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) (readAtLevel H H.depth W) (torusSiteInFrame H H.top Y, i) =
      blockContourAverage H.blockSide W Y i := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage blockContourAverage
  simp only [refineSite_inFrame hs, pathHolonomy_readAtLevel H.depth (period_depth hs)]
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem contourMean_empty (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    contourMean J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) W c := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.contourMean_empty <;> assumption
end Plain
section Field
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev coldFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
abbrev levelFrame (R : StepSetup) (n : ℕ) : BlockFrame := stepBlockFrame R.params.side n
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
theorem mem_chartBonds_iff (b : TorusBond (n * R.params.side)) :
    b ∈ chartBonds R.params.side n ↔ ¬ IsBlockTreeBond R.params.side b.1 b.2 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_chartBonds_iff <;> assumption
theorem mem_finiteCells (z : (coldFrame R n).Cell) : z ∈ finiteCells (coldFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells <;> assumption
theorem mem_innerBonds_depth (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : (coldFrame R n).Site (coldFrame R n).depth × Fin 4) :
    b ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).depth := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_depth <;> assumption
theorem inFrame_mem_chordBonds_iff (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : TorusBond (n * R.params.side)) :
    (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth b.1, b.2) ∈
        chordBonds (finiteCells (coldFrame R n)) ↔
      b ∈ chartBonds R.params.side n := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.chordBonds_mem_iff <;> assumption
def chartBondEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) :
    ↥(chartBonds R.params.side n) ≃ ↥(chordBonds (finiteCells (coldFrame R n))) where
  toFun b := ⟨(torusSiteInFrame (coldFrame R n) (coldFrame R n).depth b.1.1, b.1.2),
    (inFrame_mem_chordBonds_iff hcov hodd b.1).2 b.2⟩
  invFun k := ⟨(toTorusSite (n * R.params.side) k.1.1, k.1.2), by
    rw [← inFrame_mem_chordBonds_iff hcov hodd]
    have h : torusSiteInFrame (coldFrame R n) (coldFrame R n).depth (toTorusSite (n * R.params.side) k.1.1) =
        k.1.1 :=
      inFrame_toTorusSite _ (period_depth (n := n) fun _ => rfl) _
    rw [h]
    exact k.2⟩
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · exact toTorusSite_inFrame _ (period_depth (n := n) fun _ => rfl) _
    · rfl
  right_inv k := by
    apply Subtype.ext
    apply Prod.ext
    · exact inFrame_toTorusSite _ (period_depth (n := n) fun _ => rfl) _
    · rfl
def freeBondEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n) :
    ↥(coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (coldFrame R n))) :=
  chartBondEquiv hcov hodd
def transferCoords (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) : StepVariable (finiteCells (coldFrame R n)) :=
  fun k => η ((freeBondEquiv hcov hodd V).symm k)
theorem transferCoords_apply (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free) :
    transferCoords hcov hodd V η (freeBondEquiv hcov hodd V b) = η b := by
  simp [transferCoords]
theorem stepCoordinates_transferCoords (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) (x : TorusSite (n * R.params.side))
    (i : Fin 4) (h : (x, i) ∈ (coldChartSetting R V).free) :
    stepCoordinates (transferCoords hcov hodd V η) (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x) i =
      toImaginary (η ⟨(x, i), h⟩) := by
  unfold stepCoordinates
  rw [dif_pos ((inFrame_mem_chordBonds_iff hcov hodd (x, i)).2 h)]
  exact congrArg toImaginary (transferCoords_apply hcov hodd V η ⟨(x, i), h⟩)
abbrev topField (V : TorusField n) : (coldFrame R n).GaugeField (coldFrame R n).top :=
  readAtLevel (coldFrame R n) (coldFrame R n).top V
theorem field_inFrame (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) :
    readAtLevel (coldFrame R n) (coldFrame R n).depth ((coldChartSetting R V).field η) =
      fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (transferCoords hcov hodd V η) := by
  have hlow : ∀ i, (coldFrame R n).period (coldFrame R n).depth i = n * R.params.side :=
    period_depth (H := coldFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * R.params.side),
      torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x = y :=
    ⟨_, inFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_inFrame (H := coldFrame R n) _ hlow ((coldChartSetting R V).field η) x i).trans ?_
  unfold fieldAboveFrame chartedField
  by_cases hb : (x, i) ∈ (coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := coldFrame R n)
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x, i) := fun h2 =>
      ((mem_chartBonds_iff (R := R) (x, i)).1 hb)
        ((isAxialTreeBond_inFrame_iff (H := coldFrame R n) (fun _ => rfl) x i).1 h2)
    have hfr : (coldChartSetting R V).frame (x, i) =
        ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
          (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x, i) (topField V) := rfl
    have hw : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (transferCoords hcov hodd V η) (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x) i =
        (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := by
      unfold coordsAboveFrame
      rw [stepCoordinates_transferCoords hcov hodd V η x i hb, hfr]
    have hcr : IsCrossingBond (F := levelFrame R n) (torusSiteInFrame (levelFrame R n) 0 x, i) ↔
        IsCrossingBond (F := coldFrame R n) (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x, i) :=
      (isCrossingBond_inFrame_iff (H := levelFrame R n) (fun _ => rfl) x i).trans
        (isCrossingBond_inFrame_iff (H := coldFrame R n) (fun _ => rfl) x i).symm
    have hcell : topField (R := R) V (enclosingCell (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x)) i =
        V (parentBlock R.params.side x) i := by
      have h0 : enclosingCell (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x) =
          torusSiteInFrame (coldFrame R n) (coldFrame R n).top (parentBlock R.params.side x) :=
        enclosingCell_inFrame (H := coldFrame R n) (n := n) (fun _ => rfl) x
      rw [h0]
      exact readAtLevel_inFrame _ (period_top (H := coldFrame R n) (n := n) fun _ => rfl) V _ i
    have hfield : (coldChartSetting R V).field η x i =
        chartLink (coldChartSetting R V) x i
          ((coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw]
    unfold chartLink
    have h1 : gaugeAt (R := R) (coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := coldFrame R n)
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x, i)
    · rw [if_pos (hcr.2 hc), if_pos hc, hcell]
      rfl
    · rw [if_neg (fun h => hc (hcr.1 h)), if_neg hc, if_neg htree]
  · have hfield : (coldChartSetting R V).field η x i = (coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsBlockTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_chartBonds_iff (R := R) (x, i)).2 h)
    have htree := (isAxialTreeBond_inFrame_iff (H := coldFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := coldFrame R n)
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Field
section Cost
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem stepHotLumps_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
omit [NeZero n] in
theorem torusHotSites_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem thickening_empty (m : ℕ) : thickening m (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
def blockFitValue (L : ℕ) (W : TorusField (n * L)) (V : TorusField n) (Y : TorusSite n) (i : Fin 4) : ℝ :=
  ‖blockContourAverage L W Y i‖ - (blockContourAverage L W Y i * ((V Y i)⁻¹ : UnitQuaternion)).re
omit [NeZero n] in
theorem blockFit_inFrame {H : BlockFrame} (hs : ∀ i, H.extent i = n) (W : TorusField (n * H.blockSide))
    (V : TorusField n) (Y : TorusSite n) (i : Fin 4) :
    blockFit (j := H.depth) (readAtLevel H H.depth W) (readAtLevel H H.top V)
      (torusSiteInFrame H H.top Y, i) = blockFitValue H.blockSide W V Y i := by
  unfold blockFit blockFitValue
  rw [contourAverage_inFrame hs]
  have h := readAtLevel_inFrame (H := H) H.top (period_top hs) V Y i
  simp only [h]
theorem meanNorm_of_cold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) (c : TorusBond n) :
    meanNorm ℓ W (fun y => cellCentre 0 y) c = ‖blockContourAverage ℓ.side W c.1 c.2‖ := by
  unfold meanNorm
  rw [stepHotLumps_eq_empty ℓ W hW]
  have h := contourMean_empty (H := stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  exact (congrArg norm h).trans
    (congrArg _ (contourAverage_inFrame (H := stepBlockFrame ℓ.side n) (fun _ => rfl) W c.1 c.2))
end Cost
section Sums
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem mem_sitesOfCells_top (z : (coldFrame R n).Cell) :
    z ∈ sitesOfCells (finiteCells (coldFrame R n)) (coldFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_sitesOfCells_top <;> assumption
theorem mem_innerBonds_top (c : (coldFrame R n).Site (coldFrame R n).top × Fin 4) :
    c ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_top <;> assumption
omit [NeZero n] in
theorem unitStep_ne_zero (hn : 2 ≤ n) (i : Fin 4) : TorusFields.unitStep n i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_ne_zero <;> assumption
omit [NeZero n] in
theorem unitStep_top_ne_zero (hn : 2 ≤ n) (i : Fin 4) :
    BlockAverages.unitStep (F := coldFrame R n) (coldFrame R n).top i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_top_ne_zero <;> assumption
open Classical in
theorem sum_bonds_at_cell (hn : 2 ≤ n) (g : (coldFrame R n).Site (coldFrame R n).top × Fin 4 → ℝ)
    (Y : (coldFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (coldFrame R n).top c.2 = Y), g c =
      ∑ i : Fin 4, (g (Y, i) + g (Y - BlockAverages.unitStep (coldFrame R n).top i, i)) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_touching <;> assumption
open Classical in
theorem sum_bonds_from_cell (g : (coldFrame R n).Site (coldFrame R n).top × Fin 4 → ℝ)
    (Y : (coldFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top).filter (fun c => c.1 = Y), g c =
      ∑ i : Fin 4, g (Y, i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_starting <;> assumption
open Classical in
theorem sum_sites_of_cell (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (coldFrame R n).Site (coldFrame R n).depth → ℝ) (Y : TorusSite n) :
    ∑ y ∈ (sitesOfCells (finiteCells (coldFrame R n)) (coldFrame R n).depth).filter
        (fun y => enclosingCell y = torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y), g y =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, g (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_sites_in_cell <;> assumption
theorem sum_finiteCells (g : (coldFrame R n).Cell → ℝ) :
    ∑ Z ∈ finiteCells (coldFrame R n), g Z =
      ∑ Y : TorusSite n, g (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_finiteCells <;> assumption
end Sums
section Read
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem inFrame_sub_unitStep (Y : TorusSite n) (i : Fin 4) :
    torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y - BlockAverages.unitStep (coldFrame R n).top i =
      torusSiteInFrame (coldFrame R n) (coldFrame R n).top (Y - TorusFields.unitStep n i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.torusSiteInFrame_sub_unitStep <;> assumption
theorem blockCost_eq_cellEnergyShare (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (hsh : ∀ y, levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      minimalSiteShare (F := coldFrame R n) R.params.coupling
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth y)
        (readAtLevel (coldFrame R n) (coldFrame R n).depth W))
    (V : TorusField n) (w : (coldFrame R n).Site (coldFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (hX : chartedField w (topField (R := R) V) = readAtLevel (coldFrame R n) (coldFrame R n).depth W)
    (Y : TorusSite n) :
    blockCost R.params R.depth W V (fun y => cellCentre 0 y) Y =
      cellEnergyShare R.params.coupling (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y) w
        (topField V) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.blockCost_eq_cellEnergyShare <;> assumption
end Read
section Pointwise
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem restrictToTorus_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) : restrictToTorus m (readAtLevel H j W) = W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.restrictToTorus_readAtLevel <;> assumption
omit [NeZero n] in
theorem localFamily_inFrame (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    localFamilyOfDensity g (coldFrame R n) (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x)
        (readAtLevel (coldFrame R n) (coldFrame R n).depth W) =
      g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.localFamilyOfDensity_readAtLevel <;> assumption
omit [NeZero n] in
theorem subtractTrivial_inFrame (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    ColdStepAtMirrorFrames.subtractTrivial (localFamilyOfDensity g) (coldFrame R n)
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth x)
        (readAtLevel (coldFrame R n) (coldFrame R n).depth W) = centered g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.subtractTrivial_readAtLevel <;> assumption
theorem isHullState_empty (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W) (r : ℕ) :
    IsHullState R.params r W ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.isHullState_empty <;> assumption
theorem blockDensityAt_eq (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (hrow : R.HasExpansions) (hn₀ : R.params.n₀ ≤ n) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free)
    (hW : IsCold R.params.threshold ((coldChartSetting R V).field η)) (Y : TorusSite n) :
    (coldChartSetting R V).blockDensityAt Y η =
      cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density)
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y) (transferCoords hcov hodd V η) (topField V) := by
  unfold cellCentredExpansion
  rw [sum_sites_of_cell hcov hodd]
  unfold ChartSetting.blockDensityAt ChartSetting.blockDensity
  refine Finset.sum_congr rfl fun x _ => ?_
  have hb : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Nat.dvd_mul_left _ _, by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hn₀⟩
  have h1 := hrow.2.empty (n * R.params.side) hb ((coldChartSetting R V).field η)
    (coldChartSetting R V).labelling x (isHullState_empty _ hW _)
  refine h1.trans ?_
  unfold centredExpansion
  rw [← field_inFrame hcov hodd V η]
  exact (subtractTrivial_inFrame R.density x _).symm
end Pointwise
section Context
open Filter Topology
structure ColdFieldBounds (R : StepSetup) (n : ℕ) [NeZero n] (lam : ℝ) (V : TorusField n) : Prop where
  hcov : BlocksCoverLowerLevel
  hodd : Odd R.params.side
  hn : 2 ≤ n
  ha : 0 ≤ R.params.coupling
  hn₀ : R.params.n₀ ≤ n
  hρ : 0 < R.ballRadius
  row : R.HasExpansions
  weyl : WeylIntegrationFormula
  sum : sumCellSharesEqAction
  fix : stepIntegralInFixedVariables
  cold : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) →
    IsCold R.params.threshold ((coldChartSetting R V).field η)
  share : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ y,
    levelShare R.params.coupling R.params.side R.depth Finset.univ y ((coldChartSetting R V).field η) =
      minimalSiteShare (F := coldFrame R n) R.params.coupling
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth y)
        (readAtLevel (coldFrame R n) (coldFrame R n).depth ((coldChartSetting R V).field η))
  frames : ∀ b ∈ chordBonds (finiteCells (coldFrame R n)),
    ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach b
      (topField (R := R) V)‖ + R.ballRadius < Real.pi
  count : ∀ Y, ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_toCoords (w : imaginaryQuaternions) : toImaginary (toCoords w) = w := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem coordNorm_eq (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := norm_toImaginary v
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_zero_pos <;> assumption
theorem haarRadialDensity_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < Real.pi) : 0 < haarRadialDensity u := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_pos <;> assumption
abbrev coordsOf (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (coldFrame R n).Site (coldFrame R n).depth → Fin 4 → imaginaryQuaternions :=
  coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
    (transferCoords c.hcov c.hodd V η)
theorem coordsOf_freeBond (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (b : ↥(coldChartSetting R V).free) :
    coordsOf c η (freeBondEquiv c.hcov c.hodd V b).1.1 (freeBondEquiv c.hcov c.hodd V b).1.2 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by
  unfold coordsOf coordsAboveFrame
  have h := stepCoordinates_transferCoords c.hcov c.hodd V η b.1.1 b.1.2 b.2
  have e : (freeBondEquiv c.hcov c.hodd V b).1 =
      (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth b.1.1, b.1.2) := rfl
  simp only [e]
  rw [h]
  rfl
theorem enclosingCell_freeBond_iff (c : ColdFieldBounds R n lam V) (b : ↥(coldChartSetting R V).free)
    (Y : TorusSite n) :
    enclosingCell (freeBondEquiv c.hcov c.hodd V b).1.1 =
        torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y ↔
      bondBlock (R := R) b.1 = Y := by
  have h0 : enclosingCell (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth b.1.1) =
      torusSiteInFrame (coldFrame R n) (coldFrame R n).top (parentBlock R.params.side b.1.1) :=
    enclosingCell_inFrame (H := coldFrame R n) (n := n) (fun _ => rfl) b.1.1
  show enclosingCell (torusSiteInFrame (coldFrame R n) (coldFrame R n).depth b.1.1) = _ ↔
    parentBlock R.params.side b.1.1 = Y
  rw [h0]
  exact (inFrame_injective _ (period_top (H := coldFrame R n) (n := n) fun _ => rfl)).eq_iff
theorem blockCostAt_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    (coldChartSetting R V).blockCostAt Y η =
      cellEnergyShare R.params.coupling (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y)
        (coordsOf c η) (topField V) :=
  blockCost_eq_cellEnergyShare c.hcov c.hodd c.hn _ (c.cold η hη) (c.share η hη) V (coordsOf c η)
    (field_inFrame c.hcov c.hodd V η).symm Y
theorem totalCost_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).totalCost η = chartedEnergy R.params.coupling (coordsOf c η) (topField V) := by
  have h := (c.sum (coldFrame R n) R.params.coupling (coordsOf c η) (topField V) c.ha c.hodd
    (fun _ => c.hn)).2
  rw [← h, sum_finiteCells]
  exact Finset.sum_congr rfl fun Y _ => blockCostAt_eq c η hη Y
theorem cutoffProduct_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (coldChartSetting R V).cutoffProduct η =
      cutoffWeight R.ballRadius R.barrierFn (transferCoords c.hcov c.hodd V η) := by
  unfold ChartSetting.cutoffProduct cutoffWeight
  rw [← Equiv.prod_comp (freeBondEquiv c.hcov c.hodd V)]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [transferCoords_apply]
  have h : coordNorm (η b) = ‖η b‖ := norm_toImaginary (η b)
  rw [h]
end Context
section Exponent
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
def blockConstant (R : StepSetup) : ℝ :=
  4 * logPartitionGap (R.params.coupling * R.coupling) +
    (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0)
theorem logPartitionGap_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) (i : Fin 4) :
    logPartitionGap (R.params.coupling * R.coupling *
        meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i)) =
      haarGapExcess R.params.coupling R.coupling
        (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
          (transferCoords c.hcov c.hodd V η))
        (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y, i) +
      logPartitionGap (R.params.coupling * R.coupling) := by
  have h1 : meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i) =
      ‖blockContourAverage R.params.side ((coldChartSetting R V).field η) Y i‖ :=
    meanNorm_of_cold R.params c.hodd _ (c.cold η hη) (Y, i)
  have h2 : _root_.YangMills.Construction.BlockAverages.contourAverage (j := (coldFrame R n).depth)
      (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (transferCoords c.hcov c.hodd V η))
      (torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y, i) =
        blockContourAverage R.params.side ((coldChartSetting R V).field η) Y i := by
    rw [← field_inFrame c.hcov c.hodd V η]
    exact contourAverage_inFrame (H := coldFrame R n) (n := n) (fun _ => rfl) _ Y i
  unfold haarGapExcess
  rw [h1, h2, c.weyl.2.2, c.weyl.2.2]
  ring
theorem log_haar_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (b : ↥(coldChartSetting R V).free) :
    Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) =
      haarLogRatio (coordsOf c η (freeBondEquiv c.hcov c.hodd V b).1.1
          (freeBondEquiv c.hcov c.hodd V b).1.2) +
        Real.log (haarRadialDensity 0) := by
  rw [coordsOf_freeBond]
  have h1 : ((coldChartSetting R V).frame b.1 + toImaginary (η b) : imaginaryQuaternions) =
      toImaginary (toCoords ((coldChartSetting R V).frame b.1) + η b) := by
    rw [toImaginary_add, toImaginary_toCoords]
  have h2 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ < Real.pi := by
    have h3 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ ≤
        ‖toCoords ((coldChartSetting R V).frame b.1)‖ + ‖η b‖ := norm_add_le _ _
    have h4 : ‖toCoords ((coldChartSetting R V).frame b.1)‖ = ‖(coldChartSetting R V).frame b.1‖ := by
      rw [← norm_toImaginary, toImaginary_toCoords]
    have h5 := c.frames _ (freeBondEquiv c.hcov c.hodd V b).2
    have h6 : ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
        (freeBondEquiv c.hcov c.hodd V b).1 (topField (R := R) V)‖ =
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
theorem logJacobianAt_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    (coldChartSetting R V).logJacobianAt Y η = blockConstant R +
      (∑ e ∈ (innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top).filter
          (fun e => e.1 = torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y),
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (transferCoords c.hcov c.hodd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (coldFrame R n))),
        if enclosingCell k.1.1 = torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y then
          haarLogRatio (coordsOf c η k.1.1 k.1.2) else 0 := by
  unfold ChartSetting.logJacobianAt ChartSetting.logJacobian
  rw [sum_bonds_from_cell, ← Equiv.sum_comp (freeBondEquiv c.hcov c.hodd V)]
  simp only [logPartitionGap_eq c η hη Y]
  rw [Finset.sum_add_distrib]
  have h2 : ∀ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then
        Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) else 0) =
      (if enclosingCell (freeBondEquiv c.hcov c.hodd V b).1.1 =
          torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y then
        haarLogRatio (coordsOf c η (freeBondEquiv c.hcov c.hodd V b).1.1
          (freeBondEquiv c.hcov c.hodd V b).1.2) else 0) +
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) := by
    intro b
    by_cases hb : bondBlock (R := R) b.1 = Y
    · rw [if_pos hb, if_pos hb, if_pos ((enclosingCell_freeBond_iff c b Y).2 hb), log_haar_eq c η hη]
    · rw [if_neg hb, if_neg hb, if_neg (fun h => hb ((enclosingCell_freeBond_iff c b Y).1 h))]
      simp
  have h3 : ∑ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) =
      (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := c.count Y
    unfold ChartSetting.freeBondsOf at this
    rw [this]
  simp only [h2]
  rw [Finset.sum_add_distrib, h3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold blockConstant
  push_cast
  ring
end Exponent
section Means
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
abbrev openBalls (R : StepSetup) (n : ℕ) : Set (StepVariable (finiteCells (coldFrame R n))) :=
  openBallProduct (coldFrame R n) R.ballRadius
theorem norm_lt_of_transfer_mem (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (h : transferCoords c.hcov c.hodd V η ∈ openBalls R n) : ∀ b, ‖η b‖ < R.ballRadius := by
  intro b
  have := h (freeBondEquiv c.hcov c.hodd V b)
  rwa [transferCoords_apply] at this
end Means
section Laws
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem integral_transferCoords (c : ColdFieldBounds R n lam V)
    (h : StepVariable (finiteCells (coldFrame R n)) → ℝ) :
    ∫ η : FreeCoords (coldChartSetting R V).free, h (transferCoords c.hcov c.hodd V η) = ∫ k, h k := by
  have mp := volume_measurePreserving_piCongrLeft
    (fun _ : ↥(chordBonds (finiteCells (coldFrame R n))) => EuclideanSpace ℝ (Fin 3))
    (freeBondEquiv c.hcov c.hodd V)
  have e : ∀ η : FreeCoords (coldChartSetting R V).free, transferCoords c.hcov c.hodd V η =
      (MeasurableEquiv.piCongrLeft
        (fun _ : ↥(chordBonds (finiteCells (coldFrame R n))) => EuclideanSpace ℝ (Fin 3))
        (freeBondEquiv c.hcov c.hodd V)) η := by
    intro η
    funext k
    obtain ⟨b, rfl⟩ := (freeBondEquiv c.hcov c.hodd V).surjective k
    rw [transferCoords_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp only [e]
  exact mp.integral_comp' h
theorem cutoffWeight_eq_zero (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (h : ¬ ∀ b, ‖η b‖ < R.ballRadius) :
    cutoffWeight R.ballRadius R.barrierFn (transferCoords c.hcov c.hodd V η) = 0 := by
  have h2 : transferCoords c.hcov c.hodd V η ∉ openBallProduct (coldFrame R n) R.ballRadius :=
    fun h2 => h (norm_lt_of_transfer_mem c η h2)
  unfold openBallProduct at h2
  simp only [Set.mem_setOf_eq, not_forall, not_lt] at h2
  obtain ⟨b, hb⟩ := h2
  unfold cutoffWeight
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold cutoffFactor
  rw [if_neg (not_lt.2 hb)]
end Laws
section Final
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
abbrev exponentAt (R : StepSetup) (n : ℕ) (ν : ℝ) (V : TorusField n) :
    StepVariable (finiteCells (coldFrame R n)) → ℝ :=
  stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
    (localFamilyOfDensity R.density) ν (topField V)
theorem sum_cellCentredExpansion (c : ColdFieldBounds R n lam V) (k : StepVariable (finiteCells (coldFrame R n))) :
    ∑ Z ∈ finiteCells (coldFrame R n),
        cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
          (localFamilyOfDensity R.density) Z k (topField V) =
      ∑ y ∈ sitesOfCells (finiteCells (coldFrame R n)) (coldFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach
          (localFamilyOfDensity R.density) y k (topField V) := by
  unfold cellCentredExpansion
  exact Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.SmallTorusImage.mem_finiteCells _) _
end Final
section Image
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
open Classical in
theorem sum_gap_fibres (g : (coldFrame R n).Site (coldFrame R n).top × Fin 4 → ℝ) :
    ∑ Y : TorusSite n, ∑ e ∈ (innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top).filter
        (fun e => e.1 = torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y), g e =
      ∑ e ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top, g e := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_by_cell <;> assumption
open Classical in
theorem sum_haar_fibres (h : ↥(chordBonds (finiteCells (coldFrame R n))) → ℝ) :
    ∑ Y : TorusSite n, ∑ k : ↥(chordBonds (finiteCells (coldFrame R n))),
        (if enclosingCell k.1.1 = torusSiteInFrame (coldFrame R n) (coldFrame R n).top Y then h k else 0) =
      ∑ k, h k := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_chordBonds_by_cell <;> assumption
theorem sum_blockConstant (c : ColdFieldBounds R n lam V) :
    ∑ _Y : TorusSite n, blockConstant R =
      (∑ _e ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top,
          haarGap (R.params.coupling * R.coupling)) +
        ∑ _k : ↥(chordBonds (finiteCells (coldFrame R n))), Real.log (haarRadialDensity 0) := by
  classical
  have h1 : ∑ _e ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top,
      haarGap (R.params.coupling * R.coupling) =
      ∑ _Y : TorusSite n, 4 * logPartitionGap (R.params.coupling * R.coupling) := by
    rw [← sum_gap_fibres (R := R) (n := n) fun _ => haarGap (R.params.coupling * R.coupling)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [sum_bonds_from_cell (R := R) (n := n) (fun _ => haarGap (R.params.coupling * R.coupling)),
      c.weyl.2.2]
    simp
  have h2 : ∑ _k : ↥(chordBonds (finiteCells (coldFrame R n))), Real.log (haarRadialDensity 0) =
      ∑ _Y : TorusSite n, (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0) := by
    rw [← Equiv.sum_comp (freeBondEquiv c.hcov c.hodd V) fun _ => Real.log (haarRadialDensity 0),
      ← Finset.sum_fiberwise Finset.univ (fun b : ↥(coldChartSetting R V).free => bondBlock (R := R) b.1)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    have := c.count Y
    unfold ChartSetting.freeBondsOf at this
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
  rw [h1, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => rfl
theorem potential_eq (c : ColdFieldBounds R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).potential η = exponentAt R n 1 V (transferCoords c.hcov c.hodd V η) +
      R.coupling * chartedEnergy R.params.coupling
        (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
        (topField (R := R) V) - ∑ _Y : TorusSite n, blockConstant R := by
  classical
  have h1 : ∑ Y : TorusSite n, blockCost R.params R.depth ((coldChartSetting R V).field η)
      (coldChartSetting R V).coarse (coldChartSetting R V).bases Y =
      chartedEnergy R.params.coupling (coordsOf c η) (topField V) := totalCost_eq c η hη
  have h2 : ∑ Y : TorusSite n, (coldChartSetting R V).blockDensity ((coldChartSetting R V).field η) Y =
      ∑ y ∈ sitesOfCells (finiteCells (coldFrame R n)) (coldFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) y
          (transferCoords c.hcov c.hodd V η) (topField V) := by
    rw [← sum_cellCentredExpansion c, sum_finiteCells]
    exact Finset.sum_congr rfl fun Y _ =>
      blockDensityAt_eq c.hcov c.hodd c.row c.hn₀ V η (c.cold η hη) Y
  have h3 : ∑ Y : TorusSite n, (coldChartSetting R V).logJacobian ((coldChartSetting R V).field η) η Y =
      (∑ _Y : TorusSite n, blockConstant R) +
      (∑ e ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top,
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (transferCoords c.hcov c.hodd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (coldFrame R n))), haarLogRatio (coordsOf c η k.1.1 k.1.2) := by
    rw [← sum_gap_fibres, ← sum_haar_fibres, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Y _ => logJacobianAt_eq c η hη Y
  unfold ChartSetting.potential
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3]
  unfold exponentAt stepExponent
  ring
theorem mul_exp_rearrange (r E x S G Lg : ℝ) :
    r * Real.exp (-(E + x * S - (G + Lg))) =
      Real.exp G * Real.exp Lg * Real.exp (- x * S) * (r * Real.exp (- E)) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mul_exp_rearrange <;> assumption
theorem integral_eq_coldStepIntegral (c : ColdFieldBounds R n lam V) :
    ∫ η, (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η) =
      coldStepIntegral R n V := by
  have hfix := c.fix (coldFrame R n) R.params.coupling R.anchorRadius R.ballRadius R.coupling R.frameReach
    R.barrierFn (localFamilyOfDensity R.density) (topField V) c.hodd
    (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) c.frames
  have hprod : (∏ _b : ↥(chordBonds (finiteCells (coldFrame R n))), haarRadialDensity 0) =
      Real.exp (∑ _b : ↥(chordBonds (finiteCells (coldFrame R n))), Real.log (haarRadialDensity 0)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun _ _ => (Real.exp_log haarRadialDensity_zero_pos).symm
  rw [hprod] at hfix
  let Cst : ℝ := Real.exp (∑ _c ∈ innerBonds (finiteCells (coldFrame R n)) (coldFrame R n).top,
      haarGap (R.params.coupling * R.coupling)) *
    Real.exp (∑ _b : ↥(chordBonds (finiteCells (coldFrame R n))), Real.log (haarRadialDensity 0)) *
    Real.exp (- R.coupling * chartedEnergy R.params.coupling
      (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
      (topField (R := R) V))
  let Fn : StepVariable (finiteCells (coldFrame R n)) → ℝ := fun k =>
    Cst * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- exponentAt R n 1 V k))
  have pt : ∀ η, (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η) =
      Fn (transferCoords c.hcov c.hodd V η) := by
    intro η
    simp only [Fn, Cst]
    rw [cutoffProduct_eq c]
    by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
    · rw [potential_eq c η hη, sum_blockConstant c]
      exact mul_exp_rearrange _ _ _ _ _ _
    · rw [cutoffWeight_eq_zero c η hη]
      simp
  refine (integral_congr_ae (Eventually.of_forall pt)).trans ((integral_transferCoords c Fn).trans ?_)
  simp only [Fn]
  rw [integral_const_mul]
  unfold coldStepIntegral
  exact hfix.symm
end Image
theorem card_freeBondsOf (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (hcount : ChartBondCountPerBlock) (hodd : Odd R.params.side) (hn : 2 ≤ n) (Y : TorusSite n) :
    ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.card_freeBondsOf <;> assumption
theorem norm_bondFrameCoord_le {F : BlockFrame} (a ρ : ℝ) (hρ : 0 ≤ ρ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) : ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by apply _root_.YangMills.Construction.LogJacobian.norm_bondFrameCoord_le <;> assumption
theorem coldImageIntegral_eq_on_small_torus_holds
    (hcold : Slope.ColdChartFieldIsColdOnSmallTorus)
    (hshare : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hcount : ChartBondCountPerBlock)
    (hweyl : WeylIntegrationFormula)
    (hsum : sumCellSharesEqAction) (hfix : stepIntegralInFixedVariables)
    (hcov : BlocksCoverLowerLevel) : coldImageIntegral_eq_on_small_torus := by
  intro T hT y hy R hR n _ hn hside V hV
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hcoldR : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) →
      IsCold T.threshold ((coldChartSetting R V).field η) := by
    intro η hη x μ ν hμ
    have h1 := hcold T hT y hy R hR n hn hside V hV η
      (fun b => (by simpa [coordNorm_eq] using (hη b).le)) x μ ν hμ
    linarith
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have h1 : ℓ = T.stepParameters y := hR.params_eq
  have h2 : ρA = T.ρA := hR.anchorRadius_eq
  have h3 : p = T.cutoff := hR.barrierFn_eq
  have hstep := hR.isStep
  subst h1 h2 h3
  set R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩ with hRdef
  have hL4 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hoddR : Odd R.params.side := hT.L_odd
  have hρA0 : 0 < T.ρA := hT.chain.2.2.2.1
  have hρA1 : T.ρA ≤ 1 := hT.chain.2.2.2.2.1
  have hσ1 : T.threshold ≤ 1 := hT.σ_one
  have c : ColdFieldBounds R n T.lam V :=
    { hcov := hcov
      hodd := hoddR
      hn := hn2
      ha := by have := hT.a_ge; show (0 : ℝ) ≤ T.coupling; linarith
      hn₀ := hn
      hρ := by show (0 : ℝ) < T.threshold / 64; positivity
      row := hstep.1
      weyl := hweyl
      sum := hsum
      fix := hfix
      cold := hcoldR
      share := fun η hη y' => hshare T hT t n hn _ (hcoldR η hη) y'
      frames := by
        intro b _
        have h5 : ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach b
            (topField (R := R) V)‖ ≤ T.ρA :=
          norm_bondFrameCoord_le _ _ hρA0.le _ _ _
        have h6 : R.ballRadius = T.threshold / 64 := rfl
        have h7 := Real.pi_gt_three
        linarith
      count := card_freeBondsOf R V hcount hoddR hn2 }
  unfold coldImageIntegral
  rw [integral_eq_coldStepIntegral c]
end SmallTorusImage
end YangMills.Construction
end
