import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.CostOfTheColdSettingInTheChart
import YangMills.Construction.LawByMomentsOfTheFlow.FieldOfTheColdGround
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ChartCostInCoordinates
theorem zmod_cast_intCast (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    TorusLumps.toTorusSite m (StepCosts.torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    StepCosts.torusSiteInFrame H j (TorusLumps.toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x + y) =
      StepCosts.torusSiteInFrame H j x + StepCosts.torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    StepCosts.torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (-x) = - StepCosts.torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x - y) =
      StepCosts.torusSiteInFrame H j x - StepCosts.torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusFields.TorusField m) : TorusFields.TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (i : Fin 4) :
    TorusFields.readAtLevel H j W (StepCosts.torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (l : List PathStep) :
    pathHolonomy (TorusFields.readAtLevel H j W) (StepCosts.torusSiteInFrame H j x) l =
      torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + StepCosts.torusSiteInFrame H j x =
        StepCosts.torusSiteInFrame H j
          (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [torusSiteInFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, torusSiteInFrame_neg j hm, torusSiteInFrame_unitStep j hm, add_comm]
      · simp [stepDisplacement, torusSiteInFrame_unitStep j hm, add_comm]
    simp only [pathHolonomy, torusPathHolonomy]
    rw [add_comm (StepCosts.torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm, readAtLevel_torusSiteInFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem zmod_cast_cast_int (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m)
    (x : TorusFields.TorusSite m) (k : Fin 4) :
    siteCoords (StepCosts.torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  zmod_cast_cast_int _ _ (hm k) (x k)
def torusBlockCentre (L : ℕ) (Y : TorusFields.TorusSite n) : TorusFields.TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_readAtLevel (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) :
    enclosingCell (StepCosts.torusSiteInFrame H H.depth x) =
      StepCosts.torusSiteInFrame H H.top (TorusLumps.parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.depth (period_depth hs) x k
  show ((((siteCoords (StepCosts.torusSiteInFrame H H.depth x) k +
    ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
    (H.blockSide : ℤ) ^ (H.top - H.depth) : ℤ)) : ZMod (H.period H.top k)) = _
  rw [h1, he, pow_one]
  exact (zmod_cast_intCast _ _ (period_top hs k) _).symm
theorem torusSiteInFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (StepCosts.torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_torusSiteInFrame j hm x, h, toTorusSite_torusSiteInFrame j hm y]
theorem isCrossingBond_iff (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsCrossingBond (F := H) (StepCosts.torusSiteInFrame H H.depth x, i) ↔
      TorusLumps.parentBlock H.blockSide (x + TorusFields.unitStep _ i) ≠ TorusLumps.parentBlock H.blockSide x := by
  unfold IsCrossingBond
  show enclosingCell (StepCosts.torusSiteInFrame H H.depth x + BlockAverages.unitStep H.depth i) ≠
    enclosingCell (StepCosts.torusSiteInFrame H H.depth x) ↔ _
  rw [← torusSiteInFrame_unitStep H.depth (period_depth hs), ← torusSiteInFrame_add H.depth (period_depth hs),
    enclosingCell_readAtLevel hs, enclosingCell_readAtLevel hs]
  exact not_congr (torusSiteInFrame_injective H.top (period_top hs)).eq_iff
theorem refineSite_readAtLevel (hs : ∀ i, H.extent i = n) (Y : TorusFields.TorusSite n) :
    refineSite (j := H.depth) (StepCosts.torusSiteInFrame H H.top Y) =
      StepCosts.torusSiteInFrame H H.depth (torusBlockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.refineSite_torusSiteInFrame <;> assumption
def torusBlockOffset (L : ℕ) (x : TorusFields.TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - torusBlockCentre L (TorusLumps.parentBlock L x)) k).valMinAbs
def IsTorusTreeBond (L : ℕ) (x : TorusFields.TorusSite (n * L)) (i : Fin 4) : Prop :=
  TorusLumps.parentBlock L (x + TorusFields.unitStep _ i) = TorusLumps.parentBlock L x ∧
    ∀ l, i < l → torusBlockOffset L x l = 0
theorem isAxialTreeBond_iff (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (StepCosts.torusSiteInFrame H H.depth x, i) ↔ IsTorusTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
def torusContourAverage (L : ℕ) (W : TorusFields.TorusField (n * L)) (Y : TorusFields.TorusSite n)
    (i : Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    ((torusPathHolonomy W (torusBlockCentre L Y) (bondContour L h π i) : UnitQuaternion) : ℍ[ℝ])
theorem contourAverage_readAtLevel (hs : ∀ i, H.extent i = n) (W : TorusFields.TorusField (n * H.blockSide))
    (Y : TorusFields.TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) (TorusFields.readAtLevel H H.depth W) (StepCosts.torusSiteInFrame H H.top Y, i) =
      torusContourAverage H.blockSide W Y i := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage torusContourAverage
  simp only [refineSite_readAtLevel hs, pathHolonomy_readAtLevel H.depth (period_depth hs)]
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem contourFit_of_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (V : H.GaugeField H.top) (c : H.Cell × Fin 4) :
    contourFit J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W V c =
      blockFit (j := H.depth) W V c := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.contourFit_of_no_lumps <;> assumption
end Plain
section Field
theorem pathHolonomy_trivial {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
abbrev chartFrame (R : StepSettings.StepSetup) (n : ℕ) : BlockFrame :=
  TorusFields.torusFrame R.params.side R.depth n
abbrev twoLevelFrame (R : StepSettings.StepSetup) (n : ℕ) : BlockFrame :=
  TorusLumps.stepBlockFrame R.params.side n
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusFields.TorusSite (n * R.params.side)) :
    StepSettings.gaugeAt (R := R) (TorusFields.trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_trivial _ _
theorem mem_chartBonds_iff (b : TorusFields.TorusBond (n * R.params.side)) :
    b ∈ StepCosts.chartBonds R.params.side n ↔ ¬ IsTorusTreeBond R.params.side b.1 b.2 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_chartBonds_iff <;> assumption
theorem mem_finiteCells (z : (chartFrame R n).Cell) : z ∈ finiteCells (chartFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells <;> assumption
theorem mem_innerBonds (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : (chartFrame R n).Site (chartFrame R n).depth × Fin 4) :
    b ∈ innerBonds (finiteCells (chartFrame R n)) (chartFrame R n).depth := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_depth <;> assumption
theorem mem_chordBonds_iff (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : TorusFields.TorusBond (n * R.params.side)) :
    (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth b.1, b.2) ∈
        chordBonds (finiteCells (chartFrame R n)) ↔
      b ∈ StepCosts.chartBonds R.params.side n := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.chordBonds_mem_iff <;> assumption
def chartBondEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) :
    ↥(StepCosts.chartBonds R.params.side n) ≃ ↥(chordBonds (finiteCells (chartFrame R n))) where
  toFun b := ⟨(StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth b.1.1, b.1.2),
    (mem_chordBonds_iff hcov hodd b.1).2 b.2⟩
  invFun k := ⟨(TorusLumps.toTorusSite (n * R.params.side) k.1.1, k.1.2), by
    rw [← mem_chordBonds_iff hcov hodd]
    have h : StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth
        (TorusLumps.toTorusSite (n * R.params.side) k.1.1) = k.1.1 :=
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
def freeBondEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusFields.TorusField n) :
    ↥(StepSettings.coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (chartFrame R n))) :=
  chartBondEquiv hcov hodd
def freeToStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free) :
    StepVariable (finiteCells (chartFrame R n)) :=
  fun k => η ((freeBondEquiv hcov hodd V).symm k)
theorem freeToStepVariable_apply (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free)
    (b : ↥(StepSettings.coldChartSetting R V).free) :
    freeToStepVariable hcov hodd V η (freeBondEquiv hcov hodd V b) = η b := by
  simp [freeToStepVariable]
theorem stepCoordinates_freeToStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free)
    (x : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4)
    (h : (x, i) ∈ (StepSettings.coldChartSetting R V).free) :
    stepCoordinates (freeToStepVariable hcov hodd V η)
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x) i =
      toImaginary (η ⟨(x, i), h⟩) := by
  unfold stepCoordinates
  rw [dif_pos ((mem_chordBonds_iff hcov hodd (x, i)).2 h)]
  exact congrArg toImaginary (freeToStepVariable_apply hcov hodd V η ⟨(x, i), h⟩)
abbrev topField (V : TorusFields.TorusField n) : (chartFrame R n).GaugeField (chartFrame R n).top :=
  TorusFields.readAtLevel (chartFrame R n) (chartFrame R n).top V
theorem field_readAtLevel (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free) :
    TorusFields.readAtLevel (chartFrame R n) (chartFrame R n).depth ((StepSettings.coldChartSetting R V).field η) =
      fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (freeToStepVariable hcov hodd V η) := by
  have hlow : ∀ i, (chartFrame R n).period (chartFrame R n).depth i = n * R.params.side :=
    period_depth (H := chartFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusFields.TorusSite (n * R.params.side),
      StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := chartFrame R n) _ hlow
    ((StepSettings.coldChartSetting R V).field η) x i).trans ?_
  unfold fieldAboveFrame chartedField
  by_cases hb : (x, i) ∈ (StepSettings.coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := chartFrame R n)
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x, i) := fun h2 =>
      ((mem_chartBonds_iff (R := R) (x, i)).1 hb)
        ((isAxialTreeBond_iff (H := chartFrame R n) (fun _ => rfl) x i).1 h2)
    have hfr : (StepSettings.coldChartSetting R V).frame (x, i) =
        ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
          (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x, i) (topField V) := rfl
    have hw : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (freeToStepVariable hcov hodd V η)
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x) i =
        (StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := by
      unfold coordsAboveFrame
      rw [stepCoordinates_freeToStepVariable hcov hodd V η x i hb, hfr]
    have hcr : IsCrossingBond (F := twoLevelFrame R n)
          (StepCosts.torusSiteInFrame (twoLevelFrame R n) 0 x, i) ↔
        IsCrossingBond (F := chartFrame R n)
          (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x, i) :=
      (isCrossingBond_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).trans
        (isCrossingBond_iff (H := chartFrame R n) (fun _ => rfl) x i).symm
    have hcell : topField (R := R) V
        (enclosingCell (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x)) i =
        V (TorusLumps.parentBlock R.params.side x) i := by
      have h0 : enclosingCell (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x) =
          StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top
            (TorusLumps.parentBlock R.params.side x) :=
        enclosingCell_readAtLevel (H := chartFrame R n) (n := n) (fun _ => rfl) x
      rw [h0]
      exact readAtLevel_torusSiteInFrame _ (period_top (H := chartFrame R n) (n := n) fun _ => rfl) V _ i
    have hfield : (StepSettings.coldChartSetting R V).field η x i =
        StepSettings.chartLink (StepSettings.coldChartSetting R V) x i
          ((StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw]
    unfold StepSettings.chartLink
    have h1 : StepSettings.gaugeAt (R := R) (StepSettings.coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := chartFrame R n)
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x, i)
    · rw [if_pos (hcr.2 hc), if_pos hc, hcell]
      rfl
    · rw [if_neg (fun h => hc (hcr.1 h)), if_neg hc, if_neg htree]
  · have hfield : (StepSettings.coldChartSetting R V).field η x i =
        (StepSettings.coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsTorusTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_chartBonds_iff (R := R) (x, i)).2 h)
    have htree := (isAxialTreeBond_iff (H := chartFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := chartFrame R n)
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Field
section Cost
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem stepHotLumps_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) :
    StepCosts.stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
omit [NeZero n] in
theorem torusHotSites_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) :
    TorusLumps.torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem thickening_empty (m : ℕ) : TorusLumps.thickening m (∅ : Finset (TorusFields.TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
def torusBondFit (L : ℕ) (W : TorusFields.TorusField (n * L)) (V : TorusFields.TorusField n)
    (Y : TorusFields.TorusSite n) (i : Fin 4) : ℝ :=
  ‖torusContourAverage L W Y i‖ - (torusContourAverage L W Y i * ((V Y i)⁻¹ : UnitQuaternion)).re
omit [NeZero n] in
theorem blockFit_readAtLevel {H : BlockFrame} (hs : ∀ i, H.extent i = n)
    (W : TorusFields.TorusField (n * H.blockSide)) (V : TorusFields.TorusField n)
    (Y : TorusFields.TorusSite n) (i : Fin 4) :
    blockFit (j := H.depth) (TorusFields.readAtLevel H H.depth W) (TorusFields.readAtLevel H H.top V)
        (StepCosts.torusSiteInFrame H H.top Y, i) = torusBondFit H.blockSide W V Y i := by
  unfold blockFit torusBondFit
  rw [contourAverage_readAtLevel hs]
  have h := readAtLevel_torusSiteInFrame (H := H) H.top (period_top hs) V Y i
  simp only [h]
end Cost
section Sums
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem mem_sitesOfCells_top (z : (chartFrame R n).Cell) :
    z ∈ sitesOfCells (finiteCells (chartFrame R n)) (chartFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_sitesOfCells_top <;> assumption
theorem mem_innerBonds_top (c : (chartFrame R n).Site (chartFrame R n).top × Fin 4) :
    c ∈ innerBonds (finiteCells (chartFrame R n)) (chartFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_top <;> assumption
omit [NeZero n] in
theorem unitStep_ne_zero (hn : 2 ≤ n) (i : Fin 4) : TorusFields.unitStep n i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_ne_zero <;> assumption
omit [NeZero n] in
theorem unitStep_top_ne_zero (hn : 2 ≤ n) (i : Fin 4) :
    BlockAverages.unitStep (F := chartFrame R n) (chartFrame R n).top i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_top_ne_zero <;> assumption
open Classical in
theorem sum_bonds_at_cell (hn : 2 ≤ n) (g : (chartFrame R n).Site (chartFrame R n).top × Fin 4 → ℝ)
    (Y : (chartFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (chartFrame R n)) (chartFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (chartFrame R n).top c.2 = Y), g c =
      ∑ i : Fin 4, (g (Y, i) + g (Y - BlockAverages.unitStep (chartFrame R n).top i, i)) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_touching <;> assumption
open Classical in
theorem sum_sites_of_cell (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (chartFrame R n).Site (chartFrame R n).depth → ℝ) (Y : TorusFields.TorusSite n) :
    ∑ y ∈ (sitesOfCells (finiteCells (chartFrame R n)) (chartFrame R n).depth).filter
        (fun y => enclosingCell y = StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top Y), g y =
      ∑ x ∈ TorusLumps.sitesInBlocks R.params.side {Y},
        g (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth x) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_sites_in_cell <;> assumption
theorem sum_finiteCells (g : (chartFrame R n).Cell → ℝ) :
    ∑ Z ∈ finiteCells (chartFrame R n), g Z =
      ∑ Y : TorusFields.TorusSite n, g (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_finiteCells <;> assumption
end Sums
section Read
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem torusSiteInFrame_sub_unitStep (Y : TorusFields.TorusSite n) (i : Fin 4) :
    StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top Y -
        BlockAverages.unitStep (chartFrame R n).top i =
      StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top (Y - TorusFields.unitStep n i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.torusSiteInFrame_sub_unitStep <;> assumption
theorem blockCost_eq_cellEnergyShare (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (W : TorusFields.TorusField (n * R.params.side)) (hW : TorusFields.IsCold R.params.threshold W)
    (hsh : ∀ y, StepCosts.levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      minimalSiteShare (F := chartFrame R n) R.params.coupling
        (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).depth y)
        (TorusFields.readAtLevel (chartFrame R n) (chartFrame R n).depth W))
    (V : TorusFields.TorusField n) (w : (chartFrame R n).Site (chartFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (hX : chartedField w (topField (R := R) V) = TorusFields.readAtLevel (chartFrame R n) (chartFrame R n).depth W)
    (Y : TorusFields.TorusSite n) :
    StepCosts.blockCost R.params R.depth W V (fun y => cellCentre 0 y) Y =
      cellEnergyShare R.params.coupling (StepCosts.torusSiteInFrame (chartFrame R n) (chartFrame R n).top Y) w
        (topField V) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.blockCost_eq_cellEnergyShare <;> assumption
end Read
section Norm
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : StepSettings.coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
end Norm
end ChartCostInCoordinates
namespace MomentLaw
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem field_same (hF : coldGroundFieldStatement) (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (V : TorusFields.TorusField n) (g : TorusFields.TorusBond (n * R.params.side) → BondVector) :
    (coldSettingOver R V).field (fun b => g b.1) =
      (StepSettings.coldChartSetting R V).field (fun b => g b.1) := by
  classical
  obtain ⟨-, -, h3, h4, h5⟩ := hF R n V hodd h2
  funext x i
  by_cases hb : (x, i) ∈ StepCosts.chartBonds R.params.side n
  · have hb' : (x, i) ∈ (coldSettingOver R V).free := by rw [h3]; exact hb
    have e := h4 (fun b => g b.1) ⟨(x, i), hb'⟩
    simp only at e
    rw [e]
    have hR : (StepSettings.coldChartSetting R V).field (fun b => g b.1) x i =
        StepSettings.chartLink (StepSettings.coldChartSetting R V) x i
          ((StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (g (x, i))) := dif_pos hb
    rw [hR]
    unfold StepSettings.chartLink
    have h1 : StepSettings.gaugeAt (R := R) (StepSettings.coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => ChartCostInCoordinates.gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    rfl
  · have hb' : (x, i) ∉ (coldSettingOver R V).free := by rw [h3]; exact hb
    rw [h5 _ (x, i) hb']
    have hR : (StepSettings.coldChartSetting R V).field (fun b => g b.1) x i =
        (StepSettings.coldChartSetting R V).fine x i := dif_neg hb
    rw [hR]
    rfl
private theorem cost_core (hsum : sumCellSharesEqAction) (hcov : BlocksCoverLowerLevel)
    (hF : coldGroundFieldStatement) (hoddR : Odd R.params.side) (hn2 : 2 ≤ n) (ha : 0 ≤ R.params.coupling)
    (V : TorusFields.TorusField n)
    (k : BondField (ChartBondIndex R.params.side R.depth n)) (hk : ∀ b, ‖k b‖ < R.ballRadius)
    (hcoldR : ∀ η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free,
      (∀ b, ‖η b‖ < R.ballRadius) →
      TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η))
    (hsh : ∀ W : TorusFields.TorusField (n * R.params.side), TorusFields.IsCold R.params.threshold W → ∀ y,
      StepCosts.levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      minimalSiteShare (F := ChartCostInCoordinates.chartFrame R n) R.params.coupling
        (StepCosts.torusSiteInFrame (ChartCostInCoordinates.chartFrame R n) (ChartCostInCoordinates.chartFrame R n).depth y)
        (TorusFields.readAtLevel (ChartCostInCoordinates.chartFrame R n) (ChartCostInCoordinates.chartFrame R n).depth W)) :
    ∑ Y : TorusFields.TorusSite n, (coldSettingOver R V).blockCostAt Y (chartFreeCoords R R.depth V k) =
      chartedEnergyAt R.params.coupling
        (frameCoordField false R.params.coupling R.anchorRadius R.frameReach
          (TorusFields.readAtLevel (TorusFields.torusFrame R.params.side R.depth n)
            (TorusFields.torusFrame R.params.side R.depth n).top V))
        (TorusFields.readAtLevel (TorusFields.torusFrame R.params.side R.depth n)
          (TorusFields.torusFrame R.params.side R.depth n).top V) k := by
  classical
  set g : TorusFields.TorusBond (n * R.params.side) → BondVector := fun c =>
    ∑ c' : ChartBondIndex R.params.side R.depth n,
      if (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
        (TorusFields.torusFrame R.params.side R.depth n).depth c.1, c.2) = c'.1 then k c' else 0 with hg
  set η' : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free := fun b => g b.1 with hη'
  have hcf : chartFreeCoords R R.depth V k = fun b => g b.1 := rfl
  have htrv : ChartCostInCoordinates.freeToStepVariable hcov hoddR V η' = k := by
    funext κ
    show g (TorusLumps.toTorusSite (n * R.params.side) κ.1.1, κ.1.2) = k κ
    simp only [hg]
    have e : StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
        (TorusFields.torusFrame R.params.side R.depth n).depth
        (TorusLumps.toTorusSite (n * R.params.side) κ.1.1) = κ.1.1 :=
      ChartCostInCoordinates.torusSiteInFrame_toTorusSite _
        (ChartCostInCoordinates.period_depth (H := ChartCostInCoordinates.chartFrame R n) (n := n) fun _ => rfl) _
    rw [Finset.sum_eq_single κ]
    · rw [if_pos]
      rw [e]
    · intro c _ hne
      rw [if_neg]
      intro h
      rw [e] at h
      exact hne (Subtype.ext h.symm)
    · simp
  have hball : ∀ b, ‖η' b‖ < R.ballRadius := by
    intro b
    have e := ChartCostInCoordinates.freeToStepVariable_apply hcov hoddR V η' b
    rw [htrv] at e
    rw [← e]
    exact hk _
  have hW := hcoldR η' hball
  have hfield := field_same hF hoddR hn2 V g
  obtain ⟨hs, -⟩ := hF R n V hoddR hn2
  have hVs : (coldSettingOver R V).coarse = V := by rw [hs]; rfl
  have hBs : (coldSettingOver R V).bases = fun y => cellCentre 0 y := by rw [hs]; rfl
  set w : (ChartCostInCoordinates.chartFrame R n).Site (ChartCostInCoordinates.chartFrame R n).depth → Fin 4 →
      imaginaryQuaternions :=
    coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach
      (ChartCostInCoordinates.topField (R := R) V) k with hw
  have hX : chartedField w (ChartCostInCoordinates.topField (R := R) V) =
      TorusFields.readAtLevel (ChartCostInCoordinates.chartFrame R n) (ChartCostInCoordinates.chartFrame R n).depth
        ((StepSettings.coldChartSetting R V).field η') := by
    have e := ChartCostInCoordinates.field_readAtLevel hcov hoddR V η'
    rw [htrv] at e
    exact e.symm
  have hcost : ∀ Y : TorusFields.TorusSite n,
      (coldSettingOver R V).blockCostAt Y (chartFreeCoords R R.depth V k) =
      cellEnergyShare R.params.coupling
        (StepCosts.torusSiteInFrame (ChartCostInCoordinates.chartFrame R n) (ChartCostInCoordinates.chartFrame R n).top Y) w
        (ChartCostInCoordinates.topField V) := by
    intro Y
    unfold StepSettings.ChartSetting.blockCostAt
    rw [hcf, hfield, hVs, hBs]
    exact ChartCostInCoordinates.blockCost_eq_cellEnergyShare hcov hoddR hn2 _ hW (fun y' => hsh _ hW y') V w hX Y
  have hall := (hsum (ChartCostInCoordinates.chartFrame R n) R.params.coupling w
    (ChartCostInCoordinates.topField (R := R) V) ha hoddR (fun _ => hn2)).2
  have e2 : chartedEnergyAt R.params.coupling
      (frameCoordField false R.params.coupling R.anchorRadius R.frameReach
        (TorusFields.readAtLevel (TorusFields.torusFrame R.params.side R.depth n)
          (TorusFields.torusFrame R.params.side R.depth n).top V))
      (TorusFields.readAtLevel (TorusFields.torusFrame R.params.side R.depth n)
        (TorusFields.torusFrame R.params.side R.depth n).top V) k =
      chartedEnergy R.params.coupling w (ChartCostInCoordinates.topField (R := R) V) := rfl
  rw [e2, ← hall, ChartCostInCoordinates.sum_finiteCells]
  exact Finset.sum_congr rfl fun Y _ => hcost Y
theorem coldSettingChartCost_holds (hcold : StepSettings.ColdChartSettingIsCold)
    (hshare : ShareEvaluation.LevelShareEqMinimalSiteShare) (hsum : sumCellSharesEqAction)
    (hcov : BlocksCoverLowerLevel) (hF : coldGroundFieldStatement) :
    coldSettingChartCostStatement := by
  classical
  intro T hT
  obtain ⟨y₁, hy₁⟩ := hcold T hT
  refine ⟨y₁, fun y hy R hR n _ hn V hV u hu k hk => ?_⟩
  subst hu
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hl : R.params = T.stepParameters y := hR.params_eq
  have hσe : R.params.threshold = T.threshold := by rw [hl]; rfl
  have hL4 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hoddR : Odd R.params.side := by rw [hl]; exact hT.L_odd
  have ha : (0 : ℝ) ≤ R.params.coupling := by
    rw [hl]
    exact zero_le_one.trans hT.a_ge
  have hcoldR : ∀ η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free,
      (∀ b, ‖η b‖ < R.ballRadius) →
      TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η) := by
    intro η hη x μ ν hμ
    have h1 := hy₁ y hy R hR n hn V hV η
      (fun b => (by simpa [ChartCostInCoordinates.coordNorm_eq_norm] using (hη b).le)) x μ ν hμ
    rw [hσe]
    linarith
  refine cost_core hsum hcov hF hoddR hn2 ha V k hk hcoldR ?_
  clear hcoldR hk k hoddR ha hσe
  obtain ⟨params, depth, c, c', F, dens, labs, lw, clus, sd, ra, bar⟩ := R
  have h1 : params = T.stepParameters y := hR.params_eq
  subst h1
  intro W hW y'
  exact hshare T hT depth n hn W hW y'
end MomentLaw
end YangMills.Construction
end
