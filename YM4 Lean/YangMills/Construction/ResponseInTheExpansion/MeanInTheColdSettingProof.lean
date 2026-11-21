import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlockProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields TorusLumps StepCosts StepSettings RenormalizationStepParameters ColdStepAtMirrorFrames
namespace StepSettings
namespace ColdChartMeans
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
      torusPathHolonomy W (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (l : List PathStep) :
    pathHolonomy (readAtLevel H j W) (torusSiteInFrame H j x) l = torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + torusSiteInFrame H j x =
        torusSiteInFrame H j (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
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
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm, readAtLevel_torusSiteInFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem cast_cast_int_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m)
    (k : Fin 4) : siteCoords (torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  cast_cast_int_of_eq _ _ (hm k) (x k)
def blockCentre (L : ℕ) (Y : TorusSite n) : TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    enclosingCell (torusSiteInFrame H H.depth x) = torusSiteInFrame H H.top (parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.depth (period_depth hs) x k
  show ((((siteCoords (torusSiteInFrame H H.depth x) k + ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
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
  rw [← torusSiteInFrame_unitStep H.depth (period_depth hs), ← torusSiteInFrame_add H.depth (period_depth hs),
    enclosingCell_torusSiteInFrame hs, enclosingCell_torusSiteInFrame hs]
  exact not_congr (torusSiteInFrame_injective H.top (period_top hs)).eq_iff
theorem cellCentre_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusSite n) :
    cellCentre H.depth (torusSiteInFrame H H.top Y) = torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellCentre_torusSiteInFrame <;> assumption
theorem refineSite_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusSite n) :
    refineSite (j := H.depth) (torusSiteInFrame H H.top Y) = torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.refineSite_torusSiteInFrame <;> assumption
theorem valMinAbs_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P))).valMinAbs = a.valMinAbs := by
  subst h; simp
def blockOffset (L : ℕ) (x : TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - blockCentre L (parentBlock L x)) k).valMinAbs
theorem cellOffset_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    cellOffset (torusSiteInFrame H H.depth x) = blockOffset H.blockSide x := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellOffset_torusSiteInFrame <;> assumption
def IsBlockTreeBond (L : ℕ) (x : TorusSite (n * L)) (i : Fin 4) : Prop :=
  parentBlock L (x + TorusFields.unitStep _ i) = parentBlock L x ∧ ∀ l, i < l → blockOffset L x l = 0
theorem isAxialTreeBond_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (torusSiteInFrame H H.depth x, i) ↔ IsBlockTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
def blockContourMean (L : ℕ) (W : TorusField (n * L)) (Y : TorusSite n) (i : Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    ((torusPathHolonomy W (blockCentre L Y) (bondContour L h π i) : UnitQuaternion) : ℍ[ℝ])
theorem contourAverage_readAtLevel (hs : ∀ i, H.extent i = n) (W : TorusField (n * H.blockSide))
    (Y : TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) (readAtLevel H H.depth W) (torusSiteInFrame H H.top Y, i) =
      blockContourMean H.blockSide W Y i := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage blockContourMean
  simp only [refineSite_torusSiteInFrame hs, pathHolonomy_readAtLevel H.depth (period_depth hs)]
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem contourMean_of_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    LumpContours.contourMean J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) W c := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.contourMean_empty <;> assumption
theorem contourFit_of_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (V : H.GaugeField H.top) (c : H.Cell × Fin 4) :
    contourFit J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W V c =
      blockFit (j := H.depth) W V c := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.contourFit_of_no_lumps <;> assumption
end Plain
section Field
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev coarseFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
abbrev twoLevelFrame (R : StepSetup) (n : ℕ) : BlockFrame := stepBlockFrame R.params.side n
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
theorem mem_chartBonds_iff (b : TorusBond (n * R.params.side)) :
    b ∈ StepCosts.chartBonds R.params.side n ↔ ¬ IsBlockTreeBond R.params.side b.1 b.2 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_chartBonds_iff <;> assumption
theorem mem_finiteCells (z : (coarseFrame R n).Cell) : z ∈ finiteCells (coarseFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells <;> assumption
theorem mem_innerBonds_depth (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : (coarseFrame R n).Site (coarseFrame R n).depth × Fin 4) :
    b ∈ innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).depth := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_depth <;> assumption
theorem mem_chordBonds_iff (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : TorusBond (n * R.params.side)) :
    (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth b.1, b.2) ∈
        chordBonds (finiteCells (coarseFrame R n)) ↔
      b ∈ StepCosts.chartBonds R.params.side n := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.chordBonds_mem_iff <;> assumption
def chartBondsEquivChordBonds (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) :
    ↥(StepCosts.chartBonds R.params.side n) ≃ ↥(chordBonds (finiteCells (coarseFrame R n))) where
  toFun b := ⟨(torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth b.1.1, b.1.2),
    (mem_chordBonds_iff hcov hodd b.1).2 b.2⟩
  invFun k := ⟨(toTorusSite (n * R.params.side) k.1.1, k.1.2), by
    rw [← mem_chordBonds_iff hcov hodd]
    have h : torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth
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
def freeBondsEquivChordBonds (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) :
    ↥(coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (coarseFrame R n))) :=
  chartBondsEquivChordBonds hcov hodd
def toStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) : StepVariable (finiteCells (coarseFrame R n)) :=
  fun k => η ((freeBondsEquivChordBonds hcov hodd V).symm k)
theorem toStepVariable_apply (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free) :
    toStepVariable hcov hodd V η (freeBondsEquivChordBonds hcov hodd V b) = η b := by
  simp [toStepVariable]
theorem stepCoordinates_toStepVariable (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) (x : TorusSite (n * R.params.side))
    (i : Fin 4) (h : (x, i) ∈ (coldChartSetting R V).free) :
    stepCoordinates (toStepVariable hcov hodd V η) (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x) i =
      toImaginary (η ⟨(x, i), h⟩) := by
  unfold stepCoordinates
  rw [dif_pos ((mem_chordBonds_iff hcov hodd (x, i)).2 h)]
  exact congrArg toImaginary (toStepVariable_apply hcov hodd V η ⟨(x, i), h⟩)
abbrev topField (V : TorusField n) : (coarseFrame R n).GaugeField (coarseFrame R n).top :=
  readAtLevel (coarseFrame R n) (coarseFrame R n).top V
theorem readAtLevel_field (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) :
    readAtLevel (coarseFrame R n) (coarseFrame R n).depth ((coldChartSetting R V).field η) =
      fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable hcov hodd V η) := by
  have hlow : ∀ i, (coarseFrame R n).period (coarseFrame R n).depth i = n * R.params.side :=
    period_depth (H := coarseFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * R.params.side),
      torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := coarseFrame R n) _ hlow ((coldChartSetting R V).field η) x i).trans ?_
  unfold fieldAboveFrame chartedField
  by_cases hb : (x, i) ∈ (coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := coarseFrame R n)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x, i) := fun h2 =>
      ((mem_chartBonds_iff (R := R) (x, i)).1 hb) ((isAxialTreeBond_iff (H := coarseFrame R n) (fun _ => rfl) x i).1 h2)
    have hfr : (coldChartSetting R V).frame (x, i) =
        ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
          (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x, i) (topField V) := rfl
    have hw : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable hcov hodd V η)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x) i =
        (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := by
      unfold coordsAboveFrame
      rw [stepCoordinates_toStepVariable hcov hodd V η x i hb, hfr]
    have hcr : IsCrossingBond (F := twoLevelFrame R n) (torusSiteInFrame (twoLevelFrame R n) 0 x, i) ↔
        IsCrossingBond (F := coarseFrame R n) (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x, i) :=
      (isCrossingBond_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).trans
        (isCrossingBond_iff (H := coarseFrame R n) (fun _ => rfl) x i).symm
    have hcell : topField (R := R) V
        (enclosingCell (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x)) i =
        V (parentBlock R.params.side x) i := by
      have h0 : enclosingCell (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x) =
          torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top (parentBlock R.params.side x) :=
        enclosingCell_torusSiteInFrame (H := coarseFrame R n) (n := n) (fun _ => rfl) x
      rw [h0]
      exact readAtLevel_torusSiteInFrame _ (period_top (H := coarseFrame R n) (n := n) fun _ => rfl) V _ i
    have hfield : (coldChartSetting R V).field η x i =
        chartLink (coldChartSetting R V) x i
          ((coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw]
    unfold chartLink
    have h1 : gaugeAt (R := R) (coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := coarseFrame R n)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x, i)
    · rw [if_pos (hcr.2 hc), if_pos hc, hcell]
      rfl
    · rw [if_neg (fun h => hc (hcr.1 h)), if_neg hc, if_neg htree]
  · have hfield : (coldChartSetting R V).field η x i = (coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsBlockTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_chartBonds_iff (R := R) (x, i)).2 h)
    have htree := (isAxialTreeBond_iff (H := coarseFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := coarseFrame R n)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Field
section Cost
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem plaquetteDefect_readAtLevel_eq_curvature {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p = TorusFields.curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
omit [NeZero n] in
theorem stepHotLumps_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
omit [NeZero n] in
theorem torusHotSites_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem thickening_empty (m : ℕ) : thickening m (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
def blockContourFit (L : ℕ) (W : TorusField (n * L)) (V : TorusField n) (Y : TorusSite n) (i : Fin 4) : ℝ :=
  ‖blockContourMean L W Y i‖ - (blockContourMean L W Y i * ((V Y i)⁻¹ : UnitQuaternion)).re
omit [NeZero n] in
theorem blockFit_readAtLevel {H : BlockFrame} (hs : ∀ i, H.extent i = n) (W : TorusField (n * H.blockSide))
    (V : TorusField n) (Y : TorusSite n) (i : Fin 4) :
    blockFit (j := H.depth) (readAtLevel H H.depth W) (readAtLevel H H.top V) (torusSiteInFrame H H.top Y, i) =
      blockContourFit H.blockSide W V Y i := by
  unfold blockFit blockContourFit
  rw [contourAverage_readAtLevel hs]
  have h := readAtLevel_torusSiteInFrame (H := H) H.top (period_top hs) V Y i
  simp only [h]
theorem bondFit_of_isCold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) (V : TorusField n) (c : TorusBond n) :
    bondFit ℓ W V (fun y => cellCentre 0 y) c = blockContourFit ℓ.side W V c.1 c.2 := by
  unfold bondFit
  rw [stepHotLumps_eq_empty ℓ W hW]
  have h := contourFit_of_no_lumps (H := stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  refine h.trans ?_
  exact blockFit_readAtLevel (H := stepBlockFrame ℓ.side n) (fun _ => rfl) W V c.1 c.2
theorem meanNorm_of_isCold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) (c : TorusBond n) :
    meanNorm ℓ W (fun y => cellCentre 0 y) c = ‖blockContourMean ℓ.side W c.1 c.2‖ := by
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
theorem mem_sitesOfCells_top (z : (coarseFrame R n).Cell) :
    z ∈ sitesOfCells (finiteCells (coarseFrame R n)) (coarseFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_sitesOfCells_top <;> assumption
theorem mem_innerBonds_top (c : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4) :
    c ∈ innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_top <;> assumption
omit [NeZero n] in
theorem unitStep_ne_zero (hn : 2 ≤ n) (i : Fin 4) : TorusFields.unitStep n i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_ne_zero <;> assumption
omit [NeZero n] in
theorem unitStep_top_ne_zero (hn : 2 ≤ n) (i : Fin 4) :
    BlockAverages.unitStep (F := coarseFrame R n) (coarseFrame R n).top i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_top_ne_zero <;> assumption
open Classical in
theorem sum_bonds_touching (hn : 2 ≤ n) (g : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4 → ℝ)
    (Y : (coarseFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (coarseFrame R n).top c.2 = Y), g c =
      ∑ i : Fin 4, (g (Y, i) + g (Y - BlockAverages.unitStep (coarseFrame R n).top i, i)) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_touching <;> assumption
open Classical in
theorem sum_bonds_at (g : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4 → ℝ)
    (Y : (coarseFrame R n).Cell) :
    ∑ c ∈ (innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top).filter (fun c => c.1 = Y), g c =
      ∑ i : Fin 4, g (Y, i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_starting <;> assumption
open Classical in
theorem sum_sites_in_cell (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (coarseFrame R n).Site (coarseFrame R n).depth → ℝ) (Y : TorusSite n) :
    ∑ y ∈ (sitesOfCells (finiteCells (coarseFrame R n)) (coarseFrame R n).depth).filter
        (fun y => enclosingCell y = torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y), g y =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, g (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_sites_in_cell <;> assumption
theorem sum_finiteCells (g : (coarseFrame R n).Cell → ℝ) :
    ∑ Z ∈ finiteCells (coarseFrame R n), g Z =
      ∑ Y : TorusSite n, g (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_finiteCells <;> assumption
end Sums
section Read
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem torusSiteInFrame_sub_unitStep (Y : TorusSite n) (i : Fin 4) :
    torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y - BlockAverages.unitStep (coarseFrame R n).top i =
      torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top (Y - TorusFields.unitStep n i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.torusSiteInFrame_sub_unitStep <;> assumption
theorem blockCost_eq_cellEnergyShare (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (hsh : ∀ y, levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      minimalSiteShare (F := coarseFrame R n) R.params.coupling
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth y)
        (readAtLevel (coarseFrame R n) (coarseFrame R n).depth W))
    (V : TorusField n) (w : (coarseFrame R n).Site (coarseFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (hX : chartedField w (topField (R := R) V) = readAtLevel (coarseFrame R n) (coarseFrame R n).depth W)
    (Y : TorusSite n) :
    blockCost R.params R.depth W V (fun y => cellCentre 0 y) Y =
      cellEnergyShare R.params.coupling (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y) w
        (topField V) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.blockCost_eq_cellEnergyShare <;> assumption
end Read
section Pointwise
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem restrictToTorus_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) : restrictToTorus m (readAtLevel H j W) = W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.restrictToTorus_readAtLevel <;> assumption
omit [NeZero n] in
theorem localFamilyOfDensity_readAtLevel (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    localFamilyOfDensity g (coarseFrame R n) (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x)
        (readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) =
      g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.localFamilyOfDensity_readAtLevel <;> assumption
omit [NeZero n] in
theorem subtractTrivial_readAtLevel (g : LocalDensity) (x : TorusSite (n * R.params.side))
    (W : TorusField (n * R.params.side)) :
    subtractTrivial (localFamilyOfDensity g) (coarseFrame R n)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x)
        (readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) = centered g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.subtractTrivial_readAtLevel <;> assumption
theorem isHullState_empty (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W) (r : ℕ) :
    IsHullState R.params r W ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.isHullState_empty <;> assumption
theorem blockDensityAt_eq_cellCentredExpansion (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (hrow : R.HasExpansions) (hn₀ : R.params.n₀ ≤ n) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free)
    (hW : IsCold R.params.threshold ((coldChartSetting R V).field η)) (Y : TorusSite n) :
    (coldChartSetting R V).blockDensityAt Y η =
      cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density)
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y)
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
  shares : sumCellSharesEqAction
  cold : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) →
    IsCold R.params.threshold ((coldChartSetting R V).field η)
  share_eq : ∀ η : FreeCoords (coldChartSetting R V).free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ y,
    levelShare R.params.coupling R.params.side R.depth Finset.univ y ((coldChartSetting R V).field η) =
      minimalSiteShare (F := coarseFrame R n) R.params.coupling
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth y)
        (readAtLevel (coarseFrame R n) (coarseFrame R n).depth ((coldChartSetting R V).field η))
  frame_norm_lt : ∀ b ∈ chordBonds (finiteCells (coarseFrame R n)),
    ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach b
      (topField (R := R) V)‖ + R.ballRadius < Real.pi
  freeBonds_card : ∀ Y, ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side
  regular : ∃ M, IsRegularStep R.params.coupling R.anchorRadius R.ballRadius lam R.coupling M R.frameReach
    R.barrierFn (localFamilyOfDensity R.density) (topField (R := R) V)
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_toCoords (w : imaginaryQuaternions) : toImaginary (toCoords w) = w := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem coordNorm_eq (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := norm_toImaginary v
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_zero_pos <;> assumption
theorem haarRadialDensity_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < Real.pi) : 0 < haarRadialDensity u := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_pos <;> assumption
abbrev coldCoords (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (coarseFrame R n).Site (coarseFrame R n).depth → Fin 4 → imaginaryQuaternions :=
  coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
    (toStepVariable c.cover c.side_odd V η)
theorem coldCoords_bond (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (b : ↥(coldChartSetting R V).free) :
    coldCoords c η (freeBondsEquivChordBonds c.cover c.side_odd V b).1.1
        (freeBondsEquivChordBonds c.cover c.side_odd V b).1.2 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by
  unfold coldCoords coordsAboveFrame
  have h := stepCoordinates_toStepVariable c.cover c.side_odd V η b.1.1 b.1.2 b.2
  have e : (freeBondsEquivChordBonds c.cover c.side_odd V b).1 =
      (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth b.1.1, b.1.2) := rfl
  simp only [e]
  rw [h]
  rfl
theorem enclosingCell_eq_iff (c : ColdTopData R n lam V) (b : ↥(coldChartSetting R V).free) (Y : TorusSite n) :
    enclosingCell (freeBondsEquivChordBonds c.cover c.side_odd V b).1.1 =
        torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y ↔
      bondBlock (R := R) b.1 = Y := by
  have h0 : enclosingCell (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth b.1.1) =
      torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top (parentBlock R.params.side b.1.1) :=
    enclosingCell_torusSiteInFrame (H := coarseFrame R n) (n := n) (fun _ => rfl) b.1.1
  show enclosingCell (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth b.1.1) = _ ↔
    parentBlock R.params.side b.1.1 = Y
  rw [h0]
  exact (torusSiteInFrame_injective _ (period_top (H := coarseFrame R n) (n := n) fun _ => rfl)).eq_iff
theorem blockCostAt_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) :
    (coldChartSetting R V).blockCostAt Y η =
      cellEnergyShare R.params.coupling (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y)
        (coldCoords c η) (topField V) :=
  blockCost_eq_cellEnergyShare c.cover c.side_odd c.two_le _ (c.cold η hη) (c.share_eq η hη) V (coldCoords c η)
    (readAtLevel_field c.cover c.side_odd V η).symm Y
theorem totalCost_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).totalCost η = chartedEnergy R.params.coupling (coldCoords c η) (topField V) := by
  have h := (c.shares (coarseFrame R n) R.params.coupling (coldCoords c η) (topField V) c.coupling_nonneg
    c.side_odd (fun _ => c.two_le)).2
  rw [← h, sum_finiteCells]
  exact Finset.sum_congr rfl fun Y _ => blockCostAt_eq c η hη Y
theorem cutoffProduct_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free) :
    (coldChartSetting R V).cutoffProduct η =
      cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) := by
  unfold ChartSetting.cutoffProduct cutoffWeight
  rw [← Equiv.prod_comp (freeBondsEquivChordBonds c.cover c.side_odd V)]
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
theorem logPartitionGap_meanNorm_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (Y : TorusSite n) (i : Fin 4) :
    logPartitionGap (R.params.coupling * R.coupling *
        meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i)) =
      haarGapExcess R.params.coupling R.coupling
        (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
          (toStepVariable c.cover c.side_odd V η))
        (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y, i) +
        logPartitionGap (R.params.coupling * R.coupling) := by
  have h1 : meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases (Y, i) =
      ‖blockContourMean R.params.side ((coldChartSetting R V).field η) Y i‖ :=
    meanNorm_of_isCold R.params c.side_odd _ (c.cold η hη) (Y, i)
  have h2 : _root_.YangMills.Construction.BlockAverages.contourAverage (j := (coarseFrame R n).depth)
      (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
        (toStepVariable c.cover c.side_odd V η))
      (torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y, i) =
        blockContourMean R.params.side ((coldChartSetting R V).field η) Y i := by
    rw [← readAtLevel_field c.cover c.side_odd V η]
    exact contourAverage_readAtLevel (H := coarseFrame R n) (n := n) (fun _ => rfl) _ Y i
  unfold haarGapExcess
  rw [h1, h2, c.weyl.2.2, c.weyl.2.2]
  ring
theorem log_haarLogDensity_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) (b : ↥(coldChartSetting R V).free) :
    Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) =
      haarLogRatio (coldCoords c η (freeBondsEquivChordBonds c.cover c.side_odd V b).1.1
          (freeBondsEquivChordBonds c.cover c.side_odd V b).1.2) +
        Real.log (haarRadialDensity 0) := by
  rw [coldCoords_bond]
  have h1 : ((coldChartSetting R V).frame b.1 + toImaginary (η b) : imaginaryQuaternions) =
      toImaginary (toCoords ((coldChartSetting R V).frame b.1) + η b) := by
    rw [toImaginary_add, toImaginary_toCoords]
  have h2 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ < Real.pi := by
    have h3 : ‖toCoords ((coldChartSetting R V).frame b.1) + η b‖ ≤
        ‖toCoords ((coldChartSetting R V).frame b.1)‖ + ‖η b‖ := norm_add_le _ _
    have h4 : ‖toCoords ((coldChartSetting R V).frame b.1)‖ = ‖(coldChartSetting R V).frame b.1‖ := by
      rw [← norm_toImaginary, toImaginary_toCoords]
    have h5 := c.frame_norm_lt _ (freeBondsEquivChordBonds c.cover c.side_odd V b).2
    have h6 : ‖ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
        (freeBondsEquivChordBonds c.cover c.side_odd V b).1 (topField (R := R) V)‖ =
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
      (∑ e ∈ (innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top).filter
          (fun e => e.1 = torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y),
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (toStepVariable c.cover c.side_odd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (coarseFrame R n))),
        if enclosingCell k.1.1 = torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y then
          haarLogRatio (coldCoords c η k.1.1 k.1.2) else 0 := by
  unfold ChartSetting.logJacobianAt ChartSetting.logJacobian
  rw [sum_bonds_at, ← Equiv.sum_comp (freeBondsEquivChordBonds c.cover c.side_odd V)]
  simp only [logPartitionGap_meanNorm_eq c η hη Y]
  rw [Finset.sum_add_distrib]
  have h2 : ∀ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then
        Real.log (haarLogDensity (toCoords ((coldChartSetting R V).frame b.1) + η b)) else 0) =
      (if enclosingCell (freeBondsEquivChordBonds c.cover c.side_odd V b).1.1 =
          torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y then
        haarLogRatio (coldCoords c η (freeBondsEquivChordBonds c.cover c.side_odd V b).1.1
          (freeBondsEquivChordBonds c.cover c.side_odd V b).1.2) else 0) +
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) := by
    intro b
    by_cases hb : bondBlock (R := R) b.1 = Y
    · rw [if_pos hb, if_pos hb, if_pos ((enclosingCell_eq_iff c b Y).2 hb), log_haarLogDensity_eq c η hη]
    · rw [if_neg hb, if_neg hb, if_neg (fun h => hb ((enclosingCell_eq_iff c b Y).1 h))]
      simp
  have h3 : ∑ b : ↥(coldChartSetting R V).free,
      (if bondBlock (R := R) b.1 = Y then Real.log (haarRadialDensity 0) else 0) =
      (chartBondCount R.params.side : ℝ) * Real.log (haarRadialDensity 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := c.freeBonds_card Y
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
abbrev ballSet (R : StepSetup) (n : ℕ) : Set (StepVariable (finiteCells (coarseFrame R n))) :=
  openBallProduct (coarseFrame R n) R.ballRadius
theorem norm_lt_of_toStepVariable_mem (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (h : toStepVariable c.cover c.side_odd V η ∈ ballSet R n) : ∀ b, ‖η b‖ < R.ballRadius := by
  intro b
  have := h (freeBondsEquivChordBonds c.cover c.side_odd V b)
  rwa [toStepVariable_apply] at this
end Means
section Laws
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem integral_toStepVariable (c : ColdTopData R n lam V) (h : StepVariable (finiteCells (coarseFrame R n)) → ℝ) :
    ∫ η : FreeCoords (coldChartSetting R V).free, h (toStepVariable c.cover c.side_odd V η) = ∫ k, h k := by
  have mp := volume_measurePreserving_piCongrLeft
    (fun _ : ↥(chordBonds (finiteCells (coarseFrame R n))) => EuclideanSpace ℝ (Fin 3))
    (freeBondsEquivChordBonds c.cover c.side_odd V)
  have e : ∀ η : FreeCoords (coldChartSetting R V).free, toStepVariable c.cover c.side_odd V η =
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(chordBonds (finiteCells (coarseFrame R n))) =>
        EuclideanSpace ℝ (Fin 3)) (freeBondsEquivChordBonds c.cover c.side_odd V)) η := by
    intro η
    funext k
    obtain ⟨b, rfl⟩ := (freeBondsEquivChordBonds c.cover c.side_odd V).surjective k
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
end Regular
end Laws
section Final
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
abbrev coldExponent (R : StepSetup) (n : ℕ) (ν : ℝ) (V : TorusField n) :
    StepVariable (finiteCells (coarseFrame R n)) → ℝ :=
  stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
    (localFamilyOfDensity R.density) ν (topField V)
theorem sum_cellCentredExpansion (c : ColdTopData R n lam V) (k : StepVariable (finiteCells (coarseFrame R n))) :
    ∑ Z ∈ finiteCells (coarseFrame R n),
        cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) Z k
          (topField V) =
      ∑ y ∈ sitesOfCells (finiteCells (coarseFrame R n)) (coarseFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) y k
          (topField V) := by
  unfold cellCentredExpansion
  exact Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.StepSettings.ColdChartMeans.mem_finiteCells _) _
end Final
section Image
open Filter Topology
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
open Classical in
theorem sum_bonds_by_cell (g : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4 → ℝ) :
    ∑ Y : TorusSite n, ∑ e ∈ (innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top).filter
        (fun e => e.1 = torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y), g e =
      ∑ e ∈ innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top, g e := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_by_cell <;> assumption
open Classical in
theorem sum_chordBonds_by_cell (h : ↥(chordBonds (finiteCells (coarseFrame R n))) → ℝ) :
    ∑ Y : TorusSite n, ∑ k : ↥(chordBonds (finiteCells (coarseFrame R n))),
        (if enclosingCell k.1.1 = torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y then h k else 0) =
      ∑ k, h k := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_chordBonds_by_cell <;> assumption
theorem potential_eq (c : ColdTopData R n lam V) (η : FreeCoords (coldChartSetting R V).free)
    (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).potential η = coldExponent R n 1 V (toStepVariable c.cover c.side_odd V η) +
      R.coupling * chartedEnergy R.params.coupling
        (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
        (topField (R := R) V) - ∑ _Y : TorusSite n, blockConstant R := by
  classical
  have h1 : ∑ Y : TorusSite n, blockCost R.params R.depth ((coldChartSetting R V).field η)
      (coldChartSetting R V).coarse (coldChartSetting R V).bases Y =
      chartedEnergy R.params.coupling (coldCoords c η) (topField V) := totalCost_eq c η hη
  have h2 : ∑ Y : TorusSite n, (coldChartSetting R V).blockDensity ((coldChartSetting R V).field η) Y =
      ∑ y ∈ sitesOfCells (finiteCells (coarseFrame R n)) (coarseFrame R n).depth,
        centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) y
          (toStepVariable c.cover c.side_odd V η) (topField V) := by
    rw [← sum_cellCentredExpansion c, sum_finiteCells]
    exact Finset.sum_congr rfl fun Y _ =>
      blockDensityAt_eq_cellCentredExpansion c.cover c.side_odd c.expansions c.n₀_le V η (c.cold η hη) Y
  have h3 : ∑ Y : TorusSite n, (coldChartSetting R V).logJacobian ((coldChartSetting R V).field η) η Y =
      (∑ _Y : TorusSite n, blockConstant R) +
      (∑ e ∈ innerBonds (finiteCells (coarseFrame R n)) (coarseFrame R n).top,
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField V)
            (toStepVariable c.cover c.side_odd V η)) e) +
      ∑ k : ↥(chordBonds (finiteCells (coarseFrame R n))), haarLogRatio (coldCoords c η k.1.1 k.1.2) := by
    rw [← sum_bonds_by_cell, ← sum_chordBonds_by_cell, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Y _ => logJacobianAt_eq c η hη Y
  unfold ChartSetting.potential
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3]
  unfold coldExponent stepExponent
  ring
end Image
theorem card_freeBondsOf (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (hcount : ChartBondCountPerBlock) (hodd : Odd R.params.side) (hn : 2 ≤ n) (Y : TorusSite n) :
    ((coldChartSetting R V).freeBondsOf Y).card = chartBondCount R.params.side := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.card_freeBondsOf <;> assumption
end ColdChartMeans
namespace ColdChartMeans
open Interpolation
section Frames
variable {F : BlockFrame} (a ρA x : ℝ) (m : ℕ) (W : F.GaugeField F.top) (k : StepVariable (finiteCells F))
theorem interpolatedField_one : interpolatedField 1 a ρA m W k = fieldAboveFrame false a ρA m W k := by apply _root_.YangMills.SharedProofs.p24311 <;> assumption
theorem familyLawExponent_one (f : LocalFamily) :
    familyLawExponent 1 a ρA x m f W k = stepExponent false a ρA x m f 1 W k := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BlockImageOfOne.familyLawExponent_one <;> assumption
end Frames
variable {R : StepSetup} {n : ℕ} [NeZero n] {lam : ℝ} {V : TorusField n}
theorem coldFieldAboveFrames_toStepVariable (c : ColdTopData R n lam V)
    (η : FreeCoords (coldChartSetting R V).free) :
    ResponseInTheExpansion.coldFieldAboveFrames R V (toStepVariable c.cover c.side_odd V η) =
      (coldChartSetting R V).field η := by
  unfold ResponseInTheExpansion.coldFieldAboveFrames
  rw [interpolatedField_one]
  rw [show fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)
      (toStepVariable c.cover c.side_odd V η) =
        readAtLevel (coarseFrame R n) (coarseFrame R n).depth ((coldChartSetting R V).field η) from
    (readAtLevel_field c.cover c.side_odd V η).symm]
  exact restrictToTorus_readAtLevel (period_depth (H := coarseFrame R n) (n := n) fun _ => rfl) _
theorem weightedMean_eq_coldStepMean (c : ColdTopData R n lam V) (G : TorusField (n * R.params.side) → ℝ) :
    weightedMean (WeightedResponses.chartDensity (coldChartSetting R V))
        (fun η => G ((coldChartSetting R V).field η)) =
      ResponseInTheExpansion.coldStepMean R V fun k => G (ResponseInTheExpansion.coldFieldAboveFrames R V k) := by
  obtain ⟨M, hreg⟩ := c.regular
  set Cst : ℝ := Real.exp (-(R.coupling * chartedEnergy R.params.coupling
      (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
      (topField (R := R) V) - ∑ _Y : TorusSite n, blockConstant R)) with hCst
  have hC : Cst ≠ 0 := (Real.exp_pos _).ne'
  have pt : ∀ η, WeightedResponses.chartDensity (coldChartSetting R V) η =
      Cst * (cutoffWeight R.ballRadius R.barrierFn (toStepVariable c.cover c.side_odd V η) *
        Real.exp (- coldExponent R n 1 V (toStepVariable c.cover c.side_odd V η))) := by
    intro η
    unfold WeightedResponses.chartDensity
    rw [cutoffProduct_eq c]
    by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
    · rw [potential_eq c η hη, hCst]
      rw [show -(coldExponent R n 1 V (toStepVariable c.cover c.side_odd V η) +
            R.coupling * chartedEnergy R.params.coupling
              (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
              (topField (R := R) V) -
            ∑ _Y : TorusSite n, blockConstant R) =
          -(R.coupling * chartedEnergy R.params.coupling
              (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topField (R := R) V) 0)
              (topField (R := R) V) -
            ∑ _Y : TorusSite n, blockConstant R) +
            - coldExponent R n 1 V (toStepVariable c.cover c.side_odd V η) by ring, Real.exp_add]
      ring
    · rw [cutoffWeight_toStepVariable_eq_zero hreg c η hη]
      simp
  have hw : ∀ H : StepVariable (finiteCells (coarseFrame R n)) → ℝ,
      ∫ η, H (toStepVariable c.cover c.side_odd V η) * WeightedResponses.chartDensity (coldChartSetting R V) η =
        Cst * ∫ k, H k * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- coldExponent R n 1 V k)) := by
    intro H
    have pt' : ∀ η, H (toStepVariable c.cover c.side_odd V η) *
          WeightedResponses.chartDensity (coldChartSetting R V) η =
        (fun k => Cst * (H k * (cutoffWeight R.ballRadius R.barrierFn k * Real.exp (- coldExponent R n 1 V k))))
          (toStepVariable c.cover c.side_odd V η) := by
      intro η
      simp only
      rw [pt η]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall pt')).trans
      ((integral_toStepVariable c (fun k => Cst * (H k * (cutoffWeight R.ballRadius R.barrierFn k *
        Real.exp (- coldExponent R n 1 V k))))).trans ?_)
    rw [integral_const_mul]
  have h1 := hw fun k => G (ResponseInTheExpansion.coldFieldAboveFrames R V k)
  have h2 := hw fun _ => 1
  simp only [coldFieldAboveFrames_toStepVariable c, one_mul] at h1 h2
  have e : familyLawExponent 1 R.params.coupling R.anchorRadius R.coupling R.frameReach
      (localFamilyOfDensity R.density)
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) =
        coldExponent R n 1 V :=
    funext fun k => familyLawExponent_one _ _ _ _ _ _ _
  unfold weightedMean ResponseInTheExpansion.coldStepMean cutoffMean
  rw [e, h1, h2]
  exact mul_div_mul_left _ _ hC
end ColdChartMeans
end StepSettings
namespace ResponseInTheExpansion
open StepSettings.ColdChartMeans in
theorem coldSettingMeanEqStepMean_holds (hcold : ColdChartSettingIsCold)
    (hshare : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hcount : ChartBondCountPerBlock)
    (hrow : ColdExpansionRegular) (hweyl : WeylIntegrationFormula)
    (hsum : sumCellSharesEqAction)
    (hcov : BlocksCoverLowerLevel) : coldSettingMeanEqStepMean := by
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
    rw [plaquetteDefect_readAtLevel_eq_curvature (period_top (H := coarseFrame R n) (n := n) fun _ => rfl)]
    exact hV _ _ _ hq
  have htop : IsCubicTopTorus T.side t T.n₀ (coarseFrame R n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  obtain ⟨hfr, M, hreg⟩ := hden.regular (coarseFrame R n) htop (topField (R := R) V) hcoldV
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
      shares := hsum
      cold := hcoldR
      share_eq := fun η hη y' => hshare T hT t n hn _ (hcoldR η hη) y'
      frame_norm_lt := hfr
      freeBonds_card := card_freeBondsOf R V hcount hoddR hn2
      regular := ⟨M, hreg⟩ }
  intro G
  exact weightedMean_eq_coldStepMean c G
end ResponseInTheExpansion
end YangMills.Construction
end
