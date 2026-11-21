import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.ResponseInTheExpansion.ColdLawOfAStepIsALaw
import YangMills.Construction.ResponseInTheExpansion.ContinuousFromThreeDerivatives
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses
namespace YangMills.Construction
namespace TorusFrameTransfer
theorem intCast_cast_intCast_of_eq (P m : ℕ) (h : P = m) (z : ℤ) :
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
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem intCast_cast_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m)
    (k : Fin 4) : siteCoords (torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  intCast_cast_cast_of_eq _ _ (hm k) (x k)
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
  exact (intCast_cast_intCast_of_eq _ _ (period_top hs k) _).symm
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
def blockOffset (L : ℕ) (x : TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - blockCentre L (parentBlock L x)) k).valMinAbs
theorem cellOffset_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    cellOffset (torusSiteInFrame H H.depth x) = blockOffset H.blockSide x := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellOffset_torusSiteInFrame <;> assumption
def IsBlockTreeBond (L : ℕ) (x : TorusSite (n * L)) (i : Fin 4) : Prop :=
  parentBlock L (x + TorusFields.unitStep _ i) = parentBlock L x ∧ ∀ l, i < l → blockOffset L x l = 0
theorem isAxialTreeBond_iff (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (torusSiteInFrame H H.depth x, i) ↔ IsBlockTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
end Blocks
section Field
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    BlockAverages.pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev stepTopFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
abbrev twoLevelFrame (R : StepSetup) (n : ℕ) : BlockFrame := stepBlockFrame R.params.side n
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
theorem mem_chartBonds_iff (b : TorusBond (n * R.params.side)) :
    b ∈ chartBonds R.params.side n ↔ ¬ IsBlockTreeBond R.params.side b.1 b.2 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_chartBonds_iff <;> assumption
theorem mem_finiteCells (z : (stepTopFrame R n).Cell) : z ∈ finiteCells (stepTopFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells <;> assumption
theorem mem_innerBonds (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : (stepTopFrame R n).Site (stepTopFrame R n).depth × Fin 4) :
    b ∈ innerBonds (finiteCells (stepTopFrame R n)) (stepTopFrame R n).depth := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_depth <;> assumption
theorem mem_chordBonds_iff (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (b : TorusBond (n * R.params.side)) :
    (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth b.1, b.2) ∈
        chordBonds (finiteCells (stepTopFrame R n)) ↔
      b ∈ chartBonds R.params.side n := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.chordBonds_mem_iff <;> assumption
def chartBondsEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) :
    ↥(chartBonds R.params.side n) ≃ ↥(chordBonds (finiteCells (stepTopFrame R n))) where
  toFun b := ⟨(torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth b.1.1, b.1.2),
    (mem_chordBonds_iff hcov hodd b.1).2 b.2⟩
  invFun k := ⟨(toTorusSite (n * R.params.side) k.1.1, k.1.2), by
    rw [← mem_chordBonds_iff hcov hodd]
    have h : torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth
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
def freeBondsEquiv (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n) :
    ↥(coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (stepTopFrame R n))) :=
  chartBondsEquiv hcov hodd
def freeToStep (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) : StepVariable (finiteCells (stepTopFrame R n)) :=
  fun k => η ((freeBondsEquiv hcov hodd V).symm k)
theorem freeToStep_apply (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free) :
    freeToStep hcov hodd V η (freeBondsEquiv hcov hodd V b) = η b := by
  simp [freeToStep]
theorem stepCoordinates_freeToStep (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) (x : TorusSite (n * R.params.side))
    (i : Fin 4) (h : (x, i) ∈ (coldChartSetting R V).free) :
    stepCoordinates (freeToStep hcov hodd V η) (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x) i =
      toImaginary (η ⟨(x, i), h⟩) := by
  unfold stepCoordinates
  rw [dif_pos ((mem_chordBonds_iff hcov hodd (x, i)).2 h)]
  exact congrArg toImaginary (freeToStep_apply hcov hodd V η ⟨(x, i), h⟩)
abbrev topLevelField (V : TorusField n) : (stepTopFrame R n).GaugeField (stepTopFrame R n).top :=
  readAtLevel (stepTopFrame R n) (stepTopFrame R n).top V
theorem readAtLevel_field (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free) :
    readAtLevel (stepTopFrame R n) (stepTopFrame R n).depth ((coldChartSetting R V).field η) =
      fieldAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topLevelField V)
        (freeToStep hcov hodd V η) := by
  have hlow : ∀ i, (stepTopFrame R n).period (stepTopFrame R n).depth i = n * R.params.side :=
    period_depth (H := stepTopFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * R.params.side),
      torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := stepTopFrame R n) _ hlow ((coldChartSetting R V).field η) x i).trans ?_
  unfold fieldAboveFrame chartedField
  by_cases hb : (x, i) ∈ (coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := stepTopFrame R n)
        (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x, i) := fun h2 =>
      ((mem_chartBonds_iff (R := R) (x, i)).1 hb)
        ((isAxialTreeBond_iff (H := stepTopFrame R n) (fun _ => rfl) x i).1 h2)
    have hfr : (coldChartSetting R V).frame (x, i) =
        ColdStepAtMirrorFrames.stepFrame false R.params.coupling R.anchorRadius R.frameReach
          (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x, i) (topLevelField V) := rfl
    have hw : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach (topLevelField V)
        (freeToStep hcov hodd V η) (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x) i =
        (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := by
      unfold coordsAboveFrame
      rw [stepCoordinates_freeToStep hcov hodd V η x i hb, hfr]
    have hcr : IsCrossingBond (F := twoLevelFrame R n) (torusSiteInFrame (twoLevelFrame R n) 0 x, i) ↔
        IsCrossingBond (F := stepTopFrame R n)
          (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x, i) :=
      (isCrossingBond_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).trans
        (isCrossingBond_iff (H := stepTopFrame R n) (fun _ => rfl) x i).symm
    have hcell : topLevelField (R := R) V
        (enclosingCell (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x)) i =
        V (parentBlock R.params.side x) i := by
      have h0 : enclosingCell (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x) =
          torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).top (parentBlock R.params.side x) :=
        enclosingCell_torusSiteInFrame (H := stepTopFrame R n) (n := n) (fun _ => rfl) x
      rw [h0]
      exact readAtLevel_torusSiteInFrame _ (period_top (H := stepTopFrame R n) (n := n) fun _ => rfl) V _ i
    have hfield : (coldChartSetting R V).field η x i =
        chartLink (coldChartSetting R V) x i
          ((coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw]
    unfold chartLink
    have h1 : gaugeAt (R := R) (coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := stepTopFrame R n)
        (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x, i)
    · rw [if_pos (hcr.2 hc), if_pos hc, hcell]
      rfl
    · rw [if_neg (fun h => hc (hcr.1 h)), if_neg hc, if_neg htree]
  · have hfield : (coldChartSetting R V).field η x i = (coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsBlockTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_chartBonds_iff (R := R) (x, i)).2 h)
    have htree := (isAxialTreeBond_iff (H := stepTopFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := stepTopFrame R n)
        (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Field
theorem plaquetteDefect_readAtLevel_eq {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p = TorusFields.curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
theorem restrictToTorus_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) : restrictToTorus m (readAtLevel H j W) = W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.restrictToTorus_readAtLevel <;> assumption
theorem toImaginary_norm (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem coordNorm_eq (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := toImaginary_norm v
theorem continuous_toImaginary : Continuous toImaginary := by apply _root_.YangMills.Construction.StepCostLocality.continuous_toImaginary <;> assumption
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
section Sum
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
theorem sum_cell_fiber_eq (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (stepTopFrame R n).Site (stepTopFrame R n).depth → ℝ) (Y : TorusSite n) :
    ∑ y ∈ (sitesOfCells (finiteCells (stepTopFrame R n)) (stepTopFrame R n).depth).filter
        (fun y => enclosingCell y = torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).top Y), g y =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, g (torusSiteInFrame (stepTopFrame R n) (stepTopFrame R n).depth x) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_sites_in_cell <;> assumption
end Sum
section Law
open YangMills.Construction.Dilation
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isBallLaw_of_bounded {ρ B : ℝ} {r : ℝ → ℝ} {Ψ Ψ' : BondField ι → ℝ}
    (hnn : ∀ η : BondField ι, 0 ≤ radialWeightProd r η) (hint : Integrable (radialWeightProd (ι := ι) r))
    (hpos : 0 < ∫ η : BondField ι, radialWeightProd r η)
    (hsupp : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → radialWeightProd r η = 0)
    (hc : ContinuousOn Ψ' {η | ∀ b, ‖η b‖ < ρ}) (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |Ψ' η| ≤ B)
    (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Ψ η = Ψ' η) : IsBallLaw ρ r Ψ := by
  have e0 : ∀ η, ballDensity r (fun _ : BondField ι => 0) η = radialWeightProd r η := fun η => by
    simp [ballDensity]
  have L0 : IsBallLaw ρ r (fun _ : BondField ι => 0) :=
    ⟨fun η => by rw [e0]; exact hnn η, by simpa only [funext e0] using hint,
      by simpa only [funext e0] using hpos, fun η h => by rw [e0]; exact hsupp η h⟩
  have hcx : ContinuousOn (fun η => Real.exp (- Ψ' η)) {η : BondField ι | ∀ b, ‖η b‖ < ρ} :=
    Real.continuous_exp.comp_continuousOn hc.neg
  have hbx : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |Real.exp (- Ψ' η)| ≤ Real.exp B := fun η h => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [neg_le_of_abs_le (hb η h)])
  have hI := integrable_mul_density_of_bounded L0 hcx hbx
  have ed : ∀ η, Real.exp (- Ψ' η) * ballDensity r (fun _ : BondField ι => 0) η = ballDensity r Ψ η :=
    fun η => by
      by_cases h : ∀ b, ‖η b‖ < ρ
      · rw [e0, ballDensity, he η h, mul_comm]
      · rw [e0, ballDensity, hsupp η h]
        simp
  have hI' : Integrable (ballDensity r Ψ) := hI.congr (Eventually.of_forall ed)
  refine ⟨fun η => mul_nonneg (hnn η) (Real.exp_pos _).le, hI', ?_, fun η h => ?_⟩
  · have hle : ∀ η, Real.exp (-B) * radialWeightProd r η ≤ ballDensity r Ψ η := fun η => by
      by_cases h : ∀ b, ‖η b‖ < ρ
      · rw [ballDensity, he η h, mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [le_of_abs_le (hb η h)])) (hnn η)
      · rw [ballDensity, hsupp η h]
        simp
    have h1 := integral_mono (hint.const_mul _) hI' hle
    rw [integral_const_mul] at h1
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hpos) h1
  · rw [ballDensity, hsupp η h, zero_mul]
end Law
end TorusFrameTransfer
namespace ResponseInTheExpansion
open TorusFrameTransfer
theorem coldHalfLawIsLaw (hcold : ColdChartSettingIsCold) (hrow : ColdExpansionRegular)
    (hcov : BlocksCoverLowerLevel) (hends : interpolationAtEndpoints)
    (hc3 : ContinuousAtOfContDiffThreeAt) :
    coldHalfLawIsLawStatement := by
  intro T hT hC
  obtain ⟨y₁, hy₁⟩ := hcold T hT
  refine ⟨max y₁ (max T.yC T.floorMin), fun y hy R hR n _ hn V hV => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyC : T.yC ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy0 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hcs := hy₁ y hy1 R hR n hn V hV
  obtain ⟨cn, nss, hties, hall⟩ := hC
  obtain ⟨-, -, e_ρ, -, -, -, -, -⟩ := hties
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
  have hcoldV : IsSmallCurvature (9 / 8 * T.threshold) (topLevelField (R := R) V) := by
    intro q hq
    rw [plaquetteDefect_readAtLevel_eq (period_top (H := stepTopFrame R n) (n := n) fun _ => rfl)]
    exact hV _ _ _ hq
  have htop : IsCubicTopTorus T.side t T.n₀ (stepTopFrame R n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  obtain ⟨hfr, M, hreg⟩ := hden.regular (stepTopFrame R n) htop (topLevelField (R := R) V) hcoldV
  rw [show (T.stepParamsAt cn nss y).chainParams = cn from rfl] at hfr hreg
  rw [e_ρ] at hfr hreg
  have hcont : Continuous (coldFieldAboveFrames R V) := by
    refine continuous_pi fun z => continuous_pi fun i => ?_
    have hw : ∀ (z' : (stepTopFrame R n).Site (stepTopFrame R n).depth) (i' : Fin 4),
        Continuous fun k : StepVariable (finiteCells (stepTopFrame R n)) =>
          interpolatedCoords 1 R.params.coupling R.anchorRadius R.frameReach (topLevelField (R := R) V) k z' i' := by
      intro z' i'
      unfold interpolatedCoords stepCoordinates
      by_cases hb : (z', i') ∈ chordBonds (finiteCells (stepTopFrame R n))
      · simp only [dif_pos hb]
        exact continuous_const.add (continuous_toImaginary.comp (continuous_apply _))
      · simp only [dif_neg hb]
        exact continuous_const
    show Continuous fun k => chartedField
      (interpolatedCoords 1 R.params.coupling R.anchorRadius R.frameReach (topLevelField (R := R) V) k)
      (topLevelField (R := R) V) (siteOfCoords (stepTopFrame R n).depth fun l => ((z l).cast : ℤ)) i
    unfold chartedField
    split_ifs
    · exact (TorusFrameTransfer.continuous_expUnit.comp (hw _ _)).mul continuous_const
    · exact continuous_const
    · exact TorusFrameTransfer.continuous_expUnit.comp (hw _ _)
  have hpts : ∀ k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)),
      (∀ b, ‖k b‖ < R.ballRadius) →
      ∃ η : FreeCoords (coldChartSetting R V).free, (∀ b, coordNorm (η b) < R.ballRadius) ∧
        (coldChartSetting R V).field η = coldFieldAboveFrames R V k := by
    intro k hk
    refine ⟨fun b => k (freeBondsEquiv hcov hoddR V b), fun b => ?_, ?_⟩
    · rw [coordNorm_eq]
      exact hk _
    · have e1 : freeToStep hcov hoddR V (fun b => k (freeBondsEquiv hcov hoddR V b)) = k := by
        funext b
        simp [freeToStep]
      have e2 := readAtLevel_field hcov hoddR V (fun b => k (freeBondsEquiv hcov hoddR V b))
      rw [e1] at e2
      have e3 := (hends (stepTopFrame R n) false R.params.coupling R.anchorRadius 0 R.coupling 0 R.frameReach
        (topLevelField (R := R) V)).2.2.1 k
      have e4 : segmentEnd false = 1 := by simp [segmentEnd]
      rw [e4] at e3
      show _ = restrictToTorus _
        (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (topLevelField (R := R) V) k)
      rw [e3, ← e2]
      exact (restrictToTorus_readAtLevel (period_depth (H := stepTopFrame R n) (n := n) fun _ => rfl) _).symm
  refine ⟨?_, hcont, hpts, fun G hG => ?_, fun g Y => sum_cell_fiber_eq (R := R) hcov hoddR g Y⟩
  · have e4 : segmentEnd false = 1 := by simp [segmentEnd]
    have hcells : ∀ η : StepVariable (finiteCells (stepTopFrame R n)),
        η ∈ openBallProduct (stepTopFrame R n) R.ballRadius →
        (coldHalfLawOf R).exponent (coldTopField R V) η =
          ∑ Y ∈ finiteCells (stepTopFrame R n), cellExponent false R.params.coupling R.anchorRadius R.coupling
            R.frameReach Y (topLevelField (R := R) V) η -
          ∑ Y ∈ finiteCells (stepTopFrame R n), cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
            (localFamilyOfDensity R.density) Y η (topLevelField (R := R) V) := by
      intro η hη
      have e1 := (hends (stepTopFrame R n) false R.params.coupling R.anchorRadius 0 R.coupling 0 R.frameReach
        (topLevelField (R := R) V)).2.2.2.2.2.1 (localFamilyOfDensity R.density) η
      rw [e4] at e1
      have e2 : stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
          (localFamilyOfDensity R.density) 0 (topLevelField (R := R) V) η =
          ∑ Y ∈ finiteCells (stepTopFrame R n), cellExponent false R.params.coupling R.anchorRadius R.coupling
            R.frameReach Y (topLevelField (R := R) V) η :=
        hreg.stepExponent_eq_sum η hη
      have e3 : ∑ Y ∈ finiteCells (stepTopFrame R n), cellCentredExpansion false R.params.coupling R.anchorRadius
            R.frameReach (localFamilyOfDensity R.density) Y η (topLevelField (R := R) V) =
          ∑ y ∈ sitesOfCells (finiteCells (stepTopFrame R n)) (stepTopFrame R n).depth,
            centredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity R.density) y η
              (topLevelField (R := R) V) :=
        Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.TorusFrameTransfer.mem_finiteCells _) _
      show familyLawExponent 1 R.params.coupling R.anchorRadius R.coupling R.frameReach
        (localFamilyOfDensity R.density) (topLevelField (R := R) V) η = _
      rw [e1, ← e2, e3]
      simp [stepExponent]
    have hnnR : ∀ η : StepVariable (finiteCells (stepTopFrame R n)),
        0 ≤ radialWeightProd (coldHalfLawOf R).radialWeight η := hreg.cutoffWeight_nonneg
    refine isBallLaw_of_bounded (Ψ' := fun η =>
        ∑ Y ∈ finiteCells (stepTopFrame R n), cellExponent false R.params.coupling R.anchorRadius R.coupling
          R.frameReach Y (topLevelField (R := R) V) η -
          ∑ Y ∈ finiteCells (stepTopFrame R n), cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
            (localFamilyOfDensity R.density) Y η (topLevelField (R := R) V))
      (B := ∑ _Y ∈ finiteCells (stepTopFrame R n), M + ∑ _Y ∈ finiteCells (stepTopFrame R n), M)
      hnnR hreg.integrable_cutoffWeight hreg.integral_cutoffWeight_pos
      (fun η h => hreg.cutoffWeight_eq_zero_of_not_mem η h) ?_ ?_ (fun η h => hcells η h)
    · exact (continuousOn_finsetSum _ fun Y _ => hreg.continuousOn_cellExponent Y).sub
        (continuousOn_finsetSum _ fun Y _ => hreg.continuousOn_cellCentredExpansion Y)
    · intro η hη
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun Y _ => hreg.abs_cellExponent_le Y η hη)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun Y _ => hreg.abs_cellCentredExpansion_le Y η hη)
  · intro k hk
    obtain ⟨η, hη, e⟩ := hpts k hk
    have hc := hcs η fun b => (hη b).le
    have hc' : IsCold R.params.threshold (coldFieldAboveFrames R V k) := by
      rw [← e]
      intro z μ ν hμ
      exact (hc z μ ν hμ).trans (by show T.threshold / 4 < T.threshold; linarith)
    exact ((hc3 _ _ _ (hG _ hc')).comp hcont.continuousAt).continuousWithinAt
end ResponseInTheExpansion
end YangMills.Construction
end
