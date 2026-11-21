import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.ClusterExpansionOfAStep.GoodBondsMakeAColdPlaquette
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfAContourAtAColdTopProof
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASettingProof
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages GaugeFixing ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings
  StepMarks StepCosts StepFrames StepFloors ColdChain
namespace ColdChartFields
theorem cast_int_cast_of_eq (P m : ℕ) (h : P = m) (z : ℤ) :
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
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) :
    H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem cast_int_cast_coe_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m)
    (k : Fin 4) : siteCoords (torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  cast_int_cast_coe_of_eq _ _ (hm k) (x k)
def torusBlockCentre (L : ℕ) (Y : TorusSite n) : TorusSite (n * L) :=
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
  exact (cast_int_cast_of_eq _ _ (period_top hs k) _).symm
theorem torusSiteInFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_torusSiteInFrame j hm x, h, toTorusSite_torusSiteInFrame j hm y]
theorem isCrossingBond_torusSiteInFrame_iff (hs : ∀ i, H.extent i = n)
    (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
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
      torusSiteInFrame H H.depth (torusBlockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellCentre_torusSiteInFrame <;> assumption
theorem valMinAbs_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P))).valMinAbs = a.valMinAbs := by
  subst h; simp
def torusCellOffset (L : ℕ) (x : TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - torusBlockCentre L (parentBlock L x)) k).valMinAbs
theorem cellOffset_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusSite (n * H.blockSide)) :
    cellOffset (torusSiteInFrame H H.depth x) = torusCellOffset H.blockSide x := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellOffset_torusSiteInFrame <;> assumption
def IsTorusTreeBond (L : ℕ) (x : TorusSite (n * L)) (i : Fin 4) : Prop :=
  parentBlock L (x + TorusFields.unitStep _ i) = parentBlock L x ∧ ∀ l, i < l → torusCellOffset L x l = 0
theorem isAxialTreeBond_torusSiteInFrame_iff (hs : ∀ i, H.extent i = n)
    (x : TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (torusSiteInFrame H H.depth x, i) ↔ IsTorusTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
end Blocks
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
abbrev twoLevelFrame (R : StepSetup) (n : ℕ) : BlockFrame := stepBlockFrame R.params.side n
def coldTorusCoords (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) : imaginaryQuaternions :=
  open Classical in
  if h : (x, i) ∈ (coldChartSetting R V).free then
    (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), h⟩)
  else 0
def coldFrameCoords (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) :
    (twoLevelFrame R n).Site (twoLevelFrame R n).depth → Fin 4 → imaginaryQuaternions :=
  fun z i => coldTorusCoords V η (toTorusSite (n * R.params.side) z) i
theorem mem_free_iff (V : TorusField n) (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    (x, i) ∈ (coldChartSetting R V).free ↔ ¬ IsTorusTreeBond R.params.side x i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusTransfer.mem_free_iff <;> assumption
theorem readAtLevel_coldField (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) :
    readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).depth ((coldChartSetting R V).field η) =
      chartedField (coldFrameCoords V η) (readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V) := by
  have hlow : ∀ i, (twoLevelFrame R n).period (twoLevelFrame R n).depth i = n * R.params.side :=
    period_depth (H := twoLevelFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * R.params.side),
      torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := twoLevelFrame R n) _ hlow
    ((coldChartSetting R V).field η) x i).trans ?_
  have hw : coldFrameCoords V η (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x) i =
      coldTorusCoords V η x i := by
    show coldTorusCoords V η (toTorusSite (n * R.params.side)
      (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x)) i = _
    rw [toTorusSite_torusSiteInFrame _ hlow]
  have hcell : readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V
      (enclosingCell (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x)) i =
      V (parentBlock R.params.side x) i := by
    have h0 : enclosingCell (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x) =
        torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top (parentBlock R.params.side x) :=
      enclosingCell_torusSiteInFrame (H := twoLevelFrame R n) (n := n) (fun _ => rfl) x
    rw [h0]
    exact readAtLevel_torusSiteInFrame _ (period_top (H := twoLevelFrame R n) (n := n) fun _ => rfl) V _ i
  unfold chartedField
  by_cases hb : (x, i) ∈ (coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := twoLevelFrame R n)
        (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i) := fun h2 =>
      ((mem_free_iff V x i).1 hb)
        ((isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).1 h2)
    have hval : coldTorusCoords V η x i =
        (coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := dif_pos hb
    have hfield : (coldChartSetting R V).field η x i =
        chartLink (coldChartSetting R V) x i
          ((coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw, hval]
    unfold chartLink
    have h1 : gaugeAt (R := R) (coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := twoLevelFrame R n)
        (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i)
    · have hc0 : IsCrossingBond (F := twoLevelFrame R n)
          (torusSiteInFrame (twoLevelFrame R n) 0 x, i) := hc
      rw [if_pos hc0, if_pos hc, hcell]
      rfl
    · have hc0 : ¬ IsCrossingBond (F := twoLevelFrame R n)
          (torusSiteInFrame (twoLevelFrame R n) 0 x, i) := hc
      rw [if_neg hc0, if_neg hc, if_neg htree]
  · have hfield : (coldChartSetting R V).field η x i = (coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsTorusTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_free_iff V x i).2 h)
    have htree := (isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := twoLevelFrame R n)
        (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
theorem mem_chordBonds_of_mem_free (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (V : TorusField n) (b : TorusBond (n * R.params.side)) (hb : b ∈ (coldChartSetting R V).free) :
    (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth b.1, b.2) ∈
      chordBonds (finiteCells (twoLevelFrame R n)) := by
  have hc : ∀ x : (twoLevelFrame R n).Site (twoLevelFrame R n).depth,
      x ∈ sitesOfCells (finiteCells (twoLevelFrame R n)) (twoLevelFrame R n).depth :=
    hcov (twoLevelFrame R n) hodd (fun _ => Nat.pos_of_ne_zero (NeZero.ne n))
  simp only [chordBonds, Finset.mem_filter]
  refine ⟨?_, fun h2 => (mem_free_iff V b.1 b.2).1 hb
    ((isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) b.1 b.2).1 h2)⟩
  unfold innerBonds
  simp [hc]
theorem chartCoord_coldField (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free)
    (hw : ‖(((coldChartSetting R V).frame b.1 + toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi) :
    chartCoord R.params V ((coldChartSetting R V).field η) b.1 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by
  have hlow : ∀ i, (twoLevelFrame R n).period (twoLevelFrame R n).depth i = n * R.params.side :=
    period_depth (H := twoLevelFrame R n) (n := n) fun _ => rfl
  have hwv : coldFrameCoords V η (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth b.1.1) b.1.2 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by
    show coldTorusCoords V η (toTorusSite (n * R.params.side)
      (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth b.1.1)) b.1.2 = _
    rw [toTorusSite_torusSiteInFrame _ hlow]
    exact dif_pos b.2
  have h := GaugeFixing.bondCoordinate_of_agreeOnBonds (F := twoLevelFrame R n) (fun _ => hn) hodd
    (finiteCells (twoLevelFrame R n))
    (readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V) (coldFrameCoords V η) (fun _ => 1)
    (readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).depth ((coldChartSetting R V).field η))
    (fun _ => rfl)
    (fun c _ => by rw [readAtLevel_coldField]; simp [BlockAverages.gaugeTransform])
    (torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth b.1.1, b.1.2)
    (mem_chordBonds_of_mem_free hcov hodd V b.1 b.2)
    (by simpa only [hwv] using hw)
  exact h.trans hwv
end Chart
theorem norm_bondFrameCoord_le {F : BlockFrame} (a ρ : ℝ) (hρ : 0 ≤ ρ) (m : ℕ)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) : ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by apply _root_.YangMills.Construction.LogJacobian.norm_bondFrameCoord_le <;> assumption
theorem rangesAdmissible_clusterRange (T : ParameterAssignment) (hT : T.Admissible) (y x : ℝ)
    (hy : T.floorMin ≤ y) (hx : y ≤ x) :
    RangesAdmissible (clusterRange x) (clusterRange x) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusTransfer.rangesAdmissible_clusterRange <;> assumption
theorem coldChartSettingIsCold (hgood : coldPlaquette_of_small_frameDeviation)
    (hfloors : EventuallyFloorConditions) (hcov : BlocksCoverLowerLevel) :
    ColdChartSettingIsCold := by
  intro T hT
  have hN : 0 < T.N 0 := hT.chain.2.2.2.2.2.2.2.1 0
  have hσT : 0 < T.threshold := hT.σ_pos
  obtain ⟨yF, hyF⟩ := hfloors T hT (144 * T.N 0 * (2⁻¹ ^ 10 * T.threshold)) 1 (by positivity) one_pos
  refine ⟨max yF T.floorMin, fun y hy R hR n _ hn V hV η hη x μ ν hμ => ?_⟩
  have hyF' : yF ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : T.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hx : y ≤ R.coupling := hR.le_coupling
  have hσ0 : 0 < R.params.threshold := by rw [hσ]; exact hT.σ_pos
  have hodd : Odd R.params.side := by rw [hLe]; exact hT.L_odd
  have hn₀ : R.params.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    omega
  have h4096 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hfit : RangesAdmissible R.range R.range :=
    rangesAdmissible_clusterRange T hT y R.coupling hy0 hx
  have hsit : IsStepSituation R.params R.range V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn₀, by rw [hσ]; exact hV, rfl, rfl, rfl⟩
  have hfits : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy0
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA
      T.cg T.N := by
    rw [hR.params_eq, hR.anchorRadius_eq]
    exact hT.chain
  have h2σ : 2 * R.params.threshold ≤ T.σA := by rw [hσ]; exact hT.σ_le
  have hρ : 0 < R.anchorRadius := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.1
  have hρ1 : R.anchorRadius ≤ 1 := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
  have hgap : T.N 0 * (9 / 8 * R.params.threshold) *
      Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ R.params.threshold / 128 := by
    have hfl := (hyF R.coupling (hyF'.trans hx)).cold_tail
    have hm : boxRadius R.coupling = R.range / 2 ^ 11 := rfl
    rw [hm] at hfl
    set m : ℝ := ((R.range / 2 ^ 11 : ℕ) : ℝ) with hmdef
    have hδ : T.δc / 4 ≤ T.δ₁ := by
      have h1 := hT.δc_le
      have h2 := hT.δc_pos
      have h3 : 0 < T.δ₁ := hT.δ₁_pos
      linarith
    have hE : Real.exp (-(T.δ₁ * m)) ≤ Real.exp (-(T.δc / 4 * m)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hc : 0 < (2⁻¹ : ℝ) ^ 10 * T.threshold := by positivity
    have h144 : 144 * T.N 0 * Real.exp (-(T.δc / 4 * m)) ≤ 1 := by
      have e : (144 * T.N 0 * (2⁻¹ ^ 10 * T.threshold)) * Real.exp (-(T.δc / 4 * m)) =
          (144 * T.N 0 * Real.exp (-(T.δc / 4 * m))) * (2⁻¹ ^ 10 * T.threshold) := by ring
      rw [e] at hfl
      exact le_of_mul_le_mul_right (by linarith) hc
    rw [hσ]
    have h5 : T.N 0 * (9 / 8 * T.threshold) * Real.exp (-(T.δ₁ * m)) ≤
        T.N 0 * (9 / 8 * T.threshold) * Real.exp (-(T.δc / 4 * m)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have hσ1 : R.params.threshold ≤ 1 := by rw [hσ]; exact hT.σ_one
  have hb : ∀ b ∈ chartBonds R.params.side n,
      ‖(_root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) V
        ((coldChartSetting R V).field η) b : ℍ[ℝ])‖ ≤ R.params.threshold / 64 := by
    intro b hbm
    have hηb : ‖toImaginary (η ⟨b, hbm⟩)‖ ≤ R.ballRadius := hη ⟨b, hbm⟩
    have hfr : ‖(coldChartSetting R V).frame b‖ ≤ R.anchorRadius :=
      norm_bondFrameCoord_le _ _ hρ.le _ _ _
    have hw : ‖(((coldChartSetting R V).frame b + toImaginary (η ⟨b, hbm⟩) : imaginaryQuaternions) :
        ℍ[ℝ])‖ < Real.pi := by
      have h3 : ‖(((coldChartSetting R V).frame b + toImaginary (η ⟨b, hbm⟩) : imaginaryQuaternions) :
          ℍ[ℝ])‖ ≤ ‖(coldChartSetting R V).frame b‖ + ‖toImaginary (η ⟨b, hbm⟩)‖ := norm_add_le _ _
      have h4 : R.ballRadius = R.params.threshold / 64 := rfl
      have h5 := Real.pi_gt_three
      linarith
    have he := chartCoord_coldField (R := R) hcov hodd hn2 V η ⟨b, hbm⟩ hw
    have heta : _root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) V
        ((coldChartSetting R V).field η) b = toImaginary (η ⟨b, hbm⟩) := by
      unfold _root_.YangMills.Construction.StepMarks.frameDeviation
      rw [he]
      show (coldChartSetting R V).frame b + _ - (coldChartSetting R V).frame b = _
      abel
    rw [heta]
    exact hηb
  have hfinal := hgood R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfits hchain h2σ R.depth
    R.range R.range n V Finset.univ ∅ (9 / 8 * R.params.threshold) hfit hsit hgap
    ((coldChartSetting R V).field η) x μ ν hμ
    (fun _ _ => Finset.notMem_empty _) (fun b hbm _ => hb b hbm)
  rw [hσ] at hfinal
  exact hfinal
end ColdChartFields
end YangMills.Construction
end
