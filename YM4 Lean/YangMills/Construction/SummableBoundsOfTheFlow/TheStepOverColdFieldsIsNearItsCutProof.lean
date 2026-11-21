import YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixingOfTheStepProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsPlainFarFromLumps
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixingOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.ColdStepAtMirrorFrames.WeylFormulaOfTheGroup
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepOverColdFieldsIsNearItsCut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.TorusContours YangMills.Construction.StepCosts
namespace YangMills.Construction.Interpolation
private theorem log_sub_log_le_div {A B I J : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (h : A ≤ I) (hJ : 0 < J)
    (h' : J ≤ A + B) : Real.log J - Real.log I ≤ B / A := by
  have hI : 0 < I := lt_of_lt_of_le hA h
  rw [← Real.log_div hJ.ne' hI.ne']
  have hBA : 0 ≤ B / A := div_nonneg hB hA.le
  have hr : J / I ≤ 1 + B / A := by
    rw [div_le_iff₀ hI]
    calc J ≤ A + B := h'
      _ = (1 + B / A) * A := by field_simp
      _ ≤ (1 + B / A) * I := mul_le_mul_of_nonneg_left h (by linarith)
  have := Real.log_le_sub_one_of_pos (div_pos hJ hI)
  linarith
private theorem abs_log_sub_log_le_div {A B I J : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (h₁ : A ≤ I) (h₁' : I ≤ A + B)
    (h₂ : A ≤ J) (h₂' : J ≤ A + B) : |Real.log I - Real.log J| ≤ B / A := by
  have hI : 0 < I := lt_of_lt_of_le hA h₁
  have hJ : 0 < J := lt_of_lt_of_le hA h₂
  rw [abs_le]
  have e1 := log_sub_log_le_div hA hB h₂ hI h₁'
  have e2 := log_sub_log_le_div hA hB h₁ hJ h₂'
  constructor <;> linarith
private theorem setIntegral_le_integral_weight_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f u : Ω → ℝ}
    (hf0 : ∀ w, 0 ≤ f w) (hfi : Integrable f μ) (hum : Measurable u) (hu : ∀ w, 0 ≤ u w ∧ u w ≤ 1)
    {N : Set Ω} (hN : MeasurableSet N) (h1 : ∀ w ∈ N, u w = 1) :
    ∫ w in N, f w ∂μ ≤ ∫ w, u w * f w ∂μ ∧
      ∫ w, u w * f w ∂μ ≤ ∫ w in N, f w ∂μ + ∫ w in Nᶜ, f w ∂μ := by
  have hui : Integrable (fun w => u w * f w) μ :=
    hfi.bdd_mul (c := 1) hum.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hu w).1]
        exact (hu w).2)
  have hsplit := integral_add_compl hN hui
  have hon : ∫ w in N, u w * f w ∂μ = ∫ w in N, f w ∂μ :=
    setIntegral_congr_fun hN fun w hw => by simp [h1 w hw]
  have hoff : 0 ≤ ∫ w in Nᶜ, u w * f w ∂μ :=
    integral_nonneg fun w => mul_nonneg (hu w).1 (hf0 w)
  have hoff' : ∫ w in Nᶜ, u w * f w ∂μ ≤ ∫ w in Nᶜ, f w ∂μ :=
    integral_mono hui.integrableOn hfi.integrableOn fun w => by
      have := mul_le_mul_of_nonneg_right (hu w).2 (hf0 w)
      simpa using this
  rw [← hsplit, hon]
  constructor <;> linarith
private theorem tendsto_log_sub_log_of_gap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ) (hg0 : ∀ w, 0 ≤ g w) (hgi : Integrable g μ)
    (P : ℝ → Ω → ℝ) (hP0 : ∀ x, 0 < x → ∀ w, 0 ≤ P x w) (hPm : ∀ x, 0 < x → Measurable (P x))
    (hPb : ∀ x, 0 < x → ∃ C, ∀ w, P x w ≤ C)
    (u₁ u₂ : Ω → ℝ) (hu₁m : Measurable u₁) (hu₂m : Measurable u₂)
    (hu₁ : ∀ w, 0 ≤ u₁ w ∧ u₁ w ≤ 1) (hu₂ : ∀ w, 0 ≤ u₂ w ∧ u₂ w ≤ 1)
    (N N' : Set Ω) (hNm : MeasurableSet N) (h1N : ∀ w ∈ N, u₁ w = 1) (h2N : ∀ w ∈ N, u₂ w = 1)
    (hN'm : MeasurableSet N') (hN' : N' ⊆ N) (hpos : 0 < ∫ w in N', g w ∂μ)
    (E c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A)
    (hlow : ∀ x, 0 < x → ∀ w ∈ N', Real.exp (-x * (E + c / 4)) ≤ P x w)
    (hup : ∀ x, 0 < x → ∀ w, w ∉ N → g w ≠ 0 → P x w ≤ A * Real.exp (-x * (E + 3 * c / 4))) :
    Filter.Tendsto (fun x => Real.log (∫ w, u₁ w * (P x w * g w) ∂μ) -
      Real.log (∫ w, u₂ w * (P x w * g w) ∂μ)) Filter.atTop (nhds 0) := by
  set G' : ℝ := ∫ w in N', g w ∂μ with hG'
  set Gt : ℝ := ∫ w, g w ∂μ with hGt
  have hGt0 : 0 ≤ Gt := integral_nonneg hg0
  have hbound : ∀ x : ℝ, 0 < x → |Real.log (∫ w, u₁ w * (P x w * g w) ∂μ) -
      Real.log (∫ w, u₂ w * (P x w * g w) ∂μ)| ≤ A * Gt / G' * Real.exp (-(c / 2 * x)) := by
    intro x hx
    have hf0 : ∀ w, 0 ≤ P x w * g w := fun w => mul_nonneg (hP0 x hx w) (hg0 w)
    obtain ⟨C, hC⟩ := hPb x hx
    have hfi : Integrable (fun w => P x w * g w) μ :=
      hgi.bdd_mul (c := C) (hPm x hx).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x hx w)]
          exact hC w)
    obtain ⟨a1, b1⟩ := setIntegral_le_integral_weight_le hf0 hfi hu₁m hu₁ hNm h1N
    obtain ⟨a2, b2⟩ := setIntegral_le_integral_weight_le hf0 hfi hu₂m hu₂ hNm h2N
    set A₀ : ℝ := ∫ w in N, P x w * g w ∂μ with hA₀
    set B₀ : ℝ := ∫ w in Nᶜ, P x w * g w ∂μ with hB₀
    have hB0 : 0 ≤ B₀ := integral_nonneg hf0
    have hlowA : Real.exp (-x * (E + c / 4)) * G' ≤ A₀ := by
      have s1 : ∫ w in N', P x w * g w ∂μ ≤ A₀ :=
        setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hf0)
          (Filter.Eventually.of_forall hN')
      have s2 : Real.exp (-x * (E + c / 4)) * G' ≤ ∫ w in N', P x w * g w ∂μ := by
        rw [hG', ← integral_const_mul]
        refine setIntegral_mono_on (hgi.integrableOn.const_mul _) hfi.integrableOn hN'm ?_
        intro w hw
        exact mul_le_mul_of_nonneg_right (hlow x hx w hw) (hg0 w)
      linarith
    have hupB : B₀ ≤ A * Real.exp (-x * (E + 3 * c / 4)) * Gt := by
      have s1 : B₀ ≤ ∫ w in Nᶜ, A * Real.exp (-x * (E + 3 * c / 4)) * g w ∂μ := by
        refine setIntegral_mono_on hfi.integrableOn (hgi.integrableOn.const_mul _) hNm.compl ?_
        intro w hw
        by_cases hg : g w = 0
        · simp [hg]
        · exact mul_le_mul_of_nonneg_right (hup x hx w hw hg) (hg0 w)
      have s2 : ∫ w in Nᶜ, A * Real.exp (-x * (E + 3 * c / 4)) * g w ∂μ ≤
          A * Real.exp (-x * (E + 3 * c / 4)) * Gt := by
        rw [integral_const_mul, hGt]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
      linarith
    have hA₀pos : 0 < A₀ := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hpos) hlowA
    refine (abs_log_sub_log_le_div hA₀pos hB0 a1 b1 a2 b2).trans ?_
    have hexp : Real.exp (-x * (E + 3 * c / 4)) =
        Real.exp (-(c / 2 * x)) * Real.exp (-x * (E + c / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [div_le_iff₀ hA₀pos]
    calc B₀ ≤ A * Real.exp (-x * (E + 3 * c / 4)) * Gt := hupB
      _ = A * Gt / G' * Real.exp (-(c / 2 * x)) * (Real.exp (-x * (E + c / 4)) * G') := by
        rw [hexp]
        field_simp
      _ ≤ A * Gt / G' * Real.exp (-(c / 2 * x)) * A₀ :=
        mul_le_mul_of_nonneg_left hlowA (by positivity)
  have hlim : Filter.Tendsto (fun x : ℝ => A * Gt / G' * Real.exp (-(c / 2 * x))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => c / 2 * x) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (A * Gt / G')
    simpa [Function.comp_def] using h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  simpa [Real.norm_eq_abs] using hbound x hx
private theorem one_sub_re_unit_nonneg (g : UnitQuaternion) : 0 ≤ 1 - ((g : UnitQuaternion) : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.one_sub_re_nonneg <;> assumption
private theorem continuous_re_unit : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
private theorem haarLaplace_eq_integral (hW : WeylIntegrationFormula) (s : ℝ) :
    haarLaplace s = ∫ g : UnitQuaternion, Real.exp (-(s * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re))) ∂haarUnit :=
  (hW.1 (fun v => Real.exp (-(s * v))) (by fun_prop)).symm
private theorem integrable_exp_unit (s : ℝ) :
    Integrable (fun g : UnitQuaternion => Real.exp (-(s * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re)))) haarUnit := by
  have hc : Continuous fun g : UnitQuaternion => Real.exp (-(s * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re))) :=
    Real.continuous_exp.comp ((continuous_const.mul (continuous_const.sub continuous_re_unit)).neg)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private theorem haarLaplace_le_one (hW : WeylIntegrationFormula) {s : ℝ} (hs : 0 ≤ s) :
    haarLaplace s ≤ 1 := by
  rw [haarLaplace_eq_integral hW]
  have h : ∫ g : UnitQuaternion, Real.exp (-(s * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re))) ∂haarUnit ≤
      ∫ _g : UnitQuaternion, (1 : ℝ) ∂haarUnit := by
    refine integral_mono (integrable_exp_unit s) (integrable_const _) fun g => ?_
    have := mul_nonneg hs (one_sub_re_unit_nonneg g)
    exact Real.exp_le_one_iff.mpr (by linarith)
  simpa using h
private theorem exists_haarLaplace_lower (hW : WeylIntegrationFormula) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℝ, 0 ≤ s → m * Real.exp (-(s * δ)) ≤ haarLaplace s := by
  set A : Set UnitQuaternion := {g | 1 - ((g : UnitQuaternion) : ℍ[ℝ]).re < δ} with hA
  have hop : IsOpen A := isOpen_lt (continuous_const.sub continuous_re_unit) continuous_const
  have hone : (1 : UnitQuaternion) ∈ A := by
    simp [hA, hδ]
  have hpos : 0 < haarUnit A := hop.measure_pos haarUnit ⟨1, hone⟩
  refine ⟨haarUnit.real A, ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _), fun s hs => ?_⟩
  rw [haarLaplace_eq_integral hW]
  have hm : MeasurableSet A := hop.measurableSet
  have hint : ∫ g : UnitQuaternion, A.indicator (fun _ => Real.exp (-(s * δ))) g ∂haarUnit =
      haarUnit.real A * Real.exp (-(s * δ)) := by
    rw [integral_indicator_const _ hm, smul_eq_mul]
  rw [← hint]
  refine integral_mono ((integrable_const _).indicator hm) (integrable_exp_unit s) fun g => ?_
  by_cases hg : g ∈ A
  · simp only [Set.indicator_of_mem hg]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left (le_of_lt hg) hs
    linarith
  · simp only [Set.indicator_of_notMem hg]
    exact (Real.exp_pos _).le
private theorem haarLaplace_pos (hW : WeylIntegrationFormula) {s : ℝ} (hs : 0 ≤ s) :
    0 < haarLaplace s := by
  obtain ⟨m, hm, h⟩ := exists_haarLaplace_lower hW (δ := 1) one_pos
  exact lt_of_lt_of_le (mul_pos hm (Real.exp_pos _)) (h s hs)
section Continuity
variable {F : BlockFrame}
private theorem continuous_contourAverage' {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    Continuous fun W : F.GaugeField j => contourAverage W c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_contourAverage <;> assumption
private theorem continuous_minimalAction' (a : ℝ) (S : Finset F.Cell) :
    ∀ j, Continuous (minimalAction a S j : F.GaugeField j → ℝ) := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_minimalAction <;> assumption
private theorem continuous_blockFit_fine {j : ℕ} (V : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    Continuous fun W : F.GaugeField j => blockFit W V c := by
  unfold blockFit
  have h1 : Continuous fun W : F.GaugeField j => contourAverage W c := continuous_contourAverage' c
  exact h1.norm.sub (Quaternion.continuous_re.comp (h1.mul continuous_const))
private theorem continuous_blockEnergy' (a : ℝ) (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField (j + 1)) :
    Continuous fun X : F.GaugeField j => blockEnergy a S j X V := by
  have h : Continuous fun X : F.GaugeField j => ∑ c ∈ innerBonds S (j + 1), blockFit X V c :=
    continuous_finsetSum _ fun c _ => continuous_blockFit_fine V c
  exact (continuous_minimalAction' a S j).add (continuous_const.mul h)
end Continuity
section Gauge
variable {F : BlockFrame}
private theorem minimalAction_gaugeTransform (hgc : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (a : ℝ)
    (S : Finset F.Cell) : ∀ j, j < F.top → ∀ (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j),
      minimalAction a S j (BlockAverages.gaugeTransform γ X) = minimalAction a S j X := by
  intro j
  induction j with
  | zero =>
    intro hj γ X
    show BlockAverages.wilsonAction S (BlockAverages.gaugeTransform γ X) = BlockAverages.wilsonAction S X
    unfold BlockAverages.wilsonAction
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [(hgc F 0 hj hL).2.2.1 γ X p, re_unitQuaternion_conj]
  | succ j ih =>
    intro hj γ V
    have hj' : j < F.top := by omega
    obtain ⟨hinj, -, -, hfit⟩ := hgc F j hj' hL
    set γ' : F.Site j → UnitQuaternion := Function.extend refineSite γ 1 with hγ'
    have hd : ∀ y, γ' (refineSite y) = γ y := fun y => hinj.extend_apply _ _ y
    let e : F.GaugeField j ≃ F.GaugeField j :=
      { toFun := BlockAverages.gaugeTransform γ'
        invFun := BlockAverages.gaugeTransform fun x => (γ' x)⁻¹
        left_inv := fun W => by
          funext x i
          simp [BlockAverages.gaugeTransform, mul_assoc]
        right_inv := fun W => by
          funext x i
          simp [BlockAverages.gaugeTransform, mul_assoc] }
    show (⨅ W : F.GaugeField j, (minimalAction a S j W +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit W (BlockAverages.gaugeTransform γ V) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c)
    refine (Equiv.iInf_congr e fun W => ?_).symm
    show minimalAction a S j (BlockAverages.gaugeTransform γ' W) + a * ∑ c ∈ innerBonds S (j + 1),
      blockFit (BlockAverages.gaugeTransform γ' W) (BlockAverages.gaugeTransform γ V) c = _
    rw [ih hj' γ' W]
    congr 2
    exact Finset.sum_congr rfl fun c _ => hfit γ' γ W V c (hd _) (hd _)
private theorem cellCentre_eq_refineSite (z : F.Cell) : cellCentre F.depth z = refineSite (j := F.depth) z := by apply _root_.YangMills.Construction.BondMeans.cellCentre_eq_refineSite <;> assumption
private theorem contourAverage_gaugeTransform (hgc : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (γ : F.Site F.depth → UnitQuaternion) (h1 : ∀ z, γ (cellCentre F.depth z) = 1) (X : F.GaugeField F.depth)
    (c : F.Site (F.depth + 1) × Fin 4) :
    contourAverage (BlockAverages.gaugeTransform γ X) c = contourAverage X c := by
  have hcov := (hgc F F.depth (by simp [BlockFrame.top]) hL).2.1 γ X c
  have e1 : γ (refineSite c.1) = 1 := by rw [← cellCentre_eq_refineSite]; exact h1 _
  have e2 : γ (refineSite (c.1 + BlockAverages.unitStep (F.depth + 1) c.2)) = 1 := by
    rw [← cellCentre_eq_refineSite]; exact h1 _
  rw [hcov, e1, e2]
  simp
end Gauge
section Ties
variable {F : BlockFrame} {n : ℕ} [NeZero n] [NeZero (n * F.blockSide)]
private theorem readAtLevel_restrictToTorus (hn : ∀ i, F.extent i = n) (X : F.GaugeField F.depth) :
    readAtLevel F F.depth (restrictToTorus (n * F.blockSide) X) = X := by
  funext y i
  exact congrFun (congrArg X (TopLevelSites.torusSiteInFrame_toTorusSite
    (TopLevelSites.period_depth_of_extent hn) y)) i
private theorem contourAverage_eq_plainContourAverage (hn : ∀ i, F.extent i = n) (X : F.GaugeField F.depth)
    (Y : TorusSite n) (i : Fin 4) :
    contourAverage X (torusSiteInFrame F F.top Y, i) =
      plainContourAverage F.blockSide Y i (restrictToTorus (n * F.blockSide) X) := by
  have h := TorusContours.contourAverage_readAtLevel hn (restrictToTorus (n * F.blockSide) X) Y i
  rwa [readAtLevel_restrictToTorus hn] at h
private theorem torusSiteInFrame_unitStep (hn : ∀ i, F.extent i = n) (i : Fin 4) :
    torusSiteInFrame F F.depth (TorusFields.unitStep (n * F.blockSide) i) = BlockAverages.unitStep F.depth i := by
  rw [← TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_depth_of_extent hn) i,
    TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_depth_of_extent hn)]
private theorem restrictToTorus_gaugeTransform (hn : ∀ i, F.extent i = n) (γ : F.Site F.depth → UnitQuaternion)
    (X : F.GaugeField F.depth) :
    restrictToTorus (n * F.blockSide) (BlockAverages.gaugeTransform γ X) =
      TorusFields.gaugeTransform (fun y => γ (torusSiteInFrame F F.depth y))
        (restrictToTorus (n * F.blockSide) X) := by
  funext x i
  show γ (torusSiteInFrame F F.depth x) * X (torusSiteInFrame F F.depth x) i *
      (γ (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i))⁻¹ =
    γ (torusSiteInFrame F F.depth x) * X (torusSiteInFrame F F.depth x) i *
      (γ (torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i)))⁻¹
  rw [TopLevelSites.torusSiteInFrame_add (TopLevelSites.period_depth_of_extent hn), torusSiteInFrame_unitStep hn]
private theorem isCold_restrictToTorus_gaugeTransform (hn : ∀ i, F.extent i = n)
    (γ : F.Site F.depth → UnitQuaternion) (X : F.GaugeField F.depth) (s : ℝ) :
    TorusFields.IsCold s (restrictToTorus (n * F.blockSide) (BlockAverages.gaugeTransform γ X)) ↔
      TorusFields.IsCold s (restrictToTorus (n * F.blockSide) X) := by
  rw [restrictToTorus_gaugeTransform hn]
  unfold TorusFields.IsCold
  simp only [curvature_gaugeTransform]
omit [NeZero (n * F.blockSide)] in
private theorem extent_pos (hn : ∀ i, F.extent i = n) (i : Fin 4) : 0 < F.extent i := by
  rw [hn]
  exact Nat.pos_of_ne_zero (NeZero.ne n)
omit [NeZero (n * F.blockSide)] in
private theorem mem_sitesOfCells_top (hn : ∀ i, F.extent i = n) (x : F.Cell) :
    x ∈ sitesOfCells (finiteCells F) F.top := by
  rw [mem_sitesOfCells]
  refine ⟨x, TopLevelSites.mem_finiteCells (extent_pos hn) x, 0, ?_, ?_⟩
  · rw [TopLevelSites.mem_centredCube_iff]
    intro i
    have : F.top - F.top = 0 := Nat.sub_self _
    simp [TopLevelSites.halfWidth]
  · have hc : cellCentre F.top x = x := by
      funext i
      have := TopLevelSites.period_neZero (TopLevelSites.period_top_of_extent hn) i
      simp [cellCentre, siteOfCoords, siteCoords]
    have h0 : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [h0, add_zero, hc]
abbrev _root_.YangMills.SharedProofs.p21834 := @mem_sitesOfCells_top
omit [NeZero (n * F.blockSide)] in
private theorem mem_innerBonds_top (hn : ∀ i, F.extent i = n) (c : F.Site F.top × Fin 4) :
    c ∈ innerBonds (finiteCells F) F.top := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨mem_sitesOfCells_top hn _, Finset.mem_univ _⟩, mem_sitesOfCells_top hn _⟩
omit [NeZero (n * F.blockSide)] in
private theorem mem_sitesOfCells_depth (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hn : ∀ i, F.extent i = n) (x : F.Site F.depth) : x ∈ sitesOfCells (finiteCells F) F.depth := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [mem_sitesOfCells]
  refine ⟨z, TopLevelSites.mem_finiteCells (extent_pos hn) z, h, ?_, rfl⟩
  rw [TopLevelSites.top_sub_depth, pow_one]
  exact hh
abbrev _root_.YangMills.SharedProofs.p106137 := @mem_sitesOfCells_depth
omit [NeZero (n * F.blockSide)] in
private theorem mem_innerPlaquettes_depth (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hn : ∀ i, F.extent i = n) (p : F.Site F.depth × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) :
    p ∈ innerPlaquettes (finiteCells F) F.depth := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  exact ⟨⟨mem_sitesOfCells_depth hL hs hn _, Finset.mem_univ _, Finset.mem_univ _⟩, hp,
    fun x _ => mem_sitesOfCells_depth hL hs hn x⟩
omit [NeZero (n * F.blockSide)] in
private theorem prod_innerBonds_top (hn : ∀ i, F.extent i = n) (f : F.Site F.top × Fin 4 → ℝ) :
    ∏ c ∈ innerBonds (finiteCells F) F.top, f c =
      ∏ y : TorusSite n, ∏ i : Fin 4, f (torusSiteInFrame F F.top y, i) := by
  rw [← Fintype.prod_prod_type' (f := fun y i => f (torusSiteInFrame F F.top y, i))]
  refine Finset.prod_nbij' (fun c => (toTorusSite n c.1, c.2)) (fun c => (torusSiteInFrame F F.top c.1, c.2))
    (fun _ _ => Finset.mem_univ _) (fun c _ => mem_innerBonds_top hn _) ?_ ?_ ?_
  · intro c _
    exact Prod.ext (TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_top_of_extent hn) c.1) rfl
  · intro c _
    exact Prod.ext (TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn) c.1) rfl
  · intro c _
    simp only [TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_top_of_extent hn)]
private theorem hotLumps_eq_empty_of_isCold {H : BlockFrame} {j m : ℕ} [NeZero m] {L : ℕ}
    (g : LumpContours.LumpGrid L) (hm : ∀ i, H.period j i = m) (s : ℝ) (X : Finset (H.Site j))
    (W : TorusField m) (hW : TorusFields.IsCold s W) :
    LumpContours.hotLumps g s X (readAtLevel H j W) = ∅ := by
  unfold LumpContours.hotLumps
  have hf : ((LumpContours.cutPlaquettes X).filter fun p => s ≤ plaquetteDefect (readAtLevel H j W) p) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [Finset.mem_filter] at hp
    have h1 : p.2.1 < p.2.2 := by
      have := hp.1
      unfold LumpContours.cutPlaquettes at this
      rw [Finset.mem_filter] at this
      exact this.2.1
    have h2 := hW (toTorusSite m p.1) p.2.1 p.2.2 h1
    have h3 := hp.2
    rw [show p = (p.1, p.2.1, p.2.2) from rfl, TopLevelSites.plaquetteDefect_readAtLevel_eq hm] at h3
    exact absurd h3 (not_le.2 h2)
  rw [hf]
  rfl
end Ties
section Kernel
variable {n : ℕ} [NeZero n]
private theorem baseChoices_of_isCold (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) :
    baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = {fun y => cellCentre 0 y} := by apply _root_.YangMills.Construction.MarkedIntegrals.MarkedIntegralIdentity.baseChoices_eq_singleton <;> assumption
private theorem averagedKernel_of_isCold (hplain : KernelPlainAwayFromLumps) (ℓ : TorusLumps.StepParameters)
    (hfit : ℓ.Admissible) (x : ℝ) (W : TorusField (n * ℓ.side)) (hW : TorusFields.IsCold ℓ.threshold W)
    (V : TorusField n) :
    averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) =
      ∏ y : TorusSite n, ∏ i : Fin 4,
        Real.exp (ℓ.coupling * x * (plainContourAverage ℓ.side y i W * ((V y i)⁻¹ : UnitQuaternion)).re) /
          partitionFn (ℓ.coupling * x * ‖plainContourAverage ℓ.side y i W‖) := by
  classical
  have hm : ∀ i, (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side := fun i => by
    show n * ℓ.side ^ (0 + 1 - 0) = n * ℓ.side
    simp
  have hn : ∀ i, (stepBlockFrame ℓ.side n).extent i = n := fun _ => rfl
  have h0 : fineHotLumps ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = ∅ :=
    hotLumps_eq_empty_of_isCold _ hm _ _ W hW
  have hbase := baseChoices_of_isCold ℓ W hW
  have hmem : (fun y => cellCentre 0 y) ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) := by
    rw [hbase]
    exact Finset.mem_singleton_self _
  unfold averagedKernel
  rw [hbase]
  simp only [Finset.card_singleton, Nat.cast_one, div_one, one_mul, Finset.sum_singleton]
  rw [← Fintype.prod_prod_type' (f := fun (y : TorusSite n) (i : Fin 4) =>
    Real.exp (ℓ.coupling * x * (plainContourAverage ℓ.side y i W * ((V y i)⁻¹ : UnitQuaternion)).re) /
          partitionFn (ℓ.coupling * x * ‖plainContourAverage ℓ.side y i W‖))]
  refine Finset.prod_nbij' (fun c => (toTorusSite n c.1, c.2))
    (fun c => (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top c.1, c.2))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro c _
    exact Prod.ext (TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_top_of_extent hn) c.1) rfl
  · intro c _
    exact Prod.ext (TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn) c.1) rfl
  · rintro ⟨y, i⟩ _
    have hb : LumpContours.nearbyLumps (fineHotLumps ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W)) =
        fun _ => ∅ := by
      funext z
      rw [h0]
      unfold LumpContours.nearbyLumps
      exact Finset.filter_empty _
    have hk := ((hplain ℓ hfit n (readAtLevel (stepBlockFrame ℓ.side n) 0 W) y i (by rw [hb]) (by rw [hb])).2 x
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V) _ hmem).2.2
    have hmean : contourAverage (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (y, i) =
        plainContourAverage ℓ.side (toTorusSite n y) i W := by
      have : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := inferInstanceAs (NeZero (n * ℓ.side))
      have h := TorusContours.contourAverage_readAtLevel (F := stepBlockFrame ℓ.side n) hn W (toTorusSite n y) i
      rw [TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_top_of_extent hn)] at h
      exact h
    have hV : readAtLevel (stepBlockFrame ℓ.side n) 1 V y i = V (toTorusSite n y) i := rfl
    rw [hk, hmean, hV]
end Kernel
section Weight
private instance neZero_mul_blockSide {L t n : ℕ} [NeZero n] [NeZero L] :
    NeZero (n * (torusFrame L t n).blockSide) :=
  inferInstanceAs (NeZero (n * L))
private theorem plaquetteHolonomy_eq_holonomy {F : BlockFrame} {n : ℕ} [NeZero n] [NeZero (n * F.blockSide)]
    (hn : ∀ i, F.extent i = n) (X : F.GaugeField F.depth) (y : F.Site F.depth) (μ ν : Fin 4) :
    plaquetteHolonomy X (y, μ, ν) =
      holonomy (restrictToTorus (n * F.blockSide) X) (toTorusSite (n * F.blockSide) y) μ ν := by
  have hp := TopLevelSites.period_depth_of_extent (F := F) hn
  have f_at : ∀ (z : F.Site F.depth) (i : Fin 4),
      restrictToTorus (n * F.blockSide) X (toTorusSite (n * F.blockSide) z) i = X z i :=
    fun z i => congrFun (congrArg X (TopLevelSites.torusSiteInFrame_toTorusSite hp z)) i
  have h1 : toTorusSite (n * F.blockSide) y + TorusFields.unitStep (n * F.blockSide) μ =
      toTorusSite (n * F.blockSide) (y + BlockAverages.unitStep F.depth μ) := by
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_unitStep hp]
  have h2 : toTorusSite (n * F.blockSide) y + TorusFields.unitStep (n * F.blockSide) ν =
      toTorusSite (n * F.blockSide) (y + BlockAverages.unitStep F.depth ν) := by
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_unitStep hp]
  have h3 : y + BlockAverages.unitStep F.depth μ + BlockAverages.unitStep F.depth ν -
      BlockAverages.unitStep F.depth μ = y + BlockAverages.unitStep F.depth ν := by abel
  have h4 : y + BlockAverages.unitStep F.depth μ + BlockAverages.unitStep F.depth ν +
      -BlockAverages.unitStep F.depth μ - BlockAverages.unitStep F.depth ν = y := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    holonomy, h1, h2, f_at, h3, h4, mul_one, mul_assoc]
private theorem isCold_restrictToTorus {F : BlockFrame} {n : ℕ} [NeZero n] [NeZero (n * F.blockSide)]
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hn : ∀ i, F.extent i = n) {s : ℝ}
    {X : F.GaugeField F.depth} (h : BlockAverages.IsCold (finiteCells F) F.depth s X) :
    TorusFields.IsCold s (restrictToTorus (n * F.blockSide) X) := by
  intro x μ ν hμ
  have h1 := h (torusSiteInFrame F F.depth x, μ, ν) (mem_innerPlaquettes_depth hL hs hn _ hμ)
  unfold plaquetteDefect at h1
  rw [plaquetteHolonomy_eq_holonomy hn,
    TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn)] at h1
  exact h1
private theorem intCast_cast_zmod (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
private theorem minimalAction_eq_actionAtLevel (hla : MinimalActionTransfer) (a : ℝ) {L n : ℕ} [NeZero n]
    [NeZero L] (hL : Odd L) (h2 : 2 ≤ n) : ∀ (t : ℕ) (X : (torusFrame L t n).GaugeField (torusFrame L t n).depth),
      minimalAction a (finiteCells (torusFrame L t n)) (torusFrame L t n).depth X =
        actionAtLevel a L t Finset.univ (restrictToTorus (n * L) X) := by
  intro t X
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hL0 : 0 < L := hL.pos
  cases t with
  | zero =>
    have hn : ∀ i, (torusFrame L 0 n).extent i = n := fun _ => rfl
    have hs : ∀ i, 2 ≤ (torusFrame L 0 n).extent i := fun _ => h2
    have hp := TopLevelSites.period_depth_of_extent (F := torusFrame L 0 n) hn
    show ∑ p ∈ innerPlaquettes (finiteCells (torusFrame L 0 n)) 0,
        (1 - ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]).re) =
      TorusFields.wilsonAction Finset.univ (restrictToTorus (n * L) X)
    unfold TorusFields.wilsonAction plaquetteEnergy
    refine Finset.sum_nbij' (fun p => (toTorusSite (n * L) p.1, p.2))
      (fun p => (torusSiteInFrame (torusFrame L 0 n) 0 p.1, p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hpm
      have h1 : p.2.1 < p.2.2 := (Finset.mem_filter.mp hpm).2.1
      simp only [plaquettesIn, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h1, fun _ _ => Finset.mem_univ _⟩
    · intro p hpm
      simp only [plaquettesIn, Finset.mem_filter] at hpm
      exact mem_innerPlaquettes_depth (F := torusFrame L 0 n) hL hs hn _ hpm.2.1
    · intro p _
      exact Prod.ext (TopLevelSites.torusSiteInFrame_toTorusSite hp p.1) rfl
    · intro p _
      exact Prod.ext (TopLevelSites.toTorusSite_torusSiteInFrame hp p.1) rfl
    · rintro ⟨y, μ, ν⟩ _
      have h := plaquetteHolonomy_eq_holonomy (F := torusFrame L 0 n) hn X y μ ν
      show 1 - ((plaquetteHolonomy X (y, μ, ν) : UnitQuaternion) : ℍ[ℝ]).re = _
      rw [h]
      rfl
  | succ s =>
    have hper : ∀ k, k ≤ s + 1 → ∀ i,
        (torusFrame L (s + 1) n).period k i = (torusFrame L s (n * L)).period k i := by
      intro k hk i
      have e1 : s + 1 + 1 - k = (s + 1 - k) + 1 := by omega
      simp only [BlockFrame.period, torusFrame, BlockFrame.top]
      rw [e1, pow_succ]
      ring
    have hone : SharePeriods (torusFrame L (s + 1) n) (torusFrame L s (n * L)) (s + 1) :=
      ⟨rfl, hL, fun _ => hn0, fun _ => Nat.mul_pos hn0 hL0, by simp [torusFrame, BlockFrame.top],
        by simp [torusFrame, BlockFrame.top], hper⟩
    have h := (hla _ _ (s + 1) a hone).1 (s + 1) X le_rfl
    have hP : ∀ k, (torusFrame L (s + 1) n).period (s + 1) k = n * L := fun k => by
      rw [hper (s + 1) le_rfl k]
      simp [BlockFrame.period, torusFrame, BlockFrame.top]
    have hread : readAtLevel (torusFrame L s (n * L)) (s + 1) (restrictToTorus (n * L) X) =
        transferField (torusFrame L s (n * L)) X := by
      funext y i
      show X (siteOfCoords (s + 1) fun k => ((((siteCoords y k : ℤ) : ZMod (n * L))).cast : ℤ)) i =
        X (siteOfCoords (s + 1) (siteCoords y)) i
      congr 1
      funext k
      exact intCast_cast_zmod _ _ (hP k) _
    have hc : cellsOfSites (torusFrame L s (n * L)) (Finset.univ : Finset (TorusSite (n * L))) =
        finiteCells (torusFrame L s (n * L)) :=
      TopLevelSites.cellsOfSites_univ (F := torusFrame L s (n * L)) (n := n * L) fun _ => rfl
    show minimalAction a (finiteCells (torusFrame L (s + 1) n)) (s + 1) X =
      minimalAction a (cellsOfSites (torusFrame L s (n * L)) (Finset.univ : Finset (TorusSite (n * L)))) (s + 1)
        (readAtLevel (torusFrame L s (n * L)) (s + 1) (restrictToTorus (n * L) X))
    rw [hc, hread]
    exact h
abbrev _root_.YangMills.SharedProofs.p62714 := @minimalAction_eq_actionAtLevel
private def chartWeight {F : BlockFrame} (a x : ℝ) (X : F.GaugeField F.depth) (V : F.GaugeField F.top) : ℝ :=
  Real.exp (-x * minimalAction a (finiteCells F) F.depth X) *
    ∏ c ∈ innerBonds (finiteCells F) F.top, stepKernel a x X V c
private theorem coldWeight_eq_chartWeight (hla : MinimalActionTransfer) (hW : WeylIntegrationFormula)
    (hplain : KernelPlainAwayFromLumps) (ℓ : TorusLumps.StepParameters) (hfit : ℓ.Admissible)
    (hodd : Odd ℓ.side) (t : ℕ) {n : ℕ} [NeZero n] (h2 : 2 ≤ n) (x : ℝ) (V : TorusField n)
    (X : (torusFrame ℓ.side t n).GaugeField (torusFrame ℓ.side t n).depth)
    (hc : TorusFields.IsCold ℓ.threshold (restrictToTorus (n * ℓ.side) X)) :
    coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) (restrictToTorus (n * ℓ.side) X) *
        averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 (restrictToTorus (n * ℓ.side) X))
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) =
      chartWeight ℓ.coupling x X (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hA : coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) (restrictToTorus (n * ℓ.side) X) =
      Real.exp (-x * minimalAction ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
        (torusFrame ℓ.side t n).depth X) := by
    unfold coldActionWeight
    rw [dif_neg (NeZero.ne _), minimalAction_eq_actionAtLevel hla ℓ.coupling hodd h2 t X]
  rw [hA, averagedKernel_of_isCold hplain ℓ hfit x _ hc V]
  unfold chartWeight
  rw [prod_innerBonds_top hn]
  refine congrArg (HMul.hMul _) ?_
  refine Finset.prod_congr rfl fun y _ => Finset.prod_congr rfl fun i _ => ?_
  have hm : contourAverage X (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top y, i) =
      plainContourAverage ℓ.side y i (restrictToTorus (n * ℓ.side) X) :=
    contourAverage_eq_plainContourAverage hn X y i
  have hv : readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top y) i = V y i :=
    TopLevelSites.readAtLevel_torusSiteInFrame (TopLevelSites.period_top_of_extent hn) V y i
  unfold stepKernel
  simp only [hm, hv]
  rw [hW.2.1]
private theorem chartWeight_gaugeTransform {F : BlockFrame} (hgc : gaugeCovarianceStatement)
    (hL : 0 < F.blockSide) (a x : ℝ) (γ : F.Site F.depth → UnitQuaternion)
    (h1 : ∀ z, γ (cellCentre F.depth z) = 1) (X : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    chartWeight a x (BlockAverages.gaugeTransform γ X) V = chartWeight a x X V := by
  unfold chartWeight
  rw [minimalAction_gaugeTransform hgc hL a _ F.depth (by simp [BlockFrame.top]) γ X]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold stepKernel
  rw [contourAverage_gaugeTransform hgc hL γ h1 X c]
private theorem chartWeight_eq {F : BlockFrame} (a x : ℝ) (X : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    chartWeight a x X V = Real.exp (-x * blockEnergy a (finiteCells F) F.depth X V) *
      ∏ c ∈ innerBonds (finiteCells F) F.top, (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ := by
  have hk : ∀ c, stepKernel a x X V c =
      Real.exp (-(a * x) * blockFit X V c) * (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ := by
    intro c
    unfold stepKernel haarCharacterMean blockFit
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc, ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring
  unfold chartWeight blockEnergy
  simp only [hk]
  rw [Finset.prod_mul_distrib, ← mul_assoc, ← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
  congr 2
  ring
private theorem exp_neg_energy_le_chartWeight {F : BlockFrame} (hW : WeylIntegrationFormula) {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (X : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    Real.exp (-x * blockEnergy a (finiteCells F) F.depth X V) ≤ chartWeight a x X V := by
  rw [chartWeight_eq]
  have h1 : (1 : ℝ) ≤ ∏ c ∈ innerBonds (finiteCells F) F.top, (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ := by
    calc (1 : ℝ) = ∏ _c ∈ innerBonds (finiteCells F) F.top, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun c _ => by
        have hs : 0 ≤ a * x * ‖contourAverage X c‖ := by positivity
        exact (one_le_inv₀ (haarLaplace_pos hW hs)).mpr (haarLaplace_le_one hW hs)
  have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-x * blockEnergy a (finiteCells F) F.depth X V)).le
  simpa using this
private def contourAverageBound (F : BlockFrame) : ℝ :=
  ‖(1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)‖ * ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ)
private theorem contourAverageBound_nonneg (F : BlockFrame) : 0 ≤ contourAverageBound F :=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one)
private theorem norm_contourAverage_le {F : BlockFrame} {j : ℕ} (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) : ‖contourAverage X c‖ ≤ contourAverageBound F := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage contourAverageBound
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine norm_sum_le_of_le _ fun h _ => norm_sum_le_of_le _ fun π _ => ?_
  rw [norm_unitQuaternion]
private theorem exists_chartWeight_upper {F : BlockFrame} (hW : WeylIntegrationFormula) {a : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x →
      ∀ (X : F.GaugeField F.depth) (V : F.GaugeField F.top),
        chartWeight a x X V ≤
          M * Real.exp (-x * blockEnergy a (finiteCells F) F.depth X V) * Real.exp (x * (δ * D)) := by
  set B : ℕ := (innerBonds (finiteCells F) F.top).card with hB
  refine ⟨B * (a * contourAverageBound F),
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha.le (contourAverageBound_nonneg F)), fun δ hδ => ?_⟩
  obtain ⟨m, hm, hfl⟩ := exists_haarLaplace_lower hW hδ
  refine ⟨(m⁻¹) ^ B, by positivity, fun x hx X V => ?_⟩
  rw [chartWeight_eq]
  have hterm : ∀ c ∈ innerBonds (finiteCells F) F.top, (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ ≤
      m⁻¹ * Real.exp (x * (δ * (a * contourAverageBound F))) := by
    intro c _
    have hs : 0 ≤ a * x * ‖contourAverage X c‖ := by positivity
    have h1 := hfl _ hs
    have h2 : 0 < m * Real.exp (-(a * x * ‖contourAverage X c‖ * δ)) := mul_pos hm (Real.exp_pos _)
    have h3 : (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ ≤
        (m * Real.exp (-(a * x * ‖contourAverage X c‖ * δ)))⁻¹ := inv_anti₀ h2 h1
    refine h3.trans ?_
    rw [mul_inv, ← Real.exp_neg, neg_neg]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h4 := norm_contourAverage_le (F := F) X c
    have h5 : 0 ≤ a * x * δ := by positivity
    have := mul_le_mul_of_nonneg_left h4 h5
    nlinarith
  have hprod : ∏ c ∈ innerBonds (finiteCells F) F.top, (haarLaplace (a * x * ‖contourAverage X c‖))⁻¹ ≤
      (m⁻¹) ^ B * Real.exp (x * (δ * (B * (a * contourAverageBound F)))) := by
    calc _ ≤ ∏ _c ∈ innerBonds (finiteCells F) F.top,
          (m⁻¹ * Real.exp (x * (δ * (a * contourAverageBound F)))) :=
          Finset.prod_le_prod (fun c _ => by
            have hs : 0 ≤ a * x * ‖contourAverage X c‖ := by positivity
            exact (inv_pos.mpr (haarLaplace_pos hW hs)).le) hterm
      _ = _ := by
        rw [Finset.prod_const, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have h0 := mul_le_mul_of_nonneg_left hprod
    (Real.exp_pos (-x * blockEnergy a (finiteCells F) F.depth X V)).le
  calc _ ≤ _ := h0
    _ = _ := by ring
end Weight
section Chart
variable {F : BlockFrame}
private def chartFieldAt (V : F.GaugeField F.top) (w : StepVariable (finiteCells F)) : F.GaugeField F.depth :=
  chartedField (stepCoordinates w) V
private theorem continuous_chartFieldAt (V : F.GaugeField F.top) : Continuous (chartFieldAt (F := F) V) := by
  classical
  refine continuous_pi fun x => continuous_pi fun i => ?_
  have hco : Continuous fun w : StepVariable (finiteCells F) => stepCoordinates w x i := by
    unfold stepCoordinates
    by_cases h : (x, i) ∈ chordBonds (finiteCells F)
    · simp only [dif_pos h]
      exact ClusterExpansionOfAStep.continuous_toImaginary.comp (continuous_apply _)
    · simp only [dif_neg h]
      exact continuous_const
  unfold chartFieldAt chartedField
  by_cases h1 : IsCrossingBond (x, i)
  · simp only [if_pos h1]
    exact (continuous_expUnit.comp hco).mul continuous_const
  · simp only [if_neg h1]
    by_cases h2 : IsAxialTreeBond (x, i)
    · simp only [if_pos h2]
      exact continuous_const
    · simp only [if_neg h2]
      exact continuous_expUnit.comp hco
private def imaginaryCoords (q : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK]
private theorem toImaginary_imaginaryCoords (q : imaginaryQuaternions) : toImaginary (imaginaryCoords q) = q := by
  apply Subtype.ext
  have hq : (q : ℍ[ℝ]).re = 0 := q.2
  ext <;> simp [toImaginary, imaginaryCoords, hq]
private theorem imaginaryCoords_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryCoords (toImaginary v) = v := by
  ext i
  fin_cases i <;> simp [toImaginary, imaginaryCoords]
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
private theorem toImaginary_sub (u v : EuclideanSpace ℝ (Fin 3)) :
    ((toImaginary u : imaginaryQuaternions) : ℍ[ℝ]) - ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) =
      ((toImaginary (u - v) : imaginaryQuaternions) : ℍ[ℝ]) := by
  ext
  · show (0 : ℝ) - 0 = 0
    simp
  · show u 0 - v 0 = (u - v) 0
    simp
  · show u 1 - v 1 = (u - v) 1
    simp
  · show u 2 - v 2 = (u - v) 2
    simp
private theorem expUnit_injective_of_norm_le_pi {u v : imaginaryQuaternions} (hu : ‖(u : ℍ[ℝ])‖ ≤ Real.pi)
    (hv : ‖(v : ℍ[ℝ])‖ < Real.pi) (h : expUnit u = expUnit v) : u = v := by
  rcases lt_or_eq_of_le hu with h1 | h1
  · exact TopLevelSites.expUnit_injective_of_norm_lt_pi h1 hv h
  · exfalso
    have e1 := congrArg (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re) h
    simp only [TopLevelSites.re_expUnit, h1, Real.cos_pi] at e1
    have e2 := Real.cos_lt_cos_of_nonneg_of_le_pi (norm_nonneg (v : ℍ[ℝ])) le_rfl hv
    rw [Real.cos_pi] at e2
    linarith
private theorem toImaginary_eq_of_isMin (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {a : ℝ}
    (V : F.GaugeField F.top) (w₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hw₀ : ∀ b ∈ chordBonds (finiteCells F), ‖((w₀ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi)
    (hone : ∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        AgreeOnBonds (finiteCells F) F.depth W' (BlockAverages.gaugeTransform γ (chartedField w₀ V)))
    (w : StepVariable (finiteCells F)) (hw : ∀ b, ‖w b‖ ≤ Real.pi)
    (hmin : ∀ W'', blockEnergy a (finiteCells F) F.depth (chartFieldAt V w) V ≤
      blockEnergy a (finiteCells F) F.depth W'' V)
    (b : ↥(chordBonds (finiteCells F))) : toImaginary (w b) = w₀ b.1.1 b.1.2 := by
  classical
  obtain ⟨γ, hγ, hsame⟩ := hone _ hmin
  have htreeval : ∀ (u : F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : F.Site F.depth × Fin 4),
      IsAxialTreeBond c → chartedField u V c.1 c.2 = 1 := by
    intro u c hc
    unfold chartedField
    rw [if_neg hc.1, if_pos hc]
  have hb : ∀ c ∈ innerBonds (finiteCells F) F.depth, IsAxialTreeBond c →
      γ c.1 = γ (c.1 + BlockAverages.unitStep F.depth c.2) := by
    intro c hcS ht
    have h := hsame c hcS
    unfold chartFieldAt at h
    rw [htreeval _ c ht] at h
    unfold BlockAverages.gaugeTransform at h
    rw [htreeval w₀ c ht, mul_one] at h
    exact mul_inv_eq_one.mp h.symm
  have hone' := TopLevelSites.gauge_eq_one_on_sites hL hs γ hγ hb
  have hsite : ∀ x ∈ sitesOfCells (finiteCells F) F.depth, γ x = 1 := by
    intro x hx
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.mp hx
    rw [TopLevelSites.top_sub_depth, pow_one] at hh
    exact hone' y hy h hh
  obtain ⟨⟨x, i⟩, hc⟩ := b
  have hbS := (Finset.mem_filter.mp hc).1
  have hnt := (Finset.mem_filter.mp hc).2
  have hx1 : x ∈ sitesOfCells (finiteCells F) F.depth :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hbS).1).1
  have hx2 : x + BlockAverages.unitStep F.depth i ∈ sitesOfCells (finiteCells F) F.depth :=
    (Finset.mem_filter.mp hbS).2
  have h := hsame _ hbS
  simp only [BlockAverages.gaugeTransform, hsite x hx1, hsite _ hx2, one_mul, inv_one, mul_one] at h
  have hco : stepCoordinates w x i = toImaginary (w ⟨(x, i), hc⟩) := by
    unfold stepCoordinates
    rw [dif_pos hc]
  have n1 : ‖((toImaginary (w ⟨(x, i), hc⟩) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ Real.pi := by
    rw [norm_toImaginary]
    exact hw _
  apply expUnit_injective_of_norm_le_pi n1 (hw₀ _ hc)
  unfold chartFieldAt chartedField at h
  rw [hco] at h
  by_cases hcr : IsCrossingBond (x, i)
  · rw [if_pos hcr, if_pos hcr] at h
    exact mul_right_cancel h
  · rw [if_neg hcr, if_neg hcr, if_neg hnt, if_neg hnt] at h
    exact h
private theorem haarLogDensity_nonneg' (v : EuclideanSpace ℝ (Fin 3)) : 0 ≤ haarLogDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.haarLogDensity_nonneg <;> assumption
private theorem haarLogDensity_pos' {v : EuclideanSpace ℝ (Fin 3)} (h : ‖v‖ < Real.pi) : 0 < haarLogDensity v := by apply _root_.YangMills.Construction.StepSettings.PotentialFactorization.haarLogDensity_pos <;> assumption
private theorem norm_lt_pi_of_haarLogDensity_ne_zero {v : EuclideanSpace ℝ (Fin 3)} (h : haarLogDensity v ≠ 0) :
    ‖v‖ < Real.pi := by
  by_contra hc
  exact h (by unfold haarLogDensity; rw [if_neg hc])
private theorem measurable_cutoffFactor' {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) {α : Type}
    [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) :
    Measurable fun a => cutoffFactor ρ p (f a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_cutoffFactor <;> assumption
private theorem cutoffFactor_mem_unitInterval {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.cutoffFactor_nonneg_le_one <;> assumption
private theorem cutoffFactor_eq_one {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (hu : 0 ≤ u)
    (h : u < ρ / 2) : cutoffFactor ρ p u = 1 := by
  unfold cutoffFactor
  rw [if_pos (by linarith), hcut.vanish_small u hu (by linarith)]
  simp
private def energyAt (a : ℝ) (V : F.GaugeField F.top) (w : StepVariable (finiteCells F)) : ℝ :=
  blockEnergy a (finiteCells F) F.depth (chartFieldAt V w) V
set_option maxHeartbeats 400000 in
private theorem tendsto_log_chart_indicator_sub_cutoff (hW : WeylIntegrationFormula) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {a : ℝ} (ha : 0 < a) (V : F.GaugeField F.top)
    (w₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hchart : IsMinimizingChart a (finiteCells F) V 1 w₀)
    (hone : ∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        AgreeOnBonds (finiteCells F) F.depth W' (BlockAverages.gaugeTransform γ (chartedField w₀ V)))
    (hgi : Integrable fun w : StepVariable (finiteCells F) => ∏ b, haarLogDensity (w b))
    (O : Set (StepVariable (finiteCells F))) (hO : IsOpen O)
    (hwO : (fun b : ↥(chordBonds (finiteCells F)) => imaginaryCoords (w₀ b.1.1 b.1.2)) ∈ O)
    {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) (hρ : 0 < ρ)
    (fr : ↥(chordBonds (finiteCells F)) → imaginaryQuaternions) (hfr : ∀ b, fr b = w₀ b.1.1 b.1.2) :
    Filter.Tendsto (fun x => Real.log (∫ w : StepVariable (finiteCells F), O.indicator (fun _ => (1 : ℝ)) w *
          (chartWeight a x (chartFieldAt V w) V * ∏ b, haarLogDensity (w b))) -
        Real.log (∫ w : StepVariable (finiteCells F),
          (∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
            ((fr b : imaginaryQuaternions) : ℍ[ℝ])‖) *
            (chartWeight a x (chartFieldAt V w) V * ∏ b, haarLogDensity (w b))))
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨wS, hwS⟩ : ∃ wS : StepVariable (finiteCells F), wS = fun b => imaginaryCoords (w₀ b.1.1 b.1.2) :=
    ⟨_, rfl⟩
  rw [← hwS] at hwO
  have hcoord : stepCoordinates wS = w₀ := by
    funext x i
    unfold stepCoordinates
    by_cases h : (x, i) ∈ chordBonds (finiteCells F)
    · rw [dif_pos h, hwS]
      exact toImaginary_imaginaryCoords _
    · rw [dif_neg h]
      exact (hchart.1 (x, i) h).symm
  have hEc : Continuous (energyAt a V) := (continuous_blockEnergy' a _ F.depth V).comp (continuous_chartFieldAt V)
  have hmin : ∀ W'', energyAt a V wS ≤ blockEnergy a (finiteCells F) F.depth W'' V := by
    intro W''
    show blockEnergy a _ F.depth (chartedField (stepCoordinates wS) V) V ≤ _
    rw [hcoord]
    exact hchart.2.2 W''
  have hnorm₀ : ∀ b ∈ chordBonds (finiteCells F), ‖((w₀ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi :=
    fun b hb => lt_of_le_of_lt (hchart.2.1 b hb) (by linarith [Real.pi_gt_three])
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp hO wS hwO
  obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₁ ∧ ε ≤ ρ / 2 :=
    ⟨min ε₁ (ρ / 2), lt_min hε₁ (half_pos hρ), min_le_left _ _, min_le_right _ _⟩
  have hNO : Metric.ball wS ε ⊆ O := (Metric.ball_subset_ball hεa).trans hball
  have hK : IsCompact (Metric.closedBall (0 : StepVariable (finiteCells F)) Real.pi \ Metric.ball wS ε) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  obtain ⟨c, hc, hgap⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Metric.closedBall (0 : StepVariable (finiteCells F)) Real.pi \
      Metric.ball wS ε, energyAt a V wS + c ≤ energyAt a V w := by
    rcases (Metric.closedBall (0 : StepVariable (finiteCells F)) Real.pi \
      Metric.ball wS ε).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun w hw => by rw [he] at hw; exact hw.elim⟩
    · obtain ⟨w₁, hw₁, hm⟩ := hK.exists_isMinOn hne hEc.continuousOn
      have hlt : energyAt a V wS < energyAt a V w₁ := by
        refine lt_of_le_of_ne (hmin _) fun heq => ?_
        have hmin₁ : ∀ W'', blockEnergy a (finiteCells F) F.depth (chartFieldAt V w₁) V ≤
            blockEnergy a (finiteCells F) F.depth W'' V := by
          intro W''
          have h := hmin W''
          rw [heq] at h
          exact h
        have hb : ∀ b, ‖w₁ b‖ ≤ Real.pi := by
          have h1 : ‖w₁‖ ≤ Real.pi := mem_closedBall_zero_iff.mp hw₁.1
          exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mp h1
        have hu := toImaginary_eq_of_isMin hL hs V w₀ hnorm₀ hone w₁ hb hmin₁
        have hw : w₁ = wS := by
          funext b
          rw [hwS]
          show w₁ b = imaginaryCoords (w₀ b.1.1 b.1.2)
          rw [← hu b, imaginaryCoords_toImaginary]
        exact hw₁.2 (by rw [hw]; exact Metric.mem_ball_self hε)
      exact ⟨energyAt a V w₁ - energyAt a V wS, sub_pos.mpr hlt, fun w hw => by
        have h := isMinOn_iff.mp hm w hw
        linarith⟩
  obtain ⟨ε₂, hε₂, hnear⟩ := Metric.continuous_iff.mp hEc wS (c / 4) (by positivity)
  obtain ⟨ε', hε', hε'a, hε'b, hε'c⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ ε₂ ∧ ε' ≤ 1 :=
    ⟨min (min ε ε₂) 1, lt_min (lt_min hε hε₂) one_pos, (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  have hN'N : Metric.ball wS ε' ⊆ Metric.ball wS ε := Metric.ball_subset_ball hε'a
  obtain ⟨D, hD, hceil⟩ := exists_chartWeight_upper (F := F) hW ha
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * D ≤ c / 4 := by
    refine ⟨c / (4 * (D + 1)), by positivity, ?_⟩
    have h1 : c / (4 * (D + 1)) * (D + 1) = c / 4 := by
      field_simp
    have h2 : 0 < c / (4 * (D + 1)) := by positivity
    nlinarith
  obtain ⟨M, hM, hcl⟩ := hceil δ hδ
  have hg0 : ∀ w : StepVariable (finiteCells F), 0 ≤ ∏ b, haarLogDensity (w b) := fun w =>
    Finset.prod_nonneg fun b _ => haarLogDensity_nonneg' _
  have hgm : Continuous haarCharacterMean := by
    have e : haarCharacterMean = partitionFn := funext fun s => (hW.2.1 s).symm
    rw [e]
    exact ClusterExpansionOfAStep.continuous_partitionFn
  have hdist : ∀ (w : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))),
      ‖w b - wS b‖ ≤ dist w wS :=
    fun w b => by
      rw [← dist_eq_norm]
      exact dist_le_pi_dist w wS b
  have hP0 : ∀ x : ℝ, 0 < x → ∀ w : StepVariable (finiteCells F), 0 ≤ chartWeight a x (chartFieldAt V w) V := by
    intro x hx w
    exact (Real.exp_pos _).le.trans (exp_neg_energy_le_chartWeight hW ha hx _ V)
  have hPm : ∀ x : ℝ, 0 < x → Measurable fun w : StepVariable (finiteCells F) =>
      chartWeight a x (chartFieldAt V w) V := by
    intro x _
    have h1 : Continuous fun w : StepVariable (finiteCells F) =>
        minimalAction a (finiteCells F) F.depth (chartFieldAt V w) :=
      (continuous_minimalAction' a _ F.depth).comp (continuous_chartFieldAt V)
    have hk : ∀ c : F.Site F.top × Fin 4, Measurable fun w : StepVariable (finiteCells F) =>
        stepKernel a x (chartFieldAt V w) V c := by
      intro c
      unfold stepKernel
      have hm : Continuous fun w : StepVariable (finiteCells F) => contourAverage (chartFieldAt V w) c :=
        (continuous_contourAverage' c).comp (continuous_chartFieldAt V)
      have hnum : Continuous fun w : StepVariable (finiteCells F) =>
          Real.exp (a * x * (contourAverage (chartFieldAt V w) c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) :=
        Real.continuous_exp.comp (continuous_const.mul
          (Quaternion.continuous_re.comp (hm.mul continuous_const)))
      have hden : Continuous fun w : StepVariable (finiteCells F) =>
          haarCharacterMean (a * x * ‖contourAverage (chartFieldAt V w) c‖) :=
        hgm.comp (continuous_const.mul hm.norm)
      exact hnum.measurable.div hden.measurable
    unfold chartWeight
    exact (Real.continuous_exp.comp (continuous_const.mul h1)).measurable.mul
      (Finset.measurable_prod _ fun c _ => hk c)
  have hPb : ∀ x : ℝ, 0 < x → ∃ C : ℝ, ∀ w : StepVariable (finiteCells F),
      chartWeight a x (chartFieldAt V w) V ≤ C := by
    intro x hx
    refine ⟨M * Real.exp (-x * energyAt a V wS) * Real.exp (x * (δ * D)), fun w => (hcl x hx _ V).trans ?_⟩
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hM) (Real.exp_pos _).le
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left (hmin (chartFieldAt V w)) hx.le
    linarith
  have hu₂m : Measurable fun w : StepVariable (finiteCells F) =>
      ∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((fr b : imaginaryQuaternions) : ℍ[ℝ])‖ := by
    refine Finset.measurable_prod _ fun b _ => measurable_cutoffFactor' hcut ?_ fun _ => norm_nonneg _
    have hc1 : Continuous fun w : StepVariable (finiteCells F) =>
        ((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) :=
      continuous_subtype_val.comp (ClusterExpansionOfAStep.continuous_toImaginary.comp (continuous_apply b))
    exact (hc1.sub continuous_const).norm.measurable
  have hu₁ : ∀ w : StepVariable (finiteCells F), 0 ≤ O.indicator (fun _ => (1 : ℝ)) w ∧
      O.indicator (fun _ => (1 : ℝ)) w ≤ 1 := by
    intro w
    by_cases hw : w ∈ O
    · rw [Set.indicator_of_mem hw]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem hw]
      exact ⟨le_rfl, zero_le_one⟩
  have hu₂ : ∀ w : StepVariable (finiteCells F),
      0 ≤ ∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((fr b : imaginaryQuaternions) : ℍ[ℝ])‖ ∧
      ∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((fr b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 := by
    intro w
    exact ⟨Finset.prod_nonneg fun b _ => (cutoffFactor_mem_unitInterval hcut hρ (norm_nonneg _)).1,
      Finset.prod_le_one (fun b _ => (cutoffFactor_mem_unitInterval hcut hρ (norm_nonneg _)).1)
        fun b _ => (cutoffFactor_mem_unitInterval hcut hρ (norm_nonneg _)).2⟩
  have h1N : ∀ w ∈ Metric.ball wS ε, O.indicator (fun _ => (1 : ℝ)) w = 1 := by
    intro w hw
    exact Set.indicator_of_mem (hNO hw) _
  have h2N : ∀ w ∈ Metric.ball wS ε,
      ∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((fr b : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    intro w hw
    refine Finset.prod_eq_one fun b _ => cutoffFactor_eq_one hcut hρ (norm_nonneg _) ?_
    have e1 : fr b = toImaginary (wS b) := by
      rw [hfr b, hwS]
      exact (toImaginary_imaginaryCoords _).symm
    rw [e1, toImaginary_sub, norm_toImaginary]
    have h1 := hdist w b
    have h2 : dist w wS < ε := hw
    linarith
  have hpos : 0 < ∫ w in Metric.ball wS ε', ∏ b, haarLogDensity (w b) := by
    have hsub : Metric.ball wS ε' ⊆ Function.support fun w : StepVariable (finiteCells F) =>
        ∏ b, haarLogDensity (w b) := by
      intro w hw
      refine (Finset.prod_pos fun b _ => haarLogDensity_pos' ?_).ne'
      have h1 := hdist w b
      have h2 : dist w wS < ε' := hw
      have h3 := hε'c
      have h4 : ‖wS b‖ ≤ 1 := by
        have e : ‖wS b‖ = ‖((w₀ b.1.1 b.1.2 : imaginaryQuaternions) : ℍ[ℝ])‖ := by
          rw [← norm_toImaginary, hwS, toImaginary_imaginaryCoords]
        rw [e]
        exact hchart.2.1 b.1 b.2
      have h5 : ‖w b‖ ≤ ‖w b - wS b‖ + ‖wS b‖ := by
        have := norm_add_le (w b - wS b) (wS b)
        simpa using this
      linarith [Real.pi_gt_three]
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgi.integrableOn,
      Set.inter_eq_self_of_subset_right hsub]
    exact Metric.measure_ball_pos _ _ hε'
  have hlow : ∀ x : ℝ, 0 < x → ∀ w ∈ Metric.ball wS ε',
      Real.exp (-x * (energyAt a V wS + c / 4)) ≤ chartWeight a x (chartFieldAt V w) V := by
    intro x hx w hw
    refine (Real.exp_le_exp.mpr ?_).trans (exp_neg_energy_le_chartWeight hW ha hx _ V)
    have h2 : dist w wS < ε₂ := lt_of_lt_of_le hw hε'b
    have h3 := hnear w h2
    rw [Real.dist_eq] at h3
    have h4 : energyAt a V w ≤ energyAt a V wS + c / 4 := by
      have := (abs_lt.mp h3).2
      linarith
    have := mul_le_mul_of_nonneg_left h4 hx.le
    show -x * (energyAt a V wS + c / 4) ≤ -x * energyAt a V w
    linarith
  have hup : ∀ x : ℝ, 0 < x → ∀ w, w ∉ Metric.ball wS ε → (∏ b, haarLogDensity (w b)) ≠ 0 →
      chartWeight a x (chartFieldAt V w) V ≤ M * Real.exp (-x * (energyAt a V wS + 3 * c / 4)) := by
    intro x hx w hwN hgw
    have hb : ∀ b, ‖w b‖ ≤ Real.pi := fun b =>
      (norm_lt_pi_of_haarLogDensity_ne_zero fun h => hgw (Finset.prod_eq_zero (Finset.mem_univ b) h)).le
    have hwK : w ∈ Metric.closedBall (0 : StepVariable (finiteCells F)) Real.pi \ Metric.ball wS ε :=
      ⟨mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr hb), hwN⟩
    have hE := hgap w hwK
    refine (hcl x hx _ V).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
    have h1 : 0 ≤ x * (energyAt a V w - energyAt a V wS - 3 * c / 4 - δ * D) := mul_nonneg hx.le (by linarith)
    show -x * energyAt a V w + x * (δ * D) ≤ -x * (energyAt a V wS + 3 * c / 4)
    linarith
  have hu₁m : Measurable (O.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hO.measurableSet
  have hNm : MeasurableSet (Metric.ball wS ε) := Metric.isOpen_ball.measurableSet
  have hN'm : MeasurableSet (Metric.ball wS ε') := Metric.isOpen_ball.measurableSet
  have key := tendsto_log_sub_log_of_gap (Ω := StepVariable (finiteCells F)) volume _ hg0 hgi
    (fun x w => chartWeight a x (chartFieldAt V w) V) hP0 hPm hPb _ _ hu₁m hu₂m hu₁ hu₂
    (Metric.ball wS ε) (Metric.ball wS ε') hNm h1N h2N hN'm hN'N hpos (energyAt a V wS) c M hc hM hlow hup
  exact key
end Chart
section Main
private theorem isOpen_setOf_isCold (s : ℝ) (m : ℕ) [NeZero m] :
    IsOpen {W : TorusField m | TorusFields.IsCold s W} := by
  have e : {W : TorusField m | TorusFields.IsCold s W} =
      ⋂ (x : TorusSite m) (μ : Fin 4) (ν : Fin 4) (_ : μ < ν), {W : TorusField m | curvature W x μ ν < s} := by
    ext W
    simp [TorusFields.IsCold]
  rw [e]
  exact isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun μ =>
    isOpen_iInter_of_finite fun ν => isOpen_iInter_of_finite fun _ =>
      isOpen_lt (continuous_curvature x μ ν) continuous_const
private theorem continuous_actionAtLevel' (a : ℝ) (L t m : ℕ) [NeZero m] :
    Continuous fun W : TorusField m => actionAtLevel a L t Finset.univ W := by
  cases t with
  | zero => exact continuous_wilsonAction _
  | succ t =>
    have h : Continuous fun W : TorusField m => readAtLevel (torusFrame L t m) (t + 1) W :=
      continuous_pi fun x => continuous_pi fun i => continuous_apply_apply _ i
    exact (continuous_minimalAction' a _ (t + 1)).comp h
private theorem continuous_restrictToTorus' {F : BlockFrame} {m : ℕ} :
    Continuous fun X : F.GaugeField F.depth => restrictToTorus m X :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply_apply _ _
private theorem partitionFn_nonneg' (s : ℝ) : 0 ≤ partitionFn s :=
  integral_nonneg fun _ => (Real.exp_pos _).le
private theorem stepCoordinates_imaginaryCoords {F : BlockFrame} {a ρ : ℝ} {V : F.GaugeField F.top}
    {w₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions} (h : IsMinimizingChart a (finiteCells F) V ρ w₀) :
    stepCoordinates (fun b : ↥(chordBonds (finiteCells F)) => imaginaryCoords (w₀ b.1.1 b.1.2)) = w₀ := by
  classical
  funext x i
  unfold stepCoordinates
  by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos hb]
    exact toImaginary_imaginaryCoords _
  · rw [dif_neg hb]
    exact (h.1 (x, i) hb).symm
set_option maxHeartbeats 1000000 in
private theorem tendsto_log_coldStepIntegral_sub (hgf : HaarIntegralEqStepIntegral) (hW : WeylIntegrationFormula)
    (hgc : gaugeCovarianceStatement) (hla : MinimalActionTransfer)
    (hker : BondKernelBorel) (hplain : KernelPlainAwayFromLumps)
    (ℓ : TorusLumps.StepParameters) (hfit : ℓ.Admissible) (hodd : Odd ℓ.side) (ha : 0 < ℓ.coupling)
    (hσ : 0 < ℓ.threshold) (t : ℕ) {n : ℕ} [NeZero n]
    (h2 : 2 ≤ n) {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) (hρ : 0 < ρ) (ρA : ℝ) (V : TorusField n)
    (w₀ : (torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth → Fin 4 → imaginaryQuaternions)
    (hchart : IsMinimizingChart ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) 1 w₀)
    (hcoord : minimizingCoordinates ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) ρA = w₀)
    (hcold : BlockAverages.IsCold (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).depth
      (ℓ.threshold / 8)
      (chartedField w₀ (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
    (hone : ∀ W', (∀ W'', blockEnergy ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
          (torusFrame ℓ.side t n).depth W'
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) ≤
        blockEnergy ℓ.coupling (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).depth W''
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) →
      ∃ γ : (torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth → UnitQuaternion,
        (∀ z, γ (cellCentre (torusFrame ℓ.side t n).depth z) = 1) ∧
        AgreeOnBonds (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).depth W'
          (BlockAverages.gaugeTransform γ
            (chartedField w₀ (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))) :
    Filter.Tendsto (fun x => Real.log (coldStepIntegral ℓ t x n V) -
        Real.log (interpolatedStepIntegral 0 ℓ.coupling ρA ρ x 0 p (localFamilyOfDensity 0)
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
      Filter.atTop (nhds 0) := by
  classical
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hs : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun _ => h2
  have hodd' : Odd (torusFrame ℓ.side t n).blockSide := hodd
  have hgi : Integrable fun w : StepVariable (finiteCells (torusFrame ℓ.side t n)) =>
      ∏ b, haarLogDensity (w b) := by
    have h1 := hgf ℓ.side t n hodd h2 (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
      (fun _ => 1) measurable_const (fun _ => zero_le_one) (fun _ _ _ => rfl)
    by_contra hni
    have h3 : (∫ w : StepVariable (finiteCells (torusFrame ℓ.side t n)),
        (1 : ℝ) * ∏ b, haarLogDensity (w b)) = 0 := by
      simp only [one_mul]
      exact integral_undef hni
    rw [h3] at h1
    simp at h1
  have hO : IsOpen {w : StepVariable (finiteCells (torusFrame ℓ.side t n)) | TorusFields.IsCold ℓ.threshold
      (restrictToTorus (n * ℓ.side)
        (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))} :=
    (isOpen_setOf_isCold ℓ.threshold (n * ℓ.side)).preimage
      (continuous_restrictToTorus'.comp (continuous_chartFieldAt _))
  have hwO : (fun b : ↥(chordBonds (finiteCells (torusFrame ℓ.side t n))) => imaginaryCoords (w₀ b.1.1 b.1.2)) ∈
      {w : StepVariable (finiteCells (torusFrame ℓ.side t n)) | TorusFields.IsCold ℓ.threshold
        (restrictToTorus (n * ℓ.side)
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))} := by
    show TorusFields.IsCold ℓ.threshold (restrictToTorus (n * ℓ.side) (chartedField (stepCoordinates _)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
    rw [stepCoordinates_imaginaryCoords hchart]
    have h8 : BlockAverages.IsCold (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).depth ℓ.threshold
        (chartedField w₀ (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) :=
      fun q hq => (hcold q hq).trans (by linarith)
    exact isCold_restrictToTorus hodd' hs hn h8
  have hfr : ∀ b : ↥(chordBonds (finiteCells (torusFrame ℓ.side t n))),
      interpolatedFrame 0 ℓ.coupling ρA 0 b.1
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) = w₀ b.1.1 b.1.2 := by
    intro b
    unfold interpolatedFrame
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    show minimizingBondCoordinate ℓ.coupling ρA (finiteCells (torusFrame ℓ.side t n)) b.1
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) = _
    unfold minimizingBondCoordinate
    rw [hcoord]
  have key := tendsto_log_chart_indicator_sub_cutoff hW hodd' hs ha
    (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w₀ hchart
    hone hgi _ hO hwO hcut hρ
    (fun b => interpolatedFrame 0 ℓ.coupling ρA 0 b.1
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) hfr
  refine key.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  have hB : ∫ w : StepVariable (finiteCells (torusFrame ℓ.side t n)),
      (∏ b, cutoffFactor ρ p ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((interpolatedFrame 0 ℓ.coupling ρA 0 b.1
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) : imaginaryQuaternions) : ℍ[ℝ])‖) *
        (chartWeight ℓ.coupling x
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w)
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) * ∏ b, haarLogDensity (w b)) =
      interpolatedStepIntegral 0 ℓ.coupling ρA ρ x 0 p (localFamilyOfDensity 0)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
    unfold interpolatedStepIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show _ = interpolatedStepIntegrand 0 ℓ.coupling ρA ρ x 0 p (localFamilyOfDensity 0)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w
    unfold interpolatedStepIntegrand chartWeight lowerBoltzmann chartFieldAt
    have hc0 : ∑ y ∈ sitesOfCells (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).depth,
        subtractTrivial (localFamilyOfDensity 0) (torusFrame ℓ.side t n) y
          (chartedField (stepCoordinates w) (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) =
          0 := by
      simp [ColdStepAtMirrorFrames.subtractTrivial, localFamilyOfDensity]
    rw [hc0, add_zero]
    ring
  have hGm : Measurable fun W : TorusField (n * ℓ.side) =>
      Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'}
        (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
          averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) W := by
    refine Measurable.indicator ?_ (isOpen_setOf_isCold ℓ.threshold (n * ℓ.side)).measurableSet
    have e : (fun W' : TorusField (n * ℓ.side) => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W') =
        fun W' => Real.exp (-x * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W') := by
      funext W'
      unfold coldActionWeight
      rw [dif_neg (NeZero.ne _)]
    have h1 : Measurable fun W' : TorusField (n * ℓ.side) =>
        coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' := by
      rw [e]
      have hc : Continuous fun W' : TorusField (n * ℓ.side) =>
          -x * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W' :=
        continuous_const.mul (continuous_actionAtLevel' ℓ.coupling ℓ.side t (n * ℓ.side))
      exact hc.measurable.exp
    obtain ⟨-, -, -, -, -, -, hk, -⟩ := hker ℓ x n
    have h3 : Measurable fun W : TorusField (n * ℓ.side) => (W, V) := measurable_id.prodMk measurable_const
    have hkey : ∀ Fn : TorusField (n * ℓ.side) → TorusField n → ℝ,
        Measurable (fun q : TorusField (n * ℓ.side) × TorusField n => Fn q.1 q.2) →
        Measurable fun W : TorusField (n * ℓ.side) => Fn W V := fun Fn hF => hF.comp h3
    exact h1.mul (hkey (fun W V' => averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V')) hk)
  have hG0 : ∀ W : TorusField (n * ℓ.side), 0 ≤
      Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'}
        (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
          averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) W := by
    intro W
    refine Set.indicator_nonneg (fun W' hW' => ?_) W
    have hA : 0 ≤ coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' := by
      unfold coldActionWeight
      rw [dif_neg (NeZero.ne _)]
      exact (Real.exp_pos _).le
    refine mul_nonneg hA ?_
    rw [averagedKernel_of_isCold hplain ℓ hfit x W' hW' V]
    exact Finset.prod_nonneg fun y _ => Finset.prod_nonneg fun i _ =>
      div_nonneg (Real.exp_pos _).le (partitionFn_nonneg' _)
  have htie := fun X hc => coldWeight_eq_chartWeight hla hW hplain ℓ hfit hodd t h2 x V X hc
  have hGinv : ∀ (γ : (torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth → UnitQuaternion),
      (∀ z, γ (cellCentre (torusFrame ℓ.side t n).depth z) = 1) →
      ∀ X : (torusFrame ℓ.side t n).GaugeField (torusFrame ℓ.side t n).depth,
        Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'}
          (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
            averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
          (restrictToTorus _ (BlockAverages.gaugeTransform γ X)) =
        Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'}
          (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
            averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
          (restrictToTorus _ X) := by
    intro γ h1 X
    by_cases hc : TorusFields.IsCold ℓ.threshold (restrictToTorus (n * ℓ.side) X)
    · have hc' : TorusFields.IsCold ℓ.threshold (restrictToTorus (n * ℓ.side) (BlockAverages.gaugeTransform γ X)) :=
        (isCold_restrictToTorus_gaugeTransform hn γ X ℓ.threshold).2 hc
      rw [Set.indicator_of_mem
          (show _ ∈ {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hc'),
        Set.indicator_of_mem (show _ ∈ {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hc),
        htie _ hc', htie _ hc]
      exact chartWeight_gaugeTransform hgc hodd.pos ℓ.coupling x γ h1 X _
    · have hc' : ¬ TorusFields.IsCold ℓ.threshold
          (restrictToTorus (n * ℓ.side) (BlockAverages.gaugeTransform γ X)) :=
        fun h => hc ((isCold_restrictToTorus_gaugeTransform hn γ X ℓ.threshold).1 h)
      rw [Set.indicator_of_notMem
          (show _ ∉ {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hc'),
        Set.indicator_of_notMem
          (show _ ∉ {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hc)]
  have hA : ∫ w : StepVariable (finiteCells (torusFrame ℓ.side t n)),
      Set.indicator {w : StepVariable (finiteCells (torusFrame ℓ.side t n)) | TorusFields.IsCold ℓ.threshold
        (restrictToTorus (n * ℓ.side)
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))}
        (fun _ => (1 : ℝ)) w *
        (chartWeight ℓ.coupling x
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w)
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) * ∏ b, haarLogDensity (w b)) =
      coldStepIntegral ℓ t x n V := by
    unfold coldStepIntegral
    rw [hgf ℓ.side t n hodd h2 (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) _
      hGm hG0 hGinv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : TorusFields.IsCold ℓ.threshold (restrictToTorus (n * ℓ.side)
        (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))
    · have e1 := Set.indicator_of_mem
        (show w ∈ {w : StepVariable (finiteCells (torusFrame ℓ.side t n)) | TorusFields.IsCold ℓ.threshold
          (restrictToTorus (n * ℓ.side)
            (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))} from hw)
        (fun _ => (1 : ℝ))
      have e2 := Set.indicator_of_mem
        (show restrictToTorus (n * ℓ.side)
            (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w) ∈
          {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hw)
        (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
          averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
      have e3 := htie _ hw
      show _ * _ = Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} _
        (restrictToTorus (n * ℓ.side)
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w)) * _
      rw [e1, e2, e3, one_mul]
    · have e1 := Set.indicator_of_notMem
        (show w ∉ {w : StepVariable (finiteCells (torusFrame ℓ.side t n)) | TorusFields.IsCold ℓ.threshold
          (restrictToTorus (n * ℓ.side)
            (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w))} from hw)
        (fun _ => (1 : ℝ))
      have e2 := Set.indicator_of_notMem
        (show restrictToTorus (n * ℓ.side)
            (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w) ∉
          {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} from hw)
        (fun W' => coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
          averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W')
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
      show _ * _ = Set.indicator {W' : TorusField (n * ℓ.side) | TorusFields.IsCold ℓ.threshold W'} _
        (restrictToTorus (n * ℓ.side)
          (chartFieldAt (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) w)) * _
      rw [e1, e2, zero_mul, zero_mul]
  rw [hA, hB]
end Main
theorem coldStepLaplaceAsymptotics_holds (hgf : HaarIntegralEqStepIntegral)
    (hW : WeylIntegrationFormula) (hgc : gaugeCovarianceStatement)
    (hla : MinimalActionTransfer) (hker : BondKernelBorel)
    (hplain : KernelPlainAwayFromLumps) :
    ColdStepLaplaceAsymptotics := by
  intro a ha
  refine ⟨0, fun L hL _ c hc => ?_⟩
  refine ⟨0, fun Ct _ => ?_⟩
  refine ⟨1, one_pos, fun κ _ _ => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨c.σA, hc.positivity.2.2.2.1, fun σ hσ0 hσ p hp => ?_⟩
  refine ⟨0, fun Cs _ E _ => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨0, fun y₁ _ => ?_⟩
  intro hT hn1 ℓ hM hfit t n _ hnn
  have hLe : ℓ.side = L := hM.side_eq
  have haE : ℓ.coupling = a := hM.coupling_eq
  have hσE : ℓ.threshold = σ := hM.threshold_eq
  subst hLe
  subst haE
  subst hσE
  refine ⟨fun _ => 0, fun V hV => ?_⟩
  have h64 : 64 ≤ n := hn₀.trans hnn
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hs : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun _ => by
    show 2 ≤ n
    omega
  have hVc : IsSmallCurvature ℓ.threshold (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq (TopLevelSites.period_top_of_extent hn)]
    exact hV _ μ ν hlt
  have hcl := hc.estimates (torusFrame ℓ.side t n) ℓ.threshold _ ⟨rfl, n, h64, fun _ => rfl⟩ hσ0 hσ hVc
  obtain ⟨w₀, hw, hcold, hu⟩ := hcl.minimizer
  have hρ1 : c.ρA ≤ 1 := hc.classical.1.2.1
  have hπ : c.ρA < Real.pi := by linarith [Real.pi_gt_three]
  have hw' : IsMinimizingChart ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) c.ρA w₀ :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hw1 : IsMinimizingChart ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) 1 w₀ :=
    ⟨hw.1, fun b hb => ((hw.2.1 b hb).trans (min_le_left _ _)).trans hρ1, hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) c.ρA w := ⟨w₀, hw'⟩
  have hcoord : minimizingCoordinates ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) c.ρA = w₀ := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact TopLevelSites.minimizingChart_unique hL hs hπ hex.choose_spec hw' hu
  have key := tendsto_log_coldStepIntegral_sub hgf hW hgc hla hker hplain ℓ hfit hL (by linarith) hσ0 t
    (by omega) hp (by positivity) c.ρA V w₀ hw1 hcoord hcold hu
  exact Filter.Tendsto.congr (fun x => (sub_zero _).symm) key
end YangMills.Construction.Interpolation
end
