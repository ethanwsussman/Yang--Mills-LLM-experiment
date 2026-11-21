import YangMills.Construction.ClusterExpansionOfAStep.CostAndWideEnergy
import YangMills.Construction.LawOnABoxOfTheFlow.DensityGivenTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.DensityInTheChart
import YangMills.Construction.LawOnABoxOfTheFlow.EnergyInTheChart
import YangMills.Construction.LawOnABoxOfTheFlow.GaussianOffTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.SizeOfTheDensitiesOnAColdBox
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import YangMills.Construction.Matrices.UnitQuaternionsAsMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion ENNReal
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps TorusContours LevelAction RenormalizationStepParameters StepSettings StepCosts StepCostLocality BoxEvents
  WeightedResponses
open BlockAverages hiding unitStep gaugeTransform
open ResponseInTheExpansion hiding gaugeTransform
namespace ChartDensity
private theorem lintegral_normalize_weight {H F : Type} [MeasurableSpace H] [MeasurableSpace F]
    (μ : Measure H) [SFinite μ] (vol : Measure F) [SFinite vol]
    (Z : Set F) (hZ : MeasurableSet Z) (r : F → ℝ) (hr : Measurable r) (hr0 : ∀ ζ, 0 < r ζ)
    (hM0 : (vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ ≠ 0)
    (hMt : (vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ ≠ ∞)
    (D : H × F → ℝ≥0∞) (hD : Measurable D) (J : F → ℝ) (hJ : Measurable J) (hJ0 : ∀ ζ ∈ Z, 0 < J ζ)
    (hI : ∀ ζ ∈ Z, ∫⁻ h, D (h, ζ) ∂μ ≠ ∞) (cH N : ℝ) (hcH : 0 < cH) (hN : 0 < N)
    (Φ : F → ℝ≥0∞) (hΦ : Measurable Φ) :
    ENNReal.ofReal cH * ∫⁻ h, ∫⁻ ζ in Z, (Φ ζ * D (h, ζ)) * ENNReal.ofReal (J ζ) ∂vol ∂μ =
      ENNReal.ofReal (cH * ((vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ).toReal * N) *
        ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ * (∫⁻ h, D (h, ζ) ∂μ).toReal * (r ζ)⁻¹ * N⁻¹)
          ∂(normalize (vol.withDensity fun ζ => ENNReal.ofReal (r ζ))) := by
  set ρ : F → ℝ≥0∞ := fun ζ => ENNReal.ofReal (r ζ) with hρ
  have hρm : Measurable ρ := hr.ennreal_ofReal
  set M := (vol.withDensity ρ) Set.univ with hM
  set I : F → ℝ≥0∞ := fun ζ => ∫⁻ h, D (h, ζ) ∂μ with hIdef
  have hIm : Measurable I := hD.lintegral_prod_left'
  have hJE : Measurable fun ζ => ENNReal.ofReal (J ζ) := hJ.ennreal_ofReal
  have hψ : Measurable fun ζ => Φ ζ * ENNReal.ofReal (J ζ * (I ζ).toReal * (r ζ)⁻¹ * N⁻¹) :=
    hΦ.mul ((((hJ.mul hIm.ennreal_toReal).mul hr.inv).mul_const _).ennreal_ofReal)
  have hleft : ∫⁻ h, ∫⁻ ζ in Z, (Φ ζ * D (h, ζ)) * ENNReal.ofReal (J ζ) ∂vol ∂μ =
      ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ) * I ζ ∂vol := by
    have hjoint : AEMeasurable (Function.uncurry fun (h : H) (ζ : F) =>
        (Φ ζ * D (h, ζ)) * ENNReal.ofReal (J ζ)) (μ.prod (vol.restrict Z)) := by
      refine Measurable.aemeasurable ?_
      have h1 : Measurable fun p : H × F => Φ p.2 := hΦ.comp measurable_snd
      have h2 : Measurable fun p : H × F => ENNReal.ofReal (J p.2) := hJE.comp measurable_snd
      exact (h1.mul hD).mul h2
    rw [lintegral_lintegral_swap hjoint]
    refine lintegral_congr fun ζ => ?_
    have : ∀ h, (Φ ζ * D (h, ζ)) * ENNReal.ofReal (J ζ) = Φ ζ * ENNReal.ofReal (J ζ) * D (h, ζ) :=
      fun h => by ring
    simp_rw [this]
    exact lintegral_const_mul _ (hD.comp (measurable_id.prodMk measurable_const))
  have hright : ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ * (I ζ).toReal * (r ζ)⁻¹ * N⁻¹) ∂(normalize (vol.withDensity ρ)) =
      M⁻¹ * (ENNReal.ofReal N⁻¹ * ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ) * I ζ ∂vol) := by
    unfold normalize
    rw [Measure.restrict_smul, lintegral_smul_measure, restrict_withDensity hZ,
      lintegral_withDensity_eq_lintegral_mul _ hρm hψ, smul_eq_mul]
    congr 1
    have hpull : ENNReal.ofReal N⁻¹ * ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ) * I ζ ∂vol =
        ∫⁻ ζ in Z, ENNReal.ofReal N⁻¹ * (Φ ζ * ENNReal.ofReal (J ζ) * I ζ) ∂vol :=
      (lintegral_const_mul _ ((hΦ.mul hJE).mul hIm)).symm
    rw [hpull]
    refine setLIntegral_congr_fun hZ fun ζ hζ => ?_
    have hr1 := hr0 ζ
    have hJ1 := hJ0 ζ hζ
    have hIt := hI ζ hζ
    have e1 : J ζ * (I ζ).toReal * (r ζ)⁻¹ * N⁻¹ = J ζ * ((I ζ).toReal * ((r ζ)⁻¹ * N⁻¹)) := by ring
    simp only [Pi.mul_apply]
    rw [e1, ENNReal.ofReal_mul hJ1.le, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hIt, ENNReal.ofReal_mul (inv_pos.mpr hr1).le]
    have e2 : ρ ζ * ENNReal.ofReal (r ζ)⁻¹ = 1 := by
      rw [hρ]
      simp only
      rw [← ENNReal.ofReal_mul hr1.le, mul_inv_cancel₀ hr1.ne', ENNReal.ofReal_one]
    calc ρ ζ * (Φ ζ * (ENNReal.ofReal (J ζ) * (I ζ * (ENNReal.ofReal (r ζ)⁻¹ * ENNReal.ofReal N⁻¹))))
        = (ρ ζ * ENNReal.ofReal (r ζ)⁻¹) * (ENNReal.ofReal N⁻¹ * (Φ ζ * ENNReal.ofReal (J ζ) * I ζ)) := by ring
      _ = _ := by rw [e2, one_mul]
  rw [hleft, hright]
  have hMr : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMt
  have hc : ENNReal.ofReal (cH * M.toReal * N) = ENNReal.ofReal cH * M * ENNReal.ofReal N := by
    rw [ENNReal.ofReal_mul (mul_nonneg hcH.le ENNReal.toReal_nonneg), ENNReal.ofReal_mul hcH.le, hMr]
  have hNN : ENNReal.ofReal N * ENNReal.ofReal N⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hN.le, mul_inv_cancel₀ hN.ne', ENNReal.ofReal_one]
  have hMM : M * M⁻¹ = 1 := ENNReal.mul_inv_cancel hM0 hMt
  rw [hc]
  set L := ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (J ζ) * I ζ ∂vol
  calc ENNReal.ofReal cH * L
      = ENNReal.ofReal cH * ((M * M⁻¹) * (ENNReal.ofReal N * ENNReal.ofReal N⁻¹)) * L := by
        rw [hMM, hNN]; simp
    _ = _ := by ring
private theorem mem_unitary_of_normSq_eq_one {q : ℍ[ℝ]} (h : Quaternion.normSq q = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.UnitQuaternions.mem_unitary_of_normSq_eq_one <;> assumption
private theorem chartPoint_mem_unitary (a ζ : imaginaryQuaternions) (h : ‖ζ‖ ≤ 1) :
    chartPoint a ζ ∈ unitary ℍ[ℝ] := by
  apply mem_unitary_of_normSq_eq_one
  unfold chartPoint
  rw [map_mul, normSq_unitQuaternion, mul_one]
  have hre : (ζ : ℍ[ℝ]).re = 0 := ζ.2
  have hn : ‖ζ‖ ^ 2 = Quaternion.normSq (ζ : ℍ[ℝ]) := by
    rw [Quaternion.normSq_eq_norm_mul_self, Submodule.coe_norm]
    ring
  have h1 : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hs : Real.sqrt (1 - ‖ζ‖ ^ 2) ^ 2 = 1 - ‖ζ‖ ^ 2 := Real.sq_sqrt h1
  rw [hn] at hs h1
  rw [hn]
  simp only [Quaternion.normSq_def'] at *
  simp [hre] at *
  nlinarith
private theorem coe_toUnit {q : ℍ[ℝ]} (h : q ∈ unitary ℍ[ℝ]) : ((toUnit q : UnitQuaternion) : ℍ[ℝ]) = q := by
  unfold toUnit
  rw [dif_pos h]
private theorem chartPoint_zero (a : imaginaryQuaternions) :
    chartPoint a 0 = ((expUnit a : UnitQuaternion) : ℍ[ℝ]) := by
  unfold chartPoint
  simp
private theorem continuous_imaginaryComponent (e : Fin 3) : Continuous (imaginaryComponent e) := by apply _root_.YangMills.Construction.BoxGaussian.continuous_imaginaryComponent <;> assumption
private theorem measurable_toUnit_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X → ℍ[ℝ]) (hf : Continuous f) : Measurable fun x => toUnit (f x) := by
  classical
  let _ : MeasurableSpace ℍ[ℝ] := borel _
  have _ : BorelSpace ℍ[ℝ] := ⟨rfl⟩
  have hcl : IsClosed (unitary ℍ[ℝ] : Set ℍ[ℝ]) := isCompact_unitary_quaternion.isClosed
  have hemb : MeasurableEmbedding (Subtype.val : UnitQuaternion → ℍ[ℝ]) :=
    hcl.isClosedEmbedding_subtypeVal.measurableEmbedding (mα := TorusFields.instMeasurableSpaceUnitQuaternion)
  have hext : toUnit = Function.extend (Subtype.val : UnitQuaternion → ℍ[ℝ]) id fun _ => (1 : UnitQuaternion) := by
    funext q
    by_cases h : q ∈ unitary ℍ[ℝ]
    · have := Subtype.val_injective.extend_apply (id : UnitQuaternion → UnitQuaternion)
        (fun _ => (1 : UnitQuaternion)) (⟨q, h⟩ : UnitQuaternion)
      unfold toUnit
      rw [dif_pos h]
      exact this.symm
    · unfold toUnit
      rw [dif_neg h, Function.extend_apply']
      rintro ⟨a, ha⟩
      exact h (ha ▸ a.2)
  rw [hext]
  exact (hemb.measurable_extend measurable_id measurable_const).comp hf.measurable
variable {n : ℕ} [NeZero n]
private def gaugeInner (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) (w : InnerField o R) :
    InnerField o R :=
  fun b => g b.1.1 * w b * (g (b.1.1 + unitStep n b.1.2))⁻¹
private def ungaugeInner (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) (w : InnerField o R) :
    InnerField o R :=
  fun b => (g b.1.1)⁻¹ * w b * g (b.1.1 + unitStep n b.1.2)
private theorem ungauge_gauge (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) (w : InnerField o R) :
    ungaugeInner o R g (gaugeInner o R g w) = w := by
  funext b
  simp [ungaugeInner, gaugeInner, mul_assoc]
private theorem gauge_ungauge (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) (w : InnerField o R) :
    gaugeInner o R g (ungaugeInner o R g w) = w := by
  funext b
  simp [ungaugeInner, gaugeInner, mul_assoc]
private def gaugeInnerEquiv (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) :
    InnerField o R ≃ᵐ InnerField o R where
  toFun := gaugeInner o R g
  invFun := ungaugeInner o R g
  left_inv := ungauge_gauge o R g
  right_inv := gauge_ungauge o R g
  measurable_toFun := measurable_pi_lambda _ fun b => ((measurable_pi_apply b).const_mul _).mul_const _
  measurable_invFun := measurable_pi_lambda _ fun b => ((measurable_pi_apply b).const_mul _).mul_const _
private theorem gaugeInner_measurePreserving (o : TorusSite n) (R : ℕ) (g : TorusSite n → UnitQuaternion) :
    MeasurePreserving (gaugeInnerEquiv o R g) (innerHaar o R) (innerHaar o R) := by
  have h : ∀ b : {b : TorusBond n // b ∈ bondsTouching o R},
      MeasurePreserving (fun a : UnitQuaternion => g b.1.1 * a * (g (b.1.1 + unitStep n b.1.2))⁻¹)
        haarUnit haarUnit := fun b =>
    (measurePreserving_mul_right haarUnit _).comp (measurePreserving_mul_left haarUnit _)
  exact measurePreserving_pi (fun _ => haarUnit) (fun _ => haarUnit) h
private theorem glueField_inner {o : TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R)
    (b : {b : TorusBond n // b ∈ bondsTouching o R}) : glueField u w b.1.1 b.1.2 = w b := by
  unfold glueField
  rw [dif_pos (show (b.1.1, b.1.2) ∈ bondsTouching o R from b.2)]
private theorem glueField_outer {o : TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R)
    {b : TorusBond n} (hb : b ∉ bondsTouching o R) : glueField u w b.1 b.2 = u ⟨b, hb⟩ := by
  unfold glueField
  rw [dif_neg (show (b.1, b.2) ∉ bondsTouching o R from hb)]
private theorem restrictOuter_glueField {o : TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R) :
    restrictOuter o R (glueField u w) = u := by apply _root_.YangMills.Construction.BoxGaussian.restrictOuter_glueField <;> assumption
private theorem measurable_glueField {o : TorusSite n} {R : ℕ} (u : OuterField o R) :
    Measurable fun w : InnerField o R => glueField u w := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
  by_cases h : (x, i) ∈ bondsTouching o R
  · simp only [glueField, dif_pos h]
    exact measurable_pi_apply _
  · simp only [glueField, dif_neg h]
    exact measurable_const
private theorem mem_supBall (o z : TorusSite n) (r : ℝ) : z ∈ supBall o r ↔ (supDist z o : ℝ) ≤ r := by
  simp [supBall]
private theorem mem_bondsWithin_of_mem_bondsTouching {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) {b : TorusBond n}
    (hb : b ∈ bondsTouching o R) : b ∈ bondsWithin (supBall o (2 * R)) := by apply _root_.YangMills.SharedProofs.p15112 <;> assumption
private def gaugeOnBall (o : TorusSite n) (R : ℕ) (ε : TorusSite n → UnitQuaternion) :
    {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion :=
  fun z => ε z
private theorem extendGaugeByOne_gaugeOnBall {o : TorusSite n} {R : ℕ} {ε : TorusSite n → UnitQuaternion}
    (hε : IsSupportedGauge o R ε) : extendGaugeByOne (gaugeOnBall o R ε) = ε := by
  funext z
  unfold extendGaugeByOne
  by_cases h : z ∈ supBall o R
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h, hε z h]
private theorem isSupportedGauge_extendGaugeByOne {o : TorusSite n} {R : ℕ}
    (h : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) :
    IsSupportedGauge o R (extendGaugeByOne h) := by
  intro z hz
  unfold extendGaugeByOne
  rw [dif_neg hz]
private theorem gaugedChartField_apply (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions)
    (h : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion)
    (b : {b : TorusBond n // b ∈ bondsTouching o R}) :
    gaugedChartField o R A ζ h b = extendGaugeByOne h b.1.1 * toUnit (chartPoint (A b.1) (ζ b.1)) *
      (extendGaugeByOne h (b.1.1 + unitStep n b.1.2))⁻¹ := by
  show extendGaugeByOne h b.1.1 * glueField _ _ b.1.1 b.1.2 * (extendGaugeByOne h (b.1.1 + unitStep n b.1.2))⁻¹ = _
  rw [glueField_inner]
private theorem gaugeInner_eq_gaugedChartField {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R)
    {A ζ : TorusBond n → imaginaryQuaternions} (hζ : ∀ b, ‖ζ b‖ ≤ 1)
    {γ g : TorusSite n → UnitQuaternion} (hγ : IsSupportedGauge o R γ) {u : OuterField o R} {w : InnerField o R}
    (hc : IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))) :
    gaugeInner o R g w = gaugedChartField o R A ζ (gaugeOnBall o R fun z => g z * (γ z)⁻¹ * (g z)⁻¹) := by
  have hε : IsSupportedGauge o R fun z => g z * (γ z)⁻¹ * (g z)⁻¹ := by
    intro z hz
    simp [hγ z hz]
  funext b
  rw [gaugedChartField_apply, extendGaugeByOne_gaugeOnBall hε]
  have key : toUnit (chartPoint (A b.1) (ζ b.1)) = gaugeTransform (g * γ) (glueField u w) b.1.1 b.1.2 :=
    Subtype.ext (by
      rw [coe_toUnit (chartPoint_mem_unitary _ _ (hζ _))]
      exact (hc b.1 (mem_bondsWithin_of_mem_bondsTouching hR b.2)).symm)
  rw [key]
  simp only [gaugeTransform, gaugeInner, Pi.mul_apply, glueField_inner]
  group
private theorem isInChart_ungaugeInner {o : TorusSite n} {R : ℕ} {A ζ : TorusBond n → imaginaryQuaternions}
    (hζ : ∀ b, ‖ζ b‖ ≤ 1)
    (hoff : ∀ b, b ∉ bondsTouching o R → ζ b = 0) {g : TorusSite n → UnitQuaternion} {u : OuterField o R}
    (hbase : ∀ b ∈ bondsWithin (supBall o (2 * R)), ∀ hb : b ∉ bondsTouching o R,
      g b.1 * u ⟨b, hb⟩ * (g (b.1 + unitStep n b.2))⁻¹ = expUnit (A b))
    (h : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) :
    IsInChart (supBall o (2 * R)) A ζ
      (gaugeTransform (g * fun z => (g z)⁻¹ * (extendGaugeByOne h z)⁻¹ * g z)
        (glueField u (ungaugeInner o R g (gaugedChartField o R A ζ h)))) := by
  intro b hb
  by_cases hin : b ∈ bondsTouching o R
  · have h1 := glueField_inner u (ungaugeInner o R g (gaugedChartField o R A ζ h)) ⟨b, hin⟩
    have e : gaugeTransform (g * fun z => (g z)⁻¹ * (extendGaugeByOne h z)⁻¹ * g z)
        (glueField u (ungaugeInner o R g (gaugedChartField o R A ζ h))) b.1 b.2 =
          toUnit (chartPoint (A b) (ζ b)) := by
      simp only [gaugeTransform, Pi.mul_apply]
      rw [h1]
      simp only [ungaugeInner]
      rw [gaugedChartField_apply]
      group
    rw [e]
    exact coe_toUnit (chartPoint_mem_unitary _ _ (hζ _))
  · have h1 := glueField_outer u (ungaugeInner o R g (gaugedChartField o R A ζ h)) hin
    have hn : ¬ (b.1 ∈ supBall o R ∨ b.1 + unitStep n b.2 ∈ supBall o R) := fun hh =>
      hin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    have e1 := isSupportedGauge_extendGaugeByOne h b.1 (fun hh => hn (Or.inl hh))
    have e2 := isSupportedGauge_extendGaugeByOne h (b.1 + unitStep n b.2) (fun hh => hn (Or.inr hh))
    have e : gaugeTransform (g * fun z => (g z)⁻¹ * (extendGaugeByOne h z)⁻¹ * g z)
        (glueField u (ungaugeInner o R g (gaugedChartField o R A ζ h))) b.1 b.2 = expUnit (A b) := by
      simp only [gaugeTransform, Pi.mul_apply]
      rw [h1, e1, e2, ← hbase b hb hin]
      group
    rw [e, hoff b hin, ← chartPoint_zero]
private theorem continuous_chartPoint (a : imaginaryQuaternions) :
    Continuous fun ζ : imaginaryQuaternions => chartPoint a ζ := by
  unfold chartPoint
  refine Continuous.mul (Continuous.add ?_ continuous_subtype_val) continuous_const
  exact Quaternion.continuous_coe.comp (by fun_prop)
private theorem measurable_gaugedChartField (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) :
    Measurable fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions) =>
      gaugedChartField o R A p.2 p.1 := by
  have hext : ∀ z : TorusSite n,
      Measurable fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions) =>
        extendGaugeByOne p.1 z := by
    intro z
    by_cases h : z ∈ supBall o R
    · simp only [extendGaugeByOne, dif_pos h]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [extendGaugeByOne, dif_neg h]
      exact measurable_const
  refine measurable_pi_lambda _ fun b => ?_
  simp only [gaugedChartField_apply]
  refine ((hext _).mul (measurable_toUnit_comp _ ?_)).mul (hext _).inv
  exact (continuous_chartPoint _).comp ((continuous_apply _).comp continuous_snd)
private theorem standardBorel_gauge_prod {o : TorusSite n} {R : ℕ} :
    StandardBorelSpace (({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions)) := by
  have h1 : StandardBorelSpace ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) := inferInstance
  have h2 : StandardBorelSpace (TorusBond n → imaginaryQuaternions) := inferInstance
  exact inferInstance
private theorem law_of_density_bounds {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (A : TorusBond n → imaginaryQuaternions)
    (g : TorusSite n → UnitQuaternion) (u : OuterField o R)
    (Z : Set (TorusBond n → imaginaryQuaternions)) (hZ : MeasurableSet Z)
    (hZs : ∀ ζ ∈ Z, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    (hbase : ∀ b ∈ bondsWithin (supBall o (2 * R)), ∀ hb : b ∉ bondsTouching o R,
      g b.1 * u ⟨b, hb⟩ * (g (b.1 + unitStep n b.2))⁻¹ = expUnit (A b))
    (vol : Measure (TorusBond n → imaginaryQuaternions)) [SFinite vol]
    (cH : ℝ) (J : (TorusBond n → imaginaryQuaternions) → ℝ) (hcH : 0 < cH) (hJ : Measurable J)
    (hJ0 : ∀ ζ ∈ Z, 0 < J ζ)
    (hinj : Set.InjOn (fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions) => gaugedChartField o R A p.2 p.1) (Set.univ ×ˢ Z))
    (hchange : ∀ Φ : InnerField o R → ℝ≥0∞, Measurable Φ →
      ∫⁻ w in {w | ∃ g, ∃ ζ ∈ Z, w = gaugedChartField o R A ζ g}, Φ w ∂(innerHaar o R) =
        ENNReal.ofReal cH * ∫⁻ g, ∫⁻ ζ in Z, Φ (gaugedChartField o R A ζ g) * ENNReal.ofReal (J ζ) ∂vol
          ∂(boxGaugeHaar o R))
    (r : (TorusBond n → imaginaryQuaternions) → ℝ) (hr : Measurable r) (hr0 : ∀ ζ, 0 < r ζ)
    (hM0 : (vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ ≠ 0)
    (hMt : (vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ ≠ ∞)
    (Dt D' : InnerField o R → ℝ) (hDt : Measurable Dt) (N B : ℝ) (hN : 0 < N)
    (hD : ∀ (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ → ζ ∈ Z →
      IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w)) →
      D' w = Dt w ∧ 0 < Dt w ∧ |Real.log (Dt w) - Real.log N - Real.log (r ζ)| ≤ B) :
    ∃ (c : ℝ) (wt : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable wt ∧
      (∀ ζ ∈ Z, 0 < wt ζ ∧ |Real.log (wt ζ)| ≤ |Real.log (J ζ)| + B) ∧
      ∀ coord : InnerField o R → TorusBond n → imaginaryQuaternions,
        (∀ w ∈ {w : InnerField o R | ∃ (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
            IsSupportedGauge o R γ ∧ ζ ∈ Z ∧
            IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))},
          ∃ γ : TorusSite n → UnitQuaternion,
          IsSupportedGauge o R γ ∧ coord w ∈ Z ∧
          IsInChart (supBall o (2 * R)) A (coord w) (gaugeTransform (g * γ) (glueField u w))) →
        ∀ Φ : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞, Measurable Φ →
          ∫⁻ w in {w : InnerField o R | ∃ (γ : TorusSite n → UnitQuaternion)
              (ζ : TorusBond n → imaginaryQuaternions), IsSupportedGauge o R γ ∧ ζ ∈ Z ∧
              IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))},
              Φ (coord w) * ENNReal.ofReal (D' w) ∂(innerHaar o R) =
            ENNReal.ofReal c * ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (wt ζ)
              ∂(normalize (vol.withDensity fun ζ => ENNReal.ofReal (r ζ))) := by
  classical
  have hprob : IsProbabilityMeasure (boxGaugeHaar o R) := by
    unfold boxGaugeHaar
    infer_instance
  have hf := measurable_gaugedChartField o R A
  set D : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Dt (ungaugeInner o R g (gaugedChartField o R A p.2 p.1))) with hDdef
  have hDm : Measurable D :=
    (hDt.comp ((gaugeInnerEquiv o R g).symm.measurable.comp hf)).ennreal_ofReal
  have hin : ∀ ζ ∈ Z, ∀ h : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion,
      D' (ungaugeInner o R g (gaugedChartField o R A ζ h)) = Dt (ungaugeInner o R g (gaugedChartField o R A ζ h)) ∧
      0 < Dt (ungaugeInner o R g (gaugedChartField o R A ζ h)) ∧
      |Real.log (Dt (ungaugeInner o R g (gaugedChartField o R A ζ h))) - Real.log N - Real.log (r ζ)| ≤ B := by
    intro ζ hζ h
    have hg : IsSupportedGauge o R fun z => (g z)⁻¹ * (extendGaugeByOne h z)⁻¹ * g z := by
      intro z hz
      simp [isSupportedGauge_extendGaugeByOne h z hz]
    exact hD _ _ ζ hg hζ (isInChart_ungaugeInner (hZs ζ hζ).1 (hZs ζ hζ).2 hbase h)
  have hpt : ∀ ζ ∈ Z, ∀ h : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion,
      N * r ζ * Real.exp (-B) ≤ Dt (ungaugeInner o R g (gaugedChartField o R A ζ h)) ∧
      Dt (ungaugeInner o R g (gaugedChartField o R A ζ h)) ≤ N * r ζ * Real.exp B := by
    intro ζ hζ h
    obtain ⟨-, hp, hb⟩ := hin ζ hζ h
    have hr1 := hr0 ζ
    rw [abs_le] at hb
    have e : Real.log (N * r ζ) = Real.log N + Real.log (r ζ) := Real.log_mul hN.ne' hr1.ne'
    constructor
    · rw [← Real.exp_log (mul_pos hN hr1), ← Real.exp_add, ← Real.exp_log hp]
      exact Real.exp_le_exp.mpr (by rw [e]; linarith [hb.1])
    · rw [← Real.exp_log (mul_pos hN hr1), ← Real.exp_add, ← Real.exp_log hp]
      exact Real.exp_le_exp.mpr (by rw [e]; linarith [hb.2])
  set I : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ := fun ζ => ∫⁻ h, D (h, ζ) ∂(boxGaugeHaar o R) with hIdef
  have hIlo : ∀ ζ ∈ Z, ENNReal.ofReal (N * r ζ * Real.exp (-B)) ≤ I ζ := by
    intro ζ hζ
    calc ENNReal.ofReal (N * r ζ * Real.exp (-B))
        = ∫⁻ _, ENNReal.ofReal (N * r ζ * Real.exp (-B)) ∂(boxGaugeHaar o R) := by simp
      _ ≤ I ζ := lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hpt ζ hζ h).1
  have hIhi : ∀ ζ ∈ Z, I ζ ≤ ENNReal.ofReal (N * r ζ * Real.exp B) := by
    intro ζ hζ
    calc I ζ ≤ ∫⁻ _, ENNReal.ofReal (N * r ζ * Real.exp B) ∂(boxGaugeHaar o R) :=
          lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hpt ζ hζ h).2
      _ = _ := by simp
  have hIt : ∀ ζ ∈ Z, I ζ ≠ ∞ := fun ζ hζ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hIhi ζ hζ)
  have hIr : ∀ ζ ∈ Z, N * r ζ * Real.exp (-B) ≤ (I ζ).toReal ∧ (I ζ).toReal ≤ N * r ζ * Real.exp B := by
    intro ζ hζ
    have hp : 0 ≤ N * r ζ * Real.exp (-B) := by have := hr0 ζ; positivity
    have hq : 0 ≤ N * r ζ * Real.exp B := by have := hr0 ζ; positivity
    constructor
    · exact (ENNReal.ofReal_le_iff_le_toReal (hIt ζ hζ)).mp (hIlo ζ hζ)
    · exact ENNReal.toReal_le_of_le_ofReal hq (hIhi ζ hζ)
  set M := (vol.withDensity fun ζ => ENNReal.ofReal (r ζ)) Set.univ with hMdef
  have hMpos : 0 < M.toReal := ENNReal.toReal_pos hM0 hMt
  refine ⟨cH * M.toReal * N, fun ζ => J ζ * (I ζ).toReal * (r ζ)⁻¹ * N⁻¹, by positivity, ?_, ?_, ?_⟩
  · have hIm : Measurable I := hDm.lintegral_prod_left'
    exact ((hJ.mul hIm.ennreal_toReal).mul hr.inv).mul_const _
  · intro ζ hζ
    have hr1 := hr0 ζ
    have hJ1 := hJ0 ζ hζ
    obtain ⟨h1, h2⟩ := hIr ζ hζ
    have hpos : 0 < N * r ζ * Real.exp (-B) := by positivity
    have hIp : 0 < (I ζ).toReal := lt_of_lt_of_le hpos h1
    set t := (I ζ).toReal * (r ζ)⁻¹ * N⁻¹ with ht
    have htp : 0 < t := by positivity
    have hNr : 0 < N * r ζ := mul_pos hN hr1
    have hte : t = (I ζ).toReal / (N * r ζ) := by
      rw [ht]
      field_simp
    have hlo : Real.exp (-B) ≤ t := by
      rw [hte, le_div_iff₀ hNr]
      linarith
    have hhi : t ≤ Real.exp B := by
      rw [hte, div_le_iff₀ hNr]
      linarith
    have hw : J ζ * (I ζ).toReal * (r ζ)⁻¹ * N⁻¹ = J ζ * t := by rw [ht]; ring
    simp only [hw]
    refine ⟨mul_pos hJ1 htp, ?_⟩
    rw [Real.log_mul hJ1.ne' htp.ne']
    have hl1 : -B ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos _) hlo
      rwa [Real.log_exp] at this
    have hl2 : Real.log t ≤ B := by
      have := Real.log_le_log htp hhi
      rwa [Real.log_exp] at this
    calc |Real.log (J ζ) + Real.log t| ≤ |Real.log (J ζ)| + |Real.log t| := abs_add_le _ _
      _ ≤ _ := by
        have := abs_le.mpr ⟨hl1, hl2⟩
        linarith
  · intro coord hcoord Φ hΦ
    set Orb : Set (InnerField o R) := {w : InnerField o R | ∃ (γ : TorusSite n → UnitQuaternion)
      (ζ : TorusBond n → imaginaryQuaternions), IsSupportedGauge o R γ ∧ ζ ∈ Z ∧
      IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))} with hOrbdef
    set Img : Set (InnerField o R) := {w | ∃ g, ∃ ζ ∈ Z, w = gaugedChartField o R A ζ g} with hImgdef
    have hOrb : Orb = gaugeInnerEquiv o R g ⁻¹' Img := by
      ext w
      constructor
      · rintro ⟨γ, ζ, hγ, hζ, hc⟩
        exact ⟨_, ζ, hζ, gaugeInner_eq_gaugedChartField hR (hZs ζ hζ).1 hγ hc⟩
      · rintro ⟨h, ζ, hζ, hw⟩
        have hw' : w = ungaugeInner o R g (gaugedChartField o R A ζ h) := by
          have := ungauge_gauge o R g w
          rw [← this]
          exact congrArg _ hw
        have hg : IsSupportedGauge o R fun z => (g z)⁻¹ * (extendGaugeByOne h z)⁻¹ * g z := by
          intro z hz
          simp [isSupportedGauge_extendGaugeByOne h z hz]
        refine ⟨_, ζ, hg, hζ, ?_⟩
        rw [hw']
        exact isInChart_ungaugeInner (hZs ζ hζ).1 (hZs ζ hζ).2 hbase h
    have hEm : MeasurableSet (Set.univ ×ˢ Z : Set (({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) ×
        (TorusBond n → imaginaryQuaternions))) :=
      MeasurableSet.univ.prod hZ
    have hsbP := standardBorel_gauge_prod (o := o) (R := R)
    have hsb := hEm.standardBorel
    let e : ↥(Set.univ ×ˢ Z : Set (({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) ×
        (TorusBond n → imaginaryQuaternions))) → InnerField o R :=
      fun p => gaugedChartField o R A p.1.2 p.1.1
    have heinj : Function.Injective e := fun p q hpq => Subtype.ext (hinj p.2 q.2 hpq)
    have hem : Measurable e := hf.comp measurable_subtype_coe
    have hemb : MeasurableEmbedding e := hem.measurableEmbedding heinj
    have hrange : Img = Set.range e := by
      ext w
      constructor
      · rintro ⟨h, ζ, hζ, rfl⟩
        exact ⟨⟨(h, ζ), Set.mem_univ _, hζ⟩, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨p.1.1, p.1.2, p.2.2, rfl⟩
    have hImgm : MeasurableSet Img := hrange ▸ hemb.measurableSet_range
    have hOrbm : MeasurableSet Orb := hOrb ▸ (gaugeInnerEquiv o R g).measurable hImgm
    let Ξ : InnerField o R → ℝ≥0∞ := Function.extend e (fun p => Φ p.1.2) 0
    have hΞ : Measurable Ξ :=
      hemb.measurable_extend (hΦ.comp (measurable_snd.comp measurable_subtype_coe)) measurable_const
    have hΞe : ∀ ζ ∈ Z, ∀ h, Ξ (gaugedChartField o R A ζ h) = Φ ζ := by
      intro ζ hζ h
      exact heinj.extend_apply (fun p => Φ p.1.2) 0 ⟨(h, ζ), Set.mem_univ _, hζ⟩
    let G : InnerField o R → ℝ≥0∞ := fun w' => Ξ w' * ENNReal.ofReal (Dt (ungaugeInner o R g w'))
    have hG : Measurable G := hΞ.mul (hDt.comp (gaugeInnerEquiv o R g).symm.measurable).ennreal_ofReal
    have step1 : ∫⁻ w in Orb, Φ (coord w) * ENNReal.ofReal (D' w) ∂(innerHaar o R) =
        ∫⁻ w in Orb, G (gaugeInnerEquiv o R g w) ∂(innerHaar o R) := by
      refine setLIntegral_congr_fun hOrbm fun w hw => ?_
      obtain ⟨γ, hγ, hcz, hc⟩ := hcoord w hw
      have h1 : gaugeInner o R g w = gaugedChartField o R A (coord w) _ :=
        gaugeInner_eq_gaugedChartField hR (hZs _ hcz).1 hγ hc
      show _ = Ξ (gaugeInner o R g w) * ENNReal.ofReal (Dt (ungaugeInner o R g (gaugeInner o R g w)))
      rw [ungauge_gauge, h1, hΞe _ hcz, (hD w γ _ hγ hcz hc).1]
    have step2 : ∫⁻ w in Orb, G (gaugeInnerEquiv o R g w) ∂(innerHaar o R) =
        ∫⁻ w' in Img, G w' ∂(innerHaar o R) := by
      rw [hOrb]
      exact (gaugeInner_measurePreserving o R g).setLIntegral_comp_preimage_emb
        (gaugeInnerEquiv o R g).measurableEmbedding G Img
    have step4 : ∫⁻ h, ∫⁻ ζ in Z, G (gaugedChartField o R A ζ h) * ENNReal.ofReal (J ζ) ∂vol ∂(boxGaugeHaar o R) =
        ∫⁻ h, ∫⁻ ζ in Z, (Φ ζ * D (h, ζ)) * ENNReal.ofReal (J ζ) ∂vol ∂(boxGaugeHaar o R) := by
      refine lintegral_congr fun h => setLIntegral_congr_fun hZ fun ζ hζ => ?_
      show Ξ _ * _ * _ = _
      rw [hΞe ζ hζ]
    rw [step1, step2, hchange G hG, step4]
    exact lintegral_normalize_weight (boxGaugeHaar o R) vol Z hZ r hr hr0 hM0 hMt D hDm J hJ hJ0 hIt cH N hcH hN Φ hΦ
private theorem isRegularRegion_supBall (o : TorusSite n) (m : ℕ) (hm : 2048 ≤ m) (hn : 2 * m + 2048 < n) :
    IsRegularRegion (supBall o (m : ℝ)) 1024 := by
  intro z
  refine ⟨fun i => if 0 ≤ (z i - o i).valMinAbs then -1 else 1, fun i => ?_, ?_⟩
  · by_cases h : 0 ≤ (z i - o i).valMinAbs <;> simp [h]
  intro q hq hqz h heps hh
  rw [mem_supBall] at hq ⊢
  have hq' : supDist q o ≤ m := by exact_mod_cast hq
  have hgoal : supDist (q + siteOfInt h) o ≤ m := by
    rw [supDist_le_iff]
    intro i
    have ha : ((q i - o i).valMinAbs).natAbs ≤ m := (supDist_le_iff _ _ _).mp hq' i
    have hd : ((q i - z i).valMinAbs).natAbs ≤ 1024 := (supDist_le_iff _ _ _).mp hqz i
    have he : 0 ≤ (if 0 ≤ (z i - o i).valMinAbs then (-1 : ℤ) else 1) * h i := heps i
    have hc2 : (z i - o i).valMinAbs * 2 ∈ Set.Ioc (-(n : ℤ)) n := ZMod.valMinAbs_mem_Ioc _
    have hcast : (((q i - o i).valMinAbs - (z i - o i).valMinAbs - (q i - z i).valMinAbs : ℤ) : ZMod n) = 0 := by
      push_cast
      ring
    have hdvd : (n : ℤ) ∣ (q i - o i).valMinAbs - (z i - o i).valMinAbs - (q i - z i).valMinAbs :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    have hval : (q + siteOfInt h : TorusSite n) i - o i = (((q i - o i).valMinAbs + h i : ℤ) : ZMod n) := by
      push_cast
      simp only [siteOfInt, Pi.add_apply]
      ring
    rw [hval]
    refine (natAbs_valMinAbs_intCast_le _).trans ?_
    have hhi := abs_le.mp (hh i)
    generalize (q i - o i).valMinAbs = a at *
    generalize (z i - o i).valMinAbs = c at *
    generalize (q i - z i).valMinAbs = d at *
    obtain ⟨hc3, hc4⟩ := hc2
    have hz : a - c - d = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
    by_cases hc : 0 ≤ c
    · rw [if_pos hc] at he
      push_cast at hhi
      omega
    · rw [if_neg hc] at he
      push_cast at hhi
      omega
  exact_mod_cast hgoal
private theorem boxRadius_bounds {κ₀ x : ℝ} (hx : 1 ≤ x) (h0 : 0 ≤ κ₀) :
    x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) ∧ (boxRadius κ₀ x : ℝ) ≤ 2 * x ^ κ₀ := by
  have hP1 : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx h0
  refine ⟨Nat.le_ceil _, ?_⟩
  have := Nat.ceil_lt_add_one (show 0 ≤ x ^ κ₀ by linarith)
  unfold boxRadius
  linarith
private theorem eventually_large_coupling (κ₀ : ℝ) (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) (C σ c : ℝ) (hσ : 0 < σ)
    (hc : 0 < c) (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧ m ≤ boxRadius κ₀ x ∧
      16 * (boxRadius κ₀ x : ℝ) < x ^ (1 / 10 : ℝ) ∧ (m : ℝ) ≤ x ^ (1 / 10 : ℝ) ∧
      C * (boxRadius κ₀ x : ℝ) ^ 2 * boxScale x < σ ∧ C * (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x ≤ 1 ∧
      Real.exp (-(c * boxRadius κ₀ x)) ≤ x ^ (-(1 / 2 : ℝ)) := by
  have hε : 0 < min 1 (σ / 2) / (16 * (|C| + 1)) := by
    have : 0 < min 1 (σ / 2) := lt_min one_pos (by linarith)
    positivity
  set ε := min 1 (σ / 2) / (16 * (|C| + 1)) with hεdef
  have e1 := eventually_ge_atTop (1 : ℝ)
  have e2 := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  have e3 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 27 by norm_num)).eventually_ge_atTop (m : ℝ)
  have e4 := (tendsto_rpow_atTop (show (0 : ℝ) < 11 / 210 by norm_num)).eventually_ge_atTop (33 : ℝ)
  have e5 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 5 / 14 by norm_num)).def hε
  have e6 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 27 by norm_num)).def (show 0 < 2 * c by positivity)
  filter_upwards [e1, e2, e3, e4, e5, e6] with x hx hl h3 h4 h5 h6
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 ≤ κ₀ := by linarith [show (0 : ℝ) ≤ 1 / 27 by norm_num]
  obtain ⟨hP, hR2⟩ := boxRadius_bounds hx hκ0
  set Rr : ℝ := (boxRadius κ₀ x : ℝ) with hRr
  have hlo : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx h1
  have hhi : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h2
  have ht1 : 1 ≤ x ^ (1 / 21 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hP1 : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx hκ0
  have hR1 : 1 ≤ Rr := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity)] at h5 h6
  have hten : x ^ (1 / 10 : ℝ) = x ^ (11 / 210 : ℝ) * x ^ (1 / 21 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hδ0 : 0 ≤ boxScale x := by
    unfold boxScale
    positivity
  have hcube : (x ^ (1 / 21 : ℝ)) ^ 3 = x ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hRt : Rr ≤ 2 * x ^ (1 / 21 : ℝ) := by linarith
  have hR3 : Rr ^ 3 ≤ 8 * x ^ (1 / 7 : ℝ) := by
    calc Rr ^ 3 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) hRt 3
      _ = 8 * x ^ (1 / 7 : ℝ) := by rw [mul_pow, hcube]; norm_num
  have hdecay : x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x ≤ ε := by
    have e : x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 14 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      norm_num
    have hpos : 0 ≤ x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by positivity
    calc x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x
        ≤ x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * (ε * x ^ (5 / 14 : ℝ)) := mul_le_mul_of_nonneg_left h5 hpos
      _ = ε * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 14 : ℝ)) := by ring
      _ = ε := by rw [e, mul_one]
  have hmin : 16 * (|C| + 1) * ε = min 1 (σ / 2) := by
    rw [hεdef]
    have : (16 * (|C| + 1)) ≠ 0 := by positivity
    field_simp
  have hsmall : |C| * Rr ^ 3 * boxScale x ≤ min 1 (σ / 2) := by
    have hs0 : 0 ≤ x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x := by positivity
    calc |C| * Rr ^ 3 * boxScale x ≤ |C| * (8 * x ^ (1 / 7 : ℝ)) * boxScale x := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR3 (abs_nonneg C)) hδ0
      _ = 16 * |C| * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x) := by
          unfold boxScale
          ring
      _ ≤ 16 * (|C| + 1) * ε := by
          refine mul_le_mul (by linarith) hdecay hs0 (by positivity)
      _ = _ := hmin
  have hm1 : min 1 (σ / 2) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (σ / 2) ≤ σ / 2 := min_le_right _ _
  have hC3 : C * Rr ^ 3 * boxScale x ≤ |C| * Rr ^ 3 * boxScale x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) hδ0
  have hC2 : C * Rr ^ 2 * boxScale x ≤ |C| * Rr ^ 3 * boxScale x := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C) ?_ (by positivity) (abs_nonneg C)) hδ0
    exact pow_le_pow_right₀ hR1 (by norm_num)
  refine ⟨hx, hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (m : ℝ) ≤ (boxRadius κ₀ x : ℝ) := h3.trans (hlo.trans hP)
    exact_mod_cast this
  · rw [hten]
    have := mul_le_mul_of_nonneg_right h4 (show 0 ≤ x ^ (1 / 21 : ℝ) by positivity)
    linarith
  · exact h3.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  · linarith
  · linarith
  · have h7 : Real.log x ≤ 2 * c * Rr := h6.trans (mul_le_mul_of_nonneg_left (hlo.trans hP) (by positivity))
    rw [Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by linarith)
private theorem power_bounds (Rr t l : ℝ) (hR : 1 ≤ Rr) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 1 ≤ l) :
    Rr ^ 5 * (2 * t * l) ≤ 2 * (Rr ^ 9 * t * l ^ 3) ∧ Rr ^ 6 * (2 * t * l) ^ 2 ≤ 4 * (Rr ^ 9 * t * l ^ 3) ∧
      Rr ^ 8 * (2 * t * l) ^ 2 ≤ 4 * (Rr ^ 9 * t * l ^ 3) ∧ t ≤ Rr ^ 9 * t * l ^ 3 := by
  have hl0 : 0 ≤ l := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have p5 : Rr ^ 5 ≤ Rr ^ 9 := pow_le_pow_right₀ hR (by norm_num)
  have p6 : Rr ^ 6 ≤ Rr ^ 9 := pow_le_pow_right₀ hR (by norm_num)
  have p8 : Rr ^ 8 ≤ Rr ^ 9 := pow_le_pow_right₀ hR (by norm_num)
  have p1 : 1 ≤ Rr ^ 9 := one_le_pow₀ hR
  have l1 : l ≤ l ^ 3 := by nlinarith [mul_nonneg hl0 hl0, mul_le_mul hl hl (by norm_num) hl0]
  have l2 : l ^ 2 ≤ l ^ 3 := pow_le_pow_right₀ hl (by norm_num)
  have l3 : 1 ≤ l ^ 3 := one_le_pow₀ hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Rr ^ 5 * (2 * t * l) = 2 * (Rr ^ 5 * t * l) := by ring
      _ ≤ 2 * (Rr ^ 9 * t * l ^ 3) := by gcongr
  · calc Rr ^ 6 * (2 * t * l) ^ 2 = 4 * (Rr ^ 6 * t ^ 2 * l ^ 2) := by ring
      _ ≤ 4 * (Rr ^ 9 * t * l ^ 3) := by gcongr
  · calc Rr ^ 8 * (2 * t * l) ^ 2 = 4 * (Rr ^ 8 * t ^ 2 * l ^ 2) := by ring
      _ ≤ 4 * (Rr ^ 9 * t * l ^ 3) := by gcongr
  · calc t = 1 * t * 1 := by ring
      _ ≤ Rr ^ 9 * t * l ^ 3 := by gcongr
private theorem mass_of_isProbability_normalize {X : Type} [MeasurableSpace X] (μ : Measure X)
    (h : IsProbabilityMeasure (normalize μ)) : μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ∞ := by
  have h1 := h.measure_univ
  unfold normalize at h1
  simp only [Measure.smul_apply, smul_eq_mul] at h1
  constructor
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro ht
    rw [ht] at h1
    simp at h1
private theorem measurableSet_sliceEllipsoid (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ)
    (A : TorusBond n → imaginaryQuaternions) (c : ℝ) (cc : TorusBond n → TorusBond n → ℝ)
    (hform : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k (supBall o (2 * R)) u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        cc b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b')) :
    MeasurableSet (sliceEllipsoid a L k o R A c) ∧
      Continuous fun ζ : TorusBond n → imaginaryQuaternions =>
        hessianForm a L k (supBall o (2 * R)) (A + ζ) (A + ζ) := by
  have hq : Continuous fun ζ : TorusBond n → imaginaryQuaternions =>
      hessianForm a L k (supBall o (2 * R)) (A + ζ) (A + ζ) := by
    have e : (fun ζ : TorusBond n → imaginaryQuaternions => hessianForm a L k (supBall o (2 * R)) (A + ζ) (A + ζ)) =
        fun ζ => ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          cc b b' * imaginaryComponent e ((A + ζ) b) * imaginaryComponent e ((A + ζ) b') :=
      funext fun ζ => hform _ _
    rw [e]
    have hc : ∀ (e : Fin 3) (b : TorusBond n),
        Continuous fun ζ : TorusBond n → imaginaryQuaternions => imaginaryComponent e ((A + ζ) b) :=
      fun e b => (continuous_imaginaryComponent e).comp (continuous_const.add (continuous_apply b))
    exact continuous_finsetSum _ fun e _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun b' _ =>
      (continuous_const.mul (hc e b)).mul (hc e b')
  refine ⟨?_, hq⟩
  have hs : IsClosed (gaugeSlice o R A : Set (TorusBond n → imaginaryQuaternions)) :=
    Submodule.closed_of_finiteDimensional _
  have : sliceEllipsoid a L k o R A c = (gaugeSlice o R A : Set (TorusBond n → imaginaryQuaternions)) ∩
      {ζ | hessianForm a L k (supBall o (2 * R)) (A + ζ) (A + ζ) ≤ c} := rfl
  rw [this]
  exact (hs.inter (isClosed_le hq continuous_const)).measurableSet
omit [NeZero n] in
private theorem abs_mirrorSum_le (f : LocalDensity) (o : TorusSite n) (R : ℕ) (W : TorusField n) :
    |mirrorSum f o R id W| ≤ mirrorSum f o R abs W := by
  unfold mirrorSum
  by_cases h : 4 * (2 * R) = 0
  · rw [dif_pos h, dif_pos h]
    simp
  · rw [dif_neg h, dif_neg h]
    exact Finset.abs_sum_le_sum_abs _ _
private theorem isBoxDatum_mono {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {β κ₀ xs xs' : ℝ} {k m : ℕ}
    (h : IsBoxDatum Tb y T β κ₀ xs k m) (hle : xs' ≤ xs) : IsBoxDatum Tb y T β κ₀ xs' k m :=
  { h with le_coupling := hle.trans h.le_coupling }
private theorem orbit_log_bound (x ε KE S lD lD₀ A A₀ m m₀ q : ℝ)
    (herr : |lD - lD₀ + x * (A - A₀) - (m - m₀)| ≤ ε) (hen : |x * A - x / 2 * q| ≤ KE) (hms : |m| ≤ S) :
    |lD - (lD₀ + (x * A₀ - m₀)) - -(x / 2) * q| ≤ KE + S + ε := by
  rw [abs_le] at herr hen hms ⊢
  constructor <;> linarith [herr.1, herr.2, hen.1, hen.2, hms.1, hms.2]
private theorem total_error_bound (KH KE CE ρ t5 t6 t8 e jl : ℝ) (hρ : 0 ≤ ρ) (h5 : t5 ≤ 2 * ρ) (h6 : t6 ≤ 4 * ρ)
    (h8 : t8 ≤ 4 * ρ) (h50 : 0 ≤ t5) (h60 : 0 ≤ t6) (h80 : 0 ≤ t8) (he : e ≤ ρ) (hj : jl ≤ KH * (t5 + t6)) :
    jl + (KE * ρ + CE * t8 + e) ≤ (6 * |KH| + |KE| + 4 * |CE| + 1) * ρ := by
  have a1 : KH * (t5 + t6) ≤ |KH| * (6 * ρ) :=
    mul_le_mul (le_abs_self _) (by linarith) (by positivity) (abs_nonneg _)
  have a2 : KE * ρ ≤ |KE| * ρ := mul_le_mul_of_nonneg_right (le_abs_self _) hρ
  have a3 : CE * t8 ≤ |CE| * (4 * ρ) := mul_le_mul (le_abs_self _) h8 h80 (abs_nonneg _)
  calc jl + (KE * ρ + CE * t8 + e) ≤ |KH| * (6 * ρ) + (|KE| * ρ + |CE| * (4 * ρ) + ρ) := by linarith
    _ = _ := by ring
open Classical in
private theorem law_of_comparison {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (A : TorusBond n → imaginaryQuaternions)
    (g : TorusSite n → UnitQuaternion) (u : OuterField o R)
    (Z : Set (TorusBond n → imaginaryQuaternions)) (hZ : MeasurableSet Z)
    (hZs : ∀ ζ ∈ Z, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    (hbase : ∀ b ∈ bondsWithin (supBall o (2 * R)), ∀ hb : b ∉ bondsTouching o R,
      g b.1 * u ⟨b, hb⟩ * (g (b.1 + unitStep n b.2))⁻¹ = expUnit (A b))
    (vol : Measure (TorusBond n → imaginaryQuaternions)) [SFinite vol]
    (cH : ℝ) (J : (TorusBond n → imaginaryQuaternions) → ℝ) (hcH : 0 < cH) (hJ : Measurable J)
    (hJ0 : ∀ ζ ∈ Z, 0 < J ζ)
    (hinj : Set.InjOn (fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions) => gaugedChartField o R A p.2 p.1) (Set.univ ×ˢ Z))
    (hchange : ∀ Φ : InnerField o R → ℝ≥0∞, Measurable Φ →
      ∫⁻ w in {w | ∃ g, ∃ ζ ∈ Z, w = gaugedChartField o R A ζ g}, Φ w ∂(innerHaar o R) =
        ENNReal.ofReal cH * ∫⁻ g, ∫⁻ ζ in Z, Φ (gaugedChartField o R A ζ g) * ENNReal.ofReal (J ζ) ∂vol
          ∂(boxGaugeHaar o R))
    (q : (TorusBond n → imaginaryQuaternions) → ℝ) (hq : Continuous q) (x : ℝ)
    (hM0 : (vol.withDensity fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * q ζ))) Set.univ ≠ 0)
    (hMt : (vol.withDensity fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * q ζ))) Set.univ ≠ ∞)
    (Dq : TorusField n → ℝ) (Hull : TorusField n → Prop) (hDq : Measurable fun W => if Hull W then Dq W else 0)
    (Act Ms : TorusField n → ℝ) (ε KE S : ℝ) (W₀ : TorusField n) (hD₀ : 0 < Dq W₀)
    (hcomp : ∀ (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ → ζ ∈ Z →
      IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w)) →
      Hull (glueField u w) ∧ 0 < Dq (glueField u w) ∧
      |Real.log (Dq (glueField u w)) - Real.log (Dq W₀) + x * (Act (glueField u w) - Act W₀) -
        (Ms (glueField u w) - Ms W₀)| ≤ ε ∧
      |x * Act (glueField u w) - x / 2 * q ζ| ≤ KE ∧ |Ms (glueField u w)| ≤ S) :
    ∃ (c : ℝ) (wt : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable wt ∧
      (∀ ζ ∈ Z, 0 < wt ζ ∧ |Real.log (wt ζ)| ≤ |Real.log (J ζ)| + (KE + S + ε)) ∧
      ∀ coord : InnerField o R → TorusBond n → imaginaryQuaternions,
        (∀ w ∈ {w : InnerField o R | ∃ (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
            IsSupportedGauge o R γ ∧ ζ ∈ Z ∧
            IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))},
          ∃ γ : TorusSite n → UnitQuaternion,
          IsSupportedGauge o R γ ∧ coord w ∈ Z ∧
          IsInChart (supBall o (2 * R)) A (coord w) (gaugeTransform (g * γ) (glueField u w))) →
        ∀ Φ : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞, Measurable Φ →
          ∫⁻ w in {w : InnerField o R | ∃ (γ : TorusSite n → UnitQuaternion)
              (ζ : TorusBond n → imaginaryQuaternions), IsSupportedGauge o R γ ∧ ζ ∈ Z ∧
              IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))},
              Φ (coord w) * ENNReal.ofReal (Dq (glueField u w)) ∂(innerHaar o R) =
            ENNReal.ofReal c * ∫⁻ ζ in Z, Φ ζ * ENNReal.ofReal (wt ζ)
              ∂(normalize (vol.withDensity fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * q ζ)))) := by
  refine law_of_density_bounds hR A g u Z hZ hZs hbase vol cH J hcH hJ hJ0 hinj hchange
    (fun ζ => Real.exp (-(x / 2) * q ζ))
    (Real.measurable_exp.comp (hq.measurable.const_mul _)) (fun ζ => Real.exp_pos _) hM0 hMt
    (fun w => if Hull (glueField u w) then Dq (glueField u w) else 0) (fun w => Dq (glueField u w))
    (hDq.comp (measurable_glueField u)) (Dq W₀ * Real.exp (x * Act W₀ - Ms W₀)) (KE + S + ε)
    (mul_pos hD₀ (Real.exp_pos _)) ?_
  intro w γ ζ hγ hζ hc
  obtain ⟨hH, hp, herr, hen, hms⟩ := hcomp w γ ζ hγ hζ hc
  simp only [if_pos hH, true_and]
  refine ⟨hp, ?_⟩
  rw [Real.log_mul hD₀.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  exact orbit_log_bound _ _ _ _ _ _ _ _ _ _ _ herr hen hms
private theorem sFinite_subspaceVolume (𝒮 : Submodule ℝ (TorusBond n → imaginaryQuaternions)) :
    SFinite (subspaceVolume 𝒮) := by
  unfold subspaceVolume
  infer_instance
private theorem measurable_prod_section {X Y' E : Type} [MeasurableSpace X] [MeasurableSpace Y'] [MeasurableSpace E]
    {f : X × Y' → E} (hf : Measurable f) (c : Y') : Measurable fun x => f (x, c) :=
  hf.comp (measurable_id.prodMk measurable_const)
private theorem isBlockTorusSide_of_side_eq {Tb : ParameterAssignment} {y : ℝ} {n R : ℕ} (hn : 16 * R < n) (hR : 1 ≤ R)
    (hform : ∃ e : ℕ, n = 2 * (Tb.stepParameters y).side ^ e) (hfl : Tb.side * Tb.n₀ ≤ n) :
    IsBlockTorusSide (Tb.stepParameters y) n := by
  obtain ⟨e, he⟩ := hform
  refine ⟨?_, hfl⟩
  rcases e with _ | e
  · have : n = 2 := by simpa using he
    omega
  · rw [he, pow_succ]
    exact Dvd.intro_left (2 * (Tb.stepParameters y).side ^ e) (by ring)
private theorem orbit_comparison {Tb : ParameterAssignment} (hdrawn : Tb.Admissible)
    {y κ₀ C₀ KB KE CS c xD xS xE β : ℝ}
    (hSh : SharesSumToAction)
    (hD' : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xD k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
      ∀ (W W' : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (T.stage k).labels.Ω),
        restrictOuter o R W = restrictOuter o R W' → Disjoint Y (supBall o (3 * R)) →
        (∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature W p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x) →
        (∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature W' p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x) →
        IsHullState (Tb.stepParameters y) (clusterRange x) W Y → 0 < (T.stage k).labelWeight n W Y ω →
        IsHullState (Tb.stepParameters y) (clusterRange x) W' Y ∧ 0 < (T.stage k).labelWeight n W' Y ω ∧
          |Real.log ((T.stage k).labelWeight n W' Y ω) - Real.log ((T.stage k).labelWeight n W Y ω) +
              x * (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) W' -
                actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) W) -
              (mirrorSum (T.stage k).density o R id W' - mirrorSum (T.stage k).density o R id W)| ≤
            Real.exp (-(c * R)))
    (hS' : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xS k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
      ∀ W : TorusField n,
        (∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature W p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x) →
        mirrorSum (T.stage k).density o R abs W ≤ CS * (Tb.stepParameters y).E * (R : ℝ) ^ 8 * boxScale x ^ 2)
    (hE' : ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A : TorusBond n → imaginaryQuaternions),
      xE ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      ∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
        ∀ W : TorusField n, IsInChart (supBall o (2 * R)) A ζ W →
          |x * actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) W -
              x / 2 * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (A + ζ) (A + ζ)| ≤
            KE * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3)
    {T : StageTower (Tb.stepParameters y)} {k n : ℕ} [NeZero n] {o : TorusSite n} {x : ℝ} {R : ℕ}
    {g : TorusSite n → UnitQuaternion} {A : TorusBond n → imaginaryQuaternions} {u : OuterField o R}
    {Y : Finset (TorusSite n)} {ω : Y → (T.stage k).labels.Ω}
    (hdD : IsBoxDatum Tb y T β κ₀ xD k n) (hdS : IsBoxDatum Tb y T β κ₀ xS k n) (hxE : xE ≤ x)
    (hx : x = flowCoupling (Tb.stepParameters y) β k) (hRr : R = boxRadius κ₀ x) (hn : 16 * R < n) (hR : 1024 ≤ R)
    (hfill : IsAxialSmall o R (boxScale x) A) (hY : Disjoint Y (supBall o (3 * R)))
    (hcold : KB * (R : ℝ) ^ 2 * boxScale x < Tb.σA)
    (hcurv : ∀ (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
      ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) →
      IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w)) →
      ∀ p ∈ plaquettesIn (supBall o (2 * R)),
        curvature (glueField u w) p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x)
    {w₀ : InnerField o R} (hcurv₀ : ∀ p ∈ plaquettesIn (supBall o (2 * R)),
      curvature (glueField u w₀) p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x)
    (hH₀ : IsHullState (Tb.stepParameters y) (clusterRange x) (glueField u w₀) Y)
    (hD₀ : 0 < (T.stage k).labelWeight n (glueField u w₀) Y ω)
    (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions)
    (hζ : ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2))
    (hc : IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))) :
    IsHullState (Tb.stepParameters y) (clusterRange x) (glueField u w) Y ∧
      0 < (T.stage k).labelWeight n (glueField u w) Y ω ∧
      |Real.log ((T.stage k).labelWeight n (glueField u w) Y ω) -
          Real.log ((T.stage k).labelWeight n (glueField u w₀) Y ω) +
        x * (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) (glueField u w) -
          actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) (glueField u w₀)) -
        (mirrorSum (T.stage k).density o R id (glueField u w) -
          mirrorSum (T.stage k).density o R id (glueField u w₀))| ≤
        Real.exp (-(c * R)) ∧
      |x * actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) (glueField u w) -
        x / 2 * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (A + ζ) (A + ζ)| ≤
        KE * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 ∧
      |mirrorSum (T.stage k).density o R id (glueField u w)| ≤
        CS * (Tb.stepParameters y).E * (R : ℝ) ^ 8 * boxScale x ^ 2 := by
  have hcW := hcurv w γ ζ hζ hc
  have hoff : restrictOuter o R (glueField u w₀) = restrictOuter o R (glueField u w) := by
    rw [restrictOuter_glueField, restrictOuter_glueField]
  obtain ⟨hHW, hDW, herr⟩ := hD' T β k n o x R hdD hx hRr _ _ Y ω hoff hY hcurv₀ hcW hH₀ hD₀
  refine ⟨hHW, hDW, herr, ?_, ?_⟩
  · have hreg : IsRegularRegion (supBall o (2 * R)) 1024 := by
      have := isRegularRegion_supBall o (2 * R) (by omega) (by omega)
      rwa [show ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) by push_cast; rfl] at this
    have hco : IsColdOn Tb.σA (supBall o (2 * R)) (glueField u w) := fun p hp => (hcW p hp).trans_lt hcold
    have hgauge := actionAtLevel_gaugeTransform hSh (lt_of_lt_of_le one_pos hdrawn.a_ge) hdrawn.L_odd hdrawn.chain k
      (by omega : 64 ≤ n) hreg hco (g * γ)
    have hen := hE' x R k n o A hxE hRr hn hfill ζ hζ _ hc
    rwa [hgauge] at hen
  · exact (abs_mirrorSum_le _ o R _).trans (hS' T β k n o x R hdS hx hRr _ hcW)
end ChartDensity
set_option maxHeartbeats 400000 in
open ChartDensity in
theorem chartDensityStatement_holds (hDG : conditionalDensityStatement) (hSz : coldBoxDensitySumStatement)
    (hHa : chartChangeOfVariablesStatement) (hEn : chartEnergyStatement) (hBd : ellipsoidBoundsStatement)
    (hGa : gaussianTailOffEllipsoidStatement) (hFo : cubeHessianStatement) (hSh : SharesSumToAction) :
    chartDensityStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, hrt₁, h1⟩ := hDG a ha
  obtain ⟨L₂, rt₂, hrt₂, h2⟩ := hSz a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hLodd hL Tb hTa hTL hdrawn hrt
  obtain ⟨y₁, h1⟩ := h1 L hLodd (le_of_max_le_left hL) Tb hTa hTL hdrawn (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, h2⟩ := h2 L hLodd (le_of_max_le_right hL) Tb hTa hTL hdrawn (hrt.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, ?_⟩
  intro y hy hret hrow
  have hDy := h1 y (le_of_max_le_left hy) hret hrow
  have hSy := h2 y (le_of_max_le_right hy) hret hrow
  clear h1 h2
  intro κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨KB, xB, hKB1, hB'⟩ := hBd Tb hdrawn κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨cD, xD, hcD, hD'⟩ := hDy κ₀ hκ1 hκ2 KB
  obtain ⟨CS, xS, hS'⟩ := hSy κ₀ hκ1 hκ2 KB
  obtain ⟨KE, xE, hE'⟩ := hEn Tb hdrawn κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨KH, xH, hH'⟩ := hHa Tb hdrawn κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨CQ, R₀, hCQ, hF'⟩ := hFo Tb hdrawn
  obtain ⟨xG, hG'⟩ := hGa Tb hdrawn κ₀ hκ1 hκ2 (2 ^ 14 * CQ) (by positivity)
  have hσA : 0 < Tb.σA := hdrawn.chain.2.2.2.2.2.1
  obtain ⟨xF, hfl⟩ := eventually_atTop.mp (eventually_large_coupling κ₀ hκ1 hκ2 KB Tb.σA cD hσA hcD
    (max R₀ (max 1024 (Tb.side * Tb.n₀))))
  obtain ⟨xs, lB, lD, lS, lE, lH, lG, lF⟩ :
      ∃ xs : ℝ, xB ≤ xs ∧ xD ≤ xs ∧ xS ≤ xs ∧ xE ≤ xs ∧ xH ≤ xs ∧ xG ≤ xs ∧ xF ≤ xs :=
    ⟨max (max (max xB xD) (max xS xE)) (max (max xH xG) xF),
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)),
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)),
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨6 * |KH| + |KE| + 4 * |CS * (Tb.stepParameters y).E| + 1, xs, ?_⟩
  intro T β k n _ o x R g A u Y ω hdat hx hRr hfill hY hex
  have hfloor : xs ≤ x := by
    rw [hx]
    exact hdat.le_coupling
  obtain ⟨hx1, hl1, hmR, h16, hmn, hK2, hK3, hexp⟩ := hfl x (lF.trans hfloor)
  rw [← hRr] at hmR h16 hK2 hK3 hexp
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans hmR
  have hR1024 : 1024 ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hmR
  have hR1 : 1 ≤ R := by omega
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hwide : x ^ (1 / 10 : ℝ) ≤ n := by
    rw [hx]
    exact hdat.coupling_rpow_le
  have hn : 16 * R < n := by
    have : (16 : ℝ) * R < n := h16.trans_le hwide
    exact_mod_cast this
  have hcoup : (T.stage k).coupling = x := by
    rw [hx]
    exact hdat.onFamily.coupling_eq k (by omega)
  have hblock : IsBlockTorusSide (Tb.stepParameters y) n := by
    refine isBlockTorusSide_of_side_eq hn hR1 hdat.side_eq ?_
    have hm2 : ((Tb.side * Tb.n₀ : ℕ) : ℝ) ≤ ((max R₀ (max 1024 (Tb.side * Tb.n₀)) : ℕ) : ℝ) := by
      exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
    have : ((Tb.side * Tb.n₀ : ℕ) : ℝ) ≤ n := hm2.trans (hmn.trans hwide)
    exact_mod_cast this
  have hrowk := ((hdat.onFamily.onFamily k (Nat.le_add_right _ _)).isStep).1.2
  have hborel := (hrowk.borel n hblock Y).1
  have hcoup' : (T.stage k).toStepSetup.coupling = x := hcoup
  rw [hcoup'] at hborel
  obtain ⟨-, -, -, -, hQ, -, hform⟩ := hF' k n o R hRR₀ hn
  obtain ⟨hZm, hqc⟩ := measurableSet_sliceEllipsoid Tb.coupling Tb.side k o R A
    (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) _ hform
  obtain ⟨-, hBb⟩ := hB' x R k n o A (lB.trans hfloor) hRr hn hfill
  obtain ⟨cH, J, hcH, hJm, hJb, hinj, hch⟩ := hH' x R k n o A (lH.trans hfloor) hRr hn hfill
  have hQA : 2 * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A A ≤
      2 ^ 14 * CQ * (R : ℝ) ^ 4 * boxScale x ^ 2 := by
    have h1 := (hQ A).2
    have h2 := mul_le_mul_of_nonneg_left hfill.curlNormSq_le (show 0 ≤ CQ by linarith)
    calc 2 * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A A ≤
          2 * (CQ * (2 ^ 13 * (R : ℝ) ^ 4 * boxScale x ^ 2)) := by
          linarith
      _ = _ := by ring
  have hprob := (hG' x R k n o A (lG.trans hfloor) hRr hn hfill hQA).1
  obtain ⟨hM0, hMt⟩ := mass_of_isProbability_normalize _ hprob
  obtain ⟨w₀, ⟨γ₀, ζ₀, hγ₀, hζ₀, hc₀⟩, hH₀, hD₀⟩ := hex
  have hbase : ∀ b ∈ bondsWithin (supBall o (2 * R)), ∀ hb : b ∉ bondsTouching o R,
      g b.1 * u ⟨b, hb⟩ * (g (b.1 + unitStep n b.2))⁻¹ = expUnit (A b) := by
    intro b hbS hb
    have hn' : ¬ (b.1 ∈ supBall o R ∨ b.1 + unitStep n b.2 ∈ supBall o R) := fun hh =>
      hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    have h1 := hc₀ b hbS
    rw [hζ₀.1.1 b hb, chartPoint_zero] at h1
    have h2 : gaugeTransform (g * γ₀) (glueField u w₀) b.1 b.2 = expUnit (A b) := Subtype.ext h1
    simp only [gaugeTransform, Pi.mul_apply] at h2
    rw [glueField_outer u w₀ hb, hγ₀ b.1 (fun hh => hn' (Or.inl hh)), hγ₀ _ (fun hh => hn' (Or.inr hh))] at h2
    simpa using h2
  have hZs : ∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
      (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0 := fun ζ hζ =>
    ⟨fun b => ((hBb ζ hζ).2.1 b).trans hK3, hζ.1.1⟩
  have hcurv : ∀ (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
      ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) →
      IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w)) →
      ∀ p ∈ plaquettesIn (supBall o (2 * R)),
        curvature (glueField u w) p.1 p.2.1 p.2.2 ≤ KB * (R : ℝ) ^ 2 * boxScale x := by
    intro w γ ζ hζ hc p hp
    obtain ⟨v, β', -, -, -, hcv⟩ := (hBb ζ hζ).2.2.2 _ hc
    have := hcv p hp
    rwa [curvature_gaugeTransform] at this
  have hcurv₀ := hcurv w₀ γ₀ ζ₀ hζ₀ hc₀
  classical
  have hDq0 := measurable_prod_section hborel ω
  have hDq : Measurable fun W : TorusField n =>
      if IsHullState (Tb.stepParameters y) (clusterRange x) W Y then (T.stage k).labelWeight n W Y ω else 0 := hDq0
  have hcomp := fun (w : InnerField o R) (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions)
      (_ : IsSupportedGauge o R γ)
      (hζ : ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2))
      (hc : IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))) =>
    orbit_comparison hdrawn hSh hD' hS' hE' (isBoxDatum_mono hdat lD) (isBoxDatum_mono hdat lS)
      (lE.trans hfloor) hx hRr hn hR1024 hfill hY hK2 hcurv hcurv₀ hH₀ hD₀ w γ ζ hζ hc
  have hsf := sFinite_subspaceVolume (gaugeSlice o R A)
  have hcore := law_of_comparison hR1 A g u
    (sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2))
    hZm hZs hbase (subspaceVolume (gaugeSlice o R A)) cH J hcH hJm
    (fun ζ hζ => (hJb ζ hζ).1) hinj hch
    (fun ζ => hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (A + ζ) (A + ζ)) hqc x hM0 hMt
    (fun W => (T.stage k).labelWeight n W Y ω) (fun W => IsHullState (Tb.stepParameters y) (clusterRange x) W Y) hDq
    (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R))) (mirrorSum (T.stage k).density o R id)
    (Real.exp (-(cD * R)))
    (KE * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3)
    (CS * (Tb.stepParameters y).E * (R : ℝ) ^ 8 * boxScale x ^ 2) (glueField u w₀) hD₀ hcomp
  obtain ⟨c, wt, hc, hwm, hwb, hlaw⟩ := hcore
  refine ⟨c, wt, hc, hwm, fun ζ hζ => ⟨(hwb ζ hζ).1, ?_⟩, fun coord hcoord Φ hΦ => hlaw coord hcoord Φ hΦ⟩
  refine (hwb ζ hζ).2.trans ?_
  have ht0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by positivity
  have ht1 : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  obtain ⟨t5, t6, t8, t1⟩ := power_bounds (R : ℝ) (x ^ (-(1 / 2 : ℝ))) (Real.log x) hR1r ht0 ht1 hl1
  have hδe : boxScale x = 2 * x ^ (-(1 / 2 : ℝ)) * Real.log x := rfl
  rw [← hδe] at t5 t6 t8
  have hl0 : 0 ≤ Real.log x := by linarith
  have hδ0 : 0 ≤ boxScale x := by
    rw [hδe]
    positivity
  have hρ0 : 0 ≤ (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by positivity
  have hfin := total_error_bound KH KE (CS * (Tb.stepParameters y).E) _ _ _ _ _ _ hρ0 t5 t6 t8
    (by positivity) (by positivity) (by positivity) (hexp.trans t1) ((hJb ζ hζ).2)
  calc _ ≤ (6 * |KH| + |KE| + 4 * |CS * (Tb.stepParameters y).E| + 1) *
        ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := by
        refine le_trans (le_of_eq ?_) hfin
        ring
    _ = _ := by ring
end YangMills.Construction.BoxGaussian
end
