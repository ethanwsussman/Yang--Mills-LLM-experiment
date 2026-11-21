import YangMills.Construction.FormsOnATorus.ChangeOfVariablesOfAFreeGaugeAction
import YangMills.Construction.FormsOnATorus.DeterminantOfTheChart
import YangMills.Construction.FormsOnATorus.FactsOfTheHalfChart
import YangMills.Construction.FormsOnATorus.GaussianOffTheEllipsoidProof
import YangMills.Construction.LawOnABoxOfTheFlow.HaarMeasureInTheChart
import YangMills.Construction.LawOnABoxOfTheFlow.OnePointInAnOrbit
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
open MeasureTheory Set Filter
open scoped Quaternion ENNReal Topology
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion ColdStepAtMirrorFrames GaugeCharts
open BlockAverages hiding unitStep adjointAction
namespace HaarChart
variable {n : ℕ} [NeZero n]
abbrev SiteInBox (o : TorusSite n) (R : ℕ) : Type := {z : TorusSite n // z ∈ supBall o R}
open Classical in
def tailInBox (o : TorusSite n) (R : ℕ) (b : TouchingBond o R) : Option (SiteInBox o R) :=
  if h : b.1.1 ∈ supBall o R then some ⟨b.1.1, h⟩ else none
open Classical in
def headInBox (o : TorusSite n) (R : ℕ) (b : TouchingBond o R) : Option (SiteInBox o R) :=
  if h : b.1.1 + unitStep n b.1.2 ∈ supBall o R then some ⟨b.1.1 + unitStep n b.1.2, h⟩ else none
def baseLinks (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) (b : TouchingBond o R) : UnitQuaternion :=
  expUnit (A b.1)
def restrictToBonds (o : TorusSite n) (R : ℕ) (ζ : TorusBond n → imaginaryQuaternions) :
    TouchingBond o R → imaginaryQuaternions := fun b => ζ b.1
def sliceToBonds {S : Type} [AddCommGroup S] [Module ℝ S] (o : TorusSite n) (R : ℕ)
    (ι₀ : S →ₗ[ℝ] (TorusBond n → imaginaryQuaternions)) :
    S →ₗ[ℝ] (TouchingBond o R → imaginaryQuaternions) where
  toFun ζ := restrictToBonds o R (ι₀ ζ)
  map_add' a b := by
    funext c
    simp [restrictToBonds]
  map_smul' r a := by
    funext c
    simp [restrictToBonds]
open Classical in
def extendByZero (o : TorusSite n) (R : ℕ) (χ : SiteInBox o R → imaginaryQuaternions) :
    TorusSite n → imaginaryQuaternions :=
  fun z => if h : z ∈ supBall o R then χ ⟨z, h⟩ else 0
theorem extendByZero_of_not_mem (o : TorusSite n) (R : ℕ) (χ : SiteInBox o R → imaginaryQuaternions) {z : TorusSite n}
    (hz : z ∉ supBall o R) : _root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ z = 0 := by
  simp [_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero, hz]
theorem extendByZero_coe (o : TorusSite n) (R : ℕ) (χ : SiteInBox o R → imaginaryQuaternions) (z : SiteInBox o R) :
    _root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ z.1 = χ z := by
  simp [_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero, z.2]
theorem extendByZero_restrict (o : TorusSite n) (R : ℕ) (φ : TorusSite n → imaginaryQuaternions)
    (h : ∀ z, z ∉ supBall o R → φ z = 0) :
    _root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R (fun z => φ z.1) = φ := by
  funext z
  by_cases hz : z ∈ supBall o R
  · simp [_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero, hz]
  · simp [_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero, hz, h z hz]
theorem formAtEnd_tailInBox (o : TorusSite n) (R : ℕ) (χ : SiteInBox o R → imaginaryQuaternions) (b : TouchingBond o R) :
    formAtEnd χ (tailInBox o R b) = _root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ b.1.1 := by
  by_cases h : b.1.1 ∈ supBall o R
  · simp [tailInBox, h, formAtEnd, extendByZero]
  · simp [tailInBox, h, formAtEnd, extendByZero]
theorem formAtEnd_headInBox (o : TorusSite n) (R : ℕ) (χ : SiteInBox o R → imaginaryQuaternions) (b : TouchingBond o R) :
    formAtEnd χ (headInBox o R b) = _root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ (b.1.1 + unitStep n b.1.2) := by
  by_cases h : b.1.1 + unitStep n b.1.2 ∈ supBall o R
  · simp [headInBox, h, formAtEnd, extendByZero]
  · simp [headInBox, h, formAtEnd, extendByZero]
theorem gaugeLinearization_zero_eq (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions)
    (χ : SiteInBox o R → imaginaryQuaternions) (b : TouchingBond o R) :
    gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ b = covariantGrad A (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ) b.1 := by
  show _root_.YangMills.Construction.GaugeCharts.imaginaryPart ((formAtEnd χ (tailInBox o R b) : ℍ[ℝ]) * hemispherePoint ((0 : TouchingBond o R → imaginaryQuaternions) b)) -
    _root_.YangMills.Construction.GaugeCharts.imaginaryPart (hemispherePoint ((0 : TouchingBond o R → imaginaryQuaternions) b) *
      ((baseLinks o R A b : ℍ[ℝ]) * (formAtEnd χ (headInBox o R b) : ℍ[ℝ]) * star (baseLinks o R A b : ℍ[ℝ]))) = _
  rw [Pi.zero_apply, hemispherePoint_zero, mul_one, one_mul, formAtEnd_tailInBox, formAtEnd_headInBox,
    imaginaryPart_coe_imaginary]
  have h : ((baseLinks o R A b : ℍ[ℝ]) * (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ (b.1.1 + unitStep n b.1.2) : ℍ[ℝ]) *
      star (baseLinks o R A b : ℍ[ℝ])) =
      ((adjointAction (expUnit (A b.1)) (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ (b.1.1 + unitStep n b.1.2)) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
  rw [h, imaginaryPart_coe_imaginary]
  rfl
theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
theorem covariantGrad_eq_zero_of_not_mem (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions)
    {φ : TorusSite n → imaginaryQuaternions} (h : ∀ z, z ∉ supBall o R → φ z = 0)
    {b : TorusBond n} (hb : b ∉ bondsTouching o R) : covariantGrad A φ b = 0 := by
  have hb' : b.1 ∉ supBall o R ∧ b.1 + unitStep n b.2 ∉ supBall o R := by
    simpa [bondsTouching, not_or] using hb
  simp [covariantGrad, h _ hb'.1, h _ hb'.2, _root_.YangMills.Construction.BoxGaussian.HaarChart.adjointAction_zero]
theorem sum_eq_sum_touching (o : TorusSite n) (R : ℕ) (f : TorusBond n → ℝ) (h : ∀ b, b ∉ bondsTouching o R → f b = 0) :
    ∑ b : TorusBond n, f b = ∑ b : TouchingBond o R, f b.1 := by
  rw [← Finset.sum_subset (Finset.subset_univ (bondsTouching o R)) (fun b _ hb => h b hb)]
  exact (Finset.sum_coe_sort (bondsTouching o R) f).symm
theorem sliceToBonds_injective {S : Type} [AddCommGroup S] [Module ℝ S] (o : TorusSite n) (R : ℕ)
    (ι₀ : S →ₗ[ℝ] (TorusBond n → imaginaryQuaternions))
    (hι₀ : Function.Injective ι₀) (hoff : ∀ ζ, ∀ b, b ∉ bondsTouching o R → ι₀ ζ b = 0) :
    Function.Injective (sliceToBonds o R ι₀) := by
  intro ζ ζ' h
  apply hι₀
  funext b
  by_cases hb : b ∈ bondsTouching o R
  · exact congrFun h ⟨b, hb⟩
  · rw [hoff _ b hb, hoff _ b hb]
theorem mem_range_sliceToBonds_iff {S : Type} [AddCommGroup S] [Module ℝ S] (o : TorusSite n) (R : ℕ)
    (A : TorusBond n → imaginaryQuaternions) (ι₀ : S →ₗ[ℝ] (TorusBond n → imaginaryQuaternions))
    (hchar : ∀ v, v ∈ LinearMap.range ι₀ ↔ v ∈ gaugeSlice o R A) (v : TouchingBond o R → imaginaryQuaternions) :
    v ∈ LinearMap.range (sliceToBonds o R ι₀) ↔
      ∀ χ, ∑ b, inner ℝ (v b) (gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ b) = 0 := by
  constructor
  · rintro ⟨ζ, rfl⟩ χ
    have hm : ι₀ ζ ∈ gaugeSlice o R A := (hchar _).mp ⟨ζ, rfl⟩
    have h := hm.2 (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ) (fun z hz => extendByZero_of_not_mem o R χ hz)
    rw [sum_eq_sum_touching o R _ (fun b hb => by rw [hm.1 b hb]; simp)] at h
    rw [← h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gaugeLinearization_zero_eq]
    rfl
  · intro hv
    classical
    let ζ₀ : TorusBond n → imaginaryQuaternions := fun b => if h : b ∈ bondsTouching o R then v ⟨b, h⟩ else 0
    have hoff : ∀ b, b ∉ bondsTouching o R → ζ₀ b = 0 := fun b hb => by simp [ζ₀, hb]
    have hon : ∀ b : TouchingBond o R, ζ₀ b.1 = v b := fun b => by simp [ζ₀, b.2]
    have hmem : ζ₀ ∈ gaugeSlice o R A := by
      refine ⟨hoff, fun χ hχ => ?_⟩
      rw [sum_eq_sum_touching o R _ (fun b hb => by rw [hoff b hb]; simp)]
      have h := hv fun z => χ z.1
      rw [← h]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hon, gaugeLinearization_zero_eq, extendByZero_restrict o R χ hχ]
    obtain ⟨z, hz⟩ := (hchar _).mpr hmem
    refine ⟨z, funext fun b => ?_⟩
    show restrictToBonds o R (ι₀ z) b = v b
    rw [hz]
    exact hon b
theorem linearization_injective_and_green (hGap : covariantGradientGapStatement) (o : TorusSite n) {R : ℕ} (h1 : 1 ≤ R)
    (h8 : 8 * R < n) (A : TorusBond n → imaginaryQuaternions) :
    (∀ χ, gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ = 0 → χ = 0) ∧
    ∀ (χ : SiteInBox o R → imaginaryQuaternions) (z : SiteInBox o R) (X : imaginaryQuaternions),
      (∀ ψ, ∑ b, inner ℝ (gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ b)
        (gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 ψ b) = inner ℝ X (ψ z)) →
      ∀ z', ‖χ z'‖ ≤ ‖X‖ := by
  obtain ⟨hg1, hg2⟩ := hGap n o R h1 h8 A
  constructor
  · intro χ h0
    have hz : ∀ b, covariantGrad A (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ) b = 0 := by
      intro b
      by_cases hb : b ∈ bondsTouching o R
      · have := congrFun h0 ⟨b, hb⟩
        rwa [gaugeLinearization_zero_eq] at this
      · exact covariantGrad_eq_zero_of_not_mem o R A (fun z hz => extendByZero_of_not_mem o R χ hz) hb
    have h2 := hg1 (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ) (fun z hz => extendByZero_of_not_mem o R χ hz)
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h2
    have hpos : 0 < 4 * ((R : ℝ) + 1)⁻¹ ^ 2 := by positivity
    have h3 : ∑ z : TorusSite n, ‖_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ z‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hpos hc
      linarith
    have h4 : ∑ z : TorusSite n, ‖_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ z‖ ^ 2 = 0 :=
      le_antisymm h3 (Finset.sum_nonneg fun z _ => by positivity)
    funext z
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => by positivity)).mp h4 z.1 (Finset.mem_univ _)
    have h6 : ‖_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ z.1‖ = 0 := by simpa using h5
    rw [extendByZero_coe] at h6
    simpa using h6
  · intro χ z X hψ z'
    have h := hg2 (_root_.YangMills.Construction.BoxGaussian.HaarChart.extendByZero o R χ) z.1 X (fun z hz => extendByZero_of_not_mem o R χ hz) z.2 (fun ψ hψ' => ?_) z'.1
    · rwa [extendByZero_coe] at h
    · rw [sum_eq_sum_touching o R _ (fun b hb => by
        rw [covariantGrad_eq_zero_of_not_mem o R A (fun z hz => extendByZero_of_not_mem o R χ hz) hb]; simp)]
      have h2 := hψ fun z => ψ z.1
      rw [show ψ z.1 = (fun z : SiteInBox o R => ψ z.1) z from rfl, ← h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [gaugeLinearization_zero_eq, gaugeLinearization_zero_eq, extendByZero_restrict o R ψ hψ']
def chartFieldAll (A ζ : TorusBond n → imaginaryQuaternions) : TorusField n :=
  fun x i => hemisphereUnit (ζ (x, i)) * expUnit (A (x, i))
theorem chartPoint_eq {y : imaginaryQuaternions} (hy : ‖y‖ ≤ 1) (a : imaginaryQuaternions) :
    chartPoint a y = ((hemisphereUnit y * expUnit a : UnitQuaternion) : ℍ[ℝ]) := by
  rw [Submonoid.coe_mul, coe_hemisphereUnit hy]
  rfl
theorem toUnit_coe (g : UnitQuaternion) : toUnit (g : ℍ[ℝ]) = g := by
  simp [toUnit, g.2]
theorem glueField_eq (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions) (hζ : ∀ b, ‖ζ b‖ ≤ 1)
    (hoff : ∀ b, b ∉ bondsTouching o R → ζ b = 0) :
    glueField (restrictOuter o R (exponentialField A)) (fun b => toUnit (chartPoint (A b.1) (ζ b.1))) = chartFieldAll A ζ := by
  funext x i
  by_cases h : (x, i) ∈ bondsTouching o R
  · simp only [glueField, dif_pos h]
    rw [chartPoint_eq (hζ _), toUnit_coe]
    rfl
  · simp only [glueField, dif_neg h, restrictOuter, exponentialField, chartFieldAll]
    rw [hoff _ h, hemisphereUnit_zero, one_mul]
theorem gaugedChartField_eq (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions) (hζ : ∀ b, ‖ζ b‖ ≤ 1)
    (hoff : ∀ b, b ∉ bondsTouching o R → ζ b = 0) (g : SiteInBox o R → UnitQuaternion) :
    gaugedChartField o R A ζ g = restrictInner o R (TorusFields.gaugeTransform (extendGaugeByOne g) (chartFieldAll A ζ)) := by
  rw [gaugedChartField, glueField_eq o R A ζ hζ hoff]
theorem gaugeAtEnd_tailInBox (o : TorusSite n) (R : ℕ) (g : SiteInBox o R → UnitQuaternion) (b : TouchingBond o R) :
    gaugeAtEnd g (tailInBox o R b) = extendGaugeByOne g b.1.1 := by
  by_cases h : b.1.1 ∈ supBall o R
  · simp [tailInBox, h, gaugeAtEnd, extendGaugeByOne]
  · simp [tailInBox, h, gaugeAtEnd, extendGaugeByOne]
theorem gaugeAtEnd_headInBox (o : TorusSite n) (R : ℕ) (g : SiteInBox o R → UnitQuaternion) (b : TouchingBond o R) :
    gaugeAtEnd g (headInBox o R b) = extendGaugeByOne g (b.1.1 + unitStep n b.1.2) := by
  by_cases h : b.1.1 + unitStep n b.1.2 ∈ supBall o R
  · simp [headInBox, h, gaugeAtEnd, extendGaugeByOne]
  · simp [headInBox, h, gaugeAtEnd, extendGaugeByOne]
theorem gaugeTransform_chart_eq (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions) (hζ : ∀ b, ‖ζ b‖ ≤ 1)
    (hoff : ∀ b, b ∉ bondsTouching o R → ζ b = 0) (g : SiteInBox o R → UnitQuaternion) :
    GaugeCharts.gaugeTransform (tailInBox o R) (headInBox o R) g (hemisphereChartField (baseLinks o R A) (restrictToBonds o R ζ)) =
      gaugedChartField o R A ζ g := by
  rw [gaugedChartField_eq o R A ζ hζ hoff]
  funext b
  simp only [GaugeCharts.gaugeTransform, gaugeAtEnd_tailInBox, gaugeAtEnd_headInBox]
  rfl
theorem isInChart_chartFieldAll (S : Finset (TorusSite n)) (A ζ : TorusBond n → imaginaryQuaternions) (hζ : ∀ b, ‖ζ b‖ ≤ 1) :
    IsInChart S A ζ (chartFieldAll A ζ) := by
  intro b _
  rw [chartPoint_eq (hζ b)]
  rfl
theorem gaugedChartField_injective (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) (S : Finset (TorusSite n))
    (E : Set (TorusBond n → imaginaryQuaternions))
    (hOne : ∀ (W : TorusField n) (γ : TorusSite n → UnitQuaternion) (ζ ζ' : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ → ζ ∈ E → ζ' ∈ E →
      IsInChart S A ζ W → IsInChart S A ζ' (TorusFields.gaugeTransform γ W) → ζ' = ζ ∧ ∀ z, γ z = 1)
    (hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    {g g' : SiteInBox o R → UnitQuaternion} {ζ ζ' : TorusBond n → imaginaryQuaternions} (hζ : ζ ∈ E) (hζ' : ζ' ∈ E)
    (h : gaugedChartField o R A ζ g = gaugedChartField o R A ζ' g') : g = g' ∧ ζ = ζ' := by
  rw [gaugedChartField_eq o R A ζ (hE ζ hζ).1 (hE ζ hζ).2, gaugedChartField_eq o R A ζ' (hE ζ' hζ').1 (hE ζ' hζ').2] at h
  have hext_off : ∀ (f : SiteInBox o R → UnitQuaternion) z, z ∉ supBall o R → extendGaugeByOne f z = 1 := fun f z hz => by
    simp [extendGaugeByOne, hz]
  have hfield : TorusFields.gaugeTransform (extendGaugeByOne g) (chartFieldAll A ζ) =
      TorusFields.gaugeTransform (extendGaugeByOne g') (chartFieldAll A ζ') := by
    funext x i
    by_cases hb : (x, i) ∈ bondsTouching o R
    · exact congrFun h ⟨(x, i), hb⟩
    · have hb' : x ∉ supBall o R ∧ x + unitStep n i ∉ supBall o R := by
        simpa [bondsTouching, not_or] using hb
      simp only [TorusFields.gaugeTransform, hext_off _ _ hb'.1, hext_off _ _ hb'.2, chartFieldAll, (hE ζ hζ).2 _ hb,
        (hE ζ' hζ').2 _ hb]
  set γ : TorusSite n → UnitQuaternion := (extendGaugeByOne g')⁻¹ * extendGaugeByOne g with hγ
  have hγi : IsSupportedGauge o R γ := fun z hz => by
    simp [hγ, hext_off _ _ hz]
  have hW : TorusFields.gaugeTransform γ (chartFieldAll A ζ) = chartFieldAll A ζ' := by
    funext x i
    have hx := congrFun (congrFun hfield x) i
    simp only [TorusFields.gaugeTransform] at hx
    simp only [TorusFields.gaugeTransform, hγ, Pi.mul_apply, Pi.inv_apply]
    calc (extendGaugeByOne g' x)⁻¹ * extendGaugeByOne g x * chartFieldAll A ζ x i *
          ((extendGaugeByOne g' (x + unitStep n i))⁻¹ * extendGaugeByOne g (x + unitStep n i))⁻¹
        = (extendGaugeByOne g' x)⁻¹ * (extendGaugeByOne g x * chartFieldAll A ζ x i * (extendGaugeByOne g (x + unitStep n i))⁻¹) *
            extendGaugeByOne g' (x + unitStep n i) := by
          group
      _ = chartFieldAll A ζ' x i := by
          rw [hx]
          group
  obtain ⟨h1, h2⟩ := hOne (chartFieldAll A ζ) γ ζ ζ' hγi hζ hζ' (isInChart_chartFieldAll S A ζ (hE ζ hζ).1)
    (by rw [hW]; exact isInChart_chartFieldAll S A ζ' (hE ζ' hζ').1)
  refine ⟨?_, h1.symm⟩
  funext z
  have h3 := h2 z.1
  simp only [hγ, Pi.mul_apply, Pi.inv_apply] at h3
  have h4 : extendGaugeByOne g z.1 = extendGaugeByOne g' z.1 := by
    have := inv_mul_eq_one.mp h3
    exact this.symm
  simpa [extendGaugeByOne, z.2] using h4
theorem card_bondsTouching_le (o : TorusSite n) (R : ℕ) : (bondsTouching o R).card ≤ 8 * (2 * R + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p9498 <;> assumption
theorem mem_bondsWithin_of_touching (o : TorusSite n) {R : ℕ} (h1 : 1 ≤ R) {b : TorusBond n} (hb : b ∈ bondsTouching o R) :
    b ∈ bondsWithin (supBall o (2 * R)) := by apply _root_.YangMills.SharedProofs.p15112 <;> assumption
end HaarChart
namespace HaarChart
theorem continuous_imaginaryPart : Continuous _root_.YangMills.Construction.GaugeCharts.imaginaryPart := _root_.YangMills.Construction.GaugeCharts.imaginaryPart.continuous_of_finiteDimensional
theorem continuous_gaugeLinearization {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (χ : ι → imaginaryQuaternions) : Continuous fun y : κ → imaginaryQuaternions => gaugeLinearization tl hd V y χ := by
  refine continuous_pi fun b => ?_
  have hM : Continuous fun y : κ → imaginaryQuaternions => hemispherePoint (y b) :=
    continuous_hemispherePoint.comp (continuous_apply b)
  have h1 : Continuous fun y : κ → imaginaryQuaternions => _root_.YangMills.Construction.GaugeCharts.imaginaryPart ((formAtEnd χ (tl b) : ℍ[ℝ]) * hemispherePoint (y b)) :=
    continuous_imaginaryPart.comp (continuous_const.mul hM)
  have h2 : Continuous fun y : κ → imaginaryQuaternions =>
      _root_.YangMills.Construction.GaugeCharts.imaginaryPart (hemispherePoint (y b) * ((V b : ℍ[ℝ]) * (formAtEnd χ (hd b) : ℍ[ℝ]) * star (V b : ℍ[ℝ]))) :=
    continuous_imaginaryPart.comp (hM.mul continuous_const)
  exact h1.sub h2
theorem continuous_det_chartLinearization {ι κ S : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup S] [Module ℝ S]
    (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S)) :
    Continuous fun y : κ → imaginaryQuaternions => LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q) := by
  let B := Module.finBasis ℝ (κ → imaginaryQuaternions)
  have hc : ∀ v, Continuous fun y : κ → imaginaryQuaternions => chartLinearization tl hd V e y (Q v) := fun v => by
    have : (fun y : κ → imaginaryQuaternions => chartLinearization tl hd V e y (Q v)) =
        fun y => gaugeLinearization tl hd V y (Q v).1 + e (Q v).2 := by
      funext y
      simp [chartLinearization]
    rw [this]
    exact (continuous_gaugeLinearization tl hd V _).add continuous_const
  have h : (fun y : κ → imaginaryQuaternions => LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q)) =
      fun y => (LinearMap.toMatrix B B (chartLinearization tl hd V e y ∘ₗ Q)).det := by
    funext y
    rw [LinearMap.det_toMatrix]
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply]
  have hl : Continuous fun v : κ → imaginaryQuaternions => B.repr v i :=
    ((Finsupp.lapply i) ∘ₗ B.repr.toLinearMap).continuous_of_finiteDimensional
  exact hl.comp (hc _)
theorem eventually_scale_small (κ₀ : ℝ) (h₁ : 1 / 27 ≤ κ₀) (h₂ : κ₀ ≤ 1 / 21) {C : ℝ} (hC : 0 < C) (R₀ : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ boxScale x ∧ 1 ≤ boxRadius κ₀ x ∧ R₀ ≤ boxRadius κ₀ x ∧
      C * (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x ≤ 1 / 8 := by
  have hκ : 0 < κ₀ := by linarith
  have hε : 0 < 1 / (256 * C) := by positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 5 / 14 by norm_num)).def hε
  have hbig := (tendsto_rpow_atTop hκ).eventually_ge_atTop ((R₀ : ℝ) + 1)
  filter_upwards [hlog, hbig, eventually_ge_atTop (3 : ℝ)] with x hl hb hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogpos : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsize : 0 ≤ boxScale x := by
    unfold boxScale
    positivity
  have hR1 : x ^ κ₀ ≤ boxRadius κ₀ x := Nat.le_ceil _
  have hR2 : (boxRadius κ₀ x : ℝ) < x ^ κ₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hRR : R₀ + 1 ≤ boxRadius κ₀ x := by
    have : ((R₀ : ℝ) + 1) ≤ boxRadius κ₀ x := hb.trans hR1
    exact_mod_cast this
  refine ⟨hsize, by omega, by omega, ?_⟩
  set a : ℝ := x ^ (1 / 21 : ℝ) with ha
  set b : ℝ := x ^ (-(1 / 2) : ℝ) with hbdef
  set c : ℝ := x ^ (5 / 14 : ℝ) with hc
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hx0 _
  have hc0 : 0 < c := Real.rpow_pos_of_pos hx0 _
  have hpa : x ^ κ₀ ≤ a := Real.rpow_le_rpow_of_exponent_le hx1 h₂
  have hRa : (boxRadius κ₀ x : ℝ) ≤ 2 * a := by linarith
  have habc : a ^ 3 * b * c = 1 := by
    have h3 : a ^ 3 = x ^ (1 / 7 : ℝ) := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [h3, hbdef, hc, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hl' : Real.log x ≤ 1 / (256 * C) * c := by
    have h2 := hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogpos, abs_of_pos hc0] at h2
    exact h2
  have hsz : boxScale x = 2 * b * Real.log x := rfl
  have hR3 : (boxRadius κ₀ x : ℝ) ^ 3 ≤ 8 * a ^ 3 := by
    calc (boxRadius κ₀ x : ℝ) ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ (by positivity) hRa 3
      _ = 8 * a ^ 3 := by ring
  calc C * (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x ≤ C * (8 * a ^ 3) * boxScale x := by gcongr
    _ = C * (8 * a ^ 3) * (2 * b * Real.log x) := by rw [hsz]
    _ ≤ C * (8 * a ^ 3) * (2 * b * (1 / (256 * C) * c)) := by gcongr
    _ = (a ^ 3 * b * c) / 16 := by
        field_simp
        ring
    _ ≤ 1 / 8 := by
        rw [habc]
        norm_num
theorem abs_log_hemisphereDensity_le {y : imaginaryQuaternions} (hy : ‖y‖ ^ 2 ≤ 1 / 2) :
    0 < hemisphereDensity y ∧ |Real.log (hemisphereDensity y)| ≤ ‖y‖ ^ 2 := by
  set u := ‖y‖ ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : 0 < 1 - u := by linarith
  have hlt : ‖y‖ < 1 := by
    have : ‖y‖ ^ 2 < 1 := by linarith
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  refine ⟨hemisphereDensity_pos hlt, ?_⟩
  have hlog : Real.log (hemisphereDensity y) = -(Real.log (1 - u) / 2) := by
    rw [hemisphereDensity, Real.log_inv, Real.log_sqrt h1.le]
  have h2 : Real.log (1 - u) ≤ 0 := Real.log_nonpos h1.le (by linarith)
  have h3 : 1 - (1 - u)⁻¹ ≤ Real.log (1 - u) := Real.one_sub_inv_le_log_of_pos h1
  have h4 : -(2 * u) ≤ 1 - (1 - u)⁻¹ := by
    have he : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by
      field_simp
      ring
    rw [he, neg_le_neg_iff, div_le_iff₀ h1]
    nlinarith
  rw [hlog, abs_le]
  constructor <;> linarith
end HaarChart
namespace HaarChart
theorem chartJacobian_bounds {ι κ S : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup S]
    [Module ℝ S]
    (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S)) (y : κ → imaginaryQuaternions) {Bd T : ℝ}
    (h0 : LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q) ≠ 0)
    (hB : |Real.log (abs (LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q)))| ≤ Bd)
    (hy : ∀ b, ‖y b‖ ^ 2 ≤ 1 / 2) (hT : ∑ b, ‖y b‖ ^ 2 ≤ T) :
    0 < chartJacobian tl hd V e Q y ∧ |Real.log (chartJacobian tl hd V e Q y)| ≤ Bd + T := by
  have hpos : ∀ b, 0 < hemisphereDensity (y b) := fun b => (abs_log_hemisphereDensity_le (hy b)).1
  have hprod : 0 < ∏ b, hemisphereDensity (y b) := Finset.prod_pos fun b _ => hpos b
  have habs : 0 < |LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q)| := abs_pos.mpr h0
  refine ⟨mul_pos habs hprod, ?_⟩
  rw [chartJacobian, Real.log_mul habs.ne' hprod.ne', Real.log_prod (fun b _ => (hpos b).ne')]
  calc _ ≤ |Real.log (abs (LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q)))| +
        |∑ b, Real.log (hemisphereDensity (y b))| := abs_add_le _ _
    _ ≤ Bd + ∑ b, ‖y b‖ ^ 2 := by
        refine add_le_add hB ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _ => (abs_log_hemisphereDensity_le (hy b)).2))
    _ ≤ Bd + T := by linarith
section Box
variable {n : ℕ} [NeZero n] (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) (K₁ δ : ℝ)
  (E : Set (TorusBond n → imaginaryQuaternions))
theorem measurable_chartJacobian {S : Type} [AddCommGroup S] [Module ℝ S] (e : S →ₗ[ℝ] (TouchingBond o R → imaginaryQuaternions))
    (Q : (TouchingBond o R → imaginaryQuaternions) →ₗ[ℝ] ((SiteInBox o R → imaginaryQuaternions) × S)) :
    Measurable fun ζ : TorusBond n → imaginaryQuaternions =>
      chartJacobian (tailInBox o R) (headInBox o R) (baseLinks o R A) e Q (restrictToBonds o R ζ) := by
  have hres : Measurable (restrictToBonds o R) := measurable_pi_lambda _ fun b => measurable_pi_apply b.1
  have hdet := (continuous_det_chartLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) e Q).abs.measurable
  have hhd : Measurable hemisphereDensity := by
    have : Continuous fun y : imaginaryQuaternions => 1 - ‖y‖ ^ 2 := by fun_prop
    exact (this.measurable.sqrt).inv
  have hpr : Measurable fun y : TouchingBond o R → imaginaryQuaternions => ∏ b, hemisphereDensity (y b) :=
    Finset.measurable_prod _ fun b _ => hhd.comp (measurable_pi_apply b)
  exact (hdet.mul hpr).comp hres
theorem chartJacobian_bound_on_box {S : Type} [AddCommGroup S] [Module ℝ S]
    (e : S →ₗ[ℝ] (TouchingBond o R → imaginaryQuaternions))
    (hR1 : 1 ≤ R) (hδ : 0 ≤ δ) (hK₁ : 1 ≤ K₁) (hsmall : 6 * K₁ * (R : ℝ) ^ 3 * δ ≤ 1 / 8)
    (Q : (TouchingBond o R → imaginaryQuaternions) →ₗ[ℝ] ((SiteInBox o R → imaginaryQuaternions) × S))
    (hQd : ∀ (y : TouchingBond o R → imaginaryQuaternions) (s : ℝ), (∀ b, ‖y b‖ ≤ 1) → 0 ≤ s → s ≤ 1 / 8 →
        24 * ∑ b, ‖y b‖ ^ 2 ≤ s ^ 2 →
        LinearMap.det (chartLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) e y ∘ₗ Q) ≠ 0 ∧
        |Real.log (abs (LinearMap.det (chartLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) e y ∘ₗ Q)))| ≤
          3 * Real.sqrt (Fintype.card (TouchingBond o R × Fin 3)) * s)
    (ζ : TorusBond n → imaginaryQuaternions) (hsq : bondNormSq (supBall o (2 * R)) ζ ≤ K₁ * (R : ℝ) ^ 6 * δ ^ 2)
    (hsup : ∀ b, ‖ζ b‖ ≤ K₁ * (R : ℝ) ^ 3 * δ) :
    0 < chartJacobian (tailInBox o R) (headInBox o R) (baseLinks o R A) e Q (restrictToBonds o R ζ) ∧
      |Real.log (chartJacobian (tailInBox o R) (headInBox o R) (baseLinks o R A) e Q (restrictToBonds o R ζ))| ≤
        676 * K₁ * ((R : ℝ) ^ 5 * δ + (R : ℝ) ^ 6 * δ ^ 2) := by
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hK0 : 0 ≤ K₁ := by linarith
  have hR3 : 0 ≤ (R : ℝ) ^ 3 := by positivity
  have hKd : K₁ * (R : ℝ) ^ 3 * δ ≤ 1 / 48 := by nlinarith
  set y := restrictToBonds o R ζ with hy
  have hsum : ∑ b, ‖y b‖ ^ 2 ≤ K₁ * (R : ℝ) ^ 6 * δ ^ 2 := by
    refine le_trans ?_ hsq
    have h1 : ∑ b, ‖y b‖ ^ 2 = ∑ b ∈ bondsTouching o R, ‖ζ b‖ ^ 2 :=
      Finset.sum_coe_sort (bondsTouching o R) fun b => ‖ζ b‖ ^ 2
    rw [h1, bondNormSq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsWithin_of_touching o hR1 hb) fun b _ _ => by positivity
  set s : ℝ := 5 * (K₁ * (R : ℝ) ^ 3 * δ) with hs
  have hs0 : 0 ≤ s := by positivity
  have hs8 : s ≤ 1 / 8 := by nlinarith
  have hs2 : 24 * ∑ b, ‖y b‖ ^ 2 ≤ s ^ 2 := by
    have h1 : s ^ 2 = 25 * (K₁ * K₁) * ((R : ℝ) ^ 6 * δ ^ 2) := by
      rw [hs]
      ring
    have h2 : 0 ≤ (R : ℝ) ^ 6 * δ ^ 2 := by positivity
    rw [h1]
    nlinarith [mul_nonneg (mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ K₁ - 1)) h2]
  have hy1 : ∀ b, ‖y b‖ ≤ 1 := fun b => (hsup b.1).trans (by linarith)
  have hyh : ∀ b, ‖y b‖ ^ 2 ≤ 1 / 2 := fun b => by
    have h1 : ‖y b‖ ≤ 1 / 48 := (hsup b.1).trans hKd
    nlinarith [norm_nonneg (y b)]
  obtain ⟨hd0, hd1⟩ := hQd y s hy1 hs0 hs8 hs2
  have hcard : ((Fintype.card (TouchingBond o R × Fin 3) : ℕ) : ℝ) ≤ (45 * (R : ℝ) ^ 2) ^ 2 := by
    have h1 : Fintype.card (TouchingBond o R × Fin 3) = (bondsTouching o R).card * 3 := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    have h2 : ((bondsTouching o R).card : ℝ) ≤ 8 * (2 * (R : ℝ) + 1) ^ 4 := by
      exact_mod_cast card_bondsTouching_le o R
    have h3 : (2 * (R : ℝ) + 1) ^ 4 ≤ (3 * (R : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    rw [h1]
    push_cast
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ R) 4]
  have hsq2 : Real.sqrt (Fintype.card (TouchingBond o R × Fin 3)) ≤ 45 * (R : ℝ) ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hcard⟩
  have hBd : 3 * Real.sqrt (Fintype.card (TouchingBond o R × Fin 3)) * s ≤ 675 * K₁ * ((R : ℝ) ^ 5 * δ) := by
    calc 3 * Real.sqrt (Fintype.card (TouchingBond o R × Fin 3)) * s ≤ 3 * (45 * (R : ℝ) ^ 2) * s := by gcongr
      _ = 675 * K₁ * ((R : ℝ) ^ 5 * δ) := by
          rw [hs]
          ring
  obtain ⟨hj0, hj1⟩ := chartJacobian_bounds (tailInBox o R) (headInBox o R) (baseLinks o R A) e Q y hd0 (hd1.trans hBd) hyh hsum
  refine ⟨hj0, hj1.trans ?_⟩
  have hA5 : 0 ≤ (R : ℝ) ^ 5 * δ := by positivity
  have hA6 : 0 ≤ (R : ℝ) ^ 6 * δ ^ 2 := by positivity
  nlinarith [mul_nonneg hK0 hA5, mul_nonneg hK0 hA6]
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  (ι₀ : S →ₗ[ℝ] (TorusBond n → imaginaryQuaternions))
theorem isCompact_slicePreimage (hι₀ : Function.Injective ι₀) (hcl : IsClosed {ζ : S | ι₀ ζ ∈ E})
    (hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0) :
    IsCompact {ζ : S | ι₀ ζ ∈ E} := by
  have hemb : Topology.IsClosedEmbedding ι₀ := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hι₀)
  have hK : IsCompact (ι₀ ⁻¹' Metric.closedBall (0 : TorusBond n → imaginaryQuaternions) 1) :=
    hemb.isCompact_preimage (isCompact_closedBall _ _)
  refine hK.of_isClosed_subset hcl fun ζ hζ => ?_
  refine Metric.mem_closedBall.mpr ((dist_zero_right _).le.trans ?_)
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hE _ hζ).1
theorem injOn_gaugedChart (hι₀ : Function.Injective ι₀)
    (hone : ∀ (W : TorusField n) (γ : TorusSite n → UnitQuaternion) (ζ ζ' : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ → ζ ∈ E → ζ' ∈ E →
      IsInChart (supBall o (2 * R)) A ζ W → IsInChart (supBall o (2 * R)) A ζ' (TorusFields.gaugeTransform γ W) →
      ζ' = ζ ∧ ∀ z, γ z = 1)
    (hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0) :
    Set.InjOn (fun p : (SiteInBox o R → UnitQuaternion) × S =>
      GaugeCharts.gaugeTransform (tailInBox o R) (headInBox o R) p.1
        (hemisphereChartField (baseLinks o R A) (sliceToBonds o R ι₀ p.2)))
      (Set.univ ×ˢ {ζ : S | ι₀ ζ ∈ E}) := by
  rintro ⟨g, ζ⟩ ⟨_, hζ⟩ ⟨g', ζ'⟩ ⟨_, hζ'⟩ h
  have h' : gaugedChartField o R A (ι₀ ζ) g = gaugedChartField o R A (ι₀ ζ') g' := by
    rw [← gaugeTransform_chart_eq o R A _ (hE _ hζ).1 (hE _ hζ).2,
      ← gaugeTransform_chart_eq o R A _ (hE _ hζ').1 (hE _ hζ').2]
    exact h
  obtain ⟨h1, h2⟩ := gaugedChartField_injective o R A _ _ hone hE hζ hζ' h'
  exact Prod.ext h1 (hι₀ h2)
theorem lintegral_slice_eq (hι₀ : Function.Injective ι₀) (μ : Measure S) (hZm : MeasurableSet {ζ : S | ι₀ ζ ∈ E})
    (hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    (Φ : InnerField o R → ENNReal) (Jy : (TouchingBond o R → imaginaryQuaternions) → ℝ)
    (g : SiteInBox o R → UnitQuaternion) :
    ∫⁻ ζ in {ζ : S | ι₀ ζ ∈ E},
        Φ (GaugeCharts.gaugeTransform (tailInBox o R) (headInBox o R) g
          (hemisphereChartField (baseLinks o R A) (sliceToBonds o R ι₀ ζ))) *
          ENNReal.ofReal (Jy (sliceToBonds o R ι₀ ζ)) ∂μ =
      ∫⁻ ζ in E, Φ (gaugedChartField o R A ζ g) * ENNReal.ofReal (Jy (restrictToBonds o R ζ)) ∂(μ.map ι₀) := by
  have hemb : MeasurableEmbedding ι₀ :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hι₀)).measurableEmbedding
  rw [hemb.restrict_map, hemb.lintegral_map]
  refine setLIntegral_congr_fun hZm fun ζ hζ => ?_
  show _ = Φ (gaugedChartField o R A (ι₀ ζ) g) * ENNReal.ofReal (Jy (restrictToBonds o R (ι₀ ζ)))
  rw [← gaugeTransform_chart_eq o R A (ι₀ ζ) (hE _ hζ).1 (hE _ hζ).2]
  rfl
theorem gaugedChart_image_eq (hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0)
    (hsl : ∀ ζ ∈ E, ∃ z, ι₀ z = ζ) :
    {w | ∃ g, ∃ ζ ∈ E, w = gaugedChartField o R A ζ g} =
      (fun p : (SiteInBox o R → UnitQuaternion) × S =>
        GaugeCharts.gaugeTransform (tailInBox o R) (headInBox o R) p.1
          (hemisphereChartField (baseLinks o R A) (sliceToBonds o R ι₀ p.2))) ''
          (Set.univ ×ˢ {ζ : S | ι₀ ζ ∈ E}) := by
  ext w
  constructor
  · rintro ⟨g, ζ, hζ, rfl⟩
    obtain ⟨z, rfl⟩ := hsl ζ hζ
    exact ⟨(g, z), ⟨mem_univ _, hζ⟩, gaugeTransform_chart_eq o R A _ (hE _ hζ).1 (hE _ hζ).2 g⟩
  · rintro ⟨⟨g, ζ⟩, ⟨_, hζ⟩, rfl⟩
    exact ⟨g, ι₀ ζ, hζ, gaugeTransform_chart_eq o R A _ (hE _ hζ).1 (hE _ hζ).2 g⟩
theorem haar_in_chart_of_data (μ : Measure S) [μ.IsAddHaarMeasure]
    (hCV : FreeGaugeActionChangeOfVariables) (hDC : ChartLinearizationDetBound)
    (hR1 : 1 ≤ R) (hδ : 0 ≤ δ) (hK₁ : 1 ≤ K₁) (hsmall : 6 * K₁ * (R : ℝ) ^ 3 * δ ≤ 1 / 8)
    (hι₀ : Function.Injective ι₀)
    (hchar : ∀ v, v ∈ LinearMap.range ι₀ ↔ v ∈ gaugeSlice o R A)
    (hInj : ∀ χ, gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ = 0 → χ = 0)
    (hGr : ∀ (χ : SiteInBox o R → imaginaryQuaternions) (z : SiteInBox o R) (X : imaginaryQuaternions),
      (∀ ψ, ∑ b, inner ℝ (gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 χ b)
        (gaugeLinearization (tailInBox o R) (headInBox o R) (baseLinks o R A) 0 ψ b) = inner ℝ X (ψ z)) →
      ∀ z', ‖χ z'‖ ≤ ‖X‖)
    (hsl : ∀ ζ ∈ E, ζ ∈ gaugeSlice o R A)
    (hcl : IsClosed {ζ : S | ι₀ ζ ∈ E})
    (hbd : ∀ ζ ∈ E, bondNormSq (supBall o (2 * R)) ζ ≤ K₁ * (R : ℝ) ^ 6 * δ ^ 2 ∧
      ∀ b, ‖ζ b‖ ≤ K₁ * (R : ℝ) ^ 3 * δ)
    (hone : ∀ (W : TorusField n) (γ : TorusSite n → UnitQuaternion) (ζ ζ' : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ → ζ ∈ E → ζ' ∈ E →
      IsInChart (supBall o (2 * R)) A ζ W → IsInChart (supBall o (2 * R)) A ζ' (TorusFields.gaugeTransform γ W) →
      ζ' = ζ ∧ ∀ z, γ z = 1) :
    ∃ (c : ℝ) (J : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable J ∧
      (∀ ζ ∈ E, 0 < J ζ ∧ |Real.log (J ζ)| ≤ 676 * K₁ * ((R : ℝ) ^ 5 * δ + (R : ℝ) ^ 6 * δ ^ 2)) ∧
      Set.InjOn (fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions) =>
        gaugedChartField o R A p.2 p.1) (Set.univ ×ˢ E) ∧
      ∀ Φ : InnerField o R → ENNReal, Measurable Φ →
        ∫⁻ w in {w | ∃ g, ∃ ζ ∈ E, w = gaugedChartField o R A ζ g}, Φ w ∂(innerHaar o R) =
          ENNReal.ofReal c * ∫⁻ g, ∫⁻ ζ in E,
            Φ (gaugedChartField o R A ζ g) * ENNReal.ofReal (J ζ) ∂(μ.map ι₀) ∂(boxGaugeHaar o R) := by
  have hKd : K₁ * (R : ℝ) ^ 3 * δ ≤ 1 / 2 := by
    have hX : 0 ≤ K₁ * (R : ℝ) ^ 3 * δ := by
      have : (0 : ℝ) ≤ K₁ := by linarith
      positivity
    nlinarith
  have hoffs : ∀ ζ, ∀ b, b ∉ bondsTouching o R → ι₀ ζ b = 0 := fun ζ b hb =>
    ((hchar _).mp ⟨ζ, rfl⟩).1 b hb
  have hE : ∀ ζ ∈ E, (∀ b, ‖ζ b‖ ≤ 1) ∧ ∀ b, b ∉ bondsTouching o R → ζ b = 0 := fun ζ hζ =>
    ⟨fun b => ((hbd ζ hζ).2 b).trans (by linarith), (hsl ζ hζ).1⟩
  obtain ⟨Q, hQ1, hQ2, hQd⟩ := hDC (SiteInBox o R) (TouchingBond o R) S (tailInBox o R) (headInBox o R) (baseLinks o R A)
    (sliceToBonds o R ι₀) (sliceToBonds_injective o R ι₀ hι₀ hoffs) (mem_range_sliceToBonds_iff o R A ι₀ hchar) hInj hGr
  have hZc := isCompact_slicePreimage o R E ι₀ hι₀ hcl hE
  have hZ1 : ∀ ζ ∈ {ζ : S | ι₀ ζ ∈ E}, ∀ b, ‖sliceToBonds o R ι₀ ζ b‖ < 1 := fun ζ hζ b =>
    (((hbd _ hζ).2 b.1).trans hKd : ‖ι₀ ζ b.1‖ ≤ 1 / 2).trans_lt (by norm_num)
  have hinj := injOn_gaugedChart o R A E ι₀ hι₀ hone hE
  obtain ⟨c, hc, hform⟩ := hCV (SiteInBox o R) (TouchingBond o R) S (tailInBox o R) (headInBox o R) (baseLinks o R A)
    (sliceToBonds o R ι₀) Q _ μ hZc hZ1 hQ1 hQ2 hinj
  refine ⟨c, fun ζ => chartJacobian (tailInBox o R) (headInBox o R) (baseLinks o R A) (sliceToBonds o R ι₀) Q
    (restrictToBonds o R ζ), hc, measurable_chartJacobian o R A _ Q, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact chartJacobian_bound_on_box o R A K₁ δ _ hR1 hδ hK₁ hsmall Q hQd ζ (hbd ζ hζ).1 (hbd ζ hζ).2
  · rintro ⟨g, ζ⟩ ⟨_, hζ⟩ ⟨g', ζ'⟩ ⟨_, hζ'⟩ h
    obtain ⟨h1, h2⟩ := gaugedChartField_injective o R A _ _ hone hE hζ hζ' h
    exact Prod.ext h1 h2
  · intro Φ hΦ
    rw [gaugedChart_image_eq o R A E ι₀ hE fun ζ hζ => by
      obtain ⟨z, hz⟩ := (hchar ζ).mpr (hsl ζ hζ)
      exact ⟨z, hz⟩]
    refine (hform Φ hΦ).trans ?_
    congr 1
    exact lintegral_congr fun g => lintegral_slice_eq o R A E ι₀ hι₀ μ hZc.isClosed.measurableSet hE Φ
      (chartJacobian (tailInBox o R) (headInBox o R) (baseLinks o R A) (sliceToBonds o R ι₀) Q) g
end Box
end HaarChart
open HaarChart in
theorem chartChangeOfVariables_proof (hOne : chartMeetsOrbitOnceStatement) (hGap : covariantGradientGapStatement)
    (hBd : ellipsoidBoundsStatement) (hForm : cubeHessianStatement)
    (hCV : FreeGaugeActionChangeOfVariables) (hDC : ChartLinearizationDetBound) :
    chartChangeOfVariablesStatement := by
  intro Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨xs₁, hO⟩ := hOne Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨K₁, xs₂, hK₁, hB⟩ := hBd Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨CQ, R₀, hCQ, hFm⟩ := hForm Tb hTb
  obtain ⟨xs₃, hx₃⟩ := eventually_atTop.mp (eventually_scale_small κ₀ h1 h2 (show 0 < 6 * K₁ by linarith) R₀)
  refine ⟨676 * K₁, max xs₁ (max xs₂ xs₃), ?_⟩
  intro x R k n _ o A hxs hR h16 hA
  have hx1 : xs₁ ≤ x := (le_max_left _ _).trans hxs
  have hx2 : xs₂ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hxs
  have hx3 : xs₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hxs
  obtain ⟨hδ, hR1, hRR, hsm⟩ := hx₃ x hx3
  rw [← hR] at hR1 hRR hsm
  obtain ⟨_, hform⟩ := (hB x R k n o A hx2 hR h16 hA)
  have hfm := hFm k n o R hRR h16
  have hcl : IsClosed {ζ : gaugeSlice o R A |
      hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (A + ζ.1) (A + ζ.1) ≤ C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2} := by
    have hlc : ∀ e : Fin 3, Continuous (imaginaryComponent e) := by
      intro e
      fin_cases e
      · exact Quaternion.continuous_imI.comp continuous_subtype_val
      · exact Quaternion.continuous_imJ.comp continuous_subtype_val
      · exact Quaternion.continuous_imK.comp continuous_subtype_val
    refine isClosed_le ?_ continuous_const
    have hform' := hfm.2.2.2.2.2.2
    simp only [hform']
    refine continuous_finset_sum _ fun e _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun b' _ => ?_
    have hv : ∀ b₀ : TorusBond n, Continuous fun ζ : gaugeSlice o R A => imaginaryComponent e ((A + ζ.1) b₀) := fun b₀ =>
      (hlc e).comp (continuous_const.add ((continuous_apply b₀).comp continuous_subtype_val))
    exact (continuous_const.mul (hv b)).mul (hv b')
  obtain ⟨hInj, hGr⟩ := linearization_injective_and_green hGap o hR1 (by omega) A
  refine haar_in_chart_of_data (S := gaugeSlice o R A) o R A K₁ (boxScale x) _ (gaugeSlice o R A).subtype Measure.addHaar
    hCV hDC hR1 hδ hK₁ (by simpa using hsm) ?_ ?_ hInj hGr (fun ζ hζ => hζ.1) ?_
    (fun ζ hζ => ⟨(hform ζ hζ).1, (hform ζ hζ).2.1⟩)
    (fun W γ ζ ζ' hγ hζ hζ' hc hc' => hO x R k n o A hx1 hR h16 hA W γ ζ ζ' hγ hζ hζ' hc hc')
  · exact fun a b h => Subtype.ext h
  · intro v
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro h
      exact ⟨⟨v, h⟩, rfl⟩
  · convert hcl using 1
    · rfl
    · ext ζ
      exact ⟨fun h => h.2, fun h => ⟨ζ.2, h⟩⟩
end YangMills.Construction.BoxGaussian
end
