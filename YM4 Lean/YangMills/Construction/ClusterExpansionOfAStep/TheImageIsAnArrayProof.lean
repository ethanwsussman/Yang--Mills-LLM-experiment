import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsGaugeInvariant
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
namespace KernelImageDensity
variable {n : ℕ} [NeZero n]
theorem kernelImage_eq_integral (ℓ : StepParameters) (x : ℝ) (D : TorusFunctional) (V : TorusField n) :
    kernelImage ℓ x D n V = ∫ W : TorusField (n * ℓ.side), D (n * ℓ.side) W *
      averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar (n * ℓ.side)) := by
  simp [kernelImage, NeZero.ne n]
theorem measurable_slice_right {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (f : A × B → ℝ)
    (hf : Measurable f) (b : B) :
    Measurable fun a => f (a, b) :=
  hf.comp measurable_prodMk_right
theorem measurable_mul_of {A : Type*} [MeasurableSpace A] {d k : A → ℝ} (hd : Measurable d)
    (hk : Measurable k) :
    Measurable fun a => d a * k a :=
  hd.mul hk
theorem integral_mul_eq_of_measurePreserving {A : Type*} [MeasurableSpace A] (μ : Measure A) (Ψ : A → A)
    (hΨ : MeasurePreserving Ψ μ μ) (d k k' : A → ℝ) (hd : Measurable d) (hk' : Measurable k')
    (hinv : ∀ a, d (Ψ a) = d a) (hk : ∀ a, k' (Ψ a) = k a) :
    ∫ a, d a * k' a ∂μ = ∫ a, d a * k a ∂μ := by
  have h1 := integral_map (μ := μ) hΨ.measurable.aemeasurable (f := fun a => d a * k' a)
    (measurable_mul_of hd hk').aestronglyMeasurable
  rw [hΨ.map_eq] at h1
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show d (Ψ a) * k' (Ψ a) = _
  rw [hinv, hk]
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_contourMean_le_one {F : BlockFrame} (J₀ : ℕ) (H : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    ‖contourMean J₀ H b W c‖ ≤ 1 := by apply _root_.YangMills.Construction.WeightedResponses.norm_contourMean_le <;> assumption
theorem bondKernel_le_exp (hK : BondKernelProperties) (ℓ : StepParameters) (hadm : ℓ.Admissible) {x : ℝ}
    (hx : 0 < x) {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x W V b c ≤ Real.exp (ℓ.coupling * x) := by
  have ha : 0 < ℓ.coupling := lt_of_lt_of_le one_pos hadm.a_ge
  have hax : 0 < ℓ.coupling * x := mul_pos ha hx
  unfold bondKernel
  simp only
  set q := contourMean ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W)
    b W c with hq
  have hq1 : ‖q‖ ≤ 1 := norm_contourMean_le_one _ _ _ _ _
  have hz : 1 ≤ partitionFn (ℓ.coupling * x * ‖q‖) := (hK.1 _ (by positivity)).1
  have hre : (q * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re ≤ 1 := by
    have h1 : |(q * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| ≤
        ‖q * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ :=
      abs_re_le_norm _
    rw [norm_mul, norm_unitQuaternion, mul_one] at h1
    exact (le_abs_self _).trans (h1.trans hq1)
  calc _ ≤ Real.exp (ℓ.coupling * x * (q * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) :=
        div_le_self (Real.exp_pos _).le hz
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith
theorem bondKernel_nonneg (hK : BondKernelProperties) (ℓ : StepParameters) {x : ℝ} {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    0 ≤ bondKernel ℓ x W V b c := ((hK.2 ℓ x n W V b c).1).le
theorem averagedKernel_nonneg (hK : BondKernelProperties) (ℓ : StepParameters) (x : ℝ)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1) :
    0 ≤ averagedKernel ℓ x W V := by
  unfold averagedKernel
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => Finset.prod_nonneg fun c _ => ?_)
  exact bondKernel_nonneg hK ℓ W V b c
theorem averagedKernel_le (hK : BondKernelProperties) (ℓ : StepParameters) (hadm : ℓ.Admissible) {x : ℝ}
    (hx : 0 < x)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1) :
    averagedKernel ℓ x W V ≤
      Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4) := by
  have hM : (1 : ℝ) ≤ Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4) := by
    have ha : 0 < ℓ.coupling := lt_of_lt_of_le one_pos hadm.a_ge
    exact one_le_pow₀ (Real.one_le_exp (mul_pos ha hx).le)
  have hprod : ∀ b, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x W V b c ≤
      Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4) := by
    intro b
    calc _ ≤ ∏ _c : (stepBlockFrame ℓ.side n).Cell × Fin 4, Real.exp (ℓ.coupling * x) :=
          Finset.prod_le_prod (fun c _ => bondKernel_nonneg hK ℓ W V b c)
            (fun c _ => bondKernel_le_exp hK ℓ hadm hx W V b c)
      _ = _ := by simp
  unfold averagedKernel
  by_cases h0 : ((baseChoices ℓ W).card : ℝ) = 0
  · simp only [h0]
    simp only [div_zero, zero_mul]
    linarith
  · have hp : 0 < ((baseChoices ℓ W).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
    have hs : ∑ b ∈ baseChoices ℓ W, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, bondKernel ℓ x W V b c ≤
        ((baseChoices ℓ W).card : ℝ) *
          Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4) := by
      have := Finset.sum_le_card_nsmul (baseChoices ℓ W) _ _ (fun b _ => hprod b)
      simpa using this
    calc _ ≤ 1 / ((baseChoices ℓ W).card : ℝ) * (((baseChoices ℓ W).card : ℝ) *
          Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4)) := by gcongr
      _ = _ := by field_simp
theorem kernelImage_eq_of_carried (ℓ : StepParameters) (x : ℝ) (D : TorusFunctional)
    (hD : Measurable (D (n * ℓ.side)))
    (hB : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      averagedKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2))
    (Ψ : TorusField (n * ℓ.side) → TorusField (n * ℓ.side))
    (hΨ : MeasurePreserving Ψ (fieldHaar (n * ℓ.side)) (fieldHaar (n * ℓ.side)))
    (hinv : ∀ W, D (n * ℓ.side) (Ψ W) = D (n * ℓ.side) W) (V V' : TorusField n)
    (hk : ∀ W, averagedKernel ℓ x (fineLevelField ℓ n (Ψ W)) (coarseLevelField ℓ n V') =
      averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)) :
    kernelImage ℓ x D n V' = kernelImage ℓ x D n V := by
  rw [kernelImage_eq_integral, kernelImage_eq_integral]
  exact integral_mul_eq_of_measurePreserving _ Ψ hΨ (D (n * ℓ.side)) _ _ hD
    (measurable_slice_right _ hB V') hinv hk
end KernelImageDensity
set_option maxHeartbeats 1000000 in
open KernelImageDensity in
theorem kernelImageIsDensity_holds (hK : BondKernelProperties) (hB : BondKernelBorel)
    (hT : ExpansionBasicBounds) (hH : FieldHaar.HaarInvariantUnderSymmetries)
    (hG : KernelImageGaugeInvariant) (hI : IsometriesPreserveAveragedKernel) :
    KernelImageIsDensity := by
  intro ℓ hadm t x D hx hr hrow n _ hn
  have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnL : ℓ.n₀ ≤ n * ℓ.side := hn.trans (Nat.le_mul_of_pos_right _ hLpos)
  obtain ⟨hD, f, hc, Λ, Dq, Φ, φ, hh⟩ := hrow
  obtain ⟨hDm, hDn, hDg, hDi⟩ := hD (n * ℓ.side) hnL
  have hBk := (hB ℓ x n).2.2.2.2.2.2.1
  have hbound := (hT ℓ t x D f Λ Dq Φ φ hadm hadm.E_ge hx hr hc hh).2.2 (n * ℓ.side)
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  refine ⟨fun V => ?_, ?_, fun V => ?_, fun g V => ?_, fun g V V' hV => ?_⟩
  · have hm : Measurable fun W : TorusField (n * ℓ.side) => D (n * ℓ.side) W *
        averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) :=
      measurable_mul_of hDm (measurable_slice_right _ hBk V)
    refine Integrable.of_bound hm.aestronglyMeasurable
      ((D (n * ℓ.side) (trivialField (n * ℓ.side)) * 2 ^ Fintype.card (TorusSite (n * ℓ.side)) *
        Real.exp (2 * ℓ.E * Fintype.card (TorusSite (n * ℓ.side)))) *
        Real.exp (ℓ.coupling * x) ^ Fintype.card ((stepBlockFrame ℓ.side n).Cell × Fin 4))
      (Filter.Eventually.of_forall fun W => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hDn W) (averagedKernel_nonneg hK ℓ x _ _))]
    exact mul_le_mul (hbound W) (averagedKernel_le hK ℓ hadm hx _ _) (averagedKernel_nonneg hK ℓ x _ _)
      ((hDn W).trans (hbound W))
  · have hjoint : StronglyMeasurable fun p : TorusField n × TorusField (n * ℓ.side) => D (n * ℓ.side) p.2 *
        averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 p.2)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 p.1) :=
      ((hDm.comp measurable_snd).mul (hBk.comp (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
    have := (hjoint.integral_prod_right' (ν := fieldHaar (n * ℓ.side))).measurable
    have e : kernelImage ℓ x D n = fun V : TorusField n => ∫ W : TorusField (n * ℓ.side), D (n * ℓ.side) W *
        averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar (n * ℓ.side)) :=
      funext fun V => kernelImage_eq_integral ℓ x D V
    rw [e]
    exact this
  · rw [kernelImage_eq_integral]
    exact integral_nonneg fun W => mul_nonneg (hDn W) (averagedKernel_nonneg hK ℓ x _ _)
  · exact hG ℓ hadm x D n hDg g V
  · obtain ⟨Ψ, hΨ, hc'⟩ := (hH (n * ℓ.side)).2 (g.scaledLift ℓ.side)
    exact kernelImage_eq_of_carried ℓ x D hDm hBk Ψ hΨ (fun W => hDi _ W _ (hc' W)) V V'
      (fun W => hI ℓ hadm x n hn g W (Ψ W) V V' (hc' W) hV)
end YangMills.Construction.TorusLumps
end
