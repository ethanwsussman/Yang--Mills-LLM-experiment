import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorReadsItsBox
import YangMills.Construction.CovarianceOfTheMarks.DrawsBelowKeepTheirLaw
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.ResponseInTheExpansion.ChainIsMarkovBackwards
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.HessiansOfTheMirrorAndOfTheFlatTorus
import YangMills.Construction.ResponseInTheExpansion.LawOfAStepIsCarriedByGauges
import YangMills.Construction.ResponseInTheExpansion.MirrorOfAColdBoxIsCold
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClear
import YangMills.Construction.ResponseInTheExpansion.OneStepIsTheLawOfTheMirror
import YangMills.Construction.RunningCouplingSlope.LaplaceTotalIsAGaugeFunctionProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScaleProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps StepSettings RenormalizationStepParameters
  MarkedIntegrals StepCosts
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def stepCurvatureMomentsAt : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ C c x₀ : ℝ, 0 < c ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (j d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d' N))
      (g : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → TorusSite (fineSide (Tb.stepParameters y).side d' N) →
        UnitQuaternion)
      (s : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → ℝ)
      (l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) → ℝ) (e : Fin r → Fin 3),
      IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x₀ →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d' N →
      j < localChainDepth (Tb.stepParameters y) β k →
      j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k →
      Measurable[upperSigma T (k + j + 1) d' N] g → Measurable[upperSigma T (k + j + 1) d' N] s → (∀ u, 0 ≤ s u) →
      (∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j) →
      (∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉
          supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) →
      Integrable (Set.indicator
          {u' | Disjoint (stageState T (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u')).2.1
              (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
            StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o
              (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u')}
          (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T (k + j) (g u')
            (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
              3 * localLogScale (Tb.stepParameters y) β k))
            (topField (Tb.stepParameters y) (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u'))
            (topField (Tb.stepParameters y) (k + j) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u').1) b)))
        (markedSampleLaw T β (k + j + 1 + d') N) ∧
      ∀ᵐ u ∂(markedSampleLaw T β (k + j + 1 + d') N),
        Disjoint (stageState T (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u)).2.1
            (supBall o (localBlockSide (Tb.stepParameters y) β k)) →
        IsNearIdentity (g u)
            (topField (Tb.stepParameters y) (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u)) o
            (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) (s u) →
        |((markedSampleLaw T β (k + j + 1 + d') N)[Set.indicator
              {u' | Disjoint (stageState T (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u')).2.1
                  (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
                StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o
                  (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u')}
              (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T (k + j) (g u')
                (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
                  3 * localLogScale (Tb.stepParameters y) β k))
                (topField (Tb.stepParameters y) (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u'))
                (topField (Tb.stepParameters y) (k + j) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u').1) b)) |
            upperSigma T (k + j + 1) d' N]) u -
          flowCouplings (Tb.stepParameters y) β (k + j) ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' =>
            if e i = e i' then
              stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j)
                (fineSide (Tb.stepParameters y).side d' N) (l i) (l i')
            else 0| ≤
          C * (1 / 2 : ℝ) ^ j * (flowCouplings (Tb.stepParameters y) β k ^ (-((r : ℝ) + 1) / 2) +
              flowCouplings (Tb.stepParameters y) β k ^ (-(r : ℝ) / 2) * s u) +
            Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))
def stepCurvatureMomentsStatement : Prop := HoldsOnParameterFamilies stepCurvatureMomentsAt
end YangMills.Construction.ResponseInTheExpansion
end

noncomputable section
namespace YangMills.Construction
open BlockAverages hiding adjointAction
open LumpContours ColdStepAtMirrorFrames
open StepCosts (torusSiteInFrame)
namespace ResponseInTheExpansion
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses MarkedIntegrals
open Classical
open MeasureTheory
namespace StepCurvatureMoments
section Abstract
variable {Ω Ω' Φ : Type*} [Fintype Φ] {𝓕 mΩ : MeasurableSpace Ω} {𝓢 mΩ' : MeasurableSpace Ω'}
private theorem condExp_comp_eq_map {μ : Measure Ω} [IsFiniteMeasure μ] {π : Ω → Ω'} (hπ : Measurable π)
    (hm' : 𝓢 ≤ mΩ') {f : Ω' → ℝ} (hf : Integrable f (μ.map π)) :
    μ[f ∘ π | 𝓢.comap π] =ᵐ[μ] ((μ.map π)[f | 𝓢]) ∘ π := by
  have hm : 𝓢.comap π ≤ mΩ := (MeasurableSpace.comap_mono hm').trans hπ.comap_le
  have hfi : Integrable (f ∘ π) μ := hf.comp_measurable hπ
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfi (fun s _ _ => ?_) ?_ ?_
  · exact ((integrable_condExp (μ := μ.map π) (m := 𝓢) (f := f)).comp_measurable hπ).integrableOn
  · rintro _ ⟨t, ht, rfl⟩ _
    have ht' := hm' t ht
    have e1 : ∫ u in π ⁻¹' t, ((μ.map π)[f | 𝓢] ∘ π) u ∂μ = ∫ v in t, ((μ.map π)[f | 𝓢]) v ∂(μ.map π) :=
      (setIntegral_map ht' (stronglyMeasurable_condExp.mono hm').aestronglyMeasurable hπ.aemeasurable).symm
    have e2 : ∫ u in π ⁻¹' t, (f ∘ π) u ∂μ = ∫ v in t, f v ∂(μ.map π) :=
      (setIntegral_map ht' hf.aestronglyMeasurable hπ.aemeasurable).symm
    rw [e1, e2]
    exact setIntegral_condExp hm' hf ht
  · exact ((stronglyMeasurable_condExp (μ := μ.map π) (m := 𝓢) (f := f)).comp_measurable
      (comap_measurable π)).aestronglyMeasurable
private theorem condExp_finite_sum_near {μ : Measure Ω} [IsProbabilityMeasure μ] (h𝓕 : 𝓕 ≤ mΩ)
    {π : Ω → Ω'} (hπ : Measurable π) (h𝓢 : 𝓢 ≤ mΩ')
    (Cf : Φ → Ω → ℝ) (hC : ∀ φ, Measurable[𝓕] (Cf φ)) (K : ℝ) (hK : ∀ u, ∑ φ, |Cf φ u| ≤ K)
    (G : Φ → Ω' → ℝ) (hG : ∀ φ, Measurable (G φ)) (hG1 : ∀ φ v, |G φ v| ≤ 1)
    (hM : ∀ φ, μ[G φ ∘ π | 𝓕] =ᵐ[μ] μ[G φ ∘ π | 𝓢.comap π])
    (M : Φ → Ω' → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (E : Ω' → Prop)
    (hN : ∀ φ, ∀ᵐ v ∂(μ.map π), E v → |((μ.map π)[G φ | 𝓢]) v - M φ v| ≤ δ) :
    Integrable (fun u => ∑ φ, Cf φ u * G φ (π u)) μ ∧
    ∀ᵐ u ∂μ, E (π u) →
      |(μ[fun u => ∑ φ, Cf φ u * G φ (π u) | 𝓕]) u - ∑ φ, Cf φ u * M φ (π u)| ≤ K * δ := by
  have : IsProbabilityMeasure (μ.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hCb : ∀ φ u, |Cf φ u| ≤ K := fun φ u =>
    le_trans (Finset.single_le_sum (f := fun φ => |Cf φ u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ φ)) (hK u)
  have hGi : ∀ φ, Integrable (G φ ∘ π) μ := fun φ =>
    Integrable.of_bound ((hG φ).comp hπ).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun u => by simpa using hG1 φ (π u))
  have hGi' : ∀ φ, Integrable (G φ) (μ.map π) := fun φ =>
    Integrable.of_bound (hG φ).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun u => by simpa using hG1 φ u)
  have hCs : ∀ φ, StronglyMeasurable[𝓕] (Cf φ) := fun φ => (hC φ).stronglyMeasurable
  have hterm : ∀ φ, Integrable (Cf φ * (G φ ∘ π)) μ := fun φ =>
    Integrable.of_bound (((hC φ).mono h𝓕 le_rfl).mul ((hG φ).comp hπ)).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun u => by
        have h1 := hCb φ u
        have h2 := hG1 φ (π u)
        simp only [Pi.mul_apply, Function.comp, Real.norm_eq_abs, abs_mul]
        calc |Cf φ u| * |G φ (π u)| ≤ K * 1 := mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
          _ = K := mul_one K)
  have hsum : (fun u => ∑ φ, Cf φ u * G φ (π u)) = ∑ φ, Cf φ * (G φ ∘ π) := by
    funext u
    simp [Finset.sum_apply]
  refine ⟨integrable_finsetSum Finset.univ fun φ _ => hterm φ, ?_⟩
  have e1 : μ[fun u => ∑ φ, Cf φ u * G φ (π u) | 𝓕] =ᵐ[μ] ∑ φ, μ[Cf φ * (G φ ∘ π) | 𝓕] := by
    rw [hsum]
    exact condExp_finsetSum (fun φ _ => hterm φ) 𝓕
  have e2 : ∀ φ, μ[Cf φ * (G φ ∘ π) | 𝓕] =ᵐ[μ] Cf φ * ((μ.map π)[G φ | 𝓢] ∘ π) := fun φ => by
    have a1 := condExp_mul_of_stronglyMeasurable_left (hCs φ) (hterm φ) (hGi φ)
    have a2 := (hM φ).trans (condExp_comp_eq_map hπ h𝓢 (hGi' φ))
    exact a1.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) a2)
  have e2' : ∀ᵐ u ∂μ, ∀ φ, (μ[Cf φ * (G φ ∘ π) | 𝓕]) u = Cf φ u * ((μ.map π)[G φ | 𝓢]) (π u) :=
    (ae_all_iff.mpr fun φ => (e2 φ).mono fun u h => by simpa using h)
  have e3 : ∀ᵐ u ∂μ, ∀ φ, E (π u) → |((μ.map π)[G φ | 𝓢]) (π u) - M φ (π u)| ≤ δ :=
    ae_all_iff.mpr fun φ => ae_of_ae_map hπ.aemeasurable (hN φ)
  filter_upwards [e1, e2', e3] with u h1 h2 h3 hE
  rw [h1, Finset.sum_apply, Finset.sum_congr rfl fun φ _ => h2 φ, ← Finset.sum_sub_distrib]
  calc |∑ φ, (Cf φ u * ((μ.map π)[G φ | 𝓢]) (π u) - Cf φ u * M φ (π u))|
      ≤ ∑ φ, |Cf φ u * ((μ.map π)[G φ | 𝓢]) (π u) - Cf φ u * M φ (π u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ φ, |Cf φ u| * δ := Finset.sum_le_sum fun φ _ => by
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (h3 φ hE) (abs_nonneg _)
    _ = (∑ φ, |Cf φ u|) * δ := by rw [Finset.sum_mul]
    _ ≤ K * δ := mul_le_mul_of_nonneg_right (hK u) hδ
end Abstract
section Rotation
private def basisImaginary (a : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single a 1)
private theorem imaginaryComponent_add (e : Fin 3) (X Y : imaginaryQuaternions) :
    imaginaryComponent e (X + Y) = imaginaryComponent e X + imaginaryComponent e Y := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_smul (e : Fin 3) (c : ℝ) (X : imaginaryQuaternions) :
    imaginaryComponent e (c • X) = c * imaginaryComponent e X := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_zero (e : Fin 3) : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
  fin_cases e <;> rfl
private def imaginaryComponentHom (e : Fin 3) : imaginaryQuaternions →+ ℝ where
  toFun := imaginaryComponent e
  map_zero' := imaginaryComponent_zero e
  map_add' := imaginaryComponent_add e
private theorem imaginaryComponent_sum {ι : Type*} (e : Fin 3) (s : Finset ι) (f : ι → imaginaryQuaternions) :
    imaginaryComponent e (∑ b ∈ s, f b) = ∑ b ∈ s, imaginaryComponent e (f b) :=
  map_sum (imaginaryComponentHom e) f s
private theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    adjointAction g (X + Y) = adjointAction g X + adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (X : imaginaryQuaternions) :
    adjointAction g (c • X) = c • adjointAction g X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
private theorem imaginary_ext {X Y : imaginaryQuaternions} (h : ∀ e, imaginaryComponent e X = imaginaryComponent e Y) :
    X = Y := by
  apply Subtype.ext
  have hX : (X : Quaternion ℝ).re = 0 := X.2
  have hY : (Y : Quaternion ℝ).re = 0 := Y.2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [imaginaryComponent] at h0 h1 h2
  ext
  · rw [hX, hY]
  · simpa using h0
  · simpa using h1
  · simpa using h2
private theorem imaginaryComponent_basis (e a : Fin 3) :
    imaginaryComponent e (basisImaginary a) = if e = a then 1 else 0 := by
  fin_cases e <;> fin_cases a <;> simp [imaginaryComponent, basisImaginary, toImaginary]
private theorem imaginary_expand (w : imaginaryQuaternions) :
    w = imaginaryComponent 0 w • basisImaginary 0 + imaginaryComponent 1 w • basisImaginary 1 +
      imaginaryComponent 2 w • basisImaginary 2 := by
  apply imaginary_ext
  intro e
  simp only [imaginaryComponent_add, imaginaryComponent_smul, imaginaryComponent_basis]
  fin_cases e <;> simp
private def rotationEntry (g : UnitQuaternion) (e a : Fin 3) : ℝ :=
  imaginaryComponent e (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (basisImaginary a))
private theorem imaginaryComponent_adjointAction (g : UnitQuaternion) (e : Fin 3) (w : imaginaryQuaternions) :
    imaginaryComponent e (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g w) = ∑ a, rotationEntry g e a * imaginaryComponent a w := by
  conv_lhs => rw [imaginary_expand w]
  simp only [adjointAction_add, adjointAction_smul, imaginaryComponent_add, imaginaryComponent_smul,
    Fin.sum_univ_three, rotationEntry]
  ring
private theorem abs_imaginaryComponent_le (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryComponent e w| ≤ ‖(w : Quaternion ℝ)‖ := by
  have hn : Quaternion.normSq (w : Quaternion ℝ) = ‖(w : Quaternion ℝ)‖ * ‖(w : Quaternion ℝ)‖ :=
    Quaternion.normSq_eq_norm_mul_self _
  have hd := Quaternion.normSq_def' (w : Quaternion ℝ)
  have h : imaginaryComponent e w ^ 2 ≤ ‖(w : Quaternion ℝ)‖ ^ 2 := by
    rw [sq ‖(w : Quaternion ℝ)‖, ← hn, hd]
    fin_cases e <;> simp only [imaginaryComponent] <;> simp <;> nlinarith [sq_nonneg (w : Quaternion ℝ).re,
      sq_nonneg (w : Quaternion ℝ).imI, sq_nonneg (w : Quaternion ℝ).imJ, sq_nonneg (w : Quaternion ℝ).imK]
  rw [← sq_abs] at h
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp h
abbrev _root_.YangMills.SharedProofs.p13926 := @abs_imaginaryComponent_le
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖(adjointAction g X : Quaternion ℝ)‖ = ‖(X : Quaternion ℝ)‖ := by apply _root_.YangMills.SharedProofs.p17728 <;> assumption
private theorem norm_basisImaginary (a : Fin 3) : ‖(basisImaginary a : Quaternion ℝ)‖ = 1 := by
  have hn := Quaternion.normSq_eq_norm_mul_self (basisImaginary a : Quaternion ℝ)
  have hd := Quaternion.normSq_def' (basisImaginary a : Quaternion ℝ)
  have h1 : ‖(basisImaginary a : Quaternion ℝ)‖ * ‖(basisImaginary a : Quaternion ℝ)‖ = 1 := by
    rw [← hn, hd]
    fin_cases a <;> simp [basisImaginary, toImaginary]
  have h3 : 0 ≤ ‖(basisImaginary a : Quaternion ℝ)‖ := norm_nonneg _
  nlinarith
private theorem abs_rotationEntry_le (g : UnitQuaternion) (e a : Fin 3) : |rotationEntry g e a| ≤ 1 := by
  have := abs_imaginaryComponent_le e (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (basisImaginary a))
  rwa [norm_adjointAction, norm_basisImaginary] at this
private theorem continuous_rotationEntry (e a : Fin 3) : Continuous fun g : UnitQuaternion => rotationEntry g e a := by
  have h : Continuous fun g : UnitQuaternion =>
      (g : Quaternion ℝ) * (basisImaginary a : Quaternion ℝ) * star (g : Quaternion ℝ) :=
    (continuous_subtype_val.mul continuous_const).mul (continuous_star.comp continuous_subtype_val)
  have e' : ∀ g : UnitQuaternion, ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (basisImaginary a) : imaginaryQuaternions) : Quaternion ℝ) =
      (g : Quaternion ℝ) * (basisImaginary a : Quaternion ℝ) * star (g : Quaternion ℝ) := fun g => rfl
  fin_cases e
  · exact (Quaternion.continuous_imI.comp h).congr fun g => by simp [rotationEntry, imaginaryComponent, e']
  · exact (Quaternion.continuous_imJ.comp h).congr fun g => by simp [rotationEntry, imaginaryComponent, e']
  · exact (Quaternion.continuous_imK.comp h).congr fun g => by simp [rotationEntry, imaginaryComponent, e']
private def clampUnit (t : ℝ) : ℝ := max (-1) (min 1 t)
private theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)
private theorem abs_clampUnit_le (t : ℝ) : |clampUnit t| ≤ 1 := by
  unfold clampUnit
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
private theorem clampUnit_of_abs_le {t : ℝ} (h : |t| ≤ 1) : clampUnit t = t := by
  unfold clampUnit
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [min_eq_right h2, max_eq_right h1]
private theorem prod_sum_eq_sum_prod {ι P : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] (c X : ι → P → ℝ) :
    ∏ i, ∑ p, c i p * X i p = ∑ φ : ι → P, (∏ i, c i (φ i)) * ∏ i, X i (φ i) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun φ _ => Finset.prod_mul_distrib
private theorem sum_abs_prod_le_pow {ι P : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] (c : ι → P → ℝ) (K : ℝ)
    (_hK0 : 0 ≤ K) (hK : ∀ i, ∑ p, |c i p| ≤ K) : ∑ φ : ι → P, |∏ i, c i (φ i)| ≤ K ^ Fintype.card ι := by
  have e : ∑ φ : ι → P, |∏ i, c i (φ i)| = ∏ i, ∑ p, |c i p| := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun φ _ => Finset.abs_prod _ _
  rw [e, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun p _ => abs_nonneg _) fun i _ => hK i
end Rotation
section Draws
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem measurable_sampleBelow (s d : ℕ) : ∀ n : ℕ, Measurable (sampleBelow ℓ s d n) := by
  induction d with
  | zero => intro n; exact measurable_id
  | succ d ih =>
    intro n
    exact (ih (n * ℓ.side)).comp measurable_fst
abbrev _root_.YangMills.SharedProofs.p11381 := @measurable_sampleBelow
private theorem upperSigma_le (T : StageTower ℓ) (t : ℕ)
    (hs : ∀ (n : ℕ) [NeZero n], stageSigma T t n ≤ markedSampleMeasurableSpace ℓ t n) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n], upperSigma T t d n ≤ markedSampleMeasurableSpace ℓ (t + d) n := by
  induction d with
  | zero => intro n _; exact hs n
  | succ d ih =>
    intro n _
    refine sup_le ?_ ?_
    · exact (MeasurableSpace.comap_mono (ih (n * ℓ.side))).trans measurable_fst.comap_le
    · exact measurable_snd.comap_le
private def avoidSet (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (m : ℝ) :
    Set (MarkedSample ℓ (t + 1) n) :=
  {u | Disjoint (stageState T (t + 1) n u).2.1 (supBall o m) ∧ StepAvoids T t m o u}
private def truncatedComponent (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (σ m : ℝ)
    (u : MarkedSample ℓ (t + 1) n) (b : TorusBond (n * ℓ.side)) (a : Fin 3) : ℝ :=
  Set.indicator {q : TorusField n × TorusField (n * ℓ.side) | IsColdOnBall σ q.1 o m}
    (fun q => imaginaryComponent a (stepDeviation T t q.1 q.2 b)) (topField ℓ (t + 1) n u, topField ℓ t (n * ℓ.side) u.1)
private theorem truncatedComponent_of_cold (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (σ m : ℝ)
    (v : MarkedSample ℓ (t + 1) n) (b : TorusBond (n * ℓ.side)) (a : Fin 3)
    (hc : IsColdOnBall σ (topField ℓ (t + 1) n v) o m) :
    truncatedComponent T t o σ m v b a =
      imaginaryComponent a (stepDeviation T t (topField ℓ (t + 1) n v) (topField ℓ t (n * ℓ.side) v.1) b) := by
  unfold truncatedComponent
  rw [Set.indicator_of_mem]
  exact hc
private def rotatedCoeff {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (l : TorusBond (n * ℓ.side) → ℝ) (e : Fin 3)
    (p : TorusBond (n * ℓ.side) × Fin 3) : ℝ :=
  l p.1 * rotationEntry (g (parentBlock ℓ.side p.1.1)) e p.2
private theorem imaginaryComponent_deviation_sum (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n]
    (g : TorusSite n → UnitQuaternion) (B : Finset (TorusSite n))
    (V : TorusField n) (W : TorusField (n * ℓ.side)) (l : TorusBond (n * ℓ.side) → ℝ) (e : Fin 3) :
    imaginaryComponent e (∑ b, l b • deviationInGauge T t g B V W b) =
      ∑ p : ↥(chartBondsInBlocks ℓ.side B) × Fin 3,
        rotatedCoeff g l e (p.1.1, p.2) * imaginaryComponent p.2 (stepDeviation T t V W p.1.1) := by
  rw [imaginaryComponent_sum]
  have h1 : ∀ b : TorusBond (n * ℓ.side), imaginaryComponent e (l b • deviationInGauge T t g B V W b) =
      if b ∈ chartBondsInBlocks ℓ.side B then
        ∑ a, rotatedCoeff g l e (b, a) * imaginaryComponent a (stepDeviation T t V W b) else 0 := fun b => by
    rw [imaginaryComponent_smul]
    by_cases hb : b ∈ chartBondsInBlocks ℓ.side B
    · have hb' := Finset.mem_filter.mp hb
      have : parentBlock ℓ.side b.1 ∈ B ∧ b ∈ StepCosts.chartBonds ℓ.side n := ⟨hb'.2, hb'.1⟩
      rw [if_pos hb]
      unfold deviationInGauge
      rw [if_pos this, imaginaryComponent_adjointAction, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold rotatedCoeff stepDeviation
      ring
    · have : ¬ (parentBlock ℓ.side b.1 ∈ B ∧ b ∈ StepCosts.chartBonds ℓ.side n) := fun h =>
        hb (Finset.mem_filter.mpr ⟨h.2, h.1⟩)
      rw [if_neg hb]
      unfold deviationInGauge
      rw [if_neg this, imaginaryComponent_zero, mul_zero]
  rw [Finset.sum_congr rfl fun b _ => h1 b, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sum_coe_sort]
  conv_rhs => rw [Fintype.sum_prod_type]
end Draws
section Reduction
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (β : ℝ) (t d N : ℕ) [NeZero N]
private def clampedMonomial {P : Type*} {r : ℕ} (φ : Fin r → P) (w : P → ℝ) : ℝ := ∏ i, clampUnit (w (φ i))
private theorem measurable_clampedMonomial {P : Type*} {r : ℕ} (φ : Fin r → P) : Measurable (clampedMonomial φ) := by
  unfold clampedMonomial
  exact Finset.measurable_prod _ fun i _ => continuous_clampUnit.measurable.comp (measurable_pi_apply _)
private theorem abs_clampedMonomial_le {P : Type*} {r : ℕ} (φ : Fin r → P) (w : P → ℝ) : |clampedMonomial φ w| ≤ 1 := by
  unfold clampedMonomial
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => abs_clampUnit_le _
private theorem condExp_product_reduction {r : ℕ} (o : TorusSite (fineSide ℓ.side d N)) (σ m δ : ℝ) (hσ : σ / 64 ≤ 1)
    (hδ : 0 ≤ δ) (B : Finset (TorusSite (fineSide ℓ.side d N)))
    (g : MarkedSample ℓ (t + 1 + d) N → TorusSite (fineSide ℓ.side d N) → UnitQuaternion)
    (hg : Measurable[upperSigma T (t + 1) d N] g)
    (l : Fin r → TorusBond (fineSide ℓ.side d N * ℓ.side) → ℝ) (e : Fin r → Fin 3) (hl : ∀ i, ∑ b, |l i b| ≤ 4)
    (ν : Measure (MarkedSample ℓ (t + 1) (fineSide ℓ.side d N)))
    [IsProbabilityMeasure (markedSampleLaw T β (t + 1 + d) N)]
    (hmap : (markedSampleLaw T β (t + 1 + d) N).map (sampleBelow ℓ (t + 1) d N) = ν)
    (h𝓢 : stageSigma T (t + 1) (fineSide ℓ.side d N) ≤ markedSampleMeasurableSpace ℓ (t + 1) (fineSide ℓ.side d N))
    (h𝓕 : upperSigma T (t + 1) d N ≤ markedSampleMeasurableSpace ℓ (t + 1 + d) N)
    (hmk : ∀ (G : MarkedSample ℓ (t + 1) (fineSide ℓ.side d N) → ℝ), Measurable G → (∀ v, |G v| ≤ 1) →
      (markedSampleLaw T β (t + 1 + d) N)[fun u => G (sampleBelow ℓ (t + 1) d N u) | upperSigma T (t + 1) d N]
        =ᵐ[markedSampleLaw T β (t + 1 + d) N]
        (markedSampleLaw T β (t + 1 + d) N)[fun u => G (sampleBelow ℓ (t + 1) d N u) |
          (stageSigma T (t + 1) (fineSide ℓ.side d N)).comap (sampleBelow ℓ (t + 1) d N)])
    (hcl : ∀ᵐ v ∂ν, Disjoint (stageState T (t + 1) _ v).2.1 (supBall o m) →
      IsColdOnBall σ (topField ℓ (t + 1) _ v) o m ∧ (StepAvoids T t m o v →
        ∀ b ∈ chartBondsInBlocks ℓ.side B,
          ‖(stepDeviation T t (topField ℓ (t + 1) _ v) (topField ℓ t _ v.1) b : Quaternion ℝ)‖ < σ / 64))
    (hb1 : ∀ (b : TorusBond (fineSide ℓ.side d N * ℓ.side)) (a : Fin 3), b ∈ chartBondsInBlocks ℓ.side B →
      Measurable (Set.indicator
        {q : TorusField (fineSide ℓ.side d N) × TorusField (fineSide ℓ.side d N * ℓ.side) | IsColdOnBall σ q.1 o m}
        fun q => imaginaryComponent a (stepDeviation T t q.1 q.2 b)))
    (hb2 : MeasurableSet (avoidSet T t o m))
    (Mf : ((↥(chartBondsInBlocks ℓ.side B) × Fin 3 → ℝ) → ℝ) → MarkedSample ℓ (t + 1) (fineSide ℓ.side d N) → ℝ)
    (hlaw : ∀ F : (↥(chartBondsInBlocks ℓ.side B) × Fin 3 → ℝ) → ℝ, Measurable F → (∀ v, |F v| ≤ 1) →
      ∀ᵐ v ∂ν, Disjoint (stageState T (t + 1) _ v).2.1 (supBall o m) →
        |(ν[Set.indicator (avoidSet T t o m) (fun u' => F (imaginaryComponentsOn (chartBondsInBlocks ℓ.side B)
            (stepDeviation T t (topField ℓ (t + 1) _ u') (topField ℓ t _ u'.1)))) |
          stageSigma T (t + 1) (fineSide ℓ.side d N)]) v - Mf F v| ≤ δ) :
    Integrable (Set.indicator (sampleBelow ℓ (t + 1) d N ⁻¹' avoidSet T t o m)
        (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T t (g u') B
          (topField ℓ (t + 1) _ (sampleBelow ℓ (t + 1) d N u')) (topField ℓ t _ (sampleBelow ℓ (t + 1) d N u').1) b)))
      (markedSampleLaw T β (t + 1 + d) N) ∧
    ∀ᵐ u ∂(markedSampleLaw T β (t + 1 + d) N),
      Disjoint (stageState T (t + 1) _ (sampleBelow ℓ (t + 1) d N u)).2.1 (supBall o m) →
      |((markedSampleLaw T β (t + 1 + d) N)[Set.indicator (sampleBelow ℓ (t + 1) d N ⁻¹' avoidSet T t o m)
          (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T t (g u') B
            (topField ℓ (t + 1) _ (sampleBelow ℓ (t + 1) d N u')) (topField ℓ t _ (sampleBelow ℓ (t + 1) d N u').1) b)) |
        upperSigma T (t + 1) d N]) u -
        ∑ φ : Fin r → ↥(chartBondsInBlocks ℓ.side B) × Fin 3,
          (∏ i, rotatedCoeff (g u) (l i) (e i) ((φ i).1.1, (φ i).2)) *
            Mf (clampedMonomial φ) (sampleBelow ℓ (t + 1) d N u)| ≤
        12 ^ r * δ := by
  subst hmap
  set μ := markedSampleLaw T β (t + 1 + d) N with hμ
  set π := sampleBelow ℓ (t + 1) d N with hπdef
  have hπ : Measurable π := measurable_sampleBelow _ _ _
  let Z := chartBondsInBlocks ℓ.side B
  let Cf : (Fin r → ↥Z × Fin 3) → MarkedSample ℓ (t + 1 + d) N → ℝ := fun φ u =>
    ∏ i, rotatedCoeff (g u) (l i) (e i) ((φ i).1.1, (φ i).2)
  let Gf : (Fin r → ↥Z × Fin 3) → MarkedSample ℓ (t + 1) (fineSide ℓ.side d N) → ℝ := fun φ =>
    Set.indicator (avoidSet T t o m) fun v => ∏ i, clampUnit (truncatedComponent T t o σ m v (φ i).1.1 (φ i).2)
  have hC : ∀ φ, Measurable[upperSigma T (t + 1) d N] (Cf φ) := fun φ => by
    refine Finset.measurable_prod _ fun i _ => ?_
    have h : Measurable[upperSigma T (t + 1) d N] fun u =>
        rotationEntry (g u (parentBlock ℓ.side (φ i).1.1.1)) (e i) (φ i).2 :=
      (continuous_rotationEntry _ _).measurable.comp ((measurable_pi_apply _).comp hg)
    exact h.const_mul _
  have hK : ∀ u, ∑ φ, |Cf φ u| ≤ 12 ^ r := fun u => by
    have := sum_abs_prod_le_pow (fun (i : Fin r) (p : ↥Z × Fin 3) => rotatedCoeff (g u) (l i) (e i) (p.1.1, p.2)) 12
      (by norm_num) (fun i => ?_)
    · simpa using this
    · calc ∑ p : ↥Z × Fin 3, |rotatedCoeff (g u) (l i) (e i) (p.1.1, p.2)|
          ≤ ∑ p : ↥Z × Fin 3, |l i p.1.1| := Finset.sum_le_sum fun p _ => by
            unfold rotatedCoeff
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (abs_rotationEntry_le _ _ _)
        _ = 3 * ∑ b : ↥Z, |l i b.1| := by
            rw [Fintype.sum_prod_type]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
            rw [Finset.mul_sum]
        _ ≤ 3 * ∑ b, |l i b| := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            rw [Finset.sum_coe_sort Z fun b => |l i b|]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
        _ ≤ 12 := by linarith [hl i]
  have hpair : Measurable fun v : MarkedSample ℓ (t + 1) (fineSide ℓ.side d N) =>
      (topField ℓ (t + 1) _ v, topField ℓ t (fineSide ℓ.side d N * ℓ.side) v.1) :=
    (measurable_topField _ _).prodMk ((measurable_topField _ _).comp measurable_fst)
  have hG : ∀ φ, Measurable (Gf φ) := fun φ =>
    (Finset.measurable_prod _ fun i _ => continuous_clampUnit.measurable.comp
      ((hb1 _ _ (φ i).1.2).comp hpair)).indicator hb2
  have hG1 : ∀ φ v, |Gf φ v| ≤ 1 := fun φ v => by
    by_cases hv : v ∈ avoidSet T t o m
    · simp only [Gf, Set.indicator_of_mem hv]
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => abs_clampUnit_le _
    · simp [Gf, Set.indicator_of_notMem hv]
  have hcut : ∀ᵐ v ∂(μ.map π), v ∈ avoidSet T t o m → ∀ (b : ↥Z) (a : Fin 3),
      truncatedComponent T t o σ m v b.1 a =
          imaginaryComponent a (stepDeviation T t (topField ℓ (t + 1) _ v) (topField ℓ t _ v.1) b.1) ∧
        clampUnit (imaginaryComponent a (stepDeviation T t (topField ℓ (t + 1) _ v) (topField ℓ t _ v.1) b.1)) =
          imaginaryComponent a (stepDeviation T t (topField ℓ (t + 1) _ v) (topField ℓ t _ v.1) b.1) := by
    filter_upwards [hcl] with v hv hA b a
    obtain ⟨hc, hs⟩ := hv hA.1
    exact ⟨truncatedComponent_of_cold T t o σ m v b.1 a hc,
      clampUnit_of_abs_le (((abs_imaginaryComponent_le _ _).trans (hs hA.2 b.1 b.2).le).trans hσ)⟩
  have hGe : ∀ φ, Gf φ =ᵐ[μ.map π] Set.indicator (avoidSet T t o m) (fun u' => clampedMonomial φ
      (imaginaryComponentsOn Z (stepDeviation T t (topField ℓ (t + 1) _ u') (topField ℓ t _ u'.1)))) := fun φ => by
    filter_upwards [hcut] with v hv
    by_cases hA : v ∈ avoidSet T t o m
    · simp only [Gf, Set.indicator_of_mem hA, clampedMonomial, imaginaryComponentsOn]
      exact Finset.prod_congr rfl fun i _ => by rw [(hv hA (φ i).1 (φ i).2).1]
    · simp only [Gf, Set.indicator_of_notMem hA]
  have hN : ∀ φ, ∀ᵐ v ∂(μ.map π), Disjoint (stageState T (t + 1) _ v).2.1 (supBall o m) →
      |((μ.map π)[Gf φ | stageSigma T (t + 1) (fineSide ℓ.side d N)]) v - Mf (clampedMonomial φ) v| ≤ δ := fun φ => by
    filter_upwards [hlaw (clampedMonomial φ) (measurable_clampedMonomial φ) (abs_clampedMonomial_le φ),
      condExp_congr_ae (m := stageSigma T (t + 1) (fineSide ℓ.side d N)) (hGe φ)]
      with v h1 h2 hd
    rw [h2]
    exact h1 hd
  have hraw : Set.indicator (π ⁻¹' avoidSet T t o m)
      (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T t (g u') B
        (topField ℓ (t + 1) _ (π u')) (topField ℓ t _ (π u').1) b)) =ᵐ[μ]
      fun u => ∑ φ, Cf φ u * Gf φ (π u) := by
    filter_upwards [ae_of_ae_map hπ.aemeasurable hcut] with u hu
    by_cases hA : π u ∈ avoidSet T t o m
    · rw [Set.indicator_of_mem (show u ∈ π ⁻¹' avoidSet T t o m from hA)]
      simp only [imaginaryComponent_deviation_sum]
      rw [prod_sum_eq_sum_prod]
      refine Finset.sum_congr rfl fun φ _ => ?_
      congr 1
      simp only [Gf, Set.indicator_of_mem hA]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(hu hA (φ i).1 (φ i).2).1, (hu hA (φ i).1 (φ i).2).2]
    · rw [Set.indicator_of_notMem (show u ∉ π ⁻¹' avoidSet T t o m from hA)]
      symm
      refine Finset.sum_eq_zero fun φ _ => ?_
      simp only [Gf, Set.indicator_of_notMem hA, mul_zero]
  obtain ⟨hI, hE⟩ := condExp_finite_sum_near h𝓕 hπ h𝓢 Cf hC (12 ^ r) hK Gf hG hG1
    (fun φ => hmk (Gf φ) (hG φ) (hG1 φ)) (fun φ v => Mf (clampedMonomial φ) v) δ hδ
    (fun v => Disjoint (stageState T (t + 1) _ v).2.1 (supBall o m)) hN
  refine ⟨hI.congr hraw.symm, ?_⟩
  filter_upwards [hE, condExp_congr_ae (m := upperSigma T (t + 1) d N) hraw] with u h1 h2 hd
  rw [h2]
  exact h1 hd
end Reduction
section Mirror
variable {F : BlockFrame}
private theorem cutoffMean_congr {ρ : ℝ} {p : ℝ → ℝ} {Ψ H H' : StepVariable (finiteCells F) → ℝ}
    (h : ∀ η, (∀ b, ‖η b‖ < ρ) → H η = H' η) : cutoffMean ρ p Ψ H = cutoffMean ρ p Ψ H' := by apply _root_.YangMills.SharedProofs.p130533 <;> assumption
private theorem cutoffMean_sum {ι : Type*} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ}
    (hw : Integrable fun η => cutoffWeight ρ p η * Real.exp (- Ψ η)) (c : ι → ℝ)
    (H : ι → StepVariable (finiteCells F) → ℝ)
    (hH : ∀ i, Measurable (H i)) (hb : ∀ i η, |H i η| ≤ 1) :
    ∑ i, c i * cutoffMean ρ p Ψ (H i) = cutoffMean ρ p Ψ fun η => ∑ i, c i * H i η := by
  have hi : ∀ i, Integrable fun η => H i η * (cutoffWeight ρ p η * Real.exp (- Ψ η)) := fun i =>
    hw.mono ((hH i).aestronglyMeasurable.mul hw.1) (Filter.Eventually.of_forall fun η => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb i η))
  have e : ∫ η, (∑ i, c i * H i η) * (cutoffWeight ρ p η * Real.exp (- Ψ η)) =
      ∑ i, c i * ∫ η, H i η * (cutoffWeight ρ p η * Real.exp (- Ψ η)) := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun i _ => (hi i).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  unfold cutoffMean
  rw [e, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]
private theorem imaginaryComponent_toImaginary (e : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryComponent e (toImaginary v) = v e := by
  fin_cases e <;> simp [imaginaryComponent, toImaginary]
private theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
variable {L t m n : ℕ} [NeZero n] [NeZero L]
private theorem linearFunctional_adjointStepVariable (o : TorusSite n)
    (Γ : (reflectedTorusFrame L t m n).Cell → UnitQuaternion)
    (η : StepVariable (finiteCells (reflectedTorusFrame L t m n))) (l : TorusBond (n * L) → ℝ) (e : Fin 3) :
    linearFunctional (reflectedFunctional L t m o l e) (adjointStepVariable Γ η) =
      ∑ c : TorusBond (n * L), l c * imaginaryComponent e
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (Γ (enclosingCell (reflectedBondPosition L t m o c).1)) (reflectedCoordinateAt L t m o η c)) := by
  unfold linearFunctional
  rw [Fintype.sum_prod_type]
  have h1 : ∀ bm : ↥(BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))),
      ∑ a : Fin 3, reflectedFunctional L t m o l e (bm, a) * adjointStepVariable Γ η (bm, a).1 (bm, a).2 =
        (∑ c : TorusBond (n * L), if reflectedBondPosition L t m o c = bm.1 then l c else 0) *
          imaginaryComponent e (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (Γ (enclosingCell bm.1.1)) (toImaginary (η bm))) := fun bm => by
    rw [Finset.sum_eq_single e]
    · simp only [reflectedFunctional, if_true]
      congr 1
    · intro a _ ha
      simp [reflectedFunctional, ha]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl fun bm _ => h1 bm]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : reflectedBondPosition L t m o c ∈ BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))
  · rw [Finset.sum_eq_single
      (⟨reflectedBondPosition L t m o c, h⟩ : ↥(BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))))]
    · simp only [if_true]
      congr 3
      unfold reflectedCoordinateAt stepCoordinates
      rw [dif_pos h]
    · intro b _ hb
      rw [if_neg fun e' => hb (Subtype.ext e'.symm), zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · have e0 : reflectedCoordinateAt L t m o η c = 0 := by
      unfold reflectedCoordinateAt stepCoordinates
      rw [dif_neg h]
    rw [e0, adjointAction_zero, imaginaryComponent_zero, mul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : ¬ reflectedBondPosition L t m o c = b.1 := fun e' => h (by rw [e']; exact b.2)
    rw [if_neg hne, zero_mul]
end Mirror
section MirrorSide
variable {ℓ : TorusLumps.StepParameters} {t m n : ℕ} [NeZero n]
private theorem linearFunctional_reflected_eq_sum (o : TorusSite n)
    (Γ : (reflectedTorusFrame ℓ.side t m n).Cell → UnitQuaternion)
    (g : TorusSite n → UnitQuaternion) (B : Finset (TorusSite n))
    (l : TorusBond (n * ℓ.side) → ℝ) (e : Fin 3) (hl : ∀ b : TorusBond (n * ℓ.side), parentBlock ℓ.side b.1 ∉ B → l b = 0)
    (h1 : ∀ c : TorusBond (n * ℓ.side), parentBlock ℓ.side c.1 ∈ B → c ∉ StepCosts.chartBonds ℓ.side n →
      reflectedBondPosition ℓ.side t m o c ∉ BlockAverages.chordBonds (finiteCells (reflectedTorusFrame ℓ.side t m n)))
    (h2 : ∀ c : TorusBond (n * ℓ.side), parentBlock ℓ.side c.1 ∈ B →
      Γ (enclosingCell (reflectedBondPosition ℓ.side t m o c).1) = g (parentBlock ℓ.side c.1))
    (η : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n))) :
    linearFunctional (reflectedFunctional ℓ.side t m o l e) (adjointStepVariable Γ η) =
      ∑ p : ↥(chartBondsInBlocks ℓ.side B) × Fin 3,
        rotatedCoeff g l e (p.1.1, p.2) * imaginaryComponent p.2 (reflectedCoordinateAt ℓ.side t m o η p.1.1) := by
  rw [linearFunctional_adjointStepVariable]
  have hz : ∀ c ∉ chartBondsInBlocks ℓ.side B, l c * imaginaryComponent e
      (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (Γ (enclosingCell (reflectedBondPosition ℓ.side t m o c).1))
        (reflectedCoordinateAt ℓ.side t m o η c)) = 0 := fun c hc => by
    by_cases hB : parentBlock ℓ.side c.1 ∈ B
    · have hch : c ∉ StepCosts.chartBonds ℓ.side n := fun h => hc (Finset.mem_filter.mpr ⟨h, hB⟩)
      have e0 : reflectedCoordinateAt ℓ.side t m o η c = 0 := by
        unfold reflectedCoordinateAt stepCoordinates
        rw [dif_neg (h1 c hB hch)]
      rw [e0, adjointAction_zero, imaginaryComponent_zero, mul_zero]
    · rw [hl c hB, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ _) fun c _ hc => hz c hc, ← Finset.sum_coe_sort]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h2 c.1 (Finset.mem_filter.mp c.2).2, imaginaryComponent_adjointAction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold rotatedCoeff
  ring
private theorem measurable_reflectedComponent (o : TorusSite n) (b : TorusBond (n * ℓ.side)) (a : Fin 3) :
    Measurable fun η : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n)) =>
      imaginaryComponent a (reflectedCoordinateAt ℓ.side t m o η b) := by
  unfold reflectedCoordinateAt stepCoordinates
  by_cases h : reflectedBondPosition ℓ.side t m o b ∈
      BlockAverages.chordBonds (finiteCells (reflectedTorusFrame ℓ.side t m n))
  · simp only [Prod.mk.eta, dif_pos h, imaginaryComponent_toImaginary]
    exact (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous.measurable.comp (measurable_pi_apply _)
  · simp only [Prod.mk.eta, dif_neg h, imaginaryComponent_zero]
    exact measurable_const
private theorem abs_reflectedComponent_le (o : TorusSite n) (b : TorusBond (n * ℓ.side)) (a : Fin 3) {ρ : ℝ}
    (hρ : ρ ≤ 1) (hρ0 : 0 ≤ ρ)
    (η : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n))) (hη : ∀ b, ‖η b‖ < ρ) :
    |imaginaryComponent a (reflectedCoordinateAt ℓ.side t m o η b)| ≤ 1 := by
  unfold reflectedCoordinateAt stepCoordinates
  by_cases h : reflectedBondPosition ℓ.side t m o b ∈
      BlockAverages.chordBonds (finiteCells (reflectedTorusFrame ℓ.side t m n))
  · simp only [Prod.mk.eta, dif_pos h, imaginaryComponent_toImaginary]
    exact (PiLp.norm_apply_le _ _).trans ((hη _).le.trans hρ)
  · simp only [Prod.mk.eta, dif_neg h, imaginaryComponent_zero, abs_zero]
    norm_num
private theorem sum_cutoffMean_monomials {r : ℕ} (o : TorusSite n)
    (Γ : (reflectedTorusFrame ℓ.side t m n).Cell → UnitQuaternion)
    (g : TorusSite n → UnitQuaternion) (B : Finset (TorusSite n))
    (l : Fin r → TorusBond (n * ℓ.side) → ℝ) (e : Fin r → Fin 3)
    (hl : ∀ i (b : TorusBond (n * ℓ.side)), parentBlock ℓ.side b.1 ∉ B → l i b = 0)
    (h1 : ∀ c : TorusBond (n * ℓ.side), parentBlock ℓ.side c.1 ∈ B → c ∉ StepCosts.chartBonds ℓ.side n →
      reflectedBondPosition ℓ.side t m o c ∉ BlockAverages.chordBonds (finiteCells (reflectedTorusFrame ℓ.side t m n)))
    (h2 : ∀ c : TorusBond (n * ℓ.side), parentBlock ℓ.side c.1 ∈ B →
      Γ (enclosingCell (reflectedBondPosition ℓ.side t m o c).1) = g (parentBlock ℓ.side c.1))
    {ρ : ℝ} (hρ : ρ ≤ 1) (hρ0 : 0 ≤ ρ) (p : ℝ → ℝ)
    (Ψ Ψ' : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n)) → ℝ)
    (hw : Integrable fun η => cutoffWeight ρ p η * Real.exp (- Ψ η))
    (hcarry : ∀ H : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n)) → ℝ,
      cutoffMean ρ p Ψ' H = cutoffMean ρ p Ψ fun η => H (adjointStepVariable Γ η)) :
    ∑ φ : Fin r → ↥(chartBondsInBlocks ℓ.side B) × Fin 3, (∏ i, rotatedCoeff g (l i) (e i) ((φ i).1.1, (φ i).2)) *
        cutoffMean ρ p Ψ (fun η => clampedMonomial φ
          (imaginaryComponentsOn (chartBondsInBlocks ℓ.side B) (reflectedCoordinateAt ℓ.side t m o η))) =
      cutoffMean ρ p Ψ' fun η => ∏ i, linearFunctional (reflectedFunctional ℓ.side t m o (l i) (e i)) η := by
  have hm : ∀ φ : Fin r → ↥(chartBondsInBlocks ℓ.side B) × Fin 3,
      Measurable fun η : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n)) =>
        clampedMonomial φ (imaginaryComponentsOn (chartBondsInBlocks ℓ.side B) (reflectedCoordinateAt ℓ.side t m o η)) :=
      fun φ => by
    have h : Measurable fun η : StepVariable (finiteCells (reflectedTorusFrame ℓ.side t m n)) =>
        fun q : ↥(chartBondsInBlocks ℓ.side B) × Fin 3 =>
          imaginaryComponent q.2 (reflectedCoordinateAt ℓ.side t m o η q.1.1) :=
      measurable_pi_lambda _ fun q => measurable_reflectedComponent o q.1.1 q.2
    exact (measurable_clampedMonomial φ).comp h
  have hs := cutoffMean_sum hw (fun φ : Fin r → ↥(chartBondsInBlocks ℓ.side B) × Fin 3 =>
      ∏ i, rotatedCoeff g (l i) (e i) ((φ i).1.1, (φ i).2))
    (fun φ η => clampedMonomial φ
      (imaginaryComponentsOn (chartBondsInBlocks ℓ.side B) (reflectedCoordinateAt ℓ.side t m o η))) hm
    (fun φ η => abs_clampedMonomial_le φ _)
  rw [hs, hcarry]
  refine cutoffMean_congr fun η hη => ?_
  symm
  simp only [linearFunctional_reflected_eq_sum o Γ g B _ _ (hl _) h1 h2 η]
  rw [prod_sum_eq_sum_prod]
  refine Finset.sum_congr rfl fun φ _ => ?_
  congr 1
  unfold clampedMonomial imaginaryComponentsOn
  exact Finset.prod_congr rfl fun i _ => (clampUnit_of_abs_le (abs_reflectedComponent_le o _ _ hρ hρ0 η hη)).symm
end MirrorSide
section Places
open TopLevelSites
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem siteCoords_siteOfCoords {F : BlockFrame} {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords j a : F.Site j) i = a i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
private theorem isAxialTreeBond_reflectedBondPosition_iff (hL : Odd L) {t m : ℕ} (hm : 0 < m) (h2 : 2 ≤ n)
    (o : TorusSite n) (b : TorusBond (n * L)) :
    IsAxialTreeBond (F := reflectedTorusFrame L t m n) (reflectedBondPosition L t m o b) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) := by
  classical
  have hLp : 0 < L := hL.pos
  have h2' : 2 ≤ 4 * m := by omega
  have : NeZero (4 * m) := ⟨by omega⟩
  have : NeZero (4 * m * (reflectedTorusFrame L t m n).blockSide) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne L)⟩
  have : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set Xf : Fin 4 → ℤ := fun i =>
    (b.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs with hXf
  have hp : reflectedBondPosition L t m o b = (torusSiteInFrame (reflectedTorusFrame L t m n)
      (reflectedTorusFrame L t m n).depth
      (siteOfInt Xf : TorusSite (4 * m * (reflectedTorusFrame L t m n).blockSide)), b.2) := by
    rw [torusSiteInFrame_siteOfInt (period_depth_of_extent fun _ => rfl)]
    rfl
  rw [hp]
  refine Iff.trans (isAxialTreeBond_torusSiteInFrame_iff (F := reflectedTorusFrame L t m n) (n := 4 * m)
      (fun _ => rfl) hL h2' _ _)
    (Iff.trans ?_ (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n)
      (fun _ => rfl) hL h2 b.1 b.2).symm)
  have key : (fun l => offsetFromCentre L ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ))) =
      fun l => offsetFromCentre L (((b.1 l).cast : ℤ)) := by
    funext l
    have h1 : (L : ℤ) ∣ ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) - Xf l := by
      have : ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) = Xf l % ((4 * m * L : ℕ) : ℤ) :=
        ZMod.coe_intCast (Xf l)
      rw [this]
      have e := Int.emod_add_mul_ediv (Xf l) ((4 * m * L : ℕ) : ℤ)
      refine ⟨-(4 * m * (Xf l / ((4 * m * L : ℕ) : ℤ))), ?_⟩
      push_cast at e ⊢
      linarith
    have h2 : (L : ℤ) ∣ Xf l - ((b.1 l).cast : ℤ) := by
      have e1 : ((Xf l : ℤ) : ZMod (n * L)) =
          b.1 l - ((((L : ℤ) * ((o l).cast : ℤ) : ℤ)) : ZMod (n * L)) := by
        simp only [hXf]
        rw [ZMod.coe_valMinAbs]
        rfl
      have e2 : ((((b.1 l).cast : ℤ) - (L : ℤ) * ((o l).cast : ℤ) : ℤ) : ZMod (n * L)) =
          ((Xf l : ℤ) : ZMod (n * L)) := by
        rw [e1]
        push_cast
        simp
      have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e2
      obtain ⟨w, hw⟩ := h3
      refine ⟨(n : ℤ) * w + -((o l).cast : ℤ), ?_⟩
      push_cast at hw
      linarith
    have h3 : (L : ℤ) ∣ ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) - ((b.1 l).cast : ℤ) := by
      have := dvd_add h1 h2
      simpa using this
    have e := offsetFromCentre_add_dvd hLp hL (((b.1 l).cast : ℤ)) _ h3
    rw [add_sub_cancel] at e
    exact e
  change IsTreeOffset L ((fun l => offsetFromCentre L ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ))), b.2) ↔
    IsTreeOffset L ((fun l => offsetFromCentre L (((b.1 l).cast : ℤ))), b.2)
  rw [key]
private theorem reflectedBondPosition_not_mem (hL : Odd L) {t m : ℕ} (hm : 0 < m) (h2 : 2 ≤ n) (o : TorusSite n)
    (c : TorusBond (n * L)) (hc : c ∉ StepCosts.chartBonds L n) :
    reflectedBondPosition L t m o c ∉ BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n)) := fun h => by
  have ht : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 c.1, c.2) := by
    by_contra hn
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  exact (Finset.mem_filter.mp h).2 ((isAxialTreeBond_reflectedBondPosition_iff hL hm h2 o c).mpr ht)
private theorem valMinAbs_reflected_coord (hL : Odd L) (o : TorusSite n) (c : TorusBond (n * L)) (i : Fin 4) (a : ℤ)
    (ha : (parentBlock L c.1 i - o i).valMinAbs = a) (hb : 2 * |a| + 1 < (n : ℤ)) :
    ∃ s : ℤ, (c.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs = (L : ℤ) * a + s ∧
      0 ≤ s + ((L : ℤ) - 1) / 2 ∧ s + ((L : ℤ) - 1) / 2 < L := by
  have hLp : 0 < L := hL.pos
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLp
  have : NeZero (n * L) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨k, hk⟩ := hL
  have hh : ((L : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  set C : ℤ := ((c.1 i).cast : ℤ) with hC
  set q : ℤ := (C + ((L : ℤ) - 1) / 2) / (L : ℤ) with hq
  set rr : ℤ := (C + ((L : ℤ) - 1) / 2) % (L : ℤ) with hr
  have e1 : (L : ℤ) * q + rr = C + ((L : ℤ) - 1) / 2 := by
    rw [hq, hr, add_comm]
    exact Int.emod_add_mul_ediv _ _
  have e2 : 0 ≤ rr := Int.emod_nonneg _ hLz.ne'
  have e3 : rr < L := Int.emod_lt_of_pos _ hLz
  have hblock : parentBlock L c.1 i = ((q : ℤ) : ZMod n) := rfl
  have hcast : ((a : ℤ) : ZMod n) = ((q : ℤ) : ZMod n) - (((o i).cast : ℤ) : ZMod n) := by
    rw [← ha, ZMod.coe_valMinAbs, hblock]
    simp
  obtain ⟨w, hw⟩ : (n : ℤ) ∣ (q - ((o i).cast : ℤ)) - a := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
    push_cast
    rw [hcast]
    simp
  refine ⟨rr - ((L : ℤ) - 1) / 2, ?_, by omega, by omega⟩
  rw [ZMod.valMinAbs_spec]
  constructor
  · have hCc : ((C : ℤ) : ZMod (n * L)) = c.1 i := ZMod.intCast_zmod_cast (c.1 i)
    rw [← hCc]
    simp only [siteOfInt]
    rw [← Int.cast_sub]
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨-w, ?_⟩
    push_cast
    have : C = (L : ℤ) * q + rr - ((L : ℤ) - 1) / 2 := by linarith
    rw [this]
    linear_combination (-(L : ℤ)) * hw
  · have h1 := neg_abs_le a
    have h2 := le_abs_self a
    have h5 : (2 * |a| + 2) * (L : ℤ) ≤ (n : ℤ) * L := mul_le_mul_of_nonneg_right (by omega) hLz.le
    have h6 : (L : ℤ) * a ≤ (L : ℤ) * |a| := mul_le_mul_of_nonneg_left h2 hLz.le
    have h7 : (L : ℤ) * (-|a|) ≤ (L : ℤ) * a := mul_le_mul_of_nonneg_left h1 hLz.le
    rw [hh] at *
    have hLk : (L : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
    simp only [Set.mem_Ioc]
    push_cast
    constructor <;> nlinarith
private theorem enclosingCell_reflectedBondPosition (hL : Odd L) {t m : ℕ} (hm : 0 < m) (o : TorusSite n)
    (c : TorusBond (n * L)) (a : Fin 4 → ℤ)
    (ha : ∀ i, (parentBlock L c.1 i - o i).valMinAbs = a i) (hb : ∀ i, 2 * |a i| + 1 < (n : ℤ)) :
    enclosingCell (reflectedBondPosition L t m o c).1 = siteOfCoords (reflectedTorusFrame L t m n).top a := by
  have : NeZero (4 * m) := ⟨by omega⟩
  have hLp : 0 < L := hL.pos
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLp
  funext i
  obtain ⟨s, hs, hs0, hs1⟩ := valMinAbs_reflected_coord hL o c i (a i) (ha i) (hb i)
  have hper : ((reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).depth i : ℤ) = 4 * (m : ℤ) * L := by
    have : (reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).depth i = 4 * m * L :=
      period_depth_of_extent (F := reflectedTorusFrame L t m n) (n := 4 * m) (fun _ => rfl) i
    rw [this]
    push_cast
    ring
  have hper' : ((reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).top i) = 4 * m :=
    period_top_of_extent (F := reflectedTorusFrame L t m n) (n := 4 * m) (fun _ => rfl) i
  have hc : siteCoords (reflectedBondPosition L t m o c).1 i = ((L : ℤ) * a i + s) % (4 * (m : ℤ) * L) := by
    have := siteCoords_siteOfCoords (F := reflectedTorusFrame L t m n) (j := (reflectedTorusFrame L t m n).depth)
      (fun i => (c.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs) i
    rw [hs, hper] at this
    exact this
  simp only [enclosingCell, siteOfCoords]
  have hsub : (reflectedTorusFrame L t m n).top - (reflectedTorusFrame L t m n).depth = 1 := _root_.YangMills.Construction.TopLevelSites.top_sub_depth
  have hLL : (((reflectedTorusFrame L t m n).blockSide : ℕ) : ℤ) = (L : ℤ) := rfl
  rw [hsub, hLL, pow_one, hc]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
  rw [hper']
  set P : ℤ := 4 * (m : ℤ) * L with hP
  set X : ℤ := (L : ℤ) * a i + s with hX
  have e := Int.emod_add_mul_ediv X P
  have hq : (X % P + ((L : ℤ) - 1) / 2) / (L : ℤ) = a i - 4 * (m : ℤ) * (X / P) := by
    have e' : X % P + ((L : ℤ) - 1) / 2 = (s + ((L : ℤ) - 1) / 2) + (L : ℤ) * (a i - 4 * (m : ℤ) * (X / P)) := by
      have : X % P = X - P * (X / P) := by linarith
      rw [this, hX, hP]
      ring
    rw [e', Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt hs0 hs1, zero_add]
  rw [hq]
  refine ⟨X / P, ?_⟩
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p38944 := @enclosingCell_reflectedBondPosition
private theorem reflectedGauge_siteOfCoords {t m : ℕ} (hm : 0 < m) (o : TorusSite n) (γ : TorusSite n → UnitQuaternion)
    (y : TorusSite n) (a : Fin 4 → ℤ)
    (ha : ∀ i, (y i - o i).valMinAbs = a i) (hb : ∀ i, |a i| ≤ m) :
    reflectedGauge m (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top o) (fun x => γ (toTorusSite n x))
      (siteOfCoords (reflectedTorusFrame L t m n).top a) = γ y := by
  have : NeZero (4 * m) := ⟨by omega⟩
  unfold reflectedGauge
  have hv : (fun l => ColdStepAtMirrorFrames.reflectCoord m
      ((siteOfCoords (reflectedTorusFrame L t m n).top a : (reflectedTorusFrame L t m n).Cell) l).valMinAbs) = a := by
    funext l
    have hper' : ((reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).top l) = 4 * m :=
      period_top_of_extent (F := reflectedTorusFrame L t m n) (n := 4 * m) (fun _ => rfl) l
    have h1 : ((siteOfCoords (reflectedTorusFrame L t m n).top a : (reflectedTorusFrame L t m n).Cell) l).valMinAbs =
        a l := by
      have : ∀ (p : ℕ) (_ : p = 4 * m), (((a l : ℤ) : ZMod p)).valMinAbs = a l := by
        intro p hp
        subst hp
        rw [ZMod.valMinAbs_spec]
        refine ⟨rfl, ?_⟩
        have := abs_le.mp (hb l)
        simp only [Set.mem_Ioc]
        push_cast
        constructor <;> omega
      exact this _ hper'
    rw [h1]
    unfold ColdStepAtMirrorFrames.reflectCoord
    rw [if_pos (hb l)]
  rw [hv]
  have hpt : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n :=
    period_top_of_extent (F := torusFrame L t n) (n := n) fun _ => rfl
  show γ (toTorusSite n (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top o +
    siteOfCoords (torusFrame L t n).top a)) = γ y
  rw [toTorusSite_add hpt, toTorusSite_torusSiteInFrame hpt, toTorusSite_siteOfCoords hpt]
  congr 1
  funext i
  simp only [Pi.add_apply, siteOfInt]
  rw [← ha i, ZMod.coe_valMinAbs]
  ring
abbrev _root_.YangMills.SharedProofs.p35238 := @reflectedGauge_siteOfCoords
private theorem reflectedTopField_gaugeTransform (hMir : ReflectedFieldOfGaugedTop) {t m : ℕ} (hm : 0 < m)
    (o : TorusSite n) (γ : TorusSite n → UnitQuaternion) (V : TorusField n) :
    reflectedTopField L t m o (TorusFields.gaugeTransform γ V) =
      BlockAverages.gaugeTransform
        (reflectedGauge m (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top o) (fun x => γ (toTorusSite n x)))
        (reflectedTopField L t m o V) := by
  have hpt : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n :=
    period_top_of_extent (F := torusFrame L t n) (n := n) fun _ => rfl
  have e : readAtLevel (torusFrame L t n) (torusFrame L t n).top (TorusFields.gaugeTransform γ V) =
      BlockAverages.gaugeTransform (fun x => γ (toTorusSite n x))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
    funext x i
    have e1 : toTorusSite n (x + BlockAverages.unitStep (torusFrame L t n).top i) =
        toTorusSite n x + TorusFields.unitStep n i := by
      rw [toTorusSite_add hpt, toTorusSite_unitStep hpt]
    show TorusFields.gaugeTransform γ V (toTorusSite n x) i = _
    simp only [TorusFields.gaugeTransform, BlockAverages.gaugeTransform, e1]
    rfl
  unfold reflectedTopField
  rw [e]
  exact hMir _ _ _ _ _ hm
abbrev _root_.YangMills.SharedProofs.p89812 := @reflectedTopField_gaugeTransform
end Places
section Pairings
private theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f f' F : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : ∀ b ∈ s, 0 ≤ F b)
    (h1 : ∀ b ∈ s, |f b| ≤ F b) (h2 : ∀ b ∈ s, |f' b| ≤ F b) (h3 : ∀ b ∈ s, |f b - f' b| ≤ F b * ε) :
    |∏ b ∈ s, f b - ∏ b ∈ s, f' b| ≤ (s.card : ℝ) * (∏ b ∈ s, F b) * ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hF' : ∀ b ∈ s, 0 ≤ F b := fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have ihs := ih hF' (fun b hb => h1 b (Finset.mem_insert_of_mem hb)) (fun b hb => h2 b (Finset.mem_insert_of_mem hb))
      (fun b hb => h3 b (Finset.mem_insert_of_mem hb))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hFa := hF a (Finset.mem_insert_self a s)
    have hb1 : |∏ b ∈ s, f b| ≤ ∏ b ∈ s, F b := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun b hb => h1 b (Finset.mem_insert_of_mem hb)
    have e : f a * ∏ b ∈ s, f b - f' a * ∏ b ∈ s, f' b =
        (f a - f' a) * ∏ b ∈ s, f b + f' a * (∏ b ∈ s, f b - ∏ b ∈ s, f' b) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |f a - f' a| * |∏ b ∈ s, f b| ≤ (F a * ε) * ∏ b ∈ s, F b :=
      mul_le_mul (h3 a (Finset.mem_insert_self a s)) hb1 (abs_nonneg _) (mul_nonneg hFa hε)
    have t2 : |f' a| * |∏ b ∈ s, f b - ∏ b ∈ s, f' b| ≤ F a * ((s.card : ℝ) * (∏ b ∈ s, F b) * ε) :=
      mul_le_mul (h2 a (Finset.mem_insert_self a s)) ihs (abs_nonneg _) hFa
    push_cast
    nlinarith [t1, t2]
private theorem prod_pairs_eq_prod {r : ℕ} (π : Finpartition (Finset.univ : Finset (Fin r)))
    (h : ∀ B ∈ π.parts, B.card = 2) (a : Fin r → ℝ) :
    ∏ B ∈ π.parts, (if h : B.Nonempty then a (B.min' h) * a (B.max' h) else 1) = ∏ i, a i := by
  classical
  have e := Finset.prod_biUnion (s := π.parts) (t := id) (f := a) π.disjoint
  rw [π.biUnion_parts] at e
  rw [e]
  refine Finset.prod_congr rfl fun B hB => ?_
  have hc := h B hB
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  rw [dif_pos hne]
  have hlt : B.min' hne < B.max' hne := Finset.min'_lt_max'_of_card B (by omega)
  have hB2 : B = {B.min' hne, B.max' hne} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.min'_mem _ _
      · exact Finset.max'_mem _ _
    · rw [Finset.card_pair hlt.ne, hc]
  show _ = ∏ i ∈ B, a i
  conv_rhs => rw [hB2]
  rw [Finset.prod_pair hlt.ne]
private theorem abs_wickPairingSum_sub_le {r : ℕ} (G G' : Fin r → Fin r → ℝ) (a : Fin r → ℝ) (K ε : ℝ) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (ha : ∀ i, 0 ≤ a i) (h1 : ∀ i i', |G i i'| ≤ K * a i * a i')
    (h2 : ∀ i i', |G' i i'| ≤ K * a i * a i')
    (h3 : ∀ i i', |G i i' - G' i i'| ≤ K * a i * a i' * ε) :
    |wickPairingSum G - wickPairingSum G'| ≤
      (Fintype.card (Finpartition (Finset.univ : Finset (Fin r))) : ℝ) * ((r : ℝ) * K ^ r) * (∏ i, a i) * ε := by
  classical
  unfold wickPairingSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hP : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ => ha i
  have each : ∀ π : Finpartition (Finset.univ : Finset (Fin r)),
      |(if ∀ B ∈ π.parts, B.card = 2 then
          ∏ B ∈ π.parts, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1) else 0) -
        (if ∀ B ∈ π.parts, B.card = 2 then
          ∏ B ∈ π.parts, (if h : B.Nonempty then G' (B.min' h) (B.max' h) else 1) else 0)| ≤
      ((r : ℝ) * K ^ r) * (∏ i, a i) * ε := fun π => by
    by_cases hp : ∀ B ∈ π.parts, B.card = 2
    · rw [if_pos hp, if_pos hp]
      have hne : ∀ B ∈ π.parts, B.Nonempty := fun B hB => Finset.card_pos.mp (by rw [hp B hB]; norm_num)
      have hF : ∀ B ∈ π.parts, 0 ≤ K * (if h : B.Nonempty then a (B.min' h) * a (B.max' h) else 1) := fun B hB => by
        rw [dif_pos (hne B hB)]
        have := ha (B.min' (hne B hB))
        have := ha (B.max' (hne B hB))
        positivity
      have key := abs_prod_sub_prod_le π.parts (fun B => if h : B.Nonempty then G (B.min' h) (B.max' h) else 1)
        (fun B => if h : B.Nonempty then G' (B.min' h) (B.max' h) else 1)
        (fun B => K * (if h : B.Nonempty then a (B.min' h) * a (B.max' h) else 1)) ε hε hF
        (fun B hB => by
          simp only [dif_pos (hne B hB)]
          have := h1 (B.min' (hne B hB)) (B.max' (hne B hB))
          linarith)
        (fun B hB => by
          simp only [dif_pos (hne B hB)]
          have := h2 (B.min' (hne B hB)) (B.max' (hne B hB))
          linarith)
        (fun B hB => by
          simp only [dif_pos (hne B hB)]
          have := h3 (B.min' (hne B hB)) (B.max' (hne B hB))
          linarith)
      refine key.trans ?_
      rw [Finset.prod_mul_distrib, prod_pairs_eq_prod π hp a, Finset.prod_const]
      have hcard : π.parts.card ≤ r := by
        have := π.card_parts_le_card
        simpa using this
      have hKp : K ^ π.parts.card ≤ K ^ r := pow_le_pow_right₀ hK hcard
      have hc : (π.parts.card : ℝ) ≤ r := by exact_mod_cast hcard
      have hKp0 : 0 ≤ K ^ π.parts.card := by positivity
      calc (π.parts.card : ℝ) * (K ^ π.parts.card * ∏ i, a i) * ε
          = ((π.parts.card : ℝ) * K ^ π.parts.card) * (∏ i, a i) * ε := by ring
        _ ≤ ((r : ℝ) * K ^ r) * (∏ i, a i) * ε := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP) hε
            exact mul_le_mul hc hKp hKp0 (by positivity)
    · rw [if_neg hp, if_neg hp, sub_zero, abs_zero]
      have : 0 ≤ K ^ r := by positivity
      positivity
  calc _ ≤ ∑ _π : Finpartition (Finset.univ : Finset (Fin r)), ((r : ℝ) * K ^ r) * (∏ i, a i) * ε :=
        Finset.sum_le_sum fun π _ => each π
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end Pairings
section Integrable
open TopLevelSites
variable {F : BlockFrame}
private theorem integrable_cutoffWeight_mul_exp (hs : ∀ i, 0 < F.extent i) {a ρA ρ lam x M : ℝ} {m : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hR : IsRegularStep a ρA ρ lam x M m p f V) :
    Integrable fun η : StepVariable (finiteCells F) =>
      cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η) := by
  let Θ : StepVariable (finiteCells F) → ℝ := fun η =>
    (∑ Y ∈ finiteCells F, cellExponent false a ρA x m Y V η) - ∑ Y ∈ finiteCells F, cellCentredExpansion false a ρA m f Y η V
  have hball : MeasurableSet (openBallProduct F ρ) := by
    have : openBallProduct F ρ = ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < ρ} := by
      ext η
      simp [openBallProduct]
    rw [this]
    exact MeasurableSet.iInter fun b => measurableSet_lt (measurable_norm.comp (measurable_pi_apply b)) measurable_const
  have hΘc : ContinuousOn Θ (openBallProduct F ρ) :=
    (continuousOn_finset_sum _ fun Y _ => hR.continuousOn_cellExponent Y).sub
      (continuousOn_finset_sum _ fun Y _ => hR.continuousOn_cellCentredExpansion Y)
  have hΘb : ∀ η ∈ openBallProduct F ρ, |Θ η| ≤ 2 * ((finiteCells F).card * M) := fun η hη => by
    have h1 : |∑ Y ∈ finiteCells F, cellExponent false a ρA x m Y V η| ≤ (finiteCells F).card * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (finiteCells F) (fun Y => |cellExponent false a ρA x m Y V η|) M
        (fun Y _ => hR.abs_cellExponent_le Y η hη)
      simpa using this
    have h2 : |∑ Y ∈ finiteCells F, cellCentredExpansion false a ρA m f Y η V| ≤ (finiteCells F).card * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (finiteCells F) (fun Y => |cellCentredExpansion false a ρA m f Y η V|) M
        (fun Y _ => hR.abs_cellCentredExpansion_le Y η hη)
      simpa using this
    have := abs_sub (∑ Y ∈ finiteCells F, cellExponent false a ρA x m Y V η)
      (∑ Y ∈ finiteCells F, cellCentredExpansion false a ρA m f Y η V)
    simp only [Θ]
    linarith
  have hrows : ∀ η, ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V =
      ∑ Y ∈ finiteCells F, cellCentredExpansion false a ρA m f Y η V := fun η => by
    unfold cellCentredExpansion
    exact (Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.TopLevelSites.mem_finiteCells hs (enclosingCell y)) _).symm
  have hexp : ∀ η ∈ openBallProduct F ρ, stepExponent false a ρA x m f 1 V η = Θ η := fun η hη => by
    have h0 := hR.stepExponent_eq_sum η hη
    have h1 : stepExponent false a ρA x m f 1 V η = stepExponent false a ρA x m f 0 V η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
      unfold stepExponent
      ring
    rw [h1, h0, hrows]
  let e : StepVariable (finiteCells F) → ℝ :=
    (openBallProduct F ρ).piecewise (fun η => Real.exp (- Θ η)) (fun _ => 0)
  have hem : Measurable e := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hball
    exact Real.continuous_exp.comp_continuousOn hΘc.neg
  have heb : ∀ η, |e η| ≤ Real.exp (2 * ((finiteCells F).card * M)) := fun η => by
    by_cases hη : η ∈ openBallProduct F ρ
    · simp only [e, Set.piecewise_eq_of_mem _ _ _ hη, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((neg_le_abs _).trans (hΘb η hη))
    · simp only [e, Set.piecewise_eq_of_notMem _ _ _ hη, abs_zero]
      exact (Real.exp_pos _).le
  have heq : (fun η : StepVariable (finiteCells F) =>
      cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η)) = fun η => cutoffWeight ρ p η * e η := by
    funext η
    by_cases hη : η ∈ openBallProduct F ρ
    · simp only [e, Set.piecewise_eq_of_mem _ _ _ hη, hexp η hη]
    · simp only [hR.cutoffWeight_eq_zero_of_not_mem η hη, zero_mul]
  rw [heq]
  refine (hR.integrable_cutoffWeight.const_mul (Real.exp (2 * ((finiteCells F).card * M)))).mono'
    (hR.measurable_cutoffWeight.mul hem).aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hR.cutoffWeight_nonneg η), mul_comm]
  exact mul_le_mul_of_nonneg_right (heb η) (hR.cutoffWeight_nonneg η)
end Integrable
section Large
private theorem eventually_large_coupling (Q : ℝ) : ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → 1 ≤ x ∧
    Q + 64 * (20 * x ^ ((1 : ℝ) / 90) + 4 * Real.log x ^ 3) ≤ x ^ ((1 : ℝ) / 20) ∧
    Q + 1 ≤ Real.log x ^ 3 ∧ Q * Real.log x ^ 2 ≤ x := by
  have h20 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 20)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlog : Filter.Tendsto Real.log Filter.atTop Filter.atTop := Real.tendsto_log_atTop
  have h1 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 20)).bound
    (by norm_num : (0 : ℝ) < 1 / 2000)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).bound
    (show (0 : ℝ) < 1 / (|Q| + 1) by positivity)
  have h3 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 20 - 1 / 90)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have e4 := h20.eventually_ge_atTop (4 * |Q| + 4)
  have e5 := h3.eventually_ge_atTop (64 * 20 * 4)
  have e6 := (hlog.eventually_ge_atTop 1)
  have e7 : ∀ᶠ x : ℝ in Filter.atTop, Q + 1 ≤ Real.log x ^ 3 := by
    have := (hlog.eventually_ge_atTop (|Q| + 1))
    filter_upwards [this] with x hx
    have h0 : 1 ≤ Real.log x := by linarith [abs_nonneg Q]
    have hq := le_abs_self Q
    have : Real.log x ≤ Real.log x ^ 3 := by nlinarith [sq_nonneg (Real.log x), mul_self_nonneg (Real.log x - 1)]
    linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (h1.and (h2.and (e4.and (e5.and (e6.and (e7.and (Filter.eventually_ge_atTop 1)))))))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨a1, a2, a4, a5, a6, a7, a8⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have p20 : 0 < x ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hx0 _
  have p90 : 0 < x ^ ((1 : ℝ) / 90) := Real.rpow_pos_of_pos hx0 _
  have c3 : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have c2 : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [c3, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos p20] at a1
  rw [c2, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one, abs_of_pos hx0] at a2
  have hsplit : x ^ ((1 : ℝ) / 20) = x ^ ((1 : ℝ) / 20 - 1 / 90) * x ^ ((1 : ℝ) / 90) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have h90 : 64 * 20 * 4 * x ^ ((1 : ℝ) / 90) ≤ x ^ ((1 : ℝ) / 20) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right a5 p90.le
  refine ⟨a8, ?_, a7, ?_⟩
  · have hq := le_abs_self Q
    nlinarith [abs_nonneg Q]
  · have hq := le_abs_self Q
    have hq0 : 0 < |Q| + 1 := by positivity
    have : (|Q| + 1) * Real.log x ^ 2 ≤ x := by
      have := mul_le_mul_of_nonneg_left a2 hq0.le
      rw [← mul_assoc, mul_one_div_cancel hq0.ne', one_mul] at this
      exact this
    nlinarith [sq_nonneg (Real.log x), abs_nonneg Q]
end Large
section TopSide
variable {n : ℕ} [NeZero n]
private theorem sum_abs_reflectedFunctional_le {L t m : ℕ} [NeZero L] (o : TorusSite n) (l : TorusBond (n * L) → ℝ)
    (e : Fin 3) : ∑ q, |reflectedFunctional L t m o l e q| ≤ ∑ b, |l b| := by
  classical
  rw [Fintype.sum_prod_type]
  have h1 : ∀ bm : ↥(BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))),
      ∑ a : Fin 3, |reflectedFunctional L t m o l e (bm, a)| ≤
        ∑ c : TorusBond (n * L), if reflectedBondPosition L t m o c = bm.1 then |l c| else 0 := fun bm => by
    rw [Finset.sum_eq_single e]
    · simp only [reflectedFunctional, if_true]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      split_ifs <;> simp
    · intro a _ ha
      simp [reflectedFunctional, ha]
    · intro h
      exact absurd (Finset.mem_univ e) h
  refine (Finset.sum_le_sum fun bm _ => h1 bm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases h : reflectedBondPosition L t m o c ∈ BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))
  · rw [Finset.sum_eq_single
      (⟨reflectedBondPosition L t m o c, h⟩ : ↥(BlockAverages.chordBonds (finiteCells (reflectedTorusFrame L t m n))))]
    · simp
    · intro b _ hb
      rw [if_neg fun e' => hb (Subtype.ext e'.symm)]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [Finset.sum_eq_zero]
    · exact abs_nonneg _
    · intro b _
      have hne : ¬ reflectedBondPosition L t m o c = b.1 := fun e' => h (by rw [e']; exact b.2)
      rw [if_neg hne]
private theorem reflected_moment_bound {r : ℕ} (R : StepSetup) (m : ℕ) (hm : 0 < m) (h2 : 2 ≤ n)
    (hL : Odd R.params.side) (o : TorusSite n) (V : TorusField n)
    (g : TorusSite n → UnitQuaternion) (Bin Bbig : Finset (TorusSite n)) (l : Fin r → TorusBond (n * R.params.side) → ℝ)
    (e : Fin r → Fin 3)
    (hρ : R.ballRadius ≤ 1) (hρ0 : 0 ≤ R.ballRadius) (hx : 0 < R.coupling)
    (hl : ∀ i (b : TorusBond (n * R.params.side)), parentBlock R.params.side b.1 ∉ Bin → l i b = 0)
    (hgeo : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 ∈ Bin →
      parentBlock R.params.side c.1 ∈ Bbig ∧
      ∀ i, |(parentBlock R.params.side c.1 i - o i).valMinAbs| ≤ m ∧
        2 * |(parentBlock R.params.side c.1 i - o i).valMinAbs| + 1 < (n : ℤ))
    (hw : Integrable fun η => cutoffWeight R.ballRadius R.barrierFn η *
      Real.exp (- stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
        (localFamilyOfDensity R.density) 1 (reflectedTopField R.params.side R.depth m o V) η))
    (hcar : ∀ (Γ : (reflectedTorusFrame R.params.side R.depth m n).Cell → UnitQuaternion)
      (H : StepVariable (finiteCells (reflectedTorusFrame R.params.side R.depth m n)) → ℝ),
      cutoffMean R.ballRadius R.barrierFn (stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
          (localFamilyOfDensity R.density) 1
          (BlockAverages.gaugeTransform Γ (reflectedTopField R.params.side R.depth m o V))) H =
        cutoffMean R.ballRadius R.barrierFn (stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
            (localFamilyOfDensity R.density) 1 (reflectedTopField R.params.side R.depth m o V))
          fun η => H (adjointStepVariable Γ η))
    (hMir : ReflectedFieldOfGaugedTop) (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hL2 : ∀ l' : Fin r → ChartCoordinate (reflectedTorusFrame R.params.side R.depth m n) → ℝ,
      |reflectedStepMean R m o (TorusFields.gaugeTransform (restrictGauge g Bbig) V)
          (fun η => ∏ i, linearFunctional (l' i) η) -
        R.coupling ^ (-(r : ℝ) / 2) * wickPairingSum fun i j => l' i ⬝ᵥ Matrix.mulVec
          (frameHessian R.params.coupling R.anchorRadius R.frameReach (reflectedTopField R.params.side R.depth m o
            (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹ (l' j)| ≤
        C₂ * R.coupling ^ (-((r : ℝ) + 1) / 2) * ∏ i, ∑ p, |l' i p|)
    (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε) (W : Fin r → Fin r → ℝ)
    (hW : ∀ i i', |W i i'| ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|))
    (hA : ∀ i i', |reflectedFunctional R.params.side R.depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
      (frameHessian R.params.coupling R.anchorRadius R.frameReach (reflectedTopField R.params.side R.depth m o
        (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
      (reflectedFunctional R.params.side R.depth m o (l i') (e i'))| ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|))
    (hAW : ∀ i i', |reflectedFunctional R.params.side R.depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
      (frameHessian R.params.coupling R.anchorRadius R.frameReach (reflectedTopField R.params.side R.depth m o
        (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
      (reflectedFunctional R.params.side R.depth m o (l i') (e i')) - W i i'| ≤
        K * (∑ b, |l i b|) * (∑ b, |l i' b|) * ε) :
    |∑ φ : Fin r → ↥(chartBondsInBlocks R.params.side Bin) × Fin 3,
        (∏ i, rotatedCoeff (ℓ := R.params) g (l i) (e i) ((φ i).1.1, (φ i).2)) *
          reflectedStepMean R m o V (fun η => clampedMonomial φ (imaginaryComponentsOn (chartBondsInBlocks R.params.side Bin)
            (reflectedCoordinateAt R.params.side R.depth m o η))) -
      R.coupling ^ (-(r : ℝ) / 2) * wickPairingSum W| ≤
      C₂ * R.coupling ^ (-((r : ℝ) + 1) / 2) * (∏ i, ∑ b, |l i b|) +
        R.coupling ^ (-(r : ℝ) / 2) * ((Fintype.card (Finpartition (Finset.univ : Finset (Fin r))) : ℝ) *
          ((r : ℝ) * K ^ r) * (∏ i, ∑ b, |l i b|) * ε) := by
  set Γ : (reflectedTorusFrame R.params.side R.depth m n).Cell → UnitQuaternion :=
    reflectedGauge m (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top o)
      (fun x => restrictGauge g Bbig (toTorusSite n x)) with hΓ
  have htop := reflectedTopField_gaugeTransform (L := R.params.side) (t := R.depth) hMir hm o (restrictGauge g Bbig) V
  have e1 : ∑ φ : Fin r → ↥(chartBondsInBlocks R.params.side Bin) × Fin 3,
        (∏ i, rotatedCoeff (ℓ := R.params) g (l i) (e i) ((φ i).1.1, (φ i).2)) *
          reflectedStepMean R m o V (fun η => clampedMonomial φ (imaginaryComponentsOn (chartBondsInBlocks R.params.side Bin)
            (reflectedCoordinateAt R.params.side R.depth m o η))) =
      reflectedStepMean R m o (TorusFields.gaugeTransform (restrictGauge g Bbig) V)
        (fun η => ∏ i, linearFunctional (reflectedFunctional R.params.side R.depth m o (l i) (e i)) η) := by
    unfold reflectedStepMean
    rw [htop]
    refine sum_cutoffMean_monomials (ℓ := R.params) o Γ g Bin l e hl
      (fun c hc hch => reflectedBondPosition_not_mem hL hm h2 o c hch) (fun c hc => ?_)
      hρ hρ0 R.barrierFn _ _ hw (fun H => hcar Γ H)
    obtain ⟨hcB, hb⟩ := hgeo c hc
    rw [enclosingCell_reflectedBondPosition hL hm o c (fun i => (parentBlock R.params.side c.1 i - o i).valMinAbs)
      (fun i => rfl) (fun i => (hb i).2)]
    rw [hΓ, reflectedGauge_siteOfCoords hm o (restrictGauge g Bbig) (parentBlock R.params.side c.1) _ (fun i => rfl)
      (fun i => (hb i).1)]
    unfold restrictGauge
    rw [if_pos hcB]
  rw [e1]
  have hrow := hL2 fun i => reflectedFunctional R.params.side R.depth m o (l i) (e i)
  have hprod : ∏ i, ∑ p, |reflectedFunctional R.params.side R.depth m o (l i) (e i) p| ≤ ∏ i, ∑ b, |l i b| :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      fun i _ => sum_abs_reflectedFunctional_le o _ _
  have hxp : 0 ≤ R.coupling ^ (-((r : ℝ) + 1) / 2) := (Real.rpow_pos_of_pos hx _).le
  have hxq : 0 ≤ R.coupling ^ (-(r : ℝ) / 2) := (Real.rpow_pos_of_pos hx _).le
  have hdiff := abs_wickPairingSum_sub_le _ W (fun i => ∑ b, |l i b|) K ε hK hε
    (fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _) hA hW hAW
  calc _ ≤ |reflectedStepMean R m o (TorusFields.gaugeTransform (restrictGauge g Bbig) V)
        (fun η => ∏ i, linearFunctional (reflectedFunctional R.params.side R.depth m o (l i) (e i)) η) -
        R.coupling ^ (-(r : ℝ) / 2) * wickPairingSum fun i j =>
          reflectedFunctional R.params.side R.depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
          (frameHessian R.params.coupling R.anchorRadius R.frameReach (reflectedTopField R.params.side R.depth m o
            (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
          (reflectedFunctional R.params.side R.depth m o (l j) (e j))| +
      |R.coupling ^ (-(r : ℝ) / 2) * (wickPairingSum fun i j =>
          reflectedFunctional R.params.side R.depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
          (frameHessian R.params.coupling R.anchorRadius R.frameReach (reflectedTopField R.params.side R.depth m o
            (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
          (reflectedFunctional R.params.side R.depth m o (l j) (e j))) -
        R.coupling ^ (-(r : ℝ) / 2) * wickPairingSum W| := abs_sub_le _ _ _
    _ ≤ _ := by
      refine add_le_add (hrow.trans (mul_le_mul_of_nonneg_left hprod (mul_nonneg hC₂ hxp))) ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg hxq]
      exact mul_le_mul_of_nonneg_left hdiff hxq
end TopSide
section Core
variable (Tb : ParameterAssignment) (y : ℝ)
private theorem localChain_mono {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} {nn x₀ x₁ : ℝ}
    (h : IsLocalChainAbove Tb y T β k N nn x₀) (hx : x₁ ≤ x₀) : IsLocalChainAbove Tb y T β k N nn x₁ :=
  { h with floor_le := hx.trans h.floor_le }
private theorem gaugeTransform_one {n : ℕ} (V : TorusField n) :
    TorusFields.gaugeTransform (fun _ => (1 : UnitQuaternion)) V = V := by
  funext x i
  simp [TorusFields.gaugeTransform]
private theorem smallCurvature_mono {F : BlockFrame} {j : ℕ} {s s' : ℝ} {X : F.GaugeField j}
    (h : IsSmallCurvature s X) (hs : s ≤ s') : IsSmallCurvature s' X := fun p hp => (h p hp).trans_le hs
private theorem abs_couplingFlow_sub_le {β : ℝ} {k j : ℕ}
    (hR : ClusterExpansionOfAStep.FlowHasExpansionAt (Tb.stepParameters y) β)
    (hy : ∀ i ≤ k + j, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β i).1) :
    |(couplingFlow (Tb.stepParameters y) β (k + j)).1 - (couplingFlow (Tb.stepParameters y) β k).1| ≤
      2 * (Tb.stepParameters y).B * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih fun i hi => hy i (by omega)
    have h2 := (hR (k + j)).2 fun i hi => hy i (by omega)
    have e : (couplingFlow (Tb.stepParameters y) β (k + (j + 1))).1 - (couplingFlow (Tb.stepParameters y) β k).1 =
        ((couplingFlow (Tb.stepParameters y) β (k + j + 1)).1 - (couplingFlow (Tb.stepParameters y) β (k + j)).1) +
          ((couplingFlow (Tb.stepParameters y) β (k + j)).1 - (couplingFlow (Tb.stepParameters y) β k).1) := by
      rw [← add_assoc]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2' : |(couplingFlow (Tb.stepParameters y) β (k + j + 1)).1 - (couplingFlow (Tb.stepParameters y) β (k + j)).1| ≤
        2 * (Tb.stepParameters y).B := h2
    push_cast
    linarith
private def GaussianMomentBound (S : ColdStepAtMirrorFrames.StepParameters) (q : ℕ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), S.coupling ≤ x →
    IsRegularFamily S.L t S.n₀ S.σ S.decayRate S.E S.energyRatio f → IsCubicTopTorus S.L t S.n₀ F →
    IsSmallCurvature (9 / 8 * S.σ) V →
    ∀ l : Fin q → ChartCoordinate F → ℝ,
      |cutoffMean S.ballRadius S.p (stepExponent false S.a S.chainParams.ρA x (frameRadius x) f 1 V)
          (fun η => ∏ i, linearFunctional (l i) η) -
        x ^ (-(q : ℝ) / 2) * wickPairingSum fun i j =>
          l i ⬝ᵥ Matrix.mulVec (frameHessian S.a S.chainParams.ρA (frameRadius x) V)⁻¹ (l j)| ≤
      C * x ^ (-((q : ℝ) + 1) / 2) * ∏ i, ∑ p, |l i p|
private theorem reflected_moment_bound_at_stage {r : ℕ} (T : StageTower (Tb.stepParameters y)) (t : ℕ) {n : ℕ} [NeZero n]
    (m : ℕ) (hm : 0 < m) (h2m : 2 * m + 2 < n)
    (hn₀ : (Tb.stepParameters y).n₀ ≤ 4 * m) (o : TorusSite n) (V : TorusField n) (g : TorusSite n → UnitQuaternion)
    (Bin Bbig : Finset (TorusSite n))
    (l : Fin r → TorusBond (n * (Tb.stepParameters y).side) → ℝ) (e : Fin r → Fin 3) (hD : Tb.Admissible)
    (hyC : Tb.yC ≤ y) (hfit : (Tb.stepParameters y).Admissible)
    (hOT : (T.stage t).toStepSetup.OnParameters Tb y) (hcoldV : IsColdOnBall (Tb.stepParameters y).threshold V o m)
    (hl : ∀ i (b : TorusBond (n * (Tb.stepParameters y).side)), parentBlock (Tb.stepParameters y).side b.1 ∉ Bin → l i b = 0)
    (hgeo : ∀ c : TorusBond (n * (Tb.stepParameters y).side), parentBlock (Tb.stepParameters y).side c.1 ∈ Bin →
      parentBlock (Tb.stepParameters y).side c.1 ∈ Bbig ∧
      ∀ i, |(parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs| ≤ m ∧
        2 * |(parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs| + 1 < (n : ℤ))
    (hCold : mirrorOfColdBallSmallCurvatureStatement) (hRB : ColdExpansionRegular) (hMir : ReflectedFieldOfGaugedTop)
    (c₁ : ColdChainParameters) (nss₁ : ℕ) (hT₁ : Tb.Compatible c₁)
    (hA₁ : ∀ y' : ℝ, Tb.yC ≤ y' → DensityConditionsAt (Tb.stepParamsAt c₁ nss₁ y'))
    (c₃ : ColdChainParameters) (nss₃ : ℕ) (hT₃ : Tb.Compatible c₃)
    (hA₃ : ∀ y' : ℝ, Tb.yC ≤ y' → GaugeInvarianceOfStepLawAt (Tb.stepParamsAt c₃ nss₃ y'))
    (c₂ : ColdChainParameters) (nss₂ : ℕ) (hT₂ : Tb.Compatible c₂) (C₂ : ℝ)
    (HL : GaussianMomentBound (Tb.stepParamsAt c₂ nss₂ y) r C₂)
    (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε) (W : Fin r → Fin r → ℝ)
    (hW : ∀ i i', |W i i'| ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|))
    (hA : ∀ i i', |reflectedFunctional (Tb.stepParameters y).side (T.stage t).depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
      (frameHessian (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).toStepSetup.frameReach
        (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
          (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
      (reflectedFunctional (Tb.stepParameters y).side (T.stage t).depth m o (l i') (e i'))| ≤
        K * (∑ b, |l i b|) * (∑ b, |l i' b|))
    (hAW : ∀ i i', |reflectedFunctional (Tb.stepParameters y).side (T.stage t).depth m o (l i) (e i) ⬝ᵥ Matrix.mulVec
      (frameHessian (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).toStepSetup.frameReach
        (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
          (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹
      (reflectedFunctional (Tb.stepParameters y).side (T.stage t).depth m o (l i') (e i')) - W i i'| ≤
        K * (∑ b, |l i b|) * (∑ b, |l i' b|) * ε) :
    |∑ φ : Fin r → ↥(chartBondsInBlocks (Tb.stepParameters y).side Bin) × Fin 3,
        (∏ i, rotatedCoeff g (l i) (e i) ((φ i).1.1, (φ i).2)) *
          reflectedStepMean (T.stage t).toStepSetup m o V (fun η => clampedMonomial φ
            (imaginaryComponentsOn (chartBondsInBlocks (Tb.stepParameters y).side Bin)
              (reflectedCoordinateAt (Tb.stepParameters y).side (T.stage t).depth m o η))) -
      (T.stage t).coupling ^ (-(r : ℝ) / 2) * wickPairingSum W| ≤
      |C₂| * (T.stage t).coupling ^ (-((r : ℝ) + 1) / 2) * (∏ i, ∑ b, |l i b|) +
        (T.stage t).coupling ^ (-(r : ℝ) / 2) *
          ((Fintype.card (Finpartition (Finset.univ : Finset (Fin r))) : ℝ) * ((r : ℝ) * K ^ r) *
          (∏ i, ∑ b, |l i b|) * ε) := by
  have hρA₁ : c₁.ρA = (T.stage t).anchorRadius := hT₁.2.2.1.trans hOT.anchorRadius_eq.symm
  have hρA₂ : c₂.ρA = (T.stage t).anchorRadius := hT₂.2.2.1.trans hOT.anchorRadius_eq.symm
  have hρA₃ : c₃.ρA = (T.stage t).anchorRadius := hT₃.2.2.1.trans hOT.anchorRadius_eq.symm
  have hp : Tb.cutoff = (T.stage t).barrierFn := hOT.barrierFn_eq.symm
  have hodd : Odd (Tb.stepParameters y).side := hfit.L_odd
  have hσ0 : 0 < (Tb.stepParameters y).threshold := hfit.σ_pos
  have hσ1 : (Tb.stepParameters y).threshold ≤ 1 := hD.σ_one
  have hy1 : 1 ≤ y := hfit.y₁_ge
  have hxy : y ≤ (T.stage t).coupling := hOT.le_coupling
  have hrowB : IsRegularFamily (Tb.stepParameters y).side (T.stage t).depth (Tb.stepParameters y).n₀
      (Tb.stepParameters y).threshold (Tb.stepParameters y).weightRate (Tb.stepParameters y).E
      (Tb.stepParameters y).E₃ (localFamilyOfDensity (T.stage t).density) :=
    hRB (Tb.stepParameters y) (T.stage t).depth (T.stage t).coupling (T.stage t).functional (T.stage t).density hfit rfl
      hOT.isStep.1.1
  have hTop : IsCubicTopTorus (Tb.stepParameters y).side (T.stage t).depth (Tb.stepParameters y).n₀
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n) :=
    ⟨rfl, rfl, 4 * m, fun _ => rfl, hn₀⟩
  have hc1 : IsSmallCurvature (Tb.stepParameters y).threshold
      (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V) := by
    have := hCold (Tb.stepParameters y).side (T.stage t).depth m n o V (fun _ => 1) (Tb.stepParameters y).threshold hσ0
      hm h2m hodd hcoldV
    rwa [gaugeTransform_one] at this
  have hc2 : IsSmallCurvature (Tb.stepParameters y).threshold
      (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
        (TorusFields.gaugeTransform (restrictGauge g Bbig) V)) :=
    hCold (Tb.stepParameters y).side (T.stage t).depth m n o V _ (Tb.stepParameters y).threshold hσ0 hm h2m hodd hcoldV
  have hw : Integrable fun η => cutoffWeight (T.stage t).toStepSetup.ballRadius (T.stage t).barrierFn η *
      Real.exp (- stepExponent false (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).coupling
        (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
        (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V) η) := by
    obtain ⟨-, M', hreg⟩ := (hA₁ y hyC (T.stage t).depth (T.stage t).coupling hxy
        (localFamilyOfDensity (T.stage t).density) hrowB).regular
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n) hTop
      (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V)
      (smallCurvature_mono hc1 (by
        show (Tb.stepParameters y).threshold ≤ 9 / 8 * (Tb.stepParameters y).threshold; linarith))
    have hreg' : IsRegularStep (Tb.stepParameters y).coupling c₁.ρA (T.stage t).toStepSetup.ballRadius c₁.lam
      (T.stage t).coupling M' (T.stage t).toStepSetup.frameReach Tb.cutoff
      (localFamilyOfDensity (T.stage t).density) (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V) :=
      hreg
    rw [hρA₁, hp] at hreg'
    exact integrable_cutoffWeight_mul_exp (fun _ => by show 0 < 4 * m; omega) hreg'
  have hcar : ∀ (Γ : (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n).Cell → UnitQuaternion)
      (H : StepVariable (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n)) → ℝ),
      cutoffMean (T.stage t).toStepSetup.ballRadius (T.stage t).barrierFn
        (stepExponent false (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).coupling
          (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
          (BlockAverages.gaugeTransform Γ (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V))) H =
      cutoffMean (T.stage t).toStepSetup.ballRadius (T.stage t).barrierFn
        (stepExponent false (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).coupling
          (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
          (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V))
        fun η => H (adjointStepVariable Γ η) := fun Γ H => by
    have h := hA₃ y hyC (T.stage t).depth (T.stage t).coupling hxy (localFamilyOfDensity (T.stage t).density) hrowB
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n) hTop
      (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V)
      (smallCurvature_mono hc1 (by
        show (Tb.stepParameters y).threshold ≤ 5 / 4 * (Tb.stepParameters y).threshold; linarith)) Γ H
    have h' : cutoffMean (T.stage t).toStepSetup.ballRadius Tb.cutoff
        (stepExponent false (Tb.stepParameters y).coupling c₃.ρA (T.stage t).coupling
          (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
          (BlockAverages.gaugeTransform Γ (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V))) H =
      cutoffMean (T.stage t).toStepSetup.ballRadius Tb.cutoff
        (stepExponent false (Tb.stepParameters y).coupling c₃.ρA (T.stage t).coupling
          (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
          (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o V))
        fun η => H (adjointStepVariable Γ η) := h
    rwa [hρA₃, hp] at h'
  have hL2 : ∀ l' : Fin r → ChartCoordinate (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n) → ℝ,
      |reflectedStepMean (T.stage t).toStepSetup m o (TorusFields.gaugeTransform (restrictGauge g Bbig) V)
          (fun η => ∏ i, linearFunctional (l' i) η) -
        (T.stage t).coupling ^ (-(r : ℝ) / 2) * wickPairingSum fun i j => l' i ⬝ᵥ Matrix.mulVec
          (frameHessian (Tb.stepParameters y).coupling (T.stage t).anchorRadius (T.stage t).toStepSetup.frameReach
            (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
              (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹ (l' j)| ≤
        |C₂| * (T.stage t).coupling ^ (-((r : ℝ) + 1) / 2) * ∏ i, ∑ p, |l' i p| := fun l' => by
    have h := HL (T.stage t).depth (T.stage t).coupling (localFamilyOfDensity (T.stage t).density)
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage t).depth m n)
      (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
        (TorusFields.gaugeTransform (restrictGauge g Bbig) V)) hxy hrowB hTop
      (smallCurvature_mono hc2 (by
        show (Tb.stepParameters y).threshold ≤ 9 / 8 * (Tb.stepParameters y).threshold; linarith)) l'
    have h' : |cutoffMean (T.stage t).toStepSetup.ballRadius Tb.cutoff
          (stepExponent false (Tb.stepParameters y).coupling c₂.ρA (T.stage t).coupling
            (T.stage t).toStepSetup.frameReach (localFamilyOfDensity (T.stage t).density) 1
            (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
              (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))
          (fun η => ∏ i, linearFunctional (l' i) η) -
        (T.stage t).coupling ^ (-(r : ℝ) / 2) * wickPairingSum fun i j => l' i ⬝ᵥ Matrix.mulVec
          (frameHessian (Tb.stepParameters y).coupling c₂.ρA (T.stage t).toStepSetup.frameReach
            (reflectedTopField (Tb.stepParameters y).side (T.stage t).depth m o
              (TorusFields.gaugeTransform (restrictGauge g Bbig) V)))⁻¹ (l' j)| ≤
        C₂ * (T.stage t).coupling ^ (-((r : ℝ) + 1) / 2) * ∏ i, ∑ p, |l' i p| := h
    rw [hρA₂, hp] at h'
    refine h'.trans ?_
    have hx0 : 0 < (T.stage t).coupling := by linarith
    have h1 : 0 ≤ (T.stage t).coupling ^ (-((r : ℝ) + 1) / 2) := (Real.rpow_pos_of_pos hx0 _).le
    have h2 : 0 ≤ ∏ i, ∑ p, |l' i p| := Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) h1) h2
  exact reflected_moment_bound (T.stage t).toStepSetup m hm (by omega) hodd o V g Bin Bbig l e
    (by show (Tb.stepParameters y).threshold / 64 ≤ 1; linarith)
    (by show 0 ≤ (Tb.stepParameters y).threshold / 64; positivity) (by show 0 < (T.stage t).coupling; linarith)
    hl hgeo hw hcar hMir |C₂| (abs_nonneg _) hL2 K ε hK hε W hW hA hAW
private theorem abs_sub_le_of_chain {E S p₀ Pw p₁ a s e₄ eH ec e c2 c4 G F D A₀ A₁ X₀ X₁ h : ℝ}
    (h₁ : |E - S| ≤ G * (c4 * e₄)) (h₂ : |S - p₀ * Pw| ≤ c2 * p₁ * a + p₀ * (D * a * (s + eH)))
    (hp₀ : p₀ ≤ A₀ * X₀) (hp₁ : p₁ ≤ A₁ * X₁) (hp₀0 : 0 ≤ p₀) (hp₁0 : 0 ≤ p₁) (ha0 : 0 ≤ a) (ha : a ≤ F * h)
    (hX₀0 : 0 ≤ X₀) (hX₁0 : 0 ≤ X₁) (hX₀ : X₀ ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1) (hs : 0 ≤ s) (he₄ : e₄ ≤ ec)
    (heH : eH ≤ ec)
    (heH0 : 0 ≤ eH) (hc2 : 0 ≤ c2) (hc4 : 0 ≤ c4) (hG : 0 ≤ G) (hF : 0 ≤ F) (hD : 0 ≤ D) (hA₀ : 0 ≤ A₀)
    (hA₁ : 0 ≤ A₁)
    (hQ : (G * c4 + A₀ * D * F) * ec ≤ e) :
    |E - p₀ * Pw| ≤ (c2 * A₁ * F + A₀ * D * F) * h * (X₁ + X₀ * s) + e := by
  have t0 : |E - p₀ * Pw| ≤ |E - S| + |S - p₀ * Pw| := abs_sub_le _ _ _
  have u1 : c2 * p₁ * a ≤ c2 * (A₁ * X₁) * (F * h) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp₁ hc2) ha ha0 (by positivity)
  have u2 : p₀ * (D * a * (s + eH)) ≤ (A₀ * X₀) * (D * (F * h) * (s + eH)) := by
    have hse : 0 ≤ s + eH := add_nonneg hs heH0
    refine mul_le_mul hp₀ ?_ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hD) hse
  have t1 : G * (c4 * e₄) ≤ G * (c4 * ec) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he₄ hc4) hG
  have v : X₀ * h * eH ≤ ec := by
    have : X₀ * h ≤ 1 := by nlinarith
    have h0 : 0 ≤ X₀ * h := by positivity
    nlinarith
  have t2 : A₀ * D * F * (X₀ * h * eH) ≤ A₀ * D * F * ec := mul_le_mul_of_nonneg_left v (by positivity)
  have t3 : 0 ≤ c2 * A₁ * F * h * X₀ * s := by positivity
  have t4 : 0 ≤ A₀ * D * F * h * X₁ := by positivity
  nlinarith [t0, h₁, h₂, u1, u2, t1, t2, t3, t4, hQ]
set_option maxHeartbeats 400000 in
private theorem stepCurvatureMomentsAt_of (hD : Tb.Admissible) (hyC : Tb.yC ≤ y) (hy₀ : Tb.floorMin ≤ y)
    (hCS : Tb.ColdStepHolds)
    (hOn : Tb.HoldsFrom ColdRegimeEstimatesAt) (hCar : stepLawGaugeInvariantStatement)
    (hMk : chainMarkovBackwardsStatement) (hLaw : BoxMarks.lowerMarginalStatement)
    (hSt : StageStatesMeasurableStatement) (hProb : TwoPointByTotalCovarianceStatement)
    (hMir : reflectedFieldReadsBox) (hCold : mirrorOfColdBallSmallCurvatureStatement) (hRB : ColdExpansionRegular)
    (hScaleFlow : ∀ β, y ≤ β → ClusterExpansionOfAStep.FlowHasExpansionAt (Tb.stepParameters y) β)
    (hlaw : oneStepReflectedLawAt Tb y) (hBox : descentKeepsBallClearAt Tb y)
    (hBor : stepDeviationMeasurableAt Tb y) (hHess : reflectedHessianComparisonAt Tb y) :
    stepCurvatureMomentsAt Tb y := by
  intro r hr
  obtain ⟨C₄, c₄, x₄, hc₄, H₄⟩ := hlaw
  obtain ⟨x_b, Hb⟩ := hBox
  obtain ⟨x_r, Hr⟩ := hBor
  obtain ⟨C_H, c_H, x_H, hc_H, HH⟩ := hHess
  obtain ⟨c₂, nss₂, hT₂, hA₂⟩ := hOn
  obtain ⟨c₁, nss₁, hT₁, hA₁⟩ := hCS
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy₀
  have hLam : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hfit.depth_lt
  have hA₃ : ∀ y' : ℝ, Tb.yC ≤ y' → GaugeInvarianceOfStepLawAt (Tb.stepParamsAt c₂ nss₂ y') := fun y' hy' =>
    hCar _ hD.L_odd (by
      have := hD.n₀_ge
      show 2 ≤ Tb.n₀
      omega) hD.σ_pos (hA₂ y' hy').equivariance
  obtain ⟨C₂, HL⟩ := (hA₂ y hyC).secondOrderMoments r
  set K : ℝ := max 1 |C_H| with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKC : |C_H| ≤ K := le_max_right _ _
  set D : ℝ := (Fintype.card (Finpartition (Finset.univ : Finset (Fin r))) : ℝ) * ((r : ℝ) * K ^ r) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set A₀ : ℝ := (1 / 2 : ℝ) ^ (-(r : ℝ) / 2) with hA₀
  set A₁ : ℝ := (1 / 2 : ℝ) ^ (-((r : ℝ) + 1) / 2) with hA₁'
  have hA₀p : 0 < A₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hA₁p : 0 < A₁ := Real.rpow_pos_of_pos (by norm_num) _
  set cc : ℝ := min c₄ c_H with hcc
  have hccp : 0 < cc := lt_min hc₄ hc_H
  set Q₁ : ℝ := 12 ^ r * |C₄| + A₀ * D * 4 ^ r with hQ₁
  have hQ₁0 : 0 ≤ Q₁ := by positivity
  have hB0 : 0 < (Tb.stepParameters y).B := hfit.B_pos
  obtain ⟨xl, Hl⟩ := eventually_large_coupling
    (2 * Q₁ / cc + 8 * (Tb.stepParameters y).B + ((Tb.stepParameters y).n₀ : ℝ) + 8)
  refine ⟨|C₂| * A₁ * 4 ^ r + A₀ * D * 4 ^ r, cc / 2, max (max (max x₄ x_b) (max x_r x_H)) xl, by positivity, ?_⟩
  intro T β k N _ nn j d' o g s l e hloc hLdiv hj hjd hg hs hs0 hl1 hl2
  have hloc₄ : IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x₄ :=
    localChain_mono Tb y hloc ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hlocb : IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x_b :=
    localChain_mono Tb y hloc ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hlocr : IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x_r :=
    localChain_mono Tb y hloc ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hlocH : IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x_H :=
    localChain_mono Tb y hloc ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  set x : ℝ := flowCouplings (Tb.stepParameters y) β k with hxdef
  have hxl : xl ≤ x := (le_max_right _ _).trans hloc.floor_le
  obtain ⟨hx1, hpow, hlog3, hlog2⟩ := Hl x hxl
  set m : ℕ := localBlockSide (Tb.stepParameters y) β k with hmdef
  set ρ₀ : ℝ := localLogScale (Tb.stepParameters y) β k with hρdef
  set P : ℝ := 2 * Q₁ / cc + 8 * (Tb.stepParameters y).B + ((Tb.stepParameters y).n₀ : ℝ) + 8 with hPdef
  have hP0 : 2 * Q₁ / cc ≤ P - 8 * (Tb.stepParameters y).B - ((Tb.stepParameters y).n₀ : ℝ) - 8 := by
    rw [hPdef]; linarith
  have hPq : 0 ≤ 2 * Q₁ / cc := by positivity
  have hn0r : (0 : ℝ) ≤ ((Tb.stepParameters y).n₀ : ℝ) := Nat.cast_nonneg _
  have hx20 : 0 ≤ x ^ ((1 : ℝ) / 20) := Real.rpow_nonneg (by linarith) _
  have hmle : (m : ℝ) ≤ x ^ ((1 : ℝ) / 20) := Nat.floor_le hx20
  have hmgt : x ^ ((1 : ℝ) / 20) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl3 : 0 ≤ Real.log x ^ 3 := by linarith
  have hρle : ρ₀ ≤ Real.log x ^ 3 := Nat.floor_le hl3
  have hρgt : Real.log x ^ 3 < ρ₀ + 1 := Nat.lt_floor_add_one _
  have hρ0 : 0 ≤ ρ₀ := Nat.cast_nonneg _
  have hMle : (localChainDepth (Tb.stepParameters y) β k : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (sq_nonneg _)
  have hnn1 : 1 ≤ nn := hloc.one_le
  have hnn2 : nn ≤ x ^ ((1 : ℝ) / 90) := hloc.le_rpow
  have hLpos : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) ^ (j + 1) := one_le_pow₀ (by
    have := hfit.L_ge
    exact_mod_cast (by omega : 1 ≤ (Tb.stepParameters y).side))
  have hrB : ballRadius (Tb.stepParameters y).side nn ρ₀ (j + 1) ≤
      20 * x ^ ((1 : ℝ) / 90) + 4 * Real.log x ^ 3 := by
    unfold ballRadius
    have : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) ≤ 20 * nn := div_le_self (by linarith) hLpos
    linarith
  have hm8 : ballRadius (Tb.stepParameters y).side nn ρ₀ (j + 1) ≤ (m : ℝ) / 8 := by linarith
  have hmP : 1 ≤ (m : ℝ) := by
    have : 8 ≤ P := by linarith
    have h0 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg (by linarith) _
    linarith
  have hm0 : 0 < m := by exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hρm : ρ₀ ≤ m := by
    have h0 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg (by linarith) _
    linarith
  have hρQ : 2 * Q₁ / cc ≤ ρ₀ := by linarith
  have hn₀m : (Tb.stepParameters y).n₀ ≤ 4 * m := by
    have h0 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg (by linarith) _
    have : ((Tb.stepParameters y).n₀ : ℝ) ≤ 4 * (m : ℝ) := by linarith
    exact_mod_cast this
  have hside : 2 ^ 10 * m ≤ fineSide (Tb.stepParameters y).side d' N := by
    have h : (2 : ℝ) ^ 10 * (m : ℝ) ≤ (fineSide (Tb.stepParameters y).side d' N : ℝ) := hloc.side_ge
    exact_mod_cast h
  have h2m : 2 * m + 2 < fineSide (Tb.stepParameters y).side d' N := by omega
  have h2n : 2 ≤ fineSide (Tb.stepParameters y).side d' N := by omega
  set Bin := supBall o (ballRadius (Tb.stepParameters y).side nn ρ₀ (j + 1) - 3 * ρ₀) with hBin
  set Bbig := supBall o (ballRadius (Tb.stepParameters y).side nn ρ₀ (j + 1)) with hBbig
  have hsub8 : Bin ⊆ supBall o ((m : ℝ) / 8) := fun z hz => by
    have h := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
  have hsubm : Bin ⊆ supBall o (m : ℝ) := fun z hz => by
    have h := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
  have hZ8 : chartBondsInBlocks (Tb.stepParameters y).side Bin ⊆
      chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8)) := fun b hb => by
    have := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨this.1, hsub8 this.2⟩
  have hZm : chartBondsInBlocks (Tb.stepParameters y).side Bin ⊆
      chartBondsInBlocks (Tb.stepParameters y).side (supBall o (m : ℝ)) := fun b hb => by
    have := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨this.1, hsubm this.2⟩
  have hgeo : ∀ c : TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side),
      parentBlock (Tb.stepParameters y).side c.1 ∈ Bin → parentBlock (Tb.stepParameters y).side c.1 ∈ Bbig ∧
      ∀ i, |(parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs| ≤ m ∧
        2 * |(parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs| + 1 <
          ((fineSide (Tb.stepParameters y).side d' N : ℕ) : ℤ) := fun c hc => by
    have h := (Finset.mem_filter.mp hc).2
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩, fun i => ?_⟩
    have h1 : ((parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs).natAbs ≤
        supDist (parentBlock (Tb.stepParameters y).side c.1) o :=
      Finset.le_sup (f := fun i => ((parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs).natAbs)
        (Finset.mem_univ i)
    have h2 : (supDist (parentBlock (Tb.stepParameters y).side c.1) o : ℝ) ≤ m := by linarith
    have h3 : supDist (parentBlock (Tb.stepParameters y).side c.1) o ≤ m := by exact_mod_cast h2
    have h4 : |(parentBlock (Tb.stepParameters y).side c.1 i - o i).valMinAbs| ≤ m := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans h3
    refine ⟨h4, ?_⟩
    have h5 : (2 * m + 2 : ℤ) < ((fineSide (Tb.stepParameters y).side d' N : ℕ) : ℤ) := by exact_mod_cast h2m
    linarith
  have hjM : j < 2 * localChainDepth (Tb.stepParameters y) β k := by omega
  have hjd' : j ≤ 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := by
    have : j < localChainDepth (Tb.stepParameters y) β k := hj
    unfold localChainDepth flowCouplings at this
    omega
  have hOT : (T.stage (k + j)).toStepSetup.OnParameters Tb y := hloc.onFamily.onFamily (k + j) (by omega)
  have hcp : (T.stage (k + j)).coupling = (couplingFlow (Tb.stepParameters y) β (k + j)).1 :=
    hloc.onFamily.coupling_eq (k + j) (by omega)
  have hβ : y ≤ β := hloc.coupling_ge 0 (Nat.zero_le _)
  have hnearx := abs_couplingFlow_sub_le Tb y (k := k) (j := j) (hScaleFlow β hβ) (fun i hi => hloc.coupling_ge i (by omega))
  have hxpos : 0 < x := by linarith
  have hxt2 : x / 2 ≤ flowCouplings (Tb.stepParameters y) β (k + j) := by
    have h1 := abs_le.mp hnearx
    have hjl : (j : ℝ) ≤ Real.log x ^ 2 := by
      have : (j : ℝ) ≤ (localChainDepth (Tb.stepParameters y) β k : ℝ) := by exact_mod_cast hj.le
      linarith
    have hBP : 8 * (Tb.stepParameters y).B ≤ P := by linarith
    have h2 : 8 * (Tb.stepParameters y).B * Real.log x ^ 2 ≤ x :=
      (mul_le_mul_of_nonneg_right hBP (sq_nonneg _)).trans hlog2
    have h3 : 2 * (Tb.stepParameters y).B * (j : ℝ) ≤ 2 * (Tb.stepParameters y).B * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_left hjl (by positivity)
    have h4 : (couplingFlow (Tb.stepParameters y) β k).1 = x := rfl
    have h5 : flowCouplings (Tb.stepParameters y) β (k + j) = (couplingFlow (Tb.stepParameters y) β (k + j)).1 := rfl
    rw [h5]
    have h8 : x - 2 * (Tb.stepParameters y).B * (j : ℝ) ≤ (couplingFlow (Tb.stepParameters y) β (k + j)).1 :=
      sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp h1.1)
    have h9 : x / 2 ≤ x - 2 * (Tb.stepParameters y).B * Real.log x ^ 2 := by
      have h6 : 2 * (Tb.stepParameters y).B * Real.log x ^ 2 = (8 * (Tb.stepParameters y).B * Real.log x ^ 2) / 4 := by
        ring
      rw [h6]
      linarith
    exact h9.trans ((sub_le_sub_left h3 x).trans h8)
  have hcut := hloc.cutoff
  have hcoin := hloc.measurable
  have hprob : IsProbabilityMeasure (markedSampleLaw T β (k + j + 1 + d') N) :=
    (hProb (Tb.stepParameters y) hfit hLam T hcut hcoin β (fun _ => 0) (k + j + 1 + d') N).1
  have hst : ∀ (s n : ℕ) [NeZero n], stageSigma T s n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) s n :=
    fun s n _ => (hSt (Tb.stepParameters y) hfit T s n).comap_le
  have hσ0 : 0 < (Tb.stepParameters y).threshold := hfit.σ_pos
  have hσ1 : (Tb.stepParameters y).threshold ≤ 1 := hD.σ_one
  have hσ64 : (Tb.stepParameters y).threshold / 64 ≤ 1 := by linarith
  have hl4 : ∀ i, ∑ b, |l i b| ≤ 4 := fun i => by
    have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith [hl1 i]
  have hcl0 := Hb T β k _ nn j o hlocb hLdiv hjM
  have hcl : ∀ᵐ v ∂(markedSampleLaw T β (k + j + 1) (fineSide (Tb.stepParameters y).side d' N)),
      Disjoint (stageState T (k + j + 1) _ v).2.1 (supBall o (m : ℝ)) →
      IsColdOnBall (Tb.stepParameters y).threshold (topField (Tb.stepParameters y) (k + j + 1) _ v) o (m : ℝ) ∧
        (StepAvoids T (k + j) (m : ℝ) o v →
        ∀ b ∈ chartBondsInBlocks (Tb.stepParameters y).side Bin,
          ‖(stepDeviation T (k + j) (topField (Tb.stepParameters y) (k + j + 1) _ v)
            (topField (Tb.stepParameters y) (k + j) _ v.1) b : Quaternion ℝ)‖ < (Tb.stepParameters y).threshold / 64) := by
    filter_upwards [hcl0] with v hv hd
    exact ⟨(hv hd).1, fun hs' b hb => (((hv hd).2 hs').2 b (hZm hb)).2⟩
  have hBorel := Hr T β k _ nn j o hlocr hjM
  have hb1 : ∀ (b : TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side)) (a : Fin 3),
      b ∈ chartBondsInBlocks (Tb.stepParameters y).side Bin →
      Measurable (Set.indicator {q : TorusField (fineSide (Tb.stepParameters y).side d' N) ×
          TorusField (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) |
        IsColdOnBall (Tb.stepParameters y).threshold q.1 o (m : ℝ)}
        fun q => imaginaryComponent a (stepDeviation T (k + j) q.1 q.2 b)) :=
    fun b a hb => hBorel.1 b a (hZ8 hb)
  have hmk : ∀ (G : MarkedSample (Tb.stepParameters y) (k + j + 1) (fineSide (Tb.stepParameters y).side d' N) → ℝ),
      Measurable G → (∀ v, |G v| ≤ 1) →
      (markedSampleLaw T β (k + j + 1 + d') N)[fun u => G (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u) |
          upperSigma T (k + j + 1) d' N]
        =ᵐ[markedSampleLaw T β (k + j + 1 + d') N]
        (markedSampleLaw T β (k + j + 1 + d') N)[fun u => G (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u) |
          (stageSigma T (k + j + 1) (fineSide (Tb.stepParameters y).side d' N)).comap
            (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)] :=
    fun G hG hb => hMk (Tb.stepParameters y) hfit hLam T hcut hcoin β (k + j + 1) d' N G 1 hG hb
  have hδ : 0 ≤ |C₄| * Real.exp (-(c₄ * (m : ℝ))) := by positivity
  have hlaw' : ∀ F : (↥(chartBondsInBlocks (Tb.stepParameters y).side Bin) × Fin 3 → ℝ) → ℝ, Measurable F →
      (∀ v, |F v| ≤ 1) →
      ∀ᵐ v ∂(markedSampleLaw T β (k + j + 1) (fineSide (Tb.stepParameters y).side d' N)),
        Disjoint (stageState T (k + j + 1) _ v).2.1 (supBall o (m : ℝ)) →
        |((markedSampleLaw T β (k + j + 1) (fineSide (Tb.stepParameters y).side d' N))[Set.indicator
            (avoidSet T (k + j) o (m : ℝ))
            (fun u' => F (imaginaryComponentsOn (chartBondsInBlocks (Tb.stepParameters y).side Bin)
              (stepDeviation T (k + j) (topField (Tb.stepParameters y) (k + j + 1) _ u')
                (topField (Tb.stepParameters y) (k + j) _ u'.1)))) |
          stageSigma T (k + j + 1) (fineSide (Tb.stepParameters y).side d' N)]) v -
          reflectedStepMean (T.stage (k + j)).toStepSetup m o (topField (Tb.stepParameters y) (k + j + 1) _ v)
            (fun η => F (imaginaryComponentsOn (chartBondsInBlocks (Tb.stepParameters y).side Bin)
              (reflectedCoordinateAt (Tb.stepParameters y).side (T.stage (k + j)).depth m o η)))| ≤
          |C₄| * Real.exp (-(c₄ * (m : ℝ))) := fun F hF hb => by
    have h := (H₄ T β k _ nn j o (chartBondsInBlocks (Tb.stepParameters y).side Bin) F 1 hloc₄ hLdiv hjM hZ8 hF hb).2
    filter_upwards [h] with v hv hd
    refine (hv hd).trans ?_
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  have hred := condExp_product_reduction T β (k + j) d' N (r := r) o (Tb.stepParameters y).threshold (m : ℝ)
    (|C₄| * Real.exp (-(c₄ * (m : ℝ)))) hσ64 hδ Bin g hg l e hl4
    (markedSampleLaw T β (k + j + 1) (fineSide (Tb.stepParameters y).side d' N))
    (hLaw (Tb.stepParameters y) hfit hLam T hcut hcoin β (k + j + 1) d' N)
    (hst _ _) (upperSigma_le T (k + j + 1) (fun n _ => hst _ n) d' N) hmk hcl (fun b a hb => hb1 b a hb) hBorel.2
    (fun F v => reflectedStepMean (T.stage (k + j)).toStepSetup m o (topField (Tb.stepParameters y) (k + j + 1) _ v)
      (fun η => F (imaginaryComponentsOn (chartBondsInBlocks (Tb.stepParameters y).side Bin)
        (reflectedCoordinateAt (Tb.stepParameters y).side (T.stage (k + j)).depth m o η)))) hlaw'
  refine ⟨hred.1, ?_⟩
  have hmapcl : ∀ᵐ u ∂(markedSampleLaw T β (k + j + 1 + d') N),
      Disjoint (stageState T (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u)).2.1
        (supBall o (m : ℝ)) →
      IsColdOnBall (Tb.stepParameters y).threshold
        (topField (Tb.stepParameters y) (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u)) o (m : ℝ) := by
    have h0 : ∀ᵐ v ∂((markedSampleLaw T β (k + j + 1 + d') N).map (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)),
        Disjoint (stageState T (k + j + 1) _ v).2.1 (supBall o (m : ℝ)) →
        IsColdOnBall (Tb.stepParameters y).threshold (topField (Tb.stepParameters y) (k + j + 1) _ v) o (m : ℝ) := by
      rw [hLaw (Tb.stepParameters y) hfit hLam T hcut hcoin β (k + j + 1) d' N]
      filter_upwards [hcl] with v hv hd
      exact (hv hd).1
    exact ae_of_ae_map (measurable_sampleBelow _ _ _).aemeasurable h0
  filter_upwards [hred.2, hmapcl] with u h1 h2 hd hnear
  have hcoldV := h2 hd
  have hE := h1 hd
  set V := topField (Tb.stepParameters y) (k + j + 1) _ (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u) with hV
  set ε : ℝ := s u + Real.exp (-(c_H * ρ₀)) with hεdef
  have hε : 0 ≤ ε := add_nonneg (hs0 u) (Real.exp_pos _).le
  let W : Fin r → Fin r → ℝ := fun i i' =>
    if e i = e i' then
      stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j)
        (fineSide (Tb.stepParameters y).side d' N) (l i) (l i')
    else 0
  have hH : ∀ i i', _ := fun i i' => HH T β k _ nn j o V (g u) (s u) (l i) (l i') (e i) (e i') hlocH hj (hs0 u) hcoldV
    hnear (fun b hb => ⟨hl2 i b hb, hl2 i' b hb⟩)
  have hab : ∀ i i', |C_H| * (∑ b, |l i b|) * (∑ b, |l i' b|) ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|) := fun i i' =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hCab : ∀ i i', C_H * (∑ b, |l i b|) * (∑ b, |l i' b|) ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|) := fun i i' =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans (hab i i')
  have hW : ∀ i i', |W i i'| ≤ K * (∑ b, |l i b|) * (∑ b, |l i' b|) := fun i i' => by
    simp only [W]
    split_ifs
    · exact (hH i i').2.1.trans (hCab i i')
    · rw [abs_zero]
      have := Finset.sum_nonneg (s := Finset.univ) fun b _ => abs_nonneg (l i b)
      have := Finset.sum_nonneg (s := Finset.univ) fun b _ => abs_nonneg (l i' b)
      positivity
  have hts := reflected_moment_bound_at_stage Tb y T (k + j) m hm0 h2m hn₀m o V (g u) Bin Bbig l e hD hyC hfit hOT
    hcoldV hl2 hgeo hCold hRB hMir.2.1 c₁ nss₁ hT₁ hA₁ c₂ nss₂ hT₂ hA₃ c₂ nss₂ hT₂ C₂ HL K ε hK1 hε W hW
    (fun i i' => (hH i i').2.2.trans (hCab i i'))
    (fun i i' => (hH i i').1.trans (mul_le_mul_of_nonneg_right (hCab i i') (add_nonneg (hs0 u) (Real.exp_pos _).le)))
  have hxt : (T.stage (k + j)).coupling = flowCouplings (Tb.stepParameters y) β (k + j) := hcp
  rw [hxt] at hts
  have hxt0 : 0 < flowCouplings (Tb.stepParameters y) β (k + j) := by linarith
  have hz0 : -(r : ℝ) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    linarith
  have hz1 : -((r : ℝ) + 1) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    linarith
  have hpw : ∀ z : ℝ, z ≤ 0 → flowCouplings (Tb.stepParameters y) β (k + j) ^ z ≤ (1 / 2 : ℝ) ^ z * x ^ z :=
      fun z hz => by
    have e1 : x / 2 = (1 / 2 : ℝ) * x := by ring
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x / 2) hxt2 hz
    rwa [e1, Real.mul_rpow (by norm_num) hxpos.le] at h1
  set h : ℝ := (1 / 2 : ℝ) ^ j with hhdef
  have hh0 : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha0 : 0 ≤ ∏ i, ∑ b, |l i b| := Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : ∏ i, ∑ b, |l i b| ≤ 4 ^ r * h := by
    have h1 : ∏ i, ∑ b, |l i b| ≤ ∏ _i : Fin r, 4 * h :=
      Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) fun i _ => hl1 i
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_of_le_one hh0 hh1 (by omega)
  have hec4 : Real.exp (-(c₄ * (m : ℝ))) ≤ Real.exp (-(cc * ρ₀)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact mul_le_mul (min_le_left _ _) hρm hρ0 hc₄.le
  have hecH : Real.exp (-(c_H * ρ₀)) ≤ Real.exp (-(cc * ρ₀)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hρ0
  have hQ : (12 ^ r * |C₄| + A₀ * D * 4 ^ r) * Real.exp (-(cc * ρ₀)) ≤ Real.exp (-(cc / 2 * ρ₀)) := by
    have h1 : Q₁ ≤ cc / 2 * ρ₀ := by
      have := mul_le_mul_of_nonneg_left hρQ (by positivity : 0 ≤ cc / 2)
      have e2 : cc / 2 * (2 * Q₁ / cc) = Q₁ := by field_simp
      linarith
    have h2 : Q₁ ≤ Real.exp (cc / 2 * ρ₀) := by
      have := Real.add_one_le_exp (cc / 2 * ρ₀)
      linarith
    have h3 : Real.exp (-(cc / 2 * ρ₀)) = Real.exp (cc / 2 * ρ₀) * Real.exp (-(cc * ρ₀)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hX₀ : x ^ (-(r : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 hz0
  exact abs_sub_le_of_chain (S := _) hE hts (hpw _ hz0) (hpw _ hz1) (Real.rpow_pos_of_pos hxt0 _).le
    (Real.rpow_pos_of_pos hxt0 _).le
    ha0 ha (Real.rpow_pos_of_pos hxpos _).le (Real.rpow_pos_of_pos hxpos _).le hX₀ hh0 hh1
    (hs0 u) hec4 hecH (Real.exp_pos _).le (abs_nonneg _) (abs_nonneg _) (by positivity) (by positivity) hD0 hA₀p.le
    hA₁p.le hQ
end Core
private theorem holdsOnParameters_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) : HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParameters_imp {P R : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P) (C : ℝ)
    (f : ∀ (T : ParameterAssignment) (y : ℝ), T.Admissible → T.ColdStepHolds → T.HoldsFrom ColdRegimeEstimatesAt →
      C ≤ T.derivBound → T.floorMin ≤ y → T.yC ≤ y →
      StepReturn.ExpansionReturnsAt (T.stepParameters y) → P T y → R T y) : HoldsOnParameterFamilies R := by
  intro a ha
  obtain ⟨L₀, r₀, C₁, p, H⟩ := hP a ha
  refine ⟨L₀, r₀, max C₁ C, p, fun L hL hLe T hTa hTL hD hCS hCH hr hC => ?_⟩
  obtain ⟨y₀, Y⟩ := H L hL hLe T hTa hTL hD hCS hCH hr ((le_max_left _ _).trans hC)
  refine ⟨max y₀ (max T.floorMin T.yC), fun y hy hR hW => f T y hD hCS hCH ((le_max_right _ _).trans hC)
    (((le_max_left _ _).trans (le_max_right _ _)).trans hy) (((le_max_right _ _).trans (le_max_right _ _)).trans hy) hR
    (Y y ((le_max_left _ _).trans hy) hR hW)⟩
end StepCurvatureMoments
open StepCurvatureMoments in
theorem stepCurvatureMoments_proof (hMk : chainMarkovBackwardsStatement)
    (hLaw : BoxMarks.lowerMarginalStatement) (hSt : StageStatesMeasurableStatement)
    (hProb : TwoPointByTotalCovarianceStatement) (hMir : reflectedFieldReadsBox)
    (hCold : mirrorOfColdBallSmallCurvatureStatement) (hRB : ColdExpansionRegular)
    (hScaleFlow : ClusterExpansionOfAStep.FlowWhereExpansionReturns) (hCar : stepLawGaugeInvariantStatement)
    (hlaw : oneStepReflectedLawStatement) (hBox : descentKeepsBallClearStatement)
    (hBor : stepDeviationMeasurableStatement) (hHess : reflectedHessianComparisonStatement) :
    stepCurvatureMomentsStatement := by
  obtain ⟨C₀, hR⟩ := hScaleFlow
  refine holdsOnParameters_imp
    (holdsOnParameters_and hlaw (holdsOnParameters_and hBox (holdsOnParameters_and hBor hHess))) C₀
    fun T y hD hCS hOn hC hy₀ hyC hRet h => ?_
  obtain ⟨a, b, c, d⟩ := h
  have hfit : (T.stepParameters y).Admissible := hD.fits y hy₀
  exact stepCurvatureMomentsAt_of T y hD hyC hy₀ hCS hOn hCar hMk hLaw hSt hProb hMir hCold hRB
    (fun β hβ => ((hR (T.stepParameters y) hfit hC hRet).2 β hβ).1) a b c d
end ResponseInTheExpansion
end YangMills.Construction
end
