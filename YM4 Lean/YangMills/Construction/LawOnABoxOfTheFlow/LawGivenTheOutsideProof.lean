import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.LawOnABoxOfTheFlow.LawGivenTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALawProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps WeightedResponses StepSettings BlockAverages
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
variable {n : ℕ} [NeZero n]
private theorem lintegral_fieldHaar_split (o : TorusSite n) (R : ℕ) {f : TorusField n → ENNReal} (hf : Measurable f) :
    ∫⁻ W, f W ∂(fieldHaar n) =
      ∫⁻ V, ∫⁻ w, f (glueField (restrictOuter o R V) w) ∂(innerHaar o R) ∂(fieldHaar n) := by
  classical
  have hpres := ClusterExpansionOfAStep.measurePreserving_field_overwrite (n := n) (bondsTouching o R)
  rw [← hpres.lintegral_comp hf]
  have hmeas : Measurable fun p : (↥(bondsTouching o R) → UnitQuaternion) × TorusField n =>
      f (fun x i => if h : (x, i) ∈ bondsTouching o R then p.1 ⟨(x, i), h⟩ else p.2 x i) :=
    hf.comp hpres.measurable
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun V => lintegral_congr fun w => ?_
  congr 1
private theorem integral_wilsonWeight_pos (β : ℝ) (m : ℕ) [NeZero m] :
    0 < ∫ W, wilsonWeight β m W ∂(fieldHaar m) := by apply _root_.YangMills.Construction.WeightedResponses.ChainLaw.integral_wilsonWeight_pos <;> assumption
set_option maxHeartbeats 1000000 in
theorem conditionalLawGivenOuter_holds (hD : StageDensity.stageStateDensityStatement) :
    conditionalLawGivenOuterStatement := by
  refine holdsAtAdmissibleParameters_mono ?_ hD
  intro Tb y hTb hd T β k n _ o R hst hco hbs
  haveI := (T.stage k).labels.sfμ
  have hexp : HullExpansion (Tb.stepParameters y) (T.stage k).depth (T.stage k).coupling
      (T.stage k).functional (T.stage k).density (T.stage k).labels
      (T.stage k).labelWeight (T.stage k).clusterFactor (T.stage k).siteDensity :=
    (hst.onFamily k le_rfl).isStep.1.2
  have hbor : ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → (T.stage k).labels.Ω) =>
      (open Classical in if IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) p.1 Y then
        (T.stage k).labelWeight n p.1 Y p.2 else 0) :=
    fun Y => (hexp.borel n hbs Y).1
  have hDm : Measurable (hullStateDensity T k o R) := by
    refine measurable_prod_sigma_of_forall fun Y => ?_
    have hj : Measurable fun p : (OuterField o R × (Y → (T.stage k).labels.Ω)) × InnerField o R =>
        (glueField p.1.1 p.2 : TorusField n) :=
      Measurable.comp (g := fun p : OuterField o R × InnerField o R => (glueField p.1 p.2 : TorusField n))
        (measurable_glueField o R) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hmap : Measurable fun p : (OuterField o R × (Y → (T.stage k).labels.Ω)) × InnerField o R =>
        ((glueField p.1.1 p.2, p.1.2) : TorusField n × (Y → (T.stage k).labels.Ω)) :=
      hj.prodMk (measurable_snd.comp measurable_fst)
    have h2 : Measurable fun p : (OuterField o R × (Y → (T.stage k).labels.Ω)) × InnerField o R =>
        (open Classical in if IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling)
            (glueField p.1.1 p.2) Y then
          (T.stage k).labelWeight n (glueField p.1.1 p.2) Y p.1.2 else 0) :=
      Measurable.comp (g := fun p : TorusField n × (Y → (T.stage k).labels.Ω) =>
        (open Classical in if IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) p.1 Y then
          (T.stage k).labelWeight n p.1 Y p.2 else 0))
        (f := fun p : (OuterField o R × (Y → (T.stage k).labels.Ω)) × InnerField o R =>
          ((glueField p.1.1 p.2, p.1.2) : TorusField n × (Y → (T.stage k).labels.Ω))) (hbor Y) hmap
    have h3 := ENNReal.measurable_ofReal.comp h2
    simp only [hullStateDensity]
    exact h3
  refine ⟨hDm, ?_⟩
  set m := fineSide (Tb.stepParameters y).side k n with hm
  refine ⟨ENNReal.ofReal (∫ W, wilsonWeight β m W ∂(fieldHaar m)), ?_, ENNReal.ofReal_ne_top, ?_⟩
  · exact (ENNReal.ofReal_pos.2 (integral_wilsonWeight_pos β m)).ne'
  intro H hH
  let G : StageState T k n → ENNReal := fun s => H ((restrictOuter o R s.1, s.2), restrictInner o R s.1)
  have hG : Measurable G :=
    hH.comp ((((measurable_restrictOuter o R).comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_restrictInner o R).comp measurable_fst))
  have h1 := hd T β k n hst hco hbs G hG
  have hout : ∀ u : MarkedSample (Tb.stepParameters y) k n,
      G (stageState T k n u) =
        H (outerData T k o R (stageState T k n u), restrictInner o R (stageState T k n u).1) :=
    fun u => rfl
  simp only [hout] at h1
  rw [h1]
  let g : ∀ Y : Finset (TorusSite n), TorusField n × (Y → (T.stage k).labels.Ω) → ENNReal := fun Y p =>
    G (p.1, ⟨Y, p.2⟩) * ENNReal.ofReal
      (open Classical in if IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) p.1 Y then
        (T.stage k).labelWeight n p.1 Y p.2 else 0)
  have hg : ∀ Y, Measurable (g Y) := fun Y =>
    (hG.comp (measurable_fst.prodMk ((measurableEmbedding_sigmaMk Y).measurable.comp measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (hbor Y))
  classical
  have hsum : ∀ W : TorusField n,
      (∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
        ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) =
      ∑ Y : Finset (TorusSite n), ∫⁻ ω, g Y (W, ω) ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ) := by
    intro W
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases h : IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W Y
    · simp only [g, if_pos h]
    · simp only [g, if_neg h, ENNReal.ofReal_zero, mul_zero, lintegral_zero]
  simp only [hsum]
  rw [lintegral_finset_sum _ fun Y _ => (hg Y).lintegral_prod_right']
  unfold outerReferenceIntegral
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [lintegral_lintegral_swap (hg Y).aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hm' : Measurable fun W => g Y (W, ω) := (hg Y).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_fieldHaar_split o R hm']
  refine lintegral_congr fun V => lintegral_congr fun w => ?_
  simp only [g, G, hullStateDensity, restrictOuter_glueField, restrictInner_glueField]
end YangMills.Construction.BoxGaussian
end
