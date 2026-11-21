import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsInMass
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHull
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanOfABondIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open StepSettings StepCosts TorusLumps TorusFields
namespace ClusterExpansionOfAStep
namespace SmoothOffHull
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
theorem baseLaw_nonneg_of_field (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by
  unfold baseLaw
  split_ifs
  · positivity
  · exact le_rfl
theorem measurable_baseLaw_of_kernelBorel (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
end SmoothOffHull
open SmoothOffHull in
theorem coarseWeight_smooth (hAd : AdmissionReadsHull)
    (hC : KernelMassCumulantBound) (hK : BondKernelBorel)
    (hM : MeasurableContourMeanStatement) : coarseWeightSmoothStatement := by
  intro R hR hs hCd hx' hx n _ hB V Y ω hull hpos k c X hfar
  classical
  let q : CoarseState R n := ⟨Y, ω⟩
  obtain ⟨adm, -, hmeas, hform⟩ := hAd R hR n hB V q hull
  letI : MeasurableSpace (BaseChoice R.params.side n) := ⊤
  haveI : DiscreteMeasurableSpace (BaseChoice R.params.side n) := ⟨fun _ => trivial⟩
  let μ : Measure (TorusField (n * R.params.side) × BaseChoice R.params.side n) :=
    (fieldHaar (n * R.params.side)).prod Measure.count
  let Wf : TorusField (n * R.params.side) × BaseChoice R.params.side n →
      (stepBlockFrame R.params.side n).GaugeField 0 := fun ξ =>
    readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks ξ.1)
  let bf : TorusField (n * R.params.side) × BaseChoice R.params.side n → BaseChoice R.params.side n :=
    fun ξ => ξ.2
  let I : Finset (TorusSite (n * R.params.side)) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) → ENNReal := fun Yt b W =>
    ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, adm Yt b W ν *
      ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν))
      ∂(Measure.pi fun _ => R.labels.μ)
  let ρ : TorusField (n * R.params.side) × BaseChoice R.params.side n → ENNReal := fun ξ =>
    (∑ Yt, I Yt ξ.2 ξ.1) * ENNReal.ofReal (baseLaw (R := R) (q.fieldWithStoredLinks ξ.1) ξ.2)
  have hI : ∀ Yt b, Measurable (I Yt b) := fun Yt b => (hmeas Yt b).lintegral_prod_right'
  have hlaw : ∀ b, Measurable fun W : TorusField (n * R.params.side) =>
      baseLaw (R := R) (q.fieldWithStoredLinks W) b := fun b =>
    (measurable_baseLaw_of_kernelBorel hK b).comp (measurable_fieldWithStoredLinks q)
  have hρ : Measurable ρ := by
    refine measurable_from_prod_countable_left fun b => ?_
    exact (Finset.measurable_fun_sum _ fun Yt _ => hI Yt b).mul (hlaw b).ennreal_ofReal
  have hk : ∀ (V' : TorusField n) (c' : (stepBlockFrame R.params.side n).Cell × Fin 4), Measurable fun ξ =>
      bondKernel R.params R.coupling (Wf ξ) (readAtLevel (stepBlockFrame R.params.side n) 1 V') (bf ξ) c' := by
    intro V' c'
    obtain ⟨_, _, _, _, _, hkb, _⟩ := hK R.params R.coupling n
    refine measurable_from_prod_countable_left fun b => ?_
    have h1 : Measurable fun W : TorusField (n * R.params.side) => (q.fieldWithStoredLinks W, V') :=
      (measurable_fieldWithStoredLinks q).prodMk measurable_const
    have h2 := (hkb b c').comp h1
    show Measurable fun W : TorusField (n * R.params.side) => bondKernel R.params R.coupling
      (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W))
      (readAtLevel (stepBlockFrame R.params.side n) 1 V') b c'
    exact h2
  have hm : ∀ c' : (stepBlockFrame R.params.side n).Cell × Fin 4, MeasurableQuaternion fun ξ =>
      LumpContours.contourMean R.params.baseDepth
        (LumpContours.hotLumps R.params.grid R.params.threshold
          (levelSites (stepBlockFrame R.params.side n) 0) (Wf ξ)) (bf ξ) (Wf ξ) c' := by
    intro c'
    have hcomp : ∀ f : ℍ[ℝ] → ℝ, Continuous f →
        Measurable fun ξ : TorusField (n * R.params.side) × BaseChoice R.params.side n =>
        f (LumpContours.contourMean R.params.baseDepth
          (LumpContours.hotLumps R.params.grid R.params.threshold
            (levelSites (stepBlockFrame R.params.side n) 0) (Wf ξ)) (bf ξ) (Wf ξ) c') := by
      intro f hf
      refine measurable_from_prod_countable_left fun b => ?_
      have h2 := (hM R.params n b c' f hf).comp (measurable_fieldWithStoredLinks q)
      show Measurable fun W : TorusField (n * R.params.side) => f (LumpContours.contourMean R.params.baseDepth
        (LumpContours.hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
          (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W))) b
        (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W)) c')
      exact h2
    exact ⟨hcomp _ Quaternion.continuous_re, hcomp _ Quaternion.continuous_imI,
      hcomp _ Quaternion.continuous_imJ, hcomp _ Quaternion.continuous_imK⟩
  have hmass : ∀ V' : TorusField n, hotCoreSites R V' = hotCoreSites R V →
      (∀ c' : TorusBond n, (c'.1 ∈ q.1 ∨ c'.1 + unitStep n c'.2 ∈ q.1) → V' c'.1 c'.2 = V c'.1 c'.2) →
      coarseWeightExpansion R n V' Y ω = kernelMass R.params R.coupling μ ρ Wf bf V' := by
    intro V' h1 h2
    have hrow : coarseWeightExpansion R n V' Y ω = (coarseStateMass R (hotCoreSites R V') V' q).toReal := by
      unfold coarseWeightExpansion
      rw [dif_neg (NeZero.ne n)]
      rfl
    rw [hrow, hform V' h1 h2]
    unfold kernelMass
    congr 1
    let Kf : TorusField (n * R.params.side) × BaseChoice R.params.side n → ℝ := fun ξ =>
      ∏ c' : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (Wf ξ) (readAtLevel (stepBlockFrame R.params.side n) 1 V') (bf ξ) c'
    have hK0 : ∀ ξ, 0 ≤ Kf ξ := fun ξ => Finset.prod_nonneg fun c' _ =>
      div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
    have hKm : Measurable Kf := Finset.measurable_fun_prod _ fun c' _ => hk V' c'
    have hterm : ∀ Yt b W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, adm Yt b W ν *
        ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) *
          baseLaw (R := R) (q.fieldWithStoredLinks W) b * Kf (W, b)) ∂(Measure.pi fun _ => R.labels.μ) =
        I Yt b W * (ENNReal.ofReal (baseLaw (R := R) (q.fieldWithStoredLinks W) b) *
          ENNReal.ofReal (Kf (W, b))) := by
      intro Yt b W
      have hl := baseLaw_nonneg_of_field (R := R) (q.fieldWithStoredLinks W) b
      have e : ∀ ν : q.unlabelled Yt → R.labels.Ω, adm Yt b W ν *
          ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) *
            baseLaw (R := R) (q.fieldWithStoredLinks W) b * Kf (W, b)) =
          adm Yt b W ν * ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt
            (q.fillLabels Yt ν)) *
            (ENNReal.ofReal (baseLaw (R := R) (q.fieldWithStoredLinks W) b) * ENNReal.ofReal (Kf (W, b))) := by
        intro ν
        rw [mul_assoc (R.labelWeight _ _ _ _), ENNReal.ofReal_mul' (mul_nonneg hl (hK0 _)),
          ENNReal.ofReal_mul hl, mul_assoc]
      simp only [e]
      exact lintegral_mul_const _ ((hmeas Yt b).comp measurable_prodMk_left)
    have hlhs : ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, adm Yt b W ν *
          ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) *
            baseLaw (R := R) (q.fieldWithStoredLinks W) b * Kf (W, b))
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        ∑ b : BaseChoice R.params.side n,
          ∫⁻ W, ρ (W, b) * ENNReal.ofReal (Kf (W, b)) ∂(fieldHaar (n * R.params.side)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hmK : ∀ Yt, Measurable fun W : TorusField (n * R.params.side) => I Yt b W *
          (ENNReal.ofReal (baseLaw (R := R) (q.fieldWithStoredLinks W) b) * ENNReal.ofReal (Kf (W, b))) :=
        fun Yt => (hI Yt b).mul ((hlaw b).ennreal_ofReal.mul
          (hKm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal)
      simp only [hterm]
      rw [← lintegral_finset_sum _ fun Yt _ => hmK Yt]
      refine lintegral_congr fun W => ?_
      simp only [ρ]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun Yt _ => ?_
      rw [mul_assoc]
    have hrhs : ∫⁻ ξ, ρ ξ * ENNReal.ofReal (Kf ξ) ∂μ =
        ∑ b : BaseChoice R.params.side n,
          ∫⁻ W, ρ (W, b) * ENNReal.ofReal (Kf (W, b)) ∂(fieldHaar (n * R.params.side)) := by
      have hmeasF : Measurable fun ξ => ρ ξ * ENNReal.ofReal (Kf ξ) := hρ.mul hKm.ennreal_ofReal
      rw [lintegral_prod _ hmeasF.aemeasurable]
      simp only [lintegral_count, tsum_fintype]
      rw [lintegral_finset_sum]
      intro b _
      exact hmeasF.comp (measurable_id.prodMk measurable_const)
    exact hlhs.trans hrhs.symm
  have hfit : R.params.Admissible := hR.admissible
  have hLn : R.params.side ∣ n := hB.1
  have hr1 : 1 ≤ R.nextRange := le_trans (by norm_num) hR.nextRange_ge
  have hr2 : 2 ≤ R.nextRange := le_trans (by norm_num) hR.nextRange_ge
  have hsub : torusHotSites R.params V ⊆ Y := fun z hz => hull.1 (subset_thickening_self _ _ hz)
  have hev := eventually_torusHotLumps_perturb_eq (r := R.nextRange) hfit hLn hr1 c X
    fun l z hz => hfar l z (hsub hz)
  have hoff : ∀ (σ : Fin k → ℝ) (c' : TorusBond n), (c'.1 ∈ q.1 ∨ c'.1 + unitStep n c'.2 ∈ q.1) →
      perturb c X σ V c'.1 c'.2 = V c'.1 c'.2 := by
    intro σ c' hc'
    refine perturb_apply_of_ne c X σ V c' fun l hl => ?_
    rcases hc' with h1 | h1
    · have h2 := hfar l _ h1
      rw [hl, supDist_self] at h2
      omega
    · have h2 := hfar l _ h1
      have h3 : supDist (c l).1 (c'.1 + unitStep n c'.2) ≤ 1 := by
        rw [hl]
        have : (unitStep n c'.2 : TorusSite n) = siteOfInt (Pi.single c'.2 1) := by
          funext i
          simp [unitStep, siteOfInt, Pi.single_apply]
        rw [this]
        refine supDist_add_siteOfInt_le _ _ 1 fun i => ?_
        simp only [Pi.single_apply]
        split_ifs <;> simp
      omega
  have hEq : (fun σ : Fin k → ℝ => coarseWeightExpansion R n (perturb c X σ V) Y ω) =ᶠ[nhds 0]
      fun σ => kernelMass R.params R.coupling μ ρ Wf bf (perturb c X σ V) := by
    filter_upwards [hev] with σ hσ
    refine hmass _ ?_ (hoff σ)
    simp only [hotCoreSites, torusHotSites, hσ]
  have hV : coarseWeightExpansion R n V Y ω = kernelMass R.params R.coupling μ ρ Wf bf V :=
    hmass V rfl fun _ _ => rfl
  obtain ⟨hsm, hbd⟩ := hC R.params R.coupling n _ μ ρ Wf bf V hs hρ hm hk (hV ▸ hpos) k c X
  refine ⟨(hsm.contDiffAt.of_le ENat.LEInfty.out).congr_of_eventuallyEq hEq, fun h1 h3 hX => ?_⟩
  have hlog : (fun σ : Fin k → ℝ => Real.log (coarseWeightExpansion R n (perturb c X σ V) Y ω)) =ᶠ[nhds 0]
      fun σ => Real.log (kernelMass R.params R.coupling μ ρ Wf bf (perturb c X σ V)) :=
    hEq.fun_comp Real.log
  have hval : mixedDeriv (fun V' => Real.log (coarseWeightExpansion R n V' Y ω)) V c X =
      mixedDeriv (fun V' => Real.log (kernelMass R.params R.coupling μ ρ Wf bf V')) V c X := by
    unfold mixedDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hlog k).eq_of_nhds]
  rw [hval]
  refine (hbd h1 h3 hX).trans (pow_le_pow_left₀ (by linarith) ?_ k)
  have ha : 1 ≤ R.params.coupling := hfit.a_ge
  calc 32 * (R.params.coupling * R.coupling) ≤ 32 * (R.params.coupling * (1.01 * R.nextCoupling)) := by gcongr
    _ ≤ 2 ^ 6 * (R.params.coupling + 1) * R.nextCoupling := by
      nlinarith [mul_pos (lt_of_lt_of_le one_pos ha) hx']
    _ ≤ R.params.derivBound * R.nextCoupling := by gcongr
end ClusterExpansionOfAStep
end YangMills.Construction
end
