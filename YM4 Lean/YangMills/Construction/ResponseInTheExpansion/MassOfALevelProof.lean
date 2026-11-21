import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.HaarMassOfASmallBall
import YangMills.Construction.ResponseInTheExpansion.MassOfALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields TorusFrame RenormalizationStepParameters HaarBalls BlockAverages
namespace StageMass
private def fiberMass (S : StepSetup) (n : ℕ) [NeZero n] (W : TorusField n) : ENNReal :=
  open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState S.params (clusterRange S.coupling) W),
    ∫⁻ ω, ENNReal.ofReal (S.labelWeight n W Y ω) ∂(Measure.pi fun _ : Y => S.labels.μ)
variable {S : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fiberMass
    (hexp : HullExpansion S.params S.depth S.coupling S.functional S.density S.labels S.labelWeight
      S.clusterFactor S.siteDensity)
    (hn : IsBlockTorusSide S.params n) : Measurable (fiberMass S n) := by
  classical
  have e : fiberMass S n = fun W => ∑ Y : Finset (TorusSite n), ∫⁻ ω, ENNReal.ofReal
      (if IsHullState S.params (clusterRange S.coupling) W Y then S.labelWeight n W Y ω else 0)
        ∂(Measure.pi fun _ : Y => S.labels.μ) := by
    funext W
    unfold fiberMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases h : IsHullState S.params (clusterRange S.coupling) W Y <;> simp [h]
  rw [e]
  refine Finset.measurable_fun_sum _ fun Y _ => ?_
  exact Measurable.lintegral_prod_right'
    (f := fun q : TorusField n × (Y → S.labels.Ω) => ENNReal.ofReal
      (if IsHullState S.params (clusterRange S.coupling) q.1 Y then S.labelWeight n q.1 Y q.2 else 0))
    ((hexp.borel n hn Y).1.ennreal_ofReal)
private theorem sum_integral_eq_toReal
    (hexp : HullExpansion S.params S.depth S.coupling S.functional S.density S.labels S.labelWeight
      S.clusterFactor S.siteDensity)
    (hn : IsBlockTorusSide S.params n) (W : TorusField n) (hW : fiberMass S n W ≠ ⊤) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState S.params (clusterRange S.coupling) W),
      ∫ ω, S.labelWeight n W Y ω * 1 ∂(Measure.pi fun _ : Y => S.labels.μ)) = (fiberMass S n W).toReal := by
  classical
  have hfin : ∀ Y ∈ Finset.univ.filter (IsHullState S.params (clusterRange S.coupling) W),
      ∫⁻ ω, ENNReal.ofReal (S.labelWeight n W Y ω) ∂(Measure.pi fun _ : Y => S.labels.μ) ≠ ⊤ := by
    intro Y hY h
    exact hW (top_unique (h ▸ Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
      ∫⁻ ω, ENNReal.ofReal (S.labelWeight n W Y ω) ∂(Measure.pi fun _ : Y => S.labels.μ))
      (fun _ _ => zero_le) hY))
  unfold fiberMass
  rw [ENNReal.toReal_sum hfin]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hY' : IsHullState S.params (clusterRange S.coupling) W Y := (Finset.mem_filter.mp hY).2
  have hm : Measurable fun ω : Y → S.labels.Ω => S.labelWeight n W Y ω := by
    have h1 := (hexp.borel n hn Y).1.comp (measurable_prodMk_left (x := W))
    have e : ((fun q : TorusField n × (Y → S.labels.Ω) =>
        if IsHullState S.params (clusterRange S.coupling) q.1 Y then S.labelWeight n q.1 Y q.2 else 0) ∘
          Prod.mk W) = fun ω => S.labelWeight n W Y ω := by
      funext ω
      simp [hY']
    rwa [e] at h1
  simp only [mul_one]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => hexp.nonneg n hn W Y ω hY') hm.aestronglyMeasurable
private theorem norm_plaquette_word_sub_one_le {e : ℝ} (a b c d : UnitQuaternion)
    (ha : a ∈ closedBallAtOne e) (hb : b ∈ closedBallAtOne e) (hc : c ∈ closedBallAtOne e)
    (hd : d ∈ closedBallAtOne e) : ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * e := by
  have one : ((1 : UnitQuaternion) : ℍ[ℝ]) = 1 := rfl
  have h1 : ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((1 * 1 : UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * e := by
    have := norm_mul_sub_mul_le a b 1 1
    rw [one] at this
    have ha' : ‖((a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e := ha
    have hb' : ‖((b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e := hb
    linarith
  have hinv : ∀ g : UnitQuaternion, g ∈ closedBallAtOne e →
      ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((1⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ e := by
    intro g hg
    rw [norm_inv_sub_inv, one]
    exact hg
  have h2 := norm_mul_sub_mul_le (a * b) c⁻¹ (1 * 1) 1⁻¹
  have h3 := norm_mul_sub_mul_le (a * b * c⁻¹) d⁻¹ (1 * 1 * 1⁻¹) 1⁻¹
  have h4 := hinv c hc
  have h5 := hinv d hd
  have e1 : ((1 * 1 * 1⁻¹ * 1⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by simp
  rw [e1] at h3
  linarith
abbrev _root_.YangMills.SharedProofs.p54318 := @norm_plaquette_word_sub_one_le
private theorem fieldHaar_nearOne_ne_zero (hHaar : HaarMassCubicLowerBound) {e : ℝ} (he : 0 < e)
    (he1 : e ≤ 1) :
    fieldHaar n (Set.univ.pi fun _ : TorusSite n => Set.univ.pi fun _ : Fin 4 => closedBallAtOne e) ≠ 0 := by
  obtain ⟨c, hc, hb⟩ := hHaar
  have h0 : haarUnit (closedBallAtOne e) ≠ 0 := by
    intro h
    have h1 := hb e he he1
    rw [h] at h1
    simp only [ENNReal.toReal_zero] at h1
    have : 0 < c * e ^ 3 := by positivity
    linarith
  unfold fieldHaar
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_ne_zero _ (pow_ne_zero _ h0)
private theorem totalMass_facts (hHaar : HaarMassCubicLowerBound)
    (hcold : ColdExpansion S.params S.depth S.coupling S.functional S.density)
    (hexp : HullExpansion S.params S.depth S.coupling S.functional S.density S.labels S.labelWeight
      S.clusterFactor S.siteDensity)
    (hσ : 0 < S.params.threshold) (hn : IsBlockTorusSide S.params n) (hn₀ : S.params.n₀ ≤ n) (C : ℝ)
    (hC : ∀ W : TorusField n, S.functional n W ≤ C) :
    0 < ∫⁻ W, fiberMass S n W ∂(fieldHaar n) ∧ ∫⁻ W, fiberMass S n W ∂(fieldHaar n) ≠ ⊤ ∧
      ∀ W : TorusField n, fiberMass S n W ≠ ⊤ := by
  have hm := measurable_fiberMass hexp hn
  have hsum : ∀ W : TorusField n, fiberMass S n W = ENNReal.ofReal (S.functional n W) :=
    fun W => hexp.sum n hn W
  have hle : ∀ W : TorusField n, fiberMass S n W ≤ ENNReal.ofReal C := fun W => by
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal (hC W)
  refine ⟨?_, ?_, fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle W)⟩
  · rw [lintegral_pos_iff_support hm]
    set e : ℝ := min (S.params.threshold / 5) 1 with he
    have he0 : 0 < e := lt_min (by positivity) one_pos
    have he1 : e ≤ 1 := min_le_right _ _
    have he5 : 5 * e ≤ S.params.threshold := by
      have : e ≤ S.params.threshold / 5 := min_le_left _ _
      linarith
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr (fieldHaar_nearOne_ne_zero (n := n) hHaar he0 he1))
      (measure_mono ?_)
    intro W hW
    have hW' : ∀ x i, W x i ∈ closedBallAtOne e := fun x i =>
      (Set.mem_univ_pi.mp ((Set.mem_univ_pi.mp hW) x)) i
    have hWcold : IsCold S.params.threshold W := fun z μ ν _ => by
      have h1 : curvature W z μ ν ≤ 4 * e :=
        norm_plaquette_word_sub_one_le _ _ _ _ (hW' _ _) (hW' _ _) (hW' _ _) (hW' _ _)
      linarith
    have hpos := hcold.positive n hn₀ W hWcold
    rw [Function.mem_support, hsum]
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top ?_
    calc ∫⁻ W, fiberMass S n W ∂(fieldHaar n) ≤ ∫⁻ _, ENNReal.ofReal C ∂(fieldHaar n) := lintegral_mono hle
      _ = ENNReal.ofReal C := by simp
private theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem le_clusterRange {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
end StageMass
open StageMass in
theorem stageMassPositive_holds (hBasic : ExpansionBasicBounds) (hHaar : HaarMassCubicLowerBound) :
    stageMassPositive := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ _ => ?_⟩
  refine ⟨max T.floorMin (((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100), fun y hy S A _ hA n _ hn => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hadm0 := hT.fits y hy₀
  have hpar : S.params = T.stepParameters y := hA.onFamily.params_eq
  have hadm : S.params.Admissible := hpar ▸ hadm0
  have hxy : y ≤ S.coupling := hA.onFamily.le_coupling
  have hy1 : 1 ≤ y := hadm0.y₁_ge
  have hx0 : 0 < S.coupling := by linarith
  have hfl : 4 * T.n₀ + 2 ^ 16 ≤ clusterRange y := le_clusterRange ((le_max_right _ _).trans hy)
  have hrange : 4 * S.params.n₀ + 2 ^ 16 ≤ clusterRange S.coupling := by
    rw [hpar]
    exact hfl.trans (clusterRange_mono (by linarith) hxy)
  obtain ⟨hcold, hexp⟩ := hA.onFamily.isStep.1
  have hn₀ : S.params.n₀ ≤ n := by
    have h1 : S.params.side * S.params.n₀ ≤ n := hn.2
    have h2 : 1 ≤ S.params.side := le_trans (by norm_num) hadm.L_ge
    nlinarith
  obtain ⟨-, -, hbound⟩ := hBasic S.params S.depth S.coupling S.functional S.density S.labels S.labelWeight
    S.clusterFactor S.siteDensity hadm hadm.E_ge hx0 hrange hcold hexp
  obtain ⟨hpos, hfin, hW⟩ :=
    totalMass_facts (S := S) (n := n) hHaar hcold hexp hadm.σ_pos hn hn₀ _ (hbound n hn)
  have hm := measurable_fiberMass hexp hn
  have hI : stateIntegral S n (fun _ _ _ => 1) = (∫⁻ W, fiberMass S n W ∂(fieldHaar n)).toReal := by
    unfold stateIntegral
    rw [← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall fun W => (hW W).lt_top)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun W => sum_integral_eq_toReal hexp hn W (hW W))
  have hM : stateLIntegral S n (fun _ _ _ => 1) = ∫⁻ W, fiberMass S n W ∂(fieldHaar n) := by
    unfold stateLIntegral fiberMass
    simp only [mul_one]
  rw [hI, hM]
  exact ⟨ENNReal.toReal_pos hpos.ne' hfin, ENNReal.ofReal_toReal hfin⟩
end YangMills.Construction.ResponseInTheExpansion
end
