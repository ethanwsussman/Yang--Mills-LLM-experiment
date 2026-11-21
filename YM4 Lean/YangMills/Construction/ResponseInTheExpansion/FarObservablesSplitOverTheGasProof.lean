import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGasProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizesProof
import YangMills.Construction.ResponseInTheExpansion.CovarianceByTwoTilts
import YangMills.Construction.ResponseInTheExpansion.FarMeanUnderATilt
import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitOverTheGas
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableAtOneLevel
import YangMills.Construction.ResponseInTheExpansion.TwoTiltsOfFarObservables
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusLumps TorusFields WeightedResponses FreeEnergies BlockAverages
namespace ResponseInTheExpansion
namespace SeparatedProductOverGas
set_option linter.unusedSectionVars false
section Numbers
private theorem abs_integral_prod_sub_prod_le {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω) (u : ι → Ω → ℝ) (I : Finset ι)
    (Mp : ι → ℝ) {a ex : ℝ} (ha : 0 ≤ a) (hex : 0 ≤ ex) (hM : ∀ i ∈ I, 0 ≤ Mp i)
    (hmean : ∀ i ∈ I, |∫ σ, u i σ ∂μ| ≤ Real.exp ex * Mp i)
    (hcov : ∀ i ∈ I, ∀ J, J ⊆ I → i ∉ J → J.Nonempty →
      |∫ σ, ∏ j ∈ insert i J, u j σ ∂μ - (∫ σ, u i σ ∂μ) * ∫ σ, ∏ j ∈ J, u j σ ∂μ| ≤
        a * J.card * Real.exp (J.card * ex) * ∏ j ∈ insert i J, Mp j) :
    ∀ J, J ⊆ I → J.Nonempty →
      |∫ σ, ∏ j ∈ J, u j σ ∂μ - ∏ j ∈ J, ∫ σ, u j σ ∂μ| ≤
        a * (J.card : ℝ) ^ 2 * Real.exp (J.card * ex) * ∏ j ∈ J, Mp j := by
  intro J
  induction J using Finset.induction_on with
  | empty => exact fun _ hne => absurd hne (by simp)
  | insert i J hi ih =>
    intro hsub _
    have hiI : i ∈ I := hsub (Finset.mem_insert_self i J)
    have hJI : J ⊆ I := fun j hj => hsub (Finset.mem_insert_of_mem hj)
    have hP0 : 0 ≤ ∏ j ∈ J, Mp j := Finset.prod_nonneg fun j hj => hM j (hJI hj)
    have hMi := hM i hiI
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      simp only [insert_empty_eq, Finset.prod_singleton, sub_self, abs_zero]
      positivity
    · have h1 := hcov i hiI J hJI hi hJ
      have h2 := ih hJI hJ
      have h3 := hmean i hiI
      have e3 : ∏ j ∈ insert i J, ∫ σ, u j σ ∂μ = (∫ σ, u i σ ∂μ) * ∏ j ∈ J, ∫ σ, u j σ ∂μ := Finset.prod_insert hi
      have e4 : ∏ j ∈ insert i J, Mp j = Mp i * ∏ j ∈ J, Mp j := Finset.prod_insert hi
      rw [e3, e4, Finset.card_insert_of_notMem hi]
      rw [e4] at h1
      push_cast
      set x := ∫ σ, ∏ j ∈ insert i J, u j σ ∂μ with hx
      set m := ∫ σ, u i σ ∂μ with hm
      set yy := ∫ σ, ∏ j ∈ J, u j σ ∂μ with hyy
      set Pp := ∏ j ∈ J, ∫ σ, u j σ ∂μ with hPp
      set Pi := ∏ j ∈ J, Mp j with hPi
      set c : ℝ := (J.card : ℝ) with hc
      have hc0 : 0 ≤ c := Nat.cast_nonneg _
      set E := Real.exp (c * ex) with hE
      set F := Real.exp ex with hF
      have hE0 : 0 < E := Real.exp_pos _
      have hF1 : 1 ≤ F := Real.one_le_exp hex
      have e5 : Real.exp ((c + 1) * ex) = E * F := by
        rw [hE, hF, ← Real.exp_add]
        congr 1
        ring
      rw [e5]
      have hW : 0 ≤ a * E * Mp i * Pi := by positivity
      have k : 0 ≤ a * E * Mp i * Pi * (F * (2 * c + 1) - c) :=
        mul_nonneg hW (by nlinarith)
      calc |x - m * Pp| = |(x - m * yy) + m * (yy - Pp)| := by
            congr 1
            ring
        _ ≤ |x - m * yy| + |m| * |yy - Pp| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
        _ ≤ a * c * E * (Mp i * Pi) + (F * Mp i) * (a * c ^ 2 * E * Pi) :=
            add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) (by positivity))
        _ ≤ a * (c + 1) ^ 2 * (E * F) * (Mp i * Pi) := by
            have e6 : a * (c + 1) ^ 2 * (E * F) * (Mp i * Pi) -
                (a * c * E * (Mp i * Pi) + (F * Mp i) * (a * c ^ 2 * E * Pi)) =
                a * E * Mp i * Pi * (F * (2 * c + 1) - c) := by ring
            linarith
private theorem covariance_arith {X U d₁ d₂ Δ P : ℝ} (hb : X ≤ 3 * U * (d₁ + d₂)) (h1 : d₁ ≤ Δ) (h2 : d₂ ≤ Δ)
    (hs : 0 ≤ d₁ + d₂) (hU0 : 0 ≤ U) (hU : U ≤ P) : X ≤ 3 * P * (Δ + Δ) := by
  have h3 : 3 * U * (d₁ + d₂) ≤ 3 * U * (Δ + Δ) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  have h4 : 3 * U * (Δ + Δ) ≤ 3 * P * (Δ + Δ) :=
    mul_le_mul_of_nonneg_right (by linarith) (hs.trans (add_le_add h1 h2))
  linarith
end Numbers
section Scores
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R} {G : GasGround R n}
private theorem siteScore_eq {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) (y : TorusSite (n * R.params.side)) :
    siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y =
      recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i) := by apply _root_.YangMills.SharedProofs.p55158 <;> assumption
private theorem spinScore_eq {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) (S : Finset (TorusSite (n * R.params.side))) :
    spinScore A G S σ = gasMeanSiteScore A G S σ := by
  unfold spinScore gasMeanSiteScore meanSiteScore
  congr 2
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [siteScore_eq ha y]
  rfl
private theorem one_le_spinScore (hs : ∀ w, 0 ≤ A.score w) (S : Finset (TorusSite (n * R.params.side))) (σ : G.Config) :
    1 ≤ spinScore A G S σ := by
  unfold spinScore
  have : 0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, (recordedSiteScore A G y + ∑ i, spinLabelScore A.score G i y (σ i)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => add_nonneg (siteScore_nonneg hs _ _ _)
      (Finset.sum_nonneg fun i _ => spinSiteScore_nonneg (A := A) (G := G) hs i y _))
  linarith
private theorem measurable_spinScore (hb : Measurable A.score) (S : Finset (TorusSite (n * R.params.side))) :
    Measurable (spinScore A G S) := by
  unfold spinScore
  refine measurable_const.add (Measurable.const_mul (Finset.measurable_fun_sum _ fun y _ => ?_) _)
  exact measurable_const.add (Finset.measurable_fun_sum _ fun i _ =>
    (measurable_spinSiteScore (A := A) (G := G) hb i y).comp (measurable_pi_apply i))
private theorem parentBlock_mem_upperSites (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    {y : TorusSite (n * R.params.side)} (hy : y ∈ lowerSites f) :
    parentBlock R.params.side y ∈ upperSites f := by
  classical
  rw [← parentBlocks_lowerSites f]
  exact Finset.mem_image_of_mem _ hy
private theorem card_upperSites_le (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    (upperSites f).card ≤ (lowerSites f).card := by apply _root_.YangMills.SharedProofs.p7582 <;> assumption
private theorem card_lowerSites_pos {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (h : (upperSites f).Nonempty) :
    0 < (lowerSites f).card :=
  lt_of_lt_of_le (Finset.card_pos.mpr h) (card_upperSites_le f)
end Scores
section Data
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R} {G : GasGround R n} {ι : Type} {I J : Finset ι}
  {f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} {ex Cc E6 : ℝ} {i : ι}
private structure SeparatedData (A : ResponseSetup R) (G : GasGround R n) (I : Finset ι)
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (ex Cc E6 : ℝ) : Prop where
  prob : IsProbabilityMeasure (G.gibbsLaw ∅)
  adm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ
  score_nonneg : ∀ w, 0 ≤ A.score w
  score_borel : Measurable A.score
  c₀ : 1 ≤ A.responseParams.C₀
  nonempty : ∀ i ∈ I, (upperSites (f i)).Nonempty
  meas : ∀ i ∈ I, (open Classical in Measurable fun σ : G.Config =>
    if G.pairConstraint.IsAdmissible σ then gasSupportMean A G (f i) σ else 0)
  le : ∀ i ∈ I, ∀ σ, G.pairConstraint.IsAdmissible σ →
    |gasSupportMean A G (f i) σ| ≤ 4 * lowerSizeConst A (f i) * spinScore A G (lowerSites (f i)) σ
  scores : ∀ J, J ⊆ I → Integrable (fun σ => ∏ j ∈ J, gasMeanSiteScore A G (lowerSites (f j)) σ) (G.gibbsLaw ∅) ∧
    G.expectation ∅ (fun σ => ∏ j ∈ J, gasMeanSiteScore A G (lowerSites (f j)) σ) ≤
      Real.exp (J.card * ex) * ∏ j ∈ J,
        meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f j)) G.state.1 G.state.2
  cov : ∀ mm Yy Yp : G.Config → ℝ,
    Measurable Yy → Measurable Yp → (∀ σ, G.pairConstraint.IsAdmissible σ → 1 ≤ Yp σ ∧ |Yy σ| ≤ Yp σ) →
    Integrable mm (G.gibbsLaw ∅) → Integrable Yp (G.gibbsLaw ∅) → Integrable (fun σ => mm σ * Yp σ) (G.gibbsLaw ∅) →
    Integrable (fun σ => mm σ * Yy σ) (G.gibbsLaw ∅) ∧ Integrable Yy (G.gibbsLaw ∅) ∧
    Integrable mm (tiltedGibbsLaw G fun σ => 2 * Yp σ + Yy σ) ∧ Integrable mm (tiltedGibbsLaw G fun σ => 2 * Yp σ) ∧
    |G.expectation ∅ (fun σ => mm σ * Yy σ) - G.expectation ∅ mm * G.expectation ∅ Yy| ≤
      3 * G.expectation ∅ Yp * (|∫ σ, mm σ ∂(tiltedGibbsLaw G fun σ => 2 * Yp σ + Yy σ) - G.expectation ∅ mm| +
        |∫ σ, mm σ ∂(tiltedGibbsLaw G fun σ => 2 * Yp σ) - G.expectation ∅ mm|)
  far : ∀ i ∈ I, ∀ J, J ⊆ I → i ∉ J → J.Nonempty → ∀ Yt : G.Config → ℝ,
    (Yt = (fun σ => 2 * gasMajorantProduct A G f J σ + gasMeanProduct A G f J σ) ∨
      Yt = fun σ => 2 * gasMajorantProduct A G f J σ) →
    |∫ σ, gasSupportMean A G (f i) σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean A G (f i))| ≤
      Cc * (J.card : ℝ) * ((unionUpperSites f J).card : ℝ) * lowerSizeConst A (f i) *
        meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f i)) G.state.1 G.state.2 * E6
private theorem SeparatedData.lowerSizeConst_nonneg (h : SeparatedData A G I f ex Cc E6) (j : ι) : 0 ≤ lowerSizeConst A (f j) := by
  have h3 := h.c₀
  unfold lowerSizeConst
  have : 0 ≤ A.responseParams.C₀ := by linarith
  positivity
private theorem SeparatedData.one_le_factor (h : SeparatedData A G I f ex Cc E6) {j : ι} (hj : j ∈ I) (σ : G.Config) :
    1 ≤ 4 * lowerSizeConst A (f j) * spinScore A G (lowerSites (f j)) σ := by
  have h1 := one_le_spinScore (G := G) h.score_nonneg (lowerSites (f j)) σ
  have h2 : (1 : ℝ) ≤ ((lowerSites (f j)).card : ℝ) := by exact_mod_cast card_lowerSites_pos (h.nonempty j hj)
  have h3 := h.c₀
  have h4 : 1 ≤ lowerSizeConst A (f j) := by
    unfold lowerSizeConst
    nlinarith
  nlinarith
private theorem SeparatedData.one_le_majorant (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) (σ : G.Config) :
    1 ≤ gasMajorantProduct A G f J σ := by
  unfold gasMajorantProduct
  calc (1 : ℝ) = ∏ _j ∈ J, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun j hj => h.one_le_factor (hJ hj) σ
private theorem SeparatedData.measurable_majorant (h : SeparatedData A G I f ex Cc E6) :
    Measurable (gasMajorantProduct A G f J) := by
  unfold gasMajorantProduct
  exact Finset.measurable_fun_prod _ fun j _ => (measurable_spinScore h.score_borel _).const_mul _
private theorem SeparatedData.measurable_product (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) :
    Measurable (gasMeanProduct A G f J) := by
  unfold gasMeanProduct
  exact Finset.measurable_fun_prod _ fun j hj => h.meas j (hJ hj)
private theorem SeparatedData.abs_product_le (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) :
    |gasMeanProduct A G f J σ| ≤ gasMajorantProduct A G f J σ := by
  unfold gasMeanProduct gasMajorantProduct
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ?_
  rw [if_pos hσ]
  exact h.le j (hJ hj) σ hσ
private theorem SeparatedData.majorant_ae (h : SeparatedData A G I f ex Cc E6) :
    gasMajorantProduct A G f J =ᵐ[G.gibbsLaw ∅] fun σ => (∏ j ∈ J, 4 * lowerSizeConst A (f j)) *
      ∏ j ∈ J, gasMeanSiteScore A G (lowerSites (f j)) σ := by
  filter_upwards [h.adm] with σ hσ
  unfold gasMajorantProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [spinScore_eq hσ]
private theorem SeparatedData.integrable_majorant (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) :
    Integrable (gasMajorantProduct A G f J) (G.gibbsLaw ∅) :=
  ((h.scores J hJ).1.const_mul _).congr h.majorant_ae.symm
private theorem SeparatedData.expectation_majorant_le (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) :
    G.expectation ∅ (gasMajorantProduct A G f J) ≤ Real.exp (J.card * ex) * ∏ j ∈ J, upperMajorant A G (f j) := by
  have e1 : G.expectation ∅ (gasMajorantProduct A G f J) = (∏ j ∈ J, 4 * lowerSizeConst A (f j)) *
      G.expectation ∅ fun σ => ∏ j ∈ J, gasMeanSiteScore A G (lowerSites (f j)) σ := by
    unfold GasGround.expectation
    rw [integral_congr_ae h.majorant_ae, integral_const_mul]
  have hK : 0 ≤ ∏ j ∈ J, 4 * lowerSizeConst A (f j) := Finset.prod_nonneg fun j _ => by
    have := h.lowerSizeConst_nonneg j
    positivity
  rw [e1]
  calc _ ≤ (∏ j ∈ J, 4 * lowerSizeConst A (f j)) * (Real.exp (J.card * ex) *
        ∏ j ∈ J, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f j)) G.state.1 G.state.2) :=
        mul_le_mul_of_nonneg_left (h.scores J hJ).2 hK
    _ = _ := by
        have e : ∏ j ∈ J, upperMajorant A G (f j) = (∏ j ∈ J, 4 * lowerSizeConst A (f j)) *
            ∏ j ∈ J, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f j)) G.state.1 G.state.2 :=
          Finset.prod_mul_distrib
        rw [e]
        ring
private theorem SeparatedData.product_ae (h : SeparatedData A G I f ex Cc E6) :
    (fun σ => ∏ j ∈ J, gasSupportMean A G (f j) σ) =ᵐ[G.gibbsLaw ∅] gasMeanProduct A G f J := by
  filter_upwards [h.adm] with σ hσ
  simp only [gasMeanProduct, if_pos hσ]
private theorem SeparatedData.integrable_product (h : SeparatedData A G I f ex Cc E6) (hJ : J ⊆ I) :
    Integrable (fun σ => ∏ j ∈ J, gasSupportMean A G (f j) σ) (G.gibbsLaw ∅) := by
  have hb : ∀ᵐ σ ∂(G.gibbsLaw ∅), ‖gasMeanProduct A G f J σ‖ ≤ gasMajorantProduct A G f J σ := by
    filter_upwards [h.adm] with σ hσ
    rw [Real.norm_eq_abs]
    exact h.abs_product_le hJ hσ
  exact ((h.integrable_majorant hJ).mono' (h.measurable_product hJ).aestronglyMeasurable hb).congr h.product_ae.symm
private theorem SeparatedData.integrable_mean (h : SeparatedData A G I f ex Cc E6) (hi : i ∈ I) :
    Integrable (gasSupportMean A G (f i)) (G.gibbsLaw ∅) := by
  classical
  have := h.integrable_product (J := {i}) (Finset.singleton_subset_iff.mpr hi)
  simpa using this
private theorem SeparatedData.abs_expectation_le (h : SeparatedData A G I f ex Cc E6) (hi : i ∈ I) :
    |G.expectation ∅ (gasSupportMean A G (f i))| ≤ Real.exp ex * upperMajorant A G (f i) := by
  classical
  have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.mpr hi
  have iU := h.integrable_majorant hsub
  have hb : ∀ᵐ σ ∂(G.gibbsLaw ∅), ‖gasSupportMean A G (f i) σ‖ ≤ gasMajorantProduct A G f {i} σ := by
    filter_upwards [h.adm] with σ hσ
    rw [Real.norm_eq_abs]
    simpa [gasMajorantProduct] using h.le i hi σ hσ
  have h1 := norm_integral_le_of_norm_le iU hb
  rw [Real.norm_eq_abs] at h1
  have h2 := h.expectation_majorant_le hsub
  simp only [Finset.card_singleton, Nat.cast_one, one_mul, Finset.prod_singleton] at h2
  exact h1.trans h2
private theorem SeparatedData.integrable_mul_majorant [DecidableEq ι] (h : SeparatedData A G I f ex Cc E6) (hi : i ∈ I)
    (hJ : J ⊆ I) (hiJ : i ∉ J) :
    Integrable (fun σ => gasSupportMean A G (f i) σ * gasMajorantProduct A G f J σ) (G.gibbsLaw ∅) := by
  have hs : insert i J ⊆ I := Finset.insert_subset hi hJ
  have iU := h.integrable_majorant hs
  refine iU.mono' ((h.integrable_mean hi).aestronglyMeasurable.mul h.measurable_majorant.aestronglyMeasurable) ?_
  filter_upwards [h.adm] with σ hσ
  have hp : 0 ≤ gasMajorantProduct A G f J σ := zero_le_one.trans (h.one_le_majorant hJ σ)
  have e : gasMajorantProduct A G f (insert i J) σ =
      (4 * lowerSizeConst A (f i) * spinScore A G (lowerSites (f i)) σ) * gasMajorantProduct A G f J σ :=
    Finset.prod_insert hiJ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, e]
  exact mul_le_mul_of_nonneg_right (h.le i hi σ hσ) hp
private theorem card_unionUpperSites_le (hJ : J ⊆ I) : ((unionUpperSites f J).card : ℝ) ≤ totalLowerSites I f := by
  classical
  unfold unionUpperSites totalLowerSites
  refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
  push_cast
  refine (Finset.sum_le_sum fun j _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hJ fun _ _ _ => Nat.cast_nonneg _)
  exact_mod_cast card_upperSites_le (f j)
private theorem SeparatedData.covariance_le [DecidableEq ι] (h : SeparatedData A G I f ex Cc E6) (hC : 0 ≤ Cc)
    (hE6 : 0 ≤ E6) (hi : i ∈ I) (hJ : J ⊆ I) (hiJ : i ∉ J) (hne : J.Nonempty) :
    |∫ σ, ∏ j ∈ insert i J, gasSupportMean A G (f j) σ ∂(G.gibbsLaw ∅) -
        (∫ σ, gasSupportMean A G (f i) σ ∂(G.gibbsLaw ∅)) * ∫ σ, ∏ j ∈ J, gasSupportMean A G (f j) σ ∂(G.gibbsLaw ∅)| ≤
      (3 / 2 * Cc * totalLowerSites I f * E6) * J.card * Real.exp (J.card * ex) *
        ∏ j ∈ insert i J, upperMajorant A G (f j) := by
  obtain ⟨-, -, -, -, hb⟩ := h.cov (gasSupportMean A G (f i)) (gasMeanProduct A G f J) (gasMajorantProduct A G f J)
    (h.measurable_product hJ) h.measurable_majorant (fun σ hσ => ⟨h.one_le_majorant hJ σ, h.abs_product_le hJ hσ⟩)
    (h.integrable_mean hi) (h.integrable_majorant hJ) (h.integrable_mul_majorant hi hJ hiJ)
  have d1 := h.far i hi J hJ hiJ hne _ (Or.inl rfl)
  have d2 := h.far i hi J hJ hiJ hne _ (Or.inr rfl)
  have e1 : ∫ σ, ∏ j ∈ insert i J, gasSupportMean A G (f j) σ ∂(G.gibbsLaw ∅) =
      G.expectation ∅ (fun σ => gasSupportMean A G (f i) σ * gasMeanProduct A G f J σ) := by
    refine integral_congr_ae ?_
    filter_upwards [h.product_ae (J := J)] with σ hσ
    rw [Finset.prod_insert hiJ, hσ]
  have e2 : ∫ σ, ∏ j ∈ J, gasSupportMean A G (f j) σ ∂(G.gibbsLaw ∅) = G.expectation ∅ (gasMeanProduct A G f J) :=
    integral_congr_ae h.product_ae
  have e3 : ∏ j ∈ insert i J, upperMajorant A G (f j) = upperMajorant A G (f i) * ∏ j ∈ J, upperMajorant A G (f j) :=
    Finset.prod_insert hiJ
  rw [e1, e2, e3]
  have hU := h.expectation_majorant_le hJ
  have hU0 : 0 ≤ G.expectation ∅ (gasMajorantProduct A G f J) :=
    integral_nonneg fun σ => zero_le_one.trans (h.one_le_majorant hJ σ)
  have hMi : 0 ≤ upperMajorant A G (f i) :=
    (mul_nonneg_iff_of_pos_left (Real.exp_pos ex)).mp ((abs_nonneg _).trans (h.abs_expectation_le hi))
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℝ, Kn = lowerSizeConst A (f i) *
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f i)) G.state.1 G.state.2 :=
    ⟨_, rfl⟩
  have hKn0 : 0 ≤ Kn := by
    have e : upperMajorant A G (f i) = 4 * Kn := by
      rw [hKn]
      simp only [upperMajorant]
      ring
    linarith
  have hc0 : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : ℝ, Δ = Cc * (J.card : ℝ) * totalLowerSites I f * Kn * E6 := ⟨_, rfl⟩
  have hΔ : Cc * (J.card : ℝ) * ((unionUpperSites f J).card : ℝ) * lowerSizeConst A (f i) *
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f i)) G.state.1 G.state.2 * E6 ≤ Δ := by
    rw [hΔd]
    have e : Cc * (J.card : ℝ) * ((unionUpperSites f J).card : ℝ) * lowerSizeConst A (f i) *
        meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f i)) G.state.1 G.state.2 * E6 =
        (Cc * (J.card : ℝ) * Kn * E6) * ((unionUpperSites f J).card : ℝ) := by
      rw [hKn]
      ring
    have e' : Cc * (J.card : ℝ) * totalLowerSites I f * Kn * E6 =
        (Cc * (J.card : ℝ) * Kn * E6) * totalLowerSites I f := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left (card_unionUpperSites_le hJ) (by positivity)
  have hE0 : 0 ≤ Real.exp (J.card * ex) * ∏ j ∈ J, upperMajorant A G (f j) := hU0.trans hU
  refine (covariance_arith hb (d1.trans hΔ) (d2.trans hΔ) (add_nonneg (abs_nonneg _) (abs_nonneg _)) hU0 hU).trans
    (le_of_eq ?_)
  have e : upperMajorant A G (f i) = 4 * Kn := by
    rw [hKn]
    simp only [upperMajorant]
    ring
  rw [hΔd, e]
  ring
end Data
section Main
theorem of_components (hfar : separatedMeanUnderTiltStatement) (htt : separatedWeightTiltsStatement)
    (hcv : covarianceByTwoTiltsStatement) (hms : gasMeanScoreProductBound)
    (hsp : gasSupportMeanFarSpinBoundOneLevel) (hC : ActivityConditionalLawsStatement) :
    separatedProductOverGasStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hfar
  obtain ⟨r₂, p₂, H₂⟩ := htt
  obtain ⟨r₃, p₃, H₃⟩ := hcv
  obtain ⟨r₄, p₄, H₄⟩ := hms
  obtain ⟨r₅, p₅, H₅⟩ := hsp
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c)))), fun T hT' hrt K => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have t₂ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₃ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₄ := (((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₅ := (((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨y₁, Cf, hCf, H₁⟩ := H₁ T hT' t₁ K
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃ K
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄ K
  obtain ⟨y₅, H₅⟩ := H₅ T hT' t₅ K
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ y₅))), 3 / 2 * Cf, by positivity,
    fun y hy R A hK hAT n _ G hG ι I f D hne hF => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy4 : y₄ ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy5 : y₅ ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  obtain ⟨i₀, hi₀⟩ := id hne
  obtain ⟨-, hw, -, -⟩ := H₂ y hy2 R A hK hAT n G hG ι I {i₀} f D hF (Finset.singleton_subset_iff.mpr hi₀)
    ⟨i₀, Finset.mem_singleton_self i₀⟩ (fun σ => 2 * gasMajorantProduct A G f {i₀} σ) (Or.inr rfl)
  obtain ⟨p1, g1, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw
  have hOT := hAT.onFamily
  obtain ⟨hR, -, -, -, -⟩ := id hOT
  have ha1 : 1 ≤ R.params.coupling := by
    have : R.params.coupling = T.coupling := by rw [hR]; rfl
    rw [this]
    exact hT'.a_ge
  have hl := hAT.admissible.params_admissible
  have hc₀ : 1 ≤ A.responseParams.C₀ := by
    have h1 := hl.C₀_eq
    have h2 := hl.N₀_nonneg
    have h3 := hl.Kc_ge
    linarith only [h1, h2, h3, ha1]
  have hself : ∀ {S : Finset (TorusSite n)} {Y : TorusSite n}, Y ∈ S → Y ∈ thickening 2 S := fun {S Y} h => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Y, h, ?_⟩
    rw [supDist_self]
    omega
  have hdisj : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (lowerSites (f j)) (lowerSites (f k)) := fun j hj k hk hjk => by
    refine Finset.disjoint_left.mpr fun z h1 h2 => ?_
    have := hF.separated j hj k hk hjk _ (hself (parentBlock_mem_upperSites (f j) h1)) _
      (hself (parentBlock_mem_upperSites (f k) h2))
    rw [supDist_self] at this
    have := hF.eight_lt
    omega
  set ex := Real.exp (-(7 * T.gasRate * R.coupling)) with hex
  set E6 := Real.exp (-(R.params.rt * D / 2 ^ 6)) with hE6
  have h : SeparatedData A G I f ex Cf E6 := {
    prob := p1
    adm := g1.ae_admissible
    score_nonneg := hAT.admissible.price.nonneg
    score_borel := hAT.admissible.price.borel
    c₀ := hc₀
    nonempty := hF.nonempty
    meas := fun i hi => (H₅ y hy5 R A hK hAT n G hG (f i) (hF.weightNorm_le i hi) (hF.nonempty i hi)).1
    le := fun i hi => (H₅ y hy5 R A hK hAT n G hG (f i) (hF.weightNorm_le i hi) (hF.nonempty i hi)).2.1
    scores := fun J hJ => by
      have hm := H₄ y hy4 R A hK hAT n G hG ι J (fun j => lowerSites (f j))
        (fun j hj => Finset.card_pos.mp (card_lowerSites_pos (hF.nonempty j (hJ hj))))
        (fun j hj k hk hjk => hdisj j (hJ hj) k (hJ hk) hjk)
      simp only [parentBlocks_lowerSites] at hm
      exact hm.2
    cov := fun mm Yy Yp a b c d e g => H₃ y hy3 R A hK hAT n G hG mm Yy Yp a b c d e g
    far := fun i hi J hJ hiJ hJne Yt hYt => by
      obtain ⟨ht, -⟩ := H₂ y hy2 R A hK hAT n G hG ι I J f D hF hJ hJne Yt hYt
      obtain ⟨j₀, hj₀⟩ := hJne
      have hQ : (unionUpperSites f J).Nonempty := by
        obtain ⟨Y, hY⟩ := hF.nonempty j₀ (hJ hj₀)
        exact ⟨Y, Finset.mem_biUnion.mpr ⟨j₀, hj₀, hY⟩⟩
      have hDap : ∀ Y ∈ upperSites (f i), ∀ Y' ∈ unionUpperSites f J, D ≤ supDist Y Y' := by
        intro Y hY Y' hY'
        obtain ⟨j, hj, hYj⟩ := Finset.mem_biUnion.mp hY'
        exact hF.separated i hi j (hJ hj) (fun e => hiJ (e ▸ hj)) Y (hself hY) Y' (hself hYj)
      have hB : ∀ z ∈ lowerSites (f i), z ∉ unionLowerSites f J := by
        intro z hz hzJ
        obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hzJ
        exact Finset.disjoint_left.mp (hdisj i hi j (hJ hj) (fun e => hiJ (e ▸ hj))) hz hzj
      have he : (1 : ℝ) ≤ (J.card : ℝ) := by
        have : 0 < J.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
        exact_mod_cast this
      exact (H₁ y hy1 R A hK hAT n G hG (f i) (unionUpperSites f J) (unionLowerSites f J) (J.card : ℝ) Yt D
        (hF.weightNorm_le i hi) (hF.nonempty i hi) hF.range_le hF.eight_lt hQ hDap hB he ht).2.2 }
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have hE60 : 0 ≤ E6 := (Real.exp_pos _).le
  have hS0 : 0 ≤ totalLowerSites I f := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hM : ∀ i ∈ I, 0 ≤ upperMajorant A G (f i) := fun i hi =>
    (mul_nonneg_iff_of_pos_left (Real.exp_pos ex)).mp ((abs_nonneg _).trans (h.abs_expectation_le hi))
  have key := abs_integral_prod_sub_prod_le (G.gibbsLaw ∅) (fun i => gasSupportMean A G (f i)) I
    (fun i => upperMajorant A G (f i))
    (a := 3 / 2 * Cf * totalLowerSites I f * E6) (ex := ex) (by positivity) hex0 hM (fun i hi => h.abs_expectation_le hi)
    (fun i hi J hJ hiJ hJne => h.covariance_le hCf hE60 hi hJ hiJ hJne) I (Finset.Subset.refl I) hne
  refine ⟨h.integrable_product (Finset.Subset.refl I), fun i hi => h.integrable_mean hi, key.trans ?_⟩
  have hP0 : 0 ≤ ∏ i ∈ I, upperMajorant A G (f i) := Finset.prod_nonneg hM
  have hexp : Real.exp ((I.card : ℝ) * ex) ≤ Real.exp (2 * (I.card : ℝ) * ex) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (I.card : ℝ) * ex := by positivity
    linarith
  calc _ = (3 / 2 * Cf * (I.card : ℝ) ^ 2 * totalLowerSites I f * E6 * ∏ i ∈ I, upperMajorant A G (f i)) *
        Real.exp ((I.card : ℝ) * ex) := by ring
    _ ≤ (3 / 2 * Cf * (I.card : ℝ) ^ 2 * totalLowerSites I f * E6 * ∏ i ∈ I, upperMajorant A G (f i)) *
        Real.exp (2 * (I.card : ℝ) * ex) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring
end Main
end SeparatedProductOverGas
theorem separatedProductOverGas_holds (hfar : separatedMeanUnderTiltStatement) (htt : separatedWeightTiltsStatement)
    (hcv : covarianceByTwoTiltsStatement) (hms : FreeEnergies.gasMeanScoreProductBound)
    (hsp : gasSupportMeanFarSpinBoundOneLevel) (hC : Dobrushin.ActivityConditionalLawsStatement) :
    separatedProductOverGasStatement := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SeparatedProductOverGas.of_components <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
