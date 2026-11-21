import YangMills.Construction.ClusterExpansionOfAStep.FieldsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfTheLawOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABoxProof
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitInASetting
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.ScoresOfTwoSettings
import YangMills.Construction.ResponseInTheExpansion.SplitOfAConvexLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings TorusFields TorusLumps BlockOffsets TorusBalls RenormalizationStepParameters StepGas
  ColdStepAtMirrorFrames ClusterExpansionOfAStep ClusterExpansionOfAStep.BallLaws SettingShifts ConvexDecoupling
namespace FarSupports
set_option linter.unusedSectionVars false
section Weights
variable {L : ℕ} [NeZero L]
theorem weightLipschitz_le_succ (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.weightLipschitz_le_succ <;> assumption
theorem weightNorm_le_succ (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ t hL h)
theorem parentBlock_mem_weightSupportSites {t n : ℕ} [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n))
    {y : TorusSite (n * L)} (hy : y ∈ weightSupportSites L t (n * L) f) :
    parentBlock L y ∈ weightSupportSites L (t + 1) n f := by
  classical
  simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨p, ⟨ho, c, hc, hb⟩, hf⟩ := hy
  refine ⟨p, ⟨ho, c, hc, ?_⟩, hf⟩
  show c ∈ (sitesInBlocks L {parentBlock L y}).biUnion fun y => fineBlock L t (n * L) y
  exact Finset.mem_biUnion.mpr ⟨y, by simp [sitesInBlocks], hb⟩
theorem image_parentBlock_weightSupportSites {t n : ℕ} [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) =
      weightSupportSites L (t + 1) n f := by apply _root_.YangMills.SharedProofs.p19152 <;> assumption
theorem card_weightSupportSites_succ_le {t n : ℕ} [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (weightSupportSites L (t + 1) n f).card ≤ (weightSupportSites L t (n * L) f).card := by
  classical
  rw [← image_parentBlock_weightSupportSites f]
  exact Finset.card_image_le
end Weights
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem ballDensity_eq_zero_of_not_mem {Ψ : BondField ι → ℝ} {η : BondField ι} (hη : η ∉ ballProduct ι ρ) :
    ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  unfold ballDensity
  rw [radialWeightProd_eq_zero hη, zero_mul]
theorem ballDensity_nonneg {Ψ : BondField ι → ℝ} (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η :=
  mul_nonneg (radialWeightProd_nonneg η) (Real.exp_pos _).le
theorem integrable_ballDensity {Ψ : BondField ι → ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    Integrable (ballDensity (cutoffFactor ρ p) Ψ) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_ballProduct (ι := ι) hρ hΨ
  have := isFiniteMeasure_restrict_ballProduct (ι := ι) hρ
  have hs : Measurable (ballDensity (cutoffFactor ρ p) Ψ) :=
    (measurable_radialWeightProd hp).mul hΨ.neg.rexp.measurable
  have hb : MeasurableSet (ballProduct ι ρ) := (isOpen_ballProduct (ι := ι) (ρ := ρ)).measurableSet
  have hi : IntegrableOn (ballDensity (cutoffFactor ρ p) Ψ) (ballProduct ι ρ) := by
    refine Integrable.of_bound hs.aestronglyMeasurable (Real.exp M) ?_
    filter_upwards [ae_restrict_mem hb] with η hη
    rw [Real.norm_eq_abs, abs_of_nonneg (ballDensity_nonneg η)]
    unfold ballDensity
    have h1 : radialWeightProd (cutoffFactor ρ p) η ≤ 1 := radialWeightProd_le_one hρ hp η
    have h2 : Real.exp (-Ψ η) ≤ Real.exp M := by
      apply Real.exp_le_exp.mpr
      have a := hM η hη
      have b := neg_abs_le (Ψ η)
      linarith
    calc _ ≤ 1 * Real.exp M := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = _ := one_mul _
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro η hη
  by_contra hn
  exact hη (ballDensity_eq_zero_of_not_mem hn)
theorem integral_ballDensity_pos {Ψ : BondField ι → ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
  have := isFiniteMeasure_radialLaw (ι := ι) hρ hp
  have := radialLaw_neZero (ι := ι) hρ hp
  obtain ⟨M, hM⟩ := exists_abs_le_on_ballProduct (ι := ι) hρ hΨ
  have hi : Integrable (fun η : BondField ι => Real.exp (-Ψ η)) (radialLaw _ ρ p) := by
    refine Integrable.of_bound (hΨ.neg.rexp.aestronglyMeasurable) (Real.exp M) ?_
    filter_upwards [ae_mem_ballProduct] with η hη
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := hM η hη
    have h2 := neg_abs_le (Ψ η)
    linarith
  have h := integral_exp_pos hi
  rw [integral_radialLaw hp] at h
  refine h.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun η => ?_))
  simp only [ballDensity]
  ring
theorem integrable_mul_ballDensity {Ψ f : BondField ι → ℝ} {Q : ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hf : Measurable f) (hQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ Q) :
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η := by
  have hD := integrable_ballDensity (p := p) hΨ hρ hp
  refine Integrable.mono' (hD.const_mul Q) (hf.aestronglyMeasurable.mul hD.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballDensity_nonneg η)]
  by_cases hη : η ∈ ballProduct ι ρ
  · exact mul_le_mul_of_nonneg_right (hQ η hη) (ballDensity_nonneg η)
  · simp [ballDensity_eq_zero_of_not_mem hη]
theorem abs_ballExpectation_sub_le {Ψ f g : BondField ι → ℝ} {Q Q' E : ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hf : Measurable f) (hg : Measurable g)
    (hfQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ Q)
    (hgQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |g η| ≤ Q')
    (hE : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η - g η| ≤ E) :
    |ballExpectation (cutoffFactor ρ p) Ψ f - ballExpectation (cutoffFactor ρ p) Ψ g| ≤ E := by
  have hm := integral_ballDensity_pos (p := p) hΨ hρ hp
  have hD := integrable_ballDensity (p := p) hΨ hρ hp
  have i1 := integrable_mul_ballDensity hΨ hρ hp hf hfQ
  have i2 := integrable_mul_ballDensity hΨ hρ hp hg hgQ
  unfold ballExpectation
  rw [← sub_div, abs_div, abs_of_pos hm, div_le_iff₀ hm, ← integral_sub i1 i2]
  have : ‖∫ η, (f η * ballDensity (cutoffFactor ρ p) Ψ η - g η * ballDensity (cutoffFactor ρ p) Ψ η)‖ ≤
      ∫ η, E * ballDensity (cutoffFactor ρ p) Ψ η := by
    refine norm_integral_le_of_norm_le (hD.const_mul E) (Filter.Eventually.of_forall fun η => ?_)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballDensity_nonneg η)]
    by_cases hη : η ∈ ballProduct ι ρ
    · exact mul_le_mul_of_nonneg_right (hE η hη) (ballDensity_nonneg η)
    · simp [ballDensity_eq_zero_of_not_mem hη]
  rw [integral_const_mul] at this
  simpa [Real.norm_eq_abs] using this
theorem abs_ballExpectation_le {Ψ f : BondField ι → ℝ} {Q : ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hf : Measurable f) (hfQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ Q) :
    |ballExpectation (cutoffFactor ρ p) Ψ f| ≤ Q := by
  have := abs_ballExpectation_sub_le (g := fun _ => 0) (Q' := 0) (E := Q) hΨ hρ hp hf measurable_const hfQ
    (by simp) (by simpa using hfQ)
  have e : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => (0 : ℝ)) = 0 := by
    unfold ballExpectation
    simp
  rwa [e, sub_zero] at this
end Laws
section Setting
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
theorem isLiveState_of_inBalls
    (hrow : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hD : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))) {s : ChartSetting R n}
    (hs : s.IsAdmissible) {η : FreeCoords s.free} (hη : s.InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by
  have hh : IsHullState R.params (clusterRange R.coupling) (s.field η) s.support := hs.isHull η hη
  refine ⟨hh, ?_⟩
  rw [hrow.form (n * R.params.side) hside _ _ _ hh]
  have hΦ : 0 < ∏ X ∈ chainComponents (clusterRange R.coupling) s.support,
      R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X := by
    refine Finset.prod_pos fun X hX => ?_
    exact lt_of_le_of_ne (hrow.factor_nonneg (n * R.params.side) hside _ _ _ X)
      (Ne.symm (hs.factor_ne_zero η hη X hX))
  positivity
theorem abs_blockBondScores_le {W : TorusField (n * R.params.side)} {V : TorusField n}
    {b : StepCosts.BaseChoice R.params.side n} (Y : TorusSite n)
    (hsc : ∀ c, |bondScore R.params R.coupling W V b c| ≤ 2) : |blockBondScores (R := R) W V b Y| ≤ 16 := by
  unfold blockBondScores
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin 4, |bondScore R.params R.coupling W V b (Y, i) +
      bondScore R.params R.coupling W V b (Y - unitStep n i, i)| ≤ 4 := fun i =>
    (abs_add_le _ _).trans (by linarith [hsc (Y, i), hsc (Y - unitStep n i, i)])
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = 16 := by norm_num
theorem abs_supportResponseSum_sub_le {V : TorusField n} {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))} {b : StepCosts.BaseChoice R.params.side n}
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} {v : ℝ}
    (hs0 : ∀ y, 0 ≤ siteScore A.score Yt ωt y) (ha : 1 ≤ R.params.coupling) (hal : |A.coeff| ≤ 2)
    (hC₀ : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀)
    (hne : (weightSupportSites R.params.side R.depth (n * R.params.side) f).Nonempty)
    (hsc : ∀ c, |bondScore R.params R.coupling W V b c| ≤ 2)
    (hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1)
    (hQ : ∀ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
      |centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
        A.responseParams.C₀ + siteScore A.score Yt ωt y)
    (hv : |v| ≤ (A.responseParams.C₀ + 1 + 16 * R.params.coupling) *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ)) :
    |supportResponseSum A V f W Yt ωt bad b - v| ≤
      4 * (A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ)) *
        meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt := by
  set As := weightSupportSites R.params.side R.depth (n * R.params.side) f with hAs
  set Ap := weightSupportSites R.params.side (R.depth + 1) n f with hAp
  set Sm := ∑ y ∈ As, siteScore A.score Yt ωt y with hSm
  have hcard : (1 : ℝ) ≤ As.card := by exact_mod_cast hne.card_pos
  have hcp : (Ap.card : ℝ) ≤ As.card := by exact_mod_cast card_weightSupportSites_succ_le f
  have hS0 : 0 ≤ Sm := Finset.sum_nonneg fun y _ => hs0 y
  have h1 : |∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
      A.responseParams.C₀ * As.card + Sm := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hQ).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have h2 : |∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤ 16 * Ap.card := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _Y ∈ Ap, (16 : ℝ) := Finset.sum_le_sum fun Y _ => by
          rw [abs_mul]
          calc _ ≤ 1 * 16 := mul_le_mul (hhat Y) (abs_blockBondScores_le Y hsc) (abs_nonneg _) zero_le_one
            _ = 16 := one_mul _
      _ = 16 * Ap.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h3 : |R.params.coupling / 2 * A.coeff *
      ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤
      16 * R.params.coupling * As.card := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ R.params.coupling / 2)]
    have hb : |A.coeff| * |∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤
        2 * (16 * As.card) :=
      mul_le_mul hal (h2.trans (by linarith)) (abs_nonneg _) zero_le_two
    nlinarith
  have h4 : meanSiteScore A.score As Yt ωt = 1 + (As.card : ℝ)⁻¹ * Sm := rfl
  have hcn : (As.card : ℝ) ≠ 0 := by positivity
  have e1 : 4 * (A.responseParams.C₀ * (As.card : ℝ)) * meanSiteScore A.score As Yt ωt =
      4 * A.responseParams.C₀ * As.card + 4 * A.responseParams.C₀ * Sm := by
    rw [h4]
    field_simp
  rw [e1]
  have e2 : supportResponseSum A V f W Yt ωt bad b =
      ∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
        R.params.coupling / 2 * A.coeff *
          ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y := rfl
  rw [e2]
  have h5 := abs_sub (∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
        R.params.coupling / 2 * A.coeff *
          ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y) v
  have h6 := abs_add_le (∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
    (R.params.coupling / 2 * A.coeff *
      ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y)
  have h7 : Sm ≤ 4 * A.responseParams.C₀ * Sm := by nlinarith
  have h8 : (1 + 32 * R.params.coupling) * (As.card : ℝ) ≤ A.responseParams.C₀ * As.card := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  nlinarith
theorem blockBondScores_eq_of_coordsAgreeNear (hS : BondScoresAgreeNearBlocks) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    {s : ChartSetting R n} (hs : s.IsAdmissible) {Y : TorusSite n} {k : ℕ} (hk : 7 ≤ k) (hn : 2 * k + 2 < n)
    {η η' : FreeCoords s.free} (hnear : CoordsAgreeNear s s Y Y k η η') :
    blockBondScores (s.field η) s.coarse s.bases Y = blockBondScores (s.field η') s.coarse s.bases Y := by
  unfold blockBondScores
  have hn16 : 16 ≤ n := by omega
  have hag := settingsAgreeNear_refl s hs Y k hn
  refine Finset.sum_congr rfl fun i _ => ?_
  have box0 : OffsetInBox 1 (0 : Fin 4 → ℤ) := fun l => by simp
  have box1 : OffsetInBox 1 (Pi.single i 1 : Fin 4 → ℤ) := fun l => by
    by_cases h : l = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have box2 : OffsetInBox 1 (-(Pi.single i 1) : Fin 4 → ℤ) := fun l => by
    have := box1 l
    simpa using this
  have e1 := hS R n n s s Y Y k k η η' 0 i hfit hJ hn16 hn16 hs.subset_chart hag (by omega) le_rfl hnear box0
    (by simpa using box1)
  have e2 := hS R n n s s Y Y k k η η' (-(Pi.single i 1)) i hfit hJ hn16 hn16 hs.subset_chart hag (by omega) le_rfl
    hnear box2 (by simpa using box0)
  have o0 : Y + siteOfInt (0 : Fin 4 → ℤ) = Y := by
    funext l
    simp [siteOfInt]
  have o1 : Y + siteOfInt (-(Pi.single i 1) : Fin 4 → ℤ) = Y - unitStep n i := by
    rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
    congr 1
    funext l
    simp [siteOfInt]
  rw [o0] at e1
  rw [o1] at e2
  rw [e1, e2]
theorem abs_supportResponseSum_sub_of_coordsAgreeNear (hF : FieldsAgreeOfCoordsAgree)
    (hS : BondScoresAgreeNearBlocks) (hodd : Odd R.params.side)
    (hfit : R.params.Admissible) (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (hresp : A.IsAdmissible)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) {s : ChartSetting R n} (hs : s.IsAdmissible) {k : ℕ}
    (hk : 7 ≤ k) (hkn : 2 * k + 2 < n)
    (hr : (clusterRange R.coupling : ℝ) / 64 ≤ ((R.params.side * k - R.params.side : ℕ) : ℝ))
    {bad : Finset (TorusBond (n * R.params.side))} {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsize : weightNorm R.params.side R.depth f ≤ 1) {η η' : FreeCoords s.free}
    (hl : IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling)
    (hl' : IsLiveState R.params R.coupling R.labelWeight (s.field η') s.support s.labelling)
    (hne : (weightSupportSites R.params.side R.depth (n * R.params.side) f).Nonempty)
    (hnear : ∀ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, CoordsAgreeNear s s Y Y k η η') :
    |supportResponseSum A s.coarse f (s.field η) s.support s.labelling bad s.bases -
        supportResponseSum A s.coarse f (s.field η') s.support s.labelling bad s.bases| ≤
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) *
        meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) s.support
          s.labelling *
        Real.exp (-R.params.decayRate * ((R.params.side * k - R.params.side : ℕ) : ℝ)) := by
  set As := weightSupportSites R.params.side R.depth (n * R.params.side) f with hAs
  set Ap := weightSupportSites R.params.side (R.depth + 1) n f with hAp
  set E := Real.exp (-R.params.decayRate * ((R.params.side * k - R.params.side : ℕ) : ℝ)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hscore : ∀ Y ∈ Ap, blockBondScores (s.field η) s.coarse s.bases Y =
      blockBondScores (s.field η') s.coarse s.bases Y :=
    fun Y hY => blockBondScores_eq_of_coordsAgreeNear hS hfit hJ hs hk hkn (hnear Y hY)
  have e1 : supportResponseSum A s.coarse f (s.field η) s.support s.labelling bad s.bases -
      supportResponseSum A s.coarse f (s.field η') s.support s.labelling bad s.bases =
      ∑ y ∈ As, (centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f -
        centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η') s.support s.labelling f) := by
    show (∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
          blockBondScores (s.field η) s.coarse s.bases Y) -
      (∑ y ∈ As, centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η') s.support s.labelling f +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
          blockBondScores (s.field η') s.coarse s.bases Y) = _
    have : ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y =
        ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η') s.coarse s.bases Y :=
      Finset.sum_congr rfl fun Y hY => by rw [hscore Y hY]
    rw [this, Finset.sum_sub_distrib]
    ring
  rw [e1]
  have hn2 : 2 ≤ n := by omega
  have hm : 2 * (R.params.side * k - R.params.side) + 2 < n * R.params.side := by
    have h1 : (2 * k + 3) * R.params.side ≤ n * R.params.side := Nat.mul_le_mul_right _ hkn
    have h2 : R.params.side * k - R.params.side ≤ R.params.side * k := Nat.sub_le _ _
    nlinarith
  have one : ∀ y ∈ As,
      |centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f -
        centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η') s.support s.labelling f| ≤
        (1 + siteScore A.score s.support s.labelling y) * E := by
    intro y hy
    have hY := parentBlock_mem_weightSupportSites f hy
    obtain ⟨o, ho, hyo⟩ := exists_fineSite_of_parentBlock hodd (parentBlock R.params.side y) y rfl
    have hfa := hF R n n s s (parentBlock R.params.side y) (parentBlock R.params.side y) k k η η' o hfit hn2 hn2
      hs.subset_chart hs.subset_chart (settingsAgreeNear_refl s hs _ k hkn) (by omega) le_rfl (hnear _ hY) ho
    rw [← hyo] at hfa
    have hst : StatesAgreeNear R.params (s.field η) (s.field η') s.support s.support s.labelling s.labelling y y
        (R.params.side * k - R.params.side) :=
      ⟨hm, hm, hfa, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
    have := hresp.bounds.forget (n * R.params.side) (n * R.params.side) hside hside (s.field η) (s.field η')
      s.support s.support s.labelling s.labelling y y
      (R.params.side * k - R.params.side) f f hl hl' hr hst (fun _ _ _ _ _ => rfl)
    refine this.trans ?_
    have hs0 : 0 ≤ 1 + siteScore A.score s.support s.labelling y := by
      have : 0 ≤ siteScore A.score s.support s.labelling y := by
        unfold siteScore
        split_ifs
        · exact hresp.price.nonneg _
        · exact le_rfl
      linarith
    calc _ ≤ (1 + siteScore A.score s.support s.labelling y) * E * 1 :=
          mul_le_mul_of_nonneg_left hsize (mul_nonneg hs0 hE0)
      _ = _ := mul_one _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum one).trans ?_)
  rw [← Finset.sum_mul]
  apply le_of_eq
  congr 1
  have hc : (As.card : ℝ) ≠ 0 := by
    have := hne.card_pos
    positivity
  show _ = (As.card : ℝ) * (1 + (As.card : ℝ)⁻¹ * ∑ y ∈ As, siteScore A.score s.support s.labelling y)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
def indicatorBalls (s : ChartSetting R n) (g : FreeCoords s.free → ℝ) (η : FreeCoords s.free) : ℝ :=
  open Classical in if s.InBalls η then g η else 0
theorem measurable_indicatorBalls (s : ChartSetting R n) {g : FreeCoords s.free → ℝ} (hg : Measurable g) :
    Measurable (indicatorBalls s g) := by
  classical
  have hset : MeasurableSet {η : FreeCoords s.free | s.InBalls η} := by
    have : {η : FreeCoords s.free | s.InBalls η} = ⋂ b, {η | ‖η b‖ ≤ R.ballRadius} := by
      ext η
      simp [ChartSetting.InBalls, ClusterExpansionOfAStep.coordNorm_eq_norm]
    rw [this]
    exact MeasurableSet.iInter fun b =>
      measurableSet_le (measurable_norm.comp (measurable_pi_apply b)) measurable_const
  exact Measurable.ite hset hg measurable_const
theorem inBalls_of_forall_lt (s : ChartSetting R n) {η : FreeCoords s.free} (h : ∀ b, ‖η b‖ < R.ballRadius) :
    s.InBalls η := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.inBalls_of_norm_lt <;> assumption
theorem weightedMean_chartDensity_eq {s : ChartSetting R n} {Ψ : BondField s.free → ℝ}
    (e : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] s.potential) (G : FreeCoords s.free → ℝ) :
    weightedMean (chartDensity s) G = ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ G := by
  have hd : ∀ η, chartDensity s η = ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψ η := by
    intro η
    unfold chartDensity ballDensity ChartSetting.cutoffProduct radialWeightProd
    simp only [ClusterExpansionOfAStep.coordNorm_eq_norm]
    by_cases h : ∀ b, ‖η b‖ < R.ballRadius
    · rw [(e η (inBalls_of_forall_lt s h)).eq_of_nhds]
    · have hz : ∏ b : s.free, cutoffFactor R.ballRadius R.barrierFn ‖η b‖ = 0 := by
        simp only [not_forall, not_lt] at h
        obtain ⟨b, hb⟩ := h
        refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
        unfold cutoffFactor
        rw [if_neg (not_lt.mpr hb)]
      rw [hz]
      simp
  unfold weightedMean ballExpectation
  simp only [hd]
theorem sum_free_bondBlock_le (hodd : Odd R.params.side) (s : ChartSetting R n) {g : TorusSite n → ℝ}
    (hg0 : ∀ Z, 0 ≤ g Z) :
    ∑ b : s.free, g (bondBlock (R := R) b.1) ≤ 4 * (R.params.side : ℝ) ^ 4 * ∑ Z, g Z := by
  classical
  have hne : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have e1 : ∑ b : s.free, g (bondBlock (R := R) b.1) = ∑ b ∈ s.free, g (parentBlock R.params.side b.1) := by
    rw [← Finset.sum_coe_sort s.free]
    rfl
  have e2 : ∑ b ∈ s.free, g (parentBlock R.params.side b.1) ≤
      ∑ b : TorusBond (n * R.params.side), g (parentBlock R.params.side b.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hg0 _
  have e3 : ∑ b : TorusBond (n * R.params.side), g (parentBlock R.params.side b.1) =
      4 * ∑ x : TorusSite (n * R.params.side), g (parentBlock R.params.side x) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have e4 : ∑ x : TorusSite (n * R.params.side), g (parentBlock R.params.side x) =
      (R.params.side : ℝ) ^ 4 * ∑ Z : TorusSite n, g Z := by
    rw [← Finset.sum_fiberwise Finset.univ (parentBlock R.params.side), Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    have hfil : (Finset.univ.filter fun x : TorusSite (n * R.params.side) => parentBlock R.params.side x = Z) =
        sitesInBlocks R.params.side {Z} := by
      ext x
      simp [sitesInBlocks]
    rw [hfil]
    have h1 : ∑ x ∈ sitesInBlocks R.params.side {Z}, g (parentBlock R.params.side x) =
        ∑ x ∈ sitesInBlocks R.params.side {Z}, g Z := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have : parentBlock R.params.side x = Z := by simpa [sitesInBlocks] using hx
      rw [this]
    rw [h1, sum_sitesInBlocks hodd Z fun _ => g Z]
    simp [card_centredCube hodd]
  rw [e1]
  refine e2.trans (le_of_eq ?_)
  rw [e3, e4]
  ring
end Setting
section Closing
theorem update_add_eq_add_bondVariation {n : ℕ} {free : Finset (TorusBond n)} (η : FreeCoords free) (b : free)
    (v : EuclideanSpace ℝ (Fin 3)) : Function.update η b (η b + v) = η + bondVariation b v := by
  funext x
  by_cases h : x = b
  · subst h
    simp [bondVariation]
  · simp [bondVariation, Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem deriv_update_eq_fderiv {n : ℕ} {free : Finset (TorusBond n)} {u Ψ : FreeCoords free → ℝ}
    {η : FreeCoords free} (h : Ψ =ᶠ[nhds η] u) (hd : DifferentiableAt ℝ Ψ η) (b : free)
    (X : EuclideanSpace ℝ (Fin 3)) :
    deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0 = fderiv ℝ Ψ η (bondVariation b X) := by
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free))
      (bondVariation b X) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const (bondVariation b X : FreeCoords free)).const_add η
  have hp : ∀ τ : ℝ, Function.update η b (η b + τ • X) = η + τ • (bondVariation b X : FreeCoords free) := by
    intro τ
    rw [update_add_eq_add_bondVariation]
    congr 1
    funext x
    by_cases hx : x = b
    · subst hx
      simp [bondVariation]
    · simp [bondVariation, Pi.single_eq_of_ne hx]
  have hc : ContinuousAt (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free)) 0 := (hline 0).continuousAt
  have h0 : Filter.Tendsto (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free)) (nhds 0) (nhds η) := by
    have := hc.tendsto
    simpa using this
  have ev : (fun τ : ℝ => u (Function.update η b (η b + τ • X))) =ᶠ[nhds 0]
      fun τ : ℝ => Ψ (η + τ • (bondVariation b X : FreeCoords free)) := by
    filter_upwards [h0.eventually h] with τ hτ
    rw [hp, hτ]
  rw [ev.deriv_eq]
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ η) (η + (0 : ℝ) • (bondVariation b X : FreeCoords free)) := by
    simpa using hd.hasFDerivAt
  exact (h3.comp_hasDerivAt (0 : ℝ) (hline 0)).deriv
theorem mul_exp_le_of_far {κ Bv M g d : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hd : g ≤ d) (hB : Bv ≤ M) :
    Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) := by
  have e : M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) = M * Real.exp (-(κ / 2 * g) - κ / 2 * d) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [e]
  calc Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ * d)) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply Real.exp_le_exp.mpr
        nlinarith
theorem mul_exp_le_of_near {κ Bv M g d : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hd : d ≤ g)
    (hB : Bv ≤ M * Real.exp (-(κ * (g - d)))) :
    Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) := by
  have e : M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) = M * Real.exp (-(κ / 2 * g) - κ / 2 * d) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [e]
  calc Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ * (g - d))) * Real.exp (-(κ * d)) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ = M * Real.exp (-(κ * g)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply Real.exp_le_exp.mpr
        nlinarith
end Closing
section Pairs
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Pairs
section Geometry
variable {R : StepSetup} {n : ℕ} [NeZero n] {ι : Type} [DecidableEq ι]
end Geometry
theorem sum_bound_numerics {S₁ SA g L4 Gm x Wb rt ee Dr : ℝ} (hS₁ : 0 ≤ S₁) (hS : S₁ ≤ SA) (hg0 : 0 ≤ g)
    (hg : g ≤ 2 * (ee + 1))
    (hg2 : 2 * ee ≤ g) (hee : 0 ≤ ee) (hL4 : 0 ≤ L4) (hGm : 0 ≤ Gm) (hx : 0 ≤ x) (hWb : 0 ≤ Wb) (hrt : 0 ≤ rt)
    (hN : 16 * L4 * Gm * Wb * x ^ 1 * (ee + 1) ^ 4 * Real.exp (-(rt / 2 * ee)) ≤ 1) (hD : Dr ≤ 8 * (ee + 1)) :
    S₁ * g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb) ≤
      SA * (Real.exp (rt / 2) * Real.exp (-(rt * Dr / 2 ^ 4))) := by
  set Tt := Real.exp (-(rt / 2 * ee)) with hTt
  have hT0 : 0 ≤ Tt := (Real.exp_pos _).le
  have h1 : Real.exp (-(rt / 2 * g)) ≤ Tt * Tt := by
    rw [hTt, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h2 : g ^ 4 ≤ 16 * (ee + 1) ^ 4 := by
    calc g ^ 4 ≤ (2 * (ee + 1)) ^ 4 := by gcongr
      _ = _ := by ring
  have h3 : Tt ≤ Real.exp (rt / 2) * Real.exp (-(rt * Dr / 2 ^ 4)) := by
    rw [hTt, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h4 : g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb) ≤ Tt := by
    calc g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb)
        = (g ^ 4 * L4 * (Gm * x * Wb)) * Real.exp (-(rt / 2 * g)) := by ring
      _ ≤ (16 * (ee + 1) ^ 4 * L4 * (Gm * x * Wb)) * (Tt * Tt) := by gcongr
      _ = (16 * L4 * Gm * Wb * x ^ 1 * (ee + 1) ^ 4 * Tt) * Tt := by ring
      _ ≤ 1 * Tt := mul_le_mul_of_nonneg_right hN hT0
      _ = Tt := one_mul _
  have h5 : 0 ≤ g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb) := by positivity
  calc S₁ * g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb)
      = S₁ * (g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb)) := by ring
    _ ≤ SA * (Real.exp (rt / 2) * Real.exp (-(rt * Dr / 2 ^ 4))) :=
        mul_le_mul hS (h4.trans h3) h5 (hS₁.trans hS)
theorem final_bound_numerics {c SA E e16 U Sm Ao ρ xp : ℝ} (hc : 1 ≤ c) (hSA : 1 ≤ SA) (hE0 : 0 ≤ E)
    (hE : E ≤ e16) (hU : 0 ≤ U) (hρ : 0 ≤ ρ) (hAo : 0 ≤ Ao) (hxp : 0 ≤ xp) (he16 : 0 ≤ e16)
    (hSm : Sm ≤ SA * (xp * e16)) :
    c * E * U + 4 * ρ * (1 + Ao) * (2 * (1 + c) * U) * Sm + c * E * U ≤
      (2 + 16 * ρ * (1 + Ao) * xp) * c * SA * e16 * U := by
  have h1 : 4 * ρ * (1 + Ao) * (2 * (1 + c) * U) * Sm ≤
      4 * ρ * (1 + Ao) * (2 * (1 + c) * U) * (SA * (xp * e16)) :=
    mul_le_mul_of_nonneg_left hSm (by positivity)
  have h2 : 2 * (1 + c) ≤ 4 * c := by linarith
  have h3 : 4 * ρ * (1 + Ao) * (2 * (1 + c) * U) * (SA * (xp * e16)) ≤
      4 * ρ * (1 + Ao) * (4 * c * U) * (SA * (xp * e16)) := by
    have : 0 ≤ SA * (xp * e16) := by positivity
    gcongr
  have h4 : c * E * U ≤ c * SA * e16 * U := by
    have a1 : c * E ≤ c * (SA * e16) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    calc c * E * U ≤ c * (SA * e16) * U := mul_le_mul_of_nonneg_right a1 hU
      _ = _ := by ring
  nlinarith
end FarSupports
end YangMills.Construction.ResponseInTheExpansion
end
