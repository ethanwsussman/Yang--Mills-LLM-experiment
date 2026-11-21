import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsUpOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps StepSettings StepGas StepCosts WeightedResponses ResponseInTheExpansion RenormalizationStepParameters
section Weights
variable {L : ℕ} [NeZero L]
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
end Weights
section Sigma
variable {X A : Type} [MeasurableSpace X] {β : A → Type} [∀ a, MeasurableSpace (β a)]
private theorem measurable_of_prod_sigma [DecidableEq A] [Countable A] {g : X × Sigma β → ℝ}
    (h : ∀ a, Measurable fun p : X × β a => g (p.1, ⟨a, p.2⟩)) : Measurable g := by apply _root_.YangMills.SharedProofs.p67771 <;> assumption
end Sigma
section Levels
variable {ℓ : TorusLumps.StepParameters}
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s n) :
    (stageState T s n a).1 = topField ℓ s n a := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem weightSupportSites_eq_functionSites (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s)
    (m : ℕ) [NeZero m] :
    weightSupportSites L t m (fineWeight f (fineSide L t m)) = functionSites L f s m := by
  subst ht
  rfl
private theorem blockMean_depth_congr (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s) (m : ℕ)
    [NeZero m] (Y : TorusSite m) :
    blockMean L t m Y (fineWeight f (fineSide L t m)) = blockMean L s m Y (fineWeight f (fineSide L s m)) := by
  subst ht
  rfl
private theorem centeredSupportResponse_eq {T : StageTower ℓ} (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s : ℕ}
    (ht : (T.stage s).depth = s) (n : ℕ) [NeZero n] (V : TorusField n) (W : TorusField (n * ℓ.side))
    (Yt : Finset (TorusSite (n * ℓ.side))) (ωt : Yt → (T.stage s).labels.Ω)
    (bad : Finset (TorusBond (n * ℓ.side))) (b : BaseChoice ℓ.side n) :
    centeredSupportResponse (S.setup s) V (fineWeight f _) W Yt ωt bad b =
      fittedResponse S f s (n * ℓ.side) (W, ⟨Yt, ωt⟩) + (stepSourceTerm ℓ (T.stage s).coupling (S.coeffs s) s (fineWeight f _) W (b, V, bad) -
        caseMean (T.stage s).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
          (supportResponseSum (S.setup s) (trivialField n) (fineWeight f _))) := by apply _root_.YangMills.SharedProofs.p36430 <;> assumption
end Levels
section Core
variable {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ}
private structure StepHypotheses (S : ScoredStageTower T) (β : ℝ) (t n : ℕ) [NeZero n] {k : ℕ}
    (f : Fin k → FinePlaquetteFunction) : Prop where
  fit : ℓ.Admissible
  cut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn
  marks : T.MarksMeasurable
  block : IsBlockTorusSide ℓ (n * ℓ.side)
  row : (T.stage t).toStepSetup.HasExpansions
  read : ReadsCasesAt T β t n
  borel : Measurable (S.setup t).score
  score : (S.setup (t + 1)).score = coarseLabelScore S.params.s₁ (S.setup t).score
  score_nonneg : ∀ w, 0 ≤ (S.setup (t + 1)).score w
  score_nonneg0 : ∀ w, 0 ≤ (S.setup t).score w
  level : (T.stage t).depth = t
  one : ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
    CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ _ _ _ _ => 1)
  grounds : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
    (hotCaseGround (T.stage t).toStepSetup x.2.2.1 (stageState T (t + 1) n x).2).IsAdmissibleGround
  fm : ∀ i, ∃ fm : StageState T t (n * ℓ.side) → ℝ, Measurable fm ∧
    (∀ (W : TorusField (n * ℓ.side)) (Y : Finset (TorusSite (n * ℓ.side))) (ω : Y → (T.stage t).labels.Ω),
      IsLiveState ℓ (T.stage t).coupling (T.stage t).labelWeight W Y ω →
        fm (W, ⟨Y, ω⟩) = fittedResponse S (f i) t (n * ℓ.side) (W, ⟨Y, ω⟩)) ∧
    ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)),
      fm (stageState T t (n * ℓ.side) a) = fittedResponse S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) a)
  mean : ∀ i, ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)),
    fittedResponse S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) a) =
    ((markedSampleLaw T β t (n * ℓ.side))[completedCentered S (f i) t (n * ℓ.side) | stageSigma T t (n * ℓ.side)]) a
  up : ∀ i, ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
    caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _)) =
      fittedResponse S (f i) (t + 1) n (stageState T (t + 1) n x)
  term : ∀ i (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n),
    |stepSourceTerm ℓ (T.stage t).coupling (S.coeffs t) t (fineWeight (f i) _) W d -
        caseMean (T.stage t).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
          (supportResponseSum (S.setup t) (trivialField n) (fineWeight (f i) _))| ≤
      2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))
private def stepIncrement (S : ScoredStageTower T) {k : ℕ} (f : Fin k → FinePlaquetteFunction) (t n : ℕ) [NeZero n] (i : Fin k)
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) : ℝ :=
  stepSourceTerm ℓ (T.stage t).coupling (S.coeffs t) t (fineWeight (f i) _) W d -
    caseMean (T.stage t).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
      (supportResponseSum (S.setup t) (trivialField n) (fineWeight (f i) _))
private theorem completedCentered_succ (S : ScoredStageTower T) {k : ℕ} (f : Fin k → FinePlaquetteFunction) (t n : ℕ) [NeZero n]
    (i : Fin k) (x : MarkedSample ℓ (t + 1) n) :
    completedCentered S (f i) (t + 1) n x =
      completedCentered S (f i) t (n * ℓ.side) x.1 + stepIncrement S f t n i (stageState T t (n * ℓ.side) x.1).1 x.2 := by
  rw [stageState_fst]
  show (curvatureObservable (fineWeight (f i) (fineSide ℓ.side t (n * ℓ.side))) (bottomField ℓ t (n * ℓ.side) x.1) +
      (cumulativeSource T S.coeffs t (n * ℓ.side) (fineWeight (f i) (fineSide ℓ.side t (n * ℓ.side))) x.1 +
        sourceTerm T S.coeffs t n (fineWeight (f i) (fineSide ℓ.side (t + 1) n)) x)) -
    (centering S (f i) t (n * ℓ.side) + _) =
    (curvatureObservable (fineWeight (f i) (fineSide ℓ.side t (n * ℓ.side))) (bottomField ℓ t (n * ℓ.side) x.1) +
      cumulativeSource T S.coeffs t (n * ℓ.side) (fineWeight (f i) (fineSide ℓ.side t (n * ℓ.side))) x.1 -
      centering S (f i) t (n * ℓ.side)) + (sourceTerm T S.coeffs t n (fineWeight (f i) (fineSide ℓ.side (t + 1) n)) x - _)
  ring
private theorem one_le_meanSiteScore {Ω : Type} {s : Ω → ℝ} (h0 : ∀ w, 0 ≤ s w) {m : ℕ} (B Y : Finset (TorusSite m))
    (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by
  classical
  unfold meanSiteScore
  have h1 : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => by
    unfold siteScore
    split_ifs
    · exact h0 _
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ (B.card : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg h2 h1]
private theorem one_le_scoreMeanOver (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s m : ℕ) [NeZero m]
    (h0 : ∀ w, 0 ≤ (S.setup s).score w) (q : StageState T s m) : 1 ≤ scoreMeanOver S f s m q :=
  one_le_meanSiteScore h0 _ _ _
private theorem measurable_scoreMeanOver (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s m : ℕ) [NeZero m]
    (hs : Measurable (S.setup s).score) : Measurable (scoreMeanOver S f s m) := by
  classical
  refine measurable_of_prod_sigma fun Y => ?_
  show Measurable fun p : TorusField m × (Y → (T.stage s).labels.Ω) =>
    1 + ((functionSites ℓ.side f s m).card : ℝ)⁻¹ * ∑ y ∈ functionSites ℓ.side f s m, siteScore (S.setup s).score Y p.2 y
  refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => ?_))
  unfold siteScore
  by_cases hy : y ∈ Y
  · simp only [dif_pos hy]
    exact hs.comp ((measurable_pi_apply _).comp measurable_snd)
  · simp only [dif_neg hy]
    exact measurable_const
private def incrementProduct (S : ScoredStageTower T) {k : ℕ} (f : Fin k → FinePlaquetteFunction) (I J : Finset (Fin k))
    (t n : ℕ) [NeZero n] (p : StageState T t (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  ∏ i ∈ I \ J, stepIncrement S f t n i p.1.1 p.2
private def productCaseFunction (S : ScoredStageTower T) {k : ℕ} (f : Fin k → FinePlaquetteFunction) (I : Finset (Fin k))
    (t n : ℕ) [NeZero n] (fm : Fin k → StageState T t (n * ℓ.side) → ℝ) : TorusField n → CaseFunction (T.stage t).toStepSetup n :=
  fun V W Yt ωt bad b => ∏ i ∈ I, (fm i (W, ⟨Yt, ωt⟩) + stepIncrement S f t n i W (b, V, bad))
private def scoreCaseFunction (S : ScoredStageTower T) {k : ℕ} (f : Fin k → FinePlaquetteFunction) (J : Finset (Fin k))
    (t n : ℕ) [NeZero n] (c : ℝ) : TorusField n → CaseFunction (T.stage t).toStepSetup n :=
  fun _ _ Yt ωt _ _ => c * ∏ i ∈ J, meanSiteScore (S.setup t).score (functionSites ℓ.side (f i) t (n * ℓ.side)) Yt ωt
variable (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) (hB : completedObservablesBounded)
  (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hPast : FreeEnergiesOfTheFlow.MarkovPropertyOfStageStates)
  (hC : caseMeanProperties)
include hSt hB hT hPast hC in
private theorem conditionalProduct_step {S : ScoredStageTower T} {β : ℝ} {t n : ℕ} [NeZero n] {k : ℕ}
    {f : Fin k → FinePlaquetteFunction}
    (hF : StepHypotheses S β t n f) (hC0 : 0 ≤ S.params.C₀) (I : Finset (Fin k)) (e : ℝ) (m Err : Finset (Fin k) → ℝ)
    (hsplit : ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
      CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Yt ωt bad b =>
        ∏ i ∈ I, centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _) W Yt ωt bad b) ∧
      |caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Yt ωt bad b =>
          ∏ i ∈ I, centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _) W Yt ωt bad b) -
        ∏ i ∈ I, caseMean (T.stage t).toStepSetup G.cut G.coarse G.state
          (centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _))| ≤
      e * ∏ i ∈ I, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score) (functionSites ℓ.side (f i) (t + 1) n)
        G.state.1 G.state.2)
    (hmaj : ∀ J ⊆ I, J.Nonempty → ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
      CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Yt ωt _ _ =>
        ∏ i ∈ J, meanSiteScore (S.setup t).score (functionSites ℓ.side (f i) t (n * ℓ.side)) Yt ωt) ∧
      caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Yt ωt _ _ =>
        ∏ i ∈ J, meanSiteScore (S.setup t).score (functionSites ℓ.side (f i) t (n * ℓ.side)) Yt ωt) ≤
      m J * ∏ i ∈ J, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score) (functionSites ℓ.side (f i) (t + 1) n)
        G.state.1 G.state.2)
    (herr : ∀ J ⊆ I, J.Nonempty → 0 ≤ Err J ∧ 0 ≤ m J ∧ ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)),
      |conditionalProduct S β f J t (n * ℓ.side) a - ∏ i ∈ J, fittedResponse S (f i) t (n * ℓ.side) (stageState T t _ a)| ≤
        Err J * ∏ i ∈ J, scoreMeanOver S (f i) t (n * ℓ.side) (stageState T t _ a)) :
    ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
      |conditionalProduct S β f I (t + 1) n x - ∏ i ∈ I, fittedResponse S (f i) (t + 1) n (stageState T (t + 1) n x)| ≤
        (e + ∑ J ∈ I.powerset.filter Finset.Nonempty, Err J * m J *
            ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)))) *
          ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
  classical
  have hf := hF.fit
  have hfl := hf.depth_lt
  have hP : IsProbabilityMeasure (markedSampleLaw T β (t + 1) n) :=
    (hT ℓ hf hfl T hF.cut hF.marks β (fun _ => 0) (t + 1) n).1
  have hμ : IsProbabilityMeasure (markedSampleLaw T β t (n * ℓ.side)) :=
    (hT ℓ hf hfl T hF.cut hF.marks β (fun _ => 0) t (n * ℓ.side)).1
  have hτ : Measurable (stageState T t (n * ℓ.side)) := hSt ℓ hf T t (n * ℓ.side)
  have hG : stageSigma T t (n * ℓ.side) ≤ markedSampleMeasurableSpace ℓ t (n * ℓ.side) := hτ.comap_le
  obtain ⟨hπ, hbold⟩ := hPast ℓ hf hfl T hF.cut hF.marks β t n
  obtain ⟨hw, hread⟩ := hF.read
  have h1 : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n), CaseIntegrableAtSample T t n (fun _ _ _ _ _ _ => 1) x := by
    refine hF.grounds.mono fun x hx => ?_
    have h2 := hF.one (hotCaseGround (T.stage t).toStepSetup x.2.2.1 (stageState T (t + 1) n x).2) hx
    exact h2
  obtain ⟨hmean, hlecase⟩ := hread h1
  choose fm hfm hlive hae using hF.fm
  have hYb : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ Measurable (completedCentered S (f i) t (n * ℓ.side)) ∧
      ∀ a, |completedCentered S (f i) t (n * ℓ.side) a| ≤ K := by
    intro i
    obtain ⟨hm, K, hK⟩ := (hB ℓ hf T S.coeffs t (n * ℓ.side)).1 (fineWeight (f i) _)
    exact ⟨|K| + |centering S (f i) t (n * ℓ.side)|, by positivity, hm.sub_const _, fun a =>
      (abs_sub _ _).trans (add_le_add ((hK a).trans (le_abs_self K)) le_rfl)⟩
  choose KY hKY0 hYm hKY using hYb
  have hfmb : ∀ i, ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)), |fm i (stageState T t (n * ℓ.side) a)| ≤ KY i := by
    intro i
    have hbar := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := markedSampleLaw T β t (n * ℓ.side)) (m := stageSigma T t (n * ℓ.side))
      (Filter.Eventually.of_forall (hKY i))
    filter_upwards [hbar, hae i, hF.mean i] with a h2 h3 h4
    rw [h3, h4]
    exact h2
  have hfmb' := ae_all_iff.2 hfmb
  have hbK0 : ∀ i, 0 ≤ 2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) := fun i => by positivity
  have hsm : ∀ i, Measurable fun p : StageState T t (n * ℓ.side) × StepOutcome ℓ n => stepIncrement S f t n i p.1.1 p.2 := by
    intro i
    have h1' := ((hB ℓ hf T S.coeffs t n).2.2 (T.stage t).coupling (S.coeffs t) (fineWeight (f i) _))
    have h2 : Measurable fun p : StageState T t (n * ℓ.side) × StepOutcome ℓ n =>
        ((p.1.1, p.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h3 := (h1'.comp h2).sub_const (caseMean (T.stage t).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
      (supportResponseSum (S.setup t) (trivialField n) (fineWeight (f i) _)))
    exact h3
  have hgm : ∀ J, Measurable (incrementProduct S f I J t n) := fun J => Finset.measurable_prod _ fun i _ => hsm i
  have hgb : ∀ J p, |incrementProduct S f I J t n p| ≤
      ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) := by
    intro J p
    unfold incrementProduct
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hF.term i _ _)
  have hgb0 : ∀ J, 0 ≤ ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) := fun J =>
    Finset.prod_nonneg fun i _ => hbK0 i
  have hYp : ∀ J, Measurable fun a => ∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) a := fun J =>
    Finset.measurable_prod _ fun i _ => hYm i
  have hYpb : ∀ J a, |∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) a| ≤ ∏ i ∈ J, KY i := by
    intro J a
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hKY i a)
  have hKp : ∀ J : Finset (Fin k), 0 ≤ ∏ i ∈ J, KY i := fun J => Finset.prod_nonneg fun i _ => hKY0 i
  have hGm : ∀ J, Measurable (conditionalProduct S β f J t (n * ℓ.side)) := fun J =>
    (stronglyMeasurable_condExp.mono hG).measurable
  have hGb : ∀ J, ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)), |conditionalProduct S β f J t (n * ℓ.side) a| ≤ ∏ i ∈ J, KY i :=
    fun J => ae_bdd_abs_condExp_of_ae_bdd_abs (μ := markedSampleLaw T β t (n * ℓ.side)) (m := stageSigma T t (n * ℓ.side))
      (Filter.Eventually.of_forall (hYpb J))
  have hΦm : ∀ J, Measurable fun a => ∏ i ∈ J, fm i (stageState T t (n * ℓ.side) a) := fun J =>
    Finset.measurable_prod _ fun i _ => (hfm i).comp hτ
  have hΦb : ∀ J : Finset (Fin k), ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)),
      |∏ i ∈ J, fm i (stageState T t (n * ℓ.side) a)| ≤ ∏ i ∈ J, KY i := by
    intro J
    filter_upwards [hfmb'] with a ha
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ha i)
  have hgl : ∀ J, Measurable fun x : MarkedSample ℓ (t + 1) n =>
      incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) := by
    intro J
    have h2 : Measurable fun x : MarkedSample ℓ t (n * ℓ.side) × StepOutcome ℓ n =>
        ((stageState T t (n * ℓ.side) x.1, x.2) : StageState T t (n * ℓ.side) × StepOutcome ℓ n) :=
      (hτ.comp measurable_fst).prodMk measurable_snd
    have h3 := (hgm J).comp h2
    exact h3
  have hup : ∀ {g : MarkedSample ℓ t (n * ℓ.side) → ℝ}, Measurable g → ∀ {K : ℝ},
      (∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)), |g a| ≤ K) → ∀ J,
      Integrable (fun x : MarkedSample ℓ (t + 1) n => g x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2))
        (markedSampleLaw T β (t + 1) n) := by
    intro g hg K hK J
    refine Integrable.of_bound ((hg.comp hπ.measurable).mul (hgl J)).aestronglyMeasurable
      (K * ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)))) ?_
    filter_upwards [hπ.quasiMeasurePreserving.ae hK] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hx (hgb J _) (abs_nonneg _) ((abs_nonneg _).trans hx)
  have I1 := fun J => hup (hYp J) (Filter.Eventually.of_forall (hYpb J)) J
  have I2 := fun J => hup (hGm J) (hGb J) J
  have I3 := fun J => hup (hΦm J) (hΦb J) J
  have hA12 : ∀ J : Finset (Fin k), (markedSampleLaw T β (t + 1) n)[fun x : MarkedSample ℓ (t + 1) n =>
      (∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) x.1) *
        incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) | stageSigma T (t + 1) n]
      =ᵐ[markedSampleLaw T β (t + 1) n] (markedSampleLaw T β (t + 1) n)[fun x : MarkedSample ℓ (t + 1) n =>
      conditionalProduct S β f J t (n * ℓ.side) x.1 *
        incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) | stageSigma T (t + 1) n] :=
    fun J => hbold (fun a => ∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) a) (incrementProduct S f I J t n)
      (max (∏ i ∈ J, KY i) (∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)))))
      (hYp J) (hgm J) (fun a => (hYpb J a).trans (le_max_left _ _)) (fun p => (hgb J p).trans (le_max_right _ _))
  have hA23 : ∀ J : Finset (Fin k), (markedSampleLaw T β (t + 1) n)[fun x : MarkedSample ℓ (t + 1) n =>
      conditionalProduct S β f J t (n * ℓ.side) x.1 *
        incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) | stageSigma T (t + 1) n]
      =ᵐ[markedSampleLaw T β (t + 1) n] (markedSampleLaw T β (t + 1) n)[(fun x : MarkedSample ℓ (t + 1) n =>
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) | stageSigma T (t + 1) n] +
      (markedSampleLaw T β (t + 1) n)[(fun x : MarkedSample ℓ (t + 1) n =>
        conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) | stageSigma T (t + 1) n] := by
    intro J
    have e : (fun x : MarkedSample ℓ (t + 1) n =>
        conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) =
      (fun x : MarkedSample ℓ (t + 1) n =>
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) +
      (fun x : MarkedSample ℓ (t + 1) n =>
        conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) := by
      funext x
      simp
    rw [e]
    exact condExp_add (I3 J) ((I2 J).sub (I3 J)) _
  have e1 : (fun x : MarkedSample ℓ (t + 1) n => ∏ i ∈ I, completedCentered S (f i) (t + 1) n x) =
      ∑ J ∈ I.powerset, fun x : MarkedSample ℓ (t + 1) n =>
        (∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) x.1) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) := by
    funext x
    rw [Finset.sum_apply]
    simp only [completedCentered_succ]
    rw [Finset.prod_add]
    rfl
  have e2 : caseLift T t n (productCaseFunction S f I t n fm) =
      ∑ J ∈ I.powerset, fun x : MarkedSample ℓ (t + 1) n =>
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) := by
    funext x
    rw [Finset.sum_apply]
    have he : ((topField ℓ t (n * ℓ.side) x.1,
        ⟨(stageState T t (n * ℓ.side) x.1).2.1, (stageState T t (n * ℓ.side) x.1).2.2⟩) :
        StageState T t (n * ℓ.side)) = stageState T t (n * ℓ.side) x.1 := by
      rw [← stageState_fst]
    show ∏ i ∈ I, (fm i (topField ℓ t (n * ℓ.side) x.1,
        ⟨(stageState T t (n * ℓ.side) x.1).2.1, (stageState T t (n * ℓ.side) x.1).2.2⟩) +
      stepIncrement S f t n i (topField ℓ t (n * ℓ.side) x.1) (x.2.1, x.2.2.1, x.2.2.2)) = _
    rw [he, Finset.prod_add]
    refine Finset.sum_congr rfl fun J _ => ?_
    show _ * ∏ i ∈ I \ J, stepIncrement S f t n i (topField ℓ t (n * ℓ.side) x.1) x.2 =
      _ * ∏ i ∈ I \ J, stepIncrement S f t n i (stageState T t (n * ℓ.side) x.1).1 x.2
    rw [stageState_fst]
  have hS1 := condExp_finsetSum (μ := markedSampleLaw T β (t + 1) n) (s := I.powerset) (fun J _ => I1 J) (stageSigma T (t + 1) n)
  have hS2 := condExp_finsetSum (μ := markedSampleLaw T β (t + 1) n) (s := I.powerset) (fun J _ => I3 J) (stageSigma T (t + 1) n)
  rw [← e1] at hS1
  rw [← e2] at hS2
  have hLm : Measurable (caseLift T t n (productCaseFunction S f I t n fm)) := by
    have e2' : caseLift T t n (productCaseFunction S f I t n fm) = fun x : MarkedSample ℓ (t + 1) n => ∑ J ∈ I.powerset,
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) := by
      rw [e2]
      funext x
      rw [Finset.sum_apply]
    rw [e2']
    exact Finset.measurable_sum _ fun J _ => ((hΦm J).comp hπ.measurable).mul (hgl J)
  have hLb : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n), |caseLift T t n (productCaseFunction S f I t n fm) x| ≤
      ∑ J ∈ I.powerset, (∏ i ∈ J, KY i) *
        ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) := by
    have hall := (Finset.eventually_all I.powerset).2 fun J _ => hπ.quasiMeasurePreserving.ae (hΦb J)
    filter_upwards [hall] with x hx
    rw [e2, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hx J hJ) (hgb J _) (abs_nonneg _) (hKp J)
  have hcases : ∀ (V : TorusField n) (q : CoarseState (T.stage t).toStepSetup n),
      (hotCaseGround (T.stage t).toStepSetup V q).IsAdmissibleGround →
      CaseIntegrable (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V q (productCaseFunction S f I t n fm V) ∧
      caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V q (productCaseFunction S f I t n fm V) =
        caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V q (fun W Yt ωt bad b =>
          ∏ i ∈ I, centeredSupportResponse (S.setup t) V (fineWeight (f i) _) W Yt ωt bad b) := by
    intro V q hGr
    have hp := hC (T.stage t).toStepSetup n (hotCoreSites (T.stage t).toStepSetup V) V q
      (fun W Yt ωt bad b _ => hw _ _ W Yt ωt bad b)
    have he := hp.1 (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse (S.setup t) V (fineWeight (f i) _) W Yt ωt bad b)
      (productCaseFunction S f I t n fm V) (fun W Yt ωt bad b hh hwp => by
        have hD : 0 ≤ (T.stage t).labelWeight (n * ℓ.side) W Yt ωt := hF.row.2.nonneg _ hF.block W Yt ωt hh
        have hD' : 0 < (T.stage t).labelWeight (n * ℓ.side) W Yt ωt := lt_of_le_of_ne hD fun h0 => hwp.ne' (by
          unfold stepWeight
          show (T.stage t).labelWeight (n * ℓ.side) W Yt ωt * _ * _ * _ = 0
          rw [← h0]
          ring)
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [centeredSupportResponse_eq S (f i) hF.level n V W Yt ωt bad b, ← hlive i W Yt ωt ⟨hh, hD'⟩]
        rfl)
    exact ⟨he.1 (hsplit _ hGr).1, he.2.symm⟩
  have hIX : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n), CaseIntegrableAtSample T t n (productCaseFunction S f I t n fm) x := by
    refine hF.grounds.mono fun x hx => ?_
    have h2 := (hcases x.2.2.1 (stageState T (t + 1) n x).2 hx).1
    exact h2
  have hFX := hmean _ hLm _ hLb hIX
  have hDb : ∀ J ∈ I.powerset, ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
      |((markedSampleLaw T β (t + 1) n)[(fun x : MarkedSample ℓ (t + 1) n =>
        conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) |
          stageSigma T (t + 1) n]) x| ≤
      if J.Nonempty then Err J * m J *
        (∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)))) *
        ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) else 0 := by
    intro J hJ
    have hJI : J ⊆ I := Finset.mem_powerset.1 hJ
    by_cases hne : J.Nonempty
    · obtain ⟨hErr, hm0, hbd⟩ := herr J hJI hne
      set c := Err J * ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) with hc
      have hc0 : 0 ≤ c := mul_nonneg hErr (hgb0 J)
      have hlift : ∀ x, caseLift T t n (scoreCaseFunction S f J t n c) x =
          c * ∏ i ∈ J, scoreMeanOver S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) x.1) := fun _ => rfl
      have hN1 : ∀ i q, 1 ≤ scoreMeanOver S (f i) t (n * ℓ.side) q := fun i q =>
        one_le_scoreMeanOver S (f i) t _ hF.score_nonneg0 q
      have hφ : ∀ V W Yt ωt bad b, 0 ≤ scoreCaseFunction S f J t n c V W Yt ωt bad b := by
        intro V W Yt ωt bad b
        refine mul_nonneg hc0 (Finset.prod_nonneg fun i _ => ?_)
        exact (zero_le_one.trans (one_le_meanSiteScore hF.score_nonneg0 _ _ _))
      have hmφ : Measurable (caseLift T t n (scoreCaseFunction S f J t n c)) := by
        have e : caseLift T t n (scoreCaseFunction S f J t n c) = fun x =>
            c * ∏ i ∈ J, scoreMeanOver S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) x.1) := funext hlift
        rw [e]
        exact (Finset.measurable_prod _ fun i _ => ((measurable_scoreMeanOver S (f i) t _ hF.borel).comp hτ).comp
          hπ.measurable).const_mul _
      have hpack : ∀ (V : TorusField n) (q : CoarseState (T.stage t).toStepSetup n),
          (hotCaseGround (T.stage t).toStepSetup V q).IsAdmissibleGround →
          CaseIntegrable (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V q (scoreCaseFunction S f J t n c V) ∧
          caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V q (scoreCaseFunction S f J t n c V) ≤
            c * (m J * ∏ i ∈ J, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
              (functionSites ℓ.side (f i) (t + 1) n) q.1 q.2) := by
        intro V q hGr
        have hp := hC (T.stage t).toStepSetup n (hotCoreSites (T.stage t).toStepSetup V) V q
          (fun W Yt ωt bad b _ => hw _ _ W Yt ωt bad b)
        have hmj := hmaj J hJI hne _ hGr
        have h2 := hp.2.2.1 c _ hmj.1
        refine ⟨h2.1, ?_⟩
        show caseMean _ _ _ _ (fun W Yt ωt bad b => c * _) ≤ _
        rw [h2.2]
        exact mul_le_mul_of_nonneg_left hmj.2 hc0
      have hDi := (I2 J).sub (I3 J)
      have hDK : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
          |conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
          (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
            incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)| ≤
          ((∏ i ∈ J, KY i) + ∏ i ∈ J, KY i) *
            ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) := by
        filter_upwards [hπ.quasiMeasurePreserving.ae (hGb J), hπ.quasiMeasurePreserving.ae (hΦb J)] with x h2 h3
        rw [← sub_mul, abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add h2 h3)) (hgb J _) (abs_nonneg _)
          (add_nonneg (hKp J) (hKp J))
      have hDle : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
          |conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
          (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
            incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)| ≤
          caseLift T t n (scoreCaseFunction S f J t n c) x := by
        have hall : ∀ᵐ a ∂(markedSampleLaw T β t (n * ℓ.side)), ∀ i,
            fm i (stageState T t (n * ℓ.side) a) = fittedResponse S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) a) :=
          ae_all_iff.2 hae
        filter_upwards [hπ.quasiMeasurePreserving.ae hbd, hπ.quasiMeasurePreserving.ae hall] with x h2 h3
        rw [hlift, ← sub_mul, abs_mul]
        have e3 : ∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1) =
            ∏ i ∈ J, fittedResponse S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) x.1) :=
          Finset.prod_congr rfl fun i _ => h3 i
        rw [e3]
        have hN0 : 0 ≤ ∏ i ∈ J, scoreMeanOver S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) x.1) :=
          Finset.prod_nonneg fun i _ => zero_le_one.trans (hN1 i _)
        calc _ ≤ (Err J * ∏ i ∈ J, scoreMeanOver S (f i) t (n * ℓ.side) (stageState T t (n * ℓ.side) x.1)) *
              ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) :=
            mul_le_mul h2 (hgb J _) (abs_nonneg _) (mul_nonneg hErr hN0)
          _ = _ := by rw [hc]; ring
      have hIφ : ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n), CaseIntegrableAtSample T t n (scoreCaseFunction S f J t n c) x := by
        refine hF.grounds.mono fun x hx => ?_
        have h2 := (hpack x.2.2.1 (stageState T (t + 1) n x).2 hx).1
        exact h2
      have hres := hlecase _ hφ hmφ hIφ _ _ hDi hDK hDle
      filter_upwards [hres, hF.grounds] with x h2 h3
      rw [if_pos hne]
      refine h2.trans ((hpack x.2.2.1 (stageState T (t + 1) n x).2 h3).2.trans ?_)
      have hNup : ∀ i, 1 ≤ scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := fun i =>
        one_le_scoreMeanOver S (f i) (t + 1) n hF.score_nonneg _
      have hsame : ∏ i ∈ J, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score) (functionSites ℓ.side (f i) (t + 1) n)
          (stageState T (t + 1) n x).2.1 (stageState T (t + 1) n x).2.2 =
          ∏ i ∈ J, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        unfold scoreMeanOver
        rw [hF.score]
        rfl
      have hsub : ∏ i ∈ J, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) ≤
          ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) :=
        by
          have h5 : (1 : ℝ) ≤ ∏ i ∈ I \ J, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
            simpa using Finset.prod_le_prod (s := I \ J) (f := fun _ => (1 : ℝ))
              (g := fun i => scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x))
              (fun _ _ => zero_le_one) (fun i _ => hNup i)
          have h6 : 0 ≤ ∏ i ∈ J, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) :=
            Finset.prod_nonneg fun i _ => zero_le_one.trans (hNup i)
          rw [← Finset.prod_sdiff hJI]
          exact le_mul_of_one_le_left h6 h5
      show c * (m J * ∏ i ∈ J, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
          (functionSites ℓ.side (f i) (t + 1) n)
          (stageState T (t + 1) n x).2.1 (stageState T (t + 1) n x).2.2) ≤ _
      rw [hsame]
      calc c * (m J * ∏ i ∈ J, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x))
          ≤ c * (m J * ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hm0) hc0
        _ = _ := by rw [hc]; ring
    · have hJ0 : J = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
      subst hJ0
      have hG1 : conditionalProduct S β f ∅ t (n * ℓ.side) = fun _ => 1 := by
        unfold conditionalProduct
        simp only [Finset.prod_empty]
        exact condExp_const hG 1
      have e0 : (fun x : MarkedSample ℓ (t + 1) n =>
          conditionalProduct S β f ∅ t (n * ℓ.side) x.1 *
            incrementProduct S f I ∅ t n (stageState T t (n * ℓ.side) x.1, x.2) -
          (∏ i ∈ (∅ : Finset (Fin k)), fm i (stageState T t (n * ℓ.side) x.1)) *
            incrementProduct S f I ∅ t n (stageState T t (n * ℓ.side) x.1, x.2)) = 0 := by
        funext x
        rw [hG1]
        simp
      rw [e0, condExp_zero]
      exact Filter.Eventually.of_forall fun x => by simp
  have hall1 := (Finset.eventually_all I.powerset).2 fun J _ => hA12 J
  have hall2 := (Finset.eventually_all I.powerset).2 fun J _ => hA23 J
  have hall3 := (Finset.eventually_all I.powerset).2 hDb
  have hups := ae_all_iff.2 hF.up
  filter_upwards [hS1, hS2, hFX, hall1, hall2, hall3, hups, hF.grounds] with x h1' h2' h3' h4 h5 h6 h7 h8
  set Dx : Finset (Fin k) → ℝ := fun J => ((markedSampleLaw T β (t + 1) n)[(fun x : MarkedSample ℓ (t + 1) n =>
        conditionalProduct S β f J t (n * ℓ.side) x.1 * incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) -
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) |
          stageSigma T (t + 1) n]) x with hDx
  have hsplitx := hsplit (hotCaseGround (T.stage t).toStepSetup x.2.2.1 (stageState T (t + 1) n x).2) h8
  have hup' : ∏ i ∈ I, fittedResponse S (f i) (t + 1) n (stageState T (t + 1) n x) =
      ∏ i ∈ I, caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (t + 1) n x).2 (centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _)) :=
    Finset.prod_congr rfl fun i _ => (h7 i).symm
  have hmainEq : conditionalProduct S β f I (t + 1) n x =
      caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (fun W Yt ωt bad b =>
          ∏ i ∈ I, centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _) W Yt ωt bad b) +
        ∑ J ∈ I.powerset, Dx J := by
    have a1 : conditionalProduct S β f I (t + 1) n x = ∑ J ∈ I.powerset,
        ((markedSampleLaw T β (t + 1) n)[fun x : MarkedSample ℓ (t + 1) n =>
      (∏ i ∈ J, completedCentered S (f i) t (n * ℓ.side) x.1) *
        incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2) | stageSigma T (t + 1) n]) x := by
      refine h1'.trans ?_
      rw [Finset.sum_apply]
    have a2 : caseMeanAtSample T t n (productCaseFunction S f I t n fm) x = ∑ J ∈ I.powerset,
        ((markedSampleLaw T β (t + 1) n)[(fun x : MarkedSample ℓ (t + 1) n =>
        (∏ i ∈ J, fm i (stageState T t (n * ℓ.side) x.1)) *
          incrementProduct S f I J t n (stageState T t (n * ℓ.side) x.1, x.2)) | stageSigma T (t + 1) n]) x := by
      rw [← h3', h2', Finset.sum_apply]
    have a3 : caseMeanAtSample T t n (productCaseFunction S f I t n fm) x =
        caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (t + 1) n x).2 (fun W Yt ωt bad b =>
        ∏ i ∈ I, centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _) W Yt ωt bad b) :=
      (hcases x.2.2.1 (stageState T (t + 1) n x).2 h8).2
    rw [← a3, a2, a1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [h4 J hJ, h5 J hJ]
    rfl
  rw [hmainEq, hup']
  have hNup : ∀ i, 1 ≤ scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := fun i =>
    one_le_scoreMeanOver S (f i) (t + 1) n hF.score_nonneg _
  have hsameI : ∏ i ∈ I, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score) (functionSites ℓ.side (f i) (t + 1) n)
      (stageState T (t + 1) n x).2.1 (stageState T (t + 1) n x).2.2 =
      ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold scoreMeanOver
    rw [hF.score]
    rfl
  have hb1 : |caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (fun W Yt ωt bad b =>
        ∏ i ∈ I, centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _) W Yt ωt bad b) -
      ∏ i ∈ I, caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _))| ≤
      e * ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
    rw [← hsameI]
    exact hsplitx.2
  have hb2 : |∑ J ∈ I.powerset, Dx J| ≤ (∑ J ∈ I.powerset.filter Finset.Nonempty, Err J * m J *
      ∏ i ∈ I \ J, (2 * (S.params.C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)))) *
      ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h6).trans ?_
    rw [← Finset.sum_filter, Finset.sum_mul]
  calc _ = |(caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (fun W Yt ωt bad b =>
        ∏ i ∈ I, centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _) W Yt ωt bad b) -
      ∏ i ∈ I, caseMean (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup x.2.2.1) x.2.2.1 (stageState T (t + 1) n x).2
        (centeredSupportResponse (S.setup t) x.2.2.1 (fineWeight (f i) _))) + ∑ J ∈ I.powerset, Dx J| := by
        congr 1
        ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hb1 hb2)
    _ = _ := by ring
end Core
section Top
variable {ℓ : TorusLumps.StepParameters}
private theorem stepSourceTerm_eq {T : StageTower ℓ} (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s : ℕ}
    (ht : (T.stage s).depth = s) (n : ℕ) [NeZero n] (V : TorusField n) (W : TorusField (n * ℓ.side))
    (bad : Finset (TorusBond (n * ℓ.side))) (b : BaseChoice ℓ.side n) :
    stepSourceTerm ℓ (T.stage s).coupling (S.coeffs s) s (fineWeight f _) W (b, V, bad) =
      ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y ∈ weightSupportSites ℓ.side ((T.stage s).depth + 1) n (fineWeight f _),
        blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) * blockBondScores (R := (T.stage s).toStepSetup) W V b Y := by
  classical
  have hs2 := weightSupportSites_eq_functionSites ℓ.side f (congrArg (· + 1) ht) n
  have hh : ∀ Y : TorusSite n, blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) =
      blockMean ℓ.side (s + 1) n Y (fineWeight f _) :=
    fun Y => blockMean_depth_congr ℓ.side f (congrArg (· + 1) ht) n Y
  have hsum : ∑ Y ∈ functionSites ℓ.side f (s + 1) n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
        blockBondScores (R := (T.stage s).toStepSetup) W V b Y =
      ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) * blockBondScores (R := (T.stage s).toStepSetup) W V b Y := by
    refine Finset.sum_subset (Finset.subset_univ _) fun Y _ hY => ?_
    have h0 : blockMean ℓ.side (s + 1) n Y (fineWeight f (fineSide ℓ.side (s + 1) n)) = 0 := by
      by_contra hne
      exact hY (mem_weightSupportSites_of_blockMean_ne_zero ℓ.side (s + 1) n Y _ hne)
    rw [h0, zero_mul]
  show ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
      blockBondScores (R := (T.stage s).toStepSetup) W V b Y = _
  rw [hs2]
  simp only [hh]
  rw [hsum]
private theorem weightNorm_depth_congr (L : ℕ) (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s) (n : ℕ) (g : ℕ → ℕ) :
    weightNorm L (g t) (fineWeight f (fineSide L (t + 1) n)) = weightNorm L (g s) (fineWeight f (fineSide L (s + 1) n)) := by
  subst ht
  rfl
end Top
theorem conditionalProductStepBound_holds (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hB : completedObservablesBounded)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (hPast : FreeEnergiesOfTheFlow.MarkovPropertyOfStageStates)
    (hRead : conditionalMeanReadsCasesStatement) (hC : caseMeanProperties)
    (hMV : supportResponseMeanStatement) (hFL : labelFunctionsIntegrableStatement)
    (hGr : TowerStatesAreGroundStates) (hRow : expansionAlongFlow)
    (hFR : fittedResponseIsConditionalMeanStatement) : ConditionalProductStepBound := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hGr a ha
  obtain ⟨L₅, r₅, C₅, hr₅, H₅⟩ := hFR a ha
  obtain ⟨L₄, r₄, hr₄, H₄⟩ := hRead a ha
  obtain ⟨r₂, hr₂, H₂⟩ := hMV
  obtain ⟨r₃, hr₃, H₃⟩ := hFL
  refine ⟨max L₁ (max L₄ L₅), fun c => min (min (r₁ c) (min (r₄ c) (r₅ c))) (min (r₂ c) (r₃ c)), max C₁ C₅,
    fun c => lt_min (lt_min (hr₁ c) (lt_min (hr₄ c) (hr₅ c))) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  have hr₁' := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₄' := hrt.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr₅' := hrt.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr₂' := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₃' := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hOn hr₁' ((le_max_left _ _).trans hCd) K
  obtain ⟨y₄, Y₄⟩ := H₄ L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hr₄'
  obtain ⟨y₅, Y₅⟩ := H₅ L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hCS hOn hr₅'
    ((le_max_right _ _).trans hCd) K
  obtain ⟨y₂, Y₂⟩ := H₂ Tb hD hr₂' K
  obtain ⟨y₃, Y₃⟩ := H₃ Tb hD hr₃' K
  refine ⟨max (max y₁ y₄) (max y₅ (max y₂ (max y₃ Tb.floorMin))), fun y hy hRS => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₄ : y₄ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₅ : y₅ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₂ : y₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₀ : Tb.floorMin ≤ y :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  intro β T S t hSK hOR hRR k f n _ hbs hs0 hs1 I e m Err hsp hmj her
  have hfit := hD.fits y hy₀
  have hlevel : ∀ u, (T.stage u).depth = u := by
    intro u
    induction u with
    | zero => exact hOR.startsAtWilson.depth_eq
    | succ u ih =>
      show (T.stage u).depth + 1 = u + 1
      rw [ih]
  have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hbsL : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
  have hn₀ : (Tb.stepParameters y).n₀ ≤ n := (Nat.le_mul_of_pos_left _ hLpos).trans hbs.2
  have hAT : OnStepParameters Tb y (S.setup t) := by
    have hst := hOR.isFlowStep t (Nat.le_succ t)
    refine ⟨hst.onFamily, ?_, hOR.isAdmissible t (Nat.le_succ t), ?_⟩
    · rw [hst.nextCoupling_eq, hst.coupling_eq]
      exact (hRow _ hRS β (t + 1) hRR).2 t (Nat.lt_succ_self t)
    · rw [hOR.params_eq t]
      exact hOR.N₀_eq
  have hK : (S.setup t).responseParams = K := (hOR.params_eq t).trans hSK
  have hKf : S.params.Admissible (Tb.stepParameters y) := by
    have h := (hOR.isAdmissible 0 (Nat.zero_le _)).params_admissible
    rw [hOR.params_eq 0] at h
    exact h
  have hC0 : 0 ≤ S.params.C₀ := by
    rw [hKf.C₀_eq]
    linarith [hKf.N₀_nonneg, hKf.Kc_ge, hfit.a_ge]
  have hgr := Y₁ y hy₁ hRS β T S (t + 1) hSK hOR hRR t (Nat.lt_succ_self t)
  have hfr := fun i => Y₅ y hy₅ hRS β T S (t + 1) hSK hOR hRR (f i) t (Nat.le_succ t) (n * (Tb.stepParameters y).side) hbsL
  have hfr' := fun i => Y₅ y hy₅ hRS β T S (t + 1) hSK hOR hRR (f i) t (Nat.le_succ t) n hbs
  have hF : StepHypotheses S β t n f :=
    { fit := hfit
      cut := hOR.isCutoff_bottom
      marks := hOR.marksMeasurable
      block := hbsL
      row := (hOR.isFlowStep t (Nat.le_succ t)).onFamily.isStep.1
      read := Y₄ y hy₄ hRS.returns_at hRS.wilson_expansion T β t n
        ⟨hOR.startsAtWilson, fun j hj => (hOR.isFlowStep j (by omega)).coupling_eq,
          fun j hj => (hOR.isFlowStep j (by omega)).onFamily⟩
        hOR.isCutoff_bottom hOR.marksMeasurable hgr.1 hbsL hbs.1
      borel := (hOR.isAdmissible t (Nat.le_succ t)).price.borel
      score := hOR.score_succ t (Nat.lt_succ_self t)
      score_nonneg := (hOR.isAdmissible (t + 1) le_rfl).price.nonneg
      score_nonneg0 := (hOR.isAdmissible t (Nat.le_succ t)).price.nonneg
      level := hlevel t
      one := fun G hG => Y₃ y hy₃ _ _ hK hAT n G hG ∅ (fun _ _ => 1) (fun _ => measurable_const)
        (fun Yt ωt => by simp [scoreSumOn])
      grounds := (hgr.2 n hbs).mono fun x hx => hx.1
      fm := fun i => (hfr i).1
      mean := fun i => (hfr i).2.1
      up := fun i => (hfr' i).2.2 (Nat.lt_succ_self t)
      term := fun i W d => by
        have h := (Y₂ y hy₂ _ _ hK hAT n (fineWeight (f i) _)).2 hn₀
          ((weightNorm_depth_congr _ (f i) (hlevel t) n id).le.trans (hs0 i))
          ((weightNorm_depth_congr _ (f i) (hlevel t) n (· + 1)).le.trans (hs1 i)) W d.2.1 d.1
        have hs := stepSourceTerm_eq S (f i) (hlevel t) n d.2.1 W d.2.2 d.1
        have hs' : stepSourceTerm (Tb.stepParameters y) (T.stage t).coupling (S.coeffs t) t (fineWeight (f i) _) W d = _ := hs
        rw [hs']
        have hs1 : weightSupportSites (Tb.stepParameters y).side (T.stage t).depth (n * (Tb.stepParameters y).side)
            (fineWeight (f i) (fineSide (Tb.stepParameters y).side (T.stage t).depth (n * (Tb.stepParameters y).side))) =
            functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side) :=
          weightSupportSites_eq_functionSites _ (f i) (hlevel t) (n * (Tb.stepParameters y).side)
        refine h.trans (le_of_eq ?_)
        rw [hK, ← hSK]
        exact congrArg (fun A : Finset (TorusSite (n * (Tb.stepParameters y).side)) => 2 * (S.params.C₀ * (A.card : ℝ))) hs1 }
  exact conditionalProduct_step hSt hB hT hPast hC hF hC0 I e m Err hsp hmj her
end YangMills.Construction.FreeEnergies
end
