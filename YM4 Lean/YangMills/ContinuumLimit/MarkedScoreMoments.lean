import YangMills.ContinuumLimit.ExceptionalSetMoments
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Formulation
open Construction TorusFields TorusLumps WeightedResponses FreeEnergies ResponseInTheExpansion
  RenormalizationStepParameters

/-- The terminal centered response on an exceptional event, at every block torus side.
Both the score moments and the event probability refer to the normalized marked law. -/
theorem fitted_response_bad_at_flow :
    AtResponseParameters fun Tb Kr y => ∃ x₁ C : ℝ, 1 ≤ C ∧
      ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ),
        S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor (Tb.stepParameters y) β k →
        let x := ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k
        let n := 2 * (Tb.stepParameters y).side ^ m
        x₁ ≤ x → IsBlockTorusSide (Tb.stepParameters y) n →
        ∀ f : FinePlaquetteFunction, weightNorm (Tb.stepParameters y).side k (fineWeight f (fineSide (Tb.stepParameters y).side k n)) ≤ 1 →
        ∀ (B : Set (MarkedSample (Tb.stepParameters y) k n)) (U : ℝ),
        (markedSampleLaw T β k n) B ≤ ENNReal.ofReal (Real.exp (-U)) →
        (∫⁻ w in B, ENNReal.ofReal (fittedResponse S f k n (stageState T k n w) ^ 2)
            ∂(markedSampleLaw T β k n)) ≤ ENNReal.ofReal
          (((Kr.C₀ + 1) * ((functionSites (Tb.stepParameters y).side f k n).card : ℝ)) ^ 2 *
            (1 + (C * (clusterRange x : ℝ) ^ 4 * Real.log x) ^ 4) * Real.exp (-U / 2)) := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, one⟩ := TheStatementsProvedTogether.meanScore_moments a ha
  obtain ⟨L₂, r₂, C₂, hr₂, two⟩ := TheStatementsProvedTogether.flow_states_are_ground_states a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂,
    fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hcs hOn hrt hC Kr
  obtain ⟨y₁, h₁⟩ := one L hodd ((le_max_left ..).trans hL) Tb hTa hTL hD hcs hOn
    (hrt.trans (min_le_left ..)) ((le_max_left ..).trans hC) Kr
  obtain ⟨y₂, h₂⟩ := two L hodd ((le_max_right ..).trans hL) Tb hTa hTL hD hcs hOn
    (hrt.trans (min_le_right ..)) ((le_max_right ..).trans hC) Kr
  refine ⟨max (max y₁ y₂) Tb.floorMin, ?_⟩
  intro y hy hret
  have hy' := (le_max_left _ _).trans hy
  have hfit := hD.fits y ((le_max_right _ _).trans hy)
  obtain ⟨x₁, hmos⟩ := h₁ y ((le_max_left ..).trans hy') hret
  obtain ⟨C, hC, hfour⟩ := hmos 4 (by decide)
  have hground := h₂ y ((le_max_right ..).trans hy') hret
  refine ⟨x₁, C, hC, ?_⟩
  intro T S β k m hK hS hfl x n hx hn f hnorm B U htail
  have hresp := hS.isAdmissible k le_rfl
  have hparams : (S.setup k).responseParams = Kr := (hS.params_eq k).trans hK
  have hKfit : Kr.Admissible (Tb.stepParameters y) := hparams ▸ hresp.params_admissible
  have hCpos : 0 ≤ Kr.C₀ := by
    rw [hKfit.C₀_eq]
    linarith only [hfit.a_ge, hKfit.N₀_nonneg, hKfit.Kc_ge]
  have hscore := hfour T S β k m f hK hS hfl hx hn.2
  apply terminal_bad_second_moment _ B _ (fun w => scoreMeanOver S f k n (stageState T k n w))
    (by positivity) _ hscore htail
  have hlive := ((hground β T S k hK hS hfl).2 n hn).1 k le_rfl
  filter_upwards [hlive] with w hw
  apply YangMills.DeltaSharedProofs.p501280 S f k n hCpos hresp.price.nonneg (stageState T k n w)
  intro z
  have hb := hresp.bounds.size_hull n hn z _ _ _ hw (fineWeight f _)
  rw [hparams] at hb
  have hd := (hS.isFlowStep k le_rfl).depth_eq
  change (T.stage k).depth = k at hd
  have hw' : weightNorm (Tb.stepParameters y).side (T.stage k).depth (fineWeight f (fineSide (Tb.stepParameters y).side (T.stage k).depth n)) ≤ 1 := by rw [hd]; exact hnorm
  have hs : 0 ≤ siteScore (S.setup k).score (stageState T k n w).2.1 (stageState T k n w).2.2 z := by
    unfold siteScore
    split_ifs
    · exact hresp.price.nonneg _
    · exact le_rfl
  exact hb.trans (mul_le_of_le_one_right (add_nonneg hCpos hs) hw')

theorem measurable_score_sample {Tb : ParameterAssignment} {y : ℝ}
    (hSt : StageStatesMeasurableStatement) (hfit : (Tb.stepParameters y).Admissible)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) (k n : ℕ) [NeZero n] (g : FinePlaquetteFunction) (hs : Measurable (S.setup k).score) :
    Measurable fun u : MarkedSample (Tb.stepParameters y) k n => scoreMeanOver S g k n (stageState T k n u) := by
  have hsig : Measurable fun q : (Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω)) =>
      meanSiteScore (S.setup k).score (functionSites (Tb.stepParameters y).side g k n) q.1 q.2 := by
    refine fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun Y => ?_
    have hY : Measurable fun ω : Y → (T.stage k).labels.Ω => meanSiteScore (S.setup k).score (functionSites (Tb.stepParameters y).side g k n) Y ω := by
      unfold meanSiteScore
      refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun z _ => ?_))
      by_cases hz : z ∈ Y
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (S.setup k).score Y ω z) = fun ω => (S.setup k).score (ω ⟨z, hz⟩) := by
          funext ω
          simp [siteScore, hz]
        rw [e]
        exact hs.comp (measurable_pi_apply _)
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (S.setup k).score Y ω z) = fun _ => 0 := by
          funext ω
          simp [siteScore, hz]
        rw [e]
        exact measurable_const
    exact hY ht
  have h2 : Measurable fun u : MarkedSample (Tb.stepParameters y) k n => (stageState T k n u).2 :=
    measurable_snd.comp (hSt (Tb.stepParameters y) hfit T k n)
  exact hsig.comp h2

/-- The terminal score factor multiplying the two-observable separation error
is polynomial in the running coupling and logarithm under the actual marked law. -/
theorem score_product_at_flow :
    AtResponseParameters fun Tb Kr y => ∃ x₁ C : ℝ, 1 ≤ C ∧
      ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ),
        S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor (Tb.stepParameters y) β k →
        let x := ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k
        let n := 2 * (Tb.stepParameters y).side ^ m
        x₁ ≤ x → (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ n →
        ∀ f h : FinePlaquetteFunction,
          (∫⁻ w, ENNReal.ofReal |scoreMeanOver S f k n (stageState T k n w) *
              scoreMeanOver S h k n (stageState T k n w)| ∂(markedSampleLaw T β k n)) ≤
            ENNReal.ofReal (2 * (C * (clusterRange x : ℝ) ^ 4 * Real.log x) ^ 2) := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, one⟩ := TheStatementsProvedTogether.meanScore_moments a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hodd hL Tb hTa hTL hD hcs hOn hrt hC Kr
  obtain ⟨y₁, h₁⟩ := one L hodd hL Tb hTa hTL hD hcs hOn hrt hC Kr
  refine ⟨max y₁ Tb.floorMin, ?_⟩
  intro y hy hret
  have hfit := hD.fits y ((le_max_right _ _).trans hy)
  obtain ⟨x₁, hmos⟩ := h₁ y ((le_max_left ..).trans hy) hret
  obtain ⟨C, hC, htwo⟩ := hmos 2 (by decide)
  refine ⟨x₁, C, hC, ?_⟩
  intro T S β k m hK hS hfl x n hx hn f h
  rw [two_mul]
  apply terminal_score_product _ _ _ _ (sq_nonneg _) (sq_nonneg _)
    (htwo T S β k m f hK hS hfl hx hn) (htwo T S β k m h hK hS hfl hx hn)
  exact measurable_score_sample TheStatementsProvedTogether.chain_states_measurable hfit S k n f
    (hS.isAdmissible k le_rfl).price.borel

end YangMills.Formulation




