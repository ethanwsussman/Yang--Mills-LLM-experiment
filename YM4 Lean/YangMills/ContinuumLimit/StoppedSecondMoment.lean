import YangMills.ContinuumLimit.MarkedScoreMoments
import YangMills.ContinuumLimit.ResponseAtSmallCurvature
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace YangMills.Formulation
open Construction TorusFields TorusLumps WeightedResponses FreeEnergies ResponseInTheExpansion
  RenormalizationStepParameters TheStatementsProvedTogether

theorem responseTable_and {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hp : AtResponseParameters P) (hq : AtResponseParameters Q) :
    AtResponseParameters fun T R y => P T R y ∧ Q T R y := by
  intro a ha
  obtain ⟨L₁,r₁,C₁,hr₁,one⟩ := hp a ha
  obtain ⟨L₂,r₂,C₂,hr₂,two⟩ := hq a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL T hTa hTL hD hcs hOn hrt hC K
  obtain ⟨y₁,h₁⟩ := one L hodd ((le_max_left ..).trans hL) T hTa hTL hD hcs hOn
    (hrt.trans (min_le_left ..)) ((le_max_left ..).trans hC) K
  obtain ⟨y₂,h₂⟩ := two L hodd ((le_max_right ..).trans hL) T hTa hTL hD hcs hOn
    (hrt.trans (min_le_right ..)) ((le_max_right ..).trans hC) K
  exact ⟨max y₁ y₂, fun y hy hret => ⟨h₁ y ((le_max_left ..).trans hy) hret,
    h₂ y ((le_max_right ..).trans hy) hret⟩⟩

theorem responseTable_of_family {P : ParameterAssignment → ℝ → Prop}
    (h : HoldsOnParameterFamilies P) : AtResponseParameters fun T _ y => P T y := by
  intro a ha
  obtain ⟨L,r,C,hr,H⟩ := h a ha
  refine ⟨L,r,C,hr,?_⟩
  intro L hodd hL T hTa hTL hD hcs hOn hrt hC K
  obtain ⟨y₀,hy⟩ := H L hodd hL T hTa hTL hD hcs hOn hrt hC
  exact ⟨y₀, fun y h₀ hE => hy y h₀ hE.returns_at hE.wilson_expansion⟩

theorem responseTable_map {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (h : AtResponseParameters P) (imp : ∀ T R y, (T.stepParameters y).Admissible → P T R y → Q T R y) :
    AtResponseParameters Q := by
  intro a ha
  obtain ⟨L,r,C,hr,H⟩ := h a ha
  refine ⟨L,r,C,hr,?_⟩
  intro L hodd hL T hTa hTL hD hcs hOn hrt hC K
  obtain ⟨y₀,hy⟩ := H L hodd hL T hTa hTL hD hcs hOn hrt hC K
  exact ⟨max y₀ T.floorMin, fun y h₀ hE => imp T K y (hD.fits y ((le_max_right ..).trans h₀))
    (hy y ((le_max_left ..).trans h₀) hE)⟩

/-- The exceptional event uses exactly the marked hull and torus curvature. -/
def terminalBad {p : StepParameters} (T : StageTower p) (k n : ℕ) [NeZero n] (t : ℝ) :
    Set (MarkedSample p k n) :=
  {w | (stageState T k n w).2.1 ≠ ∅ ∨ ∃ z i j, t < curvature (stageState T k n w).1 z i j}

private theorem good_and_bad_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Set Ω) (R : Ω → ℝ) {G E U : ℝ} (hE : 0 ≤ E)
    (hgood : ∀ᵐ u ∂μ, u ∉ B → |R u| ≤ G)
    (hbad : ∀ B' : Set Ω, μ B' ≤ ENNReal.ofReal (Real.exp (-U)) →
      (∫⁻ u in B', ENNReal.ofReal (R u ^ 2) ∂μ) ≤ ENNReal.ofReal E)
    (hprob : μ B ≤ ENNReal.ofReal (Real.exp (-U))) :
    ∫ u, R u ^ 2 ∂μ ≤ G ^ 2 + E := by
  let C := toMeasurable μ B
  have hC : MeasurableSet C := measurableSet_toMeasurable ..
  have hBC : B ⊆ C := subset_toMeasurable ..
  have hbad' := hbad C (by simpa [C] using hprob)
  have hgood' : (∫⁻ u in Cᶜ, ENNReal.ofReal (R u ^ 2) ∂μ) ≤ ENNReal.ofReal (G ^ 2) := by
    calc _ ≤ ∫⁻ _ in Cᶜ, ENNReal.ofReal (G ^ 2) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hC.compl] with u hu hc
          apply ENNReal.ofReal_le_ofReal
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hu (fun h => hc (hBC h))) 2
      _ ≤ ∫⁻ _, ENNReal.ofReal (G ^ 2) ∂μ := setLIntegral_le_lintegral _ _
      _ = _ := by simp
  have hall : (∫⁻ u, ENNReal.ofReal (R u ^ 2) ∂μ) ≤ ENNReal.ofReal (G ^ 2 + E) := by
    rw [← lintegral_add_compl _ hC, ENNReal.ofReal_add (sq_nonneg _) hE, add_comm (ENNReal.ofReal (G^2))]
    exact add_le_add hbad' hgood'
  by_cases hm : AEStronglyMeasurable (fun u => R u ^ 2) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => sq_nonneg _) hm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hall
  · rw [integral_non_aestronglyMeasurable hm]; positivity

set_option maxHeartbeats 400000 in
theorem stopped_terminal_second_moment :
    AtResponseParameters fun Tb Kr y => let p := Tb.stepParameters y
      ∃ C c D x₀ : ℝ, 0 < c ∧ 1 ≤ D ∧
      ∀ (β : ℝ) (k m r : ℕ) (T : StageTower p) (S : ScoredStageTower T)
        (f : FinePlaquetteFunction) (t U : ℝ),
        let n := 2 * p.side ^ m
        let x := flowCouplings p β k
        S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor p β k → x₀ ≤ x →
        IsBlockTorusSide p n → p.n₀ ≤ n → (clusterRange x : ℝ) / 64 ≤ r →
        1 ≤ r → 4*r+4 ≤ n → 0 ≤ t → t ≤ 1 → t < p.threshold → 6*((r:ℝ)+1)*t ≤ 1 →
        weightNorm p.side k (fineWeight f (fineSide p.side k n)) ≤ 1 →
        (markedSampleLaw T β k n) (terminalBad T k n t) ≤ ENNReal.ofReal (Real.exp (-U)) →
        ∫ w, fittedResponse S f k n (stageState T k n w) ^ 2 ∂(markedSampleLaw T β k n) ≤
          ((n:ℝ)^4 * (|C| * (t^3+t+Real.exp (-(c*r))) + Real.exp (-(p.decayRate*r))))^2 +
          ((Kr.C₀+1)*((functionSites p.side f k n).card:ℝ))^2 *
            (1 + (D*(clusterRange x:ℝ)^4 * Real.log x)^4) * Real.exp (-U/2) := by
  apply responseTable_map (responseTable_and (responseTable_of_family GoodTerminal.fittedSuppression)
    (responseTable_and (responseTable_of_family scored_tower_coeffs_eq_chain)
    (responseTable_and flow_states_are_ground_states fitted_response_bad_at_flow)))
  intro Tb Kr y hfit data
  obtain ⟨hgood, hcoeff, hgr, x₂,D,hD,hbad⟩ := data
  intro p
  -- A scored tower following the flow witnesses response-parameter admissibility.
  by_cases hKr : Kr.Admissible (Tb.stepParameters y)
  · obtain ⟨C,c,x₁,hc,good⟩ := hgood Kr hKr
    refine ⟨C,c,D,max x₁ x₂,hc,hD,?_⟩
    intro β k m r T S f t U n x hK hS hfl hx hside hn hrng hr hrn ht ht1 hthr hrt hweight htail
    obtain ⟨hprob,-⟩ := two_point_function_total_covariance _ hfit hfit.depth_lt T
      hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k n
    let : IsProbabilityMeasure (markedSampleLaw T β k n) := hprob
    apply good_and_bad_second_moment _ (terminalBad T k n t) _ (by positivity) _ _ htail
    · have hlive := ((hgr β T S k hK hS hfl).2 n hside).1 k le_rfl
      have hc' := hcoeff β k T S hS
      rw [hK] at hc'
      have hEq : (T.stage k).coupling = x := (hS.isFlowStep k le_rfl).coupling_eq
      filter_upwards [hlive] with w hw hgoodw
      obtain ⟨hempty, hcurv⟩ : (stageState T k n w).2.1 = ∅ ∧
          ∀ z i j, curvature (stageState T k n w).1 z i j ≤ t := by
        simpa [terminalBad, not_or, not_lt] using hgoodw
      change IsLiveState p (T.stage k).coupling (T.stage k).labelWeight (stageState T k n w).1 (stageState T k n w).2.1 (stageState T k n w).2.2 at hw
      generalize hq : stageState T k n w = q at hw hempty hcurv ⊢
      rcases q with ⟨W,Y,ω⟩
      change Y = ∅ at hempty
      subst Y
      exact good β k n r T S f W ω t hS hfl ((le_max_left ..).trans hx) hc' hside hn
        (fun z i j _ => (hcurv z i j).trans_lt hthr) (lt_of_le_of_lt ht hthr) hw
        (by simpa only [hEq] using hrng) hr hrn ht ht1 hrt hcurv hweight
    · exact fun B hb => hbad T S β k m hK hS hfl ((le_max_right ..).trans hx) hside f hweight B U hb
  · refine ⟨0,1,D,x₂,zero_lt_one,hD,?_⟩
    intro β k m r T S f t U n x hK hS
    have hh := (hS.isAdmissible k le_rfl).params_admissible
    rw [(hS.params_eq k).trans hK] at hh
    exact (hKr hh).elim


theorem stopped_score_real_moment :
    AtResponseParameters fun Tb Kr y => let p := Tb.stepParameters y
      ∃ x₀ D : ℝ, 1 ≤ D ∧
      ∀ (T : StageTower p) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ),
        S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor p β k →
        let x := flowCouplings p β k
        let n := 2 * p.side ^ m
        x₀ ≤ x → p.side * p.n₀ ≤ n → ∀ f h : FinePlaquetteFunction,
          let Q := fun u => scoreMeanOver S f k n (stageState T k n u) * scoreMeanOver S h k n (stageState T k n u)
          Integrable Q (markedSampleLaw T β k n) ∧
          (∫ u, Q u ∂(markedSampleLaw T β k n)) ≤ 2 * (D * (clusterRange x : ℝ)^4 * Real.log x)^2 := by
  apply responseTable_map score_product_at_flow
  intro Tb Kr y hfit H p
  obtain ⟨x₀,D,hD,h⟩ := H
  refine ⟨x₀,D,hD,?_⟩
  intro T S β k m hp hs hf x n hx hn f g Q
  let μ := markedSampleLaw T β k n
  have hm (j : FinePlaquetteFunction) := measurable_score_sample chain_states_measurable hfit S k n j
    (hs.isAdmissible k le_rfl).price.borel
  have hQ : Measurable Q := (hm f).mul (hm g)
  have hbd := h T S β k m hp hs hf hx hn f g
  set ub := 2 * (D * (clusterRange x : ℝ)^4 * Real.log x)^2
  have hfin : (∫⁻ u, ENNReal.ofReal |Q u| ∂μ) < ⊤ := hbd.trans_lt ENNReal.ofReal_lt_top
  have hiabs : Integrable (fun u => |Q u|) μ := ⟨hQ.abs.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall fun u => abs_nonneg (Q u))).2 hfin⟩
  have hi : Integrable Q μ := (integrable_norm_iff hQ.aestronglyMeasurable).mp hiabs
  refine ⟨hi, (integral_mono hi hiabs (fun u => le_abs_self (Q u))).trans ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => abs_nonneg _) hQ.abs.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by dsimp [ub]; positivity) hbd

end YangMills.Formulation




