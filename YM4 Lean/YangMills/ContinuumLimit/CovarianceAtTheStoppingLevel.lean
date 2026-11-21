import YangMills.ContinuumLimit.StoppedSecondMoment
import YangMills.ContinuumLimit.StoppedErrorBounds
import YangMills.ContinuumLimit.StoppingTorusGeometry
import YangMills.Construction.TheStatementsProvedTogether.FromProductsUpOneStepProof
import YangMills.ContinuumLimit.ReferencePairRescaling
import YangMills.ContinuumLimit.StoppedCovarianceEstimate

namespace YangMills.Construction.ResponseInTheExpansion
open FreeEnergies TheStatementsProvedTogether

/-- The genuine Wilson two-point covariance is bounded by the two fitted-response second
moments and an exponentially small separation error, uniformly in the stopping level. -/
theorem stoppedWilsonCovariance : AtResponseParameters separatedPairCovarianceAt :=
  separatedPairCovarianceAt_of_products circle_rep_properties level_sites_of_function
    markedMoments_below_level two_point_function_total_covariance completed_observables_bounded
    separated_supports_products_multiscale fitted_response_eq_conditional_mean

end YangMills.Construction.ResponseInTheExpansion

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace YangMills.Formulation
open Construction TorusFields TorusLumps WeightedResponses FreeEnergies ResponseInTheExpansion
  RenormalizationStepParameters TheStatementsProvedTogether ReferenceCalibration

private theorem tableTail {F : ParameterAssignment → ℝ → Prop}
    (h : WeightedResponses.HoldsAtAdmissibleParameters F) : AtResponseParameters fun Tb _ y => F Tb y := by
  apply responseTable_of_family
  intro a ha
  obtain ⟨L,r,hr,H⟩ := h a ha
  exact ⟨L,r,0,hr,fun l hl hz T ht hs had _ _ hr' _ => H l hl hz T ht hs had hr'⟩

private theorem tower_of_follows {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {k : ℕ} (hS : S.FollowsFlow β k) : IsTowerAtParameters Tb y T β k := by
  refine ⟨hS.startsAtWilson, fun j hj => ?_, fun j hj => (hS.isFlowStep j hj).onFamily⟩
  by_cases h : j ≤ k
  · exact (hS.isFlowStep j h).coupling_eq
  · obtain rfl : j = k+1 := by omega
    exact (hS.isFlowStep k le_rfl).nextCoupling_eq

set_option maxHeartbeats 650000 in
theorem stopped_covariance_vanishes : AtResponseParameters BranchHot.StageDecayAt := by
  have hCov := stoppedWilsonCovariance
  apply responseTable_map (responseTable_and hCov (responseTable_and stopped_score_real_moment
    (responseTable_and stopped_terminal_second_moment (tableTail stopped_reference_torus_tail))))
  intro Tb Kr y hfit tables
  obtain ⟨⟨A₀,d,hA₀,hd,Hcov⟩, ⟨x₁,E,hE,Hscore⟩, ⟨C,c,D,x₂,hc,hD,Hmom⟩, Htail⟩ := tables
  let p := Tb.stepParameters y
  intro ell A vt hell hA hvt ε hε
  have had : 0 < p.decayRate := div_pos hfit.rt_pos (by norm_num)
  have hnat : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hgzero := GoodTerminal.goodEnvelope_vanishes ell C c p.decayRate hc had
  have hg : ∀ᶠ q : ℝ in atTop,
      ((ell*q)^4*(|C| *(((q^16)⁻¹)^3+(q^16)⁻¹+Real.exp (-(c*(q/2)))) +
          Real.exp (-(p.decayRate*(q/2)))))^2 ≤ ε/2 := by
    have hz := hgzero.pow 2
    simpa only [zero_pow (by decide : 2≠0)] using hz.eventually_le_const (show (0:ℝ)^2 < ε/2 by simpa using half_pos hε)
  have herr := eventually_small_stopped_errors ell Kr.C₀ A₀ D E d A (ε/2) hA₀.le
    (zero_le_one.trans hD) (zero_le_one.trans hE) hd hA (half_pos hε)
  have htail := Htail ell A (by linarith) hA
  have hgeom := stopping_torus_geometry p hA hell hvt hfit.σ_pos
  have hR := eventually_range_fits_reference_torus A 1 hA (by norm_num)
  filter_upwards [hgeom, hnat.eventually htail, hnat.eventually hg, hnat.eventually herr, hnat.eventually hR,
    hnat.eventually_ge_atTop (max x₁ x₂), hnat.eventually_ge_atTop 1] with q hqgeo hqtail hqgood hqerr hqr hqst hq1
  intro T S β k m hK hS hfloor hsize hdiv hlo hhi f hf
  let n := 2*p.side^m
  let x := flowCouplings p β k
  let scale : ℝ := (6/5:ℝ)*q
  let t := ((q:ℝ)^16)⁻¹
  let g (i : Fin 2) := StoppedReference.fineSource p.side k m (f i)
  let μ := markedSampleLaw T β k n
  let Q (i : Fin 2) (w : MarkedSample p k n) := scoreMeanOver S (g i) k n (stageState T k n w)
  let F (i : Fin 2) (w : MarkedSample p k n) := fittedResponse S (g i) k n (stageState T k n w)
  have hq0 : 0 ≤ (q:ℝ) := by positivity
  have hx : (q:ℝ) ≤ x := (le_self_pow₀ hq1 (by decide : 92 ≠ 0)).trans hlo
  have hxm := hqst.trans hx
  obtain ⟨hb,hn0,hr1,hrng,hrpos,hrn,ht0,ht1,hthr,hpatch,_,hsep,hvn⟩ := hqgeo n x hsize hdiv hlo hhi
  obtain ⟨hprob,-⟩ := two_point_function_total_covariance p hfit hfit.depth_lt T hS.isCutoff_bottom
    hS.marksMeasurable β S.coeffs k n
  let : IsProbabilityMeasure μ := hprob
  have hpBad : μ (terminalBad T k n t) ≤ ENNReal.ofReal (Real.exp (-q : ℝ)) :=
    hqtail T β k n hsize ⟨m,rfl⟩ hdiv (tower_of_follows hS) hS.marksMeasurable (inferInstanceAs (IsFiniteMeasure μ)) hlo hhi
  have hscore := Hscore T S β k m hK hS hfloor ((le_max_left ..).trans hxm) hb.2 (g 0) (g 1)
  have hs : Integrable (fun w => Q 0 w * Q 1 w) μ := hscore.1
  have hh := Hcov S hK hS hfloor hb hr1 hsep hvn hf hs
  let good := ((ell*(q:ℝ))^4*(|C| *(t^3+t+Real.exp (-(c*((q:ℝ)/2)))) + Real.exp (-(p.decayRate*((q:ℝ)/2)))))^2
  let bad := ((Kr.C₀+1)*(ell*(q:ℝ))^4)^2 * (1+(D*(clusterRange x:ℝ)^4 * Real.log x)^4) * Real.exp (-(q:ℝ)/2)
  have hKr := (hS.isAdmissible k le_rfl).params_admissible
  rw [(hS.params_eq k).trans hK] at hKr
  have hC₀ : 0 ≤ Kr.C₀ := by rw [hKr.C₀_eq]; linarith only [hfit.a_ge, hKr.N₀_nonneg, hKr.Kc_ge]
  have hm (i : Fin 2) : ∫ w, F i w ^ 2 ∂μ ≤ good + bad := by
    have hbound := Hmom β k m q T S (g i) t q hK hS hfloor ((le_max_right ..).trans hxm) hb hn0 hrng hrpos hrn ht0 ht1 hthr hpatch
      (separatedTestWeightNorm hfit hf hvn i) hpBad
    have hcard : ((functionSites p.side (g i) k n).card : ℝ) ≤ (n:ℝ)^4 := by
      have hh := (functionSites p.side (g i) k n).card_le_univ
      simpa [TorusSite, Fintype.card_pi, Fintype.card_fin, ZMod.card] using (Nat.cast_le (α:=ℝ).mpr hh)
    have hgexp (b : ℝ) (hb : 0 < b) : Real.exp (-(b*(q:ℝ))) ≤ Real.exp (-(b*((q:ℝ)/2))) := by
      apply Real.exp_le_exp.mpr; nlinarith [mul_nonneg hb.le hq0]
    refine hbound.trans (add_le_add ?_ ?_)
    · dsimp only [good]
      rw [← hsize]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add_right (hgexp c hc) _) (abs_nonneg C)) (hgexp p.decayRate had)) (by positivity)
    · dsimp only [bad]
      rw [← hsize]
      gcongr
  have hcov : |cov[curvatureObservable (testWeight p.side k m (f 0)), curvatureObservable (testWeight p.side k m (f 1));
        wilsonLaw β (fineSide p.side k n)]| ≤ good + bad +
      A₀*Real.exp (-(d*scale))*(2*(E*(clusterRange x:ℝ)^4*Real.log x)^2) := by
    refine hh.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left hscore.2 (mul_nonneg hA₀.le (Real.exp_pos _).le)))
    change ((∫ w, F 0 w ^ 2 ∂μ) + ∫ w, F 1 w ^ 2 ∂μ) / 2 ≤ good + bad
    linarith only [hm 0, hm 1]
  have hErr := hqerr x (hq1.trans hx) hhi (by simpa using hqr x hlo hhi)
  change bad + A₀*Real.exp (-(d*scale))*(2*(E*(clusterRange x:ℝ)^4*Real.log x)^2) ≤ ε/2 at hErr
  change good ≤ ε/2 at hqgood
  linarith

end YangMills.Formulation




