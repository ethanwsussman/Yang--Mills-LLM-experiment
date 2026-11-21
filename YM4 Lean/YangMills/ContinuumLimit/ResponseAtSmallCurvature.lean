import YangMills.Construction.TheStatementsProvedTogether.FromTheFourPointLawOnTheWindowProof
import YangMills.Construction.TheStatementsProvedTogether.FromThirdDerivativesAndSizesProof
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithmsProof
noncomputable section
open scoped Quaternion
namespace YangMills.GoodTerminal
open Construction TorusLumps TorusFields WeightedResponses ResponseInTheExpansion
open ColdStepAtMirrorFrames.BlockOffsets (distFromOne)
open BlockAverages (imaginaryComponent)

theorem axialLogSmall (p : StepParameters) {n r : ℕ} [NeZero n] (z : TorusSite n)
    (W : TorusField n) {t : ℝ} (hn : 2 * (r + 1) + 2 < n) (ht : 0 ≤ t)
    (hr : 6 * ((r : ℝ) + 1) * t ≤ 1) (hW : ∀ y μ ν, curvature W y μ ν ≤ t) :
    ∀ b : TorusBond n, b.1 ∈ supBall z r →
      ‖(LumpContours.minimalLog (gaugeTransform (axialGaugeAt p W z) W b) : Quaternion ℝ)‖ ≤ 1 := by
  classical
  intro b hb
  have hx : supDist b.1 z ≤ r := by
    exact_mod_cast (Finset.mem_filter.mp hb).2
  have hy : supDist (b.1 + unitStep n b.2) z ≤ r + 1 := by
    have h1 := supDist_add_unitStep_le b.1 b.2
    have h2 := supDist_triangle (b.1 + unitStep n b.2) b.1 z
    rw [supDist_comm (b.1 + _) b.1] at h2
    omega
  have h := TheStatementsProvedTogether.axial_gauge_path_bounds.2.1 p n z W (r+1) t hn ht
    (fun y μ ν _ _ _ _ _ => hW y μ ν) b (by omega) hy
  push_cast at h
  have hd : distFromOne (gaugeTransform (axialGaugeAt p W z) W b) < 1 := by linarith
  exact (YangMills.SharedProofs.p16086 _ hd).trans (by linarith)

theorem coldSites :
    HoldsOnParameterFamilies fun Tb y => ∀ Kr : ResponseParameters,
      Kr.Admissible (Tb.stepParameters y) → ∃ C c x₀ : ℝ, 0 < c ∧
      ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ) (n : ℕ) [NeZero n],
        (∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j) →
        x₀ ≤ flowCouplings (Tb.stepParameters y) β k →
        IsChainResponseCoeff (Tb.stepParameters y) Kr β k al → |al k| ≤ 2 →
        (Tb.stepParameters y).n₀ ≤ n →
        ∀ (z : TorusSite n) (h : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n)),
          weightSup h ≤ 1 → weightLipschitz (Tb.stepParameters y).side k h ≤ 1 →
          ∀ (W : TorusField n) (r : ℕ) (t : ℝ), IsCold (Tb.stepParameters y).threshold W →
          1 ≤ r → 4 * r + 4 ≤ n → 0 ≤ t → t ≤ 1 →
          6 * ((r : ℝ) + 1) * t ≤ 1 → (∀ y μ ν, curvature W y μ ν ≤ t) →
            |centeredResponse (coldResponseChain (Tb.stepParameters y) β
              (flowCouplings (Tb.stepParameters y) β) al k) n z W h| ≤
              C * (t ^ 3 + t + Real.exp (-(c * r))) := by
  classical
  intro a ha
  obtain ⟨L₀,rt₀,C₀,hrt,H⟩ := FourPointWindowLaw.curved_field_response a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L ho hL T hTa hTL hD hC hO hrtT hder
  obtain ⟨y₀, hy⟩ := H L ho hL T hTa hTL hD hC hO hrtT hder
  refine ⟨y₀, ?_⟩
  intro y hyy hret hwil Kr hk
  obtain ⟨C,c,x₀,hc,hh⟩ := hy y hyy hret hwil Kr hk
  refine ⟨C,c,x₀,hc,?_⟩
  intro β k al n _ hfloor hx hcoeff hα hn z h hsup hlip W r t hW hr hn' ht ht1 hsmall hcurv
  obtain ⟨κ, _, _, _, he⟩ := hh β k al n hfloor hx hcoeff hα hn z h hsup hlip
  let p := T.stepParameters y
  have hb := axialLogSmall p z W (r := r) (by omega) ht hsmall hcurv
  have hv := he W (axialGaugeAt p W z) (fun _ => 0) (r:ℝ) 1 t hW
    (by exact_mod_cast hr) (by exact_mod_cast hn') (by norm_num) le_rfl ht ht1
    (fun b hmem => ⟨by simp, by simpa using hb b hmem⟩)
    (fun u _ μ ν => hcurv u μ ν) (fun q _ => by simpa [lieFormCurl] using ht)
  have hc0 (i : Fin 3) : imaginaryComponent i (0 : BlockAverages.imaginaryQuaternions) = 0 := by
    fin_cases i <;> rfl
  simpa [lieFormCurl, hc0] using hv
open FreeEnergies

/-- On an empty live hull, compare each actual fitted insertion with its cold value on
the same field.  The comparison radius can be any embedded ball above the cluster scale. -/
theorem goodFittedFromSites {p : StepParameters} {T : StageTower p} (S : ScoredStageTower T)
    (k n r : ℕ) [NeZero n] (f : FinePlaquetteFunction) (W : TorusField n)
    (ω : (∅ : Finset (TorusSite n)) → (T.stage k).labels.Ω)
    (ha : (S.setup k).IsAdmissible) (hside : IsBlockTorusSide p n) (hn : p.n₀ ≤ n)
    (hW : IsCold p.threshold W)
    (hlive : IsLiveState p (T.stage k).coupling (T.stage k).labelWeight W ∅ ω)
    (hr : (clusterRange (T.stage k).coupling : ℝ) / 64 ≤ r) (hbox : 2*r+2 < n)
    (B : ℝ) (hsite : ∀ z ∈ functionSites p.side f k n,
      |centeredResponse (S.setup k).cold n z W (fineWeight f _)| ≤ B) :
    |fittedResponse S f k n (W, ⟨∅,ω⟩)| ≤
      ((functionSites p.side f k n).card:ℝ) * (B + Real.exp (-(p.decayRate*r)) *
        weightNorm p.side (T.stage k).depth (fineWeight f (fineSide p.side (T.stage k).depth n))) := by
  classical
  let h := fineWeight f (fineSide p.side (T.stage k).depth n)
  have hpoint z (hz : z ∈ functionSites p.side f k n) :
      |centeredHullResponse (S.setup k).cold (S.setup k).hull n z W ∅ ω h| ≤
        B + Real.exp (-(p.decayRate*r)) * weightNorm p.side (T.stage k).depth h := by
    have hcmp := ha.bounds.forget_cold n n hside hn W W ∅ ω ω z z r h h hlive hW hr
      (by
        refine ⟨hbox,hbox,fun _ _ => rfl,fun _ _ => Iff.rfl,?_,?_⟩
        · intro a _ h₁
          exact False.elim (Finset.notMem_empty _ h₁)
        · exact fun h => False.elim (by simpa using h))
      (fun _ _ _ _ _ => rfl)
    simp [siteScore] at hcmp
    calc |centeredHullResponse (S.setup k).cold (S.setup k).hull n z W ∅ ω h| ≤
          |centeredHullResponse (S.setup k).cold (S.setup k).hull n z W ∅ ω h -
            centeredResponse (S.setup k).cold n z W h| + |centeredResponse (S.setup k).cold n z W h| := by
            simpa using (abs_sub_le (centeredHullResponse (S.setup k).cold (S.setup k).hull n z W ∅ ω h)
              (centeredResponse (S.setup k).cold n z W h) 0)
      _ ≤ _ := by linarith [hsite z hz]
  unfold fittedResponse
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpoint).trans_eq
    (by simp [nsmul_eq_mul,h,mul_add]))
private theorem familyAnd {A B : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (ha : HoldsOnParameterFamilies A) (hb : HoldsOnParameterFamilies B) :
    HoldsOnParameterFamilies fun T y => A T y ∧ B T y := by
  intro a h
  obtain ⟨l,r,c,hr,H⟩ := ha a h
  obtain ⟨l',r',c',hr',H'⟩ := hb a h
  refine ⟨max l l',fun t => min (r t) (r' t),max c c',fun t => lt_min (hr t) (hr' t),?_⟩
  intro L odd hL T hTa hTL had hC hO hrt hcb
  obtain ⟨q,hq⟩ := H L odd ((le_max_left _ _).trans hL) T hTa hTL had hC hO
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hcb)
  obtain ⟨q',hq'⟩ := H' L odd ((le_max_right _ _).trans hL) T hTa hTL had hC hO
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hcb)
  exact ⟨max q q',fun y hy hret hw => ⟨hq y ((le_max_left _ _).trans hy) hret hw,
    hq' y ((le_max_right _ _).trans hy) hret hw⟩⟩

theorem fittedSuppression :
    HoldsOnParameterFamilies fun Tb y => let p := Tb.stepParameters y
      ∀ Kr : ResponseParameters, Kr.Admissible p → ∃ C c x₀ : ℝ, 0 < c ∧
      ∀ (β : ℝ) (k n r : ℕ) [NeZero n] (T : StageTower p) (S : ScoredStageTower T)
        (f : FinePlaquetteFunction) (W : TorusField n)
        (ω : (∅ : Finset (TorusSite n)) → (T.stage k).labels.Ω) (t : ℝ),
        S.FollowsFlow β k → (∀ j ≤ k, p.y₁ ≤ flowCouplings p β j) →
        x₀ ≤ flowCouplings p β k → IsChainResponseCoeff p Kr β k S.coeffs →
        IsBlockTorusSide p n → p.n₀ ≤ n → IsCold p.threshold W → 0 < p.threshold →
        IsLiveState p (T.stage k).coupling (T.stage k).labelWeight W ∅ ω →
        (clusterRange (T.stage k).coupling : ℝ) / 64 ≤ r → 1 ≤ r → 4*r+4 ≤ n →
        0 ≤ t → t ≤ 1 → 6 * ((r:ℝ) + 1) * t ≤ 1 → (∀ y μ ν, curvature W y μ ν ≤ t) →
        weightNorm p.side k (fineWeight f (fineSide p.side k n)) ≤ 1 →
        |fittedResponse S f k n (W,⟨∅,ω⟩)| ≤ (n:ℝ)^4 *
          (|C| * (t^3+t+Real.exp (-(c*r))) + Real.exp (-(p.decayRate*r))) := by
  classical
  intro a ha
  obtain ⟨l,rt,cb,hpos,H⟩ := familyAnd coldSites TheStatementsProvedTogether.scored_tower_cold_response_eq a ha
  refine ⟨l,rt,cb,hpos,?_⟩
  intro L odd hL Tb hTa hTL had hC hO hrt hder
  obtain ⟨q,Hq⟩ := H L odd hL Tb hTa hTL had hC hO hrt hder
  refine ⟨q,?_⟩
  intro y hy hrtn hWils
  obtain ⟨hcold,hlink⟩ := Hq y hy hrtn hWils
  dsimp only
  intro Kr hKr
  obtain ⟨C,c,x₀,hc,hbound⟩ := hcold Kr hKr
  refine ⟨C,c,x₀,hc,?_⟩
  intro β k n r _ T S f W ω t hS hfloor hx hcoeff hside hn hW hthr hlive hrng hr hn' ht ht1 hsmall hcurv hweight
  let p := Tb.stepParameters y
  have hd : (T.stage k).depth = k := (hS.isFlowStep k le_rfl).depth_eq
  have hal : |S.coeffs k| ≤ 2 := by
    have hh := abs_le.mp (hS.coeff_near_one k le_rfl)
    change |(S.setup k).coeff| ≤ 2
    exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hnorm :  weightNorm p.side (T.stage k).depth
      (fineWeight f (fineSide p.side (T.stage k).depth n)) ≤ 1 := by
    exact (congrArg (fun v => weightNorm p.side v (fineWeight f (fineSide p.side v n))) hd).le.trans hweight
  let B := |C| * (t^3+t+Real.exp (-(c*r)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfor z : |centeredResponse (S.setup k).cold n z W (fineWeight f _)| ≤ B := by
    have Hcold V (hV : IsCold p.threshold V) := hlink β k T S hS n hn z V hV f
      (fineWeight f (fineSide p.side k n)) (fun _ _ => rfl)
    rw [centeredResponse,Hcold W hW,Hcold _ (YangMills.SharedProofs.p4747 hthr n)]
    have Hhere := hbound β k S.coeffs n hfloor hx hcoeff hal hn z (fineWeight f _)
      ((le_max_left _ _).trans hweight) ((le_max_right _ _).trans hweight) W r t hW hr hn' ht ht1 hsmall hcurv
    exact Hhere.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hf := goodFittedFromSites S k n r f W ω (hS.isAdmissible k le_rfl) hside hn hW hlive hrng
    (by omega) B (fun z _ => hfor z)
  have hcard : ((functionSites p.side f k n).card : ℝ) ≤ (n:ℝ)^4 := by
    have hc : (functionSites p.side f k n).card ≤ Fintype.card (TorusSite n) := Finset.card_le_univ _
    simpa [TorusSite, Fintype.card_pi, Fintype.card_fin, ZMod.card] using (Nat.cast_le (α:=ℝ).mpr hc)
  have he := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-(p.decayRate*r))).le
  exact hf.trans ((mul_le_mul_of_nonneg_left (add_le_add (le_refl B) (he.trans_eq (mul_one _)))
    (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hcard (add_nonneg hB (Real.exp_pos _).le)))
open Filter
open scoped Topology

/-- The deterministic bound vanishes with N = side·q, t = q⁻¹⁶, and r ≥ q/2. -/
theorem goodEnvelope_vanishes (side C c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    Tendsto (fun q : ℝ => (side*q)^4 * (|C| * ((q^16)⁻¹ ^ 3 + (q^16)⁻¹ +
      Real.exp (-(c * (q/2)))) + Real.exp (-(δ * (q/2))))) atTop (𝓝 0) := by
  have hpow (m : ℕ) (hm : 0 < m) : Tendsto (fun q : ℝ => (q^m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := m) hm.ne')
  have hex (b : ℝ) (hb : 0 < b) :
      Tendsto (fun q : ℝ => q^4 * Real.exp (-(b * (q/2)))) atTop (𝓝 0) := by
    have H := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4:ℝ) (b/2) (by positivity)
    convert H using 2 with q
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    congr 2 <;> ring
  have h := (((hpow 44 (by norm_num)).add (hpow 12 (by norm_num))).add (hex c hc)).const_mul |C|
  have h' := (h.add (hex δ hδ)).const_mul (side^4)
  simp only [zero_add, mul_zero] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq
  field_simp <;> ring
end YangMills.GoodTerminal

