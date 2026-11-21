import YangMills.Construction.CellOfTheFlow.MomentOfTheMajorantProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOfTheTopLevel
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheScoresOfTheCopiesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep RenormalizationStepParameters StepSettings
private theorem le_clusterRange_of_pow_le {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem sum_siteScore_univ {n : ℕ} [NeZero n] {Ω : Type} (s : Ω → ℝ) (Y : Finset (TorusSite n))
    (ω : Y → Ω) : ∑ z : TorusSite n, siteScore s Y ω z = ∑ y : Y, s (ω y) := by apply _root_.YangMills.SharedProofs.p15197 <;> assumption
private theorem siteScore_nonneg {n : ℕ} {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    (Y : Finset (TorusSite n)) (ω : Y → Ω) (z : TorusSite n) : 0 ≤ siteScore s Y ω z := by apply _root_.YangMills.SharedProofs.p42827 <;> assumption
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem mul_two_pow_mul_exp_le {D Z C l E K N : ℝ} {M : ℕ} (hM : (M : ℝ) = N) (hN : 0 ≤ N)
    (hZ : 0 < Z) (hb : Real.log D - (C + 6 * l) * N ≤ Real.log Z) (hl : 0 ≤ l) (hE : 0 ≤ E)
    (hK : K = |C| + Real.log 2 + 2 * E + 6) :
    D * 2 ^ M * Real.exp (2 * E * M) ≤ Z * Real.exp (K * (1 + l) * N) := by apply _root_.YangMills.SharedProofs.p49832 <;> assumption
theorem topLevelScoreBoundStatement_holds
    (hD : StageDensity.stageStateDensityStatement)
    (hS : ResponseInTheExpansion.ScoredMassStatement) (hB : freeEnergyLowerBound) (hM : flowFunctionalIntegral)
    (hBo : ResponseInTheExpansion.StageStatesMeasurableStatement) : topLevelScoreBoundStatement := by
  intro a ha
  obtain ⟨L₁, rtD, hrtD, hD'⟩ := hD a ha
  obtain ⟨rtB, hrtB, hB'⟩ := hB
  refine ⟨L₁, fun c => min (rtD c) (rtB c), 0, fun c => lt_min (hrtD c) (hrtB c), ?_⟩
  intro L hL hLL Tb hTa hTL hAdm hCold _ hrt _ Kr
  obtain ⟨yD, hyD⟩ := hD' L hL hLL Tb hTa hTL hAdm (hrt.trans (min_le_left _ _))
  obtain ⟨yB, hyB⟩ := hB' Tb hAdm hCold (hrt.trans (min_le_right _ _))
  refine ⟨max (max yD yB) (max Tb.floorMin (((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100)), ?_⟩
  intro y hy hexpn
  have hyD' : yD ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyB' : yB ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyT : Tb.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyk : ((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hadm : (Tb.stepParameters y).Admissible := hAdm.fits y hyT
  obtain ⟨C, hC⟩ := hyB y hyB' hexpn
  have hDens := hyD y hyD' hexpn.returns_at hexpn.wilson_expansion
  have hE1 : 1 ≤ (Tb.stepParameters y).E := hadm.E_ge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  refine ⟨|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6, by have := abs_nonneg C; linarith, ?_⟩
  intro β T S tp n _ _ hOn hReach hn
  have hstep := hOn.isFlowStep tp le_rfl
  have htower : IsTowerAtParameters Tb y T β tp := by
    refine ⟨hOn.startsAtWilson, fun j hj => ?_, fun j hj => (hOn.isFlowStep j hj).onFamily⟩
    rcases Nat.lt_or_ge j (tp + 1) with h | h
    · exact (hOn.isFlowStep j (Nat.lt_succ_iff.mp h)).coupling_eq
    · obtain rfl : j = tp + 1 := le_antisymm hj h
      exact hstep.nextCoupling_eq
  obtain ⟨⟨hc, hh⟩, -, -⟩ := hstep.onFamily.isStep
  have hxy : y ≤ (T.stage tp).coupling := hstep.onFamily.le_coupling
  have hy1 : (1 : ℝ) ≤ y := hadm.y₁_ge
  have hx0 : 0 < (T.stage tp).coupling := by linarith
  have hfl : 4 * (Tb.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange (T.stage tp).coupling :=
    le_clusterRange_of_pow_le (hyk.trans hxy)
  have hprice := (hOn.isAdmissible tp le_rfl).price
  have hup := hS (Tb.stepParameters y) (T.stage tp).depth (T.stage tp).coupling (T.stage tp).functional
    (T.stage tp).density (T.stage tp).labels (T.stage tp).labelWeight (T.stage tp).clusterFactor
    (T.stage tp).siteDensity (S.setup tp).score hadm hadm.E_ge hx0 hfl hc hh hprice n hn
  obtain ⟨hDm, hDpos, ⟨Cb, hCb⟩, hDmass, hZ⟩ := hM (Tb.stepParameters y) hadm β tp n
  have hZ0 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) ≠ 0 := by
    simpa using hZ
  have hZt : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfun : (T.stage tp).functional = flowFunctional (Tb.stepParameters y) β tp := hstep.functional_eq
  have hprob : IsProbabilityMeasure (markedSampleLaw T β tp n) := by
    have h1 := hDens T β tp n htower hOn.marksMeasurable hn (fun _ => 1) measurable_const
    have hint : Integrable (flowFunctional (Tb.stepParameters y) β tp n) (fieldHaar n) :=
      Integrable.of_bound hDm.aestronglyMeasurable Cb (Filter.Eventually.of_forall fun V => by
        rw [Real.norm_eq_abs, abs_of_pos (hDpos V)]
        exact hCb V)
    have h2 : ∫⁻ W, ENNReal.ofReal (flowFunctional (Tb.stepParameters y) β tp n W) ∂(fieldHaar n) =
        ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) := by
      rw [← hDmass, ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun V => (hDpos V).le)]
    have h4 : ∫⁻ _u, (1 : ENNReal) ∂(markedSampleLaw T β tp n) = markedSampleLaw T β tp n Set.univ := by simp
    have h3 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) * markedSampleLaw T β tp n Set.univ =
        ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) := by
      rw [← h4]
      refine h1.trans ((lintegral_congr fun W => ?_).trans h2)
      simp only [one_mul]
      rw [← hfun]
      exact hh.sum n hn W
    constructor
    have h5 : (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n))⁻¹ *
        (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) * markedSampleLaw T β tp n Set.univ) =
        (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n))⁻¹ *
          ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) := by
      rw [h3]
    rwa [← mul_assoc, ENNReal.inv_mul_cancel hZ0 hZt, one_mul] at h5
  have hsig : Measurable fun p : (Σ Y : Finset (TorusSite n), (Y → (T.stage tp).labels.Ω)) =>
      ∑ z : TorusSite n, siteScore (S.setup tp).score p.1 p.2 z := by
    refine measurable_sigma_of_forall fun Y => ?_
    simp only [sum_siteScore_univ]
    exact Finset.measurable_sum _ fun i _ => hprice.borel.comp (measurable_pi_apply i)
  have hsum : Measurable fun q : StageState T tp n =>
      ∑ z : TorusSite n, siteScore (S.setup tp).score q.2.1 q.2.2 z :=
    hsig.comp measurable_snd
  obtain ⟨G, hGdef⟩ : ∃ G : StageState T tp n → ENNReal, ∀ q, G q =
      ENNReal.ofReal (Real.exp (∑ z : TorusSite n, siteScore (S.setup tp).score q.2.1 q.2.2 z)) :=
    ⟨_, fun _ => rfl⟩
  have hG : Measurable G := by
    have : G = fun q =>
        ENNReal.ofReal (Real.exp (∑ z : TorusSite n, siteScore (S.setup tp).score q.2.1 q.2.2 z)) :=
      funext hGdef
    rw [this]
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hsum)
  have hstate : Measurable (stageState T tp n) := hBo _ hadm T tp n
  have hf : Measurable fun u => Real.exp (S.totalScore tp n u) :=
    Real.measurable_exp.comp (hsum.comp hstate)
  have hW : ∀ W : TorusField n, (open Classical in
      ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage tp).coupling) W),
        ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage tp).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage tp).labels.μ)) ≤
      ENNReal.ofReal ((T.stage tp).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
    intro W
    refine le_trans (le_of_eq ?_) (hup W)
    refine Finset.sum_congr rfl fun Y _ => lintegral_congr fun ω => ?_
    rw [hGdef]
    simp only [sum_siteScore_univ]
    rw [ENNReal.ofReal_mul' (Real.exp_nonneg _), mul_comm]
  have hmain : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) *
      ∫⁻ u, G (stageState T tp n u) ∂(markedSampleLaw T β tp n) ≤
      ENNReal.ofReal ((T.stage tp).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
    refine (le_of_eq (hDens T β tp n htower hOn.marksMeasurable hn G hG)).trans ?_
    refine (lintegral_mono hW).trans ?_
    simp
  have hcard : ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 := by
    simp [TorusSite, ZMod.card]
  have hl : 0 ≤ Real.log (flowCoupling (Tb.stepParameters y) β tp) :=
    Real.log_nonneg (hadm.y₁_ge.trans (hReach tp le_rfl))
  have hnum := mul_two_pow_mul_exp_le (K := |C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) hcard
    (by positivity) hZ (hC β tp hReach n hn) hl (by linarith) rfl
  have htriv : (T.stage tp).functional n (trivialField n) =
      flowFunctionalAtTrivial (Tb.stepParameters y) β tp n := by
    rw [hfun]
    rfl
  rw [← htriv] at hnum
  have hI : ∫⁻ u, G (stageState T tp n u) ∂(markedSampleLaw T β tp n) ≤
      ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
        (1 + Real.log (flowCoupling (Tb.stepParameters y) β tp)) * (n : ℝ) ^ 4)) := by
    have h2 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) *
        ∫⁻ u, G (stageState T tp n u) ∂(markedSampleLaw T β tp n) ≤
        ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n) *
          ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
            (1 + Real.log (flowCoupling (Tb.stepParameters y) β tp)) * (n : ℝ) ^ 4)) := by
      rw [← ENNReal.ofReal_mul hZ.le]
      exact hmain.trans (ENNReal.ofReal_le_ofReal hnum)
    have h3 := mul_le_mul_right h2 (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β tp n))⁻¹
    rwa [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hZ0 hZt, one_mul, one_mul] at h3
  have hGf : ∀ u, ENNReal.ofReal (Real.exp (S.totalScore tp n u)) = G (stageState T tp n u) := fun u => by
    rw [hGdef]
    rfl
  have hI' : ∫⁻ u, ENNReal.ofReal (Real.exp (S.totalScore tp n u)) ∂(markedSampleLaw T β tp n) ≤
      ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
        (1 + Real.log (flowCoupling (Tb.stepParameters y) β tp)) * (n : ℝ) ^ 4)) := by
    simp only [hGf]
    exact hI
  have hnn : ∀ u, 0 ≤ S.totalScore tp n u := fun u =>
    Finset.sum_nonneg fun z _ => siteScore_nonneg hprice.nonneg _ _ z
  have hint : Integrable (fun u => Real.exp (S.totalScore tp n u)) (markedSampleLaw T β tp n) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)]
    exact hI'.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_, ?_⟩
  · have h1 := integral_mono (integrable_const (1 : ℝ)) hint fun u => Real.one_le_exp (hnn u)
    simpa [ScoredStageTower.expScoreMean] using h1
  · unfold ScoredStageTower.expScoreMean
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
      hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hI'
end YangMills.Construction.FreeEnergies
end
