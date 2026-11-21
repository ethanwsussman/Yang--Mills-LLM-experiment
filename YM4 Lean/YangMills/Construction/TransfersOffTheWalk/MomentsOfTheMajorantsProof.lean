import YangMills.Construction.FreeEnergiesOfTheFlow.FirstStepsOfTheDraws
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansOfPositiveFunctionsOverTheCases
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOfTheTopLevel
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.StatesAlongTheFlowAreGrounds
import YangMills.Construction.FreeEnergiesOfTheFlow.SumOverTheLevelsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtTheLevelOfTheirRadiusProof
import YangMills.Construction.TransfersOffTheWalk.MomentsOfTheMajorants
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields TorusLumps StepSettings StepGas WeightedResponses ClusterExpansionOfAStep
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_of_sigma_slices {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem siteScore_nonneg {n : ℕ} {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (Y : Finset (TorusSite n))
    (ω : Y → Ω) (z : TorusSite n) : 0 ≤ siteScore s Y ω z := by apply _root_.YangMills.SharedProofs.p42827 <;> assumption
private theorem measurable_meanSiteScore {n : ℕ} {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s)
    (B : Finset (TorusSite n)) :
    Measurable fun q : (Σ Y : Finset (TorusSite n), (Y → Ω)) => ResponseInTheExpansion.meanSiteScore s B q.1 q.2 := by
  refine measurable_of_sigma_slices fun Y => ?_
  unfold ResponseInTheExpansion.meanSiteScore
  refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => ?_))
  unfold siteScore
  by_cases h : y ∈ Y
  · simp only [h, dif_pos]
    exact hs.comp (measurable_pi_apply (⟨y, h⟩ : {x // x ∈ Y}))
  · simp only [h, dif_neg, not_false_iff]
    exact measurable_const
private theorem meanSiteScore_nonneg {n : ℕ} {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    (B Y : Finset (TorusSite n)) (ω : Y → Ω) : 0 ≤ ResponseInTheExpansion.meanSiteScore s B Y ω := by
  unfold ResponseInTheExpansion.meanSiteScore
  have : 0 ≤ (B.card : ℝ)⁻¹ * ∑ y ∈ B, siteScore s Y ω y :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y ω y)
  linarith
private theorem meanSiteScore_le {n : ℕ} [NeZero n] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    {B : Finset (TorusSite n)} (hB : B.Nonempty) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    ResponseInTheExpansion.meanSiteScore s B Y ω ≤ 1 + ∑ z : TorusSite n, siteScore s Y ω z := by
  unfold ResponseInTheExpansion.meanSiteScore
  have h1 : ∑ y ∈ B, siteScore s Y ω y ≤ ∑ z : TorusSite n, siteScore s Y ω z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) fun z _ _ => siteScore_nonneg hs Y ω z
  have h0 : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y ω y
  have hc : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
  have hi : (B.card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have : (B.card : ℝ)⁻¹ * ∑ y ∈ B, siteScore s Y ω y ≤ 1 * ∑ y ∈ B, siteScore s Y ω y :=
    mul_le_mul_of_nonneg_right hi h0
  linarith
private theorem prod_meanSiteScore_le {n p : ℕ} [NeZero n] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    {P : Fin p → Finset (TorusSite n)} (hP : ∀ i, (P i).Nonempty) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    ∏ i, ResponseInTheExpansion.meanSiteScore s (P i) Y ω ≤
      (p.factorial : ℝ) * Real.exp 1 * Real.exp (∑ z : TorusSite n, siteScore s Y ω z) := by
  have hS : 0 ≤ ∑ z : TorusSite n, siteScore s Y ω z := Finset.sum_nonneg fun z _ => siteScore_nonneg hs Y ω z
  have h1 : ∏ i, ResponseInTheExpansion.meanSiteScore s (P i) Y ω ≤
      ∏ _i : Fin p, (1 + ∑ z : TorusSite n, siteScore s Y ω z) :=
    Finset.prod_le_prod (fun i _ => meanSiteScore_nonneg hs _ _ _) fun i _ => meanSiteScore_le hs (hP i) Y ω
  have h2 : ∏ _i : Fin p, (1 + ∑ z : TorusSite n, siteScore s Y ω z) =
      (1 + ∑ z : TorusSite n, siteScore s Y ω z) ^ p := by
    simp
  have h3 := Real.pow_div_factorial_le_exp (1 + ∑ z : TorusSite n, siteScore s Y ω z) (by linarith) p
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  rw [div_le_iff₀ hf] at h3
  rw [h2] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := h3
    _ = _ := by rw [Real.exp_add]; ring
private def meanProduct {T : WeightedResponses.StageTower ℓ} (S : FreeEnergies.ScoredStageTower T) (s n : ℕ) [NeZero n]
    {p : ℕ} (P : Fin p → Finset (TorusSite n)) (u : MarkedSample ℓ s n) : ℝ :=
  ∏ i, ResponseInTheExpansion.meanSiteScore (S.setup s).score (P i) (stageState T s n u).2.1 (stageState T s n u).2.2
private theorem measurable_meanProduct {T : WeightedResponses.StageTower ℓ} (S : FreeEnergies.ScoredStageTower T)
    (s n : ℕ) [NeZero n] {p : ℕ} (P : Fin p → Finset (TorusSite n)) (hs : Measurable (S.setup s).score)
    (hst : Measurable (stageState T s n)) : Measurable (meanProduct S s n P) :=
  Finset.measurable_prod _ fun i _ => ((measurable_meanSiteScore hs (P i)).comp measurable_snd).comp hst
private def CaseMeansPositive (T : WeightedResponses.StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n] : Prop :=
  ∀ F : TorusField n → CaseFunction (T.stage s).toStepSetup n,
    (∀ V W Yt ωt bad b, 0 ≤ F V W Yt ωt bad b) →
    (Measurable fun u : MarkedSample ℓ (s + 1) n =>
      F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1) (stageState T s (n * ℓ.side) u.1).2.1
        (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1) →
    (∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (F u.2.2.1) ∧
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 fun _ _ _ _ _ => 1) →
    AEMeasurable (fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 (F u.2.2.1)) (markedSampleLaw T β (s + 1) n) ∧
    ∫⁻ u, ENNReal.ofReal (F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1) (stageState T s (n * ℓ.side) u.1).2.1
        (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1) ∂(markedSampleLaw T β (s + 1) n) =
      ∫⁻ u, ENNReal.ofReal (caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (F u.2.2.1)) ∂(markedSampleLaw T β (s + 1) n)
private theorem lintegral_meanProduct_step (T : WeightedResponses.StageTower ℓ) (S : FreeEnergies.ScoredStageTower T)
    (β : ℝ) (s n : ℕ) [NeZero n] (hPos : CaseMeansPositive T β s n) {p : ℕ}
    (P : Fin p → Finset (TorusSite (n * ℓ.side))) (P' : Fin p → Finset (TorusSite n)) {E : ℝ} (hE : 0 ≤ E)
    (hnn : ∀ w, 0 ≤ (S.setup s).score w)
    (hm : Measurable (meanProduct S s (n * ℓ.side) P)) (hm' : Measurable (meanProduct S (s + 1) n P'))
    (hfirst : MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)))
    (hbound : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2
        (fun _ Yt ωt _ _ => ∏ i, ResponseInTheExpansion.meanSiteScore (S.setup s).score (P i) Yt ωt) ∧
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (fun _ _ _ _ _ => 1) ∧
      caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2
        (fun _ Yt ωt _ _ => ∏ i, ResponseInTheExpansion.meanSiteScore (S.setup s).score (P i) Yt ωt) ≤
          E * meanProduct S (s + 1) n P' u) :
    ∫⁻ u, ENNReal.ofReal (meanProduct S s (n * ℓ.side) P u) ∂(markedSampleLaw T β s (n * ℓ.side)) ≤
      ENNReal.ofReal E * ∫⁻ u, ENNReal.ofReal (meanProduct S (s + 1) n P' u) ∂(markedSampleLaw T β (s + 1) n) := by
  obtain ⟨-, hEq⟩ := hPos (fun _ _ Yt ωt _ _ => ∏ i, ResponseInTheExpansion.meanSiteScore (S.setup s).score (P i) Yt ωt)
    (fun _ _ _ _ _ _ => Finset.prod_nonneg fun i _ => meanSiteScore_nonneg hnn _ _ _)
    (hm.comp hfirst.measurable) (hbound.mono fun u h => ⟨h.1, h.2.1⟩)
  calc ∫⁻ u, ENNReal.ofReal (meanProduct S s (n * ℓ.side) P u) ∂(markedSampleLaw T β s (n * ℓ.side))
      = ∫⁻ u, ENNReal.ofReal (meanProduct S s (n * ℓ.side) P u.1) ∂(markedSampleLaw T β (s + 1) n) :=
        (hfirst.lintegral_comp (ENNReal.measurable_ofReal.comp hm)).symm
    _ = _ := hEq
    _ ≤ ∫⁻ u, ENNReal.ofReal E * ENNReal.ofReal (meanProduct S (s + 1) n P' u) ∂(markedSampleLaw T β (s + 1) n) :=
        lintegral_mono_ae (hbound.mono fun u h => by
          rw [← ENNReal.ofReal_mul hE]
          exact ENNReal.ofReal_le_ofReal h.2.2)
    _ = _ := lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hm')
private theorem ancestors_nonempty (L : ℕ) : ∀ (k n : ℕ) (A : Finset (TorusSite (sideBelow L k n))), A.Nonempty →
    (ancestors L k n A).Nonempty
  | 0, _, _, h => h
  | k + 1, n, A, h => (ancestors_nonempty L k (n * L) A h).image _
private theorem lintegral_meanProduct_climb (T : WeightedResponses.StageTower ℓ) (S : FreeEnergies.ScoredStageTower T)
    (β : ℝ) {p : ℕ} (t tp : ℕ) (c : ℝ) (e : ℕ → ℝ)
    (hblock : ∀ m : ℕ, IsBlockTorusSide ℓ m → IsBlockTorusSide ℓ (m * ℓ.side))
    (hstep : ∀ s, t ≤ s → s < tp → ∀ (m : ℕ) [NeZero m], IsBlockTorusSide ℓ m →
      ∀ P : Fin p → Finset (TorusSite (m * ℓ.side)), (∀ i, (P i).Nonempty) →
      ∫⁻ u, ENNReal.ofReal (meanProduct S s (m * ℓ.side) P u) ∂(markedSampleLaw T β s (m * ℓ.side)) ≤
        ENNReal.ofReal (Real.exp (c * e s)) *
          ∫⁻ u, ENNReal.ofReal (meanProduct S (s + 1) m (fun i => ancestors ℓ.side 1 m (P i)) u)
            ∂(markedSampleLaw T β (s + 1) m)) :
    ∀ j : ℕ, t + j ≤ tp → ∀ (m : ℕ) [NeZero m], IsBlockTorusSide ℓ m →
      ∀ P : Fin p → Finset (TorusSite (sideBelow ℓ.side j m)), (∀ i, (P i).Nonempty) →
      ∫⁻ u, ENNReal.ofReal (meanProduct S t (sideBelow ℓ.side j m) P u)
          ∂(markedSampleLaw T β t (sideBelow ℓ.side j m)) ≤
        ENNReal.ofReal (Real.exp (c * ∑ u ∈ Finset.Ico t (t + j), e u)) *
          ∫⁻ u, ENNReal.ofReal (meanProduct S (t + j) m (fun i => ancestors ℓ.side j m (P i)) u)
            ∂(markedSampleLaw T β (t + j) m) := by
  intro j
  induction j with
  | zero =>
    intro _ m _ _ P _
    simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_rfl
  | succ j ih =>
    intro hj m _ hm P hP
    have h1 := ih (by omega) (m * ℓ.side) (hblock m hm) P hP
    have h2 := hstep (t + j) (by omega) (by omega) m hm (fun i => ancestors ℓ.side j (m * ℓ.side) (P i))
      (fun i => ancestors_nonempty ℓ.side j (m * ℓ.side) _ (hP i))
    have hsum : ∑ u ∈ Finset.Ico t (t + (j + 1)), e u = ∑ u ∈ Finset.Ico t (t + j), e u + e (t + j) :=
      Finset.sum_Ico_succ_top (Nat.le_add_right t j) e
    calc _ ≤ _ := h1
      _ ≤ ENNReal.ofReal (Real.exp (c * ∑ u ∈ Finset.Ico t (t + j), e u)) * _ := mul_le_mul_right h2 _
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, hsum, mul_add]
        rfl
private theorem exp_mul_le_closing {c Sg q X Ct a b : ℝ} (hc : 0 ≤ c) (hSg : Sg ≤ 1) (hq : 0 ≤ q) (hX0 : 0 ≤ X)
    (hX : X ≤ Real.exp (Ct * a * b)) (hCt : 0 ≤ Ct) (hab : 0 ≤ a * b) :
    Real.exp (c * Sg) * (q * X) ≤
      (Real.exp c * q + Ct + 1) * Real.exp ((Real.exp c * q + Ct + 1) * a * b) := by
  have hq' : 0 ≤ Real.exp c * q := mul_nonneg (Real.exp_nonneg _) hq
  have h1 : Real.exp (c * Sg) ≤ Real.exp c := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (Ct * a * b) ≤ Real.exp ((Real.exp c * q + Ct + 1) * a * b) :=
    Real.exp_le_exp.mpr (by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hab)
  have h3 : X ≤ Real.exp ((Real.exp c * q + Ct + 1) * a * b) := hX.trans h2
  calc Real.exp (c * Sg) * (q * X)
      ≤ Real.exp c * (q * Real.exp ((Real.exp c * q + Ct + 1) * a * b)) := by gcongr
    _ = Real.exp c * q * Real.exp ((Real.exp c * q + Ct + 1) * a * b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
theorem majorantMoments_holds (hMaj : ResponseInTheExpansion.productMeanScoreStepBound)
    (hPos : FreeEnergies.caseMeanTowerStatement)
    (hFirst : FreeEnergiesOfTheFlow.MarkedSampleTruncationPreserving)
    (hGr : FreeEnergies.flowStatesAreGroundsStatement)
    (hSum : FreeEnergies.levelSumBoundStatement) (hTop : FreeEnergies.topLevelScoreBoundStatement)
    (hBo : ResponseInTheExpansion.StageStatesMeasurableStatement) : WeightedObservables.majorantMomentsStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, hT'⟩ := hTop a ha
  obtain ⟨L₂, r₂, C₂, hr₂, hG'⟩ := hGr a ha
  obtain ⟨L₃, r₃, C₃, hr₃, hS'⟩ := hSum a ha
  obtain ⟨r₄, hr₄, hM'⟩ := hMaj
  obtain ⟨L₅, r₅, hr₅, hP'⟩ := hPos a ha
  refine ⟨max (max L₁ (max L₂ L₃)) L₅, fun c => min (min (r₁ c) (min (r₂ c) (min (r₃ c) (r₄ c)))) (r₅ c),
    max C₁ (max C₂ C₃),
    fun c => lt_min (lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (hr₄ c)))) (hr₅ c), ?_⟩
  intro L hL hLL₀ Tb hTa hTL hDrawn hCold hHalf hrt₀ hCd Kr
  have hLL : max L₁ (max L₂ L₃) ≤ L := (le_max_left _ _).trans hLL₀
  have hrt := hrt₀.trans (min_le_left _ _)
  obtain ⟨y₁, hy₁⟩ := hT' L hL ((le_max_left _ _).trans hLL) Tb hTa hTL hDrawn hCold hHalf
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hCd) Kr
  obtain ⟨y₂, hy₂⟩ := hG' L hL (((le_max_left _ _).trans (le_max_right _ _)).trans hLL) Tb hTa hTL hDrawn hCold hHalf
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (((le_max_left _ _).trans (le_max_right _ _)).trans hCd) Kr
  obtain ⟨y₃, hy₃⟩ := hS' L hL (((le_max_right _ _).trans (le_max_right _ _)).trans hLL) Tb hTa hTL hDrawn hCold hHalf
    (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (((le_max_right _ _).trans (le_max_right _ _)).trans hCd) Kr
  obtain ⟨y₄, hy₄⟩ := hM' Tb hDrawn
    (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) Kr
  obtain ⟨y₅, hy₅⟩ := hP' L hL ((le_max_right _ _).trans hLL₀) Tb hTa hTL hDrawn (hrt₀.trans (min_le_right _ _))
  refine ⟨max (max (max y₁ y₂) (max y₃ (max y₄ Tb.floorMin))) y₅, ?_⟩
  intro y hy₀ hrow p
  have hy : max (max y₁ y₂) (max y₃ (max y₄ Tb.floorMin)) ≤ y := (le_max_left _ _).trans hy₀
  have hPm := hy₅ y ((le_max_right _ _).trans hy₀) hrow.returns_at hrow.wilson_expansion
  have hyy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyy₄ : y₄ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hyT : Tb.floorMin ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hDrawn.fits y hyT
  have hfl : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hDrawn.L_gt
  obtain ⟨Ct, hCt0, hCt⟩ := hy₁ y hyy₁ hrow
  have hGd := hy₂ y hyy₂ hrow
  have hSm := hy₃ y hyy₃ hrow
  have hMj := hy₄ y hyy₄
  have hc0 : (0 : ℝ) ≤ 2 ^ p * (p.factorial : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (p.factorial : ℝ) * Real.exp 1 := by positivity
  refine ⟨Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) + Ct + 1, ?_, ?_⟩
  · have : 0 ≤ Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) :=
      mul_nonneg (Real.exp_nonneg _) hq0
    linarith
  intro β T S t k n _ B hK hOn hReach hn hB
  have hL1 : 1 ≤ (Tb.stepParameters y).side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hblock : ∀ m : ℕ, IsBlockTorusSide (Tb.stepParameters y) m →
      IsBlockTorusSide (Tb.stepParameters y) (m * (Tb.stepParameters y).side) := by
    intro m hm
    have hn₀ : (Tb.stepParameters y).n₀ ≤ m := (Nat.le_mul_of_pos_left _ (by omega)).trans hm.2
    exact ⟨Nat.dvd_mul_left _ _, by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hn₀⟩
  obtain ⟨hforms, hgr⟩ := hGd β T S (t + k) hK hOn hReach
  have hborel : ∀ u ≤ t + k, Measurable (S.setup u).score := fun u hu => (hOn.isAdmissible u hu).price.borel
  have hnn : ∀ u ≤ t + k, ∀ w, 0 ≤ (S.setup u).score w := fun u hu => (hOn.isAdmissible u hu).price.nonneg
  have hstate : ∀ (s m : ℕ) [NeZero m], Measurable (stageState T s m) := fun s m _ => hBo _ hfit T s m
  have hstep : ∀ s, t ≤ s → s < t + k → ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (Tb.stepParameters y) m →
      ∀ P : Fin p → Finset (TorusSite (m * (Tb.stepParameters y).side)), (∀ i, (P i).Nonempty) →
      ∫⁻ u, ENNReal.ofReal (meanProduct S s (m * (Tb.stepParameters y).side) P u)
          ∂(markedSampleLaw T β s (m * (Tb.stepParameters y).side)) ≤
        ENNReal.ofReal (Real.exp (2 ^ p * (p.factorial : ℝ) *
            Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β s)))) *
          ∫⁻ u, ENNReal.ofReal (meanProduct S (s + 1) m
              (fun i => ancestors (Tb.stepParameters y).side 1 m (P i)) u)
            ∂(markedSampleLaw T β (s + 1) m) := by
    intro s _ hs m _ hm P hP
    have hst := hOn.isFlowStep s hs.le
    have hTab : OnStepParameters Tb y (S.setup s) :=
      ⟨hst.onFamily, (hforms s hs).2, hOn.isAdmissible s hs.le, by
        rw [hOn.params_eq s]
        exact hOn.N₀_eq⟩
    have hmaj := hMj (T.stage s).toStepSetup (S.setup s) ((hOn.params_eq s).trans hK) hTab m
    have hsc : (S.setup (s + 1)).score = coarseLabelScore (S.setup s).responseParams.s₁ (S.setup s).score := by
      rw [hOn.params_eq s]
      exact hOn.score_succ s hs
    have hstand : ResponseInTheExpansion.IsTowerAtParameters Tb y T β s :=
      ⟨hOn.startsAtWilson, fun j hj => (hOn.isFlowStep j (by omega)).coupling_eq,
        fun j hj => (hOn.isFlowStep j (by omega)).onFamily⟩
    refine lintegral_meanProduct_step T S β s m
      (hPm T β s m hstand hOn.isCutoff_bottom hOn.marksMeasurable (hforms s hs).1 (hblock m hm) hm.1) P _
      (Real.exp_nonneg _) (hnn s hs.le) (measurable_meanProduct S s _ P (hborel s hs.le) (hstate s _))
      (measurable_meanProduct S (s + 1) m _ (hborel (s + 1) hs) (hstate (s + 1) m))
      (hFirst _ hfit hfl T hOn.isCutoff_bottom hOn.marksMeasurable β s m) ?_
    filter_upwards [(hgr m hm).2 s hs] with u hu
    obtain ⟨hI, hle⟩ := hmaj (hotCaseGround (T.stage s).toStepSetup u.2.2.1 (stageState T (s + 1) m u).2) hu
      (Fin p) Finset.univ P (fun i _ => hP i)
    obtain ⟨h1, -⟩ := hmaj (hotCaseGround (T.stage s).toStepSetup u.2.2.1 (stageState T (s + 1) m u).2) hu
      (Fin p) ∅ P (by simp)
    simp only [Finset.prod_empty] at h1
    refine ⟨hI, h1, ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    have hx : (T.stage s).coupling = flowCoupling (Tb.stepParameters y) β s := hst.coupling_eq
    rw [hx] at hle
    unfold meanProduct
    rw [hsc]
    exact hle
  have hsumle := (hSm β (t + k) hReach t (by omega)).1
  have hup := lintegral_meanProduct_climb T S β t (t + k) (2 ^ p * (p.factorial : ℝ))
    (fun u => Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β u))) hblock hstep k le_rfl n hn B hB
  obtain ⟨hint, hone, hmean⟩ := hCt β T S (t + k) n hK hOn hReach hn
  have hP' : ∀ i, (ancestors (Tb.stepParameters y).side k n (B i)).Nonempty := fun i =>
    ancestors_nonempty _ k n _ (hB i)
  have htop : ∫⁻ u, ENNReal.ofReal (meanProduct S (t + k) n
        (fun i => ancestors (Tb.stepParameters y).side k n (B i)) u)
      ∂(markedSampleLaw T β (t + k) n) ≤
      ENNReal.ofReal ((p.factorial : ℝ) * Real.exp 1 * S.expScoreMean β (t + k) n) := by
    calc _ ≤ ∫⁻ u, ENNReal.ofReal ((p.factorial : ℝ) * Real.exp 1) *
            ENNReal.ofReal (Real.exp (S.totalScore (t + k) n u)) ∂(markedSampleLaw T β (t + k) n) :=
          lintegral_mono fun u => by
            rw [← ENNReal.ofReal_mul hq0]
            exact ENNReal.ofReal_le_ofReal (prod_meanSiteScore_le (hnn _ le_rfl) hP' _ _)
      _ = ENNReal.ofReal ((p.factorial : ℝ) * Real.exp 1) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (S.totalScore (t + k) n u)) ∂(markedSampleLaw T β (t + k) n) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le),
            ← ENNReal.ofReal_mul hq0]
          rfl
  have hlog : 0 ≤ Real.log (flowCoupling (Tb.stepParameters y) β (t + k)) :=
    Real.log_nonneg (hfit.y₁_ge.trans (hReach _ le_rfl))
  have hab : 0 ≤ (1 + Real.log (flowCoupling (Tb.stepParameters y) β (t + k))) * (n : ℝ) ^ 4 := by positivity
  have hnum := exp_mul_le_closing hc0 hsumle hq0 (by linarith) hmean hCt0 hab
  have hall : ∫⁻ u, ENNReal.ofReal (meanProduct S t (sideBelow (Tb.stepParameters y).side k n) B u)
      ∂(markedSampleLaw T β t (sideBelow (Tb.stepParameters y).side k n)) ≤
      ENNReal.ofReal ((Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) + Ct + 1) *
        Real.exp ((Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) + Ct + 1) *
          (1 + Real.log (flowCoupling (Tb.stepParameters y) β (t + k))) * (n : ℝ) ^ 4)) := by
    refine hup.trans ((mul_le_mul_right htop _).trans ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hnum
  have hmB := measurable_meanProduct S t _ B (hborel t (by omega))
    (hstate t (sideBelow (Tb.stepParameters y).side k n))
  have hN : ∀ u, 0 ≤ meanProduct S t (sideBelow (Tb.stepParameters y).side k n) B u := fun u =>
    Finset.prod_nonneg fun i _ => meanSiteScore_nonneg (hnn t (by omega)) _ _ _
  have hC0 : 0 ≤ (Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) + Ct + 1) *
      Real.exp ((Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) + Ct + 1) *
        (1 + Real.log (flowCoupling (Tb.stepParameters y) β (t + k))) * (n : ℝ) ^ 4) := by
    have : 0 ≤ Real.exp (2 ^ p * (p.factorial : ℝ)) * ((p.factorial : ℝ) * Real.exp 1) :=
      mul_nonneg (Real.exp_nonneg _) hq0
    exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  refine ⟨⟨hmB.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hN)).2
    (hall.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  show ∫ u, meanProduct S t (sideBelow (Tb.stepParameters y).side k n) B u
      ∂(markedSampleLaw T β t (sideBelow (Tb.stepParameters y).side k n)) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hN) hmB.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC0 hall
end YangMills.Construction.TransfersOffTheWalk
end
