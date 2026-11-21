import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.OneStepIsTheLawOfTheMirror
import YangMills.Construction.ResponseInTheExpansion.TheCasesOffABoxAreTheMirror
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import YangMills.Construction.ResponseInTheExpansion.TheStepsOfTheLocalChainFormStates
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings StepCosts RenormalizationStepParameters StepMarks StepGas TorusLumps TorusFields TorusBlocks TorusCounting
  MarkedIntegrals BlockAverages ColdStepAtMirrorFrames ClusterExpansionOfAStep
namespace ReflectedStep
private theorem couplingWindow_bounds (Bc c : ℝ) (hB : 0 < Bc) (hc : 0 < c) : ∃ x₀ : ℝ, ∀ x t : ℝ, x₀ ≤ x → |t - x| ≤ 4 * Bc * Real.log x ^ 2 →
    2 ^ 12 * clusterRange t ≤ ⌊x ^ ((1 : ℝ) / 20)⌋₊ ∧ clusterRange t ^ 2 ≤ ⌊x ^ ((1 : ℝ) / 20)⌋₊ ∧
      33 * (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ c * t := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 4 * Bc * Real.log x ^ 2 ≤ x / 2 := by
    have hl := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := 1 / (8 * Bc)) (by positivity)
    filter_upwards [hl, Filter.eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), id, abs_of_pos hx0] at hx
    have : 4 * Bc * Real.log x ^ 2 ≤ 4 * Bc * (1 / (8 * Bc) * x) := mul_le_mul_of_nonneg_left hx (by positivity)
    have e : 4 * Bc * (1 / (8 * Bc) * x) = x / 2 := by
      field_simp
      ring
    linarith
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp h1
  set S : ℝ := max 16 (66 / c) with hS
  refine ⟨max (max X₁ 1) (S ^ 100), fun x t hx ht => ?_⟩
  have hxX : X₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxS : S ^ 100 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hS16 : 16 ≤ S := le_max_left _ _
  have hSc : 66 / c ≤ S := le_max_right _ _
  set s : ℝ := x ^ ((1 : ℝ) / 100) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hsx : s ^ 100 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hSs : S ≤ s := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_pow_left₀ hlt hs0.le (n := 100) (by norm_num)
    rw [hsx] at this
    linarith
  have hs16 : 16 ≤ s := hS16.trans hSs
  have hw : x ^ ((1 : ℝ) / 20) = s ^ 5 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hbound := hX₁ x hxX
  have habs := abs_le.mp ht
  have ht1 : x / 2 ≤ t := by linarith [habs.1]
  have ht2 : t ≤ 2 * x := by linarith [habs.2]
  have ht0 : 0 ≤ t := by linarith
  have hr1 : ((clusterRange t : ℕ) : ℝ) < 2 * s + 1 := by
    have h2 : t ^ ((1 : ℝ) / 100) ≤ 2 * s := by
      calc t ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow ht0 ht2 (by norm_num)
        _ = 2 ^ ((1 : ℝ) / 100) * s := by rw [Real.mul_rpow (by norm_num) hx0.le]
        _ ≤ 2 ^ (1 : ℝ) * s := by
            refine mul_le_mul_of_nonneg_right ?_ hs0.le
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 * s := by norm_num
    have h3 := Nat.ceil_lt_add_one (Real.rpow_nonneg ht0 ((1 : ℝ) / 100))
    unfold clusterRange
    linarith
  have hs5 : 16 ^ 4 * s ≤ s ^ 5 := by
    have : (16 : ℝ) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (by norm_num) hs16 4
    calc (16 : ℝ) ^ 4 * s ≤ s ^ 4 * s := mul_le_mul_of_nonneg_right this hs0.le
      _ = s ^ 5 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    refine Nat.le_floor ?_
    push_cast
    nlinarith
  · rw [hw]
    refine Nat.le_floor ?_
    push_cast
    have h0 : (0 : ℝ) ≤ (clusterRange t : ℕ) := Nat.cast_nonneg _
    have h2 : ((clusterRange t : ℕ) : ℝ) ^ 2 ≤ (2 * s + 1) ^ 2 := pow_le_pow_left₀ h0 hr1.le 2
    have h3 : (2 * s + 1) ^ 2 ≤ 16 ^ 3 * s ^ 2 := by nlinarith
    have h4 : (16 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs16 3
    have h5 : (16 : ℝ) ^ 3 * s ^ 2 ≤ s ^ 3 * s ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
    have h6 : s ^ 3 * s ^ 2 = s ^ 5 := by ring
    linarith
  · have hc66 : 66 ≤ c * s := by
      have := hSc.trans hSs
      rw [div_le_iff₀ hc] at this
      linarith
    have hfl : (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ s ^ 5 := by
      rw [hw]
      exact Nat.floor_le (by positivity)
    have hs94 : 1 ≤ s ^ 94 := one_le_pow₀ (by linarith)
    have h4 : 66 * s ^ 5 ≤ c * x := by
      have e : x = s ^ 5 * s * s ^ 94 := by
        rw [← hsx]
        ring
      have h5 : 0 ≤ s ^ 5 := by positivity
      have h6 : 66 * s ^ 5 ≤ c * s * s ^ 5 := mul_le_mul_of_nonneg_right hc66 h5
      have h7 : c * s * s ^ 5 ≤ c * s * s ^ 5 * s ^ 94 := le_mul_of_one_le_right (by positivity) hs94
      rw [e]
      nlinarith
    have h8 : c * (x / 2) ≤ c * t := mul_le_mul_of_nonneg_left ht1 hc.le
    nlinarith
section Cases
variable {P : TorusLumps.StepParameters}
private theorem stageState_fst (T : StageTower P) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample P s n),
    (stageState T s n u).1 = topField P s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem isColdOnBall_of_disjoint {n : ℕ} [NeZero n] (hadm : P.Admissible) (hLn : P.side ∣ n) {r : ℕ} {V : TorusField n}
    {Y : Finset (TorusSite n)} (hull : IsHullState P r V Y) {o : TorusSite n} {m : ℝ} (hd : Disjoint Y (supBall o m)) :
    IsColdOnBall P.threshold V o m := by
  intro p hp
  obtain ⟨-, hlt, hc⟩ := (Finset.mem_filter.mp hp)
  by_contra hge
  push Not at hge
  have hl : torusLumpOf P p.1 ∈ torusHotLumps P V :=
    (mem_torusHotLumps_iff P hadm hLn V _).mpr ⟨p.1, p.2.1, p.2.2, hlt, hge, p.1, by simp [plaquetteVertices], rfl⟩
  have hz : p.1 ∈ torusHotSites P V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
  have hY : p.1 ∈ Y := hull.1 ((mem_thickening _ _ _).mpr ⟨_, hz, by simp [supDist_self]⟩)
  exact Finset.disjoint_left.mp hd hY (hc _ (by simp [plaquetteVertices]))
private theorem card_blocksNearFreeCores_le {n L : ℕ} [NeZero n] [NeZero L] (hL : Odd L) (r m : ℕ) (o : TorusSite n) :
    ((blocksNearFreeCores L r (supBall o m)).card : ℝ) ≤ (2 * ((m : ℝ) + 4 * r + 1) + 1) ^ 4 := by
  have hsub : blocksNearFreeCores L r (supBall o m) ⊆ thickening (m + 4 * r + 1) {o} := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v, hv, hzv⟩ := (mem_thickening _ _ _).mp hz
    have hvb : parentBlock L v ∈ supBall o m := (Finset.mem_filter.mp hv).2
    have h1 : supDist (parentBlock L v) o ≤ m := by
      have := (Finset.mem_filter.mp hvb).2
      exact_mod_cast this
    have h2 := supDist_parentBlock_le hL z v
    have h3 := supDist_triangle (parentBlock L z) (parentBlock L v) o
    exact (mem_thickening _ _ _).mpr ⟨o, Finset.mem_singleton_self _, by omega⟩
  have h := (Finset.card_le_card hsub).trans (card_thickening_singleton_le _ o)
  have h' : ((blocksNearFreeCores L r (supBall o m)).card : ℝ) ≤ ((2 * (m + 4 * r + 1) + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast h
  simpa using h'
abbrev _root_.YangMills.SharedProofs.p55616 := @card_blocksNearFreeCores_le
def awayCaseFunction (R : StepSetup) (t : ℕ) {n : ℕ} [NeZero n] (Q : Finset (TorusSite n))
    (Z : Finset (TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) (V : TorusField n) : CaseFunction R n :=
  open Classical in fun W Yt ωt bad b =>
    if Disjoint (coarseStateOf R (hotCoreSites R V) W Yt ωt bad b).1 Q ∧ FreeCoresAvoid R Yt bad (hotCoreSites R V) Q then
      F (imaginaryComponentsOn Z (frameDeviation R.params R.anchorRadius t R.frameReach V W)) else 0
private theorem caseMean_awayCaseFunction {R : StepSetup} {n : ℕ} [NeZero n] {Q : Finset (TorusSite n)}
    {Z : Finset (TorusBond (n * R.params.side))} {F : (↥Z × Fin 3 → ℝ) → ℝ} {V : TorusField n} {q : CoarseState R n}
    (hd : Disjoint q.1 Q) :
    caseMean R (hotCoreSites R V) V q (awayCaseFunction R R.depth Q Z F V) =
      caseMean R (hotCoreSites R V) V q (casesAwayFromBall R V Q Z F) := by
  classical
  have hterm : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
      caseTerm R (hotCoreSites R V) V q (awayCaseFunction R R.depth Q Z F V) bad Yt b W ν =
        caseTerm R (hotCoreSites R V) V q (casesAwayFromBall R V Q Z F) bad Yt b W ν := by
    intro bad Yt b W ν
    unfold caseTerm
    split_ifs with h
    · have hd' : Disjoint (coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b).1 Q := by
        rw [h.2]
        exact hd
      have e : awayCaseFunction R R.depth Q Z F V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b =
          casesAwayFromBall R V Q Z F (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b := by
        simp only [awayCaseFunction, casesAwayFromBall, hd', true_and]
      rw [e]
    · rfl
  have hsum : caseIntegral R (hotCoreSites R V) V q (awayCaseFunction R R.depth Q Z F V) =
      caseIntegral R (hotCoreSites R V) V q (casesAwayFromBall R V Q Z F) := by
    unfold caseIntegral
    simp only [hterm]
  unfold caseMean
  rw [hsum]
end Cases
section Core
variable {Tb : ParameterAssignment} {y : ℝ}
def CaseMeansAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β s → IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed → IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) →
    (Tb.stepParameters y).side ∣ n →
    ∀ F : TorusField n → CaseFunction (T.stage s).toStepSetup n,
      (Measurable fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
        F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2
          u.2.2.2 u.2.1) →
      (∃ C : ℝ, ∀ u : MarkedSample (Tb.stepParameters y) (s + 1) n,
        |F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2
          u.2.2.2 u.2.1| ≤ C) →
      ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
          F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
            (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2
            u.2.2.2 u.2.1 |
          stageSigma T (s + 1) n]) =ᵐ[markedSampleLaw T β (s + 1) n]
        fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (stageState T (s + 1) n u).2 (F u.2.2.1)
def ReflectedCasesAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ R : StepSetup, R.OnParameters Tb y → R.IsWellPosed → R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n m : ℕ) [NeZero n] [NeZero (4 * m)] (V : TorusField n) (q : CoarseState R n) (o : TorusSite n),
      IsBlockTorusSide R.params n → IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
      2 ^ 12 * R.range ≤ m → 8 * m ≤ n → Disjoint q.1 (supBall o m) →
      ∀ (Z : Finset (TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) (B : ℝ),
        Z ⊆ chartBondsInBlocks R.params.side (supBall o ((m : ℝ) / 8)) → Measurable F → (∀ v, |F v| ≤ B) →
        |caseMean R (hotCoreSites R V) V q (casesAwayFromBall R V (supBall o m) Z F) -
          reflectedStepMean R m o V (fun k => F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o k)))| ≤
        2 * B * Real.exp (-(Tb.rt * ((m - R.frameReach - 1 : ℕ) : ℝ) / 2 ^ 3)) +
          2 * B * (blocksNearFreeCores R.params.side R.range (supBall o m)).card * Real.exp (-(7 * Tb.gasRate * R.coupling))
private theorem errorTerms_le {B rt ch x c : ℝ} {m r m₀ : ℕ} {card : ℝ} (hB : 0 ≤ B) (hc1 : c ≤ 1) (hc0 : 0 < c)
    (hct : c ≤ rt / 16) (hm : 4096 * r ≤ m) (hr : 1 ≤ r) (hm₀ : m₀ ≤ r) (hcard : card ≤ (2 * ((m : ℝ) + 4 * r + 1) + 1) ^ 4)
    (hx : 33 * (m : ℝ) ≤ 7 * ch * x) :
    2 * B * Real.exp (-(rt * ((m - m₀ - 1 : ℕ) : ℝ) / 2 ^ 3)) + 2 * B * card * Real.exp (-(7 * ch * x)) ≤
      4 * B * Real.exp (-(c * (m : ℝ))) := by
  have hrt : 0 ≤ rt := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : Real.exp (-(rt * ((m - m₀ - 1 : ℕ) : ℝ) / 2 ^ 3)) ≤ Real.exp (-(c * (m : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h2 : m ≤ 2 * (m - m₀ - 1) := by omega
    have h3 : (m : ℝ) ≤ 2 * ((m - m₀ - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    have h4 : c * m ≤ rt / 16 * m := mul_le_mul_of_nonneg_right hct hm0
    have h5 : rt / 16 * m ≤ rt / 16 * (2 * ((m - m₀ - 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : rt / 16 * (2 * ((m - m₀ - 1 : ℕ) : ℝ)) = rt * ((m - m₀ - 1 : ℕ) : ℝ) / 2 ^ 3 := by ring
    linarith
  have h2 : card * Real.exp (-(7 * ch * x)) ≤ Real.exp (-(c * (m : ℝ))) := by
    have hm3 : 2 * ((m : ℝ) + 4 * r + 1) + 1 ≤ 3 * m := by
      have : (4096 : ℝ) * r ≤ m := by exact_mod_cast hm
      have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hl : (0 : ℝ) ≤ 2 * ((m : ℝ) + 4 * r + 1) + 1 := by positivity
    have h4 : (2 * ((m : ℝ) + 4 * r + 1) + 1) ^ 4 ≤ Real.exp (12 * m) := by
      have h5 : 3 * (m : ℝ) ≤ Real.exp (3 * m) := by linarith [Real.add_one_le_exp (3 * (m : ℝ))]
      have h6 := pow_le_pow_left₀ hl (hm3.trans h5) 4
      rw [← Real.exp_nat_mul] at h6
      have e : ((4 : ℕ) : ℝ) * (3 * (m : ℝ)) = 12 * m := by
        push_cast
        ring
      rwa [e] at h6
    have h7 : card * Real.exp (-(7 * ch * x)) ≤ Real.exp (12 * m) * Real.exp (-(7 * ch * x)) :=
      mul_le_mul_of_nonneg_right (hcard.trans h4) (Real.exp_pos _).le
    refine h7.trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h8 : c * m ≤ 1 * m := mul_le_mul_of_nonneg_right hc1 hm0
    linarith
  have h3 : 2 * B * Real.exp (-(rt * ((m - m₀ - 1 : ℕ) : ℝ) / 2 ^ 3)) ≤ 2 * B * Real.exp (-(c * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 2 * B * card * Real.exp (-(7 * ch * x)) ≤ 2 * B * Real.exp (-(c * (m : ℝ))) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith
abbrev _root_.YangMills.SharedProofs.p79174 := @errorTerms_le
private theorem gasRate_pos (hT : Tb.Admissible) : 0 < Tb.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
set_option maxHeartbeats 1000000 in
private theorem oneStepReflectedLawAt_of (hTb : Tb.Admissible) (hy0 : Tb.floorMin ≤ y) (hy1 : 200 * Tb.B ≤ y)
    (hMM : CaseMeansAt Tb y) (hCases : ReflectedCasesAt Tb y) (hFlu : stepDeviationMeasurableAt Tb y)
    (hSteps : localChainStepsWellPosedAt Tb y) (hZ : CoarseWeightZeroOfFactorZero) (hHull : CoarseHullIsHullState)
    (hSB : StageStatesMeasurableStatement) (hD : forgetLastStepStatement) :
    oneStepReflectedLawAt Tb y := by
  classical
  have hadm : (Tb.stepParameters y).Admissible := hTb.fits y hy0
  have hBpos : 0 < Tb.B := lt_of_lt_of_le one_pos hTb.B_ge
  have hch : 0 < 7 * Tb.gasRate := by
    have := gasRate_pos hTb
    positivity
  have hrt := hTb.rt_pos
  obtain ⟨xF, hxF⟩ := hFlu
  obtain ⟨x₁, hnum⟩ := couplingWindow_bounds Tb.B (7 * Tb.gasRate) hBpos hch
  refine ⟨4, min (Tb.rt / 16) 1, max xF x₁, lt_min (by positivity) one_pos, ?_⟩
  intro T β k n _ nn j o Z F B hloc hLn hj hZs hFm hFB
  have hfl : max xF x₁ ≤ flowCouplings (Tb.stepParameters y) β k := hloc.floor_le
  have hlocF : IsLocalChainAbove Tb y T β k n nn xF := { hloc with floor_le := (le_max_left _ _).trans hfl }
  have hK : k + j ≤ k + 2 * localChainDepth (Tb.stepParameters y) β k := by omega
  obtain ⟨hlev, hxt, hmv, hFS⟩ := hSteps T β k n nn _ hloc (k + j) hK
  have hOn : (T.stage (k + j)).toStepSetup.OnParameters Tb y := hloc.onFamily.onFamily (k + j) hK
  have hdr : ∀ i ≤ j, |(T.stage (k + i)).coupling - (T.stage k).coupling| ≤ 2 * Tb.B * i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      obtain ⟨-, -, hm, -⟩ := hSteps T β k n nn _ hloc (k + i) (by omega)
      have h2 : (T.stage (k + (i + 1))).coupling = (T.stage (k + i)).nextCoupling := rfl
      rw [h2]
      have h3 := abs_sub_le (T.stage (k + i)).nextCoupling (T.stage (k + i)).coupling (T.stage k).coupling
      push_cast
      linarith
  obtain ⟨-, hxk, -, -⟩ := hSteps T β k n nn _ hloc k (by omega)
  have hdrift : |(T.stage (k + j)).coupling - flowCouplings (Tb.stepParameters y) β k| ≤
      4 * Tb.B * Real.log (flowCouplings (Tb.stepParameters y) β k) ^ 2 := by
    have h1 := hdr j le_rfl
    rw [hxk] at h1
    have h2 : (j : ℝ) ≤ 2 * (localChainDepth (Tb.stepParameters y) β k : ℝ) := by exact_mod_cast hj.le
    have h3 : (localChainDepth (Tb.stepParameters y) β k : ℝ) ≤ Real.log (flowCouplings (Tb.stepParameters y) β k) ^ 2 :=
      Nat.floor_le (sq_nonneg _)
    have h4 : 2 * Tb.B * (j : ℝ) ≤ 2 * Tb.B * (2 * Real.log (flowCouplings (Tb.stepParameters y) β k) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  obtain ⟨hm1, hm2, hm3⟩ := hnum _ _ ((le_max_right _ _).trans hfl) hdrift
  obtain ⟨m, hmdef⟩ : ∃ m, m = localBlockSide (Tb.stepParameters y) β k := ⟨_, rfl⟩
  rw [← hmdef] at hZs ⊢
  have hcut := hloc.cutoff
  have hco := hloc.measurable
  have hLam := hadm.depth_lt
  obtain ⟨hprob, hpres⟩ := hD (Tb.stepParameters y) hadm hLam T hcut hco β (k + j) n
  have : IsProbabilityMeasure (markedSampleLaw T β (k + j + 1) n) :=
    (hD (Tb.stepParameters y) hadm hLam T hcut hco β (k + j + 1) n).1
  have hK' : k + j < k + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := by
    have : j < 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := hj
    omega
  have hst : IsTowerAtParameters Tb y T β (k + j) :=
    ⟨hloc.onFamily.startsAtWilson, fun i hi => hloc.onFamily.coupling_eq i (by omega), fun i hi => hloc.onFamily.onFamily i (by omega)⟩
  set R := (T.stage (k + j)).toStepSetup with hRdef
  have hm1' : 2 ^ 12 * R.range ≤ m := by
    rw [hmdef]
    exact hm1
  have hm2' : R.range ^ 2 ≤ m := by
    rw [hmdef]
    exact hm2
  have hm3' : 33 * (m : ℝ) ≤ 7 * Tb.gasRate * R.coupling := by
    rw [hmdef]
    exact hm3
  have hmn : 8 * m ≤ n := by
    have h1 : (2 : ℝ) ^ 10 * (m : ℝ) ≤ n := by
      rw [hmdef]
      exact hloc.side_ge
    have h2 : 2 ^ 10 * m ≤ n := by exact_mod_cast h1
    omega
  have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hrb := hFS.range_ge_side
  have hrf := hFS.range_ge_base
  have hrL : (Tb.stepParameters y).side ≤ R.range := by
    have : (Tb.stepParameters y).side ≤ 2 ^ 40 * R.params.side := Nat.le_mul_of_pos_left _ (by positivity)
    exact this.trans hrb
  have hrn : (Tb.stepParameters y).n₀ ≤ R.range := by
    have h1 : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := hrf
    have h2 : R.params.n₀ = (Tb.stepParameters y).n₀ := rfl
    omega
  have hLn₀ : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ n := by
    have h1 : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ R.range * R.range := Nat.mul_le_mul hrL hrn
    have h2 : R.range * R.range = R.range ^ 2 := (pow_two _).symm
    omega
  have hb : IsBlockTorusSide (Tb.stepParameters y) n := ⟨hLn, hLn₀⟩
  have hn₀ : (Tb.stepParameters y).n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hLn₀
  have hbL : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 : y ≤ R.coupling := hOn.le_coupling
    have h2 := (abs_le.mp hmv).2
    have h3 : (T.stage (k + j)).nextCoupling = R.nextCoupling := rfl
    have h4 : (T.stage (k + j)).coupling = R.coupling := rfl
    rw [h3, h4] at h2
    linarith
  have hmle : stageSigma T (k + j + 1) n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (k + j + 1) n :=
    (hSB (Tb.stepParameters y) hadm T (k + j + 1) n).comap_le
  have hfst : Measurable (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n => u.1) := hpres.measurable
  have hsnd : Measurable (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n => u.2) := measurable_snd
  have hVm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n => u.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp hsnd)
  have hWm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n =>
      topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) := by
    have h1 : Measurable fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n =>
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).1 :=
      measurable_fst.comp ((hSB (Tb.stepParameters y) hadm T (k + j) (n * (Tb.stepParameters y).side)).comp hfst)
    have e : (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n =>
        topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) =
        fun u => (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).1 := by
      funext u
      rw [stageState_fst]
    rw [e]
    exact h1
  obtain ⟨hcomp, hEm⟩ := hxF T β k n nn j o hlocF hj
  rw [← hmdef] at hcomp hEm
  have hcoldE : ∀ u : MarkedSample (Tb.stepParameters y) (k + j + 1) n,
      Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o m) → IsColdOnBall (Tb.stepParameters y).threshold u.2.2.1 o m := by
    intro u hd
    have hull : IsHullState (Tb.stepParameters y) R.nextRange u.2.2.1 (stageState T (k + j + 1) n u).2.1 :=
      hHull (Tb.stepParameters y) hadm R.range R.nextRange hFS.range_le hFS.nextRange_ge n hb.1 u.2.2.1 u.2.2.2
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
    exact isColdOnBall_of_disjoint hadm hb.1 hull hd
  have hsubZ : ∀ p : ↥Z × Fin 3, p.1.1 ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8)) :=
    fun p => hZs p.1.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  set E : Set (MarkedSample (Tb.stepParameters y) (k + j + 1) n) :=
    {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o m) ∧ StepAvoids T (k + j) m o u'} with hEdef
  set f : MarkedSample (Tb.stepParameters y) (k + j + 1) n → ℝ := fun u' =>
    F (imaginaryComponentsOn Z (stepDeviation T (k + j) u'.2.2.1
      (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1))) with hfdef
  have hgm : Measurable (E.indicator f) := by
    set C : Set (TorusField n × TorusField (n * (Tb.stepParameters y).side)) :=
      {p | IsColdOnBall (Tb.stepParameters y).threshold p.1 o m} with hC
    set h : MarkedSample (Tb.stepParameters y) (k + j + 1) n → ℝ := fun u => F fun p =>
      C.indicator (fun r => imaginaryComponent p.2 (stepDeviation T (k + j) r.1 r.2 p.1.1))
        (u.2.2.1, topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) with hh
    have hhm : Measurable h := hFm.comp (measurable_pi_lambda _ fun p =>
      (hcomp p.1.1 p.2 (hsubZ p)).comp (hVm.prodMk hWm))
    have e : E.indicator f = E.indicator h := by
      funext u
      by_cases hu : u ∈ E
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        show F _ = F _
        congr 1
        funext p
        have hc : (u.2.2.1, topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) ∈ C := hcoldE u hu.1
        rw [Set.indicator_of_mem hc]
        rfl
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
    rw [e]
    exact hhm.indicator hEm
  have hEb : ∀ u, |E.indicator f u| ≤ B := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      exact hFB _
    · rw [Set.indicator_of_notMem hu]
      simpa using hB0
  have hInt : Integrable (E.indicator f) (markedSampleLaw T β (k + j + 1) n) :=
    Integrable.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact hEb u)
  refine ⟨hInt, ?_⟩
  have hEta : ∀ (V : TorusField n) (W : TorusField (n * (Tb.stepParameters y).side)),
      frameDeviation R.params R.anchorRadius R.depth R.frameReach V W = stepDeviation T (k + j) V W := by
    intro V W
    funext b
    show frameDeviation R.params R.anchorRadius R.depth R.frameReach V W b =
      frameDeviation R.params R.anchorRadius (k + j) R.frameReach V W b
    have hlev' : R.depth = k + j := hlev
    rw [hlev']
  have hgF : (fun u : MarkedSample (Tb.stepParameters y) (k + j + 1) n => awayCaseFunction R R.depth (supBall o m) Z F u.2.2.1
      (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1)
      (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
      (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1) = E.indicator f := by
    funext u
    have hs : coarseStateOf R (hotCoreSites R u.2.2.1) (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1)
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 = (stageState T (k + j + 1) n u).2 := by
      show _ = coarseStateOf R (hotCoreSites R u.2.2.1) (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).1
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
        (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1
      rw [stageState_fst]
    unfold awayCaseFunction
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu, if_pos ⟨by rw [hs]; exact hu.1, hu.2⟩, hEta]
    · rw [Set.indicator_of_notMem hu, if_neg fun h => hu ⟨by rw [← hs]; exact h.1, h.2⟩]
  have hae := hMM T β (k + j) n hst hcut hco hFS hbL hb.1 (awayCaseFunction R R.depth (supBall o m) Z F) (hgF ▸ hgm)
    ⟨B, fun u => (congrArg abs (congrFun hgF u)).trans_le (hEb u)⟩
  have hae1 := hMM T β (k + j) n hst hcut hco hFS hbL hb.1 (fun _ _ _ _ _ _ => (1 : ℝ)) measurable_const
    ⟨1, fun u => by simp⟩
  rw [hgF] at hae
  have hm0 : m ≠ 0 := by
    have : 1 ≤ R.range := by
      have h := hFS.range_ge_side
      have : 1 ≤ 2 ^ 40 * R.params.side := Nat.mul_pos (by positivity) hLpos
      omega
    omega
  have : NeZero (4 * m) := ⟨by omega⟩
  filter_upwards [hae, hae1] with u h h1 hd
  rw [h]
  have h1' : (1 : ℝ) = caseMean R (hotCoreSites R u.2.2.1) u.2.2.1 (stageState T (k + j + 1) n u).2 (fun _ _ _ _ _ => (1 : ℝ)) := by
    rw [← h1]
    have e := condExp_const (μ := markedSampleLaw T β (k + j + 1) n) hmle (1 : ℝ)
    exact (congrFun e u).symm
  have hull : IsHullState R.params R.nextRange u.2.2.1 (stageState T (k + j + 1) n u).2.1 :=
    hHull (Tb.stepParameters y) hadm R.range R.nextRange hFS.range_le hFS.nextRange_ge n hb.1 u.2.2.1 u.2.2.2
      (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
  have hnz : coarseStateWeight R (hotCoreSites R u.2.2.1) u.2.2.1 (stageState T (k + j + 1) n u).2 ≠ 0 := fun h0 => by
    unfold caseMean at h1'
    rw [h0, div_zero] at h1'
    exact one_ne_zero h1'
  have hΦ : ∀ X ∈ chainComponents R.nextRange (stageState T (k + j + 1) n u).2.1,
      coarseFactor u.2.2.1 (stageState T (k + j + 1) n u).2 X ≠ 0 :=
    fun X hX h0 => hnz (hZ R hFS n hb u.2.2.1 (stageState T (k + j + 1) n u).2 hull ⟨X, hX, h0⟩)
  rw [caseMean_awayCaseFunction hd]
  have hbound := hCases R hOn hFS hx' n m u.2.2.1 (stageState T (k + j + 1) n u).2 o hb hull hΦ hm1' hmn hd Z F B hZs hFm hFB
  have hr1 : 1 ≤ R.range := by
    have h := hFS.range_ge_side
    have : 1 ≤ 2 ^ 40 * R.params.side := Nat.mul_pos (by positivity) hLpos
    omega
  have hm₀r : R.frameReach ≤ R.range := Nat.div_le_self _ _
  have hm4 : 4096 * R.range ≤ m := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  exact hbound.trans (errorTerms_le hB0 (min_le_right _ _) (lt_min (by positivity) one_pos) (min_le_left _ _) hm4 hr1 hm₀r
    (card_blocksNearFreeCores_le hadm.L_odd R.range m o) hm3')
end Core
end ReflectedStep
open ReflectedStep in
theorem oneStepReflectedLaw_holds (hM : conditionalMeanIsCaseMeanStatement)
    (hC₀ : casesAwayFromBallReflectStatement) (hFl : stepDeviationMeasurableStatement)
    (hSt₀ : localChainStepsWellPosedStatement) (hZ : CoarseWeightZeroOfFactorZero)
    (hHull : CoarseHullIsHullState) (hSB : StageStatesMeasurableStatement)
    (hD : forgetLastStepStatement) : oneStepReflectedLawStatement := by
  obtain ⟨r1, hr1, hC⟩ := hC₀
  intro a ha
  obtain ⟨L₁, r2, hr2, hM₀⟩ := hM a ha
  obtain ⟨L₂, r3, C₃, hr3, hF₀⟩ := hFl a ha
  obtain ⟨L₃, r4, C₄, hr4, hS₀⟩ := hSt₀ a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r1 c) (min (r2 c) (min (r3 c) (r4 c))), max C₃ C₄,
    fun c => lt_min (hr1 c) (lt_min (hr2 c) (lt_min (hr3 c) (hr4 c))),
    fun L hodd hL T hTa hTL hDr hCS hCH hrt hCd => ?_⟩
  have l1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have l2 : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have l3 : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have t1 := hrt.trans (min_le_left _ _)
  have t2 := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 := hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have t4 := hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y1, h1⟩ := hC T hDr hCS t1
  obtain ⟨y2, h2⟩ := hM₀ L hodd l1 T hTa hTL hDr t2
  obtain ⟨y3, h3⟩ := hF₀ L hodd l2 T hTa hTL hDr hCS hCH t3 ((le_max_left _ _).trans hCd)
  obtain ⟨y4, h4⟩ := hS₀ L hodd l3 T hTa hTL hDr hCS hCH t4 ((le_max_right _ _).trans hCd)
  refine ⟨max (max y1 y2) (max (max y3 y4) (max T.floorMin (200 * T.B))), fun y hy hret hwil => ?_⟩
  have e1 : y1 ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have e2 : y2 ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have e3 : y3 ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e4 : y4 ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e5 : T.floorMin ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have e6 : 200 * T.B ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  exact oneStepReflectedLawAt_of hDr e5 e6 (h2 y e2 hret hwil) (h1 y e1) (h3 y e3 hret hwil) (h4 y e4 hret hwil) hZ hHull hSB hD
end YangMills.Construction.ResponseInTheExpansion
end
