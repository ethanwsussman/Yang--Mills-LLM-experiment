import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGroundsProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.StatesAlongTheFlowAreGrounds
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepGas StepFloors
  ClusterExpansionOfAStep ResponseInTheExpansion WeightedResponses StageDensity
private theorem measurable_of_sigma_slices {X A : Type} [MeasurableSpace X] [Countable A] {β : A → Type}
    [∀ a, MeasurableSpace (β a)] {γ : Type} [MeasurableSpace γ] {f : X × Sigma β → γ}
    (h : ∀ a, Measurable fun p : X × β a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hArr : R.IsSymmetricWeight) (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) :
    R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
section Live
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ)
open Classical in
private def notLiveIndicator (w n : ℕ) [NeZero n] (q : StageState T w n) : ENNReal :=
  if IsLiveState ℓ (T.stage w).coupling (T.stage w).labelWeight q.1 q.2.1 q.2.2 then 0 else 1
private theorem measurable_notLiveIndicator (w n : ℕ) [NeZero n] (hb : IsBlockTorusSide ℓ n)
    (hrow : HullExpansion ℓ (T.stage w).depth (T.stage w).coupling (T.stage w).functional (T.stage w).density
      (T.stage w).labels (T.stage w).labelWeight (T.stage w).clusterFactor (T.stage w).siteDensity) :
    Measurable (notLiveIndicator T w n) := by
  classical
  refine measurable_of_sigma_slices fun Y => ?_
  have h1 := (hrow.borel n hb Y).1
  have hset : MeasurableSet {p : TorusField n × (Y → (T.stage w).labels.Ω) |
      0 < (if IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y then (T.stage w).labelWeight n p.1 Y p.2
        else 0)} :=
    measurableSet_lt measurable_const h1
  have e : (fun p : TorusField n × (Y → (T.stage w).labels.Ω) => notLiveIndicator T w n (p.1, ⟨Y, p.2⟩)) =
      fun p => if 0 < (if IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y
          then (T.stage w).labelWeight n p.1 Y p.2 else 0)
        then 0 else 1 := by
    funext p
    unfold notLiveIndicator IsLiveState
    by_cases hh : IsHullState ℓ (clusterRange (T.stage w).coupling) p.1 Y
    · simp [hh]
    · simp [hh]
  rw [e]
  exact Measurable.ite hset measurable_const measurable_const
end Live
theorem flowStatesAreGroundsStatement_holds (hRow : expansionAlongFlow)
    (hDen : stageStateDensityStatement) (hGr : HullStateIsHotCase)
    (hZero : CoarseWeightZeroOfFactorZero) (hFl : EventuallyFloorConditions)
    (hLaw : ChainIsProbabilityLaw) (hSt : StageStatesMeasurableStatement) :
    flowStatesAreGroundsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, hDen'⟩ := hDen a ha
  refine ⟨L₀, rt₀, 0, hrt₀, fun L hodd hL Tb hTa hTL hAdm _ _ hrt _ K => ?_⟩
  obtain ⟨yD, hyD⟩ := hDen' L hodd hL Tb hTa hTL hAdm hrt
  obtain ⟨yG, hyG⟩ := hGr Tb hAdm
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl Tb hAdm _ 1 hCpos one_pos
  refine ⟨max (max yD yG) (max yF (max Tb.floorMin 1)), fun y hy hstand β T S tp hSK hOn hReach => ?_⟩
  have hyD' : yD ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyG' : yG ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyF' : yF ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₀' : Tb.floorMin ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₁' : 1 ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hAdm.fits y hy₀'
  have hforms : ∀ u < tp, (T.stage u).toStepSetup.IsWellPosed ∧
      |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B := by
    intro u hu
    have hst := hOn.isFlowStep u hu.le
    have hmove := (hRow (Tb.stepParameters y) hstand β tp hReach).2 u hu
    have hmoved : |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B := by
      rw [hst.nextCoupling_eq, hst.coupling_eq]
      exact hmove
    have hrow := (hRow (Tb.stepParameters y) hstand β u fun j hj => hReach j (hj.trans hu.le)).1
    have hArr : (T.stage u).toStepSetup.IsSymmetricWeight := by
      unfold StepSetup.IsSymmetricWeight
      rw [hst.functional_eq]
      exact hrow.1
    exact ⟨isWellPosed_of_onParameters hAdm hy₀' hy₁' hst.onFamily hmoved hArr
      (hyF _ (hyF'.trans hst.onFamily.le_coupling)), hmoved⟩
  refine ⟨hforms, fun n _ hn => ?_⟩
  have hstands : ∀ w ≤ tp, IsTowerAtParameters Tb y T β w := by
    intro w hw
    refine ⟨hOn.startsAtWilson, fun j hj => ?_, fun j hj => (hOn.isFlowStep j (hj.trans hw)).onFamily⟩
    rcases Nat.lt_or_ge j (w + 1) with h | h
    · exact (hOn.isFlowStep j (by omega)).coupling_eq
    · have : j = w + 1 := by omega
      subst this
      exact (hOn.isFlowStep w hw).nextCoupling_eq
  have hlive : ∀ w ≤ tp, ∀ᵐ d ∂(markedSampleLaw T β w n), IsLiveState (Tb.stepParameters y) (T.stage w).coupling
      (T.stage w).labelWeight (stageState T w n d).1 (stageState T w n d).2.1 (stageState T w n d).2.2 := by
    intro w hw
    have hhull := (hOn.isFlowStep w hw).onFamily.isStep.1.2
    have hm := measurable_notLiveIndicator T w n hn hhull
    have hd := hyD y hyD' hstand.returns_at (fun β hβ => hstand.wilson_expansion β hβ) T β w n (hstands w hw)
      hOn.marksMeasurable hn (notLiveIndicator T w n) hm
    have hzero : (∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage w).coupling) W),
          ∫⁻ ω, notLiveIndicator T w n (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage w).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage w).labels.μ)) ∂(fieldHaar n)) = 0 := by
      refine (lintegral_congr fun W => ?_).trans lintegral_zero
      classical
      refine Finset.sum_eq_zero fun Y hY => ?_
      have hH : IsHullState (Tb.stepParameters y) (clusterRange (T.stage w).coupling) W Y :=
        (Finset.mem_filter.mp hY).2
      refine (lintegral_congr fun ω => ?_).trans lintegral_zero
      unfold notLiveIndicator
      by_cases hp : 0 < (T.stage w).labelWeight n W Y ω
      · rw [if_pos ⟨hH, hp⟩, zero_mul]
      · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hp), mul_zero]
    have hZ : (0 : ℝ) < ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side w n) W
        ∂(fieldHaar (fineSide (Tb.stepParameters y).side w n)) :=
      (hLaw (Tb.stepParameters y) hfit hfit.depth_lt β (fun _ => 0) w n).2.1
    rw [hzero] at hd
    have hz := (mul_eq_zero.mp hd).resolve_left (by simpa using hZ)
    have hm2 : Measurable fun d => notLiveIndicator T w n (stageState T w n d) := hm.comp (hSt _ hfit T w n)
    have hae := (lintegral_eq_zero_iff hm2).mp hz
    filter_upwards [hae] with d hd0
    by_contra hcon
    have : notLiveIndicator T w n (stageState T w n d) = 1 := by
      unfold notLiveIndicator
      exact if_neg hcon
    rw [show notLiveIndicator T w n (stageState T w n d) = 0 from hd0] at this
    exact zero_ne_one this
  refine ⟨hlive, fun u hu => ?_⟩
  filter_upwards [hlive (u + 1) hu] with d hd
  obtain ⟨hH, hpos⟩ := hd
  have hF := (hforms u hu).1
  refine Or.inr (hyG y hyG' (T.stage u).toStepSetup (hOn.isFlowStep u hu.le).onFamily hF n hn d.2.2.1 _ hH ?_)
  intro X hX h0
  have hz := hZero (T.stage u).toStepSetup hF n hn d.2.2.1 _ hH ⟨X, hX, h0⟩
  have hpos' : 0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup d.2.2.1) d.2.2.1
      (stageState T (u + 1) n d).2 := by
    have e : (T.stage (u + 1)).labelWeight n (stageState T (u + 1) n d).1 (stageState T (u + 1) n d).2.1
        (stageState T (u + 1) n d).2.2 = coarseStateWeight (T.stage u).toStepSetup
          (hotCoreSites (T.stage u).toStepSetup d.2.2.1) d.2.2.1 (stageState T (u + 1) n d).2 := by
      show coarseWeightExpansion (T.stage u).toStepSetup n _ _ _ = _
      simp only [coarseWeightExpansion, NeZero.ne n, dite_false]
      rfl
    rw [← e]
    exact hpos
  exact absurd hz hpos'.ne'
end YangMills.Construction.FreeEnergies
end
