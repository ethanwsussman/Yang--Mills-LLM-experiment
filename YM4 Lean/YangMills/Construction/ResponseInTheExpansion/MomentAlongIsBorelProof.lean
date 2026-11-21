import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheCasesAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open WeightedResponses StepSettings StepCosts RenormalizationStepParameters TorusFields TorusLumps BlockAverages LumpContours
namespace ResponseInTheExpansion
private theorem liveSet_measurable {R : StepSetup} (hr : R.HasExpansions) {m : ℕ} [NeZero m]
    (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) :
    MeasurableSet {q : TorusField m × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight q.1 Yt q.2} := by apply _root_.YangMills.SharedProofs.p107331 <;> assumption
private theorem liveSupportTotal_measurable {R : StepSetup} {A : ResponseSetup R} (hr : R.HasExpansions)
    (hI : A.IsAdmissible) {m : ℕ} [NeZero m]
    (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m))
    (w : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    open Classical in Measurable fun q : TorusField m × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight q.1 Yt q.2 then supportResponseTotal A w q.1 Yt q.2 else 0 := by
  classical
  have hs := liveSet_measurable hr hb Yt
  have e : (fun q : TorusField m × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight q.1 Yt q.2 then supportResponseTotal A w q.1 Yt q.2 else 0) =
      fun q => ∑ z ∈ weightSupportSites R.params.side R.depth m w,
        ((if IsLiveState R.params R.coupling R.labelWeight q.1 Yt q.2 then A.hull m z q.1 Yt q.2 w else 0) -
        if IsLiveState R.params R.coupling R.labelWeight q.1 Yt q.2 then A.cold m z (trivialField m) w else 0) := by
    funext q
    unfold supportResponseTotal centeredHullResponse
    split_ifs <;> simp
  rw [e]
  refine Finset.measurable_sum _ fun z _ => ?_
  exact (hI.bounds.hull_borel m hb z Yt w).sub (Measurable.ite hs measurable_const measurable_const)
abbrev _root_.YangMills.SharedProofs.p23502 := @liveSupportTotal_measurable
private theorem bondScore_pair_measurable (hS : BondScoreProperties) {R : StepSetup} (hf : R.params.Admissible)
    {n : ℕ} [NeZero n] (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (c : TorusBond n) :
    Measurable fun q : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      bondScore R.params R.coupling q.2.1 q.1 b c := by
  have hq : Measurable fun q : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (q.2.1, q.1) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have h0 := (hS R.params hf R.coupling n b c).2.2.2.2
  exact Measurable.comp (g := fun r : TorusField (n * R.params.side) × TorusField n =>
      bondScore R.params R.coupling r.1 r.2 b c)
    (f := fun q : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (q.2.1, q.1)) h0 hq
private theorem centeredStepScore_measurable (hS : BondScoreProperties) {R : StepSetup} (A : ResponseSetup R)
    (hf : R.params.Admissible) {n : ℕ} [NeZero n] (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (g : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    Measurable fun q : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      centeredStepScore A q.1 g q.2.1 b := by
  unfold centeredStepScore
  refine Measurable.sub_const
    (Measurable.const_mul (Finset.measurable_sum _ fun Z _ => Measurable.const_mul ?_ _) _) _
  unfold blockBondScores
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (bondScore_pair_measurable hS hf Yt b _).add (bondScore_pair_measurable hS hf Yt b _)
abbrev _root_.YangMills.SharedProofs.p59899 := @centeredStepScore_measurable
theorem jointMoment_measurable (hMean : caseMeanMeasurableStatement) (hForm : StagesAreWellPosed)
    (hSc : BondScoreProperties) : jointMomentMeasurableStatement := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ?_⟩
  obtain ⟨y1, H1⟩ := hMean T hT
  obtain ⟨y2, H2⟩ := hForm T hT
  refine ⟨max y1 y2, fun y β hL z₀ hy hFirst => ?_⟩
  have hy1 : y1 ≤ y := (le_max_left _ _).trans hy
  have hy2 : y2 ≤ y := (le_max_right _ _).trans hy
  intro s
  induction s with
  | zero =>
    intro hS n _ hn ι I f Y
    have hst := hS 0 le_rfl
    have hfs := H2 y hy2 K β hL z₀ hFirst 0 hS 0 le_rfl
    have hset := liveSet_measurable hfs.hasExpansions hn Y
    have e : (fun q : TorusField n × (Y → (flowStages T y β hL z₀ 0).1.labels.Ω) =>
        if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ 0).1.coupling
            (flowStages T y β hL z₀ 0).1.labelWeight q.1 Y q.2 then
          jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ 0 n I f q.1 Y q.2 else 0) =
        fun q => if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ 0).1.coupling
            (flowStages T y β hL z₀ 0).1.labelWeight q.1 Y q.2 then
          ∏ i ∈ I, (if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ 0).1.coupling
              (flowStages T y β hL z₀ 0).1.labelWeight q.1 Y q.2 then
            supportResponseTotal (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ 0) (f i)
              q.1 Y q.2 else 0) else 0 := by
      funext q
      by_cases hl : IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ 0).1.coupling
          (flowStages T y β hL z₀ 0).1.labelWeight q.1 Y q.2
      · simp only [if_pos hl]
        rfl
      · simp only [if_neg hl]
    rw [e]
    exact Measurable.ite hset (Finset.measurable_prod _ fun i _ =>
      liveSupportTotal_measurable hfs.hasExpansions hst.onFamily.admissible hn Y (f i)) measurable_const
  | succ s ih =>
    intro hS n _ hn ι I f Y
    have hSs : StagesOnFlowUpTo T K y β hL z₀ s := fun t ht => hS t (ht.trans (Nat.le_succ s))
    have hst := hS s (Nat.le_succ s)
    have hfs := H2 y hy2 K β hL z₀ hFirst (s + 1) hS s (Nat.le_succ s)
    have hfs' := H2 y hy2 K β hL z₀ hFirst (s + 1) hS (s + 1) le_rfl
    have hLp : 1 ≤ (T.stepParameters y).side := NeZero.one_le
    have hnb : IsBlockTorusSide (T.stepParameters y) (n * (T.stepParameters y).side) :=
      ⟨Dvd.intro_left _ rfl, hn.2.trans (Nat.le_mul_of_pos_right _ hLp)⟩
    have hset := liveSet_measurable hfs'.hasExpansions hn Y
    have hmean : ∀ J ∈ I.powerset,
        Measurable fun q : TorusField n × (Y → (flowStages T y β hL z₀ (s + 1)).1.labels.Ω) =>
        if IsHullState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).params
            (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).nextRange q.1 Y then
          caseMean (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s)
            (hotCoreSites (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) q.1) q.1 ⟨Y, q.2⟩
            (fun W' Yt ωt _ b =>
              jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s
                (n * (T.stepParameters y).side) J f W' Yt ωt *
              ∏ i ∈ I \ J, centeredStepScore
                (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) q.1 (f i) W' b)
        else 0 := fun J _ => by
      refine H1 y hy1 _ hst.onFamily.onFamily hfs n hn Y
        (fun V W' Yt ωt _ b =>
          jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s
            (n * (T.stepParameters y).side) J f W' Yt ωt *
          ∏ i ∈ I \ J, centeredStepScore
            (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) V (f i) W' b) ?_
      intro Yt bad b
      have h1 := (ih hSs (n * (T.stepParameters y).side) hnb J f Yt).comp
        (measurable_snd : Measurable fun q : TorusField n × TorusField (n * (T.stepParameters y).side) ×
          (Yt → (flowStages T y β hL z₀ s).1.labels.Ω) => q.2)
      have h2 : Measurable fun q : TorusField n × TorusField (n * (T.stepParameters y).side) ×
          (Yt → (flowStages T y β hL z₀ s).1.labels.Ω) =>
          ∏ i ∈ I \ J, centeredStepScore
            (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) q.1 (f i) q.2.1 b :=
        Finset.measurable_prod _ fun i _ => centeredStepScore_measurable hSc _ hfs.admissible Yt b (f i)
      convert h1.mul h2 using 1
      funext q
      simp only [Function.comp, Pi.mul_apply]
      split_ifs <;> simp
    have e : (fun q : TorusField n × (Y → (flowStages T y β hL z₀ (s + 1)).1.labels.Ω) =>
        if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ (s + 1)).1.coupling
            (flowStages T y β hL z₀ (s + 1)).1.labelWeight q.1 Y q.2 then
          jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (s + 1) n I f q.1 Y q.2 else 0) =
        fun q => if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ (s + 1)).1.coupling
            (flowStages T y β hL z₀ (s + 1)).1.labelWeight q.1 Y q.2 then
          ∑ J ∈ I.powerset, (if IsHullState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).params
              (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).nextRange q.1 Y then
            caseMean (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s)
              (hotCoreSites (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) q.1) q.1 ⟨Y, q.2⟩
              (fun W' Yt ωt _ b =>
                jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s
                  (n * (T.stepParameters y).side) J f W' Yt ωt *
                ∏ i ∈ I \ J, centeredStepScore
                  (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) q.1 (f i) W' b)
          else 0) else 0 := by
      funext q
      by_cases hl : IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ (s + 1)).1.coupling
          (flowStages T y β hL z₀ (s + 1)).1.labelWeight q.1 Y q.2
      · rw [if_pos hl, if_pos hl]
        have hh : IsHullState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).params
            (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s).nextRange q.1 Y := hl.1
        simp only [if_pos hh]
        rfl
      · rw [if_neg hl, if_neg hl]
    rw [e]
    exact Measurable.ite hset (Finset.measurable_sum _ hmean) measurable_const
end ResponseInTheExpansion
end YangMills.Construction
end
