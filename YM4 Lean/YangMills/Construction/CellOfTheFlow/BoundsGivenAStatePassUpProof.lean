import YangMills.Construction.CellOfTheFlow.BoundsGivenAStatePassUp
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
section Abstract
private theorem setLIntegral_comp_le_of_preimage_bound {Ω Q : Type} [MeasurableSpace Ω] [MeasurableSpace Q]
    {μ : Measure Ω} {q : Ω → Q} (hq : Measurable q) {E : Set Ω} {c : ENNReal}
    (hb : ∀ A : Set Q, MeasurableSet A → μ (q ⁻¹' A ∩ E) ≤ c * μ (q ⁻¹' A)) {h : Q → ENNReal} (hh : Measurable h) :
    ∫⁻ u in E, h (q u) ∂μ ≤ c * ∫⁻ u, h (q u) ∂μ := by
  refine Measurable.ennreal_induction (motive := fun h => ∫⁻ u in E, h (q u) ∂μ ≤ c * ∫⁻ u, h (q u) ∂μ)
    ?_ ?_ ?_ hh
  · intro a S hS
    have hS' : MeasurableSet (q ⁻¹' S) := hq hS
    show ∫⁻ u in E, (q ⁻¹' S).indicator (fun _ => a) u ∂μ ≤ c * ∫⁻ u, (q ⁻¹' S).indicator (fun _ => a) u ∂μ
    rw [lintegral_indicator_const hS', lintegral_indicator_const hS', Measure.restrict_apply hS', mul_left_comm]
    exact mul_le_mul_right (hb S hS) a
  · intro f g _ hf hg ihf ihg
    show ∫⁻ u in E, (f (q u) + g (q u)) ∂μ ≤ c * ∫⁻ u, (f (q u) + g (q u)) ∂μ
    have hfq : Measurable fun u => f (q u) := hf.comp hq
    rw [lintegral_add_left hfq, lintegral_add_left hfq, mul_add]
    exact add_le_add ihf ihg
  · intro f hf hmono ih
    show ∫⁻ u in E, ⨆ n, f n (q u) ∂μ ≤ c * ∫⁻ u, ⨆ n, f n (q u) ∂μ
    have hfq : ∀ n, Measurable fun u => f n (q u) := fun n => (hf n).comp hq
    have hm : Monotone fun n u => f n (q u) := fun i j hij u => hmono hij (q u)
    rw [lintegral_iSup hfq hm, lintegral_iSup hfq hm, ENNReal.mul_iSup]
    exact iSup_mono ih
private theorem setLIntegral_fst_preimage_withDensity_le {A D : Type} [MeasurableSpace A] [MeasurableSpace D]
    {μ : Measure A} {ρ : Measure D}
    [SFinite μ] [SFinite ρ] {w K : A × D → ENNReal} (hw : Measurable w) (hK : Measurable K) {S : Set A}
    (hS : MeasurableSet S) {c : ENNReal}
    (h : ∀ d, ∫⁻ a in S, w (a, d) * K (a, d) ∂μ ≤ c * ∫⁻ a, w (a, d) * K (a, d) ∂μ) :
    ∫⁻ z in Prod.fst ⁻¹' S, K z ∂((μ.prod ρ).withDensity w) ≤ c * ∫⁻ z, K z ∂((μ.prod ρ).withDensity w) := by
  have hS' : MeasurableSet (Prod.fst ⁻¹' S : Set (A × D)) := measurable_fst hS
  have hwK : Measurable fun z => w z * K z := hw.mul hK
  have e1 : ∫⁻ z, K z ∂((μ.prod ρ).withDensity w) = ∫⁻ d, ∫⁻ a, w (a, d) * K (a, d) ∂μ ∂ρ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hw hK]
    exact lintegral_prod_symm _ hwK.aemeasurable
  have e2 : ∫⁻ z in Prod.fst ⁻¹' S, K z ∂((μ.prod ρ).withDensity w) =
      ∫⁻ d, ∫⁻ a in S, w (a, d) * K (a, d) ∂μ ∂ρ := by
    rw [← lintegral_indicator hS', lintegral_withDensity_eq_lintegral_mul _ hw (hK.indicator hS')]
    refine (lintegral_prod_symm _ (hw.mul (hK.indicator hS')).aemeasurable).trans ?_
    refine lintegral_congr fun d => ?_
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun a => ?_
    by_cases ha : a ∈ S <;> simp [Set.indicator, ha]
  have hm : Measurable fun d => ∫⁻ a, w (a, d) * K (a, d) ∂μ := hwK.lintegral_prod_left'
  rw [e1, e2, ← lintegral_const_mul _ hm]
  exact lintegral_mono h
end Abstract
section Samples
variable {ℓ : TorusLumps.StepParameters}
private instance (m : ℕ) [NeZero m] : Fintype (WeightedResponses.BondSet m) :=
  inferInstanceAs (Fintype (Finset (TorusFields.TorusBond m)))
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (WeightedResponses.stepReferenceMeasure ℓ n) := by
  unfold WeightedResponses.stepReferenceMeasure
  infer_instance
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × WeightedResponses.StepOutcome ℓ n → ℝ}
    (h : ∀ (b : StepCosts.BaseChoice ℓ.side n) (bad : WeightedResponses.BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusFields.TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private theorem measurable_stepOutcomeDensity (R : StepSettings.StepSetup) {n : ℕ} [NeZero n]
    (hS : WeightedResponses.StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusFields.TorusBond (n * R.params.side)),
      Measurable fun p : TorusFields.TorusField (n * R.params.side) × TorusFields.TorusField n =>
        WeightedResponses.markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusFields.TorusField (n * R.params.side) × WeightedResponses.StepOutcome R.params n =>
      WeightedResponses.stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem measurable_sampleBelow (s : ℕ) : ∀ d n : ℕ, Measurable (ResponseInTheExpansion.sampleBelow ℓ s d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow s d (n * ℓ.side)).comp measurable_fst
private theorem measurable_coarserStepsOf (s : ℕ) : ∀ d n : ℕ, Measurable (coarserStepsOf ℓ s d n)
  | 0, _ => measurable_const
  | d + 1, n => ((measurable_coarserStepsOf s d (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
private def stateAndCoarser (T : WeightedResponses.StageTower ℓ) (s d n : ℕ) [NeZero n]
    (u : WeightedResponses.MarkedSample ℓ (s + d) n) :
    WeightedResponses.StageState T s (WeightedResponses.fineSide ℓ.side d n) × CoarserSteps ℓ d n :=
  (WeightedResponses.stageState T s (WeightedResponses.fineSide ℓ.side d n)
    (ResponseInTheExpansion.sampleBelow ℓ s d n u), coarserStepsOf ℓ s d n u)
private def topFieldOf (T : WeightedResponses.StageTower ℓ) (s : ℕ) : (d n : ℕ) →
    WeightedResponses.StageState T s (WeightedResponses.fineSide ℓ.side d n) × CoarserSteps ℓ d n →
      TorusFields.TorusField n
  | 0, _, p => p.1.1
  | _ + 1, _, p => p.2.2.2.1
private theorem measurable_topFieldOf (T : WeightedResponses.StageTower ℓ) (s : ℕ) :
    ∀ d n : ℕ, Measurable (topFieldOf T s d n)
  | 0, _ => measurable_fst.comp measurable_fst
  | _ + 1, _ => measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
private theorem stageState_fst (T : WeightedResponses.StageTower ℓ) :
    ∀ (s n : ℕ) [NeZero n] (u : WeightedResponses.MarkedSample ℓ s n),
      (WeightedResponses.stageState T s n u).1 = WeightedResponses.topField ℓ s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem topFieldOf_stateAndCoarser (T : WeightedResponses.StageTower ℓ) (s : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (u : WeightedResponses.MarkedSample ℓ (s + d) n),
      topFieldOf T s d n (stateAndCoarser T s d n u) = WeightedResponses.topField ℓ (s + d) n u
  | 0, n, _, u => stageState_fst T s n u
  | _ + 1, _, _, _ => rfl
private theorem setLIntegral_stateAndCoarser_le (hSd : WeightedResponses.StepTransitionDensityBounds)
    (T : WeightedResponses.StageTower ℓ) (β : ℝ) (s : ℕ)
    (hlaw : ∀ (t n : ℕ) [NeZero n], SFinite (WeightedResponses.markedSampleLaw T β t n))
    (hco : T.MarksMeasurable)
    (hq : ∀ (m : ℕ) [NeZero m], Measurable (WeightedResponses.stageState T s m)) {c : ENNReal} (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (E : Set (WeightedResponses.MarkedSample ℓ s (WeightedResponses.fineSide ℓ.side d n))),
      MeasurableSet E →
      (∀ A', MeasurableSet[WeightedResponses.stageSigma T s (WeightedResponses.fineSide ℓ.side d n)] A' →
        WeightedResponses.markedSampleLaw T β s (WeightedResponses.fineSide ℓ.side d n) (A' ∩ E) ≤
          c * WeightedResponses.markedSampleLaw T β s (WeightedResponses.fineSide ℓ.side d n) A') →
      ∀ H : WeightedResponses.StageState T s (WeightedResponses.fineSide ℓ.side d n) × CoarserSteps ℓ d n → ENNReal,
        Measurable H →
        ∫⁻ u in ResponseInTheExpansion.sampleBelow ℓ s d n ⁻¹' E, H (stateAndCoarser T s d n u)
            ∂(WeightedResponses.markedSampleLaw T β (s + d) n) ≤
          c * ∫⁻ u, H (stateAndCoarser T s d n u) ∂(WeightedResponses.markedSampleLaw T β (s + d) n) := by
  induction d with
  | zero =>
    intro n _ E hE hb H hH
    exact setLIntegral_comp_le_of_preimage_bound (q := WeightedResponses.stageState T s n) (hq n)
      (fun A hA => hb _ ⟨A, hA, rfl⟩)
      (h := fun p => H (p, ())) (hH.comp (measurable_id.prodMk measurable_const))
  | succ d ih =>
    intro n _ E hE hb H hH
    have hwm := measurable_stepOutcomeDensity (T.stage (s + d)).toStepSetup (n := n) hSd
      (fun bad => hco (s + d) n bad)
    have := hlaw (s + d) (n * ℓ.side)
    have hab : Measurable (stateAndCoarser T s d (n * ℓ.side)) :=
      ((hq _).comp (measurable_sampleBelow s d (n * ℓ.side))).prodMk (measurable_coarserStepsOf s d (n * ℓ.side))
    have htop : Measurable (WeightedResponses.topField ℓ (s + d) (n * ℓ.side)) := by
      have e : WeightedResponses.topField ℓ (s + d) (n * ℓ.side) =
          topFieldOf T s d (n * ℓ.side) ∘ stateAndCoarser T s d (n * ℓ.side) :=
        funext fun u => (topFieldOf_stateAndCoarser T s d (n * ℓ.side) u).symm
      rw [e]
      exact (measurable_topFieldOf T s d (n * ℓ.side)).comp hab
    have hw : Measurable fun u : WeightedResponses.MarkedSample ℓ (s + d) (n * ℓ.side) ×
        WeightedResponses.StepOutcome ℓ n =>
        ENNReal.ofReal (WeightedResponses.stepOutcomeDensity (T.stage (s + d)).toStepSetup
          (WeightedResponses.topField ℓ (s + d) (n * ℓ.side) u.1) u.2) :=
      (hwm.comp ((htop.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
    have hK : Measurable fun z : WeightedResponses.MarkedSample ℓ (s + d) (n * ℓ.side) ×
        WeightedResponses.StepOutcome ℓ n =>
        H ((stateAndCoarser T s d (n * ℓ.side) z.1).1, ((stateAndCoarser T s d (n * ℓ.side) z.1).2, z.2)) :=
      hH.comp ((measurable_fst.comp (hab.comp measurable_fst)).prodMk
        ((measurable_snd.comp (hab.comp measurable_fst)).prodMk measurable_snd))
    have hS : MeasurableSet (ResponseInTheExpansion.sampleBelow ℓ s d (n * ℓ.side) ⁻¹' E) :=
      measurable_sampleBelow s d (n * ℓ.side) hE
    have key := setLIntegral_fst_preimage_withDensity_le (ρ := WeightedResponses.stepReferenceMeasure ℓ n)
      (c := c) hw hK hS (fun δ => by
      have hδ := ih (n * ℓ.side) E hE hb
        (fun p => ENNReal.ofReal (WeightedResponses.stepOutcomeDensity (T.stage (s + d)).toStepSetup
          (topFieldOf T s d (n * ℓ.side) p) δ) * H (p.1, (p.2, δ)))
        ((hwm.comp ((measurable_topFieldOf T s d (n * ℓ.side)).prodMk measurable_const)).ennreal_ofReal.mul
          (hH.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))))
      simp only [topFieldOf_stateAndCoarser] at hδ
      exact hδ)
    exact key
end Samples
theorem conditionalBoundLifts (hD : WeightedResponses.forgetLastStepStatement)
    (hSd : WeightedResponses.StepTransitionDensityBounds)
    (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) : conditionalBoundLiftsStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hDr _
  refine ⟨Tb.floorMin, fun y hy _ _ => ?_⟩
  have hf : (Tb.stepParameters y).Admissible := hDr.fits y hy
  intro T β s d hrun n _ E c hE hb B hB
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h1 : T.base.barrierFn = Tb.cutoff := (hrun.onFamily.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    rw [h1]
    exact hDr.cut
  have hco := hrun.measurable
  have hlaw : ∀ (t m : ℕ) [NeZero m], SFinite (WeightedResponses.markedSampleLaw T β t m) := fun t m _ => by
    have := (hD _ hf hf.depth_lt T hcut hco β t m).1
    infer_instance
  have hq : ∀ (m : ℕ) [NeZero m], Measurable (WeightedResponses.stageState T s m) := fun m _ => hSt _ hf T s m
  obtain ⟨G, hG, rfl⟩ := hB
  have hab : Measurable (stateAndCoarser T s d n) :=
    ((hq _).comp (measurable_sampleBelow s d n)).prodMk (measurable_coarserStepsOf s d n)
  have hBm : MeasurableSet (stateAndCoarser T s d n ⁻¹' G) := hab hG
  have hS : MeasurableSet (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) s d n ⁻¹' E) :=
    measurable_sampleBelow s d n hE
  have key := setLIntegral_stateAndCoarser_le hSd T β s hlaw hco hq d n E hE hb
    (G.indicator fun _ => (1 : ENNReal)) (measurable_const.indicator hG)
  have e : (fun u => G.indicator (fun _ => (1 : ENNReal)) (stateAndCoarser T s d n u)) =
      (stateAndCoarser T s d n ⁻¹' G).indicator fun _ => (1 : ENNReal) := rfl
  simp only [e] at key
  rw [lintegral_indicator_const hBm, lintegral_indicator_const hBm, one_mul, one_mul,
    Measure.restrict_apply hBm] at key
  exact key
end YangMills.Construction.CellWindows
end
