import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepAddUpProof
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.CasesOfAStepCarryAFunction
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StageDensity
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts WeightedResponses ResponseInTheExpansion
  ClusterExpansionOfAStep StepReturn RenormalizationStepParameters StepFloors ColdStepAtMirrorFrames
section SigmaTypes
private theorem measurable_sigma_mk {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  measurable_iff_le_map.2 (iInf_le _ a)
end SigmaTypes
section CoarseStates
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_coarseStateOf {X : Type} [MeasurableSpace X] {Vf : X → TorusField n}
    (hV : Measurable Vf) {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    {bf : X → Finset (TorusBond (n * R.params.side))} (hbad : ∀ a, MeasurableSet {x | bf x = a})
    {cf : X → BaseChoice R.params.side n} (hcf : ∀ a, MeasurableSet {x | cf x = a}) :
    Measurable fun x =>
      coarseStateOf R (hotCoreSites R (Vf x)) (Wf x) (qf x).1 (qf x).2 (bf x) (cf x) := by apply _root_.YangMills.SharedProofs.p10828 <;> assumption
end CoarseStates
section Outcomes
private instance bondSetFintype (m : ℕ) [NeZero m] : Fintype (BondSet m) :=
  inferInstanceAs (Fintype (Finset (TorusBond m)))
variable {ℓ : TorusLumps.StepParameters}
private instance stepReferenceMeasure_isFinite (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem measurable_of_outcome_slices {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private theorem lintegral_stepReferenceMeasure {n : ℕ} [NeZero n] {g : StepOutcome ℓ n → ENNReal}
    (hg : Measurable g) :
    ∫⁻ d, g d ∂(stepReferenceMeasure ℓ n) =
      ∑ b : BaseChoice ℓ.side n, ∫⁻ V : TorusField n,
        ∑ bad : Finset (TorusBond (n * ℓ.side)), g (b, V, bad) ∂(fieldHaar n) := by
  unfold stepReferenceMeasure
  rw [lintegral_prod _ hg.aemeasurable, lintegral_count, tsum_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lintegral_prod (fun y : TorusField n × BondSet (n * ℓ.side) => g (b, y))
    (hg.comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr fun V => ?_
  rw [lintegral_count, tsum_fintype]
  rfl
private theorem lintegral_withDensity_prod {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ρ : Measure B} [SFinite ρ] {w : A × B → ℝ} (hw : Measurable w)
    {f : A × B → ENNReal} (hf : Measurable f) :
    ∫⁻ u, f u ∂((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫⁻ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) * f (a, d) ∂ρ ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hw.ennreal_ofReal hf,
    lintegral_prod _ (hw.ennreal_ofReal.mul hf).aemeasurable]
  rfl
private theorem const_mul_iterated_lintegral {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (f g : A → B → ENNReal) (c : ENNReal) (hg : ∀ a b, g a b = c * f a b)
    (h0 : ∫⁻ a, ∫⁻ b, f a b ∂ν ∂μ = 0 → ∫⁻ a, ∫⁻ b, g a b ∂ν ∂μ = 0) :
    c * ∫⁻ a, ∫⁻ b, f a b ∂ν ∂μ = ∫⁻ a, ∫⁻ b, g a b ∂ν ∂μ := by
  by_cases hc : c = ⊤
  · by_cases hz : ∫⁻ a, ∫⁻ b, f a b ∂ν ∂μ = 0
    · rw [hz, mul_zero, h0 hz]
    · have hle : c * ∫⁻ a, ∫⁻ b, f a b ∂ν ∂μ ≤ ∫⁻ a, ∫⁻ b, g a b ∂ν ∂μ := by
        refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun a => ?_)
        refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun b => ?_)
        exact (hg a b).ge
      rw [hc, ENNReal.top_mul hz] at hle ⊢
      exact (top_le_iff.mp hle).symm
  · simp_rw [hg, lintegral_const_mul' _ _ hc]
end Outcomes
section StepMeans
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hcoin : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R p.1 p.2 := by
  refine measurable_of_outcome_slices fun b bad => ?_
  exact ((hS R.params R.coupling n).1 b).mul (hcoin bad)
private def outcomeTerm (G : TorusField n × CoarseState R n → ENNReal)
    (q : TorusField (n * R.params.side) × Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω))
    (d : StepOutcome R.params n) : ENNReal :=
  ENNReal.ofReal (stepOutcomeDensity R q.1 d) *
    G (d.2.1, coarseStateOf R (hotCoreSites R d.2.1) q.1 q.2.1 q.2.2 d.2.2 d.1)
private theorem measurable_outcomeTerm {X : Type} [MeasurableSpace X]
    (hdraw : Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R p.1 p.2)
    {G : TorusField n × CoarseState R n → ENNReal} (hG : Measurable G)
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    {df : X → StepOutcome R.params n} (hd : Measurable df) :
    Measurable fun x => outcomeTerm G (Wf x, qf x) (df x) := by
  have hV : Measurable fun x => (df x).2.1 := measurable_fst.comp (measurable_snd.comp hd)
  have hb : ∀ a : Finset (TorusBond (n * R.params.side)),
      MeasurableSet {x | ((df x).2.2 : Finset (TorusBond (n * R.params.side))) = a} := by
    intro a
    have hm : Measurable fun x => (df x).2.2 := measurable_snd.comp (measurable_snd.comp hd)
    have hs : MeasurableSet ({a} : Set (BondSet (n * R.params.side))) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hc : ∀ a : BaseChoice R.params.side n, MeasurableSet {x | (df x).1 = a} := by
    intro a
    have hm : Measurable fun x => (df x).1 := measurable_fst.comp hd
    have hs : MeasurableSet ({a} : Set (BaseChoice R.params.side n)) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hst := measurable_coarseStateOf R hV hW hq hb hc
  unfold outcomeTerm
  exact (hdraw.comp (hW.prodMk hd)).ennreal_ofReal.mul (hG.comp (hV.prodMk hst))
private theorem measurable_state_of_fixed_field {G : TorusField n × CoarseState R n → ENNReal}
    (hG : Measurable G) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      G (V, coarseStateOf R (hotCoreSites R V) p.1 Yt p.2 bad b) := by
  have hq : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      (⟨Yt, p.2⟩ : Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) :=
    (measurable_sigma_mk (β := fun Y : Finset (TorusSite (n * R.params.side)) => Y → R.labels.Ω) Yt).comp
      measurable_snd
  have hst := measurable_coarseStateOf R (X := TorusField (n * R.params.side) × (Yt → R.labels.Ω))
    (Vf := fun _ => V) (bf := fun _ => bad) (cf := fun _ => b) measurable_const measurable_fst hq
    (fun a => MeasurableSet.const _) (fun a => MeasurableSet.const _)
  exact hG.comp (measurable_const.prodMk hst)
private theorem measurable_coarseStateMass (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side => coarseStateMass R C V ⟨Y, ω⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseStateMass_measurable <;> assumption
private theorem lintegral_coarseStateMass (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMass R C V bad Yt b ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.lintegral_coarseStateMass <;> assumption
private theorem coarseStateMass_lt_top (hC : ConfigurationSupportedOnCoarseHull)
    (hA : ConfigurationWeightsSum) (hH : CoarseHullIsHullState) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params n) (hn : R.params.n₀ ≤ n) (V : TorusField n)
    (Y : Finset (TorusSite n)) (hY : open Classical in Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩ < ⊤ := by
  classical
  set C := hotCoreSites R V with hCdef
  have hcase : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, configurationMass R C V bad Yt b ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro bad Yt b
    have hmem : coarseHull R.params.side R.range R.nextRange bad Yt C ∈
        Finset.univ.filter (IsHullState R.params R.nextRange V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hH R.params hR.admissible R.range R.nextRange hR.range_le hR.nextRange_ge n hside.1 V bad Yt⟩
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · exact (hC R hR n hn C V bad Yt b).2.2
    · intro Y _ hY
      rw [lintegral_congr fun ω => (hC R hR n hn C V bad Yt b).1 ⟨Y, ω⟩ hY]
      simp
  have htotal : ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V) := by
    simp_rw [lintegral_coarseStateMass hC hR hn C V]
    rw [← hA R hR n hn C V, Finset.sum_comm]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => hcase bad Yt b
  have hfin : ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ htotal.le)
    exact Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))
      (fun _ _ => zero_le) (by convert hY)
  exact ae_lt_top (measurable_coarseStateMass hC hR hn C V Y) hfin
private theorem mul_configurationMass (hc : ConfigurationMassWithFunction) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (G : CoarseState R n → ENNReal)
    (hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      G (coarseStateOf R C p.1 Yt p.2 bad b)) (q : CoarseState R n) :
    G q * configurationMass R C V bad Yt b q =
      configurationMassWith R C V bad Yt b (fun W ωt => G (coarseStateOf R C W Yt ωt bad b)) q := by
  classical
  have h2 := (hc R hR n hn C V bad Yt b (fun W ωt => G (coarseStateOf R C W Yt ωt bad b)) hg).2.1 q
  unfold configurationMass at h2 ⊢
  unfold configurationMassWith at h2 ⊢
  refine const_mul_iterated_lintegral _ _ _ _ _ (fun W ν => ?_) h2
  split_ifs with h
  · beta_reduce
    rw [h.2, mul_comm]
  · simp
private theorem sum_over_hulls_eq (hc : ConfigurationMassWithFunction) (hC : ConfigurationSupportedOnCoarseHull)
    (hA : ConfigurationWeightsSum) (hH : CoarseHullIsHullState) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params n) (hn : R.params.n₀ ≤ n) {G : TorusField n × CoarseState R n → ENNReal}
    (hG : Measurable G) (V : TorusField n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, G (V, ⟨Y, ω⟩) * ENNReal.ofReal (coarseWeightExpansion R n V Y ω)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
    ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
        G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hg := fun (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) => measurable_state_of_fixed_field (R := R) hG V bad Yt b
  set C := hotCoreSites R V with hCdef
  let gf : (bad : Finset (TorusBond (n * R.params.side))) → (Yt : Finset (TorusSite (n * R.params.side))) →
      BaseChoice R.params.side n → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal :=
    fun bad Yt b W ωt => G (V, coarseStateOf R C W Yt ωt bad b)
  have hst := fun (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) => hc R hR n hn C V bad Yt b (gf bad Yt b) (hg bad Yt b)
  have hcm : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (Y : Finset (TorusSite n)),
      Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
        configurationMassWith R C V bad Yt b (gf bad Yt b) ⟨Y, ω⟩ := by
    intro bad Yt b Y
    by_cases h : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
    · subst h
      exact (hst bad Yt b).2.2.1
    · have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
          configurationMassWith R C V bad Yt b (gf bad Yt b) ⟨Y, ω⟩) = fun _ => 0 :=
        funext fun ω => (hst bad Yt b).1 ⟨Y, ω⟩ h
      rw [this]
      exact measurable_const
  have hint : ∀ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, G (V, ⟨Y, ω⟩) * ENNReal.ofReal (coarseWeightExpansion R n V Y ω)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMassWith R C V bad Yt b (gf bad Yt b) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Y hY
    have hae := coarseStateMass_lt_top hC hA hH hR hside hn V Y (by convert hY)
    have hcongr : ∫⁻ ω, G (V, ⟨Y, ω⟩) * ENNReal.ofReal (coarseWeightExpansion R n V Y ω)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
        ∫⁻ ω, ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
          ∑ b : BaseChoice R.params.side n,
          configurationMassWith R C V bad Yt b (gf bad Yt b) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      have e1 : ENNReal.ofReal (coarseWeightExpansion R n V Y ω) = coarseStateMass R C V ⟨Y, ω⟩ := by
        simp only [coarseWeightExpansion, NeZero.ne n, dite_false]
        exact ENNReal.ofReal_toReal hω.ne
      rw [e1]
      show G (V, ⟨Y, ω⟩) * (∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n, configurationMass R C V bad Yt b ⟨Y, ω⟩) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun bad _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Yt _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact mul_configurationMass hc hR hn C V bad Yt b (fun q => G (V, q)) (hg bad Yt b) ⟨Y, ω⟩
    rw [hcongr, lintegral_finsetSum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
      Finset.measurable_sum _ fun b _ => hcm bad Yt b Y]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [lintegral_finsetSum _ fun Yt _ => Finset.measurable_sum _ fun b _ => hcm bad Yt b Y]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [lintegral_finsetSum _ fun b _ => hcm bad Yt b Y]
  have hcase : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, configurationMassWith R C V bad Yt b (gf bad Yt b) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt *
        G (V, coarseStateOf R C W Yt ωt bad b)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro bad Yt b
    have hmem : coarseHull R.params.side R.range R.nextRange bad Yt C ∈
        Finset.univ.filter (IsHullState R.params R.nextRange V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hH R.params hR.admissible R.range R.nextRange hR.range_le hR.nextRange_ge n hside.1 V bad Yt⟩
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · exact (hst bad Yt b).2.2.2
    · intro Y _ hY
      rw [lintegral_congr fun ω => (hst bad Yt b).1 ⟨Y, ω⟩ hY]
      simp
  rw [Finset.sum_congr rfl hint, Finset.sum_comm]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => hcase bad Yt b
private theorem baseLaw_mul_kernel (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c =
      stepTransitionDensity R.params R.coupling W b V := by
  classical
  unfold baseLaw stepTransitionDensity
  split_ifs <;> simp
open Classical in
private def weightedTerm (G : TorusField n × CoarseState R n → ENNReal) (Yt : Finset (TorusSite (n * R.params.side)))
    (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) (d : StepOutcome R.params n) : ENNReal :=
  ENNReal.ofReal (if IsHullState R.params (clusterRange R.coupling) W Yt then
      R.labelWeight (n * R.params.side) W Yt ωt else 0) *
    outcomeTerm G (W, ⟨Yt, ωt⟩) d
private theorem measurable_weightedTerm {X : Type} [MeasurableSpace X] (hR : R.IsWellPosed)
    (hsideL : IsBlockTorusSide R.params (n * R.params.side))
    (hdraw : Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R p.1 p.2)
    {G : TorusField n × CoarseState R n → ENNReal} (hG : Measurable G)
    (Yt : Finset (TorusSite (n * R.params.side)))
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf) {ωf : X → (Yt → R.labels.Ω)}
    (hω : Measurable ωf) {df : X → StepOutcome R.params n} (hd : Measurable df) :
    Measurable fun x => weightedTerm G Yt (Wf x) (ωf x) (df x) := by
  classical
  have h0 : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity := hR.hasExpansions.2
  have h1 := (h0.borel (n * R.params.side) hsideL Yt).1
  have hmk : Measurable fun ω : Yt → R.labels.Ω =>
      (⟨Yt, ω⟩ : Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) :=
    measurable_sigma_mk (β := fun Y : Finset (TorusSite (n * R.params.side)) => Y → R.labels.Ω) Yt
  have a2 : Measurable fun x => outcomeTerm G (Wf x, ⟨Yt, ωf x⟩) (df x) :=
    measurable_outcomeTerm hdraw hG hW (hmk.comp hω) hd
  have a1 : Measurable fun x =>
      ENNReal.ofReal (if IsHullState R.params (clusterRange R.coupling) (Wf x) Yt then
        R.labelWeight (n * R.params.side) (Wf x) Yt (ωf x) else 0) :=
    (h1.comp (hW.prodMk hω)).ennreal_ofReal
  exact a1.mul a2
private theorem weightedTerm_eq (hR : R.IsWellPosed) (hsideL : IsBlockTorusSide R.params (n * R.params.side))
    (hblk : R.params.side ∣ n ∧ 64 ≤ n) (G : TorusField n × CoarseState R n → ENNReal)
    (Yt : Finset (TorusSite (n * R.params.side))) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω)
    (b : BaseChoice R.params.side n) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    weightedTerm G Yt W ωt (b, V, bad) = (open Classical in if bad ⊆ markedBonds R (hotCoreSites R V) then
      configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
        G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b) else 0) := by
  classical
  unfold weightedTerm outcomeTerm stepOutcomeDensity markLaw
  simp only [if_pos hblk]
  by_cases hh : IsHullState R.params (clusterRange R.coupling) W Yt
  · have hnn : 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt :=
      hR.hasExpansions.2.nonneg _ hsideL W Yt ωt hh
    by_cases hb : bad ⊆ markedBonds R (hotCoreSites R V)
    · have hh' : IsHullState R.params R.range W Yt := hh
      simp only [if_pos hb, if_pos hh, configurationWeight, if_pos hh']
      have e : stepWeight R (hotCoreSites R V) V W Yt ωt bad b = R.labelWeight (n * R.params.side) W Yt ωt *
          (stepTransitionDensity R.params R.coupling W b V * markProduct R (hotCoreSites R V) V W bad) := by
        rw [← baseLaw_mul_kernel]
        unfold stepWeight
        ring
      rw [e, ENNReal.ofReal_mul hnn, mul_assoc]
    · simp [if_neg hb]
  · have hh' : ¬ IsHullState R.params R.range W Yt := hh
    simp [if_neg hh, configurationWeight, if_neg hh']
private theorem lintegral_step_eq (hR : R.IsWellPosed) (hsideL : IsBlockTorusSide R.params (n * R.params.side))
    (hblk : R.params.side ∣ n ∧ 64 ≤ n)
    (hdraw : Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R p.1 p.2)
    {G : TorusField n × CoarseState R n → ENNReal} (hG : Measurable G) :
    ∫⁻ W, (open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
        ∫⁻ ωt, (∫⁻ d, outcomeTerm G (W, ⟨Yt, ωt⟩) d ∂(stepReferenceMeasure R.params n)) *
          ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ))
        ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ V, ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
          G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
        ∂(fieldHaar n) := by
  classical
  have hE : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      Measurable fun z : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
        weightedTerm G Yt z.1.1 z.1.2 z.2 :=
    fun Yt => measurable_weightedTerm hR hsideL hdraw hG Yt (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd
  have hdm : ∀ q, Measurable (outcomeTerm G q) := fun q =>
    measurable_outcomeTerm hdraw hG measurable_const measurable_const measurable_id
  have h1 : ∀ W, (∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫⁻ ωt, (∫⁻ d, outcomeTerm G (W, ⟨Yt, ωt⟩) d ∂(stepReferenceMeasure R.params n)) *
        ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ)) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∫⁻ ωt, ∫⁻ d, weightedTerm G Yt W ωt d ∂(stepReferenceMeasure R.params n)
          ∂(Measure.pi fun _ : Yt => R.labels.μ) := by
    intro W
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    by_cases h : IsHullState R.params (clusterRange R.coupling) W Yt
    · rw [if_pos h]
      refine lintegral_congr fun ωt => ?_
      rw [mul_comm, ← lintegral_const_mul _ (hdm _)]
      refine lintegral_congr fun d => ?_
      simp only [weightedTerm, if_pos h]
    · rw [if_neg h]
      simp [weightedTerm, if_neg h]
  have hin : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        ∫⁻ d, weightedTerm G Yt p.1 p.2 d ∂(stepReferenceMeasure R.params n) :=
    fun Yt => (hE Yt).lintegral_prod_right'
  have hin2 : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun W : TorusField (n * R.params.side) =>
      ∫⁻ ωt, ∫⁻ d, weightedTerm G Yt W ωt d ∂(stepReferenceMeasure R.params n)
        ∂(Measure.pi fun _ : Yt => R.labels.μ) := fun Yt => (hin Yt).lintegral_prod_right'
  have hH1 : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      Measurable fun p : StepOutcome R.params n × TorusField (n * R.params.side) =>
        ∫⁻ ωt, weightedTerm G Yt p.2 ωt p.1 ∂(Measure.pi fun _ : Yt => R.labels.μ) := by
    intro Yt
    have hh : Measurable fun z : (StepOutcome R.params n × TorusField (n * R.params.side)) × (Yt → R.labels.Ω) =>
        weightedTerm G Yt z.1.2 z.2 z.1.1 :=
      measurable_weightedTerm hR hsideL hdraw hG Yt (measurable_snd.comp measurable_fst) measurable_snd
        (measurable_fst.comp measurable_fst)
    exact hh.lintegral_prod_right'
  have hH : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun d : StepOutcome R.params n =>
      ∫⁻ W, ∫⁻ ωt, weightedTerm G Yt W ωt d ∂(Measure.pi fun _ : Yt => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) :=
    fun Yt => (hH1 Yt).lintegral_prod_right'
  have h2 : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      ∫⁻ W, ∫⁻ ωt, ∫⁻ d, weightedTerm G Yt W ωt d ∂(stepReferenceMeasure R.params n)
        ∂(Measure.pi fun _ : Yt => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ d, ∫⁻ W, ∫⁻ ωt, weightedTerm G Yt W ωt d ∂(Measure.pi fun _ : Yt => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) ∂(stepReferenceMeasure R.params n) := by
    intro Yt
    have e1 := lintegral_prod (μ := fieldHaar (n * R.params.side)) (ν := Measure.pi fun _ : Yt => R.labels.μ)
      (fun p => ∫⁻ d, weightedTerm G Yt p.1 p.2 d ∂(stepReferenceMeasure R.params n)) (hin Yt).aemeasurable
    have e2 := lintegral_lintegral_swap
      (μ := (fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ))
      (ν := stepReferenceMeasure R.params n) (f := fun p d => weightedTerm G Yt p.1 p.2 d) (hE Yt).aemeasurable
    refine e1.symm.trans (e2.trans (lintegral_congr fun d => ?_))
    exact lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => weightedTerm G Yt p.1 p.2 d)
      (measurable_weightedTerm hR hsideL hdraw hG Yt measurable_fst measurable_snd measurable_const).aemeasurable
  simp_rw [h1]
  rw [lintegral_finsetSum _ fun Yt _ => hin2 Yt]
  simp_rw [h2]
  have hgm : Measurable fun d : StepOutcome R.params n => ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∫⁻ W, ∫⁻ ωt, weightedTerm G Yt W ωt d ∂(Measure.pi fun _ : Yt => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) :=
    Finset.measurable_sum _ fun Yt _ => hH Yt
  rw [← lintegral_finsetSum _ fun Yt _ => hH Yt, lintegral_stepReferenceMeasure hgm]
  have hVm : ∀ b : BaseChoice R.params.side n, Measurable fun V : TorusField n =>
      ∑ bad : Finset (TorusBond (n * R.params.side)),
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∫⁻ W, ∫⁻ ωt, weightedTerm G Yt W ωt (b, V, bad)
        ∂(Measure.pi fun _ : Yt => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := fun b =>
    Finset.measurable_sum _ fun bad _ =>
      hgm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  rw [← lintegral_finsetSum _ fun b _ => hVm b]
  refine lintegral_congr fun V => ?_
  have ht : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (bad : Finset (TorusBond (n * R.params.side))),
      ∫⁻ W, ∫⁻ ωt, weightedTerm G Yt W ωt (b, V, bad) ∂(Measure.pi fun _ : Yt => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) =
      if bad ⊆ markedBonds R (hotCoreSites R V) then
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
          G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
      else 0 := by
    intro Yt b bad
    simp_rw [weightedTerm_eq hR hsideL hblk G Yt]
    split_ifs <;> simp
  simp_rw [ht]
  rw [Finset.sum_comm]
  have hq : ∀ bad : Finset (TorusBond (n * R.params.side)),
      (∑ b : BaseChoice R.params.side n, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      if bad ⊆ markedBonds R (hotCoreSites R V) then
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
          G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
      else 0) = if bad ⊆ markedBonds R (hotCoreSites R V) then
        ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt *
          G (V, coarseStateOf R (hotCoreSites R V) W Yt ωt bad b)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
      else 0 := by
    intro bad
    by_cases h : bad ⊆ markedBonds R (hotCoreSites R V)
    · simp only [if_pos h]
      exact Finset.sum_comm
    · simp [if_neg h]
  simp_rw [hq]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp
end StepMeans
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem blockSide_mul {m : ℕ} (hs : IsBlockTorusSide ℓ m) :
    IsBlockTorusSide ℓ (m * ℓ.side) ∧ ℓ.n₀ ≤ m := by
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h0 : ℓ.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hL) hs.2
  refine ⟨⟨Dvd.intro_left _ rfl, ?_⟩, h0⟩
  rw [Nat.mul_comm m]
  exact Nat.mul_le_mul_left _ h0
private theorem stageState_fst (T : WeightedResponses.StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s n) : (stageState T s n u).1 = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem lintegral_next_stage (hS : StepTransitionDensityBounds) (hB : StageStatesMeasurableStatement)
    (hfit : ℓ.Admissible) (T : WeightedResponses.StageTower ℓ) (hcoin : T.MarksMeasurable) (β : ℝ) (s n : ℕ)
    [NeZero n] {G : StageState T (s + 1) n → ENNReal} (hG : Measurable G) :
    ∫⁻ u, G (stageState T (s + 1) n u) ∂(markedSampleLaw T β (s + 1) n) =
      ∫⁻ a, ∫⁻ d, outcomeTerm (R := (T.stage s).toStepSetup) G (stageState T s (n * ℓ.side) a) d
        ∂(stepReferenceMeasure ℓ n) ∂(markedSampleLaw T β s (n * ℓ.side)) := by
  have hd := measurable_stepOutcomeDensity (R := (T.stage s).toStepSetup) (n := n) hS (fun bad => hcoin s n bad)
  have htop : Measurable fun a : MarkedSample ℓ s (n * ℓ.side) => (stageState T s (n * ℓ.side) a).1 :=
    measurable_fst.comp (hB ℓ hfit T s (n * ℓ.side))
  have hw : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2 := by
    have e : (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2) =
        fun u => stepOutcomeDensity (T.stage s).toStepSetup (stageState T s (n * ℓ.side) u.1).1 u.2 := by
      funext u
      rw [stageState_fst]
    rw [e]
    have h3 := hd.comp ((htop.comp measurable_fst).prodMk measurable_snd)
    exact h3
  have hf : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      G (stageState T (s + 1) n u) := by
    have h3 := hG.comp (hB ℓ hfit T (s + 1) n)
    exact h3
  have key := lintegral_withDensity_prod (μ := markedSampleLaw T β s (n * ℓ.side))
    (ρ := stepReferenceMeasure ℓ n) hw hf
  refine key.trans (lintegral_congr fun a => lintegral_congr fun d => ?_)
  show ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) a) d) *
      G (stageState T (s + 1) n (a, d)) =
    ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (stageState T s (n * ℓ.side) a).1 d) *
      G (stageState T (s + 1) n (a, d))
  rw [stageState_fst]
private theorem density_succ (hc : ConfigurationMassWithFunction) (hC : ConfigurationSupportedOnCoarseHull)
    (hA : ConfigurationWeightsSum) (hH : CoarseHullIsHullState) (hS : StepTransitionDensityBounds)
    (hB : StageStatesMeasurableStatement) (hfit : ℓ.Admissible) (T : WeightedResponses.StageTower ℓ)
    (hcoin : T.MarksMeasurable) (β : ℝ) (s n : ℕ) [NeZero n] (hR : (T.stage s).toStepSetup.IsWellPosed)
    (hside : IsBlockTorusSide ℓ n) (c : ENNReal)
    (ih : ∀ G' : StageState T s (n * ℓ.side) → ENNReal, Measurable G' →
      c * ∫⁻ u, G' (stageState T s (n * ℓ.side) u) ∂(markedSampleLaw T β s (n * ℓ.side)) =
      ∫⁻ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange (T.stage s).coupling) W),
        ∫⁻ ω, G' (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage s).labelWeight (n * ℓ.side) W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage s).labels.μ)) ∂(fieldHaar (n * ℓ.side)))
    {G : StageState T (s + 1) n → ENNReal} (hG : Measurable G) :
    c * ∫⁻ u, G (stageState T (s + 1) n u) ∂(markedSampleLaw T β (s + 1) n) =
    ∫⁻ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange (T.stage (s + 1)).coupling) W),
      ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage (s + 1)).labelWeight n W Y ω)
        ∂(Measure.pi fun _ : Y => (T.stage (s + 1)).labels.μ)) ∂(fieldHaar n) := by
  classical
  have hd := measurable_stepOutcomeDensity (R := (T.stage s).toStepSetup) (n := n) hS (fun bad => hcoin s n bad)
  obtain ⟨hsideL, hn⟩ := blockSide_mul hside
  have hK : Measurable fun q : StageState T s (n * ℓ.side) =>
      ∫⁻ d, outcomeTerm (R := (T.stage s).toStepSetup) G q d ∂(stepReferenceMeasure ℓ n) := by
    have hh : Measurable fun z : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
        outcomeTerm (R := (T.stage s).toStepSetup) G (z.1.1, z.1.2) z.2 :=
      measurable_outcomeTerm hd hG (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
        measurable_snd
    exact hh.lintegral_prod_right'
  refine (congrArg (c * ·) (lintegral_next_stage hS hB hfit T hcoin β s n hG)).trans ((ih _ hK).trans ?_)
  have hblk : (T.stage s).toStepSetup.params.side ∣ n ∧ 64 ≤ n :=
    ⟨hside.1, le_trans (le_trans (by norm_num) hR.admissible.n₀_ge) hn⟩
  refine (lintegral_step_eq (R := (T.stage s).toStepSetup) hR hsideL hblk hd hG).trans ?_
  exact lintegral_congr fun V => (sum_over_hulls_eq hc hC hA hH hR hside hn hG V).symm
private theorem density_base (T : WeightedResponses.StageTower ℓ) (β : ℝ)
    (hst : ResponseInTheExpansion.StageTower.StartsAtWilson T β) (n : ℕ) [NeZero n]
    (hm : Measurable (wilsonWeight β n)) (hpos : 0 < ∫ W, wilsonWeight β n W ∂(fieldHaar n))
    (hB : Measurable (stageState T 0 n)) {G : StageState T 0 n → ENNReal} (hG : Measurable G) :
    ENNReal.ofReal (∫ W, wilsonWeight β n W ∂(fieldHaar n)) *
      ∫⁻ u, G (stageState T 0 n u) ∂(markedSampleLaw T β 0 n) =
    ∫⁻ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange T.base.coupling) W),
      ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal (T.base.labelWeight n W Y ω)
        ∂(Measure.pi fun _ : Y => T.base.labels.μ)) ∂(fieldHaar n) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, c = ∫ W, wilsonWeight β n W ∂(fieldHaar n) := ⟨_, rfl⟩
  rw [← hc] at hpos ⊢
  have hwe : ∀ W : TorusField n, wilsonWeight β n W = Real.exp (-β * wilsonAction Finset.univ W) := fun W => by
    simp [wilsonWeight, NeZero.ne n]
  have hlaw : wilsonLaw β n = (fieldHaar n).withDensity fun W => ENNReal.ofReal (wilsonWeight β n W / c) := by
    have hcc : (∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar n)) = c := by
      rw [hc]
      exact integral_congr_ae (Filter.Eventually.of_forall fun W => (hwe W).symm)
    unfold wilsonLaw
    rw [hcc]
    simp_rw [hwe]
  have hdens : Measurable fun W : TorusField n => ENNReal.ofReal (wilsonWeight β n W / c) :=
    (hm.div_const c).ennreal_ofReal
  have hf : Measurable fun u : TorusField n => G (stageState T 0 n u) := by
    have h3 := hG.comp hB
    exact h3
  have hμ : T.base.labels.μ Set.univ = 1 := by
    have e : (Set.univ : Set T.base.labels.Ω) = {T.basePoint} := by
      ext x
      simp [hst.eq_basePoint x]
    rw [e]
    exact hst.measure_basePoint
  have : IsProbabilityMeasure T.base.labels.μ := ⟨hμ⟩
  have hL : ∫⁻ u, G (stageState T 0 n u) ∂(markedSampleLaw T β 0 n) =
      ∫⁻ W : TorusField n, ENNReal.ofReal (wilsonWeight β n W / c) * G (stageState T 0 n W) ∂(fieldHaar n) := by
    show ∫⁻ u : TorusField n, G (stageState T 0 n u) ∂(wilsonLaw β n) = _
    rw [hlaw, lintegral_withDensity_eq_lintegral_mul _ hdens hf]
    rfl
  rw [hL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun W => ?_
  have hmem : thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W) ∈
      Finset.univ.filter (IsHullState ℓ (clusterRange T.base.coupling) W) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, minimalHull_isHullState⟩
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · have hconst : ∀ ω : thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W) → T.base.labels.Ω,
        G (W, ⟨_, ω⟩) * ENNReal.ofReal (T.base.labelWeight n W _ ω) =
          G (stageState T 0 n W) * ENNReal.ofReal (wilsonWeight β n W) := by
      intro ω
      have e : ω = fun _ => T.basePoint := funext fun z => hst.eq_basePoint (ω z)
      have hD := hst.labelWeight_eq n W _ ω
      rw [if_pos rfl] at hD
      rw [hD, e]
      rfl
    rw [lintegral_congr hconst, lintegral_const, measure_univ, mul_one]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne', mul_comm]
  · intro Y _ hY
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    rw [hst.labelWeight_eq n W Y ω, if_neg hY]
    simp
private theorem expansion_next (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (hr : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem expansion_along_flow (hret : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ j : ℕ, (∀ i < j, ℓ.y₁ ≤ (couplingFlow ℓ β i).1) →
      HasExpansion ℓ j (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2
  | 0, _ => h0
  | j + 1, h => (expansion_next hret (h j (Nat.lt_succ_self j))
      (expansion_along_flow hret h0 j fun i hi => h i (Nat.lt_succ_of_lt hi))).1
private theorem stage_functional_eq {Tb : ParameterAssignment} {y : ℝ}
    {T : WeightedResponses.StageTower (Tb.stepParameters y)} {β : ℝ} {k : ℕ}
    (hst : IsTowerAtParameters Tb y T β k) :
    ∀ j ≤ k + 1, (T.stage j).functional = (couplingFlow (Tb.stepParameters y) β j).2
  | 0, _ => hst.startsAtWilson.functional_eq
  | j + 1, hj => by
    have h1 := stage_functional_eq hst j (by omega)
    have h2 := hst.coupling_eq j (by omega)
    show kernelImage (Tb.stepParameters y) (T.stage j).coupling (T.stage j).functional =
      kernelImage (Tb.stepParameters y) _ _
    rw [h1, h2]
private theorem stage_wellPosed {Tb : ParameterAssignment} (hT : Tb.Admissible) {y yF : ℝ} (hy₀ : Tb.floorMin ≤ y)
    (hy₁ : 1 ≤ y) (hyy : yF ≤ y)
    (hyF : ∀ x : ℝ, yF ≤ x → Tb.FloorConditions (2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17) 1 x)
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hwil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    {T : WeightedResponses.StageTower (Tb.stepParameters y)} {β : ℝ} {k : ℕ}
    (hst : IsTowerAtParameters Tb y T β k) {j : ℕ} (hj : j ≤ k) : (T.stage j).toStepSetup.IsWellPosed := by
  have hx := hst.coupling_eq
  have hfloor : ∀ i ≤ k, y ≤ (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi => by
    rw [← hx i (by omega)]
    exact (hst.onFamily i hi).le_coupling
  have hβ : y ≤ β := hfloor 0 (Nat.zero_le _)
  have hrow : ∀ i ≤ k, HasExpansion (Tb.stepParameters y) i (couplingFlow (Tb.stepParameters y) β i).1
      (couplingFlow (Tb.stepParameters y) β i).2 := fun i hi =>
    expansion_along_flow hret (hwil β hβ) i fun i' h => hfloor i' (by omega)
  have hon := hst.onFamily j hj
  have hmoved : |(T.stage j).toStepSetup.nextCoupling - (T.stage j).toStepSetup.coupling| ≤ 2 * Tb.B := by
    have h1 : (T.stage j).toStepSetup.nextCoupling = (couplingFlow (Tb.stepParameters y) β (j + 1)).1 :=
      hx (j + 1) (by omega)
    have h0 : (T.stage j).toStepSetup.coupling = (couplingFlow (Tb.stepParameters y) β j).1 := hx j (by omega)
    rw [h1, h0]
    exact (expansion_next hret (hfloor j hj) (hrow j hj)).2
  have hArr : (T.stage j).toStepSetup.IsSymmetricWeight := by
    intro m _ hm
    have e : (T.stage j).toStepSetup.functional = (couplingFlow (Tb.stepParameters y) β j).2 :=
      stage_functional_eq hst j (by omega)
    rw [e]
    exact (hrow j hj).1 m hm
  have hF := hyF _ (hyy.trans hon.le_coupling)
  have hfit : (T.stage j).toStepSetup.params.Admissible := hT.fits y hy₀
  have hxpos : 0 < (T.stage j).toStepSetup.coupling := lt_of_lt_of_le one_pos (hy₁.trans hon.le_coupling)
  obtain ⟨_, hy9⟩ := hF.stable_nearby
  obtain ⟨_, _, hr1, hr2⟩ := hy9 _ hmoved
  have hr : (2 : ℝ) ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 ≤ clusterRange (T.stage j).toStepSetup.coupling :=
    hF.range_ge
  have hr' : 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 ≤ clusterRange (T.stage j).toStepSetup.coupling := by
    exact_mod_cast hr
  have hLL : (T.stage j).toStepSetup.params.side = Tb.side := rfl
  have hNN : (T.stage j).toStepSetup.params.n₀ = Tb.n₀ := rfl
  have hρ : (T.stage j).toStepSetup.ballRadius = Tb.ballRadius := rfl
  have hcut : IsCutoff (T.stage j).toStepSetup.ballRadius (T.stage j).toStepSetup.barrierFn := by
    rw [hρ, hon.barrierFn_eq]
    exact hT.cut
  refine ⟨hon.isStep.1, hfit, hcut, hr1, hr2, ?_, ?_, ?_, hxpos, hArr⟩
  · show 2 ^ 16 ≤ clusterRange (T.stage j).toStepSetup.nextCoupling
    omega
  · show 2 ^ 40 * (T.stage j).toStepSetup.params.side ≤ clusterRange (T.stage j).toStepSetup.coupling
    omega
  · show 4 * (T.stage j).toStepSetup.params.n₀ + 2 ^ 16 ≤ clusterRange (T.stage j).toStepSetup.coupling
    omega
end Tower
theorem stageStateDensity_holds (hc : ConfigurationMassWithFunction)
    (hC : ConfigurationSupportedOnCoarseHull) (hA : ConfigurationWeightsSum) (hH : CoarseHullIsHullState)
    (hS : StepTransitionDensityBounds) (hB : StageStatesMeasurableStatement) (hLaw : ChainIsProbabilityLaw)
    (hFl : EventuallyFloorConditions) : stageStateDensityStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ Tb _ _ hT _ => ?_⟩
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl Tb hT _ 1 hCpos one_pos
  refine ⟨max (max Tb.floorMin yF) 1, fun y hy hret hwil T β k n _ hst hcoin hside G hG => ?_⟩
  have h1 : Tb.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h2 : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h3 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hform := fun (j : ℕ) (hj : j ≤ k) => stage_wellPosed hT h1 h3 h2 hyF hret hwil hst hj
  have hfit : (Tb.stepParameters y).Admissible := hT.fits y h1
  have hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hT.L_gt
  have hβ : y ≤ β := by
    have e : (T.stage 0).coupling = β := hst.coupling_eq 0 (Nat.zero_le _)
    rw [← e]
    exact (hst.onFamily 0 (Nat.zero_le _)).le_coupling
  have key : ∀ j ≤ k, ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (Tb.stepParameters y) m →
      ∀ G : StageState T j m → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side j m) W
          ∂(fieldHaar (fineSide (Tb.stepParameters y).side j m))) *
        ∫⁻ u, G (stageState T j m u) ∂(markedSampleLaw T β j m) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage j).labelWeight m W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage j).labels.μ)) ∂(fieldHaar m) := by
    intro j
    induction j with
    | zero =>
      intro _ m _ hs G hG
      exact density_base T β hst.startsAtWilson m ((hwil β hβ).1 m (blockSide_mul hs).2).1
        (hLaw _ hfit hLgt β (fun _ => 0) 0 m).2.1 (hB _ hfit T 0 m) hG
    | succ j ih =>
      intro hj m _ hs G hG
      exact density_succ hc hC hA hH hS hB hfit T hcoin β j m (hform j (by omega)) hs _
        (fun G' hG' => ih (by omega) (m * (Tb.stepParameters y).side) (blockSide_mul hs).1 G' hG') hG
  exact key k le_rfl n hside G hG
end YangMills.Construction.StageDensity
end
