import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStepHasOneState
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepAddUp
import YangMills.Construction.ClusterExpansionOfAStep.WeightsOfAStepAddUp
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coarseStateMass_eq_sum (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) :
    coarseStateMass R C V q = ∑ bad ∈ (markedBonds R C).powerset,
      ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, configurationMass R C V bad Yt b q := rfl
theorem configurationMass_measurable (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      configurationMass R C V bad Yt b ⟨Y, ω⟩ := by
  classical
  by_cases h : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst h
    exact (hC R hR n hn C V bad Yt b).2.1
  · have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
        configurationMass R C V bad Yt b ⟨Y, ω⟩) = fun _ => 0 :=
      funext fun ω => (hC R hR n hn C V bad Yt b).1 ⟨Y, ω⟩ h
    rw [this]
    exact measurable_const
theorem coarseStateMass_measurable (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side => coarseStateMass R C V ⟨Y, ω⟩ :=
  Finset.measurable_sum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
    Finset.measurable_sum _ fun b _ => configurationMass_measurable hC hR hn C V bad Yt b Y
theorem lintegral_coarseStateMass (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMass R C V bad Yt b ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
  simp only [coarseStateMass_eq_sum]
  rw [lintegral_finsetSum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
    Finset.measurable_sum _ fun b _ => configurationMass_measurable hC hR hn C V bad Yt b Y]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [lintegral_finsetSum _ fun Yt _ => Finset.measurable_sum _ fun b _ =>
    configurationMass_measurable hC hR hn C V bad Yt b Y]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [lintegral_finsetSum _ fun b _ => configurationMass_measurable hC hR hn C V bad Yt b Y]
theorem coarseStatesSum (hC : ConfigurationSupportedOnCoarseHull) (hA : ConfigurationWeightsSum)
    (hH : CoarseHullIsHullState) : coarseStatesSumStatement := by
  classical
  intro R hR n _ hside V
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hside.2
  set C := hotCoreSites R V with hCdef
  have hcase : ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
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
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V) := by
    simp_rw [lintegral_coarseStateMass hC hR hn C V]
    rw [← hA R hR n hn C V, Finset.sum_comm]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => hcase bad Yt b
  rw [← htotal]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hfin : ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ htotal.le)
    exact Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))
      (fun _ _ => zero_le) hY
  have hae := ae_lt_top (coarseStateMass_measurable hC hR hn C V Y) hfin
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ω hω
  exact ENNReal.ofReal_toReal hω.ne
end YangMills.Construction.ClusterExpansionOfAStep
end
