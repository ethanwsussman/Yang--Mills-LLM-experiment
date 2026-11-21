import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStepHasOneState
import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ClusterExpansionOfAStep.StateOverAColdField
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ClusterExpansionOfAStep.WeightsOfAStepAddUp
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coarseHull_empty (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
  classical
  have hb : sitesInBlocks R.params.side (∅ : Finset (TorusSite n)) = ∅ := by
    ext x
    simp [sitesInBlocks]
  have ha : attachedSites R.params.side R.range bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    simp [attachedSites, hb]
  have hc : coreBlocks R.params.side R.range (∅ : Finset (TorusSite (n * R.params.side))) =
      (∅ : Finset (TorusSite n)) := by
    ext y
    simp [coreBlocks, thickening]
  have hs : storedBlocks R.params.side R.range bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    simp [storedBlocks, ha, hc]
  ext z
  simp [coarseHull, hs, thickening]
theorem configurationMass_of_empty (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (Y : Finset (TorusSite n))
    (hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    configurationMass R ∅ V bad Yt b ⟨Y, ω⟩ =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  subst hY
  obtain ⟨-, hm, hi⟩ := hC R hR n hn ∅ V bad Yt b
  rw [← hi]
  have he : IsEmpty (coarseHull R.params.side R.range R.nextRange bad Yt
      (∅ : Finset (TorusSite n))) :=
    ⟨fun x => by
      obtain ⟨z, hz⟩ := x
      rw [coarseHull_empty] at hz
      simp at hz⟩
  rw [Measure.pi_of_empty _ ω, lintegral_dirac' _ hm]
theorem coldFieldState_holds (hC : ConfigurationSupportedOnCoarseHull) (hA : ConfigurationWeightsSum)
    (hK : KernelImageIsDensity) : coldFieldStateStatement := by
  classical
  intro R hR n _ hn
  refine ⟨fun V ω => ?_, fun hside V hV => ?_⟩
  · have hexp : HasExpansion R.params R.depth R.coupling R.functional :=
      ⟨hR.functional_spec, R.density, hR.hasExpansions.1, R.labels, R.labelWeight, R.clusterFactor,
        R.siteDensity, hR.hasExpansions.2⟩
    have himage := hK R.params hR.admissible R.depth R.coupling R.functional hR.coupling_pos
      hR.range_ge_base hexp n hn
    have hm : coarseStateMass R ∅ V ⟨∅, ω⟩ =
        ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V) := by
      rw [← hA R hR n hn ∅ V]
      refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ =>
        Finset.sum_congr rfl fun b _ => ?_
      exact configurationMass_of_empty hC hR hn V bad Yt b ∅ (coarseHull_empty bad Yt).symm ω
    unfold coarseStateWeight
    rw [hm, ENNReal.toReal_ofReal (himage.2.2.1 V)]
  · have hhot : torusHotLumps R.params V = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
      obtain ⟨x, μ, ν, h1, h2, -⟩ := (mem_torusHotLumps_iff R.params hR.admissible hside.1 V l).mp hl
      exact absurd (hV x μ ν h1) (not_lt.mpr h2)
    have hsites : torusHotSites R.params V = ∅ := by
      simp [torusHotSites, hhot]
    refine ⟨?_, fun Y => ⟨fun hY => ?_, fun hY => ?_⟩⟩
    · ext z
      simp [hotCoreSites, hsites, thickening]
    · refine Finset.eq_empty_of_forall_notMem fun y hy => ?_
      have hc : Y.filter (ChainConnected R.nextRange Y y) ∈ chainComponents R.nextRange Y :=
        Finset.mem_image.mpr ⟨y, hy, rfl⟩
      obtain ⟨l, hl, -⟩ := hY.2 _ hc
      simp [hhot] at hl
    · subst hY
      refine ⟨?_, ?_⟩
      · simp [hsites, thickening]
      · intro X hX
        simp [chainComponents] at hX
end YangMills.Construction.ClusterExpansionOfAStep
end
