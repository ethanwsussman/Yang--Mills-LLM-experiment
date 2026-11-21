import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsHaveTheirBases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_topField : ∀ (s n : ℕ), Measurable (WeightedResponses.topField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    letI := WeightedResponses.markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem measurableSet_mem_baseChoices (hK : TorusLumps.BondKernelBorel) (n : ℕ) [NeZero n]
    (b : StepCosts.BaseChoice ℓ.side n) :
    MeasurableSet {W : TorusFields.TorusField (n * ℓ.side) |
      b ∈ TorusLumps.baseChoices ℓ (TorusLumps.fineLevelField ℓ n W)} := by
  obtain ⟨-, hfin, -, hset, -⟩ := hK ℓ 0 n
  have hEq : {W : TorusFields.TorusField (n * ℓ.side) |
        b ∈ TorusLumps.baseChoices ℓ (TorusLumps.fineLevelField ℓ n W)} =
      ⋃ A ∈ (Set.range fun W : TorusFields.TorusField (n * ℓ.side) =>
          TorusLumps.baseChoices ℓ (TorusLumps.fineLevelField ℓ n W)) ∩ {A | b ∈ A},
        {W : TorusFields.TorusField (n * ℓ.side) |
          TorusLumps.baseChoices ℓ (TorusLumps.fineLevelField ℓ n W) = A} := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨⟨W, rfl⟩, h⟩, rfl⟩
    · rintro ⟨A, ⟨-, hb⟩, hA⟩
      rw [hA]
      exact hb
  rw [hEq]
  exact (hfin.subset Set.inter_subset_left).measurableSet_biUnion fun A _ => hset A
private theorem measurableSet_not_mem_baseChoices (hK : TorusLumps.BondKernelBorel) (s n : ℕ) [NeZero n] :
    letI := WeightedResponses.markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    MeasurableSet {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n |
      u.2.1 ∉ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
        (WeightedResponses.topField ℓ s (n * ℓ.side) u.1))} := by
  letI := WeightedResponses.markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  have hEq : {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n |
      u.2.1 ∉ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
        (WeightedResponses.topField ℓ s (n * ℓ.side) u.1))} =
      ⋃ b : StepCosts.BaseChoice ℓ.side n,
        {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n | u.2.1 = b} ∩
        (fun u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n =>
            WeightedResponses.topField ℓ s (n * ℓ.side) u.1) ⁻¹'
          {W : TorusFields.TorusField (n * ℓ.side) |
            b ∈ TorusLumps.baseChoices ℓ (TorusLumps.fineLevelField ℓ n W)}ᶜ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro h
      exact ⟨u.2.1, rfl, h⟩
    · rintro ⟨b, rfl, h⟩
      exact h
  rw [hEq]
  refine MeasurableSet.iUnion fun b => MeasurableSet.inter ?_ ?_
  · have hb : MeasurableSet ({b} : Set (StepCosts.BaseChoice ℓ.side n)) := MeasurableSpace.measurableSet_top
    exact (measurable_fst.comp measurable_snd) hb
  · exact ((measurable_topField s (n * ℓ.side)).comp measurable_fst)
      (measurableSet_mem_baseChoices hK n b).compl
private theorem ae_mem_baseChoices_step (hK : TorusLumps.BondKernelBorel) (T : WeightedResponses.StageTower ℓ)
    (β : ℝ) (s n : ℕ) [NeZero n] :
    ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (s + 1) n),
      u.2.1 ∈ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
        (WeightedResponses.topField ℓ s (n * ℓ.side) u.1)) := by
  letI := WeightedResponses.markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  have hM := measurableSet_not_mem_baseChoices (ℓ := ℓ) hK s n
  have hzero : (((WeightedResponses.markedSampleLaw T β s (n * ℓ.side)).prod
      (WeightedResponses.stepReferenceMeasure ℓ n)).withDensity fun u =>
      ENNReal.ofReal (WeightedResponses.stepOutcomeDensity (T.stage s).toStepSetup
        (WeightedResponses.topField ℓ s (n * ℓ.side) u.1) u.2))
      {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n |
        u.2.1 ∉ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
          (WeightedResponses.topField ℓ s (n * ℓ.side) u.1))} = 0 := by
    rw [withDensity_apply _ hM]
    have hc : ∫⁻ u in {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n |
          u.2.1 ∉ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
            (WeightedResponses.topField ℓ s (n * ℓ.side) u.1))},
          ENNReal.ofReal (WeightedResponses.stepOutcomeDensity (T.stage s).toStepSetup
            (WeightedResponses.topField ℓ s (n * ℓ.side) u.1) u.2)
            ∂((WeightedResponses.markedSampleLaw T β s (n * ℓ.side)).prod
              (WeightedResponses.stepReferenceMeasure ℓ n)) =
        ∫⁻ _ in {u : WeightedResponses.MarkedSample ℓ s (n * ℓ.side) × WeightedResponses.StepOutcome ℓ n |
          u.2.1 ∉ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
            (WeightedResponses.topField ℓ s (n * ℓ.side) u.1))}, 0
            ∂((WeightedResponses.markedSampleLaw T β s (n * ℓ.side)).prod
              (WeightedResponses.stepReferenceMeasure ℓ n)) := by
      refine setLIntegral_congr_fun hM fun u hu => ?_
      have hd : WeightedResponses.stepTransitionDensity ℓ (T.stage s).toStepSetup.coupling
          (WeightedResponses.topField ℓ s (n * ℓ.side) u.1) u.2.1 u.2.2.1 = 0 :=
        if_neg hu
      show ENNReal.ofReal (WeightedResponses.stepTransitionDensity ℓ (T.stage s).toStepSetup.coupling
          (WeightedResponses.topField ℓ s (n * ℓ.side) u.1) u.2.1 u.2.2.1 *
        WeightedResponses.markLaw (T.stage s).toStepSetup
          (WeightedResponses.topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.2.2) = 0
      rw [hd, zero_mul, ENNReal.ofReal_zero]
    rw [hc]
    simp
  rw [ae_iff]
  exact hzero
theorem ae_hasBaseChoices_of_bondKernelBorel (hK : TorusLumps.BondKernelBorel) :
    ae_hasBaseChoicesStatement := by
  intro ℓ T β k d
  induction d with
  | zero =>
    intro n _
    exact Filter.Eventually.of_forall fun _ => trivial
  | succ d ih =>
    intro n _
    letI := WeightedResponses.markedSampleMeasurableSpace ℓ (k + d) (n * ℓ.side)
    have hac : WeightedResponses.markedSampleLaw T β (k + d + 1) n ≪
        (WeightedResponses.markedSampleLaw T β (k + d) (n * ℓ.side)).prod
          (WeightedResponses.stepReferenceMeasure ℓ n) :=
      withDensity_absolutelyContinuous _ _
    have hlow : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + d + 1) n),
        HasBaseChoices ℓ k d (n * ℓ.side) u.1 :=
      hac.ae_le (Measure.quasiMeasurePreserving_fst.ae (ih (n * ℓ.side)))
    filter_upwards [ae_mem_baseChoices_step hK T β (k + d) n, hlow] with u h₁ h₂
    exact ⟨h₁, h₂⟩
end YangMills.Construction.BoxEvents
end
