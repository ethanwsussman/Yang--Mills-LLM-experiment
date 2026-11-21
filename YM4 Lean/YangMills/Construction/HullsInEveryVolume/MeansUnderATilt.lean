import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open RenormalizationStepParameters WeightedResponses TorusFields TorusLumps BlockAverages ChainNoise HullTrees ResponseInTheExpansion
namespace TiltedMeans
variable {ℓ : StepParameters}
instance isProbabilityMeasure_stepNoiseLaw (ℓ : StepParameters) (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
  unfold stepNoiseLaw
  infer_instance
theorem isProbabilityMeasure_chainNoiseLaw (ℓ : StepParameters) :
    ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n)
  | 0, n, _ => by
    unfold chainNoiseLaw
    exact Measure.dirac.isProbabilityMeasure
  | s + 1, n, _ => by
    have := isProbabilityMeasure_chainNoiseLaw ℓ s (n * ℓ.side)
    unfold chainNoiseLaw
    exact Measure.prod.instIsProbabilityMeasure _ _
instance instIsProbabilityMeasureChainNoiseLaw (ℓ : StepParameters) (s n : ℕ) [NeZero n] :
    IsProbabilityMeasure (chainNoiseLaw ℓ s n) :=
  isProbabilityMeasure_chainNoiseLaw ℓ s n
instance isProbabilityMeasure_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : IsProbabilityMeasure (wilsonLaw β m) := by
  constructor
  have : SecondCountableTopology UnitQuaternion := TopologicalSpace.Subtype.secondCountableTopology _
  have hc : Continuous fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := TorusField m)).exists_bound_of_continuousOn hc.continuousOn
  have hI : Integrable (fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W)) (fieldHaar m) :=
    Integrable.of_bound hc.measurable.aestronglyMeasurable C (ae_of_all _ fun W => hC W (Set.mem_univ _))
  have hZ : 0 < ∫ W, Real.exp (-β * wilsonAction Finset.univ W) ∂(fieldHaar m) := integral_exp_pos hI
  unfold wilsonLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hI.div_const _)
      (Filter.Eventually.of_forall fun W => div_nonneg (Real.exp_nonneg _) hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]
end TiltedMeans
end YangMills.Construction
end
