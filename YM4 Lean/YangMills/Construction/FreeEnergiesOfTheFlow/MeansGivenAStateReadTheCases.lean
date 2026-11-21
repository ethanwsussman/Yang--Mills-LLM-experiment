import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def ReadsCasesAt {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n] : Prop :=
      (∀ (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n) W Yt ωt bad b, 0 ≤ StepSettings.stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b) ∧
      ((∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n (fun _ _ _ _ _ _ => 1) x) →
        (∀ (F : TorusFields.TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n), Measurable (caseLift T s n F) → ∀ K : ℝ,
          (∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), |caseLift T s n F x| ≤ K) →
          (∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n F x) →
          (WeightedResponses.markedSampleLaw T β (s + 1) n)[caseLift T s n F | WeightedResponses.stageSigma T (s + 1) n] =ᵐ[WeightedResponses.markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n F) ∧
        (∀ (φ : TorusFields.TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n), (∀ V W Yt ωt bad b, 0 ≤ φ V W Yt ωt bad b) →
          Measurable (caseLift T s n φ) → (∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n φ x) →
          ∀ (D : WeightedResponses.MarkedSample ℓ (s + 1) n → ℝ) (K : ℝ), Integrable D (WeightedResponses.markedSampleLaw T β (s + 1) n) →
          (∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), |D x| ≤ K) →
          (∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n), |D x| ≤ caseLift T s n φ x) →
          ∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n),
            |((WeightedResponses.markedSampleLaw T β (s + 1) n)[D | WeightedResponses.stageSigma T (s + 1) n]) x| ≤ caseMeanAtSample T s n φ x))
def conditionalMeanReadsCasesStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    ResponseInTheExpansion.IsTowerAtParameters Tb y T β s → ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed → TorusLumps.IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) → (Tb.stepParameters y).side ∣ n →
    ReadsCasesAt T β s n
end YangMills.Construction.FreeEnergies
end
