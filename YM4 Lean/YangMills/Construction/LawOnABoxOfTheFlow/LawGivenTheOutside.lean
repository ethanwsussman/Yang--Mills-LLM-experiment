import YangMills.Construction.LawOnABoxOfTheFlow.HaarMeasureInTheChart
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion RenormalizationStepParameters BlockAverages
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
open Classical in
def hullStateDensity (T : StageTower ℓ) (k : ℕ) (o : TorusSite n) (R : ℕ)
    (p : OuterData T k o R × InnerField o R) : ENNReal :=
  ENNReal.ofReal (if IsHullState ℓ (clusterRange (T.stage k).coupling) (glueField p.1.1 p.2) p.1.2.1 then
    (T.stage k).labelWeight n (glueField p.1.1 p.2) p.1.2.1 p.1.2.2 else 0)
def outerReferenceIntegral (T : StageTower ℓ) (k : ℕ) (o : TorusSite n) (R : ℕ)
    (J : OuterData T k o R → ENNReal) : ENNReal :=
  ∑ Y : Finset (TorusSite n), ∫⁻ ω, ∫⁻ V, J (restrictOuter o R V, ⟨Y, ω⟩) ∂(fieldHaar n)
    ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)
def conditionalLawGivenOuterStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n]
    (o : TorusSite n) (R : ℕ),
    IsTowerAtParameters Tb y T β k → T.MarksMeasurable → IsBlockTorusSide (Tb.stepParameters y) n →
    Measurable (hullStateDensity T k o R) ∧
    ∃ Z : ENNReal, Z ≠ 0 ∧ Z ≠ ⊤ ∧
      ∀ H : OuterData T k o R × InnerField o R → ENNReal, Measurable H →
        Z * ∫⁻ u, H (outerData T k o R (stageState T k n u), restrictInner o R (stageState T k n u).1)
            ∂(markedSampleLaw T β k n) =
          outerReferenceIntegral T k o R fun q =>
            ∫⁻ w, H (q, w) * hullStateDensity T k o R (q, w) ∂(innerHaar o R)
end YangMills.Construction.BoxGaussian
end
