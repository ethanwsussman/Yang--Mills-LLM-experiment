import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def weightContractionStatement : Prop :=
  ForAllPoints fun Λ C _ _ S =>
    0 ≤ C 0 ∧ C 0 * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2⁻¹ ^ 10 * (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ∧
    (∀ (u n : ℕ) [NeZero n], IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8)
      (S.distanceWeight u (n * Λ.stepParams.side)) (S.distanceWeight (u + 1) n)) ∧
    (∀ (n : ℕ) [NeZero n] (A : Finset (TorusFields.TorusSite (n * Λ.stepParams.side))) (A' : Finset (TorusFields.TorusSite n)),
      A.Nonempty → (∀ z ∈ A, TorusLumps.parentBlock Λ.stepParams.side z ∈ A') →
      IsSlowlyVaryingPair (n := n) Λ.stepParams.side (Λ.stepParams.weightRate / 8)
        (fun p => Real.exp (-(Λ.stepParams.weightRate / 8 * (finsetDist A p.1 : ℝ))))
        (fun p => Real.exp (-(Λ.stepParams.weightRate / 8 * (finsetDist A' p.1 : ℝ))))) ∧
    (∀ (e n m : ℕ) [NeZero n] [NeZero m] (b : TorusFields.TorusSite m), n = m * Λ.stepParams.side ^ e →
      IsSlowlyVaryingPair (n := n) Λ.stepParams.side (Λ.stepParams.weightRate / 8)
        (fun p => Real.exp (Λ.stepParams.weightRate / 8 * (TorusFields.supDist (ancestor Λ.stepParams.side (e + 1) m p.1) b : ℝ)))
        (fun p => Real.exp (Λ.stepParams.weightRate / 8 * (TorusFields.supDist (ancestor Λ.stepParams.side e m p.1) b : ℝ)))) ∧
    (∀ (n : ℕ) [NeZero n], IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8)
      (fun _ : TorusFields.TorusPlaquette (n * Λ.stepParams.side) => 1) (fun _ : TorusFields.TorusPlaquette n => 1)) ∧
    ∀ (d n : ℕ) [NeZero n], 64 ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal),
      1 ≤ q → Measurable X →
      weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (WeightedResponses.fineSide Λ.stepParams.side d n)) q
          (fun e => descend Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X e)) ≤
        ENNReal.ofReal ((C 0 * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ)) ^ d) *
          weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) q X
end YangMills.Construction.MomentLaw
end
