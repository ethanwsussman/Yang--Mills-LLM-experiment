import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def gaussianChainFluctuationsStatement : Prop :=
  ForAllPoints fun Λ _ c _ S =>
    (∀ u j d : ℕ, u + 1 + j + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (u + 1 + j + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (u + 1 + j + d) (S.data.period Λ.stepParams.side)) μ →
      (∀ᵐ X ∂μ, IsTreeGauge (u + 1 + j + d) (S.data.period Λ.stepParams.side) X) →
      (∀ᵐ X ∂μ, ∀ (e : Fin 3), ∀ b ∉ StepCosts.chartBonds Λ.stepParams.side
          (WeightedResponses.fineSide Λ.stepParams.side j
            (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))),
        stepDefect Λ.stepParams.coupling Λ.table.ρA u _
          (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d (S.data.period Λ.stepParams.side) X)) e b = 0) ∧
      (∀ co : Fin 3 → ChartBondIndex Λ.stepParams.side u
          (WeightedResponses.fineSide Λ.stepParams.side j
            (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) → ℝ,
        μ.map (fun X => ∑ e : Fin 3, ∑ b, co e b * chartValues (u := u)
            (stepDefect Λ.stepParams.coupling Λ.table.ρA u _
              (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d (S.data.period Λ.stepParams.side) X))) e b) =
          gaussianReal 0 (∑ e : Fin 3, co e ⬝ᵥ
            ((WeightedResponses.trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
              (WeightedResponses.fineSide Λ.stepParams.side j
                (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))))⁻¹.mulVec
              (co e))).toNNReal) ∧
      IndepFun (fun X => stepDefect Λ.stepParams.coupling Λ.table.ρA u _
          (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d (S.data.period Λ.stepParams.side) X)))
        (fun X (e : Fin 3)
            (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          WeightedResponses.curl
            (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) d (S.data.period Λ.stepParams.side) X) e) p) μ) ∧
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ b b' : ChartBondIndex Λ.stepParams.side u n,
      |(WeightedResponses.trivialHessian Λ.stepParams.coupling Λ.stepParams.side u n)⁻¹ b b'| ≤
        2 / Λ.table.lam * Real.exp (-(2 * c * (TorusFields.supDist
          (TorusLumps.toTorusSite (n * Λ.stepParams.side) b.1.1)
          (TorusLumps.toTorusSite (n * Λ.stepParams.side) b'.1.1) : ℝ)))
end YangMills.Construction.MomentLaw
end
