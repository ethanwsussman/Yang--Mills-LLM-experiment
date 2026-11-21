import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open CyclicFormula
def gaussianQuadraticCumulantStatement : Prop :=
  ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℝ), G.PosSemidef → ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ∀ Q : Fin n → Matrix (Fin N) (Fin N) ℝ, (∀ i, (Q i).IsSymm) →
    jointCumulant (multivariateGaussian 0 G)
        (fun i x => (1 / 2) * ((fun a => x a) ⬝ᵥ (Q i).mulVec fun a => x a)) =
      (if n = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders n, Matrix.trace (List.ofFn fun c : Fin n => Q (σ c) * G).prod ∧
    jointCumulant (Measure.pi fun _ : Fin 3 => multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) G)
        (fun i X => ∑ e : Fin 3, (1 / 2) * ((fun a => X e a) ⬝ᵥ (Q i).mulVec fun a => X e a)) =
      3 * ((if n = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders n, Matrix.trace (List.ofFn fun c : Fin n => Q (σ c) * G).prod)
end YangMills.Construction.MomentLaw
end
