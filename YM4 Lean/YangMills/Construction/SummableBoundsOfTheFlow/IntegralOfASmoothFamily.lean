import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace IteratedDerivative
def IntervalIntegralSmoothFamily : Prop :=
  ∀ (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] (A : ℝ × Q → ℝ) (p₀ : Q) (n : ℕ),
    (∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n : WithTop ℕ∞) A (v, p₀)) →
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun p => ∫ v in (0 : ℝ)..1, A (v, p)) p₀ ∧
    ∀ l : List Q, l.length ≤ n →
      derivAlong (fun p => ∫ v in (0 : ℝ)..1, A (v, p)) l p₀ =
        ∫ v in (0 : ℝ)..1, derivAlong (fun p => A (v, p)) l p₀
end IteratedDerivative
end YangMills.Construction
end
