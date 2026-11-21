import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def invariantFunctionFormStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (ψ : TorusFields.TorusField n → ℝ) (ε : ℝ), 0 < ε →
    (∀ W : TorusFields.TorusField n, TorusFields.IsCold ε W →
      ∀ g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion,
        ψ (TorusFields.gaugeTransform g W) = ψ W) →
    (∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ψ (TorusFields.perturb c X σ (TorusFields.trivialField n))) 0) →
    HasQuadraticFormAtIdentity ψ
end YangMills.Construction.MomentLaw
end
