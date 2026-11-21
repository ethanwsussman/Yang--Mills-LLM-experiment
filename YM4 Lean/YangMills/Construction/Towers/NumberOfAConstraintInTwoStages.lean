import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import YangMills.Construction.Towers.TwoStagesOfAConstraintDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConstraintStages
def GaussianNumberOfComposite : Prop :=
  ∀ (E F F' : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
    (P : E →ₗ[ℝ] F) (Q : F →ₗ[ℝ] F') (T : QuadraticForm ℝ (LinearMap.ker (Q ∘ₗ P))),
    Function.Surjective P → Function.Surjective Q → T.PosDef →
    ∃ S : QuadraticForm ℝ (LinearMap.ker Q), S.PosDef ∧
      IsFiberwiseMinimum P Q T S ∧
      GaussianConstraint.constrainedGaussianNumber (Q ∘ₗ P) T =
        GaussianConstraint.constrainedGaussianNumber P (restrictToInnerKernel P Q T) *
          GaussianConstraint.constrainedGaussianNumber Q S
end YangMills.Construction.ConstraintStages
end
