import YangMills.Construction.Parameters.ConstructionParameters
import YangMills.Construction.Towers.TheCoefficientOfTheMassiveDeterminants
import YangMills.Construction.Towers.TheRemainderOfTheFreePolarisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.NormaliserLaw
def normaliserStiffness {L : ℕ} (hL : 0 < L) (k : ℕ) : ℝ :=
  OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (Tower.stepNormaliserFamily L k)
def deviationBound (L : ℕ) : ℝ :=
  Tower.FullSpace.BackgroundJets.FreePolarizationRemainder.remainderBound L *
      Tower.FullSpace.BackgroundJets.stripHalfWidth ^ (-2 : ℤ) +
    Tower.Massive.uvConstant
def NormaliserStiffnessLaw : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    (∀ m : ℕ,
      |∑ k ∈ Finset.range m, normaliserStiffness hL k -
          (m : ℝ) * ParameterChoice.oneLoopCoefficient L| ≤ deviationBound L) ∧
    (∀ a b : ℕ, a ≤ b →
      |∑ k ∈ Finset.Ico a b, normaliserStiffness hL k -
          ((b : ℝ) - a) * ParameterChoice.oneLoopCoefficient L| ≤
        2 * deviationBound L) ∧
    ∀ a b : ℕ, a ≤ b →
      ((b : ℝ) - a) * ParameterChoice.oneLoopCoefficient L - 2 * deviationBound L ≤
        ∑ k ∈ Finset.Ico a b, normaliserStiffness hL k
end YangMills.Construction.OneLoopLaw.NormaliserLaw
end
