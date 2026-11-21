import YangMills.Construction.SystemOfAdmissibleConstants.ConditionsFromTheInequality
import YangMills.Construction.SystemOfAdmissibleConstants.ConditionsOnTheAdmissibleConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
def CumulantConditionsOfInequality : Prop :=
  ∀ (L : ℕ) (IsAdmissible : ℕ+ → ℝ → Prop) (A v M : ℝ),
    YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    (∀ K β, IsAdmissible K β → 0 < β) → 1 ≤ A → 1 ≤ v → 1 ≤ M →
    YangMills.Construction.SeparatedMoments.CopyInequalityOnRelation L IsAdmissible A v →
      (∀ K β, IsAdmissible K β → YangMills.Construction.AdmissibleConstants.TorusClusterBound L M K β A v) ∧
      (∀ K β, IsAdmissible K β → YangMills.Construction.AdmissibleConstants.BallClusterBoundOnTori L M K β A v) ∧
      (∀ K β, IsAdmissible K β → YangMills.Construction.AdmissibleConstants.BallClusterBoundInStates L M K β A v)
end YangMills.Construction.AdmissibleConstants
end
