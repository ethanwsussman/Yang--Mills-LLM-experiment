import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty
def NonemptyOfLimits (L K : ℕ) (β : ℝ) : Prop :=
  (InfiniteLattice.torusLimitSet L K β).Nonempty ∧
    ∀ ν ∈ InfiniteLattice.torusLimitSet L K β, InfiniteLattice.IsInfiniteVolumeLimit L K β ν
def NonemptyStatement : Prop :=
  (∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β → NonemptyOfLimits L K β) ∧
    ∀ ℓ : TorusLumps.StepParameters, TotalDensitySystem.IsUnitMeshStepParameters ℓ → ∀ Bs g : ℝ, 0 < Bs →
      ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β → NonemptyOfLimits ℓ.side K β
end YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty
end
