import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StepImageOfFourierModes
def ImageExpansion : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ i : ℕ,
    PeriodicOperators.Tempered.EventuallyForSides L fun n =>
    ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ (a : Fin 3) (μ : Fin 4),
      PeriodicOperators.Tempered.OneStep.complexStepPushforward hL n i
          (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
        (L : ℂ)⁻¹ • ∑ r ∈ PeriodicOperators.Tempered.OneStep.residueBox L, ∑ ρ,
          PeriodicOperators.Tempered.OneStep.stepEntry L i r (PeriodicOperators.toComplexVec p) ρ μ •
            PeriodicOperators.Tempered.fourierModeForm L (n + 1) a
              (PeriodicOperators.Tempered.OneStep.rescaledMomentum L p r) ρ
end YangMills.Construction.Tower.StepImageOfFourierModes
end
