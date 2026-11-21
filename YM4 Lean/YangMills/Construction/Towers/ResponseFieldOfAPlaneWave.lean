import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseOfFourierMode
open PeriodicOperators (toComplexVec dualLattice)
open PeriodicOperators.Tempered (EventuallyForSides fourierModeForm)
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    EventuallyForSides L fun n => ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a : Fin 3) (μ : Fin 4),
      Tower.TorusResponseField.complexResponse L n k (fourierModeForm L n a p μ) =
        Tower.TorusResponseField.blochWaveField L n k hL (toComplexVec p)
          (Tower.FullSpace.responseSymbol L k hL (toComplexVec p)
            (Tower.FullSpace.axisPauliElement μ a))
end YangMills.Construction.Tower.ResponseOfFourierMode
end
