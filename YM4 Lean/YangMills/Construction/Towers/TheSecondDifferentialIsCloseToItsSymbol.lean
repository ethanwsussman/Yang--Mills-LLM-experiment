import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SecondDerivNearSymbol
open PeriodicOperators (toComplexVec wNorm dualLattice)
open TorusResponseField (blochWaveField)
open PeriodicOperators.Tempered (EventuallyForSides)
open FullSpace (fieldPeriodicData secondVariationSymbol)
def SecondDerivCloseToSymbol : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ EventuallyForSides L fun n =>
      ∀ p ∈ dualLattice (2 * L ^ n), ∀ u v : (fieldPeriodicData L k hL).UnitQuot → ℂ,
        ‖(((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ *
              complexSecondDeriv L n k
                (blochWaveField L n k hL (toComplexVec p) u)
                (blochWaveField L n k hL (-toComplexVec p) v) -
            secondVariationSymbol L k hL (toComplexVec p) u v‖ ≤
          C * Real.exp (-c * (2 * L ^ n : ℕ)) *
            wNorm ((fieldPeriodicData L k hL).quotWeight 1) u *
            wNorm ((fieldPeriodicData L k hL).quotWeight 1) v
end YangMills.Construction.Tower.SecondDerivNearSymbol
end
