import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage castVec)
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl in
def MoyalRemainderBound : Prop :=
  ∀ (φ : ℝ) (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N''']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (b : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol a → IsWeylSymbol b →
    ∀ r : AmbientSpace → Matrix (Fin N') (Fin N''') ℂ,
      (∀ q, r q = moyalProduct φ a b q - a q * b q +
        (Complex.I / 2 * (φ : ℂ)) • poissonBracket a b q +
        ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) • secondPoissonBracket a b q) →
      HasAbsSummableFourier r ∧
      weightedCoeffNorm 0 r ≤ 1 / 48 * |φ| ^ 3 * weightedCoeffNorm 3 a * weightedCoeffNorm 3 b
end YangMills.Construction.Tower
end
