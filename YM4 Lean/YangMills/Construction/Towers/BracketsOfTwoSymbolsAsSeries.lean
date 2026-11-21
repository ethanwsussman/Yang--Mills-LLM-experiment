import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
namespace Tower
open MagneticWeyl in
def SymbolBracketSeries : Prop :=
  ∀ (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N''']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol a → IsWeylSymbol a' →
    HasFourierExpansion
      (fun n => ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        fourierCoeff a p.1.1 * fourierCoeff a' p.1.2) (fun q => a q * a' q) ∧
    HasFourierExpansion
      (fun n => ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        (-(symplecticForm p.1.1 p.1.2 : ℂ)) • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2))
      (poissonBracket a a') ∧
    HasFourierExpansion
      (fun n => ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        ((symplecticForm p.1.1 p.1.2 : ℂ) ^ 2) • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2))
      (secondPoissonBracket a a')
end Tower
end YangMills.Construction
end
