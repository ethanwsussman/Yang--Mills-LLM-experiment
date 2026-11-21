import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec)
namespace Tower.MagneticWeyl
namespace SymbolAlgebra
def AbsSummableLinear (N' N'' : ℕ) [NeZero N'] [NeZero N''] : Prop :=
  (∀ s r : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, HasAbsSummableFourier s →
    HasAbsSummableFourier r →
    HasAbsSummableFourier (fun q => s q + r q) ∧
      (∀ m, fourierCoeff (fun q => s q + r q) m = fourierCoeff s m + fourierCoeff r m) ∧
      weightedCoeffNorm 0 (fun q => s q + r q) ≤ weightedCoeffNorm 0 s + weightedCoeffNorm 0 r) ∧
  ∀ (c : ℂ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ), HasAbsSummableFourier s →
    HasAbsSummableFourier (fun q => c • s q) ∧
      (∀ m, fourierCoeff (fun q => c • s q) m = c • fourierCoeff s m) ∧
      weightedCoeffNorm 0 (fun q => c • s q) = ‖c‖ * weightedCoeffNorm 0 s
def SymbolSpace (N' N'' : ℕ) [NeZero N'] [NeZero N''] : Prop :=
  (∀ s r : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, IsWeylSymbol s → IsWeylSymbol r →
    IsWeylSymbol (fun q => s q + r q) ∧
      (∀ m, fourierCoeff (fun q => s q + r q) m = fourierCoeff s m + fourierCoeff r m) ∧
      ∀ j : ℕ, j ≤ 3 →
        weightedCoeffNorm j (fun q => s q + r q) ≤ weightedCoeffNorm j s + weightedCoeffNorm j r) ∧
  (∀ (c : ℂ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ), IsWeylSymbol s →
    IsWeylSymbol (fun q => c • s q) ∧
      (∀ m, fourierCoeff (fun q => c • s q) m = c • fourierCoeff s m) ∧
      ∀ j : ℕ, j ≤ 3 → weightedCoeffNorm j (fun q => c • s q) = ‖c‖ * weightedCoeffNorm j s) ∧
  (∀ c : Matrix (Fin N') (Fin N'') ℂ, IsWeylSymbol (fun _ : AmbientSpace => c) ∧
    fourierCoeff (fun _ : AmbientSpace => c) 0 = c ∧
    (∀ m, m ≠ 0 → fourierCoeff (fun _ : AmbientSpace => c) m = 0) ∧
    ∀ j : ℕ, j ≤ 3 →
      weightedCoeffNorm j (fun _ : AmbientSpace => c) = Matrices.RectangularMatrix.opNormValue c) ∧
  ∀ s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, IsWeylSymbol s →
    (∀ j : ℕ, j ≤ 3 → 0 ≤ weightedCoeffNorm j s) ∧
    weightedCoeffNorm 0 s ≤ weightedCoeffNorm 3 s ∧
    (∀ m, Matrices.RectangularMatrix.opNormValue (fourierCoeff s m) ≤ weightedCoeffNorm 3 s) ∧
    Continuous s ∧
    ∀ (μ : Fin 4) (q : AmbientSpace) (i : Fin N') (k : Fin N''),
      HasDerivAt (fun t : ℝ => s (Function.update q μ t) i k) (coordDeriv μ s q i k) (q μ)
def PointwiseProducts (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N'''] : Prop :=
  ∀ (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (s' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol s → IsWeylSymbol s' →
    IsWeylSymbol (fun q => s q * s' q) ∧
    (∀ j : ℕ, j ≤ 3 →
      weightedCoeffNorm j (fun q => s q * s' q) ≤ weightedCoeffNorm j s * weightedCoeffNorm j s') ∧
    HasAbsSummableFourier (poissonBracket s s') ∧
    weightedCoeffNorm 0 (poissonBracket s s') ≤ 2 * weightedCoeffNorm 3 s * weightedCoeffNorm 3 s' ∧
    HasAbsSummableFourier (secondPoissonBracket s s') ∧
    weightedCoeffNorm 0 (secondPoissonBracket s s') ≤
      4 * weightedCoeffNorm 3 s * weightedCoeffNorm 3 s'
def MoyalBilinear (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N'''] : Prop :=
  ∀ (φ : ℝ) (s r : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (s' r' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (c : ℂ),
    IsWeylSymbol s → IsWeylSymbol r → IsWeylSymbol s' → IsWeylSymbol r' →
    moyalProduct φ (fun q => s q + r q) s' =
        (fun q => moyalProduct φ s s' q + moyalProduct φ r s' q) ∧
    moyalProduct φ s (fun q => s' q + r' q) =
        (fun q => moyalProduct φ s s' q + moyalProduct φ s r' q) ∧
    moyalProduct φ (fun q => c • s q) s' = (fun q => c • moyalProduct φ s s' q) ∧
    moyalProduct φ s (fun q => c • s' q) = (fun q => c • moyalProduct φ s s' q)
end SymbolAlgebra
open SymbolAlgebra in
def SymbolAlgebra.Claim : Prop :=
  ∀ (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N'''],
    AbsSummableLinear N' N'' ∧ SymbolSpace N' N'' ∧
      PointwiseProducts N' N'' N''' ∧ MoyalBilinear N' N'' N'''
end Tower.MagneticWeyl
end YangMills.Construction
end
