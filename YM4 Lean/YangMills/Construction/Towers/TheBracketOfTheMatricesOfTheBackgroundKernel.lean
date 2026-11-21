import YangMills.Construction.Towers.TheFactorsOfTheBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SixMatrixBracket
open LocalKernels LocalKernels.Periodisation
def BracketIsBackgroundBilinear : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ Tower.smallIterateFields L n k, ∀ J ∈ Tower.complexEdgeForms L n k 0,
      ∀ μ ∈ Tower.complexEdgeForms L n k k, ∀ B ∈ Tower.complexEdgeForms L n k 0,
        ∀ B' ∈ Tower.complexEdgeForms L n k 0,
          quotBracket L n (edgesAtZero k).colourPairs (CellClass.quotCoeffsOn L n (edgesAtZero k) B)
              (PeriodicOperators.applyKernel (quotFactors L n k U J μ).assembled
                (CellClass.quotCoeffsOn L n (edgesAtZero k) B')) =
            Tower.backgroundBilinear U J μ B B'
end YangMills.Construction.Tower.SixMatrixBracket
end
