import YangMills.Construction.ChessboardTori.DominatedMatricesOverTheExpansionIndex
import YangMills.Construction.ChessboardTori.TraceFormula
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SquareSummable
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace TransferSetup
variable {S : ChessboardSetup} (T : TransferSetup S)
def gramPower (m : ℕ) (Φ : T.SlabConfig → ℂ) : T.WordMatrix :=
  T.matrixPower (T.wordMul (T.slabKernelMatrix Φ) (adjointKernel (T.slabKernelMatrix Φ))) (m / 2)
end TransferSetup
def TraceFormulaConsequences.Statement : Prop :=
  ∀ (S : ChessboardSetup) (T : TransferSetup S) (m : SlabCount) (hm : Even (m : ℕ)),
    (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      T.alternatingSlabIntegral m hm Φ = alternatingCyclicTrace (T.slabKernelMatrix Φ) (m : ℕ) ∧
      alternatingCyclicTrace (T.slabKernelMatrix Φ) (m : ℕ) =
        ((schattenEvenNorm (T.slabKernelMatrix Φ) (m : ℕ) ^ (m : ℕ) : ℝ) : ℂ) ∧
      0 ≤ T.alternatingSlabIntegral m hm Φ ∧
      T.alternatingSlabIntegral m hm (T.reflectConj Φ) = T.alternatingSlabIntegral m hm Φ) ∧
    (∀ Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ, (∀ k, T.IsBoundedMeasurable (Φ k)) →
      ‖T.slabProductIntegral m Φ‖ ≤
        ∏ k : ZMod (m : ℕ), schattenEvenNorm (T.slabKernelMatrix (Φ k)) (m : ℕ) ∧
      ∏ k : ZMod (m : ℕ), schattenEvenNorm (T.slabKernelMatrix (Φ k)) (m : ℕ) =
        ∏ k : ZMod (m : ℕ), (T.alternatingSlabIntegral m hm (Φ k)).re ^ (1 / ((m : ℕ) : ℝ))) ∧
    ∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ → ∀ (j : ℕ) (hj : 1 ≤ j),
      T.IsDominated (T.gramPower (m : ℕ) Φ) ∧
      0 ≤ T.alternatingSlabIntegral (SlabCount.scale j hj m)
        (SlabCount.even_scale j hj hm) Φ ∧
      T.alternatingSlabIntegral (SlabCount.scale j hj m) (SlabCount.even_scale j hj hm) Φ =
        T.diagonalTrace (T.matrixPower (T.gramPower (m : ℕ) Φ) j) ∧
      T.diagonalTrace (T.matrixPower (T.gramPower (m : ℕ) Φ) j) ≤
        T.diagonalTrace (T.gramPower (m : ℕ) Φ) ^ j ∧
      T.diagonalTrace (T.gramPower (m : ℕ) Φ) ^ j =
        T.alternatingSlabIntegral m hm Φ ^ j
end YangMills.Construction.ChessboardTori
end
