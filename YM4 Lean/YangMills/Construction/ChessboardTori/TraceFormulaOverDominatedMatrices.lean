import YangMills.Construction.ChessboardTori.DominatedMatricesOverTheExpansionIndex
import YangMills.Construction.ChessboardTori.TraceFormula
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
open SquareSummable
def DominatedTraceFormula.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D),
    (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      T.IsDominated (T.slabKernelMatrix Φ) ∧
      T.dominationNorm (T.slabKernelMatrix Φ) ≤ ⨆ η, ‖Φ η‖ ∧
      adjointKernel (T.slabKernelMatrix Φ) = T.slabKernelMatrix (T.reflectConj Φ)) ∧
    ∀ (m : SlabCount) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ),
      (∀ k, T.IsBoundedMeasurable (Φ k)) →
      CyclicTraceConverges (T.slabKernels m Φ) ∧
      T.slabProductIntegral m Φ = cyclicTrace (T.slabKernels m Φ)
end YangMills.Construction.ChessboardTori
end
