import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.PeriodicLift
open Periodisation YangMills.Construction.Tower
def LiftProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n → ∀ A : CellClass k,
    (∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.periodicExtension L n A f ∈ (CellClass.fullSpace L A).complexSubmodule) ∧
    ∀ (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)
      (c : Cell L k A.level A.cellType),
      CellClass.cellFn L A (CellClass.periodicExtension L n A f) c =
        CellClass.quotCellFn L n A f (Cell.proj n c)
end YangMills.Construction.LocalKernels.PeriodicLift
end
