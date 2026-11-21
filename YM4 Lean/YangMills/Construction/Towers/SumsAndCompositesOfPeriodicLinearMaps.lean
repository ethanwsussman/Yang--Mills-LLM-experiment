import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.PeriodicOperatorAlgebra
open OneStepChart
structure Rules (s : ℕ) : Prop where
  id : ∀ X : TwoScaleFunctions, CellCoordinates s X → PeriodicOperator X X (fun f => f) (fun f => f)
  zero : ∀ X Y : TwoScaleFunctions, CellCoordinates s X → CellCoordinates s Y →
    PeriodicOperator X Y (fun _ => 0) (fun _ => 0)
  comp : ∀ X Y Z : TwoScaleFunctions, CellCoordinates s X → CellCoordinates s Y → CellCoordinates s Z →
    ∀ (A : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
      (A' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index → Matrices.ComplexMatrix2)
      (B : (Y.fullSpace.index → Matrices.ComplexMatrix2) → Z.fullSpace.index → Matrices.ComplexMatrix2)
      (B' : (Y.torusSpace.index → Matrices.ComplexMatrix2) → Z.torusSpace.index → Matrices.ComplexMatrix2),
      PeriodicOperator X Y A A' → PeriodicOperator Y Z B B' →
        PeriodicOperator X Z (fun f => B (A f)) (fun f => B' (A' f))
  add : ∀ X Y : TwoScaleFunctions, CellCoordinates s X → CellCoordinates s Y →
    ∀ (A B : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
      (A' B' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index → Matrices.ComplexMatrix2),
      PeriodicOperator X Y A A' → PeriodicOperator X Y B B' →
        PeriodicOperator X Y (fun f => A f + B f) (fun f => A' f + B' f)
  sub : ∀ X Y : TwoScaleFunctions, CellCoordinates s X → CellCoordinates s Y →
    ∀ (A B : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
      (A' B' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index → Matrices.ComplexMatrix2),
      PeriodicOperator X Y A A' → PeriodicOperator X Y B B' →
        PeriodicOperator X Y (fun f => A f - B f) (fun f => A' f - B' f)
  congr : ∀ X Y : TwoScaleFunctions, CellCoordinates s X → CellCoordinates s Y →
    ∀ (A B : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
      (A' B' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index → Matrices.ComplexMatrix2),
      PeriodicOperator X Y A A' → (∀ f ∈ X.fullSpace.complexSubmodule, B f = A f) →
        (∀ f ∈ X.torusSpace.complexSubmodule, B' f = A' f) → PeriodicOperator X Y B B'
def Statement : Prop := ∀ s : ℕ, 0 < s → Rules s
end YangMills.Construction.Tower.UnitScale.PeriodicOperatorAlgebra
end
