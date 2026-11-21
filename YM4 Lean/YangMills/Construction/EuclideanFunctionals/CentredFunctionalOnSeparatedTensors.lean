import YangMills.Construction.EuclideanFunctionals.TensorsAndTensorComponentsOfTheFreeSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def HasSoleTensorComp (q : ℕ) (A : TestSpaces.PointTuple q → ℂ) (F : FreeSep) : Prop :=
  tensorComp q F = A ∧ ∀ q', q' ≠ q → tensorComp q' F = 0
def centeredOnTensor (S : ConnFamily) (q : ℕ) (A : TestSpaces.PointTuple q → ℂ) : ℂ :=
  centeredFnFree S (Classical.epsilon (HasSoleTensorComp q A))
end YangMills.Construction.EuclideanFunctionals
