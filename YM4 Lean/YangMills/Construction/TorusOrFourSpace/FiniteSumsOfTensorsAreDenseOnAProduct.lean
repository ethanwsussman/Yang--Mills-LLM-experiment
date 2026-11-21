import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def TensorSpanDenseOnBoxes : Prop :=
  ∀ (P : Params) (K : Kind) (k : ℕ+) (R d : ℝ) (U : Fin (k : ℕ) → Set (K.Pt P)),
    AdmissibleWith P K R d U → (∀ i, (U i).Nonempty) →
      Tuple.DenseInTestFns (tensorSpan P K U)
end YangMills.Construction.PeriodicSpace.Kind
