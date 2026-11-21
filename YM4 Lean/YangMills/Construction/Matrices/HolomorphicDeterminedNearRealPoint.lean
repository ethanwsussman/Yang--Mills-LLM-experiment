import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
def tracelessPoint {σ : Type} (B : σ → ComplexMatrix2) : Empty ⊕ σ → ComplexMatrix2 :=
  Sum.elim Empty.elim B
end YangMills.Construction.Matrices.GroupLieProduct
end
