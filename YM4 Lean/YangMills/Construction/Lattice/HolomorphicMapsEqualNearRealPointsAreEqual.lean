import YangMills.Construction.Lattice.ContinuationsFromRealData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def RealIdentityPrinciple.Statement : Prop :=
  ∀ (ι τ : Type) [Fintype ι] [Fintype τ] (r : ℝ)
    (f g : (ι → Matrices.ComplexMatrix2) → τ → Matrices.ComplexMatrix2)
    (S : Set (ι → Matrices.ComplexMatrix2)),
    IsHolomorphicMatrixValued (Matrices.GroupLieProduct.supBall ι r) f →
    IsHolomorphicMatrixValued (Matrices.GroupLieProduct.supBall ι r) g →
    S ⊆ Matrices.GroupLieProduct.supBall ι r ∩ selfAdjointFunctions ι → S.Nonempty →
    Matrices.ComplexMatrix2.IsRelativelyOpen (selfAdjointFunctions ι) S → Set.EqOn f g S →
    Set.EqOn f g (Matrices.GroupLieProduct.supBall ι r)
end YangMills.Construction.PeriodicLattice
