import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Averaging
def identityFamily (n : ℕ) : Fin n → Matrices.ComplexMatrix2 := fun _ => 1
def IdentityFamilyMeanIsOne : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Matrices.ComplexMatrix2.familyDiameter (identityFamily n) = 0 ∧
    (∀ H : Set Matrices.ComplexMatrix2,
      (H = PeriodicLattice.compactGaugeGroup ∨ H = PeriodicLattice.complexGaugeGroup) →
      (∀ W, Matrices.ComplexMatrix2.IsLogMean H (identityFamily n) W ↔ W = 1) ∧
      Matrices.ComplexMatrix2.HasUniqueLogMean H (identityFamily n) ∧
      Matrices.ComplexMatrix2.logMean H (identityFamily n) = 1) ∧
    PeriodicLattice.complexLogMean (identityFamily n) = 1
end Averaging
end YangMills.Construction
end
