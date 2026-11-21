import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels
def LiftIsGaugeField : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ U : Tower.Edge L n k j → Matrices.ComplexMatrix2,
      (PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U →
        Tower.FullSpace.IsFieldIn PeriodicLattice.compactGaugeGroup
          (liftGaugeField L n k j U)) ∧
      (PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U →
        Tower.FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup
          (liftGaugeField L n k j U))
end YangMills.Construction.LocalKernels
end
