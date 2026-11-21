import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.Periodisation
def PeriodisationHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    (∀ j ≤ k, ProjCellsClassified L n k j ∧ ProjEdgesCompatible L n k j) ∧
    (∀ I : WeightedIndexSet k, QuotientClassesPeriodic L n I) ∧
    DescendsAlgebra (k := k) L n ∧
    LocalKernelFacts (k := k) L ∧
    LinearMapHasMatrix (k := k) L n ∧
    PairBracketTranspose (k := k) L ∧
    BilinearDescends (k := k) L n ∧
    (∀ (j : ℕ) (h : j ≤ k), HessianDataDescend L n k j h) ∧
    (1 ≤ k → MeansDescend L n k)
end YangMills.Construction.LocalKernels.Periodisation
end
