import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open Matrices Tower Tower.FullSpace
def nearIdentityFields (L k j : ℕ) (δ : ℝ) : Set (Edge L k j → ComplexMatrix2) :=
  {V | V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
    ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < δ}
def nextMeanIterate {L k j : ℕ} (V : Edge L k j → ComplexMatrix2) :
    Edge L k (j + 1) → ComplexMatrix2 :=
  open Classical in fun c =>
    if c.IsPositivelyOriented then normalizedMean V c else (normalizedMean V c.opposite)⁻¹
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
