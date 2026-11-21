import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def compactTestFunctions : Set (AmbientSpace → ℝ) := {f | IsBoundedBorelCompactlySupported f}
def ursellFunction (ν : Measure (GaugeField a)) (n : ℕ) (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  Cumulants.mixedCumulant ν fun i U => smearedEnergy (f i) U
def centeredMoment (ν : Measure (GaugeField a)) {q : ℕ} (h : Fin q → AmbientSpace → ℝ) : ℂ :=
  Probability.complexExpectation ν fun U =>
    ∏ l, (((smearedEnergy (h l) U : ℝ) : ℂ) -
      Probability.complexExpectation ν fun V => ((smearedEnergy (h l) V : ℝ) : ℂ))
def ursellPartitionSum (ν : Measure (GaugeField a)) {q : ℕ} (h : Fin q → AmbientSpace → ℝ) : ℂ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts,
    ursellFunction ν J.card (Cumulants.restrictTuple h J)
end InfiniteLattice
end YangMills.Construction
end
