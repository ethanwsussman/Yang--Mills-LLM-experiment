import YangMills.Construction.ClusterExpansion.MultiplicitiesAndPrincipalLog
import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedComplexExpectation
import Mathlib
set_option autoImplicit false

section
open MeasureTheory
noncomputable section
namespace YangMills.Construction.RandomTuple
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def laplaceTransform (μ : Measure Ω) (X : Fin n → Ω → ℝ) : YangMills.Construction.Coordinates.ComplexCoordinates n → ℂ :=
  fun z => YangMills.Construction.Probability.complexExpectation μ
    (YangMills.Construction.ComplexVariables.expComp fun ω => ∑ i, z i * (X i ω : ℂ))
def jointCumulant (μ : Measure Ω) (X : Fin n → Ω → ℝ) : ℂ :=
  YangMills.Construction.Cumulants.mixedCumulant μ X
def translate (X : Fin n → Ω → ℝ) (c : Fin n → ℝ) : Fin n → Ω → ℝ := fun i ω => X i ω + c i
def restrictTo (X : Fin n → Ω → ℝ) (B : Finset (Fin n)) : Fin B.card → Ω → ℝ :=
  fun a => X (B.orderEmbOfFin rfl a)
end YangMills.Construction.RandomTuple
end
end

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RandomTuple
variable {n : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]
def logRegion (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | ‖RandomTuple.laplaceTransform ν Y z - 1‖ < 1}
def logLaplace (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Coordinates.ComplexCoordinates n → ℂ :=
  fun z => PrincipalLog.principalBranch (RandomTuple.laplaceTransform ν Y z)
end YangMills.Construction.RandomTuple
