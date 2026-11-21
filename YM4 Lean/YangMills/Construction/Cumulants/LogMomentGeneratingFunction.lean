import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedComplexExpectation
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace Cumulants
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def tupleMomentGeneratingFunction (ν : Measure Ω) (x : Fin n → Ω → ℝ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => YangMills.Construction.Probability.complexExpectation ν
    (YangMills.Construction.ComplexVariables.expComp fun ω => ∑ i, z i * (x i ω : ℂ))
theorem tupleMomentGeneratingFunction_eq_momentGeneratingFunction (ν : Measure Ω)
    (x : Fin n → Ω → ℝ) :
    tupleMomentGeneratingFunction ν x = momentGeneratingFunction ν x :=
  rfl
def logDomain (ν : Measure Ω) (x : Fin n → Ω → ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | ‖tupleMomentGeneratingFunction ν x z - 1‖ < 1}
def logMomentGeneratingFunction (ν : Measure Ω) (x : Fin n → Ω → ℝ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => YangMills.Construction.ComplexVariables.logPrincipal
    (tupleMomentGeneratingFunction ν x z)
def shiftTuple (x : Fin n → Ω → ℝ) (c : Fin n → ℝ) : Fin n → Ω → ℝ :=
  fun i ω => x i ω + c i
def realComplexPairing (c : Fin n → ℝ) (z : Coordinates.ComplexCoordinates n) : ℂ :=
  ∑ i, (c i : ℂ) * z i
def restrictTuple (x : Fin n → Ω → ℝ) (J : Finset (Fin n)) : Fin J.card → Ω → ℝ :=
  fun a => x (J.orderEmbOfFin rfl a)
open Classical in
def finsetMoment (ν : Measure Ω) (x : Fin n → Ω → ℝ) (J : Finset (Fin n)) : ℂ :=
  if J = ∅ then 1 else
    YangMills.Construction.Probability.complexExpectation ν fun ω => ((∏ l ∈ J, x l ω : ℝ) : ℂ)
def finsetCumulant (ν : Measure Ω) (x : Fin n → Ω → ℝ) (J : Finset (Fin n)) : ℂ :=
  mixedCumulant ν (restrictTuple x J)
end Cumulants
end YangMills.Construction
