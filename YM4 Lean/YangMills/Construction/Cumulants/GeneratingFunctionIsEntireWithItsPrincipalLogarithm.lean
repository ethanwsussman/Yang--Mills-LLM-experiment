import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.GeneratingLog
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def nearOneSet (ν : Measure Ω) (X : Fin n → Ω → ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | ‖momentGeneratingFunction ν X z - 1‖ < 1}
def logOfGenerating (ν : Measure Ω) (X : Fin n → Ω → ℝ) : Coordinates.ComplexCoordinates n → ℂ :=
  TorusBoundNotation.principalLog ∘ momentGeneratingFunction ν X
structure EntireWithLog (ν : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  integrable : ∀ z : Coordinates.ComplexCoordinates n,
    Integrable (fun ω => Complex.exp (∑ i, z i * (X i ω : ℂ))) ν
  entire : ComplexVariables.IsEntireFun (momentGeneratingFunction ν X)
  value_at_zero : momentGeneratingFunction ν X 0 = 1
  isOpen : IsOpen (nearOneSet ν X)
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈ nearOneSet ν X
  holomorphic : ComplexVariables.IsHolomorphicScalar (nearOneSet ν X) (logOfGenerating ν X)
  exp_eq : ∀ z ∈ nearOneSet ν X, Complex.exp (logOfGenerating ν X z) = momentGeneratingFunction ν X z
  log_at_zero : logOfGenerating ν X 0 = 0
  formed : TorusBoundNotation.MixedDerivFormed (nearOneSet ν X) (logOfGenerating ν X)
  cumulant_eq : mixedCumulant ν X = TorusBoundNotation.mixedDeriv (logOfGenerating ν X) 0
def EntireAndLogCumulant : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (X : Fin n → Ω → ℝ), 1 ≤ n → (∀ i, Probability.IsBoundedRealRV (X i)) →
    EntireWithLog ν X ∧ ∀ i, X i = 0 → mixedCumulant ν X = 0
end YangMills.Construction.Cumulants.GeneratingLog
