import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace Cumulants
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def IsBoundedComplexObservable (Y : Ω → ℂ) : Prop := Measurable Y ∧ ∃ C : ℝ, ∀ ω, ‖Y ω‖ ≤ C
def complexMomentGeneratingFunction (ν : Measure Ω) (Y : Fin n → Ω → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∫ ω, Complex.exp (∑ i, z i * Y i ω) ∂ν
def HasComplexCumulant (ν : Measure Ω) (Y : Fin n → Ω → ℂ) : Prop :=
  (∃ O : Set (Coordinates.ComplexCoordinates n), 0 ∈ O ∧
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O
      fun z _ => complexMomentGeneratingFunction ν Y z) ∧
  complexMomentGeneratingFunction ν Y 0 = 1
def complexJointCumulant (ν : Measure Ω) (Y : Fin n → Ω → ℂ) : ℂ :=
  iteratedFDeriv ℂ n (fun z => Complex.log (complexMomentGeneratingFunction ν Y z)) 0
    fun i => Pi.single i 1
end Cumulants
end YangMills.Construction
