import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDetOfMaps
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (seriesLog scalarSecondDeriv IsHolomorphicScalarIn)
variable {ι : Type} {d : ℕ}
def detRatio (A : ComplexCoordinates d → Module.End ℂ (ι → ℂ))
    (z : ComplexCoordinates d) : ℂ :=
  LinearMap.det (Ring.inverse (A 0) * A z)
def logDetRatio (A : ComplexCoordinates d → Module.End ℂ (ι → ℂ)) (z : ComplexCoordinates d) : ℂ :=
  seriesLog (detRatio A z)
def Claim : Prop :=
  ∀ (ι : Type) [Finite ι] (d : ℕ) (U : Set (ComplexCoordinates d))
    (A : ComplexCoordinates d → Module.End ℂ (ι → ℂ)) (B₁ : ComplexCoordinates d → Module.End ℂ (ι → ℂ))
    (B₂ : ComplexCoordinates d → ComplexCoordinates d → Module.End ℂ (ι → ℂ)),
    IsOpen U → 0 ∈ U → (∀ i' i, IsHolomorphicScalarIn U fun z => linearMapEntry (A z) i' i) →
    IsUnit (A 0) → IsLinearMap ℂ B₁ → (∀ h, IsLinearMap ℂ fun k => B₂ k h) →
    (∀ k, IsLinearMap ℂ (B₂ k)) → (∀ k h, B₂ k h = B₂ h k) →
    (∀ i' i, (fun z => linearMapEntry (A z) i' i -
        (linearMapEntry (A 0) i' i + linearMapEntry (B₁ z) i' i + (1 / 2 : ℂ) * linearMapEntry (B₂ z z) i' i))
      =O[𝓝 0] fun z : ComplexCoordinates d => ‖z‖ ^ 3) →
    (∃ V : Set (ComplexCoordinates d), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V, ‖detRatio A z - 1‖ < 1) ∧
      IsHolomorphicScalarIn V (logDetRatio A)) ∧
    ∀ k h : ComplexCoordinates d,
      scalarSecondDeriv (logDetRatio A) 0 k h =
        LinearMap.trace ℂ (ι → ℂ) (Ring.inverse (A 0) * B₂ k h) -
          LinearMap.trace ℂ (ι → ℂ)
            (Ring.inverse (A 0) * B₁ k * Ring.inverse (A 0) * B₁ h)
end YangMills.Construction.PeriodicOperators.LogDetOfMaps
end
