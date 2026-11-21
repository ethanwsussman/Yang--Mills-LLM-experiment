import YangMills.Construction.PeriodicOperators.LogarithmOfTheDeterminantOfLinearMaps
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RealLogDet
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (scalarSecondDeriv IsHolomorphicScalarIn)
open YangMills.Construction.PeriodicOperators.LogDetOfMaps (detRatio logDetRatio)
variable {C : Type} {N : ℕ}
def realEmbed (v : Fin N → ℝ) : Coordinates.ComplexCoordinates N := fun j => (v j : ℂ)
def realLogAbsDetDiff (M : Coordinates.ComplexCoordinates N → Module.End ℂ (C → ℂ))
    (v : Fin N → ℝ) : ℝ :=
  Real.log ‖LinearMap.det (M (realEmbed v))‖ - Real.log ‖LinearMap.det (M 0)‖
def Claim : Prop :=
  ∀ (C : Type) [Finite C] (N : ℕ) (W : Set (Coordinates.ComplexCoordinates N))
    (M : Coordinates.ComplexCoordinates N → Module.End ℂ (C → ℂ)),
    IsOpen W → 0 ∈ W → IsUnit (M 0) → (∀ z ∈ W, ‖detRatio M z - 1‖ < 1) →
    IsHolomorphicScalarIn W (logDetRatio M) →
    (∀ᶠ v : Fin N → ℝ in 𝓝 0, ∀ c' c, (linearMapEntry (M (realEmbed v)) c' c).im = 0) →
    (∀ᶠ v : Fin N → ℝ in 𝓝 0, LinearMap.det (M (realEmbed v)) ≠ 0) ∧
    (∀ᶠ v : Fin N → ℝ in 𝓝 0, DifferentiableAt ℝ (realLogAbsDetDiff M) v) ∧
    DifferentiableAt ℝ (fderiv ℝ (realLogAbsDetDiff M)) (0 : Fin N → ℝ) ∧
    ∀ z z' : Coordinates.ComplexCoordinates N,
      ((fderiv ℝ (fderiv ℝ (realLogAbsDetDiff M)) 0 (fun j => (z j).re) (fun j => (z' j).re) -
          fderiv ℝ (fderiv ℝ (realLogAbsDetDiff M)) 0 (fun j => (z j).im) (fun j => (z' j).im) :
            ℝ) : ℂ) +
        Complex.I *
          ((fderiv ℝ (fderiv ℝ (realLogAbsDetDiff M)) 0 (fun j => (z j).re) (fun j => (z' j).im) +
            fderiv ℝ (fderiv ℝ (realLogAbsDetDiff M)) 0 (fun j => (z j).im) (fun j => (z' j).re) :
              ℝ) : ℂ) =
      scalarSecondDeriv (logDetRatio M) 0 z z'
end YangMills.Construction.PeriodicOperators.RealLogDet
end
