import YangMills.Construction.ReflectionPositivity.AutocorrelationSmearedAutocorrelationAndRate
import YangMills.Construction.ReflectionPositivity.SpectralDensityConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TransverseCounting
open scoped Real
open Autocorrelation (correlationDecayRate)
open EnergyMomentum (orthLattice supNormCoord)
open SmearingFilter (absCoeffSum spectralDensityConst)
def TransverseSumBound : Prop :=
  ∀ (μ : Fin 4) (r : ℕ+) (ρ : ℝ), 0 ≤ ρ →
    (0 < correlationDecayRate r ∧ correlationDecayRate r < 1 / 4) ∧
    ∀ κ : orthLattice μ → ℂ,
      (∀ w : orthLattice μ, supNormCoord (fun l => (w.1 l : ℝ)) < 2 * (r : ℝ) →
        ‖κ w‖ ≤ absCoeffSum * ρ) →
      (∀ w : orthLattice μ, 2 * (r : ℝ) ≤ supNormCoord (fun l => (w.1 l : ℝ)) →
        ‖κ w‖ ≤ 8 * Real.exp (-(correlationDecayRate r *
          (supNormCoord (fun l => (w.1 l : ℝ)) - 2 * (r : ℝ)))) * ρ) →
      Summable (fun w : orthLattice μ => ‖κ w‖) ∧
        ∑' w : orthLattice μ, ‖κ w‖ ≤
          (2 * π) ^ 3 * spectralDensityConst * (r : ℝ) ^ 3 * ρ
end YangMills.Construction.ReflectionPositivity.TransverseCounting
