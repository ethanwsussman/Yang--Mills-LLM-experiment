import YangMills.Construction.RunningCouplingSlope.FamiliesOfExponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LaplaceAsymptotics
open ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def rimWeightedDensity (ρ : ℝ) (p : ℝ → ℝ) (x : ℝ) (Q B : (Fin 2 → ℝ) × BondField ι → ℝ)
    (η : BondField ι) : ℝ :=
  radialWeightProd (cutoffFactor ρ p) η * Real.exp (-(x * Q (0, η) + B (0, η)))
def densityMean (f g : BondField ι → ℝ) : ℝ := (∫ η, g η * f η) / ∫ η, f η
def linearExponent (x : ℝ) (Q B : (Fin 2 → ℝ) × BondField ι → ℝ) :
    (Fin 2 → ℝ) × BondField ι → ℝ := fun z => x * Q z + B z
def parameterSlope (A : (Fin 2 → ℝ) × BondField ι → ℝ) (l : Fin 2) (η : BondField ι) : ℝ :=
  fderiv ℝ A (0, η) (Pi.single l 1, 0)
def parameterMixedDeriv (A : (Fin 2 → ℝ) × BondField ι → ℝ) (η : BondField ι) : ℝ :=
  iteratedFDeriv ℝ 2 A (0, η) fun l => (Pi.single l 1, 0)
def logCutoffIntegralSecondDeriv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x : ℝ) (p : ℝ → ℝ)
    (Q B : (Fin 2 → ℝ) × BondField ι → ℝ), 0 < ρ → IsCutoff ρ p →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 Q (0, η)) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 B (0, η)) →
    iteratedFDeriv ℝ 2 (logCutoffIntegral ρ p x Q B) 0 (fun l => Pi.single l 1) =
      densityMean (rimWeightedDensity ρ p x Q B) (fun η =>
          -parameterMixedDeriv (linearExponent x Q B) η +
            parameterSlope (linearExponent x Q B) 0 η *
              parameterSlope (linearExponent x Q B) 1 η) -
        densityMean (rimWeightedDensity ρ p x Q B) (parameterSlope (linearExponent x Q B) 0) *
          densityMean (rimWeightedDensity ρ p x Q B) (parameterSlope (linearExponent x Q B) 1)
end YangMills.Construction.LaplaceAsymptotics
end
