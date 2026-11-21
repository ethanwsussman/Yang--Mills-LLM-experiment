import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
open scoped Topology
namespace YangMills.Construction.LaplaceAsymptotics
variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
def familyHessian (Q : (Fin k → ℝ) × BondField ι → ℝ) (τ : Fin k → ℝ) :
    Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun i j => secondDerivAlong (fun η => Q (τ, η)) 0 (bondVariation i.1 (EuclideanSpace.single i.2 1))
    (bondVariation j.1 (EuclideanSpace.single j.2 1))
structure IsAdmissibleExponentFamily (ρ lam K : ℝ) (Q B : (Fin k → ℝ) × BondField ι → ℝ) : Prop where
  contDiff_Q : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 5 Q (0, η)
  contDiff_B : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 B (0, η)
  value_zero : ∀ τ : Fin k → ℝ, Q (τ, 0) = 0
  critical_zero : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), fderiv ℝ (fun η => Q (τ, η)) 0 = 0
  hessian_lower : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ∀ u : BondField ι,
    lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (fun ζ => Q (0, ζ)) η u u
  deriv_bound_Q : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ∀ j : ℕ, 2 ≤ j → j ≤ 5 →
    ‖iteratedFDeriv ℝ j Q (0, η)‖ ≤ K
  deriv_bound_B : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
    ‖iteratedFDeriv ℝ j B (0, η)‖ ≤ K
def logCutoffIntegral (ρ : ℝ) (p : ℝ → ℝ) (x : ℝ) (Q B : (Fin k → ℝ) × BondField ι → ℝ)
    (τ : Fin k → ℝ) : ℝ :=
  Real.log (∫ η, radialWeightProd (cutoffFactor ρ p) η * Real.exp (-(x * Q (τ, η) + B (τ, η))))
def haarGapSubLog (s : ℝ) : ℝ := haarGap s - 3 / 2 * Real.log s
def gaussianLogValue (Q B : (Fin k → ℝ) × BondField ι → ℝ) (τ : Fin k → ℝ) : ℝ :=
  -B (τ, 0) - 1 / 2 * Real.log (familyHessian Q τ).det
end YangMills.Construction.LaplaceAsymptotics
end
