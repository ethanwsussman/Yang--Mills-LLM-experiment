import YangMills.Construction.Coordinates.ConstancyOnConnectedOpenSets
import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.CubicAgreement
open YangMills.Construction.Coordinates.ConstancyOnConnected (IsHolomorphicScalarIn)
open YangMills.Construction.OneLoopLaw.TemperedStiffness (secondPartialAtZero)
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
def SecondPartialExists (g : (Fin 4 → ℂ) → ℂ) (μ ν : Fin 4) : Prop :=
  (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t : ℝ =>
    g (toComplexVec (Pi.single μ s + Pi.single ν t))) 0) ∧
  DifferentiableAt ℝ (fun s : ℝ => deriv (fun t : ℝ =>
    g (toComplexVec (Pi.single μ s + Pi.single ν t))) 0) 0
def SecondPartialsAgree : Prop :=
  ∀ (U : Set (Fin 4 → ℂ)) (f g : (Fin 4 → ℂ) → ℂ), IsOpen U → 0 ∈ U →
    IsHolomorphicScalarIn U f → IsHolomorphicScalarIn U g →
    (fun p : AmbientSpace => f (toComplexVec p) - g (toComplexVec p)) =O[𝓝 0]
      (fun p : AmbientSpace => euclidNormVec p ^ 3) →
    ∀ μ ν : Fin 4, SecondPartialExists f μ ν ∧ SecondPartialExists g μ ν ∧
      secondPartialAtZero f μ ν = secondPartialAtZero g μ ν
end YangMills.Construction.OneLoopLaw.CubicAgreement
end
