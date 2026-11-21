import YangMills.Construction.InfiniteLattice.CountableDenseFamilyOfLocalFunctions
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.PeriodicGibbsStateSpace.DenseLocalFamily
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicGibbsStateSpace.DenseToBorel
variable {a : ℝ}
def boundedRealBorel (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | IsBoundedObservable F ∧ IsRealValued F}
def IsRealSubspace (ℳ : Set (GaugeField a → ℂ)) : Prop :=
  ∃ W : Submodule ℝ (GaugeField a → ℂ), (W : Set (GaugeField a → ℂ)) = ℳ
def IsClosedUnderBoundedPointwiseLimits (ℳ : Set (GaugeField a → ℂ)) : Prop :=
  ∀ (F : ℕ → GaugeField a → ℂ) (G : GaugeField a → ℂ), (∀ k, F k ∈ ℳ) →
    (∃ c : ℝ, ∀ k U, ‖F k U‖ ≤ c) → (∀ U, Tendsto (fun k => F k U) atTop (𝓝 (G U))) → G ∈ ℳ
def meanAbs (ν : BorelProb a) (A : GaugeField a → ℂ) : ℝ :=
  (ν.integral fun U => ((‖A U‖ : ℝ) : ℂ)).re
def DenseFamilyDeterminesBorel : Prop :=
  ∀ (D : Params) (𝒟 : Set (GaugeField D.mesh → ℂ)), IsCountableRealDense 𝒟 →
    (∀ ℳ : Set (GaugeField D.mesh → ℂ), ℳ ⊆ boundedRealBorel D.mesh → 𝒟 ⊆ ℳ →
      IsRealSubspace ℳ → IsClosedUnderBoundedPointwiseLimits ℳ →
        ℳ = boundedRealBorel D.mesh) ∧
    ∀ (ν : BorelProb D.mesh) (h : GaugeField D.mesh → ℂ), IsBoundedObservable h → ∀ ε : ℝ, 0 < ε →
      ∃ H ∈ complexSpan 𝒟, meanAbs ν (fun U => h U - H U) ≤ ε
end YangMills.Construction.PeriodicGibbsStateSpace.DenseToBorel
