import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open GibbsAtFixedSpacing
def IsTorusWeakClusterPoint (L K : ℕ) (β : ℝ)
    (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∀ 𝒰 ∈ 𝓝 ν, ∀ ℓ₀ ∈ PeriodicLattice.torusSides L, ∃ m : ℕ, 0 < m ∧
    ℓ₀ ≤ PeriodicLattice.torusSide L m ∧
    ∃ ρ ∈ 𝒰, (ρ : GaugeFieldProbability _).1 = liftedWilsonMeasure L m K β
def torusWeakClusterPoints (L K : ℕ) (β : ℝ) :
    Set (BorelProb (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | IsTorusWeakClusterPoint L K β ν}
def TendstoInfinityThroughSides (L : ℕ) (ℓ : ℕ → ℝ) : Prop :=
  (∀ i, ℓ i ∈ PeriodicLattice.torusSides L) ∧ Tendsto ℓ atTop atTop
end YangMills.Construction.InfiniteLattice
