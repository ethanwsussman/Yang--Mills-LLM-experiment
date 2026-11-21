import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
variable {a : ℝ}
def BorelProb.basicWeakSet (ν : BorelProb a) {q : ℕ} (H : Fin q → C(GaugeField a, ℂ)) (ε : ℝ) :
    Set (BorelProb a) :=
  {ν' | ∀ r, ‖ν'.integral (H r) - ν.integral (H r)‖ < ε}
def WeakTopologyAndSeqCompactness : Prop :=
  ∀ (s : Conventions.StandingParameters) (a : ℝ), a = PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) →
    (∀ ν : BorelProb a,
      (∀ U ∈ 𝓝 ν, ∃ q : ℕ, 1 ≤ q ∧ ∃ H : Fin q → C(GaugeField a, ℂ), ∃ ε : ℝ, 0 < ε ∧
        ν.basicWeakSet H ε ⊆ U) ∧
      (∀ q : ℕ, 1 ≤ q → ∀ H : Fin q → C(GaugeField a, ℂ), ∀ ε : ℝ, 0 < ε →
        IsOpen (ν.basicWeakSet H ε) ∧ ν ∈ ν.basicWeakSet H ε)) ∧
    (∀ (ρ : ℕ → BorelProb a) (ν : BorelProb a),
      BorelProb.TendstoWeak ρ ν ↔ ∀ U ∈ 𝓝 ν, ∀ᶠ i in atTop, ρ i ∈ U) ∧
    (∀ ρ : ℕ → BorelProb a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, 1 ≤ φ k) ∧
      ∃ ν : BorelProb a, BorelProb.TendstoWeak (ρ ∘ φ) ν)
end GibbsAtFixedSpacing
end YangMills.Construction
end
