import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.GibbsAtFixedSpacing
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def WeakCompactnessAndSymmetryOfStates : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ ν ν' : Measure (GaugeField a), IsLatticeState ν → IsLatticeState ν' →
      (∀ F ∈ continuousLocalFunctions a, stateEval ν F = stateEval ν' F) → ν = ν') ∧
    (∀ (ν : Measure (GaugeField a)) (N : Set (Measure (GaugeField a))), IsLatticeState ν →
      IsWeakBasicNhd ν N → IsWeakOpen N ∧ ν ∈ N) ∧
    (∀ (ν : ProbabilityMeasure (GaugeField a)) (N : Set (ProbabilityMeasure (GaugeField a))),
      N ∈ @nhds _ (probabilityMeasuresWeakTopology a) ν →
        ∃ B : Set (Measure (GaugeField a)),
          IsWeakBasicNhd (ν : Measure (GaugeField a)) B ∧ asProbabilityMeasures B ⊆ N) ∧
    (∀ (ν : ℕ → Measure (GaugeField a)) (ν₀ : Measure (GaugeField a)),
      (∀ i, 1 ≤ i → IsLatticeState (ν i)) → IsLatticeState ν₀ →
        (IsWeakClusterPoint ν ν₀ ↔
          ∃ φ : ℕ → ℕ, StrictMono φ ∧ StatesTendstoWeakly (ν ∘ φ) ν₀)) ∧
    (∀ ν : ℕ → Measure (GaugeField a), (∀ i, 1 ≤ i → IsLatticeState (ν i)) →
      ∃ ν₀, IsLatticeState ν₀ ∧ IsWeakClusterPoint ν ν₀) ∧
    IsWeakCompact {ρ : Measure (GaugeField a) | IsLatticeState ρ} ∧
    (∀ (ν : Measure (GaugeField a)) (r : LatticeSymmetry a), IsLatticeState ν →
      (IsSymmetricUnder ν r ↔
        ∀ F ∈ continuousFns a, stateEval ν (r.actOn F) = stateEval ν F)) ∧
    (∀ ν : Measure (GaugeField a), IsLatticeState ν →
      ∃ G : Subgroup (Equiv.Perm AmbientSpace), ∀ f : AmbientSpace → AmbientSpace,
        (∃ r : LatticeSymmetry a, r.toFun = f ∧ IsSymmetricUnder ν r) ↔ ∃ g ∈ G, ⇑g = f)
end YangMills.Construction.InfiniteLattice
end
