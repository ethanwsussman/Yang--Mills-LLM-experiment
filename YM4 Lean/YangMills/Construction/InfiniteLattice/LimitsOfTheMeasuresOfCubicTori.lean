import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.TestFunctions
def cubicTorusLimitStates (L K : ℕ) (β : ℝ) :
    Set (BorelProb (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | ∃ (m : ℕ → ℕ) (ρ : ℕ → BorelProb (PeriodicLattice.meshSize L (K : ℤ))), (∀ i, 0 < m i) ∧
    Tendsto (fun i => PeriodicLattice.torusSide L (m i)) atTop atTop ∧
    (∀ i, (ρ i).1 = liftedWilsonMeasure L (m i) K β) ∧ BorelProb.TendstoWeak ρ ν}
def IsSeparatedLipschitzTuple {n : ℕ} (ℓ : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  2 ≤ n ∧ (∀ i, IsLipschitzFor euclidDistR4 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
    (∀ i k, i ≠ k → Disjoint (tsupport (f i)) (tsupport (f k))) ∧
    ∃ A : Set (Fin 4 → ℝ), HasDiameterLE A (ℓ / 2) ∧ ∀ i, tsupport (f i) ⊆ A
end InfiniteLattice
end YangMills.Construction
