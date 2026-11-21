import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABound
import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
def SubsequentialLimitsAlongParameterSequence : Prop :=
  ForAllTrajectoryCouplings fun T y D g =>
    (∀ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, β j ∈ D.passageWindow (K j) g) →
      Tendsto K atTop atTop → Tendsto m atTop atTop →
      ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n, ∃ s : ℂ,
        Tendsto (fun j => PeriodicLattice.torusUrsellFunction T.side (m (φ j)) (K (φ j)) (β (φ j))
          (fun i => TestFunctions.periodize (PeriodicLattice.torusSide T.side (m (φ j))) (X.1 i)))
          atTop (𝓝 s)) ∧
    (∀ (m : ℕ+) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, β j ∈ D.passageWindow (K j) g) →
      Tendsto K atTop atTop →
      ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧ ∀ n, 2 ≤ n →
        ∀ X : Fin n → PeriodicLattice.FourTorus T.side m → ℝ,
        (∀ i, TestFunctions.IsC1Torus (X i)) →
        (∃ d : ℝ, 0 < d ∧ TestFunctions.HasSeparatedSupportsTorus X d) → ∃ s : ℂ,
        Tendsto (fun j => PeriodicLattice.torusUrsellFunction T.side m (K (φ j)) (β (φ j)) X)
          atTop (𝓝 s))
end YangMills.Construction.SystemOfAdmissibleConstants
end
