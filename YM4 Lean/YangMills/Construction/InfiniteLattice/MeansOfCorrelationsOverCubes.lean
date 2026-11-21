import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.IntegrableVersionsAndVariance
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace LatticePhases
variable {a : ℝ}
def centredCubePoints (a : ℝ) (n : ℕ+) : Set (LatticePoint a) :=
  {y | PeriodicLattice.supNormVec (y : AmbientSpace) ≤ (n : ℝ) * a}
def cubeCorrelationMean (ρ : ProbMeasure (GaugeField a)) (A : GaugeField a → ℂ) (n : ℕ+) : ℂ :=
  ((centredCubePoints a n).ncard : ℂ)⁻¹ *
    ∑ᶠ y ∈ centredCubePoints a n,
      ρ.eval fun U => conj (A U) * (shift y).actOn A U
def CorrelationMeansConverge : Prop :=
  ∀ (D : Setup) (ρ : ProbMeasure (GaugeField D.mesh)) (A : GaugeField D.mesh → ℂ),
    IsShiftInvariant ρ.toMeasure → IsBoundedObservable A →
      Tendsto (cubeCorrelationMean ρ A) atTop (𝓝 (plateauPairing ρ.toMeasure A A)) ∧
        ∀ Y : GaugeField D.mesh → ℂ, IsIntegrableCondExpRepresentative ρ.toMeasure A Y →
          (ρ.eval fun U => conj (A U) * Y U) = plateauPairing ρ.toMeasure A A
end LatticePhases
end YangMills.Construction
end
