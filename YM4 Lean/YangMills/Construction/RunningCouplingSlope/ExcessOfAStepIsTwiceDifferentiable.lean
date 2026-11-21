import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields Conventions
def ExcessEnergyIsContDiffTwo : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t m : ℕ) (ρ : ℝ), 2 * L ≤ m → 0 < ρ → ρ ≤ 1 →
    ∀ᶠ U in 𝓝 (trivialField m),
      ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (y₀ : Y)
        (F : Y → (torusFrame L t m).GaugeField (torusFrame L t m).depth)
        (G : Y → (torusFrame L t m).GaugeField (torusFrame L t m).top),
        F y₀ = stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top U) →
        G y₀ = readAtLevel (torusFrame L t m) (torusFrame L t m).top U →
        (∀ x μ, ContDiffAt ℝ 2 (fun y => ((F y x μ : UnitQuaternion) : ℍ[ℝ])) y₀) →
        (∀ x μ, ContDiffAt ℝ 2 (fun y => ((G y x μ : UnitQuaternion) : ℍ[ℝ])) y₀) →
        ContDiffAt ℝ 2 (fun y => excessEnergy a (F y) (G y)) y₀
end YangMills.Construction.RunningCouplingSlope
end
