import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields Conventions
def SecondDerivExcessEnergyEqExcessHessian : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t m : ℕ) (ρ : ℝ), 2 * L ≤ m → 0 < ρ → ρ ≤ 1 →
    ∀ᶠ U in 𝓝 (trivialField m),
      ∀ (F : ℝ → (torusFrame L t m).GaugeField (torusFrame L t m).depth)
        (G : ℝ → (torusFrame L t m).GaugeField (torusFrame L t m).top)
        (A : (torusFrame L t m).Site (torusFrame L t m).depth → Fin 4 → imaginaryQuaternions)
        (v : (torusFrame L t m).Site (torusFrame L t m).top → Fin 4 → imaginaryQuaternions),
        F 0 = stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top U) →
        G 0 = readAtLevel (torusFrame L t m) (torusFrame L t m).top U →
        (∀ x μ, ContDiffAt ℝ 2 (fun r => ((F r x μ : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x μ, ContDiffAt ℝ 2 (fun r => ((G r x μ : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x μ, HasDerivAt (fun r => ((F r x μ : UnitQuaternion) : ℍ[ℝ]))
          ((A x μ : ℍ[ℝ]) * ((F 0 x μ : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x μ, HasDerivAt (fun r => ((G r x μ : UnitQuaternion) : ℍ[ℝ]))
          ((v x μ : ℍ[ℝ]) * ((G 0 x μ : UnitQuaternion) : ℍ[ℝ])) 0) →
        ContDiffAt ℝ 2 (fun r => excessEnergy a (F r) (G r)) 0 ∧
          deriv (deriv fun r => excessEnergy a (F r) (G r)) 0 =
            excessHessian a (F 0) (G 0) A v
end YangMills.Construction.RunningCouplingSlope
end
