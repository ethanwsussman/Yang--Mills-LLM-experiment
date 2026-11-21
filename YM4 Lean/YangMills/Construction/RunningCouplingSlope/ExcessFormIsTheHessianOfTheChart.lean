import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Conventions TorusFields ReferenceDensity
namespace RunningCouplingSlope
def ExcessHessianEqChartHessian : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t m : ℕ) (ρ : ℝ), 2 * L ≤ m → 0 < ρ → ρ ≤ 1 →
    ∀ᶠ V₀ in 𝓝 (trivialField m),
      ∃ M : Matrix (ChartCoord (torusFrame L t m)) (TopCoord (torusFrame L t m)) ℝ,
        ∀ (A : (torusFrame L t m).Site (torusFrame L t m).depth → Fin 4 → imaginaryQuaternions)
          (v : (torusFrame L t m).Site (torusFrame L t m).top → Fin 4 → imaginaryQuaternions)
          (x : ChartCoord (torusFrame L t m) → ℝ)
          (γ : (torusFrame L t m).Site (torusFrame L t m).depth → imaginaryQuaternions),
          (∀ z : (torusFrame L t m).Cell, γ (cellCentre (torusFrame L t m).depth z) = 0) →
          (∀ i : ChartCoord (torusFrame L t m), imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
            chartTangentCoords a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) x i +
              imaginaryComponents (covariantDifference
                (stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀)) γ i.1.1) i.2 +
              Matrix.mulVec M (topCoords v) i) →
          (∀ (i : TreeCoord (torusFrame L t m)), imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
            imaginaryComponents (covariantDifference
              (stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀)) γ i.1.1) i.2) →
          excessHessian a (stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀))
              (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) A v =
            dotProduct x (Matrix.mulVec
              (chartedHessian a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) 0) x)
end RunningCouplingSlope
end YangMills.Construction
end
