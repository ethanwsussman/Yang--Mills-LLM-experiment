import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
open Kind.Tuple
def FourierTruncationsConverge : Prop :=
  ∀ (D : Params) (p : ℕ+) (P : ℝ), 0 < P →
    ∀ θ ∈ cellTestFns D p P, ∀ F ∈ cellTestFns D p P,
    ∀ G : ℕ+ → Kind.euclidean.Tuple D p → ℂ,
      (∀ t, G t ∘ proj D Kind.euclidean = fourierPartialSum D P F t) →
      (∀ t, IsSmoothT D Kind.euclidean (G t)) ∧
      ∀ k : ℕ, Tendsto (fun t => cNorm D Kind.euclidean k (θ * (G t - F))) atTop (𝓝 0)
end YangMills.Construction.PeriodicSpace.PeriodCell
