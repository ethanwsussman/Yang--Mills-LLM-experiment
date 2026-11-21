import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def TendstoLatticeSumOfTorusSums : Prop :=
  ∀ (s : ℕ → ℕ) (M θ : ℝ) (f : (n : ℕ) → TorusFields.TorusBond (s n) → ℝ)
    (g : TorusLumps.LatticeBond → ℝ) (F : ℕ → ℝ),
    Filter.Tendsto s Filter.atTop Filter.atTop → 0 < θ →
    (∀ᶠ n in Filter.atTop, ∀ b : TorusFields.TorusBond (s n),
      |f n b| ≤ M * Real.exp (-(θ * TorusFields.supDist b.1 0))) →
    (∀ b : TorusLumps.LatticeBond,
      Filter.Tendsto (fun n => f n (TorusLumps.bondFrom 0 b)) Filter.atTop (𝓝 (g b))) →
    (∀ᶠ n in Filter.atTop, ∀ [NeZero (s n)], F n = ∑ b : TorusFields.TorusBond (s n), f n b) →
    Summable g ∧ Filter.Tendsto F Filter.atTop (𝓝 (∑' b, g b))
end YangMills.Construction.RunningCouplingSlope
end
