import YangMills.Construction.ReflectionPositivity.FrameOfFunctionalsOnSeparatedTuplesDefs
import Mathlib
set_option autoImplicit false
open Filter Topology
namespace YangMills.Construction.TestNormComparison
open SeparatedTupleFunctionals TestFunctions
open InfiniteLattice (AmbientSpace)
def NormBounds (M : ℝ) : Prop :=
  ∀ f ∈ c1CompactSupp ℝ,
    c1NormR4 f ≤ sharpNormR4 M f ∧ sharpNormR4 M f ≤ 80 * M * c1NormR4 f
def TendstoZeroIff (M : ℝ) : Prop :=
  ∀ (r₀ : ℕ) (s : ℕ → AmbientSpace → ℝ) (f : AmbientSpace → ℝ), 1 ≤ r₀ →
    (∀ r, r₀ ≤ r → s r ∈ c1CompactSupp ℝ) → f ∈ c1CompactSupp ℝ →
    (Tendsto (fun r => c1NormR4 (s r - f)) atTop (𝓝 0) ↔
      Tendsto (fun r => sharpNormR4 M (s r - f)) atTop (𝓝 0))
def NormsEquivalent : Prop := ∀ M : ℝ, 1 ≤ M → NormBounds M ∧ TendstoZeroIff M
end YangMills.Construction.TestNormComparison
