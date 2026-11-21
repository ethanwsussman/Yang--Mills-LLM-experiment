import YangMills.Construction.TwoPoints.PartsOfATestPlate
import YangMills.Construction.TwoPoints.RealFunctionsOnSeparatedPairsAndTheirBilinearExtension
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
structure ReflectedUpperBound (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (r₀ : ℝ)
    (g : ℝ → ℝ) : Prop where
  radius_pos : 0 < r₀
  value_pos : ∀ r ∈ Ioc 0 r₀, 0 < g r
  tendsto_zero : Tendsto g (𝓝[>] 0) (𝓝 0)
  le_reflected : ∀ w : ℝ, 0 < w → 5 / 2 * w ≤ r₀ → ∀ f : AmbientSpace → ℂ,
    TestPlates.ReflectedPairAdmissible w f →
    S (reflectFun (coordVec 3) f) f ≤
      g (5 / 2 * w) * TestFunctions.uniformNorm f * TestFunctions.uniformNorm f
def AxisDecayGrowthFromReflectedPairs.Statement : Prop :=
  ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (r₀ : ℝ) (g : ℝ → ℝ)
    (ψ : (Fin 2 → ℝ) → ℂ) (ρ : ℝ),
    IsDisjointForm S → IsAdmissibleForm L S → ReflectedUpperBound S r₀ g →
    ψ ∈ transProfiles → ψ ≠ 0 → 0 < ρ → tsupport ψ ⊆ {ξ | euclidNorm ξ ≤ ρ} →
      (∀ w : ℝ, 0 < w → w ≤ min 1 (min ρ (2 / 5 * r₀)) →
        axisDecayTransform S ψ (7 * w) ≤
          TestPlates.growthConst * ρ ^ 4 * TestPlates.plateWidthNorm w ψ ^ 2 * w ^ (-8 : ℤ) *
            g (5 / 2 * w)) ∧
      (∀ s : ℝ, 0 < s → s ≤ 7 * min 1 (min ρ (2 / 5 * r₀)) →
        s ^ 8 * axisDecayTransform S ψ s ≤
          TestPlates.decayGrowthConst * ρ ^ 4 *
            (TestFunctions.uniformNorm ψ + gradPlaneSup ψ) ^ 2 * g (5 / 14 * s)) ∧
      Tendsto (fun s : ℝ => s ^ 8 * axisDecayTransform S ψ s) (𝓝[>] 0) (𝓝 0)
end YangMills.Construction.TwoPoints
namespace YangMills.Construction.PairFunctions
open YangMills.Construction.EuclideanFunctionals (R4)
open YangMills.Construction.TwoPoints (FixedScale IsDisjointForm IsAdmissibleForm ReflectedUpperBound
  rotateFun)
def RotationInvarianceFromReflectedBound.Statement : Prop :=
  ∀ (L : FixedScale) (T : sepPairs → ℝ), IsDisjointForm (realPartForm T) →
    IsAdmissibleForm L (realPartForm T) →
    (∃ (r₀ : ℝ) (g : ℝ → ℝ), ReflectedUpperBound (realPartForm T) r₀ g) →
    ∀ (R : Matrix.orthogonalGroup (Fin 4) ℝ) (f h : R4 → ℝ), [f, h] ∈ sepPairs →
      evalPair T (rotateFun R f) (rotateFun R h) = evalPair T f h
end YangMills.Construction.PairFunctions
end
