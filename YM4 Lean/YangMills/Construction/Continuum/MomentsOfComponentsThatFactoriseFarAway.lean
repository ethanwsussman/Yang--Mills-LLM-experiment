import YangMills.Construction.Continuum.CanonicalDecompositionOfAFamilyOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ClusterMoments
open YangMills.Construction.TestSpaces YangMills.Construction.TupleLists
open YangMills.Construction.CanonicalDecomposition
open YangMills.Construction.SeparatedTuples (atInfinity push)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def ClusterFactorises {Ξ : Type*} (σ : Ξ → SepTuple → ℝ) : Prop :=
  ∀ Y Z : SeparatedTuples.SepTuple, ∃ b : AmbientSpace → ℝ, Tendsto b atInfinity (𝓝 0) ∧
    ∀ᶠ v in atInfinity, ∀ ξ,
      |σ ξ (ofList (SeparatedTuples.SepTuple.juxt Y (push (SeparatedTuples.translate v) Z))) -
        σ ξ (ofList Y) * σ ξ (ofList Z)| ≤ b v
def IteratedLimitIsMoment : Prop :=
  ∀ (Ξ : Type) [TopologicalSpace Ξ] [CompactSpace Ξ] [TopologicalSpace.MetrizableSpace Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (σ : Ξ → SepTuple → ℝ) (s : SepTuple → ℝ),
    (∀ X, Continuous fun ξ => σ ξ X) → (∀ ξ, WightmanReconstruction.IsPermutationInvariant (σ ξ)) →
    (∀ X, s X = ∫ ξ, σ ξ X ∂μ) → ClusterFactorises σ →
    ∀ (X : SepTuple) (Y : List SepTuple), IteratedLimitsExist X Y s ∧
      ∫ ξ, σ ξ X * (Y.map fun Z => σ ξ Z).prod ∂μ = iterLimit X Y s
end YangMills.Construction.ClusterMoments
end
