import YangMills.Construction.Continuum.CanonicalDecompositionOfAFunctional
import YangMills.Construction.InfiniteLattice.CutoffGibbsSets
import YangMills.Construction.SystemsWithFiveBounds.GrowthOfALimitAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.StatesOfTheWindowForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.SeparatedTuples (TupleFunctional SepTuple DecompositionData)
open YangMills.Construction.WindowLimits (clusteringRadiusOf)
open YangMills.Construction.LimitTheorem
open YangMills.Construction.InfiniteLattice (IsInfiniteVolumeLimit cutoffExtremalSet)
open YangMills.Construction.TorusMetric (euclidNormVec)
structure CanonicalDecompositionConditions : Prop where
  growth_bound : ∀ {F : StatedSideFamily} {N : BoundConstants}, BoundsHoldAt F N →
    ∀ (Q : WindowStates F) {σ : TupleFunctional}, Q.HasLimit σ →
      YangMills.Construction.TestSpaces.GrowthBound (growthOrder N)
        (1 + 2 * YangMills.Construction.SeparatedBound.extFactorAbs)
        (growthConst F.M N (unitBallBound F.M N)) (20 + N.factorialExponent) (evalOnMap σ)
  cluster_law : ∀ {F : StatedSideFamily} {N : BoundConstants}, BoundsHoldAt F N →
    ∀ (Q : WindowStates F) {σ : TupleFunctional}, Q.HasLimit σ →
      (∀ k, Q.ρ k ∈ cutoffExtremalSet F.L (Q.K k) (Q.β k)) →
      ∀ (X Y : SepTuple) (v : Fin 4 → ℝ), clusteringRadiusOf X Y ≤ euclidNormVec v →
        SepTuple.Composable X (YangMills.Construction.SeparatedTuples.push (YangMills.Construction.SeparatedTuples.translate v) Y) ∧
          |σ (SepTuple.juxt X (YangMills.Construction.SeparatedTuples.push (YangMills.Construction.SeparatedTuples.translate v) Y)) - σ X * σ Y| ≤
            clusteringConstOf F.M N X Y * (euclidNormVec v ^ 2)⁻¹
  exists_canonical_decomposition : ∀ {F : StatedSideFamily} {N : BoundConstants}, BoundsHoldAt F N →
    ∀ {Q : WindowStates F} {S : CumulantFamily}, Q.ρ = Q.ν →
      (∀ k, IsInfiniteVolumeLimit F.L (Q.K k) (Q.β k) (Q.ν k)) → Q.HasLimit (centredOf S) →
      ∃ D : DecompositionData, D.IsCanonical (centredOf S) ∧
        ∀ ξ, ∃ Q' : WindowStates F, Q'.HasLimit (D.comp ξ) ∧
          ∀ k, Q'.ρ k ∈ cutoffExtremalSet F.L (Q'.K k) (Q'.β k)
  exists_states_of_component : ∀ {F : StatedSideFamily} {N : BoundConstants}, BoundsHoldAt F N →
    ∀ {Q : WindowStates F} {S : CumulantFamily}, Q.ρ = Q.ν →
      (∀ k, IsInfiniteVolumeLimit F.L (Q.K k) (Q.β k) (Q.ν k)) → Q.HasLimit (centredOf S) →
      ∀ {D : DecompositionData}, D.IsCanonical (centredOf S) → ∀ ξ : D.space,
        ∃ Q' : WindowStates F, Q'.HasLimit (D.comp ξ) ∧
          ∀ k, Q'.ρ k ∈ cutoffExtremalSet F.L (Q'.K k) (Q'.β k)
def CanonicalDecompositionOfLimits : Prop := CanonicalDecompositionConditions
end YangMills.Construction.SystemsWithFiveBounds
end
