import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import YangMills.Construction.InfiniteLattice.MeasuresOfATorusOfAnyShapeWithAndWithoutAnArray
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
namespace SingleGeneratorArray
variable {a : ℝ}
def linkEndpoints (S : Finset (Link a)) : Set (LatticePoint a) :=
  {x | ∃ b ∈ S, x = b.initial ∨ x = b.terminal}
structure WindowFitsInQuotient (A : SingleGeneratorArray a) (ha : 0 < a) (Γ : PeriodSublattice a)
    (W S : Finset (Link a)) : Prop where
  edges_subset : ∀ p ∈ plaquettesTouching W, edgesOf p ⊆ (S : Set (Link a))
  linkSupport_subset : ∀ v ∈ A.supportIndices ha W, linkSupport ha (A.translate v) ⊆ (S : Set (Link a))
  linfNorm_lt_minPeriodNorm : ∀ x ∈ linkEndpoints S, ∀ y ∈ linkEndpoints S,
    linfNorm ((x : AmbientSpace) - (y : AmbientSpace)) < minPeriodNorm Γ
end SingleGeneratorArray
open SingleGeneratorArray in
def EquilibriumInEmbeddableWindow.Statement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ (A : SingleGeneratorArray a) (t : ℝ)
    (Γ : PeriodSublattice a) (hΓ : A.PeriodsWithin Γ) (W S : Finset (Link a)) (hWS : W ⊆ S)
    (hS : (S : Set (Link a)) ⊆ positiveLinkSet a),
    A.WindowFitsInQuotient ha Γ W S →
      ∀ F : GaugeField a → ℂ, (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
        Measurable[linkSigma (S : Set (Link a))] F →
          ∫ U, A.tiltedKernel ha β t W
              (hasNoOppositePairs_of_subset_positiveLinks ha
                ((Finset.coe_subset.2 hWS).trans hS)) F U ∂A.liftedTiltMeasure hΓ β t =
            ∫ U, F U ∂A.liftedTiltMeasure hΓ β t
end GibbsAtFixedSpacing
end YangMills.Construction
