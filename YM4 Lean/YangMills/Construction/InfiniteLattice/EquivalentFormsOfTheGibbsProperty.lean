import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.InfiniteLattice.WilsonSpecificationOnObservablesVersionsAndTrivialMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open GibbsAtFixedSpacing
namespace InfiniteLattice.GibbsEquivalences
variable {a : ℝ}
def positivePart (L : Finset (Link a)) : Set (Link a) :=
  {b | b ∈ positiveLinkSet a ∧ (b ∈ L ∨ ∃ c ∈ L, b = c.opposite)}
def specKernel (ha : 0 < a) (β : ℝ) (L : Finset (Link a))
    (hL : (L : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ) :
    GaugeField a → ℂ :=
  wilsonLinkKernel β L (hasNoOppositePairs_of_subset_positiveLinks ha hL) F
def glueOnLinks (ha : 0 < a) (L : Finset (Link a))
    (hL : (L : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a)
    (V : L → Matrices.ComplexMatrix2.specialUnitary) : GaugeField a :=
  overwriteLinks (hasNoOppositePairs_of_subset_positiveLinks ha hL)
    (fun b => V ⟨b, Finset.mem_coe.1 b.2⟩) U
def specImage (ha : 0 < a) (β : ℝ) (L : Finset (Link a))
    (hL : (L : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    Measure (GaugeField a) :=
  (wilsonSpecificationAt ha β L (complementValues L U)).map (glueOnLinks ha L hL U)
def KernelOrientationInvariant (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ (L' : Finset (Link a)) (h : HasNoOppositePairs (L' : Set (Link a))),
    ∃ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a),
      (L : Set (Link a)) = positivePart L' ∧
      plaquettesTouching L' = plaquettesTouching L ∧
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        wilsonLinkKernel β L' h F = specKernel ha β L hL F
def KernelBasicProps (ha : 0 < a) (β : ℝ) (L : Finset (Link a))
    (hL : (L : Set (Link a)) ⊆ positiveLinkSet a) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    IsBoundedObservable (specKernel ha β L hL F) ∧
      Measurable[complementSigma L] (specKernel ha β L hL F) ∧
      observableSupNorm (specKernel ha β L hL F) ≤ observableSupNorm F) ∧
  (∀ U : GaugeField a,
    IsProbabilityMeasure (specImage ha β L hL U) ∧
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        specKernel ha β L hL F U = ∫ U', F U' ∂specImage ha β L hL U ∧
        specKernel ha β L hL F U =
          ∫ V, F (glueOnLinks ha L hL U V)
            ∂wilsonSpecificationAt ha β L (complementValues L U)) ∧
  (∀ F H : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable H →
    Measurable[complementSigma L] H →
      specKernel ha β L hL (fun U => H U * F U) =
        fun U => H U * specKernel ha β L hL F U) ∧
  ∀ F ∈ continuousLocalFunctions a,
    specKernel ha β L hL F ∈ continuousLocalFunctions a
def DLRRectangles (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a)
    (B₁ : Set (LinkVariables (L : Set (Link a)))) (B₂ : Set (ComplementVariables L)),
    MeasurableSet[borel (LinkVariables (L : Set (Link a)))] B₁ →
    MeasurableSet[borel (ComplementVariables L)] B₂ →
      ((ν.real {U | restrictField U (L : Set (Link a)) ∈ B₁ ∧ complementValues L U ∈ B₂} : ℝ) : ℂ) =
        ∫ U, observableOfComplement L (setIndicator B₂) U *
          specKernel ha β L hL (observableOfLinks L (setIndicator B₁)) U ∂ν
def KernelCondExpInner (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) :
    Prop :=
  ∀ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a),
    ∀ φ ∈ boundedBorelSpace (LinkVariables (L : Set (Link a))),
      IsCondExpRepresentative ν (complementSigma L) (observableOfLinks L φ)
        (specKernel ha β L hL (observableOfLinks L φ))
def KernelCondExp (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a)
    (F : GaugeField a → ℂ), IsBoundedObservable F →
    IsCondExpRepresentative ν (complementSigma L) F (specKernel ha β L hL F)
def KernelInvariant (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a),
    ∀ F ∈ continuousLocalFunctions a,
      ∫ U, specKernel ha β L hL F U ∂ν = ∫ U, F U ∂ν
def GibbsEquivalenceStatement : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β →
    KernelOrientationInvariant ha β ∧
    (∀ (L : Finset (Link a)) (hL : (L : Set (Link a)) ⊆ positiveLinkSet a),
      KernelBasicProps ha β L hL) ∧
    (∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
      List.TFAE [DLRRectangles ha β ν, KernelCondExpInner ha β ν,
        KernelCondExp ha β ν, KernelInvariant ha β ν] ∧
      (IsGibbs β ν ↔
        DLRRectangles ha β ν ∧ KernelCondExpInner ha β ν ∧
          KernelCondExp ha β ν ∧ KernelInvariant ha β ν)) ∧
    ∀ ν₁ ν₂ : Measure (GaugeField a), IsPeriodicGibbs β ν₁ → IsPeriodicGibbs β ν₂ →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        IsPeriodicGibbs β (ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂)
end InfiniteLattice.GibbsEquivalences
end YangMills.Construction
