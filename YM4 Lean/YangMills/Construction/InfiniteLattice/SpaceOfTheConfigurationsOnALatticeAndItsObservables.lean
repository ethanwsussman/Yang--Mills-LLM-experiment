import YangMills.Construction.InfiniteLattice.CopiesOfTheGroupAndBoundedConvergence
import YangMills.Construction.InfiniteLattice.LinksAndTheReplacementOfAConfigurationOnAFiniteSet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set
open GibbsAtFixedSpacing
namespace InfiniteLattice.ConfigurationSpace
def HomeomorphPositiveLinks (a : ℝ) : Prop :=
  IsHomeomorph (fun U : GaugeField a => restrictField U (positiveLinkSet a)) ∧
    (CompactSpace (LinkVariables (positiveLinkSet a)) ∧
      TopologicalSpace.MetrizableSpace (LinkVariables (positiveLinkSet a))) ∧
    CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a)
def BorelEqLinkSigma (a : ℝ) : Prop :=
  borel (GaugeField a) = linkSigma (univ : Set (Link a)) ∧
    borel (GaugeField a) = linkSigma (positiveLinkSet a)
def FaceEnergyAndBoltzmannWeight (a : ℝ) : Prop :=
  (∀ p : ElementaryPlaquette a,
    Continuous (fun U : GaugeField a => faceEnergy U p) ∧
    (∀ U : GaugeField a, faceEnergy U p ∈ Icc (0 : ℝ) 2) ∧
    IsRegionMeasurable (Subtype.val '' p.cornerSet)
      (fun U : GaugeField a => (faceEnergy U p : ℂ))) ∧
  ∀ L : Finset (Link a), HasNoOppositePairs (L : Set (Link a)) →
    ∀ β : ℝ, 0 < β →
      (plaquettesTouching L).Finite ∧
      IsRealLocalContinuous (fun U : GaugeField a => Real.exp (-wilsonLinkEnergy β L U)) ∧
      ∀ U : GaugeField a, Real.exp (-wilsonLinkEnergy β L U) ∈ Ioc (0 : ℝ) 1
def MeasurableOnLinksCharacterization (a : ℝ) : Prop :=
  (∀ M : Set (Link a), M ⊆ positiveLinkSet a →
    ∀ H : GaugeField a → ℂ, IsBoundedObservable H →
      List.TFAE [
        Measurable[linkSigma M] H,
        ∀ U U' : GaugeField a, restrictField U M = restrictField U' M → H U = H U',
        ∃ g ∈ boundedBorelSpace (LinkVariables M),
          ∀ U : GaugeField a, H U = g (restrictField U M)] ∧
      (∀ g ∈ boundedBorelSpace (LinkVariables M), ∀ g' ∈ boundedBorelSpace (LinkVariables M),
        (∀ U : GaugeField a, H U = g (restrictField U M)) →
        (∀ U : GaugeField a, H U = g' (restrictField U M)) → g = g') ∧
      ∀ g ∈ boundedBorelSpace (LinkVariables M),
        (∀ U : GaugeField a, H U = g (restrictField U M)) → Continuous H → Continuous g) ∧
  ∀ L : Finset (Link a), (L : Set (Link a)) ⊆ positiveLinkSet a →
    ∀ H : GaugeField a → ℂ, IsBoundedObservable H →
      (Measurable[complementSigma L] H ↔
        ∃ g ∈ boundedBorelSpace (ComplementVariables L),
          ∀ U : GaugeField a, H U = g (complementValues L U))
def OverwriteLinksProperties (a : ℝ) : Prop :=
  (∀ (L : Finset (Link a)) (hL : HasNoOppositePairs (L : Set (Link a))),
    (∀ (V : LinkVariables (L : Set (Link a))) (U : GaugeField a),
      (∀ b : (L : Set (Link a)), overwriteLinks hL V U b = V b) ∧
      (∀ b : (L : Set (Link a)), overwriteLinks hL V U (b : Link a).opposite = (V b)⁻¹) ∧
      ∀ e : Link a, e ∉ (L : Set (Link a)) → e.opposite ∉ (L : Set (Link a)) →
        overwriteLinks hL V U e = U e) ∧
    Continuous (fun x : LinkVariables (L : Set (Link a)) × GaugeField a =>
      overwriteLinks hL x.1 x.2)) ∧
  ∀ (L : Finset (Link a)) (hL : HasNoOppositePairs (L : Set (Link a))),
    (L : Set (Link a)) ⊆ positiveLinkSet a →
    ∀ (V : LinkVariables (L : Set (Link a))) (U U' : GaugeField a),
      complementValues L U = complementValues L U' → overwriteLinks hL V U = overwriteLinks hL V U'
def LinkSigmaAndLocality (a : ℝ) : Prop :=
  (∀ S : Set AmbientSpace,
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      linkSigma (positiveLinksWithin a S)) ∧
  (∀ M M' : Set (Link a), M ⊆ M' → M' ⊆ positiveLinkSet a →
    linkSigma M ≤ linkSigma M') ∧
  (∀ A : GaugeField a → ℂ, IsBoundedObservable A →
    (IsLocalObservable A ↔ ∃ M : Set (Link a), M.Finite ∧ M ⊆ positiveLinkSet a ∧
      Measurable[linkSigma M] A)) ∧
  ∀ A B : GaugeField a → ℂ, IsBoundedObservable A → IsLocalObservable A →
    IsBoundedObservable B → IsLocalObservable B →
    (IsBoundedObservable (A + B) ∧ IsLocalObservable (A + B)) ∧
      (IsBoundedObservable (A * B) ∧ IsLocalObservable (A * B))
def DenseContinuousLocal (a : ℝ) : Prop :=
  ∀ F : GaugeField a → ℂ, Continuous F → ∀ ε : ℝ, 0 < ε →
    ∃ F' ∈ continuousLocal a, observableSupNorm (F - F') ≤ ε
def Main : Prop :=
  ∀ a : ℝ, 0 < a →
    HomeomorphPositiveLinks a ∧ BorelEqLinkSigma a ∧
      FaceEnergyAndBoltzmannWeight a ∧ MeasurableOnLinksCharacterization a ∧
      OverwriteLinksProperties a ∧ LinkSigmaAndLocality a ∧
      DenseContinuousLocal a
end InfiniteLattice.ConfigurationSpace
end YangMills.Construction
