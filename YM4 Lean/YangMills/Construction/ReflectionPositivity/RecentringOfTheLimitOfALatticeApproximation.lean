import YangMills.Construction.Continuum.ConnectedFunctionsCentredFunctionalsOnTheSpanAndCumulantsOfAState
import YangMills.Construction.Continuum.RecentringOfATupleAndOfACombination
import YangMills.Construction.ReflectionPositivity.HamiltonianBoundsTheMomentaInTheLimit
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitCentring
open YangMills.Construction
open YangMills.Construction.ReflectionPositivity
open YangMills.Construction.LimitConventions (ApproxTriple cubicMotionGroup)
open YangMills.Construction.TupleLists (ofList toList)
open YangMills.Construction.SetPartition (atLeastTwoPartitions)
open YangMills.Construction.TestSpaces (IsMultilinearSepFunctional SepTupleOfCard c1CompactSupp
  centredPart centredPartFunctional cumulant cumulantOne sepTupleNil ofList_sepTupleNil
  singletonSepTuple centredTuple centring sepRestrict)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional pushSpan formalMul spanIn
  conjugation)
def listFunctional (s : TestSpaces.SepTuple → ℝ) (h : s sepTupleNil = 1) : TupleFunctional where
  toFun X := s (ofList X)
  map_nil := by rw [ofList_sepTupleNil]; exact h
def CentredValueAtCentring (s : TestSpaces.SepTuple → ℝ)
    (hs : IsMultilinearSepFunctional s) : Prop :=
  (∀ Z : FormalSpan,
    (centredPartFunctional s).spanExtension Z = (listFunctional s hs.1).spanExtension (centring s Z)) ∧
  (∀ (k : ℕ) (X : SepTupleOfCard k),
    (listFunctional s hs.1).spanExtension (centredTuple s (toList ⟨k, X⟩)) =
      ((∑ π ∈ atLeastTwoPartitions (Finset.univ : Finset (Fin k)),
        ∏ B ∈ π.parts, cumulant s (sepRestrict X B) : ℝ) : ℂ)) ∧
  centredPart s sepTupleNil = 1 ∧
  (∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
    centredPart s ⟨1, singletonSepTuple f hf⟩ = 0) ∧
  IsMultilinearSepFunctional (centredPart s)
def withOffset {L : ℕ} (T : ApproxTriple L) (c : ℕ+ → ℝ) : ApproxTriple L where
  cutoff := T.cutoff
  tendsto_cutoff := T.tendsto_cutoff
  state := T.state
  isProbabilityMeasure_state := T.isProbabilityMeasure_state
  offset := c
def HasFaceMeans {L : ℕ} (T : ApproxTriple L) (c : ℕ+ → ℝ) : Prop :=
  ∀ (j : ℕ+) (p : InfiniteLattice.ElementaryPlaquette (InfiniteLattice.refinedSpacing L (T.cutoff j))),
    ∫ U, InfiniteLattice.faceEnergy U p ∂T.state j = c j
def CentredApproxAndCumulants (D : AxisMirror.MirrorData) (T : ApproxTriple D.L)
    (s : TestSpaces.SepTuple → ℝ) : Prop :=
  (∃ c : ℕ+ → ℝ, HasFaceMeans T c ∧
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D (withOffset T c) ∧
    ApproxTriple.IsReflPos (withOffset T c) ∧
    ApproxTriple.ConvergesTo (withOffset T c) (centredPartFunctional s)) ∧
  (∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
    cumulantOne s f hf = s ⟨1, singletonSepTuple f hf⟩ ∧
      Tendsto (fun j => ∫ U, ApproximatingSequences.LatticeApproximation.smearedField T j f U ∂T.state j)
        atTop (𝓝 (s ⟨1, singletonSepTuple f hf⟩))) ∧
  ∀ (n : ℕ), 2 ≤ n → ∀ X : SepTupleOfCard n,
    Tendsto (fun j => InfiniteLattice.ursellFunction (T.state j) n X.1) atTop
      (𝓝 (cumulant s X : ℂ))
def CentringRespectsOperations (s : TestSpaces.SepTuple → ℝ) : Prop :=
  (∀ Z W : FormalSpan, (∀ X ∈ Z.support, ∀ Y ∈ W.support, SeparatedTuples.SepTuple.Composable X Y) →
    centring s (formalMul Z W) = formalMul (centring s Z) (centring s W)) ∧
  (∀ Z : FormalSpan, centring s (conjugation Z) = conjugation (centring s Z)) ∧
  (∀ r ∈ cubicMotionGroup, ∀ Z : FormalSpan,
    centring s (pushSpan r Z) = pushSpan r (centring s Z)) ∧
  ∀ O : Set (Fin 4 → ℝ), IsOpen O → ∀ Z ∈ spanIn O, centring s Z ∈ spanIn O
def CentredSymmetricAndCone (L : ℕ) (s : TestSpaces.SepTuple → ℝ)
    (h : s sepTupleNil = 1) : Prop :=
  (∀ r ∈ cubicMotionGroup, ∀ W : FormalSpan,
    (centredPartFunctional s).spanExtension (pushSpan r W) =
      (centredPartFunctional s).spanExtension W) ∧
  (∀ M : Mirrors.ReflectingHyperplane, ∀ Z ∈ spanIn M.positiveSide,
    (centredPartFunctional s).spanExtension
        (formalMul (pushSpan M.reflect (conjugation Z)) Z) =
      (listFunctional s h).spanExtension
        (formalMul (pushSpan M.reflect (conjugation (centring s Z))) (centring s Z)) ∧
    SeparatedTupleFunctionals.IsRealNonneg ((listFunctional s h).spanExtension
      (formalMul (pushSpan M.reflect (conjugation (centring s Z))) (centring s Z)))) ∧
  LimitMomentumBound.MomentumBoundAssertions L (listFunctional s h) ∧
    LimitMomentumBound.MomentumBoundAssertions L (centredPartFunctional s)
def CentringTrivialAtFaceMeans {L : ℕ} (T : ApproxTriple L)
    (s : TestSpaces.SepTuple → ℝ) : Prop :=
  HasFaceMeans T T.offset →
    (∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
      cumulantOne s f hf = 0) ∧
    (∀ Z : FormalSpan, centring s Z = Z) ∧ centredPart s = s
def LimitCentringTheorem : Prop :=
  (∀ (s : TestSpaces.SepTuple → ℝ) (hs : IsMultilinearSepFunctional s),
    CentredValueAtCentring s hs) ∧
  ∀ (D : AxisMirror.MirrorData) (T : ApproxTriple D.L) (s : TestSpaces.SepTuple → ℝ),
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T → ApproxTriple.IsReflPos T →
    ApproxTriple.ConvergesTo T (fun X => s (ofList X)) →
    ∃ hs : IsMultilinearSepFunctional s,
      CentredApproxAndCumulants D T s ∧ CentringRespectsOperations s ∧
        CentredSymmetricAndCone D.L s hs.1 ∧
        CentringTrivialAtFaceMeans T s
end YangMills.Construction.ReflectionPositivity.LimitCentring
end
