import YangMills.Construction.Continuum.RecentringOfATupleAndOfACombination
import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Continuum.CentringRespectsOperations
open YangMills.Construction.LimitConventions (cubicMotionGroup)
open YangMills.Construction.TupleLists (ofList)
open YangMills.Construction.TestSpaces (SepTuple c1CompactSupp cumulantOne centring)
open YangMills.Construction.SeparatedTuples (FormalSpan push pushSpan formalMul spanIn
  conjugation)
def CentringPreservesStructure : Prop :=
  ∀ s : SepTuple → ℝ,
    (∀ Z W : FormalSpan, (∀ X ∈ Z.support, ∀ Y ∈ W.support,
        YangMills.Construction.SeparatedTuples.SepTuple.Composable X Y) →
      centring s (formalMul Z W) =
        formalMul (centring s Z) (centring s W)) ∧
    (∀ Z : FormalSpan, centring s (conjugation Z) = conjugation (centring s Z)) ∧
    (∀ O : Set (Fin 4 → ℝ), ∀ Z ∈ spanIn O, centring s Z ∈ spanIn O) ∧
    (∀ r ∈ cubicMotionGroup, (∀ X : YangMills.Construction.SeparatedTuples.SepTuple,
        s (ofList (push r X)) = s (ofList X)) → ∀ Z : FormalSpan,
      centring s (pushSpan r Z) = pushSpan r (centring s Z)) ∧
    ((∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
      cumulantOne s f hf = 0) → ∀ Z : FormalSpan, centring s Z = Z)
end YangMills.Construction.Continuum.CentringRespectsOperations
end
