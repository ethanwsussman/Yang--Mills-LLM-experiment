import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
open YangMills.Construction.LimitSpaces YangMills.Construction.LimitSpaces.Ambient
open YangMills.Construction.AmbientPoints YangMills.Construction.Conventions
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings
variable (s : StandingParameters)
def C1SupportedHasFiniteNorms (M : SharpParameter) : Prop :=
  ∀ f ∈ c1SupportedIn (univ : Set (EuclideanFour s)),
    IsBoundedFun f ∧ IsLipschitzFor euclidDistR4 f ∧
      (∀ i : Fin 4, IsBoundedFun (partialDerivR4 i f)) ∧
      sharpNormR4 (M : ℝ) f ≤ 80 * (M : ℝ) * c1NormR4 f
def SharpNormIsNorm (M : SharpParameter) : Prop :=
  ∀ A : Set (EuclideanFour s),
    IsFunctionSubspace (c1SupportedIn A) ∧
      IsNormOn (c1SupportedIn A) (sharpNormR4 (M : ℝ))
def IsometryPreservesNorms (M : SharpParameter) (r : FourIsometry s) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (f : EuclideanFour s → E),
    IsBoundedFun f → IsLipschitzFor euclidDistR4 f →
      uniformNorm (transportFn r.1 f) = uniformNorm f ∧
        lipConstR4 (transportFn r.1 f) = lipConstR4 f ∧
          sharpNormR4 (M : ℝ) (transportFn r.1 f) = sharpNormR4 (M : ℝ) f
def IsometryPreservesBallsAndSetDist (r : FourIsometry s) : Prop :=
  (∀ (S : Set (EuclideanFour s)) (x : Fin 4 → ℝ) (R : ℝ), S ⊆ closedBallR4 x R →
      ∃ y : Fin 4 → ℝ, r.1 '' S ⊆ closedBallR4 y R) ∧
    ∀ S S' : Set (EuclideanFour s), setDistR4 (r.1 '' S) (r.1 '' S') = setDistR4 S S'
def TranslateContinuousSharp (M : SharpParameter) : Prop :=
  ∀ f ∈ c1SupportedIn (univ : Set (EuclideanFour s)), ∀ v : Fin 4 → ℝ,
    Tendsto (fun w : Fin 4 → ℝ =>
      sharpNormR4 (M : ℝ) (translateFn w f - translateFn v f))
      (𝓝 v) (𝓝 0)
variable {s}
def HasTwoNonemptyMembers {k : ℕ} (A : Fin k → Set (EuclideanFour s)) : Prop :=
  ∃ i j, i ≠ j ∧ (A i).Nonempty ∧ (A j).Nonempty
def minPairSetDist {k : ℕ} (A : Fin k → Set (EuclideanFour s)) : ℝ≥0∞ :=
  ⨅ (i : Fin k) (j : Fin k) (_ : i ≠ j ∧ (A i).Nonempty ∧ (A j).Nonempty),
    setDistR4 (A i) (A j)
open Classical in
def separationConst {k : ℕ} (A : Fin k → Set (EuclideanFour s)) : ℝ :=
  if HasTwoNonemptyMembers A then (minPairSetDist A).toReal else 1
open Classical in
def thickening {k : ℕ} (A : Fin k → Set (EuclideanFour s)) (i : Fin k) :
    Set (EuclideanFour s) :=
  if A i = ∅ then ∅
  else {x | setDistR4 {x} (A i) ≤ ENNReal.ofReal (separationConst A / 3)}
variable (s)
def DisjointCompactsHaveDisjointThickenings : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set (EuclideanFour s), (∀ i, IsCompact (A i)) →
    (Pairwise fun i j => Disjoint (A i) (A j)) →
      0 < separationConst A ∧ (∀ i, IsCompact (thickening A i)) ∧
        (Pairwise fun i j => Disjoint (thickening A i) (thickening A j)) ∧
          ∀ (i : Fin k) (v : Fin 4 → ℝ), euclidNormVec v ≤ separationConst A / 3 →
            (fun x : Fin 4 → ℝ => x + v) '' A i ⊆ thickening A i
def Statement : Prop :=
  ∀ (s : StandingParameters) (M : SharpParameter),
    (C1SupportedHasFiniteNorms s M ∧ SharpNormIsNorm s M) ∧
      (∀ r : FourIsometry s,
        IsometryPreservesNorms s M r ∧ IsometryPreservesBallsAndSetDist s r) ∧
        TranslateContinuousSharp s M ∧ DisjointCompactsHaveDisjointThickenings s
end YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings
end
