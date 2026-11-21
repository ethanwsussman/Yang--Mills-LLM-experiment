import YangMills.Construction.Continuum.ClassesOfTuplesMomentConstantsAndApproximants
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Lattice.AdicRationalsPositive
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter AmbientPoints
open R4TupleForms (FinTuple listOf)
open TorusFunctionals (sharpNormAt)
open ReflectionPositivity (maxNorm)
open PeriodicLattice (adicRationalsPositive)
open scoped ENNReal Topology
namespace SeparatedClasses
variable (s : Conventions.StandingParameters)
def FunctionalsAgree : Prop :=
  (∀ σ : SeparatedTuples.TupleFunctional, σ.IsEntrywiseLinear ↔
    ∀ n, 1 ≤ n → IsTupleMultilinear (ofLength (fun X : FinTuple s => σ (listOf X)) n)) ∧
  ∀ τ : FinTuple s → ℝ, IsTupleFunctional τ ↔
    ∃ σ : SeparatedTuples.TupleFunctional, σ.IsEntrywiseLinear ∧ ∀ X, τ X = σ (listOf X)
def ClassesMonotone : Prop :=
  ∀ ϖ ϖ' d d' R R' : ℝ, ϖ ∈ adicRationalsPositive s.L →
    ϖ' ∈ adicRationalsPositive s.L → ϖ ≤ ϖ' → 0 < d' → d' ≤ d → d ≤ ϖ → 0 < R → R ≤ R' →
      classOf s ϖ d R ⊆ classOf s ϖ' d' R'
def FiniteFamilyInOneClass : Prop :=
  ∀ (n : ℕ) (X : Fin n → FunctionTuple s .euclidean),
    (∀ b, X b ∈ allSeparatedTuples s .euclidean) →
      ∃ ϖ ∈ adicRationalsPositive s.L, ∃ d R : ℝ, 0 < d ∧ d ≤ ϖ ∧ 0 < R ∧
        ∀ b, X b ∈ classOf s ϖ d R
def IsometryPreservesSharpNorm : Prop :=
  ∀ (M : ℕ) (r : Pt s .euclidean ≃ Pt s .euclidean), IsDistIsometry r →
    ∀ f : Pt s .euclidean → ℝ, TestFunctions.IsBoundedFun f →
      TestFunctions.IsLipschitzFor (pointDist s .euclidean) f →
        sharpNormAt s .euclidean M (transportFn r f) = sharpNormAt s .euclidean M f
def IsometryPreservesSupportedTuples : Prop :=
  ∀ (r : Pt s .euclidean ≃ Pt s .euclidean), IsDistIsometry r → ∀ d R : ℝ, 0 < d → 0 < R →
    ∀ X ∈ allSeparatedTuples s .euclidean, IsSupportedInBalls R X.2 →
      PairwiseSupportSep s d X.2 →
        transportTuple r X.2 ∈ separatedTuples s .euclidean X.1 ∧
          IsSupportedInBalls R (transportTuple r X.2) ∧
            PairwiseSupportSep s d (transportTuple r X.2)
def HyperoctahedralPreservesClasses : Prop :=
  ∀ (w : InfiniteLattice.hyperoctahedralLinearGroup) (ϖ d R : ℝ), ϖ ∈ adicRationalsPositive s.L →
    0 < d → d ≤ ϖ → 0 < R →
      signedPermTuple w '' classOf s ϖ d R = classOf s ϖ d R ∧
        ∀ (M : ℕ) (Cst : ℕ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ), ∀ X ∈ classOf s ϖ d R,
          momentWeight s M Cst C₁ d R (signedPermTuple w X) =
              momentWeight s M Cst C₁ d R X ∧
            momentWeightSq s M Cst C₁ d R (signedPermTuple w X) =
              momentWeightSq s M Cst C₁ d R X
def FarTranslatesInClass : Prop :=
  ∀ ϖ d R : ℝ, ϖ ∈ adicRationalsPositive s.L → 0 < d → d ≤ ϖ → 0 < R →
    ∀ X ∈ classOf s ϖ d R, ∀ Y ∈ classOf s ϖ d R, ∀ v : Fin 4 → ℝ, 2 * ϖ < maxNorm v →
      tupleAppend X (translateTuple v Y) ∈ allSeparatedTuples s .euclidean ∧
        IsSupportedInBalls R (tupleAppend X (translateTuple v Y)).2 ∧
          PairwiseSupportSep s d (tupleAppend X (translateTuple v Y)).2 ∧
            ∀ ϖ' ∈ adicRationalsPositive s.L, ϖ + maxNorm v ≤ ϖ' →
              tupleAppend X (translateTuple v Y) ∈ classOf s ϖ' d R
def TranslationContinuousSharpNorm : Prop :=
  ∀ (M : ℕ) (f : Pt s .euclidean → ℝ), IsC1Fn f → IsCompact (tsupport f) →
    ∀ v : Fin 4 → ℝ, Tendsto
      (fun v' : Fin 4 → ℝ =>
        sharpNormAt s .euclidean M (translateFn v' f - translateFn v f))
      (𝓝 v) (𝓝 0)
def quarterThickening (d : ℝ) (A : Set (Pt s .euclidean)) : Set (Pt s .euclidean) :=
  {x | setDist s .euclidean {x} A < ENNReal.ofReal (d / 4)}
def SupportNeighbourhoods : Prop :=
  ∀ d R : ℝ, 0 < d → 0 < R → ∀ X ∈ allSeparatedTuples s .euclidean,
    IsSupportedInBalls R X.2 → PairwiseSupportSep s d X.2 →
      (∀ i, IsOpen (quarterThickening s d (tsupport (X.2 i))) ∧
        tsupport (X.2 i) ⊆ quarterThickening s d (tsupport (X.2 i)) ∧
          ∃ B, IsClosedBallRadius s .euclidean (R + d / 4) B ∧
            quarterThickening s d (tsupport (X.2 i)) ⊆ B) ∧
      (Pairwise fun i k => ENNReal.ofReal (d / 2) ≤ setDist s .euclidean
        (quarterThickening s d (tsupport (X.2 i))) (quarterThickening s d (tsupport (X.2 k)))) ∧
      ∀ v v' : Fin 4 → ℝ, pointDist s .euclidean v' v < d / 4 → ∀ i,
        tsupport (translateFn v' (X.2 i)) ⊆
          translateEquiv s v '' quarterThickening s d (tsupport (X.2 i))
def SeparatingTuplesAreSeparated : Prop :=
  ∀ X ∈ SeparatingFamily.separatingTuples s.L, SeparatedTuples.IsDisjointlySupported X ∧
    (X ≠ [] → (∀ f ∈ X, TestFunctions.IsC1R4 f ∧ HasCompactSupport f) ∧
      X.Pairwise fun f h => Disjoint (tsupport f) (tsupport h))
def ClassFacts : Prop :=
  ∀ s : Conventions.StandingParameters, FunctionalsAgree s ∧ ClassesMonotone s ∧
    FiniteFamilyInOneClass s ∧ IsometryPreservesSharpNorm s ∧
    IsometryPreservesSupportedTuples s ∧ HyperoctahedralPreservesClasses s ∧
    FarTranslatesInClass s ∧ TranslationContinuousSharpNorm s ∧
    SupportNeighbourhoods s ∧ SeparatingTuplesAreSeparated s
end SeparatedClasses
end YangMills.Construction
end
