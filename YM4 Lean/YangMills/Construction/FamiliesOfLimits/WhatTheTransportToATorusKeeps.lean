import YangMills.Construction.SourcesAndGluing.FundamentalBoxAndIntegralOverATorus
import YangMills.Construction.Torus.LipschitzTuplesSeparationConcatenationAndTransport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set TestFunctions AmbientPoints
open ReflectionPositivity.AxisMirror (Ambient)
open FundamentalDomain (fundBox openBox IntegrableOnFundBox torusIntegral)
namespace FamiliesOfLimits.TorusPeriodization
variable (s : Conventions.StandingParameters)
def IsSupportedIn (A : Set (Pt s .euclidean)) (f : Pt s .euclidean → ℝ) : Prop :=
  IsCompact (tsupport f) ∧ tsupport f ⊆ A
abbrev periodizeOnTorus (f : Pt s .euclidean → ℝ) : Pt s .torus → ℝ :=
  periodize (PeriodicLattice.torusSide s.L s.m) f
def originBall (r : ℝ) : Set (Pt s .euclidean) :=
  AmbientPoints.openBall s .euclidean (0 : Fin 4 → ℝ) r
def PeriodizeEqTsumTranslates (A : Set (Pt s .euclidean))
    (f : Pt s .euclidean → ℝ) : Prop :=
  (periodizeOnTorus s f ∘ proj s .torus =
      fun x : Fin 4 → ℝ => ∑' k : Fin 4 → ℤ, f (x + latticeTranslate s.side k)) ∧
    (∀ x : Fin 4 → ℝ, {k : Fin 4 → ℤ | f (x + latticeTranslate s.side k) ≠ 0}.Subsingleton) ∧
    (A ⊆ openBox s.side → ∀ y ∈ fundBox s.side, ∀ k : Fin 4 → ℤ, k ≠ 0 →
      f (y + latticeTranslate s.side k) = 0)
def ProjPreservesDist (A : Set (Pt s .euclidean)) : Prop :=
  (∀ x ∈ A, ∀ y ∈ A,
    pointDist s .torus (proj s .torus x) (proj s .torus y) =
      pointDist s .euclidean x y) ∧
    ∀ B C : Set (Pt s .euclidean), B ⊆ A → C ⊆ A →
      setDist s .torus (proj s .torus '' B) (proj s .torus '' C) =
        setDist s .euclidean B C
def PeriodizeLinearOn (A : Set (Pt s .euclidean)) : Prop :=
  ∀ f g : Pt s .euclidean → ℝ, IsSupportedIn s A f → IsSupportedIn s A g → ∀ a b : ℝ,
    IsSupportedIn s A (a • f + b • g) ∧
      periodizeOnTorus s (a • f + b • g) = a • periodizeOnTorus s f + b • periodizeOnTorus s g
def PeriodizePreservesFun (M : ℝ) (f : Pt s .euclidean → ℝ) : Prop :=
  tsupport (periodizeOnTorus s f) = proj s .torus '' tsupport f ∧
    (IsBoundedFun f → IsBoundedFun (periodizeOnTorus s f) ∧
      uniformNorm (periodizeOnTorus s f) = uniformNorm f) ∧
    (Continuous f →
      IntegrableOnFundBox (ℓ := PeriodicLattice.torusSide s.L s.m) (periodizeOnTorus s f) ∧
        MeasureTheory.Integrable (fun x : Fin 4 → ℝ => f x) ∧
        torusIntegral (ℓ := PeriodicLattice.torusSide s.L s.m) (periodizeOnTorus s f) =
          ∫ x : Fin 4 → ℝ, f x) ∧
    (IsLipschitzFor (pointDist s .euclidean) f →
      IsLipschitzFor (pointDist s .torus) (periodizeOnTorus s f) ∧
        lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (periodizeOnTorus s f) ≤
          lipConstR4 f ∧
        sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) M (periodizeOnTorus s f) ≤
          sharpNormR4 M f) ∧
    (IsC1Fn f → IsC1Fn (periodizeOnTorus s f))
def ProjImageClosedBall : Prop :=
  ∀ (c : Pt s .euclidean) (R : ℝ), 0 < R → R ≤ s.side / 4 →
    proj s .torus '' AmbientPoints.closedBall s .euclidean c R =
      AmbientPoints.closedBall s .torus (proj s .torus c) R
def PeriodizeBasicProps (M : ℝ) (A : Set (Pt s .euclidean)) (f : Pt s .euclidean → ℝ) :
    Prop :=
  PeriodizeEqTsumTranslates s A f ∧ ProjPreservesDist s A ∧
    PeriodizeLinearOn s A ∧ PeriodizePreservesFun s M f ∧
    ProjImageClosedBall s
variable {n : ℕ}
def SupportsInOriginBall (r : ℝ) (X : Fin n → Pt s .euclidean → ℝ) : Prop :=
  ∀ i, tsupport (X i) ⊆ originBall s r
def OriginBallAdmits (M r : ℝ) (X : Fin n → Pt s .euclidean → ℝ) : Prop :=
  HasDiameterLE (originBall s r) (s.side / 2) ∧
    originBall s r ⊆ openBox s.side ∧
    ∀ i, IsSupportedIn s (originBall s r) (X i) ∧
      PeriodizeBasicProps s M (originBall s r) (X i)
def PeriodizePreservesTuple (M : ℝ) (X : Fin n → Pt s .euclidean → ℝ) : Prop :=
  periodizedTuple s X ∈ separatedTuples s .torus n ∧
    (∀ i, IsLipschitzFor (pointDist s .torus) (periodizedTuple s X i) ∧
      sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) M (periodizedTuple s X i) ≤
        sharpNormR4 M (X i)) ∧
    (∀ i k, i ≠ k →
      setDist s .torus (tsupport (periodizedTuple s X i))
          (tsupport (periodizedTuple s X k)) =
        setDist s .euclidean (tsupport (X i)) (tsupport (X k))) ∧
    ∀ (i : Fin n) (c : Pt s .euclidean) (R : ℝ), 0 < R → R ≤ s.side / 4 →
      tsupport (X i) ⊆ AmbientPoints.closedBall s .euclidean c R →
        tsupport (periodizedTuple s X i) ⊆
          AmbientPoints.closedBall s .torus (proj s .torus c) R
variable {s}
def ConnectedSchwingerDefined (t : Conventions.StandingParameters)
    (X : Fin n → Pt s .euclidean → ℝ) : Prop :=
  FitsInTorusHalfSide t X ∧ ∀ i, IsBoundedFun (periodizedTuple t X i)
variable (s)
def EventuallyConnectedSchwingerDefined (X : Fin n → Pt s .euclidean → ℝ) : Prop :=
  ∀ t : ℕ → Conventions.StandingParameters, (∀ j, (t j).L = s.L) →
    Tendsto (fun j => (t j).side) atTop atTop →
      ∀ᶠ j in atTop, ConnectedSchwingerDefined (t j) X
def PeriodizationProperties : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : ℝ), 1 ≤ M →
    (∀ A : Set (Pt s .euclidean), HasDiameterLE A (s.side / 2) →
      ∀ f : Pt s .euclidean → ℝ, IsSupportedIn s A f → PeriodizeBasicProps s M A f) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ X ∈ separatedTuples s .euclidean n,
      (∃ r : ℝ, 0 < r ∧ SupportsInOriginBall s r X) ∧
      (∀ r : ℝ, 0 < r → SupportsInOriginBall s r X → 4 * r ≤ s.side →
        OriginBallAdmits s M r X ∧ PeriodizePreservesTuple s M X) ∧
      (2 ≤ n → EventuallyConnectedSchwingerDefined s X)
end FamiliesOfLimits.TorusPeriodization
end YangMills.Construction
end
