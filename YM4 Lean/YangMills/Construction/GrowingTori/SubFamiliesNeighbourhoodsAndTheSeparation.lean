import YangMills.Construction.GrowingTori.TuplesClassesAndAdmissibleFamiliesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits.SubfamiliesAndGaps
def SubfamilyAdmissible : Prop :=
  ∀ (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (q : ℕ) (hq : 1 ≤ q) (A : Fin q → Set (Fin 4 → ℝ)),
    AdmissibleSets hq d R hd hR A →
      ∀ (J : Finset (Fin q)) (hJ : J.Nonempty),
        AdmissibleSets (q := J.card) hJ.card_pos d R hd hR (subfamily A J)
def ThickeningDistanceBound : Prop :=
  ∀ (K K' : Set (Fin 4 → ℝ)) (hK : IsCompact K) (hK' : IsCompact K') (ε ε' : ℝ) (hε : 0 < ε)
    (hε' : 0 < ε'),
    infDist K K' - ENNReal.ofReal ε - ENNReal.ofReal ε' ≤
      infDist (closedThick K hK ε hε) (closedThick K' hK' ε' hε')
def SepTuplesLipschitz (p : Conventions.StandingParameters) : Prop :=
  (∀ (n : ℕ) (f : Fin n → RealFn),
    f ∈ sepTuplesR4 p n ↔ IsSepLipTuple f ∧ ∀ i, ContDiff ℝ 1 (f i)) ∧
  ∀ K : Set (Fin 4 → ℝ), c1SuppIn p K ⊆ lipSuppIn K
def SupportGapPositive : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : Fin n → RealFn) (hf : IsSepLipTuple f),
    0 < minSuppGap hn f hf ∧
    (∃ r : ℝ, 0 < r ∧ SuppsWithin f (ballOrigin r)) ∧
    ∀ (r : ℝ) (hr : 0 < r), SuppsWithin f (ballOrigin r) →
      ∀ (d : ℝ) (hd : 0 < d), ENNReal.ofReal d ≤ minSuppGap hn f hf →
        AdmissibleSets (q := n) (by omega) d r hd hr (fun i => fnSupport (f i)) ∧
          f ∈ lipTuples n hn d r hd hr
def AdmissibleProductsInClasses (p : Conventions.StandingParameters) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin n → Set (Fin 4 → ℝ)),
    AdmissibleSets (q := n) (by omega) d R hd hR A →
      (∀ g : Fin n → RealFn, (∀ l, g l ∈ lipSuppIn (A l)) →
        g ∈ lipTuples n hn d R hd hR) ∧
      ∀ g : Fin n → RealFn, (∀ l, g l ∈ c1SuppIn p (A l)) →
        g ∈ sepTuplesR4 p n ∩ lipTuples n hn d R hd hR
def EuclideanSpaceNotions (P : PeriodicSpace.Params) : Prop :=
  (∀ x y : Fin 4 → ℝ,
    PeriodicSpace.Kind.quotDist P .euclidean x y = TorusMetric.euclidNormVec (x - y)) ∧
  (∀ S T : Set (Fin 4 → ℝ),
    PeriodicSpace.Kind.setInfDist P .euclidean S T = infDist S T) ∧
  (∀ (y : Fin 4 → ℝ) (S : Set (Fin 4 → ℝ)),
    PeriodicSpace.Kind.infDistPt P .euclidean y S = ptInfDist y S) ∧
  (∀ u : RealFn,
    PeriodicSpace.Kind.IsC1Fn P .euclidean u ↔ ContDiff ℝ 1 u) ∧
  (∀ u : RealFn, PeriodicSpace.Kind.supportQ P .euclidean u = fnSupport u) ∧
  ∀ u : RealFn, PeriodicSpace.Kind.IsLipschitzQ P .euclidean u ↔ LipschitzR4 u
def EuclideanBallsAndLipClass (P : PeriodicSpace.Params) : Prop :=
  (∀ (x : Fin 4 → ℝ) (R : ℝ), 0 < R →
    PeriodicSpace.Kind.closedBallAbout P .euclidean x R = closedBallR4 x R) ∧
  (∀ r : ℝ, 0 < r →
    PeriodicSpace.Kind.centredBall P .euclidean (ENNReal.ofReal r) = ballOrigin r) ∧
  ∀ K : Set (Fin 4 → ℝ), PeriodicSpace.Kind.lipschitzSupportedIn P .euclidean K = lipSuppIn K
def EuclideanC1Classes (P : PeriodicSpace.Params) (p : Conventions.StandingParameters) : Prop :=
  (∀ K : Set (Fin 4 → ℝ), PeriodicSpace.Kind.c1SupportedIn P .euclidean K = c1SuppIn p K) ∧
  ∀ n : ℕ, 1 ≤ n →
    PeriodicSpace.Kind.sepC1Tuples P .euclidean n = sepTuplesR4 p n
def EuclideanTuples (P : PeriodicSpace.Params) : Prop :=
  (∀ (n : ℕ), 1 ≤ n → ∀ f : Fin n → RealFn,
    f ∈ PeriodicSpace.Kind.sepLipTuples P .euclidean n ↔
      IsSepLipTuple f) ∧
  (∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ, 0 < r → ∀ f : Fin n → RealFn,
    f ∈ PeriodicSpace.Kind.sepLipTuplesWithin P .euclidean n
        (PeriodicSpace.Kind.centredBall P .euclidean (ENNReal.ofReal r)) ↔
      IsSepLipTuple f ∧ SuppsWithin f (ballOrigin r)) ∧
  (∀ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → RealFn)
    (hg : IsSepLipTuple g),
    PeriodicSpace.Kind.supportGap P .euclidean g = minSuppGap hn g hg) ∧
  PeriodicSpace.Kind.allowedRadii P .euclidean = Ioi 0 ∧
  ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (hd : 0 < d) (hR : 0 < R),
    PeriodicSpace.Kind.lipTuplesSpacedInBalls P .euclidean n d R =
      lipTuples n hn d R hd hR
def GluingClassEuclidean (G : SourcesAndGluing.GluingSetup) : Prop :=
  ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (d R : ℝ) (hd : 0 < d) (hR : 0 < R),
    SourcesAndGluing.Ambient.euclidean.lipClass G n d R =
      lipTuples n hn d R hd hR
def Statement : Prop :=
  SubfamilyAdmissible ∧ ThickeningDistanceBound ∧
  (∀ p : Conventions.StandingParameters, SepTuplesLipschitz p ∧ AdmissibleProductsInClasses p) ∧
  SupportGapPositive ∧
  (∀ P : PeriodicSpace.Params,
    EuclideanSpaceNotions P ∧ EuclideanBallsAndLipClass P ∧ EuclideanTuples P ∧
      ∀ p : Conventions.StandingParameters, EuclideanC1Classes P p) ∧
  ∀ G : SourcesAndGluing.GluingSetup, GluingClassEuclidean G
end YangMills.Construction.ToriLimits.SubfamiliesAndGaps
end
