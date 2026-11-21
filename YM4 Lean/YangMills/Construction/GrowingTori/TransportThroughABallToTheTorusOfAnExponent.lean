import YangMills.Construction.FamiliesOfLimits.TuplesTransportAndConnectedFunctionsOfATorusOnTuplesOfFourSpace
import YangMills.Construction.GrowingTori.DataAndSequencesOfTheLimitsAlongGrowingTori
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits.ExponentTorusPeriodization
variable (S : Setup) (m : ℕ+)
abbrev exponentSide : ℝ := PeriodicLattice.torusSide S.L m
abbrev ExponentTorus : Type := PeriodicLattice.FourTorus S.L m
abbrev proj : (Fin 4 → ℝ) → ExponentTorus S m := TorusMetric.torusProj (exponentSide S m)
abbrev periodShift (k : Fin 4 → ℤ) : Fin 4 → ℝ := TestFunctions.latticeTranslate (exponentSide S m) k
def maxBallRadius : ℝ := ((S.L : ℝ) ^ (m : ℕ) - 2) / 2
def cutoffMirrorData : ReflectionPositivity.CutoffMirrors.MirrorData :=
  ⟨FamiliesOfLimits.TorusTransportOfTuples.standingParams S.params 1 m, 1, one_pos, 0⟩
def torusSupp {E : Type*} [Zero E] (u : ExponentTorus S m → E) : Set (ExponentTorus S m) :=
  (cutoffMirrorData S m).supp u
def gluingSetup : SourcesAndGluing.GluingSetup :=
  ⟨FamiliesOfLimits.TorusTransportOfTuples.standingParams S.params 1 m, 1, one_pos, S.params.cubeExp⟩
def TorusDistIsLeastOverLifts : Prop :=
  ∀ x y : Fin 4 → ℝ,
    IsLeast (range fun k : Fin 4 → ℤ => TorusMetric.euclidNormVec (x - y - periodShift S m k))
        (TestFunctions.euclidDistTorus (proj S m x) (proj S m y)) ∧
      TestFunctions.euclidDistTorus (proj S m x) (proj S m y) ≤ TorusMetric.euclidNormVec (x - y)
def ProjOnBall (ρ : ℝ) : Prop :=
  (∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ, ∀ k : Fin 4 → ℤ, k ≠ 0 →
    TorusMetric.euclidNormVec (x - y) < TorusMetric.euclidNormVec (x - y - periodShift S m k)) ∧
  (∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ,
    TestFunctions.euclidDistTorus (proj S m x) (proj S m y) = TorusMetric.euclidNormVec (x - y)) ∧
  InjOn (proj S m) (ballOrigin ρ) ∧
  ∀ x ∈ ballOrigin ρ, ∀ k : Fin 4 → ℤ, k ≠ 0 → x + periodShift S m k ∉ ballOrigin ρ
section Functions
variable (ρ : ℝ) (𝕜 : Type) [RCLike 𝕜]
def PeriodizeValues : Prop :=
  (∀ f : (Fin 4 → ℝ) → 𝕜, SupportedIn f (ballOrigin ρ) →
    (∀ x ∈ ballOrigin ρ, TestFunctions.periodize (exponentSide S m) f (proj S m x) = f x) ∧
    (∀ u, u ∉ proj S m '' ballOrigin ρ → TestFunctions.periodize (exponentSide S m) f u = 0) ∧
    TestFunctions.periodize (exponentSide S m) (fun x => starRingEnd 𝕜 (f x)) =
      (fun u => starRingEnd 𝕜 (TestFunctions.periodize (exponentSide S m) f u)) ∧
    torusSupp S m (TestFunctions.periodize (exponentSide S m) f) = proj S m '' fnSupport f) ∧
  ∀ (f h : (Fin 4 → ℝ) → 𝕜) (c c' : 𝕜), SupportedIn f (ballOrigin ρ) →
    SupportedIn h (ballOrigin ρ) →
      SupportedIn (c • f + c' • h) (ballOrigin ρ) ∧
        TestFunctions.periodize (exponentSide S m) (c • f + c' • h) =
          c • TestFunctions.periodize (exponentSide S m) f + c' • TestFunctions.periodize (exponentSide S m) h
def PeriodizeNorms : Prop :=
  ∀ f : (Fin 4 → ℝ) → 𝕜, SupportedIn f (ballOrigin ρ) → (∀ x, RCLike.im (f x) = 0) →
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
      (∀ u, RCLike.im (TestFunctions.periodize (exponentSide S m) f u) = 0) ∧
      TestFunctions.IsLipschitzFor (TestFunctions.euclidDistTorus (ℓ := exponentSide S m))
        (TestFunctions.periodize (exponentSide S m) f) ∧
      TestFunctions.uniformNorm (TestFunctions.periodize (exponentSide S m) f) = TestFunctions.uniformNorm f ∧
      TestFunctions.lipConstTorus (TestFunctions.periodize (exponentSide S m) f) = TestFunctions.lipConstR4 f ∧
      TestFunctions.sharpNormTorus (S.M : ℝ) (TestFunctions.periodize (exponentSide S m) f) =
        TestFunctions.sharpNormR4 (S.M : ℝ) f
def PeriodizeSupports : Prop :=
  (∀ f h : (Fin 4 → ℝ) → 𝕜, SupportedIn f (ballOrigin ρ) → SupportedIn h (ballOrigin ρ) →
    TorusMetric.setEuclidDist (torusSupp S m (TestFunctions.periodize (exponentSide S m) f))
        (torusSupp S m (TestFunctions.periodize (exponentSide S m) h)) =
      infDist (fnSupport f) (fnSupport h)) ∧
  ∀ (f : (Fin 4 → ℝ) → 𝕜) (x : Fin 4 → ℝ) (R : ℝ), SupportedIn f (ballOrigin ρ) → 0 < R →
    R < (S.L : ℝ) ^ (m : ℕ) / 2 → fnSupport f ⊆ closedBallR4 x R →
      torusSupp S m (TestFunctions.periodize (exponentSide S m) f) ⊆
        TestFunctions.closedBallTorus (proj S m x) R
end Functions
def IsFormedThroughBall {n : ℕ} (ρ' : ℝ) (f : Fin n → RealFn)
    (g : Fin n → ExponentTorus S m → ℝ) : Prop :=
  ∀ i, (∀ x ∈ ballOrigin ρ', g i (proj S m x) = f i x) ∧ ∀ u, u ∉ proj S m '' ballOrigin ρ' → g i u = 0
def PeriodizeTuples (ρ : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : Fin n → RealFn) (hf : IsSepLipTuple f),
    SuppsWithin f (ballOrigin ρ) →
      (∀ i, TestFunctions.IsBoundedFun (SchwingerFunctions.periodizeAll S.L m f i)) ∧
      (∀ i, Measurable (SchwingerFunctions.periodizeAll S.L m f i)) ∧
      (∀ d : ℝ, 0 < d → ENNReal.ofReal d ≤ minSuppGap hn f hf →
        TestFunctions.HasSeparatedSupportsTorus (SchwingerFunctions.periodizeAll S.L m f) d) ∧
      SchwingerFunctions.IsTorusTestFamily (SchwingerFunctions.periodizeAll S.L m f) ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ maxBallRadius S m → SuppsWithin f (ballOrigin ρ') →
        ∀ g : Fin n → ExponentTorus S m → ℝ, IsFormedThroughBall S m ρ' f g →
          g = SchwingerFunctions.periodizeAll S.L m f ∧
          ∀ (K : ℕ+) (β : ℝ),
            S.connectedOnTorus K m β g = S.connectedOnFourSpace K m β f ∧
            S.centredOnTorus K m β g = S.centredOnFourSpace K m β f) ∧
      ∀ (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (hRm : R < (S.L : ℝ) ^ (m : ℕ) / 2),
        f ∈ lipTuples n hn d R hd hR →
          SchwingerFunctions.periodizeAll S.L m f ∈
            lipTuplesTorus (gluingSetup S m) m n hn d R hd hR hRm
def Statement : Prop :=
  ∀ (S : Setup) (m : ℕ+),
    TorusDistIsLeastOverLifts S m ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ maxBallRadius S m →
      ProjOnBall S m ρ ∧
      (∀ (𝕜 : Type) [RCLike 𝕜],
        PeriodizeValues S m ρ 𝕜 ∧ PeriodizeNorms S m ρ 𝕜 ∧
          PeriodizeSupports S m ρ 𝕜) ∧
      PeriodizeTuples S m ρ
end YangMills.Construction.ToriLimits.ExponentTorusPeriodization
end
