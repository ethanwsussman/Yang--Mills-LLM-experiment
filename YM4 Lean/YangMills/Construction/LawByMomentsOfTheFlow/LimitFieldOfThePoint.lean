import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ChainNoise LevelTestFunctions ResponseInTheExpansion MomentMethod
def translationVector (L p : ℕ) : Fin 4 → ℤ := Pi.single 0 ((p : ℤ) * (L : ℤ))
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
theorem lastSeparated_le : S.lastSeparated ≤ S.data.windowLevel := by
  unfold MomentPoint.lastSeparated
  classical
  exact le_trans (Nat.findGreatest_le S.data.scaleLevel) S.supAdmissible.scaleLevel_le
def withSideExponent (m : ℕ) (hp : ({ S.data with sideExponent := m } : LevelData Λ.k).SupAdmissible Λ.stepParams.side Λ.R Λ.d)
    (hs : Λ.stepParams.side * Λ.stepParams.n₀ ≤ ({ S.data with sideExponent := m } : LevelData Λ.k).period Λ.stepParams.side) : MomentPoint Λ :=
  { S with data := { S.data with sideExponent := m }, supAdmissible := hp, side_le := hs }
abbrev SampleSpace : Type :=
  TorusField (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)) × ChainNoise.ChainNoise Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
def sampleLaw : Measure S.SampleSpace := (wilsonLaw S.β _).prod (chainNoiseLaw Λ.stepParams S.data.windowLevel _)
def sampleOf (rule : NoiseRule Λ.stepParams) (ω : S.SampleSpace) : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) :=
  rule.chain S.tower S.data.windowLevel (S.data.period Λ.stepParams.side) ω.1 ω.2
abbrev sideAtLevel (u : ℕ) : ℕ := fineSide Λ.stepParams.side (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
def sampleAtLevel (u : ℕ) (hu : u ≤ S.data.windowLevel) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    MarkedSample Λ.stepParams u (S.sideAtLevel u) :=
  sampleBelow Λ.stepParams u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) ((Nat.add_sub_of_le hu).symm ▸ w)
def stateAtLevel (u : ℕ) (hu : u ≤ S.data.windowLevel) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    StageState S.tower u (S.sideAtLevel u) :=
  stageState S.tower u (S.sideAtLevel u) (S.sampleAtLevel u hu w)
end MomentPoint
variable {Λ : MomentParameters}
def translatedTori (Sq : ℕ → MomentPoint Λ) (p : ℕ) : TranslatedLaws where
  Ω i := (Sq i).SampleSpace
  μ i := (Sq i).sampleLaw
  τ i := pairTranslate Λ.stepParams (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side) (translationVector Λ.stepParams.side p)
abbrev SampleObservable (Λ : MomentParameters) : Type 1 :=
  (S : MomentPoint Λ) → MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) → ℝ
def sampleFamily (rule : NoiseRule Λ.stepParams) (Sq : ℕ → MomentPoint Λ) (p : ℕ) (g : SampleObservable Λ) : (translatedTori Sq p).Family :=
  fun i ω => g (Sq i) ((Sq i).sampleOf rule ω)
structure LimitLawAtPoint (S : MomentPoint Λ) where
  rule : NoiseRule Λ.stepParams
  rule_admissible : rule.IsAdmissible S.tower
  period : ℕ
  one_le_period : 1 ≤ period
  exponents : ℕ → ℕ
  strictMono_exponents : StrictMono exponents
  points : ℕ → MomentPoint Λ
  points_eq : ∀ i, ∃ hp hs, points i = S.withSideExponent (exponents i) hp hs
  Index : Type
  countable_index : Countable Index
  observables : Index → SampleObservable Λ
  hasBoundedMoments : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily rule points period (observables j))
  law : Measure (TranslateValues Index)
  isJointLimitLaw : IsJointLimitLaw (translatedTori points period) (fun j => sampleFamily rule points period (observables j)) law
namespace LimitLawAtPoint
variable {S : MomentPoint Λ} (F : LimitLawAtPoint S)
def condMean (Y : TranslateValues F.Index → ℝ) : TranslateValues F.Index → ℝ := invariantCondExp F.law Y
def condMeanAt (j : F.Index) : TranslateValues F.Index → ℝ := F.condMean (evalAtZero j)
end LimitLawAtPoint
end YangMills.Construction.MomentLaw
end
