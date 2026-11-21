import YangMills.Construction.Continuum.DistributionsOnOpenSetsOfPointsAndRegularFunctionals
import YangMills.Construction.Continuum.FunctionalsWithAOnePointFunction
import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAtACutoff
import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open LimitTheorem
section PassedConditions
variable (M ϑ : ℝ) (C : ConditionConstants)
open TestSpaces (SepTupleOfCard)
open SeparatedTuples (TupleFunctional)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 separatedPairsR4)
open InfiniteLattice (AmbientSpace)
def PerBallBoundsAt (σ : TupleFunctional) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ R : ℝ, 0 < R → ∀ d : ℝ, 0 < d → ∀ X : SepTupleOfCard n,
    (∀ i, ∃ x, tsupport (X.1 i) ⊆ closedBallR4 x R) →
    (∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4 (tsupport (X.1 i)) (tsupport (X.1 l))) →
    |connectedFn σ X| ≤ C.perBallConst n d R * ∏ i, sharpNormR4 M (X.1 i) ∧
      |connectedFn σ X| ≤ C.A d R * C.B R ^ n * (n.factorial : ℝ) ^ C.κStar *
        ∏ i, sharpNormR4 M (X.1 i)
def TwoPointLawHoldsAt (σ : TupleFunctional) : Prop :=
  ∀ d ∈ Ioc (0 : ℝ) C.d₀, ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ →
    ContDiff ℝ 1 f → ContDiff ℝ 1 h →
      ∃ X : SepTupleOfCard 2, X.1 = ![f, h] ∧ TwoPointAsymptotic C d (connectedFn σ X) f h
end PassedConditions
namespace GibbsLimitInheritance
open InfiniteLattice (AmbientSpace smearedEnergyCumulant smearedEnergy)
open CutoffLattice (FieldsAt)
open InfiniteLattice.CutoffRepresentative (centredProduct)
open TestFunctions (IsLipschitzFor HasSeparatedSupportsR4 inverseEighthKernel closedBallR4 euclidDistR4
  sharpNormR4 separatedPairsR4)
open TestSpaces (SepTupleOfCard flatSchwartzSet weightedSeminorm)
open SeparatedTuples (TupleFunctional)
abbrev ConfigMeasures (L : ℕ) (K : ℕ+ → ℕ+) : Type :=
  ∀ k, Measure (FieldsAt L (K k))
variable {L : ℕ} {K : ℕ+ → ℕ+}
def IsRepresentativeLimit (ρ ν : ConfigMeasures L K) (σ : TupleFunctional) : Prop :=
  ∀ X : TestSpaces.SepTuple,
    Tendsto (fun k => ∫ U, centredProduct L (K k) (ν k) X U ∂ρ k) atTop (𝓝 (evalOnMap σ X))
abbrev cumulantFamilyOf (σ : TupleFunctional) : CumulantFamily := fun _ _ X => connectedFn σ X
def CumulantsAreLimits (ρ ν : ConfigMeasures L K) (σ : TupleFunctional) : Prop :=
  (∀ X : SepTupleOfCard 1,
    Tendsto (fun k => (∫ U, smearedEnergy (X.1 0) U ∂ρ k) - ∫ U, smearedEnergy (X.1 0) U ∂ν k)
      atTop (𝓝 (connectedFn σ X))) ∧
  ∀ n, 2 ≤ n → ∀ X : SepTupleOfCard n,
    Tendsto (fun k => smearedEnergyCumulant (ρ k) X.1) atTop (𝓝 ((connectedFn σ X : ℝ) : ℂ))
def StatesPerBallBounds (M : ℝ) (C : ConditionConstants) (ρ : ConfigMeasures L K) : Prop :=
  ∀ k, ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → ∀ R : ℝ, 0 < R → ∀ f : Fin n → AmbientSpace → ℝ,
    (∀ i, IsLipschitzFor euclidDistR4 (f i)) → (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) →
    HasSeparatedSupportsR4 f d →
      ‖smearedEnergyCumulant (ρ k) f‖ ≤
          C.perBallConst n d R * ∏ i, sharpNormR4 M (f i) ∧
        ‖smearedEnergyCumulant (ρ k) f‖ ≤
          C.A d R * C.B R ^ n * (n.factorial : ℝ) ^ C.κStar *
            ∏ i, sharpNormR4 M (f i)
def StatesOnePointTransfer (M : ℝ) (c₁ : ℝ → ℝ) (ρ ν : ConfigMeasures L K) : Prop :=
  ∀ k, ∀ R : ℝ, 0 < R → ∀ (f : AmbientSpace → ℝ) (x : AmbientSpace),
    IsLipschitzFor euclidDistR4 f → tsupport f ⊆ closedBallR4 x R →
      |(∫ U, smearedEnergy f U ∂ρ k) - ∫ U, smearedEnergy f U ∂ν k| ≤
        c₁ R * sharpNormR4 M f
def OnePointBounded (M : ℝ) (c₁ : ℝ → ℝ) (σ : TupleFunctional) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ X : SepTupleOfCard 1, (∃ x, tsupport (X.1 0) ⊆ closedBallR4 x R) →
    |connectedFn σ X| ≤ c₁ R * sharpNormR4 M (X.1 0)
def IsOnePointCoefficient (σ : TupleFunctional) (c : ℝ) : Prop :=
  ∀ X : SepTupleOfCard 1, connectedFn σ X = c * ∫ x, X.1 0 x
def unitIntegralTestFunctions : Set (AmbientSpace → ℝ) :=
  {f | f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) ∧
    tsupport f ⊆ closedBallR4 0 1 ∧ ∫ x, f x = 1}
def twoPointScale (d : ℝ) (f h : AmbientSpace → ℝ) : ℝ :=
  twoPointFactor * inverseEighthKernel f h / Real.log (1 / d) ^ 2
def StatesObeyTwoPointLaw (ϑ : ℝ) (C : ConditionConstants) (ρ : ConfigMeasures L K) : Prop :=
  ∀ d ∈ Ioc (0 : ℝ) C.d₀, ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ →
    ContDiff ℝ 1 f → ContDiff ℝ 1 h → ∀ᶠ k in atTop, ∃ t : ℝ,
      smearedEnergyCumulant (ρ k) ![f, h] = ((twoPointScale d f h * t : ℝ) : ℂ) ∧
        1 / 2 * (1 - C.ηBar d) ^ 4 ≤ t ∧ t ≤ 3 / 2 * (1 + C.ηBar d) ^ 4
def CentredGrowthBound (σ : TupleFunctional) (m : ℕ) (c C κ : ℝ) : Prop :=
  ∃ T, TestSpaces.IsSchwingerFamily (TestSpaces.centredPart (evalOnMap σ)) T ∧
    ∀ n, 1 ≤ n → ∀ φ : flatSchwartzSet n,
      ‖T n φ‖ ≤ c * C ^ n * (n.factorial : ℝ) ^ κ * (weightedSeminorm (m * n) φ.1).toReal
def TwoPointPositive (ϑ : ℝ) (C : ConditionConstants) (σ : TupleFunctional) : Prop :=
  ∀ d ∈ Ioc (0 : ℝ) C.d₀, ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ →
    ContDiff ℝ 1 f → ContDiff ℝ 1 h → ∃ X : SepTupleOfCard 2, X.1 = ![f, h] ∧ 0 < connectedFn σ X
def InheritanceTheorem : Prop :=
  (∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (M ϑ : ℝ) (K : ℕ+ → ℕ+)
      (ρ ν : ConfigMeasures L K) (σ : TupleFunctional),
      (∀ k, IsProbabilityMeasure (ρ k)) → IsRepresentativeLimit ρ ν σ →
      CumulantsAreLimits ρ ν σ ∧
        TestSpaces.centredOfCumulants (cumulantFamilyOf σ) = TestSpaces.centredPart (evalOnMap σ) ∧
        (∀ C : ConditionConstants, StatesPerBallBounds M C ρ → PerBallBoundsAt M C σ) ∧
        (∀ c₁ : ℝ → ℝ, StatesOnePointTransfer M c₁ ρ ν →
          OnePointBounded M c₁ σ ∧
            ∀ c : ℝ, 0 ≤ c₁ 1 → IsOnePointCoefficient σ c →
              |c| ≤ c₁ 1 * sInf (sharpNormR4 M '' unitIntegralTestFunctions)) ∧
        ∀ C : ConditionConstants, StatesObeyTwoPointLaw ϑ C ρ → TwoPointLawHoldsAt ϑ C σ) ∧
    (∀ (C : ConditionConstants) (σ : TupleFunctional) (c cBound a Cstar Cσ : ℝ),
      TestSpaces.IsSepFunctional (evalOnMap σ) →
      IsOnePointCoefficient σ c → |c| ≤ cBound → 0 ≤ a → 0 ≤ Cstar → Cstar ≤ Cσ →
      0 ≤ C.κ → 4 < C.kE → CentredGrowthBound σ C.kE a Cstar C.κ →
      C.cE = 1 + a → C.CE = TestSpaces.onePointConst C.kE Cσ cBound →
      1 ≤ C.cE ∧ 0 ≤ C.CE ∧ GrowthBound C σ ∧
        TestSpaces.IsRegular (evalOnMap σ)) ∧
    ∀ (ϑ : ℝ) (C : ConditionConstants) (σ : TupleFunctional),
      ϑ ∈ Ioc (0 : ℝ) 1 → C.d₀ < 1 → (∀ d ∈ Ioc (0 : ℝ) C.d₀, C.ηBar d ∈ Icc (0 : ℝ) (1 / 3)) →
      TwoPointLawHoldsAt ϑ C σ → TwoPointPositive ϑ C σ
end GibbsLimitInheritance
end YangMills.Construction.SystemsWithFiveBounds
end
