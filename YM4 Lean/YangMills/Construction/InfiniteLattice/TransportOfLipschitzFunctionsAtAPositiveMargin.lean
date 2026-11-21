import YangMills.Construction.InfiniteLattice.TransportAtAPositiveMarginAndTheCoveringOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LipschitzPeriodization
def TsupportCompactInBall (r : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  IsCompact (tsupport f) ∧ tsupport f ⊆ SourcesAndGluing.ballR4 r
def ProjIsometricOnBall (ℓ r : ℝ) : Prop :=
  (∀ x ∈ SourcesAndGluing.ballR4 r, ∀ y ∈ SourcesAndGluing.ballR4 r,
      TorusMetric.torusEuclidNorm (TorusMetric.torusProj ℓ x - TorusMetric.torusProj ℓ y) =
        TorusMetric.euclidNormVec (x - y)) ∧
    InjOn (TorusMetric.torusProj ℓ) (SourcesAndGluing.ballR4 r)
def PeriodizeEqPeriodicSum (ℓ r : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ x, TestFunctions.periodize ℓ f (TorusMetric.torusProj ℓ x) =
      ∑' k : Fin 4 → ℤ, f (x + TestFunctions.latticeTranslate ℓ k)) ∧
    (∀ x, {k : Fin 4 → ℤ | f (x + TestFunctions.latticeTranslate ℓ k) ≠ 0}.Subsingleton) ∧
    ∀ x ∈ SourcesAndGluing.ballR4 r, TestFunctions.periodize ℓ f (TorusMetric.torusProj ℓ x) = f x
def PeriodizeLinear {L : ℕ} (c : ExpandingTori.PeriodizationMargin L) (ℓ r : ℝ)
    (f g : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ s t : ℝ, InfiniteLattice.MarginPeriodization.IsPeriodizableAtRadius c ℓ r (s • f + t • g) ∧
    TestFunctions.periodize ℓ (s • f + t • g) =
      s • TestFunctions.periodize ℓ f + t • TestFunctions.periodize ℓ g
def PeriodizeIndependentOfRadius {L : ℕ} (c : ExpandingTori.PeriodizationMargin L) (ℓ : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ c.radius ℓ → tsupport f ⊆ SourcesAndGluing.ballR4 ρ →
    InfiniteLattice.MarginPeriodization.IsPeriodizableAtRadius c ℓ ρ f ∧
      ∀ u : TorusMetric.Torus4 ℓ → ℝ,
        (∀ x, u (TorusMetric.torusProj ℓ x) =
          ∑' k : Fin 4 → ℤ, f (x + TestFunctions.latticeTranslate ℓ k)) →
          u = TestFunctions.periodize ℓ f
def PeriodizePreservesNorms (ℓ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  TestFunctions.IsBoundedFun (TestFunctions.periodize ℓ f) ∧
    TestFunctions.uniformNorm (TestFunctions.periodize ℓ f) = TestFunctions.uniformNorm f ∧
    TestFunctions.IsLipschitzFor (TestFunctions.euclidDistTorus (ℓ := ℓ))
      (TestFunctions.periodize ℓ f) ∧
    TestFunctions.lipConstTorus (TestFunctions.periodize ℓ f) = TestFunctions.lipConstR4 f ∧
    ∀ M : ℝ, TestFunctions.sharpNormTorus M (TestFunctions.periodize ℓ f) =
      TestFunctions.sharpNormR4 M f
def PeriodizePreservesC1 (ℓ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  TestFunctions.IsC1R4 f → TestFunctions.IsC1Torus (TestFunctions.periodize ℓ f)
def PeriodizeSupport (ℓ : ℝ) (f g : (Fin 4 → ℝ) → ℝ) : Prop :=
  tsupport (TestFunctions.periodize ℓ f) = TorusMetric.torusProj ℓ '' tsupport f ∧
    IsCompact (tsupport (TestFunctions.periodize ℓ f)) ∧
    TorusMetric.setEuclidDist (tsupport (TestFunctions.periodize ℓ f))
        (tsupport (TestFunctions.periodize ℓ g)) =
      TestFunctions.setDistR4 (tsupport f) (tsupport g)
def RadiusMonotoneInSide {L : ℕ} (c : ExpandingTori.PeriodizationMargin L) (r : ℝ) : Prop :=
  ∀ ℓ' ∈ PeriodicLattice.torusSides L, 4 * (r + c.value) ≤ ℓ' → r ≤ c.radius ℓ'
def Statement : Prop :=
  ∀ (D : Conventions.StandingParameters) (c : ExpandingTori.PeriodizationMargin D.L) (r : ℝ)
    (f g : (Fin 4 → ℝ) → ℝ),
    0 < r → r ≤ c.radius D.side →
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 g →
    TsupportCompactInBall r f → TsupportCompactInBall r g →
    ProjIsometricOnBall D.side r ∧
      PeriodizeEqPeriodicSum D.side r f ∧
      PeriodizeLinear c D.side r f g ∧
      PeriodizeIndependentOfRadius c D.side f ∧
      PeriodizePreservesNorms D.side f ∧
      PeriodizePreservesC1 D.side f ∧
      PeriodizeSupport D.side f g ∧
      RadiusMonotoneInSide c r
end YangMills.Construction.LipschitzPeriodization
end
