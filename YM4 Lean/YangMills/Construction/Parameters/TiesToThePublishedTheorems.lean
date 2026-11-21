import YangMills.Construction.BackgroundField.BoundsOfTheSitePropagatorOnCoveringCubes
import YangMills.Construction.BackgroundField.NumbersOfTheMinimalOrbitsTheorem
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
abbrev gaugeFixingConstantsAt (L M R : ℕ) : BackgroundField.GaugeFixingConstants :=
  BackgroundField.gaugeFixingConstants L (Nat.log L M) (Nat.log L R)
def subcriticalB₃Pos (L : ℕ) : ℝ :=
  if 0 < (BackgroundField.PrescribedAverageProblem.subcriticalB₃AndFloors L).1 then
    (BackgroundField.PrescribedAverageProblem.subcriticalB₃AndFloors L).1 else 1
def subcriticalMinimizerConstantsAt (L M R : ℕ) :
    BackgroundField.PrescribedAverageProblem.MinimizerConstants :=
  Classical.epsilon
    (BackgroundField.PrescribedAverageProblem.AreMinimizerConstants
      BackgroundField.PrescribedAverageProblem.IsSubcriticalExponent L (Nat.log L M) (Nat.log L R)
      (subcriticalB₃Pos L))
abbrev greenBoundMinimizerConstantsAt (L M R : ℕ) :
    BackgroundField.PrescribedAverageProblem.MinimizerConstants :=
  BackgroundField.GreenBoundMinimizers.minimizerConstants L (Nat.log L M) (Nat.log L R)
def GaugeFixingConstantsValid (L M R : ℕ) : Prop :=
  BackgroundField.AreUniqueGaugeFixingConstants L (Nat.log L M) (Nat.log L R)
    (gaugeFixingConstantsAt L M R)
def SubcriticalMinimizerConstantsValid (L M R : ℕ) : Prop :=
  BackgroundField.PrescribedAverageProblem.AreMinimizerConstants
    BackgroundField.PrescribedAverageProblem.IsSubcriticalExponent L (Nat.log L M) (Nat.log L R)
    (subcriticalB₃Pos L) (subcriticalMinimizerConstantsAt L M R)
def GreenBoundMinimizerConstantsValid (L M R : ℕ) : Prop :=
  BackgroundField.GreenBoundMinimizers.ServingConstants L (Nat.log L M) (Nat.log L R)
    (BackgroundField.PrescribedAverageProblem.subcriticalB₃ L) (greenBoundMinimizerConstantsAt L M R)
structure IsBlockAndGapScale (L M R : ℕ) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  block_pow : IsPositivePowerOf L M
  gap_pow : IsPositivePowerOf L R
structure MatchesPublishedConstants (T : DerivedConstants) (N : ExternalConstants) : Prop where
  M₁Thr_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    T.M₁Thr L = (BackgroundField.chosenSiteGreenConstants L).M₁
  δ₀Ring_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    T.δ₀Ring L = min 1 (BackgroundField.chosenSiteGreenConstants L).δ₀
  B₀_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    T.B₀ L = (BackgroundField.chosenSiteGreenConstants L).B₀
  a₀Ring_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∃ c : ℝ, 10 ≤ c ∧ T.a₀Ring L = (BackgroundField.chosenSiteGreenConstants L).a₀ c
  B₁_eq : ∀ L M R : ℕ, IsBlockAndGapScale L M R → GaugeFixingConstantsValid L M R →
    T.B₁ L M R = BackgroundField.gaugeFixingB₁ L M R
  c₁_eq : ∀ L M R : ℕ, IsBlockAndGapScale L M R → GaugeFixingConstantsValid L M R →
    T.c₁ L M R = BackgroundField.gaugeFixingC₁ L M R
  greenBoundB₃_le : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    BackgroundField.PrescribedAverageProblem.subcriticalB₃ L ≤ T.B₃ L
  subcriticalB₃Pos_le : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    subcriticalB₃Pos L ≤ T.B₃ L
  a₀_le : ∀ L M R : ℕ, IsBlockAndGapScale L M R → SubcriticalMinimizerConstantsValid L M R →
    T.a₀ L M R ≤ (subcriticalMinimizerConstantsAt L M R).a₀
  a₁_le : ∀ L M R : ℕ, IsBlockAndGapScale L M R → SubcriticalMinimizerConstantsValid L M R →
    T.a₁ L M R ≤ (subcriticalMinimizerConstantsAt L M R).a₁
  productFloor_le : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    BackgroundField.PrescribedAverageProblem.subcriticalProductFloor L ≤ N.productFloor L
  minimizer_holds : ∀ L M R : ℕ, IsBlockAndGapScale L M R → SubcriticalMinimizerConstantsValid L M R →
    ∀ B a a' : ℝ, T.B₃ L ≤ B → 0 < a → a ≤ T.a₀ L M R → 0 < a' → a' ≤ T.a₁ L M R → B * a' ≤ a →
      ∃ B₄ : ℝ → ℝ, (∀ β₀, 0 < B₄ β₀) ∧
        BackgroundField.PrescribedAverageProblem.MinimizerTheoremHolds
          BackgroundField.PrescribedAverageProblem.IsSubcriticalExponent L (Nat.log L M) (Nat.log L R)
          a a' B B₄
  a₀_le_greenBound : ∀ L M R : ℕ, IsBlockAndGapScale L M R →
    GreenBoundMinimizerConstantsValid L M R →
    T.a₀ L M R ≤ (greenBoundMinimizerConstantsAt L M R).a₀
  a₁_le_greenBound : ∀ L M R : ℕ, IsBlockAndGapScale L M R →
    GreenBoundMinimizerConstantsValid L M R →
    T.a₁ L M R ≤ (greenBoundMinimizerConstantsAt L M R).a₁
  greenBound_minimizer_holds : ∀ L M R : ℕ, IsBlockAndGapScale L M R →
    GreenBoundMinimizerConstantsValid L M R →
    ∀ B a a' : ℝ, T.B₃ L ≤ B → 0 < a → a ≤ T.a₀ L M R → 0 < a' → a' ≤ T.a₁ L M R → B * a' ≤ a →
      ∃ B₄ : ℝ → ℝ, (∀ β₀, 0 < B₄ β₀) ∧
        BackgroundField.GreenBoundMinimizers.ConclusionHoldsWith L (Nat.log L M) (Nat.log L R)
          a a' B B₄
end YangMills.Construction.ParameterChoice
end
