import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.WellPosedness
open YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.TorusMetric (euclidNormVec torusEuclidNorm torusProj)
variable (P : Params) (K : Kind)
def QuotMapSurjectiveHomWithKernel : Prop :=
  (∀ a b : Fin 4 → ℝ, K.quotMap P (a + b) = K.quotMap P a + K.quotMap P b) ∧
    Function.Surjective (K.quotMap P) ∧
    ∀ a : Fin 4 → ℝ, K.quotMap P a = 0 ↔ a ∈ K.periodGroup P
def ExistsLiftOfEachPoint : Prop := ∀ p : K.Pt P, ∃ a, IsLift P K p a
def SameLiftIffSubPeriod : Prop :=
  ∀ a b : Fin 4 → ℝ, (∃ p : K.Pt P, IsLift P K p a ∧ IsLift P K p b) ↔ a - b ∈ K.periodGroup P
def translateNorms (a b : Fin 4 → ℝ) : Set ℝ :=
  {t | ∃ g ∈ K.periodGroup P, t = euclidNormVec (a - b - g)}
def TranslateNormMinExists : Prop :=
  ∀ a b : Fin 4 → ℝ, ∃ t, IsLeast (translateNorms P K a b) t
def TranslateNormMinPeriodInvariant : Prop :=
  ∀ a b g : Fin 4 → ℝ, g ∈ K.periodGroup P → ∀ t : ℝ,
    (IsLeast (translateNorms P K (a + g) b) t ↔
      IsLeast (translateNorms P K a b) t) ∧
    (IsLeast (translateNorms P K a (b + g)) t ↔
      IsLeast (translateNorms P K a b) t)
def TranslateNormMinWellDefined : Prop :=
  ∀ p q : K.Pt P, ∃! t : ℝ, ∀ a b : Fin 4 → ℝ, IsLift P K p a → IsLift P K q b →
    IsLeast (translateNorms P K a b) t
def QuotDistEqMinTranslateNorm : Prop :=
  ∀ a b : Fin 4 → ℝ,
    IsLeast (translateNorms P K a b)
      (quotDist P K (K.quotMap P a) (K.quotMap P b))
def EuclideanQuotDistEqNorm : Prop :=
  ∀ p q : Fin 4 → ℝ, quotDist P Kind.euclidean p q = euclidNormVec (p - q)
def TorusQuotDistEqEuclid : Prop :=
  ∀ p q : P.Torus,
    quotDist P Kind.torus p q = torusEuclidNorm (p - q) ∧
      IsLeast (euclidNormVec '' (torusProj P.side ⁻¹' {p - q})) (quotDist P Kind.torus p q)
def PartialDerivDescends : Prop :=
  ∀ f : K.Pt P → ℝ, IsC1Fn P K f →
    IsGammaPeriodic P K (f ∘ K.quotMap P) ∧
      ∀ i : Fin 4,
        IsGammaPeriodic P K (TestFunctions.partialDerivR4 i (f ∘ K.quotMap P)) ∧
          (∃! g : K.Pt P → ℝ,
            g ∘ K.quotMap P = TestFunctions.partialDerivR4 i (f ∘ K.quotMap P)) ∧
          partialDeriv P K i f ∘ K.quotMap P =
            TestFunctions.partialDerivR4 i (f ∘ K.quotMap P)
def lipschitzBounds (f : K.Pt P → ℝ) : Set ℝ :=
  {L | 0 ≤ L ∧ ∀ p q : K.Pt P, |f p - f q| ≤ L * quotDist P K p q}
def LipConstIsLeastBound : Prop :=
  ∀ f : K.Pt P → ℝ, IsLipschitzQ P K f →
    (∃ L, IsLeast (lipschitzBounds P K f) L) ∧
      IsLeast (lipschitzBounds P K f) (lipConstQ P K f)
def WellPosed : Prop :=
  ∀ (P : Params) (K : Kind),
    QuotMapSurjectiveHomWithKernel P K ∧
    ExistsLiftOfEachPoint P K ∧
    SameLiftIffSubPeriod P K ∧
    TranslateNormMinExists P K ∧
    TranslateNormMinPeriodInvariant P K ∧
    TranslateNormMinWellDefined P K ∧
    QuotDistEqMinTranslateNorm P K ∧
    EuclideanQuotDistEqNorm P ∧
    TorusQuotDistEqEuclid P ∧
    PartialDerivDescends P K ∧
    1 ≤ 40 * P.M ∧
    LipConstIsLeastBound P K
end YangMills.Construction.PeriodicSpace.WellPosedness
