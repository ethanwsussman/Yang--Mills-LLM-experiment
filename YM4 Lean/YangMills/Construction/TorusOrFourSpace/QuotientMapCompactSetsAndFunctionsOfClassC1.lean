import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsOfACompactSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1
variable (P : Params) (K : Kind)
def QuotDistIsMetricWithLifts : Prop :=
  (∀ p p' : K.Pt P, 0 ≤ quotDist P K p p') ∧
  (∀ p p' : K.Pt P, quotDist P K p p' = 0 ↔ p = p') ∧
  (∀ p p' : K.Pt P, quotDist P K p p' = quotDist P K p' p) ∧
  (∀ p p' p'' : K.Pt P, quotDist P K p p'' ≤ quotDist P K p p' + quotDist P K p' p'') ∧
  (∀ v v' : Fin 4 → ℝ, quotDist P K (K.quotMap P v) (K.quotMap P v') ≤
    TorusMetric.euclidNormVec (v - v')) ∧
  (∀ (p p' : K.Pt P) (v : Fin 4 → ℝ), IsLift P K p v →
    ∃ v', IsLift P K p' v' ∧ TorusMetric.euclidNormVec (v - v') = quotDist P K p p')
def QuotMapContinuousOpen : Prop :=
  MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 (quotDist P K) (K.quotMap P) ∧
  (∀ U : Set (Fin 4 → ℝ), MetricNotions.IsOpenWrt TestFunctions.euclidDistR4 U →
    IsOpenQ P K (K.quotMap P '' U)) ∧
  (∀ g : K.Pt P → ℝ, IsContinuousQ P K g ↔
    MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 dist (g ∘ K.quotMap P))
def TorusCompact : Prop := IsCompactQ P Kind.torus Set.univ
def CompactSetsThickenings : Prop :=
  (∀ A A' : Set (K.Pt P), IsCompactQ P K A → IsCompactQ P K A' → Disjoint A A' →
    0 < setInfDist P K A A') ∧
  (∀ (A : Set (K.Pt P)) (hA : IsCompactQ P K A) (r : ℝ) (hr : 0 < r),
    IsOpenQ P K (openThickening P K A hA r hr) ∧ A ⊆ openThickening P K A hA r hr) ∧
  (∃ h : IsCompactQ P K (∅ : Set (K.Pt P)), ∀ (r : ℝ) (hr : 0 < r),
    openThickening P K ∅ h r hr = ∅) ∧
  (∀ (A A' : Set (K.Pt P)) (hA : IsCompactQ P K A) (hA' : IsCompactQ P K A')
    (r : ℝ) (hr : 0 < r), ENNReal.ofReal (2 * r) ≤ setInfDist P K A A' →
      openThickening P K A hA r hr ∩ openThickening P K A' hA' r hr = ∅)
def CompactSupportC1Facts : Prop :=
  ∀ g : K.Pt P → ℝ, g ∈ c1Set P K → IsCompactQ P K (supportQ P K g) →
    (∀ μ : Fin 4, IsContinuousQ P K (partialDeriv P K μ g)) ∧
    (∀ p, p ∉ supportQ P K g → gradVec P K g p = 0) ∧
    euclidC1Norm P K g < ∞ ∧
    (∀ p p' : K.Pt P, |g p - g p'| ≤
      (vecSupNormQ P K (gradVec P K g)).toReal * quotDist P K p p') ∧
    IsLipschitzQ P K g ∧
    ENNReal.ofReal (lipConstQ P K g) = vecSupNormQ P K (gradVec P K g) ∧
    sharpNormQ P K g =
      max (supNormQ P K g) (ENNReal.ofReal (40 * P.M) * vecSupNormQ P K (gradVec P K g)) ∧
    sharpNormQ P K g ≤ ENNReal.ofReal (40 * P.M) * euclidC1Norm P K g
def Claim : Prop :=
  ∀ (P : Params) (K : Kind),
    QuotDistIsMetricWithLifts P K ∧ QuotMapContinuousOpen P K ∧ TorusCompact P ∧
      CompactSetsThickenings P K ∧ CompactSupportC1Facts P K
end YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1
