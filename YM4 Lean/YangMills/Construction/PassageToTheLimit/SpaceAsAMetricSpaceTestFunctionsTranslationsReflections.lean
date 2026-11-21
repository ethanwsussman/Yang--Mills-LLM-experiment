import YangMills.Construction.Functions.FamilyTopology
import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace AmbientMetric
variable (s : Conventions.StandingParameters) (E : Ambient)
def IsDistPreserving (t : E.Carrier s → E.Carrier s) : Prop :=
  ∀ x y, E.pointDist s (t x) (t y) = E.pointDist s x y
def EuclidDistFacts : Prop :=
  (∀ x y : Fin 4 → ℝ,
    IsLeast ((fun γ => TorusMetric.euclidNormVec (x - y - γ)) ''
        (E.periodGroup s : Set (Fin 4 → ℝ)))
      (E.pointDist s (E.proj s x) (E.proj s y)) ∧
    E.pointDist s (E.proj s x) (E.proj s y) ≤ TorusMetric.euclidNormVec (x - y)) ∧
  FamilyTopology.IsMetricFunction (E.pointDist s) ∧
  (∀ x y z : E.Carrier s, E.pointDist s (x + z) (y + z) = E.pointDist s x y) ∧
  (∀ (x y : E.Carrier s) (u : Fin 4 → ℝ), E.IsLiftOf s x u →
    ∃ w : Fin 4 → ℝ, E.IsLiftOf s y w ∧ TorusMetric.euclidNormVec (u - w) = E.pointDist s x y) ∧
  MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 (E.pointDist s) (E.proj s)
def CompactAndIsometryFacts : Prop :=
  (∀ S S' : Set (E.Carrier s), E.IsCompactSubset s S → E.IsCompactSubset s S' → Disjoint S S' →
    E.PositivelySeparated s S S') ∧
  ∀ t : E.Carrier s ≃ E.Carrier s, IsDistPreserving s E t →
    E.IsContinuousSelf s t ∧ E.IsContinuousSelf s t.symm ∧
    ∀ (Z : Type) [Zero Z] (f : E.Carrier s → Z), E.closedSupport s (f ∘ t) = t ⁻¹' E.closedSupport s f
def C1CompactFacts : Prop :=
  ∀ g ∈ E.c1Compact s,
    E.IsContinuousInto s g ∧ TestFunctions.IsBoundedFun g ∧
    MetricNotions.IsContinuousWrt (E.pointDist s) TestFunctions.euclidDistR4 (E.grad s g) ∧
    (∃ C : ℝ, ∀ x, TorusMetric.euclidNormVec (E.grad s g x) ≤ C) ∧
    (∀ x, x ∉ E.closedSupport s g → E.grad s g x = 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y, E.pointDist s x y ≤ δ →
      TorusMetric.euclidNormVec (E.grad s g x - E.grad s g y) ≤ ε) ∧
    E.IsLip s g ∧
    ENNReal.ofReal (E.lipConst s g) ≤ E.gradSup s g ∧ E.gradSup s g < ∞
def LinearCombinationFacts : Prop :=
  ∀ f ∈ E.c1Compact s, ∀ g ∈ E.c1Compact s, ∀ (a b : ℝ) (ψ : E.Carrier s → ℝ),
    E.IsC1 s ψ →
      (fun x => a * f x + b * g x) ∈ E.c1Compact s ∧
      E.grad s (fun x => a * f x + b * g x) = a • E.grad s f + b • E.grad s g ∧
      E.closedSupport s (fun x => a * f x + b * g x) ⊆ E.closedSupport s f ∪ E.closedSupport s g ∧
      (fun x => ψ x * f x) ∈ E.c1Compact s ∧
      E.closedSupport s (fun x => ψ x * f x) ⊆ E.closedSupport s ψ ∩ E.closedSupport s f
def TranslationFacts : Prop :=
  ∀ v : E.Carrier s,
    Function.Bijective (fun x : E.Carrier s => x + v) ∧
    IsDistPreserving s E (fun x => x + v) ∧
    (∀ (Z : Type) [Zero Z] (f : E.Carrier s → Z),
      E.closedSupport s (E.translateFun s v f) = E.translateSet s (E.closedSupport s f) v) ∧
    ∀ f ∈ E.c1Compact s,
      E.translateFun s v f ∈ E.c1Compact s ∧
      ∀ x, E.grad s (E.translateFun s v f) x = E.grad s f (x - v)
def ReflectionFacts : Prop :=
  ∀ (μ : Fin 4) (c : ℝ),
    Function.Bijective (E.reflect s μ c) ∧
    IsDistPreserving s E (E.reflect s μ c) ∧
    E.reflect s μ c ∘ E.reflect s μ c = id ∧
    ∀ f ∈ E.c1Compact s,
      E.reflectFun s μ c f ∈ E.c1Compact s ∧
      ∀ x, E.grad s (E.reflectFun s μ c f) x =
        (coordFlipMatrix μ).mulVec (E.grad s f (E.reflect s μ c x))
def PeriodicReflectHalfPeriod : Prop :=
  ∀ (μ : Fin 4) (c c' : ℝ), c' - c ∈ multiplesOf (s.side / 2) →
    Ambient.periodic.reflect s μ c' = Ambient.periodic.reflect s μ c
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient),
    EuclidDistFacts s E ∧
    CompactAndIsometryFacts s E ∧
    C1CompactFacts s E ∧
    LinearCombinationFacts s E ∧
    TranslationFacts s E ∧
    ReflectionFacts s E ∧
    PeriodicReflectHalfPeriod s
end AmbientMetric
end LimitSpaces
end YangMills.Construction
end
