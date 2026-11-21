import YangMills.Construction.Functions.FamilyTopology
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace TorusMetricSpace
variable (D : MirrorData)
def IsBorelFn {E : Type*} [TopologicalSpace E] (f : D.Torus → E) : Prop :=
  ∀ B : Set E, MeasurableSet[borel E] B → D.IsBorel (f ⁻¹' B)
def CompactMetricTorus : Prop :=
  (∀ x y : Fin 4 → ℝ,
    IsLeast
      (range fun k : Fin 4 → ℤ =>
        YangMills.Construction.TorusMetric.euclidNormVec
          (x - y - YangMills.Construction.TestFunctions.latticeTranslate D.side k))
      (D.torusDist (D.proj x) (D.proj y))) ∧
  YangMills.Construction.FamilyTopology.IsMetricFunction D.torusDist ∧
  (∀ x y : Fin 4 → ℝ,
    D.torusDist (D.proj x) (D.proj y) ≤ YangMills.Construction.TorusMetric.euclidNormVec (x - y)) ∧
  YangMills.Construction.MetricNotions.IsContinuousWrt
    YangMills.Construction.TestFunctions.euclidDistR4 D.torusDist D.proj ∧
  D.IsCompactSubset univ
def LipschitzBoundedBorel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (f : D.Torus → E),
    YangMills.Construction.TestFunctions.IsLipschitzFor D.torusDist f →
      D.IsContinuousFn (fun u v : E => ‖u - v‖) f ∧
        YangMills.Construction.TestFunctions.IsBoundedFun f ∧ IsBorelFn D f
def DisjointSuppSeparated : Prop :=
  (∀ (E : Type) [NormedAddCommGroup E] (q : ℕ) (h : Fin q → D.Torus → E), 1 ≤ q →
    MirrorData.PairwiseDisjointSupp (D := D) h →
      ∃ d : ℝ, YangMills.Construction.TestFunctions.HasSeparatedSupportsTorus h d) ∧
  ∀ (q : ℕ) (h : Fin q → D.Torus → ℝ), 2 ≤ q →
    MirrorData.PairwiseDisjointSupp (D := D) h →
    (∀ l, YangMills.Construction.TestFunctions.IsLipschitzFor D.torusDist (h l)) →
      YangMills.Construction.SchwingerFunctions.IsTorusTestFamily h ∧
        ∀ J : Finset (Fin q), 2 ≤ J.card →
          YangMills.Construction.SchwingerFunctions.IsTorusTestFamily
            fun k : Fin J.card => h (J.orderEmbOfFin rfl k)
def IsometryActionOnFunctions : Prop :=
  ∀ s : D.Torus → D.Torus, Function.Bijective s → D.IsDistPreserving s →
    D.IsHomeo s ∧
    (∀ (E : Type) [NormedAddCommGroup E] (h : D.Torus → E),
      D.supp (h ∘ s) = s ⁻¹' D.supp h ∧
      (YangMills.Construction.TestFunctions.IsBoundedFun h →
        YangMills.Construction.TestFunctions.IsBoundedFun (h ∘ s)) ∧
      (IsBorelFn D h → IsBorelFn D (h ∘ s)) ∧
      (YangMills.Construction.TestFunctions.IsLipschitzFor D.torusDist h →
        YangMills.Construction.TestFunctions.IsLipschitzFor D.torusDist (h ∘ s))) ∧
    (∀ h : D.Torus → ℂ, (∀ u, (h u).im = 0) → ∀ u, ((h ∘ s) u).im = 0) ∧
    ∀ (E : Type) [NormedAddCommGroup E] (q : ℕ) (h : Fin q → D.Torus → E),
      (MirrorData.PairwiseDisjointSupp (D := D) h →
        MirrorData.PairwiseDisjointSupp (D := D) fun l => h l ∘ s) ∧
      ∀ d : ℝ, YangMills.Construction.TestFunctions.HasSeparatedSupportsTorus h d →
        YangMills.Construction.TestFunctions.HasSeparatedSupportsTorus (fun l => h l ∘ s) d
def MetricTorusFacts : Prop :=
  ∀ D : MirrorData, CompactMetricTorus D ∧ LipschitzBoundedBorel D ∧
    DisjointSuppSeparated D ∧ IsometryActionOnFunctions D
end TorusMetricSpace
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
