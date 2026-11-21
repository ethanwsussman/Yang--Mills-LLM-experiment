import YangMills.Construction.ReflectionPositivity.CommonSetsForAMirrorThatMoves
import YangMills.Construction.ReflectionPositivity.InstancesOfTheInequalityAtAMirror
import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import YangMills.Construction.ReflectionPositivity.SharpNormAndModulusOfAFunctionOfClassC1
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.DenseMirrors
open Ambient
section
variable {D : MirrorData} {E : Ambient}
def ElementsInDistinctSets {q : ℕ} (A : Fin q → Set (E.Point D)) (h : FnList D E) : Prop :=
  ∃ ι : Fin h.length → Fin q, Function.Injective (A ∘ ι) ∧
    ∀ i, MovingMirrorSets.SupportedOn D E (A (ι i)) (h.get i)
def SeparatedCompactBound (M : ScaleParam) (T : FunctionalFamily D E) : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ A : Fin q → Set (E.Point D),
    (∀ l, MetricNotions.IsCompactWrt (metric D E) (A l)) →
    (∀ l l', l ≠ l' → 0 < setDist D E (A l) (A l')) →
    ∃ C : ℕ → ℝ, (∀ n, 2 ≤ n → n ≤ q → 0 ≤ C n) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n), n ≤ q → ∀ h : separatedN D E n,
        ElementsInDistinctSets A h.1 →
          |T n hn h| ≤ C n * (h.1.map (normSharp D M E)).prod
def InstanceOnUpperSide {μ : Fin 4} {c : ℝ} (I : (CoordMirror.mk μ c).PositivityInstance D E)
    (c' : ℝ) : Prop :=
  I.suppUnion ⊆ (CoordMirror.mk μ c').upperSide D E ∧
    ∀ i, (I.tuples i).1 ∈ separatedWithin D E ((CoordMirror.mk μ c').upperSide D E)
end
def InstancesStayUpper (D : MirrorData) (E : Ambient) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ I : (CoordMirror.mk μ c).PositivityInstance D E,
    (∀ c' : ℝ, ENNReal.ofReal |c' - c| < I.distToMirror →
      InstanceOnUpperSide I c') ∧
    (E = euclidean → ∀ c' : ℝ, c' ≤ c → InstanceOnUpperSide I c')
def CenteredContinuousInHeight {D : MirrorData} {E : Ambient}
    (T : FunctionalFamily D E) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ X Y : separatedWithin D E ((CoordMirror.mk μ c).upperSide D E),
    (∀ c' : ℝ, 2 * |c' - c| ≤ MovingMirrorSets.margin D E μ c X.1 Y.1 →
      (CoordMirror.mk μ c').reflectAppend D E X.1 Y.1 ∈ separatedAll D E) ∧
    Tendsto
      (fun c' : ℝ => evalOrZero (FunctionalFamily.centeredFunctional T)
        ((CoordMirror.mk μ c').reflectAppend D E X.1 Y.1))
      (𝓝 c)
      (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T)
        ((CoordMirror.mk μ c).reflectAppend D E X.1 Y.1)))
def ContinuityInHeight : Prop :=
  ∀ (D : MirrorData) (E : Ambient) (S : LatticeDataSeq D E) (T : FunctionalFamily D E),
    S.TendsToFamily T → ∀ M : ScaleParam, SeparatedCompactBound M T →
      ∀ (μ : Fin 4) (c : ℝ),
        InstancesStayUpper D E μ c ∧
        CenteredContinuousInHeight T μ c ∧
        ∀ I : (CoordMirror.mk μ c).PositivityInstance D E,
          I.HoldsReal (FunctionalFamily.centeredFunctional T)
end YangMills.Construction.ReflectionPositivity.AxisMirror.DenseMirrors
end
