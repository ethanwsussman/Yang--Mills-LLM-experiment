import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.ReflectionPositivity.SupportsTranslationsSeparationAndTransportOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirrorSets
variable (D : MirrorData) (E : Ambient)
def SupportedOn : (E : Ambient) → Set (E.Point D) → (E.Point D → ℝ) → Prop
  | .torus, A, f => LimitSpaces.Ambient.periodic.SupportedWithin D.toStandingParameters A f
  | .euclidean, A, f => LimitSpaces.Ambient.euclidean.SupportedWithin D.toStandingParameters A f
def distToMirror (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E) : ℝ≥0∞ :=
  Ambient.setDist D E (Ambient.listSupport D E X ∪ Ambient.listSupport D E Y)
    (CoordMirror.carrier D ⟨μ, c⟩ E)
def margin (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E) : ℝ :=
  (min 1 (min (distToMirror D E μ c X Y) (Ambient.listGap D E X))).toReal / 3
def imageNbhd (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E) (f : E.Point D → ℝ) :
    Set (E.Point D) :=
  {x | Ambient.setDist D E {x} (CoordMirror.reflect D ⟨μ, c⟩ E '' Ambient.closedSupport D E f) ≤
    ENNReal.ofReal (margin D E μ c X Y)}
def sharedSets (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E) : List (Set (E.Point D)) :=
  X.map (imageNbhd D E μ c X Y) ++ Y.map (Ambient.closedSupport D E)
def SharedSetsCompactSeparated (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E) : Prop :=
  0 < margin D E μ c X Y ∧ margin D E μ c X Y ≤ 1 / 3 ∧
    (∀ A ∈ sharedSets D E μ c X Y, MetricNotions.IsCompactWrt (Ambient.metric D E) A) ∧
    0 < min (ENNReal.ofReal (margin D E μ c X Y)) (Ambient.listGap D E Y) ∧
    ∀ l l' : Fin (sharedSets D E μ c X Y).length, l ≠ l' →
      min (ENNReal.ofReal (margin D E μ c X Y)) (Ambient.listGap D E Y) ≤
        Ambient.setDist D E ((sharedSets D E μ c X Y).get l) ((sharedSets D E μ c X Y).get l')
def MovedListInSharedSets (μ : Fin 4) (c c' : ℝ) (X Y : Ambient.FnList D E) : Prop :=
  List.Forall₂ (fun g A => SupportedOn D E A g) (CoordMirror.reflectAppend D ⟨μ, c'⟩ E X Y)
      (sharedSets D E μ c X Y) ∧
    CoordMirror.reflectAppend D ⟨μ, c'⟩ E X Y ∈
      Ambient.separatedN D E (X.length + Y.length)
def withCutoffCoupling (K' : ℕ+) (β' : ℝ) (hβ : 0 < β') : MirrorData :=
  { D with K := K', β := β', β_pos := hβ }
def SharedSetsProperties : Prop :=
  ∀ (D : MirrorData) (E : Ambient) (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E),
    X ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
    Y ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
    SharedSetsCompactSeparated D E μ c X Y ∧
      (∀ c' : ℝ, 2 * |c' - c| ≤ margin D E μ c X Y → MovedListInSharedSets D E μ c c' X Y) ∧
      ∀ (K' : ℕ+) (β' : ℝ) (hβ : 0 < β'),
        margin (withCutoffCoupling D K' β' hβ) E μ c X Y = margin D E μ c X Y ∧
          sharedSets (withCutoffCoupling D K' β' hβ) E μ c X Y = sharedSets D E μ c X Y
end YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirrorSets
end
