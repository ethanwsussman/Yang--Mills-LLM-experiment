import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace Ambient
variable (s : Conventions.StandingParameters) (E : Ambient) {Z : Type*}
def listSupport [Zero Z] (X : List (E.Carrier s → Z)) : Set (E.Carrier s) :=
  ⋃ f ∈ X, E.closedSupport s f
theorem listSupport_ofFn [Zero Z] {n : ℕ} (f : Fin n → E.Carrier s → Z) :
    E.listSupport s (List.ofFn f) = ⋃ i, E.closedSupport s (f i) := by
  ext x
  simp [listSupport]
def listGap : (E : Ambient) → List (E.Carrier s → ℝ) → ℝ≥0∞
  | periodic, X => ReflectionPositivity.TorusTuples.gap (s := s) X
  | euclidean, X =>
    (Finset.univ.offDiag : Finset (Fin X.length × Fin X.length)).inf fun p =>
      euclidean.infSetDist s (euclidean.closedSupport s (X.get p.1))
        (euclidean.closedSupport s (X.get p.2))
end Ambient
section Periodization
variable (s : Conventions.StandingParameters) {Z : Type*}
def periodizeFun [AddCommMonoid Z] [TopologicalSpace Z] (f : (Fin 4 → ℝ) → Z) : s.Torus → Z :=
  TestFunctions.periodize s.side f
def FitsInTorus [Zero Z] (X : List ((Fin 4 → ℝ) → Z)) : Prop :=
  (∀ f ∈ X, Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f)) ∧
    TestFunctions.HasDiameterLE (Ambient.euclidean.listSupport s X) (s.side / 2)
def periodizeList [AddCommMonoid Z] [TopologicalSpace Z] (X : List ((Fin 4 → ℝ) → Z)) :
    List (s.Torus → Z) :=
  X.map (periodizeFun s)
end Periodization
end LimitSpaces
namespace ReflectionPositivity.AxisMirror.Ambient
variable (D : MirrorData) {𝕜 : Type*} [RCLike 𝕜] {Z : Type*}
def listSupport (E : Ambient) (X : List (E.Point D → 𝕜)) : Set (E.Point D) :=
  ⋃ f ∈ X, closedSupport D E f
def listGap : (E : Ambient) → FnList D E → ℝ≥0∞
  | torus, X => LimitSpaces.Ambient.periodic.listGap D.toStandingParameters X
  | euclidean, X => LimitSpaces.Ambient.euclidean.listGap D.toStandingParameters X
end ReflectionPositivity.AxisMirror.Ambient
end YangMills.Construction
