import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open scoped ComplexConjugate Matrix
namespace NormalFamilies
open InfiniteLattice
def ReflectionLinearPart.Statement : Prop :=
  ∀ (n : AmbientSpace) (hn : n ∈ normalSet) (c c' : ℝ) (hc : IsAllowedLevel 1 n c)
    (hc' : IsAllowedLevel 1 n c') (v : LatticePoint 1),
    let P : NormalLevelPair 1 := ⟨n, hn, c, hc⟩
    let P' : NormalLevelPair 1 := ⟨n, hn, c', hc'⟩
    (∀ x y : AmbientSpace, TorusMetric.euclidNormVec (reflectAcross n c x - reflectAcross n c y) =
      TorusMetric.euclidNormVec (x - y)) ∧
    reflectAcross n c '' (latticeSubgroup 1 : Set AmbientSpace) = latticeSubgroup 1 ∧
    P.reflectSymmetry.toFun = reflectAcross n c ∧
    IsAllowedLevel 1 n 0 ∧
    IsLinearMap ℝ (linearReflect n) ∧
    (∀ x : AmbientSpace, n ⬝ᵥ x = 0 → linearReflect n x = x) ∧
    linearReflect n n = -n ∧
    (∀ x : AmbientSpace, reflectAcross n c (x + (v : AmbientSpace)) =
      reflectAcross n c x + linearReflect n (v : AmbientSpace)) ∧
    (∃ w : LatticePoint 1, (w : AmbientSpace) = linearReflect n (v : AmbientSpace) ∧
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        P.reflectObservable ((shift v).actOn F) =
          (shift w).actOn (P.reflectObservable F)) ∧
    reflectAcross n c ∘ reflectAcross n c = id ∧
    (∀ x : AmbientSpace, n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x) ∧
    reflectAcross n c' ∘ reflectAcross n c = translateBy ((2 * (c' - c)) • dualVector n) ∧
    translateBy (v : AmbientSpace) ∘ reflectAcross n c ∘ translateBy (-(v : AmbientSpace)) =
      reflectAcross n (c + n ⬝ᵥ (v : AmbientSpace)) ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → P.reflectObservable (P.reflectObservable F) = F) ∧
    (∃ w : LatticePoint 1, (w : AmbientSpace) = (2 * (c' - c)) • dualVector n ∧
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        P'.reflectObservable (P.reflectObservable F) = (shift w).actOn F) ∧
    (∃ h : IsAllowedLevel 1 n (c + n ⬝ᵥ (v : AmbientSpace)),
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        (shift v).actOn (P.reflectObservable ((shift (-v)).actOn F)) =
          NormalLevelPair.reflectObservable ⟨n, hn, c + n ⬝ᵥ (v : AmbientSpace), h⟩ F) ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsBoundedObservable (P.conjReflectObservable F)) ∧
    (∀ (α : ℂ) (F H : GaugeField 1 → ℂ), IsBoundedObservable F → IsBoundedObservable H →
      P.conjReflectObservable (α • F + H) =
        conj α • P.conjReflectObservable F + P.conjReflectObservable H) ∧
    (∀ F H : GaugeField 1 → ℂ, IsBoundedObservable F → IsBoundedObservable H →
      P.conjReflectObservable (F * H) = P.conjReflectObservable F * P.conjReflectObservable H) ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      P.conjReflectObservable (P.conjReflectObservable F) = F) ∧
    P.conjReflectObservable '' regionObservables 1 {x | c ≤ n ⬝ᵥ x} =
      regionObservables 1 {x | n ⬝ᵥ x ≤ c} ∧
    P.conjReflectObservable '' regionObservables 1 {x | n ⬝ᵥ x ≤ c} =
      regionObservables 1 {x | c ≤ n ⬝ᵥ x}
end NormalFamilies
end YangMills.Construction
