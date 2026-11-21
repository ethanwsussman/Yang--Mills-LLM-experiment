import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
def ReflectionIdentities.Statement : Prop :=
  ∀ (n : AmbientSpace) (hn : n ∈ normalSet) (c c' : ℝ) (hc : IsAllowedLevel 1 n c)
    (hc' : IsAllowedLevel 1 n c') (v : LatticePoint 1),
    let P : NormalLevelPair 1 := ⟨n, hn, c, hc⟩
    let P' : NormalLevelPair 1 := ⟨n, hn, c', hc'⟩
    (∀ x : AmbientSpace, reflectAcross n c (reflectAcross n c x) = x) ∧
    (∀ x : AmbientSpace, n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x) ∧
    (∀ x : AmbientSpace, reflectAcross n c' (reflectAcross n c x) =
      translateBy ((2 * (c' - c)) • dualVector n) x) ∧
    (∀ x : AmbientSpace,
      translateBy (v : AmbientSpace) (reflectAcross n c (translateBy (-(v : AmbientSpace)) x)) =
        reflectAcross n (c + n ⬝ᵥ (v : AmbientSpace)) x) ∧
    (∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
      P.reflectObservable (P.reflectObservable G) = G) ∧
    (∃ w : LatticePoint 1, (w : AmbientSpace) = (2 * (c' - c)) • dualVector n ∧
      linearHeight n (w : AmbientSpace) = 2 * (c' - c) ∧
      ∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
        P'.reflectObservable (P.reflectObservable G) = (shift w).actOn G) ∧
    (∃ h : IsAllowedLevel 1 n (c + n ⬝ᵥ (v : AmbientSpace)),
      ∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
        (shift v).actOn (P.reflectObservable ((shift (-v)).actOn G)) =
          NormalLevelPair.reflectObservable ⟨n, hn, c + n ⬝ᵥ (v : AmbientSpace), h⟩ G) ∧
    (∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
      IsBoundedObservable (P.conjReflectObservable G)) ∧
    (∀ (α : ℂ) (G H : GaugeField 1 → ℂ), IsBoundedObservable G → IsBoundedObservable H →
      P.conjReflectObservable (α • G + H) =
        conj α • P.conjReflectObservable G + P.conjReflectObservable H) ∧
    (∀ G H : GaugeField 1 → ℂ, IsBoundedObservable G → IsBoundedObservable H →
      P.conjReflectObservable (G * H) = P.conjReflectObservable G * P.conjReflectObservable H) ∧
    (∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
      P.conjReflectObservable (P.conjReflectObservable G) = G) ∧
    (∀ ε : ℤˣ, P.conjReflectObservable '' halfSpaceObservables 1 n c ε =
      halfSpaceObservables 1 n c (-ε)) ∧
    (∀ ε : ℤˣ, P.conjReflectObservable '' halfSpaceContinuousLocal 1 n c ε =
      halfSpaceContinuousLocal 1 n c (-ε)) ∧
    (∀ G ∈ halfSpaceObservables 1 n c (-1),
      let G' := P.conjReflectObservable G
      G' ∈ halfSpaceObservables 1 n c 1 ∧
        P.conjReflectObservable G * G = G' * P.conjReflectObservable G')
end YangMills.Construction.NormalFamilies
