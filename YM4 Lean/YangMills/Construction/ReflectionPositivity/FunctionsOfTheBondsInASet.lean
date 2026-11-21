import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.RegionFunctions
open YangMills.Construction.InfiniteLattice (AmbientSpace GaugeField IsLocalObservable
  IsBoundedObservable regionObservables positiveLinksWithin latticeSubgroup)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (RegionLinkVariables
  restrictToRegion extendFromRegion)
variable {a : ℝ}
def IsBddBorel {S : Set AmbientSpace} (f : RegionLinkVariables a S → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ V, ‖f V‖ ≤ C
def sqMean (μ : BorelProb a) (H : GaugeField a → ℂ) : ℂ :=
  μ.integral fun U => ((‖H U‖ ^ 2 : ℝ) : ℂ)
def absMean (μ : BorelProb a) (H : GaugeField a → ℂ) : ℂ :=
  μ.integral fun U => ((‖H U‖ : ℝ) : ℂ)
def RegionObservablesFactor (ha : 0 < a) (S : Set AmbientSpace) : Prop :=
  Continuous (restrictToRegion S : GaugeField a → RegionLinkVariables a S) ∧
  Continuous (extendFromRegion ha S) ∧
  (restrictToRegion S : GaugeField a → RegionLinkVariables a S) ∘ extendFromRegion ha S = id ∧
  CompactSpace (RegionLinkVariables a S) ∧
  TopologicalSpace.MetrizableSpace (RegionLinkVariables a S) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (F ∈ regionObservables a S ↔ F = F ∘ extendFromRegion ha S ∘ restrictToRegion S)) ∧
  (∀ F ∈ regionObservables a S,
    IsBddBorel (F ∘ extendFromRegion ha S) ∧
      F = (F ∘ extendFromRegion ha S) ∘ restrictToRegion S ∧
      (Continuous F → Continuous (F ∘ extendFromRegion ha S))) ∧
  ∀ f : RegionLinkVariables a S → ℂ, IsBddBorel f →
    f ∘ restrictToRegion S ∈ regionObservables a S ∧
      (Continuous f → Continuous (f ∘ (restrictToRegion S : GaugeField a → RegionLinkVariables a S)))
def RegionObservablesMonotoneInter (a : ℝ) (S T : Set AmbientSpace) : Prop :=
  (S ∩ (latticeSubgroup a : Set AmbientSpace) ⊆ T → regionObservables a S ⊆ regionObservables a T) ∧
  regionObservables a S ∩ regionObservables a T = regionObservables a (S ∩ T) ∧
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    ((F ∈ regionObservables a S ∧ IsLocalObservable F) ↔
      ∃ Q : Set AmbientSpace, Bornology.IsBounded Q ∧ F ∈ regionObservables a (S ∩ Q))
def LinksOfBoundedOrEmptyRegion (a : ℝ) (S : Set AmbientSpace) : Prop :=
  (Bornology.IsBounded S → (positiveLinksWithin a S).Finite) ∧
  (positiveLinksWithin a S = ∅ → ∀ F ∈ regionObservables a S, ∃ z : ℂ, ∀ U, F U = z)
def ContinuousApproximation (a : ℝ) (S : Set AmbientSpace) : Prop :=
  ∀ (μ : BorelProb a) (F : GaugeField a → ℂ), IsBoundedObservable F →
    (∃ Fn : ℕ → GaugeField a → ℂ, (∀ n, Fn n ∈ continuousFns a) ∧
      Tendsto (fun n => sqMean μ (F - Fn n)) atTop (𝓝 0)) ∧
    (∀ Fn : ℕ → GaugeField a → ℂ, (∀ n, Fn n ∈ continuousFns a) →
      Tendsto (fun n => sqMean μ (F - Fn n)) atTop (𝓝 0) →
        Tendsto (fun n => absMean μ (F - Fn n)) atTop (𝓝 0)) ∧
    (F ∈ regionObservables a S →
      ∃ Fn : ℕ → GaugeField a → ℂ,
        (∀ n, Fn n ∈ continuousFns a ∧ Fn n ∈ regionObservables a S) ∧
        Tendsto (fun n => sqMean μ (F - Fn n)) atTop (𝓝 0))
def RegionFunctionsStatement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (S T : Set AmbientSpace),
    RegionObservablesFactor ha S ∧ RegionObservablesMonotoneInter a S T ∧
      LinksOfBoundedOrEmptyRegion a S ∧ ContinuousApproximation a S
end YangMills.Construction.ReflectionPositivity.RegionFunctions
