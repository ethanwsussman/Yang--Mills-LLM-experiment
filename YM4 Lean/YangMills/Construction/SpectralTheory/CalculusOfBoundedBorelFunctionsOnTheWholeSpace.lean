import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import YangMills.Construction.SpectralTheory.ProjectionValuedBorelMeasuresOnTheWholeSpaceAndSimpleFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction
namespace WholeSpaceSpectral
open YangMills.Construction.BorelSpectral (BorelSubsets SpectralMeasure)
open YangMills.Construction.BorelCalculus (IsBoundedFn conjFn)
def IsBoundedMeasurableFn {X : Type*} [MeasurableSpace X] (f : X → ℂ) : Prop :=
  Measurable f ∧ IsBoundedFn f
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def integralOpOf (E : SpectralMeasureOnSpace n H) (f : (Fin n → ℝ) → ℂ) : H →L[ℂ] H :=
  E.integralOp fun y => f y.1
def integralOpOver (E : SpectralMeasureOnSpace n H) (S : BorelSubsets (Fin n → ℝ)) (g : S.1 → ℂ) :
    H →L[ℂ] H :=
  E.integralOpOn (restrictToUniv S) fun y => g ⟨y.1.1, y.2⟩
def liftMap {m : ℕ} (p : (Fin n → ℝ) → (Fin m → ℝ)) :
    ↥(univ : Set (Fin n → ℝ)) → ↥(univ : Set (Fin m → ℝ)) :=
  fun y => ⟨p y.1, mem_univ _⟩
structure BoundedCalculusLaws (E : SpectralMeasureOnSpace n H) : Prop where
  add_smul : ∀ f g : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
    ∀ c : ℂ, integralOpOf E (f + c • g) = integralOpOf E f + c • integralOpOf E g
  mul : ∀ f g : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
    integralOpOf E (f * g) = integralOpOf E f * integralOpOf E g
  indicator : ∀ A : BorelSubsets (Fin n → ℝ),
    integralOpOf E (A.1.indicator fun _ => 1) = opAt E A
  one : integralOpOf E (fun _ => 1) = 1
  adjoint : ∀ f : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f →
    star (integralOpOf E f) = integralOpOf E (conjFn f)
  norm_sq : ∀ f : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f → ∀ v : H,
    ‖integralOpOf E f v‖ ^ 2 = ∫ y, ‖f y.1‖ ^ 2 ∂E.diagMeasure v
structure SupportLaws (E : SpectralMeasureOnSpace n H) (S : BorelSubsets (Fin n → ℝ)) : Prop where
  opAt_support : opAt E S = 1
  diagSetFn_compl : ∀ v : H,
    diagSetFn E v ⟨univ \ S.1, MeasurableSet.univ.diff S.2⟩ = 0
  congr : ∀ f g : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
    (∀ x ∈ S.1, f x = g x) → integralOpOf E f = integralOpOf E g
  eq_integralOpOver : ∀ f : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f →
    integralOpOf E f = integralOpOver E S (fun x => f x)
  norm_sq : ∀ f : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f → ∀ v : H,
    ‖integralOpOver E S (fun x => f x) v‖ ^ 2 =
      ∫ y in (restrictToUniv S).1, ‖f y.1‖ ^ 2 ∂E.diagMeasure v
  opNorm_le : ∀ f : (Fin n → ℝ) → ℂ, IsBoundedMeasurableFn f →
    ‖integralOpOver E S (fun x => f x)‖ ≤ ⨆ x : S.1, ‖f x‖
  over_add : ∀ g h : S.1 → ℂ, IsBoundedMeasurableFn g → IsBoundedMeasurableFn h →
    integralOpOver E S (g + h) = integralOpOver E S g + integralOpOver E S h
  over_smul : ∀ (c : ℂ) (g : S.1 → ℂ), IsBoundedMeasurableFn g →
    integralOpOver E S (c • g) = c • integralOpOver E S g
  over_mul : ∀ g h : S.1 → ℂ, IsBoundedMeasurableFn g → IsBoundedMeasurableFn h →
    integralOpOver E S (g * h) = integralOpOver E S g * integralOpOver E S h
  over_one : integralOpOver E S (fun _ => 1) = 1
  over_conj : ∀ g : S.1 → ℂ, IsBoundedMeasurableFn g →
    integralOpOver E S (conjFn g) = star (integralOpOver E S g)
  support_empty : S.1 = ∅ → 1 = opAt E ⟨univ, MeasurableSet.univ⟩ ∧
    opAt E ⟨univ, MeasurableSet.univ⟩ = 0 ∧ ∀ v : H, v = 0
def StrongConvergenceOver (E : SpectralMeasureOnSpace n H) (S : BorelSubsets (Fin n → ℝ)) : Prop :=
  ∀ (fs : ℕ → S.1 → ℂ) (g : S.1 → ℂ), (∀ k, 1 ≤ k → Measurable (fs k)) →
    (∃ c : ℝ, ∀ k, 1 ≤ k → ∀ y, ‖fs k y‖ ≤ c) →
    (∀ y, Tendsto (fun k => fs k y) atTop (𝓝 (g y))) → ∀ v : H,
      Tendsto (fun k => integralOpOver E S (fs k) v) atTop
        (𝓝 (integralOpOver E S g v))
structure PushforwardLaws (E : SpectralMeasureOnSpace n H) : Prop where
  diagMeasure_mapBy : ∀ {m : ℕ} (hm : 1 ≤ m) (p : (Fin n → ℝ) → (Fin m → ℝ))
    (hp : Measurable p) (v : H),
    (mapBy E hm p hp).diagMeasure v = (E.diagMeasure v).map (liftMap p)
  integralOpOf_mapBy : ∀ {m : ℕ} (hm : 1 ≤ m) (p : (Fin n → ℝ) → (Fin m → ℝ))
    (hp : Measurable p) (h : (Fin m → ℝ) → ℂ), IsBoundedMeasurableFn h →
    integralOpOf (mapBy E hm p hp) h = integralOpOf E (h ∘ p)
end WholeSpaceSpectral
namespace WholeSpaceCalculus
open YangMills.Construction.BorelSpectral (BorelSubsets)
open YangMills.Construction.WholeSpaceSpectral
def BoundedCalculusTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (E : SpectralMeasureOnSpace n H),
    BoundedCalculusLaws E ∧
      (∀ S : BorelSubsets (Fin n → ℝ), IsSupportedOn E S → SupportLaws E S ∧ StrongConvergenceOver E S) ∧
      PushforwardLaws E
end WholeSpaceCalculus
end YangMills.Construction
