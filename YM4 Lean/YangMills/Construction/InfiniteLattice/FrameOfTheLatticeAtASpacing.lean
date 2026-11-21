import YangMills.Construction.InfiniteLattice.LongRangeOrderAndVarianceInAState
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint LatticeSymmetry IsBoundedObservable
  IsLocalObservable IsShiftInvariant AmbientSpace condExpShiftInvariant shiftInvariantSigma
  longRangeOrderParameter observableSupNorm stateVariance regionObservables plateauPairing shift)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns continuousLocal)
variable {a : ℝ}
def CompactMetrizableFieldsAndStates (a : ℝ) : Prop :=
  CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a) ∧
    CompactSpace (BorelProb a) ∧ TopologicalSpace.MetrizableSpace (BorelProb a) ∧
    ∀ μ μ' : BorelProb a, (∀ G ∈ continuousFns a, μ.integral G = μ'.integral G) → μ = μ'
def ContinuousLocalDenseSubalgebra (a : ℝ) : Prop :=
  continuousLocal a ⊆ continuousFns a ∧
    (∃ S : Subalgebra ℂ (GaugeField a → ℂ),
      (S : Set (GaugeField a → ℂ)) = continuousLocal a) ∧
    (∀ z : ℂ, (fun _ : GaugeField a => z) ∈ continuousLocal a) ∧
    (∀ G ∈ continuousLocal a, (fun U => conj (G U)) ∈ continuousLocal a) ∧
    (∀ G ∈ continuousFns a, ∀ ε : ℝ, 0 < ε →
      ∃ G' ∈ continuousLocal a, observableSupNorm (G - G') < ε) ∧
    ∃ g : ℕ → GaugeField a → ℂ, (∀ k, g k ∈ continuousLocal a) ∧
      ∀ G ∈ continuousFns a, ∀ ε : ℝ, 0 < ε → ∃ k, observableSupNorm (G - g k) < ε
def SymmetryActionProperties (r r' : LatticeSymmetry a) : Prop :=
  Function.Bijective r.linkMap ∧
    (r.comp r').toFun = r.toFun ∘ r'.toFun ∧
    (∃ t : LatticeSymmetry a, t.IsInverse r) ∧
    (∀ t : LatticeSymmetry a, t.IsInverse r →
      ∃ h : GaugeField a ≃ₜ GaugeField a,
        ⇑h = r.pullbackField ∧ ⇑h.symm = t.pullbackField) ∧
    (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField ∧
    (∀ G G' : GaugeField a → ℂ, IsBoundedObservable G → IsBoundedObservable G' →
      r.actOn (G * G') = r.actOn G * r.actOn G') ∧
    (∀ G : GaugeField a → ℂ, IsBoundedObservable G →
      r.actOn (fun U => conj (G U)) = fun U => conj (r.actOn G U)) ∧
    (∀ G : GaugeField a → ℂ, IsBoundedObservable G →
      observableSupNorm (r.actOn G) = observableSupNorm G) ∧
    (∀ S : Set AmbientSpace, r.actOn '' regionObservables a S = regionObservables a (r.setImage S)) ∧
    (∀ G : GaugeField a → ℂ, IsBoundedObservable G →
      (r.comp r').actOn G = r.actOn (r'.actOn G)) ∧
    (∀ (z z' : ℂ) (G G' : GaugeField a → ℂ), IsBoundedObservable G → IsBoundedObservable G' →
      r.actOn (z • G + z' • G') =
        z • r.actOn G + z' • r.actOn G') ∧
    (∀ G : GaugeField a → ℂ, IsBoundedObservable G → Continuous G → Continuous (r.actOn G)) ∧
    ∀ G : GaugeField a → ℂ, IsBoundedObservable G → IsLocalObservable G →
      IsLocalObservable (r.actOn G)
def PlateauAndOrderOfInvariantState (μ : BorelProb a) : Prop :=
  ∀ A B : GaugeField a → ℂ, IsBoundedObservable A → IsBoundedObservable B → ∀ v : LatticePoint a,
    longRangeOrderParameter μ.1 A =
        ((∫ U, ‖condExpShiftInvariant μ.1 A U - ∫ V, A V ∂μ.1‖ ^ 2 ∂μ.1 : ℝ) : ℂ) ∧
      ∫ U, ‖condExpShiftInvariant μ.1 A U - ∫ V, A V ∂μ.1‖ ^ 2 ∂μ.1 =
        stateVariance μ.1 (condExpShiftInvariant μ.1 A) ∧
      0 ≤ stateVariance μ.1 (condExpShiftInvariant μ.1 A) ∧
      condExpShiftInvariant μ.1 ((shift v).actOn A) =ᵐ[μ.1]
        condExpShiftInvariant μ.1 A ∧
      plateauPairing μ.1 ((shift v).actOn A) ((shift v).actOn B) =
        plateauPairing μ.1 A B ∧
      plateauPairing μ.1 (fun U => conj (A U)) B = ∫ U, A U * condExpShiftInvariant μ.1 B U ∂μ.1
def ErgodicInvariantFunctionsConstant (μ : BorelProb a) : Prop :=
  (∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
    J =ᵐ[μ.1] fun _ => ∫ U, J U ∂μ.1) ∧
  (IsShiftInvariant μ.1 → ∀ A B : GaugeField a → ℂ, IsBoundedObservable A →
    IsBoundedObservable B →
    condExpShiftInvariant μ.1 B =ᵐ[μ.1] (fun _ => ∫ U, B U ∂μ.1) ∧
      plateauPairing μ.1 A B = conj (∫ U, A U ∂μ.1) * ∫ U, B U ∂μ.1 ∧
      longRangeOrderParameter μ.1 A = 0)
def LatticeFrameAtSpacing : Prop :=
  ∀ a : ℝ, 0 < a →
    CompactMetrizableFieldsAndStates a ∧
      ContinuousLocalDenseSubalgebra a ∧
      (∀ r r' : LatticeSymmetry a, SymmetryActionProperties r r') ∧
      (∀ μ : BorelProb a, IsShiftInvariant μ.1 → PlateauAndOrderOfInvariantState μ) ∧
      ∀ μ : BorelProb a, IsErgodicState μ → ErgodicInvariantFunctionsConstant μ
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
