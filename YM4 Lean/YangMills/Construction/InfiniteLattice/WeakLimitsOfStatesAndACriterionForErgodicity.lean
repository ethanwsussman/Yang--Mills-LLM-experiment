import YangMills.Construction.InfiniteLattice.LongRangeOrderAndVarianceInAState
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
open YangMills.Construction.InfiniteLattice (GaugeField LatticeSymmetry IsBoundedObservable
  IsLocalObservable IsSymmetricUnder IsShiftInvariant regionObservables observableSupNorm
  longRangeOrderParameter)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns continuousLocal)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair)
def l2Norm {a : ℝ} (μ : BorelProb a) (H : GaugeField a → ℂ) : ℝ :=
  (∫ U, ‖H U‖ ^ 2 ∂μ.1) ^ (1 / 2 : ℝ)
def mirrorReflectionForm {a : ℝ} (μ : BorelProb a) (M : MirrorPair a) (G : GaugeField a → ℂ) : ℂ :=
  μ.integral fun U => conj (M.reflect.actOn G U) * G U
def SymmetryPassesToWeakLimits (a : ℝ) : Prop :=
  ∀ (μ : ℕ → BorelProb a) (μ₀ : BorelProb a) (r : LatticeSymmetry a), BorelProb.TendstoWeak μ μ₀ →
    (∀ i, IsSymmetricUnder (μ i).1 r) → IsSymmetricUnder μ₀.1 r
def ReflectionFormL2Continuous (a : ℝ) : Prop :=
  ∀ (M : MirrorPair a) (μ : BorelProb a), IsSymmetricUnder μ.1 M.reflect →
    (∀ G G' : GaugeField a → ℂ, IsBoundedObservable G → IsBoundedObservable G' →
      ‖mirrorReflectionForm μ M G - mirrorReflectionForm μ M G'‖ ≤
        l2Norm μ (G - G') * (l2Norm μ G + l2Norm μ G')) ∧
    ((∀ G ∈ continuousLocal a, G ∈ regionObservables a M.upperHalf →
        0 ≤ mirrorReflectionForm μ M G) →
      ∀ G : GaugeField a → ℂ, IsLocalObservable G → G ∈ regionObservables a M.upperHalf →
        0 ≤ mirrorReflectionForm μ M G)
def ErgodicOfVanishingLongRangeOrder (a : ℝ) : Prop :=
  ∀ (ρ : BorelProb a) (D : Set (GaugeField a → ℂ)), IsShiftInvariant ρ.1 →
    D ⊆ continuousFns a →
    (∀ G ∈ continuousFns a, ∀ ε : ℝ, 0 < ε → ∃ A ∈ D, observableSupNorm (G - A) < ε) →
    (∀ A ∈ D, longRangeOrderParameter ρ.1 A = 0) → IsErgodicState ρ
def WeakLimitsAndErgodicity : Prop :=
  ∀ a : ℝ, 0 < a →
    SymmetryPassesToWeakLimits a ∧ ReflectionFormL2Continuous a ∧
      ErgodicOfVanishingLongRangeOrder a
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
