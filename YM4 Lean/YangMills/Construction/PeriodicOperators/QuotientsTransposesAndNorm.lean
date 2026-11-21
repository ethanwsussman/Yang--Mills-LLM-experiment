import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace Quotients
def QuotFinite (I : PeriodicData) (s : ℕ) : Prop :=
  Finite I.UnitQuot ∧ Finite (I.QuotMod s) ∧
    Nat.card (I.QuotMod s) = s ^ 4 * Nat.card I.UnitQuot
def WeightFactorsThroughQuot (I : PeriodicData) (t : ℕ) : Prop :=
  (∀ x y, I.mkQuot t x = I.mkQuot t y → I.weightOf x = I.weightOf y) ∧
    ∀ x, I.quotWeight t (I.mkQuot t x) = I.weightOf x
def PairingNormFiniteSum (I : PeriodicData) (t : ℕ) : Prop :=
  ∀ f g : I.QuotMod t → ℂ,
    PairingSummable (I.quotWeight t) f g ∧ NormSummable (I.quotWeight t) f ∧
      wPairing (I.quotWeight t) f g = ∑ᶠ c, (I.quotWeight t c : ℂ) * (f c * g c) ∧
      wNorm (I.quotWeight t) f = Real.sqrt (∑ᶠ c, I.quotWeight t c * ‖f c‖ ^ 2)
def LinearMapNormFinite (I J : PeriodicData) (t u : ℕ) : Prop :=
  ∀ L : (I.QuotMod t → ℂ) →ₗ[ℂ] (J.QuotMod u → ℂ),
    OpNormSummable (I.quotWeight t) (J.quotWeight u) univ L ∧
      wOpNorm (I.quotWeight t) (J.quotWeight u) univ L < ∞
def TransposeDual (I J : PeriodicData) (t u : ℕ) : Prop :=
  ∀ (K : J.QuotMod u → I.QuotMod t → ℂ) (f : I.QuotMod t → ℂ)
    (g : J.QuotMod u → ℂ),
    wPairing (I.quotWeight t)
        (applyKernel (wTranspose (I.quotWeight t) (J.quotWeight u) K) g) f =
      wPairing (J.quotWeight u) g (applyKernel K f)
def conjKernel {α β : Type} (K : β → α → ℂ) : β → α → ℂ := fun y x => conj (K y x)
def conjFun {α : Type} (f : α → ℂ) : α → ℂ := fun x => conj (f x)
def ConjTransposeAdjoint (I J : PeriodicData) (t u : ℕ) : Prop :=
  ∀ (K : J.QuotMod u → I.QuotMod t → ℂ) (f : I.QuotMod t → ℂ)
    (g : J.QuotMod u → ℂ),
    wPairing (I.quotWeight t)
        (conjFun
          (applyKernel (wTranspose (I.quotWeight t) (J.quotWeight u) (conjKernel K)) g)) f =
      wPairing (J.quotWeight u) (conjFun g) (applyKernel K f)
def TransposeNormEq (I J : PeriodicData) (t u : ℕ) : Prop :=
  ∀ K : J.QuotMod u → I.QuotMod t → ℂ,
    wOpNorm (J.quotWeight u) (I.quotWeight t) univ
        (applyKernel (wTranspose (I.quotWeight t) (J.quotWeight u) K)) =
      wOpNorm (I.quotWeight t) (J.quotWeight u) univ (applyKernel K)
def finiteNormSpace (I : PeriodicData) : Set (I.Carrier → ℂ) :=
  {f | NormSummable I.weightOf f}
def MapsFiniteNorm (I J : PeriodicData) (T : J.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ f ∈ finiteNormSpace I,
    (∀ y, ApplySummableAt T f y) ∧ NormSummable J.weightOf (applyKernel T f)
def OpNormFinite (I J : PeriodicData) (T : J.Carrier → I.Carrier → ℂ) : Prop :=
  OpNormSummable I.weightOf J.weightOf (finiteNormSpace I) (applyKernel T) ∧
    wOpNorm I.weightOf J.weightOf (finiteNormSpace I) (applyKernel T) < ∞
def QuotientTransposeNorm : Prop :=
  ∀ I J : PeriodicData, IsPeriodic I → IsPeriodic J → ∀ s : ℕ, 0 < s →
    QuotFinite I s ∧
    (∀ t : ℕ, t = 1 ∨ t = s →
      WeightFactorsThroughQuot I t ∧ PairingNormFiniteSum I t) ∧
    (∀ t u : ℕ, t = 1 ∨ t = s → u = 1 ∨ u = s →
      LinearMapNormFinite I J t u ∧ TransposeDual I J t u ∧
        ConjTransposeAdjoint I J t u ∧ TransposeNormEq I J t u) ∧
    ∀ T : J.Carrier → I.Carrier → ℂ, IsPeriodicKernel I J T →
      MapsFiniteNorm I J T ∧ OpNormFinite I J T
end Quotients
end YangMills.Construction.PeriodicOperators
end
