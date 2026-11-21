import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.SpectralMeasures.SpectralProjectionsFunctionsAndStrongCommutation
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsContractive IsNonneg IsPositiveBounded
  IsSelfAdj Commutes UnitaryMap ofCLM)
open YangMills.Construction.SpectralTheory (UnboundedOp)
def ioiSet (c : ℝ) : BorelSubset 1 :=
  ⟨{y | c < y 0}, (isOpen_lt continuous_const (by fun_prop)).measurableSet⟩
def iioSet (c : ℝ) : BorelSubset 1 :=
  ⟨{y | y 0 < c}, (isOpen_lt (by fun_prop) continuous_const).measurableSet⟩
def iciZeroSet : BorelSubset 1 :=
  ⟨{y | 0 ≤ y 0}, (isClosed_le continuous_const (by fun_prop)).measurableSet⟩
def unitIntervalSet : BorelSubset 1 :=
  ⟨{y | y 0 ∈ Set.Icc (0 : ℝ) 1},
    (isClosed_Icc.preimage (f := fun y : Space 1 => y 0) (by fun_prop)).measurableSet⟩
def sqrtOnNonneg : iciZeroSet.1 → ℂ :=
  fun y => ((YangMills.Construction.RealPower.sqrtOf (y.1 0) : ℝ) : ℂ)
def toLine (x : ℝ) : Space 1 := WithLp.toLp 2 fun _ => x
def liftToLine {n : ℕ} (f : Space n → ℝ) : Space n → Space 1 :=
  fun y => toLine (f y)
theorem measurable_liftToLine {n : ℕ} {f : Space n → ℝ} (hf : Measurable f) :
    Measurable (liftToLine f) := by
  have hcont : Continuous toLine := by
    unfold toLine
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
  exact hcont.measurable.comp hf
def realCoord {n : ℕ} (i : Fin n) : Space n → ℝ := fun y => y i
theorem measurable_realCoord {n : ℕ} (i : Fin n) : Measurable (realCoord i) := by
  unfold realCoord
  fun_prop
section PartialMaps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def PartialMapEq {S T : Set H} (u : S → H) (v : T → H) : Prop :=
  ∃ hST : S = T, ∀ x : S, v ⟨x, hST ▸ x.2⟩ = u x
def conjPartialMap (U : UnitaryMap H H) {S : Set H} (u : S → H) : U '' S → H :=
  fun φ => U (u ⟨U.symm φ, by
    obtain ⟨_, x, hx, rfl⟩ := φ
    simpa using hx⟩)
end PartialMaps
namespace SpectralRules
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def FormBounds : Prop :=
  (∀ A : UnboundedOp H, IsSelfAdj A → ∀ c : ℝ,
    ((∀ x : A.domain, ⟪(x : H), A x⟫_ℂ ≤ ((c * ‖(x : H)‖ ^ 2 : ℝ) : ℂ)) →
      spectralResolution A (ioiSet c) = 0) ∧
    ((∀ x : A.domain, ((c * ‖(x : H)‖ ^ 2 : ℝ) : ℂ) ≤ ⟪(x : H), A x⟫_ℂ) →
      spectralResolution A (iioSet c) = 0)) ∧
  (∀ A : UnboundedOp H, IsSelfAdj A →
    (IsNonneg A ↔ IsSupportedOnPVM (spectralResolution A) iciZeroSet)) ∧
  ∀ T : H →L[ℂ] H, IsSelfAdj (ofCLM T) → IsPositiveBounded T → IsContractive T →
    IsSupportedOnPVM (spectralResolution (ofCLM T)) unitIntervalSet
def Pushforward : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ E : BorelSubset n → H →L[ℂ] H, IsPVM E →
    ∀ (f : Space n → ℝ) (hf : Measurable f),
      ∃ A : UnboundedOp H, IsSpectralIntegralOp A E (fun y => ((f y : ℝ) : ℂ)) ∧
        IsSelfAdj A ∧
        spectralResolution A = pushforward E (liftToLine f) (measurable_liftToLine hf) ∧
        ∀ h : ℝ → ℂ, Measurable h →
          PartialMapEq (borelCalculus A h) (spectralIntegral E fun y => h (f y))
def Coordinates : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ E : BorelSubset n → H →L[ℂ] H, IsPVM E →
    ∃ A : Fin n → UnboundedOp H,
      (∀ i, IsSpectralIntegralOp (A i) E (coordFn i)) ∧
      (∀ i, IsSelfAdj (A i)) ∧
      (∀ i, spectralResolution (A i) =
        pushforward E (liftToLine (realCoord i))
          (measurable_liftToLine (measurable_realCoord i))) ∧
      StronglyCommute A
def UnitaryConjugation : Prop :=
  ∀ A : UnboundedOp H, IsSelfAdj A → ∀ U : UnitaryMap H H,
    IsSelfAdj (YangMills.Construction.FormsOperators.unitaryConjugate U A) ∧
    spectralResolution (YangMills.Construction.FormsOperators.unitaryConjugate U A) =
      unitaryConj U (spectralResolution A) ∧
    (∀ h : ℝ → ℂ, Measurable h →
      PartialMapEq (borelCalculus (YangMills.Construction.FormsOperators.unitaryConjugate U A) h)
        (conjPartialMap U (borelCalculus A h))) ∧
    ∀ T : H →L[ℂ] H, A = ofCLM T →
      Commutes (U.toContinuousLinearEquiv : H →L[ℂ] H) T →
        unitaryConj U (spectralResolution A) = spectralResolution A ∧
        ∀ h : ℝ → ℂ, Measurable h →
          PartialMapEq (conjPartialMap U (borelCalculus A h)) (borelCalculus A h)
def SquareRoot : Prop :=
  ∀ T S : H →L[ℂ] H, IsSelfAdj (ofCLM T) → IsPositiveBounded T →
    IsSelfAdj (ofCLM S) → IsPositiveBounded S → S * S = T →
      IsSpectralIntegralOp (ofCLM S) (spectralResolution (ofCLM T))
        (zeroExtend iciZeroSet sqrtOnNonneg)
def AllRules : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    FormBounds H ∧ Pushforward H ∧ Coordinates H ∧ UnitaryConjugation H ∧ SquareRoot H
end SpectralRules
end YangMills.Construction.EuclideanBorel
