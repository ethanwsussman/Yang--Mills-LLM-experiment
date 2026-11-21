import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.FivePointCone
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def heatOp (E : SpectralMeasure Y H) (w : Y → ℝ) (t : ℝ) : H →L[ℂ] H :=
  E.integralOp fun x => Complex.exp ((-(t * w x) : ℝ) : ℂ)
def phaseOp (E : SpectralMeasure Y H) (p : Y → ℝ) (s : ℝ) : H →L[ℂ] H :=
  E.integralOp fun x => Complex.exp (Complex.I * s * (p x : ℝ))
def fivePointOp (E : SpectralMeasure Y H) (w p : Y → ℝ) (t : ℝ) : H →L[ℂ] H :=
  1 - (4 : ℂ) • heatOp E w t + heatOp E w (2 * t) +
    heatOp E w t * phaseOp E p t + heatOp E w t * phaseOp E p (-t)
def fivePointFn (w p : Y → ℝ) (t : ℝ) (x : Y) : ℝ :=
  (1 - Real.exp (-(t * w x))) ^ 2 -
    Real.exp (-(t * w x)) * ‖1 - Complex.exp (Complex.I * t * (p x : ℝ))‖ ^ 2
def defectSq (E : SpectralMeasure Y H) (w : Y → ℝ) (t : ℝ) : H →L[ℂ] H :=
  (1 - heatOp E w t) ^ 2
def phaseDefectOp (E : SpectralMeasure Y H) (w p : Y → ℝ) (t : ℝ) : H →L[ℂ] H :=
  heatOp E w t * ((2 : ℂ) • (1 : H →L[ℂ] H) - phaseOp E p t - star (phaseOp E p t))
def IsNonnegOnDense (A : H →L[ℂ] H) : Prop :=
  ∃ D : Set H, Dense D ∧ ∀ v ∈ D, 0 ≤ ⟪v, A v⟫_ℂ
def sinhGeSinSet {w p : Y → ℝ} (hw : Measurable w) (hp : Measurable p) (t : ℝ) :
    BorelSubsets Y :=
  ⟨{x | |Real.sin (t * p x / 2)| ≤ Real.sinh (t * w x / 2)},
    measurableSet_le (by fun_prop) (by fun_prop)⟩
def ltAbsSet {w p : Y → ℝ} (hw : Measurable w) (hp : Measurable p) : BorelSubsets Y :=
  ⟨{x | w x < |p x|}, measurableSet_lt hw hp.abs⟩
def energyOp (E : SpectralMeasure Y H) (w : Y → ℝ) : UnboundedOp H :=
  spectralIntegralOp E fun x => ((w x : ℝ) : ℂ)
def momentumOp (E : SpectralMeasure Y H) (p : Y → ℝ) : UnboundedOp H :=
  spectralIntegralOp E fun x => ((p x : ℝ) : ℂ)
def FivePointConeTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H) (w p : Y → ℝ)
    (hw : Measurable w) (hp : Measurable p), (∀ x, 0 ≤ w x) →
    (∀ t : ℝ, 0 < t →
      fivePointOp E w p t = defectSq E w t - phaseDefectOp E w p t ∧
      fivePointOp E w p t =
        E.integralOp (fun x => ((fivePointFn w p t x : ℝ) : ℂ)) ∧
      IsSelfAdjoint (defectSq E w t) ∧ IsSelfAdjoint (phaseDefectOp E w p t) ∧
      IsSelfAdjoint (fivePointOp E w p t) ∧
      ∀ x, Real.exp (t * w x) * fivePointFn w p t x =
          4 * Real.sinh (t * w x / 2) ^ 2 - 4 * Real.sin (t * p x / 2) ^ 2 ∧
        4 * Real.sinh (t * w x / 2) ^ 2 - 4 * Real.sin (t * p x / 2) ^ 2 =
          2 * (Real.cosh (t * w x) + Real.cos (t * p x) - 2)) ∧
    (∀ t : ℝ, 0 < t → IsNonnegOnDense (fivePointOp E w p t) →
      IsGE (defectSq E w t) (phaseDefectOp E w p t) ∧
      E.IsCarriedBy (sinhGeSinSet hw hp t)) ∧
    (∀ t : ℕ → ℝ, (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
      (∀ k, IsNonnegOnDense (fivePointOp E w p (t k))) →
      E (ltAbsSet hw hp) = 0) ∧
    (E (ltAbsSet hw hp) = 0 →
      absOp (momentumOp E p) = spectralIntegralOp E (fun x => ((|p x| : ℝ) : ℂ)) ∧
      (energyOp E w).domain ≤ (momentumOp E p).domain ∧
      (momentumOp E p).domain = (absOp (momentumOp E p)).domain ∧
      (∀ v : (energyOp E w).domain, ∃ h : (v : H) ∈ (absOp (momentumOp E p)).domain,
        ⟪(v : H), absOp (momentumOp E p) ⟨v, h⟩⟫_ℂ ≤ ⟪(v : H), energyOp E w v⟫_ℂ) ∧
      ∀ v : (energyOp E w).domain, energyOp E w v = 0 → ∀ s : ℝ, phaseOp E p s v = v)
end YangMills.Construction.FivePointCone
