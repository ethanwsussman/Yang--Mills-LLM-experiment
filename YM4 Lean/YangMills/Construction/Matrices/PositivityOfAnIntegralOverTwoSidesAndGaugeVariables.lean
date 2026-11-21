import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.Matrices.TwoSidedGaugePositivity
open ComplexMatrix2
def gaugeExponent {B S E : Type} [Fintype E] (b : E → B) (y y' : E → S)
    (A : (B → specialUnitary) → ℝ)
    (x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary)) : ℝ :=
  A x.1 + A x.2.1 +
    ∑ e, (1 - (1 / 2) *
      (fullTrace ((x.1 (b e) * (x.2.2 (y' e))⁻¹ * (x.2.1 (b e))⁻¹ * x.2.2 (y e) :
        specialUnitary) : ComplexMatrix2)).re)
def gaugeForm {B S E : Type} [Fintype B] [Fintype S] [Fintype E] (b : E → B) (y y' : E → S)
    (A : (B → specialUnitary) → ℝ) (β : ℝ) (G H : (B → specialUnitary) → ℂ) : ℂ :=
  ∫ x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary),
    starRingEnd ℂ (G x.2.1) * H x.1 * (Real.exp (-β * gaugeExponent b y y' A x) : ℂ)
    ∂(haarPi B).prod ((haarPi B).prod (haarPi S))
def PositivityStatement : Prop :=
  ∀ (B S E : Type) [Fintype B] [Fintype S] [Fintype E] (b : E → B) (y y' : E → S)
    (A : (B → specialUnitary) → ℝ) (β : ℝ), 0 < β → Measurable A → (∀ W, 0 ≤ A W) →
    ∀ H G : (B → specialUnitary) → ℂ, Measurable H → (∃ C : ℝ, ∀ W, ‖H W‖ ≤ C) →
      Measurable G → (∃ C : ℝ, ∀ W, ‖G W‖ ≤ C) →
      0 ≤ gaugeForm b y y' A β H H ∧
        ‖gaugeForm b y y' A β G H‖ ^ 2 ≤
          (gaugeForm b y y' A β G G).re * (gaugeForm b y y' A β H H).re
end YangMills.Construction.Matrices.TwoSidedGaugePositivity
end
