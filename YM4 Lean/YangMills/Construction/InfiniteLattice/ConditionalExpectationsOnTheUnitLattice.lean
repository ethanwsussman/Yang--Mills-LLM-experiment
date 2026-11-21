import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.UnitLatticeCondExp
open FormHilbert (IsOrthProjOnto subFieldL2)
def fieldL2 (μ : Measure (GaugeField 1)) :
    (𝓖 : MeasurableSpace (GaugeField 1)) → 𝓖 ≤ borel (GaugeField 1) → Set (Lp ℂ 2 μ) :=
  subFieldL2 μ
def CondExpVersionsExist (μ : Measure (GaugeField 1))
    (𝓖 : MeasurableSpace (GaugeField 1)) : Prop :=
  ∀ X : GaugeField 1 → ℂ, Integrable X μ →
    (∃ Y : GaugeField 1 → ℂ, IsCondExpOf μ 𝓖 X Y) ∧
    (∀ Y₁ Y₂ : GaugeField 1 → ℂ, IsCondExpOf μ 𝓖 X Y₁ →
      IsCondExpOf μ 𝓖 X Y₂ → Y₁ =ᵐ[μ] Y₂) ∧
    ∀ Y : GaugeField 1 → ℂ, IsCondExpOf μ 𝓖 X Y →
      ∀ H : GaugeField 1 → ℂ, Measurable[𝓖] H → (∃ C : ℝ, ∀ U, ‖H U‖ ≤ C) →
        ∫ U, H U * Y U ∂μ = ∫ U, H U * X U ∂μ
def CondExpLinearConjFixes (μ : Measure (GaugeField 1))
    (𝓖 : MeasurableSpace (GaugeField 1)) : Prop :=
  (∀ (z₁ z₂ : ℂ) (X₁ X₂ : GaugeField 1 → ℂ), Integrable X₁ μ → Integrable X₂ μ →
    condExpGiven μ 𝓖 (fun U => z₁ * X₁ U + z₂ * X₂ U) =ᵐ[μ]
      fun U => z₁ * condExpGiven μ 𝓖 X₁ U + z₂ * condExpGiven μ 𝓖 X₂ U) ∧
  (∀ X : GaugeField 1 → ℂ, Integrable X μ →
    condExpGiven μ 𝓖 (fun U => conj (X U)) =ᵐ[μ]
      fun U => conj (condExpGiven μ 𝓖 X U)) ∧
  ∀ X : GaugeField 1 → ℂ, Integrable X μ →
    (∃ H : GaugeField 1 → ℂ, Measurable[𝓖] H ∧ X =ᵐ[μ] H) →
      condExpGiven μ 𝓖 X =ᵐ[μ] X
def CondExpIsOrthProj (μ : Measure (GaugeField 1))
    (𝓖 : MeasurableSpace (GaugeField 1)) (h𝓖 : 𝓖 ≤ borel (GaugeField 1)) : Prop :=
  (∀ X : Lp ℂ 2 μ, ∃ H ∈ fieldL2 μ 𝓖 h𝓖,
    (H : GaugeField 1 → ℂ) =ᵐ[μ] condExpGiven μ 𝓖 X) ∧
  (∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
    IsOrthProjOnto P (fieldL2 μ 𝓖 h𝓖) ∧
    ∀ X : Lp ℂ 2 μ, (P X : GaugeField 1 → ℂ) =ᵐ[μ] condExpGiven μ 𝓖 X) ∧
  (∃ K : Submodule ℂ (Lp ℂ 2 μ),
    (K : Set (Lp ℂ 2 μ)) = fieldL2 μ 𝓖 h𝓖) ∧
  IsClosed (fieldL2 μ 𝓖 h𝓖) ∧
  ∀ X Y : GaugeField 1 → ℂ, MemLp X 2 μ → MemLp Y 2 μ →
    Integrable (fun U => conj (condExpGiven μ 𝓖 X U) *
      condExpGiven μ 𝓖 Y U) μ ∧
    Integrable (fun U => conj (X U) * condExpGiven μ 𝓖 Y U) μ ∧
    Integrable (fun U => conj (condExpGiven μ 𝓖 X U) * Y U) μ ∧
    ∫ U, conj (condExpGiven μ 𝓖 X U) * condExpGiven μ 𝓖 Y U ∂μ =
      ∫ U, conj (X U) * condExpGiven μ 𝓖 Y U ∂μ ∧
    ∫ U, conj (X U) * condExpGiven μ 𝓖 Y U ∂μ =
      ∫ U, conj (condExpGiven μ 𝓖 X U) * Y U ∂μ
def CondExpCommutesSymmetry (μ : Measure (GaugeField 1))
    (𝓖 : MeasurableSpace (GaugeField 1)) : Prop :=
  ∀ g t : LatticeSymmetry 1, t.IsInverse g → IsSymmetricUnder μ g →
    (∀ A : Set (GaugeField 1), MeasurableSet[𝓖] A →
      Measurable[𝓖] (g.actOn (A.indicator (1 : GaugeField 1 → ℂ))) ∧
      Measurable[𝓖] (t.actOn (A.indicator (1 : GaugeField 1 → ℂ)))) →
    ∀ X : GaugeField 1 → ℂ, Integrable X μ →
      condExpGiven μ 𝓖 (g.actOn X) =ᵐ[μ]
        g.actOn (condExpGiven μ 𝓖 X)
def UnitLatticeCondExpProperties : Prop :=
  ∀ (μ : Measure (GaugeField 1)) [IsProbabilityMeasure μ] (𝓖 : MeasurableSpace (GaugeField 1))
    (h𝓖 : 𝓖 ≤ borel (GaugeField 1)),
    CondExpVersionsExist μ 𝓖 ∧
    CondExpLinearConjFixes μ 𝓖 ∧
    CondExpIsOrthProj μ 𝓖 h𝓖 ∧
    CondExpCommutesSymmetry μ 𝓖
end YangMills.Construction.InfiniteLattice.UnitLatticeCondExp
end
