import YangMills.Construction.FormsOnATorus.GaugeActionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open BlockAverages
def ChartLinearizationDetBound : Prop :=
  ∀ (ι κ S : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup S] [Module ℝ S]
    (src tgt : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)),
    Function.Injective e →
    (∀ v : κ → imaginaryQuaternions, v ∈ LinearMap.range e ↔
      ∀ χ, ∑ b, inner ℝ (v b) (gaugeLinearization src tgt V 0 χ b) = 0) →
    (∀ χ, gaugeLinearization src tgt V 0 χ = 0 → χ = 0) →
    (∀ (χ : ι → imaginaryQuaternions) (z : ι) (X : imaginaryQuaternions),
      (∀ ψ, ∑ b, inner ℝ (gaugeLinearization src tgt V 0 χ b) (gaugeLinearization src tgt V 0 ψ b) =
        inner ℝ X (ψ z)) →
      ∀ z', ‖χ z'‖ ≤ ‖X‖) →
    ∃ Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S),
      chartLinearization src tgt V e 0 ∘ₗ Q = LinearMap.id ∧
      Q ∘ₗ chartLinearization src tgt V e 0 = LinearMap.id ∧
      ∀ (y : κ → imaginaryQuaternions) (s : ℝ), (∀ b, ‖y b‖ ≤ 1) → 0 ≤ s → s ≤ 1 / 8 →
        24 * ∑ b, ‖y b‖ ^ 2 ≤ s ^ 2 →
        LinearMap.det (chartLinearization src tgt V e y ∘ₗ Q) ≠ 0 ∧
        |Real.log (abs (LinearMap.det (chartLinearization src tgt V e y ∘ₗ Q)))| ≤
          3 * Real.sqrt (Fintype.card (κ × Fin 3)) * s
end YangMills.Construction.GaugeCharts
end
