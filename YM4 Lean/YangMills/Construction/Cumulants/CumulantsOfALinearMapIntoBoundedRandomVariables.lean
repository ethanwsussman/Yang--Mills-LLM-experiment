import YangMills.Construction.Probability.BoundedComplexExpectation
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
def linearMapCumulant {Ω F : Type*} [MeasurableSpace Ω] [AddCommGroup F] [Module ℝ F]
    (μ : Measure Ω) (T : F →ₗ[ℝ] Ω → ℝ) {n : ℕ} (f : Fin n → F) : ℂ :=
  mixedCumulant μ fun i => T (f i)
def LinearMapCumulantProperties : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Type) [AddCommGroup F] [Module ℝ F] (T : F →ₗ[ℝ] Ω → ℝ),
    (∀ f, YangMills.Construction.Probability.IsBoundedRealRV (T f)) →
    (∀ n : ℕ, 1 ≤ n →
      (∀ f : Fin n → F, (linearMapCumulant μ T f).im = 0) ∧
      (∀ (f : Fin n → F) (σ : Equiv.Perm (Fin n)),
        linearMapCumulant μ T (fun i => f (σ i)) = linearMapCumulant μ T f) ∧
      (∀ (f : Fin n → F) (j : Fin n) (g g' : F),
        linearMapCumulant μ T (Function.update f j (g + g')) =
          linearMapCumulant μ T (Function.update f j g) +
            linearMapCumulant μ T (Function.update f j g')) ∧
      ∀ (f : Fin n → F) (j : Fin n) (a : ℝ) (g : F),
        linearMapCumulant μ T (Function.update f j (a • g)) =
          (a : ℂ) * linearMapCumulant μ T (Function.update f j g)) ∧
    (∀ f : F, linearMapCumulant μ T (fun _ : Fin 1 => f) =
      YangMills.Construction.Probability.complexExpectation μ fun ω => (T f ω : ℂ)) ∧
    ∀ (q : ℕ) (h : Fin q → F),
      YangMills.Construction.Probability.complexExpectation μ
          (fun ω => ∏ l, ((T (h l) ω : ℂ) -
            YangMills.Construction.Probability.complexExpectation μ fun ω' => (T (h l) ω' : ℂ))) =
        ∑ π ∈ YangMills.Construction.SetPartition.singletonFree q, ∏ J ∈ π.parts,
          linearMapCumulant μ T fun k : Fin J.card => h (J.orderEmbOfFin rfl k)
end YangMills.Construction.Cumulants
