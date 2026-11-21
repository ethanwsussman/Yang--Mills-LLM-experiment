import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ResponseInTheExpansion
namespace FourPointCondition
structure QuadraticFormApproximation {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {I : Type} [Fintype I] {q : ℕ}
    (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (K : Fin (q + 1) → Matrix I I ℝ)
    (T : Matrix I I ℝ) (c : Fin (q + 1) → ℝ) (x n C P M : ℝ) (Cr : ℕ → ℝ) : Prop where
  measurableSet_event : MeasurableSet A
  measurable_component : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (G ω a)
  abs_component_le : ∀ ω a e, |imaginaryComponent e (G ω a)| ≤ M
  gaussian_moments : ∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 16 →
    Integrable (Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) μ ∧
    |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ -
      x ^ (-(r : ℝ) / 2) * wickPairingSum fun i j => if e i = e j then T (a i) (a j) else 0| ≤
      C * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000)
  covariance_isSymm : T.IsSymm
  abs_covariance_le : ∀ a b, |T a b| ≤ C
  kernel_isSymm : ∀ i, (K i).IsSymm
  kernel_sum_abs_le : ∀ i, ∑ a, ∑ b, |K i a b| ≤ C * n ^ 4 * Real.log x ^ 24
  lintegral_deviation_le : ∀ (i : Fin (q + 1)) (r : ℕ), 1 ≤ r →
    ∫⁻ ω, ENNReal.ofReal (Set.indicator (A ∩ B)
        (fun ω => |F i ω - c i - quadraticForm (K i) (G ω)| ^ (2 * r)) ω) ∂μ ≤
      ENNReal.ofReal ((Cr r * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * r))
  measureReal_compl_le : μ.real Aᶜ ≤ C * x ^ (-P)
  measureReal_inter_compl_le : μ.real (A ∩ Bᶜ) ≤ C * x ^ (-P)
def cumulantOfQuadraticApproximationStatement : Prop :=
  ∀ (q : ℕ) (Cr Cq : ℕ → ℝ) (C : ℝ), 1 ≤ q → q ≤ 3 → ∃ C' x₁ : ℝ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
      (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (K : Fin (q + 1) → Matrix I I ℝ)
      (T : Matrix I I ℝ) (c m : Fin (q + 1) → ℝ) (x n w M : ℝ),
      x₁ ≤ x → 1 ≤ n → n ≤ x ^ ((1 : ℝ) / 90) → 0 ≤ w → w ≤ x →
      QuadraticFormApproximation μ F G A B K T c x n C 40 M Cr →
      (∀ i, Measurable (F i)) → (∀ i, ∃ D : ℝ, ∀ᵐ ω ∂μ, |F i ω| ≤ D) →
      (∀ i (r : ℕ), 1 ≤ r → ∫ ω, |F i ω - m i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r)) →
      ‖(x : ℂ) ^ (q + 1) * Cumulants.mixedCumulant μ F - ((cyclicTraceSum K T : ℝ) : ℂ)‖ ≤
        C' * x ^ (-(1 / 5 : ℝ))
end FourPointCondition
end YangMills.Construction
end
