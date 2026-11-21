import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
open Classical in
def PairConstraint.embedConfig (A : PairConstraint S) {J : Type} {T : J → Type} (e : J → I)
    (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) : ∀ i, S i := fun i =>
  if h : ∃ j, e j = i then h.choose_spec ▸ v h.choose (τ h.choose) else A.vacant i
structure PairConstraint.IsVacantOffRange (A : PairConstraint S) {J : Type} (m m' : ∀ i, Measure (S i))
    (e : J → I) : Prop where
  eq_on_range : ∀ j, m' (e j) = m (e j)
  eq_dirac_off_range : ∀ i, (∀ j, e j ≠ i) → m' i = Measure.dirac (A.vacant i)
structure PairConstraint.HasDobrushinColumns (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SFinite (m i)] {G : (∀ i, S i) → ℝ} (hd : Measurable (A.weightDensity G)) (c : I → I → ℝ)
    (w : I → ℝ) : Prop where
  coeff_nonneg : ∀ i j, 0 ≤ c i j
  weight_pos : ∀ i, 0 < w i
  kernel_le : ∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
    ∀ B, MeasurableSet B →
      (A.singleSiteKernel m hd i σ).real B ≤ (A.singleSiteKernel m hd i σ').real B + c i j / 2
  column_sum_le : ∀ j, ∑ i, w i * c i j ≤ w j / 2
structure PairConstraint.IsLocalObservable (A : PairConstraint S) (M : Finset I) (w : I → ℝ)
    (F : (∀ i, S i) → ℝ) : Prop where
  measurable : Measurable F
  abs_le_one : ∀ σ, |F σ| ≤ 1
  oscillation : A.OscillationBound F fun i => if i ∈ M then 2 else 0
  one_le_weight : ∀ i ∈ M, 1 ≤ w i
end Dobrushin
end YangMills.Construction
end
