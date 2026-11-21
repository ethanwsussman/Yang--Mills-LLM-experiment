import YangMills.Construction.ClusterExpansionOfAStep.DobrushinComparison
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
open Classical in
def PairConstraint.weightDensity (A : PairConstraint S) (G : (∀ i, S i) → ℝ) (σ : ∀ i, S i) : ℝ≥0∞ :=
  if A.IsAdmissible σ then ENNReal.ofReal (G σ) else 0
def PairConstraint.conditionalMass (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (i : I)
    (σ : ∀ i, S i) : ℝ≥0∞ :=
  ∫⁻ s, A.weightDensity G (Function.update σ i s) ∂m i
def PairConstraint.gibbsLaw (A : PairConstraint S) (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)]
    (G : (∀ i, S i) → ℝ) : Measure (∀ i, S i) :=
  (∫⁻ σ, A.weightDensity G σ ∂Measure.pi m)⁻¹ • (Measure.pi m).withDensity (A.weightDensity G)
open Classical in
def PairConstraint.singleSiteLaw (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (i : I)
    (σ : ∀ i, S i) : Measure (S i) :=
  if 0 < A.conditionalMass m G i σ ∧ A.conditionalMass m G i σ ≠ ⊤ then
    (A.conditionalMass m G i σ)⁻¹ • (m i).withDensity fun s => A.weightDensity G (Function.update σ i s)
  else Measure.dirac (A.vacant i)
theorem PairConstraint.measurable_singleSiteLaw (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SFinite (m i)] {G : (∀ i, S i) → ℝ} (hd : Measurable (A.weightDensity G)) (i : I) :
    Measurable (A.singleSiteLaw m G i) := by
  have hj : Measurable fun p : (∀ j, S j) × S i => A.weightDensity G (Function.update p.1 i p.2) :=
    hd.comp measurable_update'
  have hmass : Measurable (A.conditionalMass m G i) := hj.lintegral_prod_right'
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have hset : MeasurableSet {σ | 0 < A.conditionalMass m G i σ ∧ A.conditionalMass m G i σ ≠ ⊤} :=
    (measurableSet_lt measurable_const hmass).inter
      (hmass (measurableSet_singleton ⊤)).compl
  have hB' : Measurable fun σ => ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i :=
    hj.lintegral_prod_right'
  have : (fun σ => A.singleSiteLaw m G i σ B) = fun σ =>
      if 0 < A.conditionalMass m G i σ ∧ A.conditionalMass m G i σ ≠ ⊤ then
        (A.conditionalMass m G i σ)⁻¹ * ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i
      else Measure.dirac (A.vacant i) B := by
    funext σ
    unfold PairConstraint.singleSiteLaw
    split_ifs with h
    · simp only [Measure.smul_apply, smul_eq_mul]
      rw [withDensity_apply _ hB]
    · rfl
  rw [this]
  exact Measurable.ite hset (hmass.inv.mul hB') measurable_const
def PairConstraint.singleSiteKernel (A : PairConstraint S) (m : ∀ i, Measure (S i)) [∀ i, SFinite (m i)]
    {G : (∀ i, S i) → ℝ} (hd : Measurable (A.weightDensity G)) (i : I) : Kernel (∀ j, S j) (S i) :=
  ⟨A.singleSiteLaw m G i, A.measurable_singleSiteLaw m hd i⟩
structure PairConstraint.IsActivityBounded (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ)
    (z : I → ℝ) : Prop where
  measurableSet_admissible : MeasurableSet {σ | A.IsAdmissible σ}
  measurable : Measurable G
  pos_of_admissible : ∀ σ, A.IsAdmissible σ → 0 < G σ
  measurableSet_vacant : ∀ i, MeasurableSet {A.vacant i}
  measure_vacant : ∀ i, m i {A.vacant i} = 1
  activity_nonneg : ∀ i, 0 ≤ z i
  lintegral_compl_vacant_le : ∀ i σ, A.IsAdmissible σ →
    ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal (z i) * A.weightDensity G (Function.update σ i (A.vacant i))
theorem PairConstraint.IsActivityBounded.measurable_weightDensity {A : PairConstraint S}
    {m : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) :
    Measurable (A.weightDensity G) := by
  classical
  unfold PairConstraint.weightDensity
  exact Measurable.ite h.measurableSet_admissible (ENNReal.measurable_ofReal.comp h.measurable) measurable_const
end Dobrushin
end YangMills.Construction
end
