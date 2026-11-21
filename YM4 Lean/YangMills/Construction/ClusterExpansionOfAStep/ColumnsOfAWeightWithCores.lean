import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCores
import YangMills.Construction.ClusterExpansionOfAStep.InfluencesOfAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.CoreColumns
open Dobrushin TorusFields TorusLumps
variable {n : ℕ} [NeZero n] {I : Type}
open Classical in
def spinInfluence (near : I → I → Prop) (rt : ℝ) (core : I → Finset (TorusSite n)) (z : I → ℝ) (i j : I) : ℝ :=
  if near i j then 4 * z i
  else 8 * z i * min 1 (((core i).card : ℝ) * Real.exp (-(rt * (setGap (core i) (core j) : ℝ) / 8)))
def ColumnsOfActivityWithCores : Prop :=
  ∀ (n : ℕ) [NeZero n] (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)]
    (A : PairConstraint S) (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (h : A.IsActivityBounded m G z) (core : I → Finset (TorusSite n)) (near : I → I → Prop) (rt e : ℝ) (Dn : ℕ),
    0 < rt → (∀ i, z i ≤ 1 / 2) → (∀ i, (core i).Nonempty) →
    (∀ y, ∑ i with y ∈ core i, z i * ((core i).card : ℝ) ^ 4 * Real.exp (2 * rt * (siteDiameter (core i) : ℝ)) ≤ e) →
    (∀ i j, near i j → setGap (core i) (core j) ≤ Dn) →
    (∀ i j, i ≠ j → ¬ near i j → A.AllCompatible i j ∧ A.DoubleRatioBound G i j
      (((core i).card : ℝ) * Real.exp (-(rt * (setGap (core i) (core j) : ℝ) / 8)))) →
    (∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B →
        (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
          (A.singleSiteKernel m h.measurable_weightDensity i σ').real B + spinInfluence near rt core z i j / 2) ∧
    (∀ (Y : TorusSite n) j, ∑ i, coreWeight (rt / 2 ^ 6) Y (core i) * spinInfluence near rt core z i j ≤
      coreWeight (rt / 2 ^ 6) Y (core j) * (8 * e * columnConstant rt Dn)) ∧
    ∀ (Y : TorusSite n) (F : (∀ i, S i) → ℝ), Measurable F → (∀ σ, |F σ| ≤ 1) →
      (∀ σ, (∀ i, Y ∈ core i → σ i = A.vacant i) → F σ = 0) → |∫ σ, F σ ∂A.gibbsLaw m G| ≤ e
end YangMills.Construction.CoreColumns
end
