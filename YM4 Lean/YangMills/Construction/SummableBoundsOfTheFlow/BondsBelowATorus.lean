import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps TorusCounting TwoLevelMixtures
namespace BondSums
section Sums
variable (L : ℕ) [NeZero L]
def bondDecaySum (s : ℝ) : ℝ := 4 * ((2 * L + 1 : ℕ) : ℝ) ^ 4 * expSumOnInt (s / 4) ^ 4
theorem bondDecaySum_nonneg (s : ℝ) : 0 ≤ bondDecaySum L s := by
  unfold bondDecaySum
  have := expSumOnInt_nonneg (s / 4)
  positivity
theorem sum_exp_neg_bondSiteDist_le {s : ℝ} (hs : 0 < s) (n : ℕ) [NeZero n] (z : TorusSite n) :
    ∑ b : TorusBond (n * L), Real.exp (-(s * (bondSiteDist L b z : ℝ))) ≤ bondDecaySum L s := by
  classical
  have h1 : ∑ b : TorusBond (n * L), Real.exp (-(s * (bondSiteDist L b z : ℝ))) =
      4 * ∑ x : TorusSite (n * L), Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [bondSiteDist]
  have h2 : ∑ x : TorusSite (n * L), Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) =
      ∑ Y' : TorusSite n, ∑ x ∈ Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y'),
        Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) :=
    (Finset.sum_fiberwise _ _ _).symm
  have h3 : ∀ Y' : TorusSite n, ∑ x ∈ Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y'),
      Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) ≤
        ((2 * L + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(s * (supDist Y' z : ℝ))) := by
    intro Y'
    have e1 : ∑ x ∈ Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y'),
        Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) =
        ((Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y')).card : ℝ) *
          Real.exp (-(s * (supDist Y' z : ℝ))) := by
      rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const, nsmul_eq_mul]
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have e2 : Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y') = sitesInBlocks L {Y'} := by
      ext x
      simp [sitesInBlocks]
    rw [e2]
    exact_mod_cast card_sitesInBlocks_singleton_le Y'
  rw [h1, h2]
  have h4 : ∑ Y' : TorusSite n, ∑ x ∈ Finset.univ.filter (fun x : TorusSite (n * L) => parentBlock L x = Y'),
      Real.exp (-(s * (supDist (parentBlock L x) z : ℝ))) ≤
      ((2 * L + 1 : ℕ) : ℝ) ^ 4 * expSumOnInt (s / 4) ^ 4 := by
    refine (Finset.sum_le_sum fun Y' _ => h3 Y').trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_exp_neg_supDist_le hs z) (by positivity)
  unfold bondDecaySum
  linarith
end Sums
end BondSums
end YangMills.Construction
end
