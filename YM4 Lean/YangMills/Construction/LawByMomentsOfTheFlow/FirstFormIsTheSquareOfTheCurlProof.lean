import YangMills.Construction.LawByMomentsOfTheFlow.FirstFormIsTheSquareOfTheCurl
import YangMills.Construction.SummableBoundsOfTheFlow.EntriesOfTheLevelsOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TopLevelSites TorusFrame WeightedResponses LocalFunctionals
namespace MomentLaw
variable {m : ℕ}
private theorem maxwellKernel_eq_sum_curl [NeZero m] (a : ℝ) (L : ℕ) (b b' : TorusBond m) :
    maxwellKernel a L 0 b b' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      curl (bondIndicator b) p * curl (bondIndicator b') p := by apply _root_.YangMills.SharedProofs.p29646 <;> assumption
private theorem curl_eq_sum_bondIndicator [NeZero m] (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl A p = ∑ b : TorusBond m, A b * curl (bondIndicator b) p := by
  classical
  have h : ∀ e : TorusBond m, A e = ∑ b : TorusBond m, A b * bondIndicator b e := fun e => by
    simp [bondIndicator]
  have hsum : ∑ b : TorusBond m, A b * curl (bondIndicator b) p =
      (∑ b : TorusBond m, A b * bondIndicator b (p.1, p.2.1)) +
        (∑ b : TorusBond m, A b * bondIndicator b (p.1 + TorusFields.unitStep m p.2.1, p.2.2)) -
        (∑ b : TorusBond m, A b * bondIndicator b (p.1 + TorusFields.unitStep m p.2.2, p.2.1)) -
          ∑ b : TorusBond m, A b * bondIndicator b (p.1, p.2.2) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [curl]
    ring
  rw [hsum, ← h, ← h, ← h, ← h]
  rfl
theorem maxwellFormAtZero : maxwellFormAtZeroStatement := by
  intro a L m _ A
  unfold maxwellForm
  simp only [maxwellKernel_eq_sum_curl]
  calc ∑ b : TorusBond m, ∑ b' : TorusBond m, A b * (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
          curl (bondIndicator b) p * curl (bondIndicator b') p) * A b'
      = ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
          (A b * curl (bondIndicator b) p) * (A b' * curl (bondIndicator b') p) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), ∑ b : TorusBond m, ∑ b' : TorusBond m,
          (A b * curl (bondIndicator b) p) * (A b' * curl (bondIndicator b') p) := by
        rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
    _ = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [sq, curl_eq_sum_bondIndicator A p, Finset.sum_mul_sum]
end MomentLaw
end YangMills.Construction
end
