import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import YangMills.Construction.Lattice.SetsOfSitesInEveryDimension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace MaxBallSites
variable {d N : ℕ}
theorem norm_coord_sub_le_maxDist (a b : Torus d N) (μ : Fin d) : ‖a μ - b μ‖ ≤ maxDist a b :=
  norm_le_pi_norm (a - b) μ
theorem taxicabDist_le_of_maxDist_le {a b : Torus d N} {r : ℝ} (hab : maxDist a b ≤ r) :
    taxicabDist a b ≤ (d : ℝ) * r := by
  unfold taxicabDist
  calc ∑ μ, ‖a μ - b μ‖ ≤ ∑ _μ : Fin d, r :=
        Finset.sum_le_sum fun μ _ => (norm_coord_sub_le_maxDist a b μ).trans hab
    _ = (d : ℝ) * r := by simp
theorem taxicabDist_triangle (a b c : Torus d N) :
    taxicabDist a c ≤ taxicabDist a b + taxicabDist b c := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem taxicabDist_comm (a b : Torus d N) : taxicabDist a b = taxicabDist b a := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem exists_real_lift (u : Torus d N) :
    ∃ w : Fin d → ℝ, ∀ μ, (w μ : AddCircle (N : ℝ)) = u μ := by
  choose w hw using fun μ => QuotientAddGroup.mk_surjective (u μ)
  exact ⟨w, hw⟩
end MaxBallSites
end YangMills.Construction.PeriodicLattice
