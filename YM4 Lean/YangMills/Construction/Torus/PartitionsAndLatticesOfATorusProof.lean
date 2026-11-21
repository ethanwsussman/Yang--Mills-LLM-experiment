import YangMills.Construction.GeneralTorus.CubePartitions
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set Metric TorusMetric
open scoped ENNReal Topology
noncomputable section
namespace GeneralTorus.CubePartitions
variable {S : ℝ}
theorem exists_nat_lt_coe_mul_eq {r : ℝ} {m : ℕ} (hm : 0 < m) (hS : S = 2 * m * r) (n : ℤ) :
    ∃ i : ℕ, i < 2 * m ∧ ((r * n : ℝ) : AddCircle S) = ((r * ((i : ℤ) : ℝ) : ℝ) : AddCircle S) := by
  have hM : (0 : ℤ) < 2 * m := by positivity
  have hnn := Int.emod_nonneg n hM.ne'
  have hlt := Int.emod_lt_of_pos n hM
  refine ⟨(n % (2 * m)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  have h0 : r * (n : ℝ) = r * ((n % (2 * m) : ℤ) : ℝ) + ((n / (2 * m) : ℤ) : ℝ) * S := by
    have h1 : (n : ℝ) = ((2 * m * (n / (2 * m)) + n % (2 * m) : ℤ) : ℝ) := by
      rw [Int.mul_ediv_add_emod]
    rw [hS]
    nth_rw 1 [h1]
    push_cast
    ring
  have hz : ((((n / (2 * m) : ℤ) : ℝ) * S : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n / (2 * m), by simp⟩
  rw [h0, AddCircle.coe_add, hz, add_zero]
theorem torusSupNorm_eq_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem supCube_eq_closedBall (r : ℝ) (y : Torus4 S) :
    supCube r y = closedBall y (r / 2) := by
  ext x
  simp only [supCube, mem_ofPred_eq, mem_closedBall, dist_eq_norm, torusSupNorm_eq_norm]
theorem isClosed_supCube (r : ℝ) (y : Torus4 S) : IsClosed (supCube r y) := by
  rw [supCube_eq_closedBall]
  exact isClosed_closedBall
theorem self_mem_supCube {r : ℝ} (hr : 0 ≤ r) (y : Torus4 S) : y ∈ supCube r y := by
  rw [supCube_eq_closedBall]
  exact mem_closedBall_self (by positivity)
theorem mem_spacingLattice_iff {r : ℝ} {x : Torus4 S} :
    x ∈ spacingLattice S r ↔ ∃ k : Fin 4 → ℤ, x = torusProj S fun μ => r * (k μ : ℝ) := Iff.rfl
theorem spacingLattice_finite {r : ℝ} (he : IsEvenMultipleOf S r) :
    (spacingLattice S r : Set (Torus4 S)).Finite := by
  obtain ⟨m, hm, hS⟩ := he
  refine (Set.finite_range fun g : Fin 4 → Fin (2 * m) =>
    torusProj S fun μ => r * (((g μ : ℕ) : ℤ) : ℝ)).subset ?_
  intro x hx
  obtain ⟨a, rfl⟩ := mem_spacingLattice_iff.1 hx
  choose i hi hi' using fun μ => exists_nat_lt_coe_mul_eq hm hS (a μ)
  exact ⟨fun μ => ⟨i μ, hi μ⟩, funext fun μ => (hi' μ).symm⟩
variable (D : ScaleData)
theorem shiftedPoint_apply {s : ℝ} (z : D.Space) (σ : Fin 4 → ℤ) (μ : Fin 4) :
    shiftedPoint D s z σ μ = z μ + ((s * (σ μ : ℝ) : ℝ) : AddCircle D.torusSide) := rfl
variable {D}
end GeneralTorus.CubePartitions
end
end YangMills.Construction
