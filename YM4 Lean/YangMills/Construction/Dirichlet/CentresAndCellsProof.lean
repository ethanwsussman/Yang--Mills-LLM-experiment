import YangMills.Construction.Dirichlet.CentresAndCells
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.CentresCellsProof
variable {d : ℕ} {S : ℝ}
theorem spacingLattice_finite {σ : ℝ} {N : ℕ} (hN : 0 < N) (hS : S = (N : ℝ) * σ) :
    ((spacingLattice d S σ : AddSubgroup (PeriodicTorus d S)) : Set (PeriodicTorus d S)).Finite := by
  refine (Set.finite_range fun r : Fin d → Fin N =>
    torusProj d S fun μ => (((r μ : ℕ) : ℝ)) * σ).subset ?_
  rintro x ⟨k, rfl⟩
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNp : (0 : ℤ) < N := by exact_mod_cast hN
  have hlt : ∀ μ, (k μ % (N : ℤ)).toNat < N := fun μ => by
    have h1 := Int.emod_nonneg (k μ) hNz
    have h2 := Int.emod_lt_of_pos (k μ) hNp
    omega
  refine ⟨fun μ => ⟨(k μ % (N : ℤ)).toNat, hlt μ⟩, ?_⟩
  funext μ
  have hcast : (((k μ % (N : ℤ)).toNat : ℕ) : ℤ) = k μ % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hNz)
  have hk : (k μ : ℝ) = (((k μ % (N : ℤ)).toNat : ℕ) : ℝ) + (N : ℝ) * ((k μ / (N : ℤ) : ℤ) : ℝ) := by
    have h := Int.emod_add_mul_ediv (k μ) (N : ℤ)
    rw [← hcast] at h
    exact_mod_cast h.symm
  have h0 : (((((k μ % (N : ℤ)).toNat : ℕ) : ℝ) * σ - (k μ : ℝ) * σ : ℝ) : AddCircle S) = 0 := by
    refine (AddCircle.coe_eq_zero_iff S).2 ⟨-(k μ / (N : ℤ)), ?_⟩
    rw [hk, zsmul_eq_mul, hS]
    push_cast
    ring
  exact show (((((k μ % (N : ℤ)).toNat : ℕ) : ℝ) * σ : ℝ) : AddCircle S) = ((k μ : ℝ) * σ : ℝ) from
    sub_eq_zero.1 (by rw [← AddCircle.coe_sub]; exact h0)
end YangMills.Construction.Dirichlet.CentresCellsProof
end
