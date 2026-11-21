import YangMills.Construction.RegionSequence.AvgOpWeightFormula
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus
namespace RegionSequence.AvgOpWeightSum
open NestedRegions
theorem finite_latticeSite {S σ : ℝ} (hσ : 0 < σ) (hS₀ : 0 < S) {N : ℤ} (hS : S = (N : ℝ) * σ) :
    Finite (LatticeSite 4 S σ) := by
  have hN : 0 < N := by
    have h₀ : (0 : ℝ) < (N : ℝ) * σ := hS ▸ hS₀
    have h₁ : (0 : ℝ) < (N : ℝ) := (pos_iff_pos_of_mul_pos h₀).2 hσ
    exact_mod_cast h₁
  let f : (Fin 4 → Fin N.toNat) → LatticeSite 4 S σ := fun a =>
    ⟨torusProj 4 S fun μ => ((((a μ : ℕ) : ℤ) : ℝ)) * σ, ⟨fun μ => ((a μ : ℕ) : ℤ), rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨_, a, rfl⟩
  have hnn : ∀ μ, 0 ≤ a μ % N := fun μ => Int.emod_nonneg _ hN.ne'
  refine ⟨fun μ => ⟨(a μ % N).toNat, ?_⟩, ?_⟩
  · have h₁ := Int.emod_lt_of_pos (a μ) hN
    have h₂ := hnn μ
    omega
  · apply Subtype.ext
    funext μ
    have h₁ : (((a μ % N).toNat : ℕ) : ℤ) = a μ % N := Int.toNat_of_nonneg (hnn μ)
    have h₂ : ((a μ % N : ℤ) : ℝ) + (N : ℝ) * ((a μ / N : ℤ) : ℝ) = a μ := by
      exact_mod_cast Int.emod_add_mul_ediv (a μ) N
    have h₃ : (a μ : ℝ) * σ = ((a μ % N : ℤ) : ℝ) * σ + (a μ / N : ℤ) • S := by
      rw [zsmul_eq_mul, hS]
      linear_combination (-σ) * h₂
    have h₄ : (((a μ / N : ℤ) • S : ℝ) : AddCircle S) = 0 :=
      (AddCircle.coe_eq_zero_iff S).2 ⟨_, rfl⟩
    show ((((((a μ % N).toNat : ℕ) : ℤ) : ℝ) * σ : ℝ) : AddCircle S) =
      (((a μ : ℝ) * σ : ℝ) : AddCircle S)
    rw [h₁, h₃, AddCircle.coe_add, h₄, add_zero]
theorem finite_latticeBond {S σ : ℝ} (h : Finite (LatticeSite 4 S σ)) :
    Finite (LatticeBond 4 S σ) := by
  refine Finite.of_injective (fun b : LatticeBond 4 S σ => (b.source, b.dir)) ?_
  rintro ⟨a, μ⟩ ⟨b, ν⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl
theorem scale_pos (𝒯 : NestedRegions) (j : ℕ) : 0 < 𝒯.scale j := by
  have hL : (0 : ℝ) < 𝒯.L := by
    have := 𝒯.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒯.L)
  exact mul_pos (zpow_pos hL _) 𝒯.ξ_pos
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by
  obtain ⟨k, hk⟩ := 𝒯.side_mem_zmultiples
  refine finite_latticeBond (finite_latticeSite 𝒯.ξ_pos 𝒯.side_pos
    (N := k * (2 * (𝒯.L : ℤ) ^ 𝒯.s)) ?_)
  rw [hk]
  simp only [scaleSpacing, zpow_natCast]
  push_cast
  ring
theorem finite_fineSite (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by
  obtain ⟨k, hk⟩ := 𝒯.side_mem_zmultiples
  refine finite_latticeSite 𝒯.ξ_pos 𝒯.side_pos (N := k * (2 * (𝒯.L : ℤ) ^ 𝒯.s)) ?_
  rw [hk]
  simp only [scaleSpacing, zpow_natCast]
  push_cast
  ring
end RegionSequence.AvgOpWeightSum
end YangMills.Construction
