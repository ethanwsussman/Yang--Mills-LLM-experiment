import YangMills.Construction.TorusForms.BlocksCorridorsDomains
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open YangMills.Construction.Lattice
namespace CellDecomposition
theorem eq_of_sub_dvd_of_mem_window {q a t t' : ℤ} (ht : -a ≤ t ∧ t ≤ q - 1 - a)
    (ht' : -a ≤ t' ∧ t' ≤ q - 1 - a) (hd : q ∣ t - t') : t = t' := by
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega
theorem exists_mul_add_mem_window {q : ℤ} (a : ℤ) (hq : 0 < q) (t : ℤ) :
    ∃ s r : ℤ, (-a ≤ r ∧ r ≤ q - 1 - a) ∧ t = q * s + r := by
  have h0 := Int.emod_nonneg (t + a) hq.ne'
  have h1 := Int.emod_lt_of_pos (t + a) hq
  have h2 := Int.mul_ediv_add_emod (t + a) q
  exact ⟨(t + a) / q, (t + a) % q - a, ⟨by linarith, by linarith⟩, by linarith⟩
variable {d : ℕ} {F C E : Type*} [AddCommGroup F] [AddCommGroup C] [AddCommGroup E]
def InWindow (a q : ℤ) (σ : Fin d → ℤ) : Prop := ∀ μ, -a ≤ σ μ ∧ σ μ ≤ q - 1 - a
theorem InWindow.update {a q : ℤ} {σ : Fin d → ℤ} (h : InWindow a q σ) (μ : Fin d) {t : ℤ}
    (ht : -a ≤ t ∧ t ≤ q - 1 - a) : InWindow a q (Function.update σ μ t) := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    simpa using ht
  · simpa [Function.update_of_ne hν] using h ν
structure CommensurateGroups (Q : ℕ) (q a : ℤ) (e : (Fin d → ℤ) →+ F) (e' : (Fin d → ℤ) →+ C)
    (ι : C →+ F) (B : C → Set F) (s : Fin d → F) (s' : Fin d → C) : Prop where
  q_eq : (Q : ℤ) = q
  q_pos : 0 < q
  a_nonneg : 0 ≤ a
  a_le : a ≤ q - 1
  e_surj : Function.Surjective e
  e'_surj : Function.Surjective e'
  ι_inj : Function.Injective ι
  ι_e' : ∀ κ, ι (e' κ) = e (q • κ)
  ker : ∀ σ, e σ = 0 → ∀ μ, q ∣ σ μ
  s_eq : ∀ μ, s μ = e (Pi.single μ 1)
  s'_eq : ∀ μ, s' μ = e' (Pi.single μ 1)
  s'_ne : ∀ μ, s' μ ≠ 0
  mem_B : ∀ x y, x ∈ B y ↔ ∃ σ, InWindow a q σ ∧ x = ι y + e σ
namespace CommensurateGroups
variable {Q : ℕ} {q a : ℤ} {e : (Fin d → ℤ) →+ F} {e' : (Fin d → ℤ) →+ C} {ι : C →+ F}
  {B : C → Set F} {s : Fin d → F} {s' : Fin d → C}
theorem eq_of_add_eq_add (P : CommensurateGroups Q q a e e' ι B s s') {y y₂ : C} {σ σ₂ : Fin d → ℤ}
    (hσ : InWindow a q σ) (hσ₂ : InWindow a q σ₂) (h : ι y + e σ = ι y₂ + e σ₂) :
    y = y₂ ∧ σ = σ₂ := by
  obtain ⟨κ, hκ⟩ := P.e'_surj (y - y₂)
  have h1 : ι (y - y₂) = e (σ₂ - σ) := by
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : e (q • κ - (σ₂ - σ)) = 0 := by
    rw [map_sub, ← P.ι_e', hκ, h1, sub_self]
  have hσeq : σ = σ₂ := by
    funext μ
    have hd := P.ker _ h2 μ
    have hd' : q ∣ σ μ - σ₂ μ := by
      have h3 : (q • κ - (σ₂ - σ)) μ = q * κ μ + (σ μ - σ₂ μ) := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h3] at hd
      exact (dvd_add_right (dvd_mul_right _ _)).mp hd
    exact eq_of_sub_dvd_of_mem_window (hσ μ) (hσ₂ μ) hd'
  subst hσeq
  exact ⟨P.ι_inj (add_right_cancel h), rfl⟩
theorem exists_decomposition (P : CommensurateGroups Q q a e e' ι B s s') (x : F) :
    ∃ y σ, InWindow a q σ ∧ x = ι y + e σ := by
  obtain ⟨τ, rfl⟩ := P.e_surj x
  choose κ ρ hρ he using fun μ => exists_mul_add_mem_window a P.q_pos (τ μ)
  refine ⟨e' κ, ρ, hρ, ?_⟩
  rw [P.ι_e', ← map_add]
  congr 1
  funext μ
  simpa using he μ
theorem cell_unique (P : CommensurateGroups Q q a e e' ι B s s') {x : F} {y y₂ : C} (h : x ∈ B y)
    (h₂ : x ∈ B y₂) : y = y₂ := by
  obtain ⟨σ, hσ, hx⟩ := (P.mem_B x y).mp h
  obtain ⟨σ₂, hσ₂, hx₂⟩ := (P.mem_B x y₂).mp h₂
  exact (P.eq_of_add_eq_add hσ hσ₂ (hx.symm.trans hx₂)).1
theorem existsUnique_cell (P : CommensurateGroups Q q a e e' ι B s s') (x : F) : ∃! y, x ∈ B y := by
  obtain ⟨y, σ, hσ, hx⟩ := P.exists_decomposition x
  have hy : x ∈ B y := (P.mem_B x y).mpr ⟨σ, hσ, hx⟩
  exact ⟨y, hy, fun y₂ h₂ => P.cell_unique h₂ hy⟩
end CommensurateGroups
section
end
end CellDecomposition
end YangMills.Construction.BlockSpin
