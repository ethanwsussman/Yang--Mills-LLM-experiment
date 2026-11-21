import YangMills.Construction.Torus.NeighborCountStatement
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
open YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Torus.NeighborCount
variable {d : ℕ} {S ξ : ℝ}
theorem addCircle_coe_ne_zero_of_lt {t : ℝ} (h0 : 0 < t) (h1 : t < S) : (t : AddCircle S) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h
  rw [zsmul_eq_mul] at hn
  have hn0 : 0 < n := by
    by_contra hc
    have hle : (n : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hc
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  nlinarith
def signedUnitStep (d : ℕ) (S ξ : ℝ) (a : Fin d × Bool) : LatticeSite d S ξ :=
  if a.2 then unitStep d S ξ a.1 else -unitStep d S ξ a.1
theorem signedUnitStep_apply (a : Fin d × Bool) (κ : Fin d) :
    ((signedUnitStep d S ξ a : LatticeSite d S ξ) : PeriodicTorus d S) κ =
      if κ = a.1 then cond a.2 (ξ : AddCircle S) (-ξ) else 0 := by
  obtain ⟨μ, b⟩ := a
  by_cases h : κ = μ
  · subst h
    cases b <;> simp [signedUnitStep, unitStep, torusProj]
  · cases b <;> simp [signedUnitStep, unitStep, torusProj, h]
theorem signedUnitStep_injective (h0 : 0 < ξ) (h1 : 2 * ξ < S) :
    Function.Injective (signedUnitStep d S ξ) := by
  have hξ : (ξ : AddCircle S) ≠ 0 := addCircle_coe_ne_zero_of_lt h0 (by linarith)
  have h2 : (ξ : AddCircle S) + ξ ≠ 0 := by
    have h := addCircle_coe_ne_zero_of_lt (S := S) (t := 2 * ξ) (by linarith) h1
    rwa [two_mul, AddCircle.coe_add] at h
  have hneg : -(ξ : AddCircle S) ≠ 0 := neg_ne_zero.2 hξ
  have hne : (ξ : AddCircle S) ≠ -ξ := fun h => h2 (eq_neg_iff_add_eq_zero.1 h)
  rintro ⟨μ, b⟩ ⟨ν, c⟩ h
  have hc : ∀ κ, (if κ = μ then cond b (ξ : AddCircle S) (-ξ) else 0) =
      if κ = ν then cond c (ξ : AddCircle S) (-ξ) else 0 := fun κ =>
    (signedUnitStep_apply (μ, b) κ).symm.trans
      ((congrArg (fun s : LatticeSite d S ξ => (s : PeriodicTorus d S) κ) h).trans
        (signedUnitStep_apply (ν, c) κ))
  by_cases hμ : μ = ν
  · subst hμ
    have hcμ := hc μ
    simp only [↓reduceIte] at hcμ
    cases b <;> cases c
    · rfl
    · exact absurd hcμ.symm hne
    · exact absurd hcμ hne
    · rfl
  · have hcμ := hc μ
    simp only [↓reduceIte, if_neg hμ] at hcμ
    cases b
    · exact absurd hcμ hneg
    · exact absurd hcμ hξ
theorem setOf_isNeighbor_eq_range (x : LatticeSite d S ξ) :
    {x' | IsNeighbor x x'} = range fun a => x + signedUnitStep d S ξ a := by
  ext x'
  constructor
  · rintro ⟨μ, rfl | rfl⟩
    · exact ⟨(μ, true), by simp [signedUnitStep]⟩
    · exact ⟨(μ, false), by simp [signedUnitStep, sub_eq_add_neg]⟩
  · rintro ⟨⟨μ, b⟩, rfl⟩
    cases b
    · exact ⟨μ, Or.inr (by simp [signedUnitStep, sub_eq_add_neg])⟩
    · exact ⟨μ, Or.inl (by simp [signedUnitStep])⟩
theorem neighborCountStatement_holds : NeighborCountStatement := by
  intro d S ξ h0 h1 x
  have hinj : Function.Injective fun a => x + signedUnitStep d S ξ a :=
    (add_right_injective x).comp (signedUnitStep_injective h0 h1)
  rw [setOf_isNeighbor_eq_range, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ,
    Nat.card_eq_fintype_card]
  simp [mul_comm]
end YangMills.Construction.Torus.NeighborCount
end
