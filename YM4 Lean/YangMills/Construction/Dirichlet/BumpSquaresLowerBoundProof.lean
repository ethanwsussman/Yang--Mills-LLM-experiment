import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
namespace YangMills.Construction.Dirichlet.BumpSquares
variable {d : ℕ} {S : ℝ}
theorem supNorm_torusProj_le (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem exists_lift_norm_lt (hsurj : Function.Surjective (torusProj d S)) {p : PeriodicTorus d S}
    {r : ℝ} (h : supNorm p < r) : ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ < r := by
  obtain ⟨v₀, hv₀⟩ := hsurj p
  have hne : ({r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖} : Set ℝ).Nonempty :=
    ⟨‖v₀‖, v₀, hv₀, rfl⟩
  obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨v, hv, hlt⟩
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
end YangMills.Construction.Dirichlet.BumpSquares
