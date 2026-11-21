import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
namespace CubePlacement
variable {d : ℕ} {S : ℝ}
theorem supNorm_torusProj_le_norm (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem exists_lift_norm_eq_supNorm (hS : 0 < S) (p : PeriodicTorus d S) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ = supNorm p := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.exists_lift_norm_eq_supNorm <;> assumption
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem supNorm_sub_comm (hS : 0 < S) (p q : PeriodicTorus d S) :
    supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.supNorm_sub_comm <;> assumption
theorem isNatAtLeastTwo_of_isPosEvenNat {r : ℝ} (h : Torus.IsPosEvenNat r) :
    Torus.IsNatAtLeastTwo r := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.isNatAtLeastTwo_of_isPosEvenNat <;> assumption
end CubePlacement
end YangMills.Construction
