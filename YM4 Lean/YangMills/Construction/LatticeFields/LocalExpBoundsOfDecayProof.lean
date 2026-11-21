import YangMills.Construction.LatticeFields.DifferenceIdentities
import YangMills.Construction.LatticeFields.SiteSetDecay
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields.LocalExpBoundsOfDecayProof
variable {d N : ℕ} {κ : LatticeShape d} {I I' : Type}
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem latticeSpacing_nonneg : 0 ≤ latticeSpacing N := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.latticeSpacing_nonneg <;> assumption
section Norms
variable [Finite (LatticeSite N κ)]
theorem summable_of_finite [Finite I] (g : LatticeSite N κ × I → ℝ) : Summable g := by
  have := Fintype.ofFinite (LatticeSite N κ × I)
  exact (hasSum_fintype g).summable
theorem fieldSquareSummable_of_finite [Finite I] (F : LatticeField N κ I) : FieldSquareSummable F :=
  summable_of_finite _
end Norms
theorem exp_neg_mul_le {δ a b k : ℝ} (hδ : 0 ≤ δ) (h : b - k ≤ a) :
    Real.exp (-δ * a) ≤ Real.exp (k * δ) * Real.exp (-δ * b) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith
theorem eta_pos (P : ScaleData) : 0 < P.η := by
  have : (0 : ℝ) < P.N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne P.N))
  change 0 < ((P.N : ℝ))⁻¹
  positivity
section Torus
variable {P : ScaleData} {ℓ : Fin P.d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
end Torus
end YangMills.Construction.LatticeFields.LocalExpBoundsOfDecayProof
