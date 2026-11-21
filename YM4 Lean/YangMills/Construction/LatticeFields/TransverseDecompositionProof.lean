import YangMills.Construction.LatticeFields.MassiveLaplacianIdentities
import YangMills.Construction.LatticeFields.ProjGradDecayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.Transverse
variable {d : ℕ}
theorem finite_torusSites (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Operators
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem forwardDiff_add (μ : Fin d) (F G : LatticeField N κ I) :
    forwardDiff μ (F + G) = forwardDiff μ F + forwardDiff μ G := by
  funext x i
  simp only [forwardDiff, shiftForward, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring
theorem forwardDiff_smul (μ : Fin d) (c : ℝ) (F : LatticeField N κ I) :
    forwardDiff μ (c • F) = c • forwardDiff μ F := by
  funext x i
  simp only [forwardDiff, shiftForward, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring
theorem backwardDiff_add (μ : Fin d) (F G : LatticeField N κ I) :
    backwardDiff μ (F + G) = backwardDiff μ F + backwardDiff μ G := by
  funext x i
  simp only [backwardDiff, shiftBackward, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    smul_eq_mul]
  ring
theorem backwardDiff_smul (μ : Fin d) (c : ℝ) (F : LatticeField N κ I) :
    backwardDiff μ (c • F) = c • backwardDiff μ F := by
  funext x i
  simp only [backwardDiff, shiftBackward, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring
theorem tensorGrad_add {r : ℕ} (F G : LatticeTensor N κ r) :
    tensorGrad (F + G) = tensorGrad F + tensorGrad G := by
  funext x i
  simp only [tensorGrad, forwardDiff_add, Pi.add_apply]
theorem tensorGrad_smul {r : ℕ} (c : ℝ) (F : LatticeTensor N κ r) :
    tensorGrad (c • F) = c • tensorGrad F := by
  funext x i
  simp only [tensorGrad, forwardDiff_smul, Pi.smul_apply]
theorem tensorGradAdjoint_add {r : ℕ} (F G : LatticeTensor N κ (r + 1)) :
    tensorGradAdjoint (F + G) = tensorGradAdjoint F + tensorGradAdjoint G := by
  funext x i
  simp only [tensorGradAdjoint, backwardDiff_add, Pi.add_apply, Finset.sum_add_distrib]
theorem tensorGradAdjoint_smul {r : ℕ} (c : ℝ) (F : LatticeTensor N κ (r + 1)) :
    tensorGradAdjoint (c • F) = c • tensorGradAdjoint F := by
  funext x i
  simp only [tensorGradAdjoint, backwardDiff_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
theorem tensorLaplacian_add {r : ℕ} (F G : LatticeTensor N κ r) :
    tensorLaplacian (F + G) = tensorLaplacian F + tensorLaplacian G := by
  simp only [tensorLaplacian, tensorGrad_add, tensorGradAdjoint_add]
theorem tensorLaplacian_smul {r : ℕ} (c : ℝ) (F : LatticeTensor N κ r) :
    tensorLaplacian (c • F) = c • tensorLaplacian F := by
  simp only [tensorLaplacian, tensorGrad_smul, tensorGradAdjoint_smul]
theorem latticeGrad_eq_tensorGrad (f : ScalarField N κ) : latticeGrad f = tensorGrad f := by
  funext x i
  simp only [latticeGrad, tensorGrad]
  rw [Subsingleton.elim (Fin.tail i) scalarIndex]
theorem tensorLaplacian_eq_latticeDiv_latticeGrad (f : ScalarField N κ) :
    tensorLaplacian f = latticeDiv (latticeGrad f) := by apply _root_.YangMills.Construction.LatticeFields.ProjGradDecayProof.tensorLaplacian_eq_div_grad <;> assumption
def constField (c : ℝ) : ScalarField N κ := fun _ _ => c
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
variable [Finite (LatticeSite N κ)]
theorem fieldInner_sub_left [Finite I] (F F' G : LatticeField N κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by apply _root_.YangMills.SharedProofs.p65939 <;> assumption
theorem fieldInner_add_left [Finite I] (F F' G : LatticeField N κ I) :
    fieldInner (F + F') G = fieldInner F G + fieldInner F' G := by
  unfold fieldInner
  rw [← Summable.tsum_add Summable.of_finite Summable.of_finite]
  exact tsum_congr fun p => by simp only [Pi.add_apply]; ring
omit [Finite (LatticeSite N κ)] in
theorem fieldInner_smul_left (c : ℝ) (F G : LatticeField N κ I) :
    fieldInner (c • F) G = c * fieldInner F G := by
  unfold fieldInner
  rw [← tsum_mul_left]
  exact tsum_congr fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring
theorem eq_zero_of_fieldInner_self [NeZero N] [Finite I] (F : LatticeField N κ I)
    (h : fieldInner F F = 0) : F = 0 := by
  have := Fintype.ofFinite (LatticeSite N κ)
  have := Fintype.ofFinite I
  have hs : 0 < latticeSpacing N :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hc : 0 < latticeSpacing N ^ d := pow_pos hs d
  unfold fieldInner at h
  rw [tsum_fintype] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
    have := mul_nonneg hc.le (mul_self_nonneg (F p.1 p.2))
    linarith [mul_assoc (latticeSpacing N ^ d) (F p.1 p.2) (F p.1 p.2)])).mp h
  funext x i
  have hp := hz (x, i) (Finset.mem_univ _)
  simp only at hp
  have hq : latticeSpacing N ^ d * (F x i * F x i) = 0 := by rw [← mul_assoc]; exact hp
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hc.ne')
end Operators
section Connected
variable {N : ℕ} {κ : LatticeShape d}
end Connected
section Main
variable {N : ℕ} {κ : LatticeShape d} [NeZero N] [Finite (LatticeSite N κ)]
variable (hadj : TorusLaws.TorusAdjointProps N κ)
include hadj
end Main
end YangMills.Construction.LatticeFields.Transverse
