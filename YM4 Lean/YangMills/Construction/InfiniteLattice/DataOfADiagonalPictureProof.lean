import YangMills.Construction.InfiniteLattice.ConeInequalityInTheLinkPictureProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace DiagonalPictureExpansion
open MirrorExpansions NormalHyperplane
theorem basisVector_apply_self (μ : Direction) : basisVector μ μ = 1 := by
  simp [basisVector]
theorem basisVector_apply_of_ne {μ ν : Direction} (h : μ ≠ ν) : basisVector ν μ = 0 := by
  simp [basisVector, h]
theorem euclidDot_basis_add_left (μ ν : Direction) (x : Point) :
    euclidDot (basisVector μ + basisVector ν) x = x μ + x ν := by apply _root_.YangMills.Construction.LatticeConventions.LinkConeProof.euclidDot_diagonal <;> assumption
theorem euclidNorm_sq_eq_selfDot (x : Point) : euclidNorm x ^ 2 = euclidDot x x := by
  have hnn : 0 ≤ euclidDot x x := Finset.sum_nonneg fun μ _ => mul_self_nonneg (x μ)
  rw [euclidNorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
theorem euclidDot_self_basis_add {μ ν : Direction} (hne : μ ≠ ν) :
    euclidDot (basisVector μ + basisVector ν) (basisVector μ + basisVector ν) = 2 := by
  rw [euclidDot_basis_add_left]
  simp only [Pi.add_apply, basisVector_apply_self, basisVector_apply_of_ne hne,
    basisVector_apply_of_ne hne.symm]
  norm_num
theorem euclidDot_smul_basis_add {μ ν : Direction} (hne : μ ≠ ν) (t : ℝ) :
    euclidDot (basisVector μ + basisVector ν) (t • (basisVector μ + basisVector ν)) = 2 * t := by
  rw [euclidDot_basis_add_left]
  simp only [Pi.smul_apply, Pi.add_apply, basisVector_apply_self, basisVector_apply_of_ne hne,
    basisVector_apply_of_ne hne.symm, smul_eq_mul]
  ring
theorem euclidDot_smul_basis_sub {μ ν : Direction} (hne : μ ≠ ν) (t : ℝ) :
    euclidDot (basisVector μ + basisVector ν) (t • (basisVector μ - basisVector ν)) = 0 := by
  rw [euclidDot_basis_add_left]
  simp only [Pi.smul_apply, Pi.sub_apply, basisVector_apply_self, basisVector_apply_of_ne hne,
    basisVector_apply_of_ne hne.symm, smul_eq_mul]
  ring
theorem smul_basisVector_mem (t : ℝ) (μ : Direction) :
    t • basisVector μ ∈ InfiniteLattice.latticeSubgroup t := by
  show ∃ k : Fin 4 → ℤ, ∀ ν, (t • basisVector μ) ν = (k ν : ℝ) * t
  refine ⟨Pi.single μ 1, fun ν => ?_⟩
  by_cases h : ν = μ
  · subst h
    simp [basisVector]
  · simp [basisVector, h]
theorem diagonal_isLatticeMirror {t : ℝ} {μ ν : Direction} (hne : μ ≠ ν) {c : ℝ}
    (hc : ∃ q : ℤ, c = (q : ℝ) * t) : (diagonal μ ν hne c).IsLatticeMirror t := by
  obtain ⟨q, hq⟩ := hc
  refine ⟨fun _ => ⟨2 * q, ?_⟩, fun _ => ⟨q, hq⟩⟩
  show c = _
  rw [hq]
  push_cast
  ring
theorem smul_isOutwardNormalStep {t : ℝ} (ht : 0 < t) {μ ν : Direction} (hne : μ ≠ ν)
    (c : ℝ) : (diagonal μ ν hne c).IsOutwardNormalStep t
      (t • (basisVector μ + basisVector ν)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_add]
    exact add_mem (smul_basisVector_mem t μ) (smul_basisVector_mem t ν)
  · show t • (basisVector μ + basisVector ν) -
        (2 * (euclidNorm (basisVector μ + basisVector ν) ^ 2)⁻¹ *
          euclidDot (basisVector μ + basisVector ν) (t • (basisVector μ + basisVector ν))) •
          (basisVector μ + basisVector ν) = -(t • (basisVector μ + basisVector ν))
    rw [euclidNorm_sq_eq_selfDot, euclidDot_self_basis_add hne, euclidDot_smul_basis_add hne]
    have hcoef : (2 * (2 : ℝ)⁻¹ * (2 * t)) = t + t := by ring
    rw [hcoef, add_smul]
    abel
  · show 0 < euclidDot (basisVector μ + basisVector ν) (t • (basisVector μ + basisVector ν))
    rw [euclidDot_smul_basis_add hne]
    positivity
theorem holds : DiagonalPictureExpansion.Statement := by
  intro t μ ν hne c hc
  have ht : 0 < (t : ℝ) := t.2
  have hL : (diagonal μ ν hne c).IsLatticeMirror (t : ℝ) :=
    diagonal_isLatticeMirror hne hc
  have hL' : (diagonal μ ν hne (c + (t : ℝ))).IsLatticeMirror (t : ℝ) := by
    obtain ⟨q, hq⟩ := hc
    refine diagonal_isLatticeMirror hne ⟨q + 1, ?_⟩
    rw [hq]
    push_cast
    ring
  have hstep := smul_isOutwardNormalStep ht hne c
  have hmid : (diagonal μ ν hne (c + (t : ℝ))).IsMidPlaneOf (t : ℝ)
      (diagonal μ ν hne c) ((t : ℝ) • (basisVector μ + basisVector ν)) := by
    refine ⟨hL, hstep, ?_⟩
    have hp : c + (t : ℝ) = c + 1 / 2 *
        euclidDot (basisVector μ + basisVector ν)
          ((t : ℝ) • (basisVector μ + basisVector ν)) := by
      rw [euclidDot_smul_basis_add hne]
      ring
    simp only [diagonal, midPlane, NormalHyperplane.mk.injEq, true_and]
    exact hp
  have hmem : (t : ℝ) • (basisVector μ - basisVector ν) ∈
      InfiniteLattice.latticeSubgroup (t : ℝ) := by
    rw [smul_sub]
    exact sub_mem (smul_basisVector_mem _ μ) (smul_basisVector_mem _ ν)
  exact
    { plane_normal := rfl
      midPlane_normal := rfl
      plane_isLatticeMirror := hL
      midPlane_isLatticeMirror := hL'
      normalStep_outward := hstep
      euclidDot_normalStep := euclidDot_smul_basis_add hne _
      midPlane_isMid := hmid
      tangentStep_mem := fun _ => hmem
      euclidDot_tangentStep := fun _ => euclidDot_smul_basis_sub hne _
      hyps :=
        { isMidPlane := hmid
          midPlane_isLatticeMirror := hL'
          one_le_card := by simp
          step_mem := fun _ => hmem
          euclidDot_step := fun _ => euclidDot_smul_basis_sub hne _ }
      card_eq := by simp }
end DiagonalPictureExpansion
end LatticeConventions
end YangMills.Construction
end
