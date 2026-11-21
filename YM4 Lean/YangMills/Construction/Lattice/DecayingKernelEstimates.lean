import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CombesThomas
open ScaledFun
variable {d N : ℕ}
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_self (u : Torus d N) : taxicabDist u u = 0 := by simp [taxicabDist]
theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  sum_nonneg fun _ _ => norm_nonneg _
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem summable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ => Real.exp (-a * |(n : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
section Entries
variable {s : Mesh N} {Y Y' Y'' : Type}
def evalLinear (x : Y) : ScaledFun d s Y →ₗ[ℝ] ℝ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem inner_basisVec [Fintype Y] (hs : s.h = 1) (p : Y) (f : ScaledFun d s Y) :
    inner ℝ (basisVec p : ScaledFun d s Y) f = f p := by
  classical
  rw [ScaledFun.inner_eq]
  simp only [basisVec, hs, one_pow, one_mul, ofMap_apply, ite_mul, zero_mul]
  exact (sum_eq_single p (fun b _ hb => if_neg hb) fun hp => absurd (mem_univ p) hp).trans
    (if_pos rfl)
theorem eq_sum_basisVec [Fintype Y] (f : ScaledFun d s Y) :
    f = ∑ r, f r • (basisVec r : ScaledFun d s Y) := by
  classical
  refine ScaledFun.ext fun x => ?_
  have hmap := map_sum (evalLinear (d := d) (s := s) x)
    (fun r => f r • (basisVec r : ScaledFun d s Y)) univ
  have hmap' : (∑ r, f r • (basisVec r : ScaledFun d s Y)) x =
      ∑ r, (f r • (basisVec r : ScaledFun d s Y)) x := hmap
  rw [hmap']
  simp only [smul_apply, basisVec, ofMap_apply, mul_ite, mul_one, mul_zero]
  exact ((sum_eq_single x (fun b _ hb => if_neg hb.symm) fun hx => absurd (mem_univ x) hx).trans
    (if_pos rfl)).symm
theorem apply_eq_sum_matrixEntry [Fintype Y] [Fintype Y'] (hs : s.h = 1)
    (U : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y) (f : ScaledFun d s Y') (x : Y) :
    U f x = ∑ y, matrixEntry U x y * f y := by
  have h1 : U f = ∑ r, f r • U (basisVec r) := by
    conv_lhs => rw [eq_sum_basisVec f]
    simp only [map_sum, map_smul]
  have h2 := map_sum (evalLinear (d := d) (s := s) x) (fun r => f r • U (basisVec r)) univ
  have h3 : (∑ r, f r • U (basisVec r)) x = ∑ r, (f r • U (basisVec r)) x := h2
  rw [h1, h3]
  refine sum_congr rfl fun r _ => ?_
  rw [matrixEntry, inner_basisVec hs, smul_apply, mul_comm]
theorem matrixEntry_comp [Fintype Y] [Fintype Y'] (hs : s.h = 1)
    (U₁ : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y) (U₂ : ScaledFun d s Y'' →ₗ[ℝ] ScaledFun d s Y')
    (p : Y) (q : Y'') :
    matrixEntry (U₁ ∘ₗ U₂) p q = ∑ r, matrixEntry U₁ p r * matrixEntry U₂ r q := by
  rw [matrixEntry, inner_basisVec hs, LinearMap.comp_apply, apply_eq_sum_matrixEntry hs]
  refine sum_congr rfl fun r _ => ?_
  have e : U₂ (basisVec q) r = matrixEntry U₂ r q := (inner_basisVec hs r _).symm
  rw [e]
theorem norm_sq_eq_sum [Fintype Y] (hs : s.h = 1) (u : ScaledFun d s Y) :
    ‖u‖ ^ 2 = ∑ x, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ScaledFun.inner_eq, hs]
  exact sum_congr rfl fun x _ => by simp [sq]
theorem abs_apply_le_norm [Fintype Y] (hs : s.h = 1) (u : ScaledFun d s Y) (p : Y) :
    |u p| ≤ ‖u‖ := by
  have hsq : u p ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_eq_sum hs]
    exact single_le_sum (f := fun x => u x ^ 2) (fun _ _ => sq_nonneg _) (mem_univ p)
  simpa [Real.sqrt_sq (norm_nonneg u)] using Real.abs_le_sqrt hsq
end Entries
section Composition
variable {s : Mesh N} {Y Y' Y'' : Type}
end Composition
section SubspaceInverse
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
end SubspaceInverse
section Conjugation
variable {s : Mesh N} {Y : Type} [Fintype Y]
theorem abs_exp_sub_one_le_mul_exp {x B : ℝ} (h : |x| ≤ B) :
    |Real.exp x - 1| ≤ B * Real.exp B := by
  have hB : 0 ≤ B := (abs_nonneg x).trans h
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h
    have h1 : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonneg (by linarith)]
    have h2 := Real.add_one_le_exp (-x)
    have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp x * (-x + 1) ≤ 1 :=
      (mul_le_mul_of_nonneg_left h2 (Real.exp_pos x).le).trans_eq h3
    have h5 : Real.exp x ≤ Real.exp B := Real.exp_le_exp.mpr h
    have h6 : x * Real.exp x ≤ B * Real.exp B :=
      mul_le_mul h h5 (Real.exp_pos x).le hB
    linarith
  · rw [abs_of_neg hx] at h
    have h1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
    rw [abs_of_neg (by linarith)]
    have h2 := Real.add_one_le_exp x
    have h3 : 1 ≤ Real.exp B := Real.one_le_exp hB
    nlinarith
end Conjugation
section Cells
variable {Y : Type} [Finite Y]
end Cells
section Decay
variable {s : Mesh N} {Y : Type} [Fintype Y] [HasSitePosition d s Y]
omit [Fintype Y] in
theorem posDist_comm (x y : Y) :
    posDist (d := d) (s := s) x y = posDist (d := d) (s := s) y x :=
  taxicabDist_comm _ _
omit [Fintype Y] in
theorem posDist_nonneg (x y : Y) : 0 ≤ posDist (d := d) (s := s) x y :=
  taxicabDist_nonneg _ _
end Decay
end YangMills.Construction.PeriodicLattice.CombesThomas
