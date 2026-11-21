import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
private theorem blockMomentLowerBound_pos (d : ℕ) : 0 < LatticeFields.blockMomentLowerBound d := by apply _root_.YangMills.SharedProofs.p223 <;> assumption
private def projComplRate (d : ℕ) : ℝ :=
  LatticeFields.blockMomentLowerBound d / (260 * ((d : ℝ) + 1) * (d : ℝ) ^ 3)
private def uniformRate (d : ℕ) : ℝ :=
  1 / 2 * min (LatticeFields.greenDecayConst d 1) (projComplRate d)
private def uniformConst (d : ℕ) : ℝ :=
  Real.exp (4 * (d : ℝ)) +
    4 * (LatticeFields.coerciveConst d 1)⁻¹ * Real.exp (6 * (d : ℝ)) *
      (1 + 4 * (d : ℝ) + 4 * Real.sqrt d +
        Real.sqrt d * (46 * (d : ℝ) ^ 2 * (LatticeFields.blockMomentLowerBound d)⁻¹) *
          latticeExpSum d (uniformRate d))
private theorem latticeExpSum_nonneg (d : ℕ) (δ : ℝ) : 0 ≤ latticeExpSum d δ := by
  unfold latticeExpSum
  exact mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg fun z => (Real.exp_pos _).le)
section Norms
variable {s : Mesh N} {X ι : Type}
private theorem scaledFun_norm_sq [Fintype X] (f : ScaledFun d s X) :
    ‖f‖ ^ 2 = ∑ x, s.h ^ d * f x * f x := by
  rw [← real_inner_self_eq_norm_sq, ScaledFun.inner_eq]
private theorem scaledFun_norm_le_of_abs_le [Fintype X] (f g : ScaledFun d s X) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, |f x| ≤ c * |g x|) : ‖f‖ ≤ c * ‖g‖ := by
  have hw := pow_pos s.h_pos d
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, scaledFun_norm_sq, scaledFun_norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h2 : f x * f x ≤ c ^ 2 * (g x * g x) := by
    have h1 := h x
    have h3 : |f x| * |f x| ≤ (c * |g x|) * (c * |g x|) :=
      mul_self_le_mul_self (abs_nonneg _) h1
    rw [abs_mul_abs_self] at h3
    have h4 : (c * |g x|) * (c * |g x|) = c ^ 2 * (|g x| * |g x|) := by ring
    rwa [h4, abs_mul_abs_self] at h3
  have h5 := mul_le_mul_of_nonneg_left h2 hw.le
  nlinarith
abbrev _root_.YangMills.SharedProofs.p51167 := @scaledFun_norm_le_of_abs_le
private theorem siteFun_maxNorm_nonneg (ζ : SiteFun d s) : 0 ≤ SiteFun.maxNorm ζ :=
  Real.iSup_nonneg fun _ => abs_nonneg _
private theorem siteFun_abs_le_maxNorm (ζ : SiteFun d s) (x : GridPoint d s) :
    |ζ x| ≤ SiteFun.maxNorm ζ :=
  le_ciSup (f := fun x => |ζ x|) (Set.finite_range _).bddAbove x
private theorem indicatorMul_apply (U : Set (GridPoint d s)) (f : MultiField d s ι) (q : ι × GridPoint d s) :
    MultiField.indicatorMul U f q = U.indicator 1 q.2 * f q := rfl
private theorem indicatorMul_of_mem {U : Set (GridPoint d s)} (f : MultiField d s ι) {q : ι × GridPoint d s}
    (h : q.2 ∈ U) : MultiField.indicatorMul U f q = f q := by
  rw [indicatorMul_apply, Set.indicator_of_mem h]
  simp
private theorem norm_mulLeft_le [Fintype ι] (ζ : SiteFun d s) (U : Set (GridPoint d s))
    (hζ : SiteFun.SupportedIn ζ U) (F : MultiField d s ι) :
    ‖MultiField.mulLeft ζ F‖ ≤ SiteFun.maxNorm ζ * ‖MultiField.indicatorMul U F‖ := by
  refine scaledFun_norm_le_of_abs_le _ _ _ (siteFun_maxNorm_nonneg ζ) fun q => ?_
  by_cases hq : q.2 ∈ U
  · rw [indicatorMul_of_mem F hq]
    change |ζ q.2 * F q| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (siteFun_abs_le_maxNorm ζ q.2) (abs_nonneg _)
  · change |ζ q.2 * F q| ≤ _
    rw [hζ q.2 hq]
    simpa using mul_nonneg (siteFun_maxNorm_nonneg ζ) (abs_nonneg _)
end Norms
private abbrev nearSites (s : Mesh N) (r : ℝ) (u : Torus d N) : Set (GridPoint d s) :=
  {x | maxDist (x : Torus d N) u ≤ r}
private theorem addCircle_norm_coe_le (hN : 0 < N) (x : ℝ) : ‖(x : AddCircle (N : ℝ))‖ ≤ |x| := by apply _root_.YangMills.SharedProofs.p53979 <;> assumption
private theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by
  unfold taxicabDist
  exact Finset.sum_congr rfl fun μ _ => norm_sub_rev _ _
abbrev _root_.YangMills.SharedProofs.p1021 := @taxicabDist_comm
private theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
private theorem taxicabDist_self (u : Torus d N) : taxicabDist u u = 0 := by
  simp [taxicabDist]
variable {L j : ℕ}
end YangMills.Construction.PeriodicLattice
