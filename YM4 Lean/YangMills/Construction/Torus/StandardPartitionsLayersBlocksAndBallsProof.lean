import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import YangMills.Construction.Torus.GivenSequenceOnTheTorusOfAnyDimensionProof
import YangMills.Construction.Torus.StandardPartitionsLayersBlocksAndBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric Filter Topology
namespace Weighted.CubeGeometry
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {v : Fin 4 → ℝ} (h : ∀ μ, |v μ| ≤ r) :
    ‖torusProj S v‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun μ => (addCircle_norm_coe_le_abs (v μ)).trans (h μ)
theorem exists_lift_abs_eq_norm {S : ℝ} (d : Torus4 S) :
    ∃ v, torusProj S v = d ∧ ∀ μ, |v μ| = ‖d μ‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.exists_torusProj_eq_abs_eq_norm <;> assumption
theorem exists_int_eq_add_mul_of_coe_eq {S a b : ℝ} (h : (a : AddCircle S) = b) :
    ∃ k : ℤ, a = b + k * S := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.exists_int_eq_add_mul_of_coe_eq <;> assumption
theorem coe_add_int_mul_eq {S : ℝ} (v : ℝ) (k : ℤ) : ((v + k * S : ℝ) : AddCircle S) = v := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.coe_add_int_mul_period <;> assumption
theorem exists_int_near_between {a b : ℤ} (hab : a ≤ b) {W t : ℝ} (hW : 0 < W)
    (h1 : (a : ℝ) * W - W / 2 ≤ t) (h2 : t ≤ (b : ℝ) * W + W / 2) :
    ∃ p : ℤ, a ≤ p ∧ p ≤ b ∧ |t - W * (p : ℝ)| ≤ W / 2 := by
  have hr := abs_sub_round (t / W)
  set r := round (t / W) with hrdef
  have hscale : ∀ p : ℤ, |t / W - (p : ℝ)| ≤ 1 / 2 → |t - W * (p : ℝ)| ≤ W / 2 := by
    intro p hp
    have : t - W * (p : ℝ) = (t / W - (p : ℝ)) * W := by field_simp
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  have hlo : (a : ℝ) - 1 / 2 ≤ t / W := by
    rw [le_div_iff₀ hW]; nlinarith
  have hhi : t / W ≤ (b : ℝ) + 1 / 2 := by
    rw [div_le_iff₀ hW]; nlinarith
  rw [abs_le] at hr
  by_cases hra : r < a
  · refine ⟨a, le_rfl, hab, hscale a ?_⟩
    have : (r : ℝ) + 1 ≤ a := by exact_mod_cast hra
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  by_cases hrb : b < r
  · refine ⟨b, hab, le_rfl, hscale b ?_⟩
    have : (b : ℝ) + 1 ≤ r := by exact_mod_cast hrb
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  · exact ⟨r, not_lt.1 hra, not_lt.1 hrb, hscale r (abs_le.2 hr)⟩
theorem exists_int_near {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : ∃ p : ℤ, |t - σ * (p : ℝ)| ≤ σ / 2 := by
  refine ⟨round (t / σ), ?_⟩
  have hr := abs_sub_round (t / σ)
  have : t - σ * (round (t / σ) : ℝ) = (t / σ - (round (t / σ) : ℝ)) * σ := by
    field_simp
  rw [this, abs_mul, abs_of_pos hσ]
  nlinarith
def EvenMultiple (S σ : ℝ) : Prop := 0 < σ ∧ ∃ N : ℤ, Even N ∧ 0 < N ∧ S = N * σ
section Circle
variable {S σ : ℝ}
theorem EvenMultiple.two_mul_le (h : EvenMultiple S σ) : 2 * σ ≤ S := by
  obtain ⟨hσ, N, ⟨r, rfl⟩, hN, rfl⟩ := h
  have : (1 : ℤ) ≤ r := by omega
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast this
  push_cast
  nlinarith
theorem EvenMultiple.pos (h : EvenMultiple S σ) : 0 < S := by
  have := h.two_mul_le
  linarith [h.1]
def gridCircle (S σ : ℝ) : Set (AddCircle S) :=
  {a | ∃ k : ℤ, a = ((σ * (k : ℝ) : ℝ) : AddCircle S)}
theorem EvenMultiple.exists_int_of_mem_grid (h : EvenMultiple S σ) {a : AddCircle S}
    (ha : a ∈ gridCircle S σ) {v : ℝ} (hv : (v : AddCircle S) = a) :
    ∃ l : ℤ, v = σ * (l : ℝ) := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨j, hj⟩ := exists_int_eq_add_mul_of_coe_eq hv
  obtain ⟨-, N, -, -, hS⟩ := h
  refine ⟨k + j * N, ?_⟩
  rw [hj, hS]
  push_cast
  ring
theorem sub_mem_gridCircle {a b : AddCircle S} (ha : a ∈ gridCircle S σ)
    (hb : b ∈ gridCircle S σ) : a - b ∈ gridCircle S σ := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  refine ⟨k - l, ?_⟩
  rw [← AddCircle.coe_sub]
  congr 1
  push_cast
  ring
theorem EvenMultiple.le_norm_sub (h : EvenMultiple S σ) {a b : AddCircle S}
    (ha : a ∈ gridCircle S σ) (hb : b ∈ gridCircle S σ) (hab : a ≠ b) : σ ≤ ‖a - b‖ := by
  obtain ⟨v, hv, hv'⟩ := exists_coe_eq_abs_eq_norm (a - b)
  obtain ⟨l, rfl⟩ := h.exists_int_of_mem_grid (sub_mem_gridCircle ha hb) hv
  have hσ := h.1
  have hl : l ≠ 0 := by
    rintro rfl
    apply hab
    have : a - b = 0 := by rw [← hv]; simp
    exact sub_eq_zero.1 this
  rw [← hv', abs_mul, abs_of_pos hσ]
  have : (1 : ℝ) ≤ |(l : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |l| := Int.one_le_abs hl
    exact_mod_cast h1
  nlinarith
end Circle
section Balls
variable {S σ : ℝ}
theorem interior_closedBall_half_eq_ball (h : EvenMultiple S σ) (y : Torus4 S) :
    interior (Metric.closedBall y (σ / 2)) = Metric.ball y (σ / 2) := by
  have hσ := h.1
  have hS := h.two_mul_le
  have hS0 := h.pos
  apply Subset.antisymm _ (interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball)
  intro x hx
  have hx' := interior_subset hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx'
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff (by positivity)]
  intro μ
  by_contra hμ
  push Not at hμ
  have hμ' : ‖(x - y) μ‖ = σ / 2 := le_antisymm ((norm_le_pi_norm _ μ).trans hx') hμ
  obtain ⟨w, hw, hw'⟩ := exists_coe_eq_abs_eq_norm ((x - y) μ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * σ ≤ δ := by
    refine ⟨min 1 (δ / σ), lt_min one_pos (div_pos hδ hσ), min_le_left _ _, ?_⟩
    have := min_le_right 1 (δ / σ)
    rwa [le_div_iff₀ hσ] at this
  have habs : |w| = σ / 2 := by rw [hw', hμ']
  set x' : Torus4 S := x + Pi.single μ ((ε * w : ℝ) : AddCircle S) with hx'def
  have hin : x' ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : x' - x = Pi.single μ ((ε * w : ℝ) : AddCircle S) := by simp [hx'def]
    rw [this, Pi.norm_single]
    refine (addCircle_norm_coe_le_abs _).trans_lt ?_
    rw [abs_mul, abs_of_pos hε0, habs]
    nlinarith
  have hin' := hball hin
  rw [Metric.mem_closedBall, dist_eq_norm] at hin'
  have hcoord : (x' - y) μ = (((1 + ε) * w : ℝ) : AddCircle S) := by
    have h1 : (x' - y) μ = (x - y) μ + ((ε * w : ℝ) : AddCircle S) := by
      simp [hx'def, sub_eq_add_neg]
      abel
    rw [h1, ← hw, ← AddCircle.coe_add]
    congr 1
    ring
  have hsmall : |(1 + ε) * w| ≤ |S| / 2 := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + ε), habs, abs_of_pos hS0]
    nlinarith
  have hnorm := (AddCircle.norm_coe_eq_abs_iff S hS0.ne').2 hsmall
  have hle := (norm_le_pi_norm (x' - y) μ).trans hin'
  rw [hcoord, hnorm, abs_mul, abs_of_pos (by linarith : 0 < 1 + ε), habs] at hle
  nlinarith
theorem continuous_ray {S : ℝ} (y : Torus4 S) (w : Fin 4 → ℝ) :
    Continuous fun t : ℝ => y + torusProj S fun μ => t * w μ := by
  refine continuous_const.add (continuous_pi fun μ => ?_)
  exact (AddCircle.continuous_mk' S).comp (continuous_id.mul continuous_const)
theorem closure_ball_half_eq_closedBall (hσ : 0 < σ) (y : Torus4 S) :
    closure (Metric.ball y (σ / 2)) = Metric.closedBall y (σ / 2) := by
  apply Subset.antisymm (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  obtain ⟨w, hw, hw'⟩ := exists_lift_abs_eq_norm (x - y)
  have hf := continuous_ray y w
  have h1 : (y + torusProj S fun μ => (1 : ℝ) * w μ) = x := by
    simp only [one_mul]
    have : (torusProj S fun μ => w μ) = x - y := hw
    rw [this]
    abel
  have ht : Tendsto (fun t : ℝ => y + torusProj S fun μ => t * w μ) (𝓝[<] 1) (𝓝 x) := by
    have := hf.continuousAt (x := 1)
    rw [ContinuousAt, h1] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t htt
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : (y + torusProj S fun μ => t * w μ) - y = torusProj S fun μ => t * w μ := by abel
  rw [hsub]
  have hb : ‖torusProj S fun μ => t * w μ‖ ≤ t * (σ / 2) := by
    refine norm_torusProj_le (mul_nonneg htt.1.le (by positivity)) fun μ => ?_
    rw [abs_mul, abs_of_pos htt.1, hw' μ]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ μ).trans hx) htt.1.le
  have := htt.2
  nlinarith
end Balls
namespace Cube
variable {D : TorusData} {σ : ℝ}
theorem cubeAround_eq_closedBall (y : D.Space) : D.cubeAround σ y = Metric.closedBall y (σ / 2) := by
  ext x
  simp [TorusData.cubeAround, dist_eq_norm, torusSupNorm_eq_norm]
theorem mem_latticeAt_iff {x : D.Space} :
    x ∈ D.latticeAt σ ↔ ∀ μ, x μ ∈ gridCircle D.side σ := by
  constructor
  · rintro ⟨k, rfl⟩ μ
    exact ⟨k μ, rfl⟩
  · intro h
    choose k hk using h
    exact ⟨k, funext hk⟩
theorem interior_cubeAround (h : EvenMultiple D.side σ) (y : D.Space) :
    interior (D.cubeAround σ y) = Metric.ball y (σ / 2) := by
  rw [cubeAround_eq_closedBall, interior_closedBall_half_eq_ball h]
theorem closure_interior_cubeAround (h : EvenMultiple D.side σ) (y : D.Space) :
    closure (interior (D.cubeAround σ y)) = D.cubeAround σ y := by
  rw [interior_cubeAround h, closure_ball_half_eq_closedBall h.1, cubeAround_eq_closedBall]
theorem center_mem_ball (h : EvenMultiple D.side σ) (y : D.Space) : y ∈ Metric.ball y (σ / 2) :=
  Metric.mem_ball_self (by have := h.1; positivity)
theorem center_mem_cubeAround (h : EvenMultiple D.side σ) (y : D.Space) :
    y ∈ D.cubeAround σ y := by
  rw [cubeAround_eq_closedBall]
  exact Metric.ball_subset_closedBall (center_mem_ball h y)
theorem disjoint_ball_cubeAround (h : EvenMultiple D.side σ) {y y' : D.Space}
    (hy : y ∈ D.latticeAt σ) (hy' : y' ∈ D.latticeAt σ) (hne : y ≠ y') :
    Disjoint (Metric.ball y (σ / 2)) (D.cubeAround σ y') := by
  rw [cubeAround_eq_closedBall, Set.disjoint_left]
  intro x hx hx'
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx'
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hne
  have h1 := h.le_norm_sub (mem_latticeAt_iff.1 hy μ) (mem_latticeAt_iff.1 hy' μ) hμ
  have h2 : ‖(x - y) μ‖ < σ / 2 := (norm_le_pi_norm _ μ).trans_lt hx
  have h3 : ‖(x - y') μ‖ ≤ σ / 2 := (norm_le_pi_norm _ μ).trans hx'
  have h4 : y μ - y' μ = (x - y') μ - (x - y) μ := by simp
  rw [h4] at h1
  have := norm_sub_le ((x - y') μ) ((x - y) μ)
  linarith
theorem cubeAround_inj (h : EvenMultiple D.side σ) {y y' : D.Space}
    (hy : y ∈ D.latticeAt σ) (hy' : y' ∈ D.latticeAt σ)
    (he : D.cubeAround σ y = D.cubeAround σ y') : y = y' := by
  by_contra hne
  have := disjoint_ball_cubeAround h hy hy' hne
  rw [← he, cubeAround_eq_closedBall] at this
  exact Set.disjoint_left.1 this (center_mem_ball h y)
    (Metric.ball_subset_closedBall (center_mem_ball h y))
theorem exists_mem_cubeAround (h : EvenMultiple D.side σ) (x : D.Space) :
    ∃ y ∈ D.latticeAt σ, x ∈ D.cubeAround σ y := by
  obtain ⟨v, rfl, -⟩ := exists_lift_abs_eq_norm x
  have hσ := h.1
  choose k hk using fun μ => exists_int_near hσ (v μ)
  refine ⟨torusProj D.side fun μ => σ * (k μ : ℝ), ⟨k, rfl⟩, ?_⟩
  rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  have : (torusProj D.side v - torusProj D.side fun μ => σ * (k μ : ℝ)) μ =
      ((v μ - σ * (k μ : ℝ) : ℝ) : AddCircle D.side) := by
    simp [torusProj]
  rw [this]
  exact (addCircle_norm_coe_le_abs _).trans (hk μ)
theorem latticeAt_finite (h : EvenMultiple D.side σ) : (D.latticeAt σ).Finite := by
  obtain ⟨hσ, N, -, hN, hS⟩ := h
  have hfin : (Set.pi univ fun _ : Fin 4 => Set.Icc (0 : ℤ) N).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hfin.image fun k : Fin 4 → ℤ => torusProj D.side fun μ => σ * (k μ : ℝ)).subset ?_
  rintro x ⟨k, rfl⟩
  refine ⟨fun μ => k μ % N, ?_, ?_⟩
  · intro μ _
    exact ⟨Int.emod_nonneg _ hN.ne', (Int.emod_lt_of_pos _ hN).le⟩
  · funext μ
    have hk : (k μ : ℝ) = ((k μ % N : ℤ) : ℝ) + (N : ℝ) * ((k μ / N : ℤ) : ℝ) := by
      have := Int.emod_add_mul_ediv (k μ) N
      exact_mod_cast this.symm
    have : σ * (k μ : ℝ) = σ * ((k μ % N : ℤ) : ℝ) + ((k μ / N : ℤ) : ℝ) * D.side := by
      rw [hS, hk]
      ring
    simp only [torusProj]
    rw [this, coe_add_int_mul_eq]
end Cube
namespace Cube
variable {D : TorusData} {σ σ' : ℝ}
theorem isClosed_sUnion_of_subset_partition (h : EvenMultiple D.side σ) {C : Set (Set D.Space)}
    (hC : C ⊆ D.partitionAt σ) : IsClosed (⋃₀ C) := by
  rw [sUnion_eq_biUnion]
  refine Set.Finite.isClosed_biUnion (((latticeAt_finite h).image _).subset hC) fun β hβ => ?_
  obtain ⟨y, -, rfl⟩ := hC hβ
  rw [cubeAround_eq_closedBall]
  exact Metric.isClosed_closedBall
theorem add_mem_latticeAt {x y : D.Space} (hx : x ∈ D.latticeAt σ)
    (hy : y ∈ D.latticeAt σ) : x + y ∈ D.latticeAt σ := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  refine ⟨k + l, ?_⟩
  funext μ
  simp only [torusProj, Pi.add_apply, ← AddCircle.coe_add]
  congr 1
  push_cast
  ring
theorem sub_mem_latticeAt {x y : D.Space} (hx : x ∈ D.latticeAt σ)
    (hy : y ∈ D.latticeAt σ) : x - y ∈ D.latticeAt σ :=
  mem_latticeAt_iff.2 fun μ =>
    sub_mem_gridCircle (mem_latticeAt_iff.1 hx μ) (mem_latticeAt_iff.1 hy μ)
theorem inUniqueCubeInterior_torusProj (h : EvenMultiple D.side σ) {v : Fin 4 → ℝ}
    (hv : ∀ μ, v μ ∉ faceCoords σ) : D.InUniqueCubeInterior σ (torusProj D.side v) := by
  have hσ := h.1
  choose k hk using fun μ => exists_int_near hσ (v μ)
  have hlt : ∀ μ, |v μ - σ * (k μ : ℝ)| < σ / 2 := by
    intro μ
    refine lt_of_le_of_ne (hk μ) fun he => hv μ ?_
    rcases (abs_eq (by positivity)).1 he with h1 | h1
    · exact ⟨k μ, by linarith⟩
    · exact ⟨k μ - 1, by push_cast; linarith⟩
  have hy : (torusProj D.side fun μ => σ * (k μ : ℝ)) ∈ D.latticeAt σ := ⟨k, rfl⟩
  have hball : torusProj D.side v ∈
      Metric.ball (torusProj D.side fun μ => σ * (k μ : ℝ)) (σ / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff (by positivity)]
    intro μ
    have : (torusProj D.side v - torusProj D.side fun μ => σ * (k μ : ℝ)) μ =
        ((v μ - σ * (k μ : ℝ) : ℝ) : AddCircle D.side) := by
      simp [torusProj]
    rw [this]
    exact (addCircle_norm_coe_le_abs _).trans_lt (hlt μ)
  refine ⟨_, ⟨_, hy, rfl⟩, ?_, ?_⟩
  · rw [interior_cubeAround h]
    exact hball
  · rintro _ ⟨y', hy', rfl⟩ hx
    by_contra hne
    have hne' : (torusProj D.side fun μ => σ * (k μ : ℝ)) ≠ y' := fun e => hne (by rw [e])
    exact Set.disjoint_left.1 (disjoint_ball_cubeAround h hy hy' hne') hball hx
theorem partitionFacts (h : EvenMultiple D.side σ) : D.PartitionFacts σ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, N, hE, -, hS⟩ := h
    exact ⟨N, hE, hS⟩
  · intro v hv
    refine ⟨?_, inUniqueCubeInterior_torusProj h hv⟩
    intro w hw μ hwμ
    apply hv μ
    have hc : ((w μ : ℝ) : AddCircle D.side) = v μ := congrFun hw μ
    obtain ⟨j, hj⟩ := exists_int_eq_add_mul_of_coe_eq hc
    obtain ⟨k, hk⟩ := hwμ
    obtain ⟨-, N, -, -, hS⟩ := h
    refine ⟨k - j * N, ?_⟩
    have : v μ = w μ - j * D.side := by linarith
    rw [this, hk, hS]
    push_cast
    ring
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨closure_interior_cubeAround h y, ?_⟩
    rintro _ ⟨y', hy', rfl⟩ hne
    rw [interior_cubeAround h]
    exact disjoint_ball_cubeAround h hy hy' (fun e => hne (by rw [e]))
theorem disjoint_interior_sUnion_of_not_mem (h : EvenMultiple D.side σ) {β : Set D.Space}
    (hβ : β ∈ D.partitionAt σ) {E : Set (Set D.Space)} (hE : E ⊆ D.partitionAt σ)
    (hn : β ∉ E) : Disjoint (interior β) (⋃₀ E) := by
  rw [Set.disjoint_sUnion_right]
  intro β' hβ'
  exact ((partitionFacts h).2.2 β hβ).2 β' (hE hβ') fun e => hn (e ▸ hβ')
theorem closedComplement_sUnion_eq (h : EvenMultiple D.side σ) {C : Set (Set D.Space)}
    (hC : C ⊆ D.partitionAt σ) :
    D.closedComplement (⋃₀ C) = ⋃₀ (D.partitionAt σ \ C) := by
  apply Subset.antisymm
  · refine closure_minimal ?_ (isClosed_sUnion_of_subset_partition h sdiff_subset)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_mem_cubeAround h x
    exact ⟨_, ⟨⟨y, hy, rfl⟩, fun hm => hx ⟨_, hm, hxy⟩⟩, hxy⟩
  · rintro x ⟨β, ⟨hβ, hn⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := hβ
    rw [← closure_interior_cubeAround h y] at hx
    refine closure_mono ?_ hx
    intro z hz hz'
    exact Set.disjoint_left.1
      (disjoint_interior_sUnion_of_not_mem h ⟨y, hy, rfl⟩ hC hn) hz hz'
theorem interior_nonempty_of_mem (h : EvenMultiple D.side σ) {β : Set D.Space}
    (hβ : β ∈ D.partitionAt σ) : (interior β).Nonempty := by
  obtain ⟨y, -, rfl⟩ := hβ
  exact ⟨y, by rw [interior_cubeAround h]; exact center_mem_ball h y⟩
section TwoSides
variable {p : ℕ}
theorem EvenMultiple.of_odd_mul (h' : EvenMultiple D.side σ') (hσ : 0 < σ)
    (hq : σ' = (2 * (p : ℝ) + 1) * σ) : EvenMultiple D.side σ := by
  obtain ⟨-, N, hE, hN, hS⟩ := h'
  refine ⟨hσ, N * (2 * p + 1), hE.mul_right _, by positivity, ?_⟩
  rw [hS, hq]
  push_cast
  ring
theorem latticeAt_subset_of_odd (hq : σ' = (2 * (p : ℝ) + 1) * σ) :
    D.latticeAt σ' ⊆ D.latticeAt σ := by
  rintro x ⟨k, rfl⟩
  refine ⟨fun μ => (2 * p + 1) * k μ, ?_⟩
  funext μ
  simp only [torusProj, hq]
  congr 1
  push_cast
  ring
theorem norm_sub_le_mul_of_mem (h : EvenMultiple D.side σ) (hq : σ' = (2 * (p : ℝ) + 1) * σ)
    {y y₀ : D.Space} (hy : y ∈ D.latticeAt σ) (hy₀ : y₀ ∈ D.latticeAt σ')
    (hn : ‖y - y₀‖ ≤ σ' / 2) : ‖y - y₀‖ ≤ (p : ℝ) * σ := by
  have hσ := h.1
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  have hmem := mem_latticeAt_iff.1 (sub_mem_latticeAt hy (latticeAt_subset_of_odd hq hy₀)) μ
  obtain ⟨w, hw, hw'⟩ := exists_coe_eq_abs_eq_norm ((y - y₀) μ)
  obtain ⟨l, rfl⟩ := h.exists_int_of_mem_grid hmem hw
  rw [← hw', abs_mul, abs_of_pos hσ]
  have h1 : σ * |(l : ℝ)| ≤ (2 * (p : ℝ) + 1) * σ / 2 := by
    rw [abs_mul, abs_of_pos hσ] at hw'
    rw [hw', ← hq]
    exact (norm_le_pi_norm _ μ).trans hn
  have h2 : 2 * |(l : ℝ)| ≤ 2 * (p : ℝ) + 1 := by
    have : σ * (2 * |(l : ℝ)|) ≤ σ * (2 * (p : ℝ) + 1) := by linarith
    exact le_of_mul_le_mul_left this hσ
  have h3 : 2 * |l| ≤ 2 * (p : ℤ) + 1 := by exact_mod_cast h2
  have h4 : |l| ≤ (p : ℤ) := by omega
  have h5 : |(l : ℝ)| ≤ (p : ℝ) := by exact_mod_cast h4
  nlinarith
theorem cubeAround_subset_cubeAround (hq : σ' = (2 * (p : ℝ) + 1) * σ) {y y₀ : D.Space}
    (hn : ‖y - y₀‖ ≤ (p : ℝ) * σ) : D.cubeAround σ y ⊆ D.cubeAround σ' y₀ := by
  rw [cubeAround_eq_closedBall, cubeAround_eq_closedBall]
  refine Metric.closedBall_subset_closedBall' ?_
  rw [dist_eq_norm, hq]
  linarith
theorem refinementFacts (h' : EvenMultiple D.side σ') (hσ : 0 < σ)
    (hq : σ' = (2 * (p : ℝ) + 1) * σ) : D.RefinementFacts σ σ' := by
  have h : EvenMultiple D.side σ := EvenMultiple.of_odd_mul h' hσ hq
  have hface : faceCoords σ' ⊆ faceCoords σ := by
    rintro a ⟨k, rfl⟩
    refine ⟨(2 * p + 1) * k + p, ?_⟩
    rw [hq]
    push_cast
    ring
  have hsite : ∀ x ∈ D.latticeAt σ, D.InUniqueCubeInterior σ' x := by
    rintro x ⟨k, rfl⟩
    apply inUniqueCubeInterior_torusProj h'
    intro μ hμ
    obtain ⟨l, hl⟩ := hface hμ
    have h1 : (k μ : ℝ) = (l : ℝ) + 1 / 2 := mul_left_cancel₀ hσ.ne' hl
    have h2 : 2 * (k μ : ℝ) = 2 * (l : ℝ) + 1 := by linarith
    have h3 : 2 * k μ = 2 * l + 1 := by exact_mod_cast h2
    omega
  have hone : ∀ β ∈ D.partitionAt σ, ∃! β', β' ∈ D.partitionAt σ' ∧ β ⊆ β' := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hin, huniq⟩ := hsite y hy
    have hn : ‖y - y₀‖ ≤ σ' / 2 := by
      have := interior_subset hin
      rwa [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm] at this
    refine ⟨_, ⟨⟨y₀, hy₀, rfl⟩,
      cubeAround_subset_cubeAround hq (norm_sub_le_mul_of_mem h hq hy hy₀ hn)⟩, ?_⟩
    rintro β'' ⟨hβ'', hs⟩
    exact huniq β'' hβ'' (hs (center_mem_cubeAround h y))
  have hunion : ∀ β' ∈ D.partitionAt σ',
      β' = ⋃₀ {β ∈ D.partitionAt σ | β ⊆ β'} := by
    rintro _ ⟨y₀, hy₀, rfl⟩
    apply Subset.antisymm
    · intro x hx
      rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm] at hx
      obtain ⟨w, hw, hw'⟩ := exists_lift_abs_eq_norm (x - y₀)
      have hbound : ∀ μ, |w μ| ≤ (p : ℝ) * σ + σ / 2 := fun μ => by
        rw [hw' μ]
        refine (norm_le_pi_norm _ μ).trans (hx.trans (le_of_eq ?_))
        rw [hq]
        ring
      have hg : ∀ μ, ∃ l : ℤ, -(p : ℤ) ≤ l ∧ l ≤ p ∧ |w μ - σ * (l : ℝ)| ≤ σ / 2 := fun μ => by
        have := abs_le.1 (hbound μ)
        refine exists_int_near_between (by omega) hσ ?_ ?_
        · push_cast
          linarith [this.1]
        · push_cast
          linarith [this.2]
      choose l hl1 hl2 hl3 using hg
      have hyl : (torusProj D.side fun μ => σ * (l μ : ℝ)) ∈ D.latticeAt σ := ⟨l, rfl⟩
      have hy : y₀ + (torusProj D.side fun μ => σ * (l μ : ℝ)) ∈ D.latticeAt σ :=
        add_mem_latticeAt (latticeAt_subset_of_odd hq hy₀) hyl
      refine ⟨D.cubeAround σ (y₀ + torusProj D.side fun μ => σ * (l μ : ℝ)),
        ⟨⟨_, hy, rfl⟩, ?_⟩, ?_⟩
      · refine cubeAround_subset_cubeAround hq ?_
        rw [add_sub_cancel_left]
        refine norm_torusProj_le (by positivity) fun μ => ?_
        rw [abs_mul, abs_of_pos hσ, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ hσ.le
        have : |l μ| ≤ (p : ℤ) := abs_le.2 ⟨hl1 μ, hl2 μ⟩
        exact_mod_cast this
      · rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm]
        have hsub : x - (y₀ + torusProj D.side fun μ => σ * (l μ : ℝ)) =
            torusProj D.side fun μ => w μ - σ * (l μ : ℝ) := by
          funext μ
          have h1 : (x - y₀) μ = ((w μ : ℝ) : AddCircle D.side) := (congrFun hw μ).symm
          have h2 : x μ - y₀ μ = ((w μ : ℝ) : AddCircle D.side) := h1
          simp only [Pi.sub_apply, Pi.add_apply, torusProj, AddCircle.coe_sub]
          rw [← h2]
          abel
        rw [hsub]
        exact norm_torusProj_le (by positivity) hl3
    · exact sUnion_subset fun β hβ => hβ.2
  refine ⟨hface, hsite, hone, hunion, ?_⟩
  rintro _ ⟨C, hC, rfl⟩
  have hrefine : ∀ E : Set (Set D.Space), E ⊆ D.partitionAt σ' →
      D.IsCubeUnionAt σ (⋃₀ E) := by
    intro E hE
    refine ⟨{β ∈ D.partitionAt σ | ∃ β' ∈ E, β ⊆ β'}, sep_subset _ _, ?_⟩
    apply Subset.antisymm
    · rintro x ⟨β', hβ', hx⟩
      rw [hunion β' (hE hβ')] at hx
      obtain ⟨β, ⟨hβ, hs⟩, hx⟩ := hx
      exact ⟨β, ⟨hβ, β', hβ', hs⟩, hx⟩
    · rintro x ⟨β, ⟨-, β', hβ', hs⟩, hx⟩
      exact ⟨β', hβ', hs hx⟩
  rw [closedComplement_sUnion_eq h' hC]
  refine ⟨hrefine C hC, hrefine _ sdiff_subset, ?_⟩
  intro β hβ
  obtain ⟨β', ⟨hβ', hsub⟩, -⟩ := hone β hβ
  have hne := interior_nonempty_of_mem h hβ
  have key : ∀ E : Set (Set D.Space), E ⊆ D.partitionAt σ' → β' ∉ E →
      ¬ β ⊆ ⋃₀ E ∧ Disjoint (interior β) (⋃₀ E) := by
    intro E hE hn
    have hd : Disjoint (interior β) (⋃₀ E) :=
      (disjoint_interior_sUnion_of_not_mem h' hβ' hE hn).mono_left (interior_mono hsub)
    refine ⟨fun hs => ?_, hd⟩
    obtain ⟨z, hz⟩ := hne
    exact Set.disjoint_left.1 hd hz (hs (interior_subset hz))
  by_cases hm : β' ∈ C
  · left
    have := key (D.partitionAt σ' \ C) sdiff_subset fun hh => hh.2 hm
    exact ⟨hsub.trans (subset_sUnion_of_mem hm), this.1, this.2⟩
  · right
    have := key C hC hm
    exact ⟨hsub.trans (subset_sUnion_of_mem ⟨hβ', hm⟩), this.1, this.2⟩
end TwoSides
section Vertices
theorem vertex_shift_mem_latticeAt {y : D.Space} (hy : y ∈ D.latticeAt σ) {ε : Fin 4 → ℝ}
    (hε : ∀ μ, ε μ = 1 ∨ ε μ = -1) (e : Fin 4 → ℤ) :
    y + (torusProj D.side fun μ => ε μ * (σ / 2)) +
      (torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2)) ∈ D.latticeAt σ := by
  have hg : ∀ μ, ∃ l : ℤ, ε μ * (σ / 2) + σ * ((e μ : ℝ) + 1 / 2) = σ * (l : ℝ) := fun μ => by
    rcases hε μ with h1 | h1
    · exact ⟨e μ + 1, by rw [h1]; push_cast; ring⟩
    · exact ⟨e μ, by rw [h1]; ring⟩
  choose l hl using hg
  have : y + (torusProj D.side fun μ => ε μ * (σ / 2)) +
      (torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2)) =
      y + torusProj D.side fun μ => σ * (l μ : ℝ) := by
    rw [add_assoc]
    congr 1
    funext μ
    simp only [torusProj, Pi.add_apply, ← AddCircle.coe_add, hl]
  rw [this]
  exact add_mem_latticeAt hy ⟨l, rfl⟩
theorem exists_cube_near_vertex (h : EvenMultiple D.side σ) {z x : D.Space} {r : ℕ} (hr : 1 ≤ r)
    (hx : ‖x - z‖ ≤ (r : ℝ) * σ) :
    ∃ e : Fin 4 → ℤ, (∀ μ, -(r : ℤ) ≤ e μ ∧ e μ ≤ r - 1) ∧
      x ∈ D.cubeAround σ (z + torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2)) := by
  have hσ := h.1
  obtain ⟨w, hw, hw'⟩ := exists_lift_abs_eq_norm (x - z)
  have hb : ∀ μ, |w μ| ≤ (r : ℝ) * σ := fun μ => by
    rw [hw' μ]
    exact (norm_le_pi_norm _ μ).trans hx
  have hg : ∀ μ, ∃ l : ℤ, -(r : ℤ) ≤ l ∧ l ≤ r - 1 ∧
      |w μ - σ / 2 - σ * (l : ℝ)| ≤ σ / 2 := fun μ => by
    have := abs_le.1 (hb μ)
    refine exists_int_near_between (by omega) hσ ?_ ?_
    · push_cast
      linarith [this.1]
    · push_cast
      linarith [this.2]
  choose e he1 he2 he3 using hg
  refine ⟨e, fun μ => ⟨he1 μ, he2 μ⟩, ?_⟩
  rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm]
  have hsub : x - (z + torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2)) =
      torusProj D.side fun μ => w μ - σ / 2 - σ * (e μ : ℝ) := by
    funext μ
    have h2 : x μ - z μ = ((w μ : ℝ) : AddCircle D.side) := (congrFun hw μ).symm
    have h3 : w μ - σ / 2 - σ * (e μ : ℝ) = w μ - σ * ((e μ : ℝ) + 1 / 2) := by ring
    simp only [Pi.sub_apply, Pi.add_apply, torusProj, h3, AddCircle.coe_sub]
    rw [← h2]
    abel
  rw [hsub]
  exact norm_torusProj_le (by positivity) he3
theorem norm_sub_le_of_mem_shifted_cube (hσ : 0 < σ) {z : D.Space} {r : ℕ} {e : Fin 4 → ℤ}
    (he : ∀ μ, -(r : ℤ) ≤ e μ ∧ e μ ≤ r - 1) {x : D.Space}
    (hx : x ∈ D.cubeAround σ (z + torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2))) :
    ‖x - z‖ ≤ (r : ℝ) * σ := by
  rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm] at hx
  have hc : ‖torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2)‖ ≤ (r : ℝ) * σ - σ / 2 := by
    have hr : (1 : ℝ) ≤ r := by
      have h0 := he 0
      have : (1 : ℤ) ≤ r := by omega
      exact_mod_cast this
    refine norm_torusProj_le (by nlinarith) fun μ => ?_
    have h1 : (-(r : ℝ)) ≤ e μ := by exact_mod_cast (he μ).1
    have h2 : (e μ : ℝ) ≤ r - 1 := by exact_mod_cast (he μ).2
    rw [abs_le]
    constructor <;> nlinarith
  have hd : x - z = (x - (z + torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2))) +
      torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2) := by abel
  rw [hd]
  refine (norm_add_le _ _).trans ?_
  linarith
theorem supBall_isCubeUnionAt (h : EvenMultiple D.side σ) {y z : D.Space}
    (hy : y ∈ D.latticeAt σ) (hz : z ∈ D.cubeVertices σ y) {r : ℕ} (hr : 1 ≤ r) :
    D.IsCubeUnionAt σ {x | torusSupNorm (x - z) ≤ (r : ℝ) * σ} := by
  obtain ⟨ε, hε, rfl⟩ := hz
  refine ⟨{β | ∃ e : Fin 4 → ℤ, (∀ μ, -(r : ℤ) ≤ e μ ∧ e μ ≤ r - 1) ∧
    β = D.cubeAround σ (y + (torusProj D.side fun μ => ε μ * (σ / 2)) +
      torusProj D.side fun μ => σ * ((e μ : ℝ) + 1 / 2))}, ?_, ?_⟩
  · rintro _ ⟨e, -, rfl⟩
    exact ⟨_, vertex_shift_mem_latticeAt hy hε e, rfl⟩
  · apply Subset.antisymm
    · intro x hx
      rw [mem_ofPred_eq, torusSupNorm_eq_norm] at hx
      obtain ⟨e, he, hxe⟩ := exists_cube_near_vertex h hr hx
      exact ⟨_, ⟨e, he, rfl⟩, hxe⟩
    · rintro x ⟨_, ⟨e, he, rfl⟩, hx⟩
      rw [mem_ofPred_eq, torusSupNorm_eq_norm]
      exact norm_sub_le_of_mem_shifted_cube h.1 he hx
def boolSign (b : Bool) : ℝ := if b then 1 else -1
theorem boolSign_eq (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]
def adjacentCenter (σ : ℝ) (z : D.Space) (b : Fin 4 → Bool) : D.Space :=
  z + torusProj D.side fun μ => boolSign (b μ) * (σ / 2)
theorem adjacentCenter_mem_latticeAt {y : D.Space} (hy : y ∈ D.latticeAt σ) {ε : Fin 4 → ℝ}
    (hε : ∀ μ, ε μ = 1 ∨ ε μ = -1) (b : Fin 4 → Bool) :
    adjacentCenter σ (y + torusProj D.side fun μ => ε μ * (σ / 2)) b ∈ D.latticeAt σ := by
  have := vertex_shift_mem_latticeAt hy hε fun μ => if b μ then 0 else -1
  have hs : ∀ μ, boolSign (b μ) * (σ / 2) =
      σ * (((if b μ then 0 else -1 : ℤ) : ℝ) + 1 / 2) := by
    intro μ
    cases b μ <;> simp [boolSign] <;> ring
  rw [adjacentCenter]
  simp only [hs]
  exact this
theorem adjacentCenter_injective (h : EvenMultiple D.side σ) (z : D.Space) :
    Function.Injective (adjacentCenter σ z : (Fin 4 → Bool) → D.Space) := by
  have hσ := h.1
  have hS0 := h.pos
  have hS := h.two_mul_le
  intro b b' he
  funext μ
  by_contra hne
  have h1 := add_left_cancel he
  have h2 : ((boolSign (b μ) * (σ / 2) : ℝ) : AddCircle D.side) =
      ((boolSign (b' μ) * (σ / 2) : ℝ) : AddCircle D.side) :=
    congrFun h1 μ
  have h3 : ((σ : ℝ) : AddCircle D.side) = 0 := by
    have h4 : ((boolSign (b μ) * (σ / 2) - boolSign (b' μ) * (σ / 2) : ℝ) :
        AddCircle D.side) = 0 := by
      rw [AddCircle.coe_sub, h2, sub_self]
    cases hb : b μ <;> cases hb' : b' μ <;> simp [hb, hb'] at hne
    · have : (boolSign false * (σ / 2) - boolSign true * (σ / 2)) = -σ := by
        simp [boolSign]; ring
      rw [hb, hb', this] at h4
      simpa using h4
    · have : (boolSign true * (σ / 2) - boolSign false * (σ / 2)) = σ := by simp [boolSign]
      rw [hb, hb', this] at h4
      exact h4
  have h5 : ‖((σ : ℝ) : AddCircle D.side)‖ = |σ| :=
    (AddCircle.norm_coe_eq_abs_iff D.side hS0.ne').2 (by
      rw [abs_of_pos hσ, abs_of_pos hS0]
      linarith)
  rw [h3, norm_zero, abs_of_pos hσ] at h5
  linarith
theorem cubes_at_vertex (h : EvenMultiple D.side σ) {y z : D.Space}
    (hy : y ∈ D.latticeAt σ) (hz : z ∈ D.cubeVertices σ y) :
    {β | ∃ y' ∈ D.latticeAt σ, z ∈ D.cubeVertices σ y' ∧ β = D.cubeAround σ y'} =
        (fun b => D.cubeAround σ (adjacentCenter σ z b)) '' univ ∧
      {β | ∃ y' ∈ D.latticeAt σ, z ∈ D.cubeVertices σ y' ∧ β = D.cubeAround σ y'}.ncard =
        2 ^ 4 := by
  obtain ⟨ε, hε, rfl⟩ := hz
  set z := y + torusProj D.side fun μ => ε μ * (σ / 2) with hzdef
  have hlat : ∀ b, adjacentCenter σ z b ∈ D.latticeAt σ := adjacentCenter_mem_latticeAt hy hε
  have himage : {β | ∃ y' ∈ D.latticeAt σ, z ∈ D.cubeVertices σ y' ∧
      β = D.cubeAround σ y'} = (fun b => D.cubeAround σ (adjacentCenter σ z b)) '' univ := by
    ext β
    constructor
    · rintro ⟨y', -, ⟨ε', hε', hz'⟩, rfl⟩
      refine ⟨fun μ => decide (ε' μ = -1), mem_univ _, ?_⟩
      have : adjacentCenter σ z (fun μ => decide (ε' μ = -1)) = y' := by
        rw [hz', adjacentCenter, add_assoc]
        have : (torusProj D.side fun μ => ε' μ * (σ / 2)) +
            (torusProj D.side fun μ => boolSign (decide (ε' μ = -1)) * (σ / 2)) = 0 := by
          funext μ
          simp only [torusProj, Pi.add_apply, Pi.zero_apply, ← AddCircle.coe_add]
          rcases hε' μ with h1 | h1
          · have h2 : ¬ ((1 : ℝ) = -1) := by norm_num
            simp [h1, boolSign, h2]
          · simp [h1, boolSign]
        rw [this, add_zero]
      simp only [this]
    · rintro ⟨b, -, rfl⟩
      refine ⟨_, hlat b, ⟨fun μ => - boolSign (b μ), fun μ => ?_, ?_⟩, rfl⟩
      · rcases boolSign_eq (b μ) with h1 | h1 <;> simp [h1]
      · rw [adjacentCenter, add_assoc]
        have : (torusProj D.side fun μ => boolSign (b μ) * (σ / 2)) +
            (torusProj D.side fun μ => - boolSign (b μ) * (σ / 2)) = 0 := by
          funext μ
          simp only [torusProj, Pi.add_apply, Pi.zero_apply, ← AddCircle.coe_add]
          have : boolSign (b μ) * (σ / 2) + - boolSign (b μ) * (σ / 2) = 0 := by ring
          rw [this]
          simp
        rw [this, add_zero]
  refine ⟨himage, ?_⟩
  rw [himage, Set.ncard_image_of_injective]
  · rw [Set.ncard_univ]
    simp
  · intro b b' he
    exact adjacentCenter_injective h z (cubeAround_inj h (hlat b) (hlat b') he)
theorem supBall_one_eq (h : EvenMultiple D.side σ) {y z : D.Space} (hy : y ∈ D.latticeAt σ)
    (hz : z ∈ D.cubeVertices σ y) :
    {x | torusSupNorm (x - z) ≤ σ} =
      ⋃₀ {β | ∃ y' ∈ D.latticeAt σ, z ∈ D.cubeVertices σ y' ∧ β = D.cubeAround σ y'} := by
  have hσ := h.1
  rw [(cubes_at_vertex h hy hz).1]
  apply Subset.antisymm
  · intro x hx
    rw [mem_ofPred_eq, torusSupNorm_eq_norm] at hx
    have hx1 : ‖x - z‖ ≤ ((1 : ℕ) : ℝ) * σ := by simpa using hx
    obtain ⟨e, he, hxe⟩ := exists_cube_near_vertex h le_rfl hx1
    refine ⟨_, ⟨fun μ => decide (e μ = 0), mem_univ _, rfl⟩, ?_⟩
    convert hxe using 2
    rw [adjacentCenter]
    congr 1
    funext μ
    simp only [torusProj]
    congr 1
    have h1 := (he μ).1
    have h2 := (he μ).2
    have h3 : e μ = 0 ∨ e μ = -1 := by
      push_cast at h1 h2
      omega
    rcases h3 with h3 | h3 <;> simp [h3, boolSign] <;> ring
  · rintro x ⟨_, ⟨b, -, rfl⟩, hx⟩
    rw [mem_ofPred_eq, torusSupNorm_eq_norm]
    change x ∈ D.cubeAround σ (adjacentCenter σ z b) at hx
    rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm, adjacentCenter] at hx
    have hc : ‖torusProj D.side fun μ => boolSign (b μ) * (σ / 2)‖ ≤ σ / 2 := by
      refine norm_torusProj_le (by positivity) fun μ => ?_
      have hh : |σ / 2| = σ / 2 := abs_of_pos (half_pos hσ)
      rcases boolSign_eq (b μ) with h1 | h1 <;> rw [h1] <;> simp [hh]
    have hd : x - z = (x - (z + torusProj D.side fun μ => boolSign (b μ) * (σ / 2))) +
        torusProj D.side fun μ => boolSign (b μ) * (σ / 2) := by abel
    rw [hd]
    refine (norm_add_le _ _).trans ?_
    linarith
end Vertices
end Cube
open Cube
theorem closure_sdiff_cubeUnion {D : TorusData} {σ : ℝ} (h : EvenMultiple D.side σ)
    {W X : Set D.Space} (hW : D.IsCubeUnionAt σ W) (hX : D.IsCubeUnionAt σ X) :
    closure (W \ X) = ⋃₀ {β ∈ D.partitionAt σ | β ⊆ W ∧ ¬ β ⊆ X} ∧
      W \ X ⊆ ⋃₀ {β ∈ D.partitionAt σ | β ⊆ W ∧ ¬ β ⊆ X} ∧
      ⋃₀ {β ∈ D.partitionAt σ | β ⊆ W ∧ ¬ β ⊆ X} ⊆ W ∩ D.closedComplement X := by
  have hT : D.RefinementFacts σ σ := refinementFacts (p := 0) h h.1 (by simp)
  have hdich := (hT.2.2.2.2 X hX).2.2
  have hsub : W \ X ⊆ ⋃₀ {β ∈ D.partitionAt σ | β ⊆ W ∧ ¬ β ⊆ X} := by
    rintro x ⟨hxW, hxX⟩
    obtain ⟨C, hC, rfl⟩ := hW
    obtain ⟨β, hβ, hx⟩ := hxW
    exact ⟨β, ⟨hC hβ, subset_sUnion_of_mem hβ, fun hs => hxX (hs hx)⟩, hx⟩
  have hcube : ∀ β ∈ {β ∈ D.partitionAt σ | β ⊆ W ∧ ¬ β ⊆ X},
      β ⊆ D.closedComplement X ∧ Disjoint (interior β) X := by
    rintro β ⟨hβ, -, hn⟩
    rcases hdich β hβ with h1 | h1
    · exact absurd h1.1 hn
    · exact ⟨h1.1, h1.2.2⟩
  refine ⟨?_, hsub, ?_⟩
  · apply Subset.antisymm
    · exact closure_minimal hsub (isClosed_sUnion_of_subset_partition h (sep_subset _ _))
    · rintro x ⟨β, hβ, hx⟩
      have hβ' := hβ
      obtain ⟨⟨y, -, rfl⟩, hs, -⟩ := hβ
      rw [← closure_interior_cubeAround h y] at hx
      refine closure_mono ?_ hx
      intro z hz
      exact ⟨hs (interior_subset hz), Set.disjoint_left.1 (hcube _ hβ').2 hz⟩
  · rintro x ⟨β, hβ, hx⟩
    exact ⟨hβ.2.1 hx, (hcube β hβ).1 hx⟩
namespace Scales
variable {D : TorusData}
theorem three_le_L : 3 ≤ D.L := D.blocking.three_le_factor
theorem one_lt_L : (1 : ℝ) < D.L := by apply _root_.YangMills.Construction.Weighted.GivenChainGeneral.Comparison.one_lt_L <;> assumption
theorem scale_pos (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_add (n k : ℕ) : D.scale (n + k) = (D.L : ℝ) ^ k * D.scale n := by
  unfold TorusData.scale
  rw [pow_add]
  ring
theorem exists_pow_eq_odd (k : ℕ) :
    ∃ p : ℕ, (D.L : ℝ) ^ k = 2 * (p : ℝ) + 1 ∧ D.L ^ k = 2 * p + 1 := by
  obtain ⟨p, hp⟩ := D.blocking.factor_odd.pow (n := k)
  exact ⟨p, by exact_mod_cast hp, hp⟩
variable {m : ℕ}
theorem evenMultiple_scale (hm : D.blockNumber = D.L ^ m) {i : ℕ} (hi : i ≤ D.top + m) :
    EvenMultiple D.side (D.scale i) := by
  obtain ⟨k, hk, hS⟩ := D.side_multiple
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hi
  refine ⟨scale_pos i, 2 * k * (D.L : ℤ) ^ c, ⟨k * (D.L : ℤ) ^ c, by ring⟩, ?_, ?_⟩
  · have : 0 < D.L := by have := three_le_L (D := D); omega
    positivity
  · rw [hS, hm]
    unfold TorusData.scale
    push_cast
    have : (D.L : ℝ) ^ m * (D.L : ℝ) ^ D.top = (D.L : ℝ) ^ i * (D.L : ℝ) ^ c := by
      rw [← pow_add, ← pow_add, add_comm m, hc]
    linear_combination (2 * (k : ℝ) * D.bareSpacing) * this
theorem le_top_add_of_scale_le (hm : D.blockNumber = D.L ^ m) {i : ℕ}
    (h : D.scale i ≤ (D.blockNumber : ℝ) * D.scale D.top) : i ≤ D.top + m := by
  have hb := D.bareSpacing_pos
  rw [hm] at h
  unfold TorusData.scale at h
  push_cast at h
  have h1 : (D.L : ℝ) ^ i ≤ (D.L : ℝ) ^ (D.top + m) := by
    rw [add_comm, pow_add]
    have : (D.L : ℝ) ^ i * D.bareSpacing ≤
        ((D.L : ℝ) ^ m * (D.L : ℝ) ^ D.top) * D.bareSpacing := by
      linarith
    exact le_of_mul_le_mul_right this hb
  exact (pow_le_pow_iff_right₀ one_lt_L).1 h1
theorem blockSide_eq_scale (hm : D.blockNumber = D.L ^ m) (n : ℕ) :
    D.blockSide n = D.scale (n + m) := by apply _root_.YangMills.Construction.Weighted.GivenChainGeneral.Comparison.blockNumber_mul_scale <;> assumption
theorem blockCubeFacts (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    D.BlockCubeFacts m n := by
  have hf : EvenMultiple D.side (D.blockSide n) := by
    rw [blockSide_eq_scale hm]
    exact evenMultiple_scale hm (by omega)
  refine ⟨by rw [blockSide_eq_scale hm], ?_, hf.two_mul_le, ?_⟩
  · obtain ⟨hσ, N, hE, -, hS⟩ := hf
    exact ⟨N, hE, by rw [hS]; field_simp⟩
  · have h1 : (D.L : ℝ) ≤ D.blockNumber := by exact_mod_cast D.le_blockNumber
    have h2 := scale_pos (D := D) n
    unfold TorusData.blockSide
    nlinarith
theorem refinementFacts_scale (hm : D.blockNumber = D.L ^ m) {i i' : ℕ} (h : i ≤ i')
    (hi' : i' ≤ D.top + m) : D.RefinementFacts (D.scale i) (D.scale i') := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨p, hp, -⟩ := exists_pow_eq_odd (D := D) c
  exact refinementFacts (evenMultiple_scale hm hi') (scale_pos i) (by rw [scale_add, hp])
theorem latticeAt_scale_anti {i i' : ℕ} (h : i ≤ i') :
    D.latticeAt (D.scale i') ⊆ D.latticeAt (D.scale i) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨p, hp, -⟩ := exists_pow_eq_odd (D := D) c
  exact latticeAt_subset_of_odd (p := p) (by rw [scale_add, hp])
end Scales
namespace Layers
open Scales
variable {D : TorusData} (B : SeparatedChain D) {m : ℕ}
theorem stage_isCubeUnionAt {n : ℕ} (hn : n ≤ D.top) :
    D.IsCubeUnionAt (D.blockSide n) (B.stage n) :=
  B.cubeUnion n hn
theorem succ_stage_isCubeUnionAt (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    D.IsCubeUnionAt (D.blockSide n) (B.stage (n + 1)) := by
  rcases hn.lt_or_eq with h | rfl
  · have hu := stage_isCubeUnionAt B (show n + 1 ≤ D.top by omega)
    rw [blockSide_eq_scale hm] at hu
    rw [blockSide_eq_scale hm]
    exact ((refinementFacts_scale hm (show n + m ≤ n + 1 + m by omega)
      (by omega)).2.2.2.2 _ hu).1
  · rw [B.empty_above _ (by omega)]
    exact ⟨∅, empty_subset _, by simp⟩
theorem stage_anti {n n' : ℕ} (h : n ≤ n') (hn' : n' ≤ D.top) :
    B.stage n' ⊆ B.stage n := by
  induction n', h using Nat.le_induction with
  | base => exact Subset.rfl
  | succ k hk ih =>
    exact (B.decreasing k (by omega)).trans (ih (by omega))
theorem evenMultiple_blockSide (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    EvenMultiple D.side (D.blockSide n) := by
  rw [blockSide_eq_scale hm]
  exact evenMultiple_scale hm (by omega)
theorem layer_eq_closure_sdiff (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    B.layer n = closure (B.stage n \ B.stage (n + 1)) := by
  unfold SeparatedChain.layer
  rcases hn.lt_or_eq with h | rfl
  · rw [if_pos h]
  · rw [if_neg (lt_irrefl _), if_pos rfl, B.empty_above _ (Nat.lt_succ_self _), sdiff_empty]
    obtain ⟨C, hC, hE⟩ := stage_isCubeUnionAt B (le_refl D.top)
    rw [hE]
    exact (isClosed_sUnion_of_subset_partition (evenMultiple_blockSide hm le_rfl) hC).closure_eq.symm
theorem layer_eq_and_bounds (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    B.layer n = ⋃₀ {β ∈ D.partitionAt (D.blockSide n) |
        β ⊆ B.stage n ∧ ¬ β ⊆ B.stage (n + 1)} ∧
      B.stage n \ B.stage (n + 1) ⊆ B.layer n ∧
      B.layer n ⊆ B.stage n ∩ D.closedComplement (B.stage (n + 1)) := by
  obtain ⟨h1, h2, h3⟩ := closure_sdiff_cubeUnion (evenMultiple_blockSide hm hn)
    (stage_isCubeUnionAt B hn) (succ_stage_isCubeUnionAt B hm hn)
  rw [layer_eq_closure_sdiff B hm hn]
  refine ⟨h1, subset_closure, ?_⟩
  rw [h1]
  exact h3
theorem layer_eq_empty {n : ℕ} (hn : D.top < n) : B.layer n = ∅ := by
  unfold SeparatedChain.layer
  rw [if_neg (by omega), if_neg (by omega)]
theorem le_top_of_mem_layerSites {n : ℕ} {y : D.Space} (hy : y ∈ B.layerSites n) :
    n ≤ D.top := by
  by_contra hn
  have := hy.2
  rw [layer_eq_empty B (by omega)] at this
  exact this
theorem layer_eq_iUnion_cubeAround (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    B.layer n = ⋃ y ∈ B.layerSites n, D.cubeAround (D.scale n) y := by
  have hT := refinementFacts_scale hm (show n ≤ n + m by omega) (by omega)
  have hfn : EvenMultiple D.side (D.scale n) := evenMultiple_scale hm (by omega)
  obtain ⟨-, hsite, hone, hunion, -⟩ := hT
  have hlayer := (layer_eq_and_bounds B hm hn).1
  have hbcs := blockSide_eq_scale hm n
  rw [hbcs] at hlayer
  apply Subset.antisymm
  · intro x hx
    have hx' := hx
    rw [hlayer] at hx'
    obtain ⟨β, hβ, hxβ⟩ := hx'
    have hβl : β ⊆ B.layer n := by
      rw [hlayer]
      exact subset_sUnion_of_mem hβ
    rw [hunion β hβ.1] at hxβ
    obtain ⟨_, ⟨⟨y, hy, rfl⟩, hs⟩, hx2⟩ := hxβ
    exact mem_iUnion₂.2 ⟨y, ⟨hy, hβl (hs (center_mem_cubeAround hfn y))⟩, hx2⟩
  · refine iUnion₂_subset fun y hy => ?_
    have hyl := hy.2
    rw [hlayer] at hyl
    obtain ⟨β, hβ, hyβ⟩ := hyl
    obtain ⟨β', ⟨hβ', hs⟩, -⟩ := hone _ ⟨y, hy.1, rfl⟩
    obtain ⟨β₀, -, -, huniq⟩ := hsite y hy.1
    have e : β' = β :=
      (huniq β' hβ' (hs (center_mem_cubeAround hfn y))).trans (huniq β hβ.1 hyβ).symm
    rw [e] at hs
    refine hs.trans ?_
    rw [hlayer]
    exact subset_sUnion_of_mem hβ
theorem cubeAround_subset_layer (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : D.cubeAround (D.scale n) y ⊆ B.layer n := by
  have hn := le_top_of_mem_layerSites B hy
  rw [layer_eq_iUnion_cubeAround B hm hn]
  exact subset_iUnion₂_of_subset y hy Subset.rfl
theorem disjoint_interior_succ_stage (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) :
    Disjoint (interior (D.cubeAround (D.scale n) y)) (B.stage (n + 1)) := by
  have hn := le_top_of_mem_layerSites B hy
  rcases hn.lt_or_eq with h | rfl
  · have hu := stage_isCubeUnionAt B (show n + 1 ≤ D.top by omega)
    rw [blockSide_eq_scale hm] at hu
    have hT := refinementFacts_scale hm (show n ≤ n + 1 + m by omega)
      (show n + 1 + m ≤ D.top + m by omega)
    have hd := (hT.2.2.2.2 _ hu).2.2 _ ⟨y, hy.1, rfl⟩
    rcases hd with h1 | h1
    · exact absurd (((cubeAround_subset_layer B hm hy).trans
        (layer_eq_and_bounds B hm hn).2.2).trans inter_subset_right) h1.2.1
    · exact h1.2.2
  · rw [B.empty_above _ (Nat.lt_succ_self _)]
    exact disjoint_empty _
theorem disjoint_interior_of_lt (hm : D.blockNumber = D.L ^ m) {n n' : ℕ} {y y' : D.Space}
    (hy : y ∈ B.layerSites n) (hy' : y' ∈ B.layerSites n') (h : n < n') :
    Disjoint (interior (D.cubeAround (D.scale n) y)) (D.cubeAround (D.scale n') y') := by
  have hn' := le_top_of_mem_layerSites B hy'
  refine (disjoint_interior_succ_stage B hm hy).mono_right ?_
  refine (cubeAround_subset_layer B hm hy').trans ?_
  exact ((layer_eq_and_bounds B hm hn').2.2.trans inter_subset_left).trans (stage_anti B h hn')
theorem level_eq_of_mem_layerSites (hm : D.blockNumber = D.L ^ m) {n n' : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) (hy' : y ∈ B.layerSites n') : n = n' := by
  have hin : ∀ {k : ℕ} (_ : y ∈ B.layerSites k),
      y ∈ interior (D.cubeAround (D.scale k) y) := by
    intro k hk
    have hf : EvenMultiple D.side (D.scale k) :=
      evenMultiple_scale hm (by have := le_top_of_mem_layerSites B hk; omega)
    rw [interior_cubeAround hf]
    exact center_mem_ball hf y
  have hcube : ∀ {k : ℕ} (_ : y ∈ B.layerSites k), y ∈ D.cubeAround (D.scale k) y :=
    fun hk => interior_subset (hin hk)
  rcases lt_trichotomy n n' with h | h | h
  · exact absurd (hcube hy')
      (Set.disjoint_left.1 (disjoint_interior_of_lt B hm hy hy' h) (hin hy))
  · exact h
  · exact absurd (hcube hy)
      (Set.disjoint_left.1 (disjoint_interior_of_lt B hm hy' hy h) (hin hy'))
theorem sInf_level_eq (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : sInf {k | y ∈ B.layerSites k} = n :=
  level_eq_of_mem_layerSites B hm (Nat.sInf_mem (s := {k | y ∈ B.layerSites k}) ⟨n, hy⟩) hy
theorem siteScale_eq (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : B.siteScale y = D.scale n := by
  rw [SeparatedChain.siteScale, sInf_level_eq B hm hy]
theorem siteCube_eq_cubeAround (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : B.siteCube y = D.cubeAround (D.scale n) y := by
  rw [SeparatedChain.siteCube, siteScale_eq B hm hy]
theorem layerDecomposition (hm : D.blockNumber = D.L ^ m) {n : ℕ} (hn : n ≤ D.top) :
    B.LayerDecomposition n := by
  obtain ⟨h1, h2, h3⟩ := layer_eq_and_bounds B hm hn
  refine ⟨h1, h2, h3, ?_⟩
  rw [layer_eq_iUnion_cubeAround B hm hn]
  exact iUnion₂_congr fun y hy => (siteCube_eq_cubeAround B hm hy).symm
theorem mem_allSites_iff {y : D.Space} : y ∈ B.allSites ↔ ∃ n, y ∈ B.layerSites n := by
  constructor
  · intro hy
    simp only [SeparatedChain.allSites, mem_iUnion] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    have := le_top_of_mem_layerSites B hn
    simp only [SeparatedChain.allSites, mem_iUnion]
    exact ⟨n, Finset.mem_range.2 (by omega), hn⟩
theorem exists_mem_layer (hm : D.blockNumber = D.L ^ m) {x : D.Space} (hx : x ∈ B.stage 0) :
    ∃ n, n ≤ D.top ∧ x ∈ B.layer n := by
  classical
  have htop : x ∉ B.stage (D.top + 1) := by
    rw [B.empty_above _ (Nat.lt_succ_self _)]
    exact notMem_empty x
  have hex : ∃ k, x ∉ B.stage (k + 1) := ⟨_, htop⟩
  have h2 : Nat.find hex ≤ D.top := Nat.find_min' hex htop
  have h3 : x ∈ B.stage (Nat.find hex) := by
    rcases hk : Nat.find hex with _ | k
    · exact hx
    · by_contra hn
      exact Nat.find_min hex (m := k) (by omega) hn
  exact ⟨_, h2, (layer_eq_and_bounds B hm h2).2.1 ⟨h3, Nat.find_spec hex⟩⟩
end Layers
namespace Layers
open Scales
variable {D : TorusData} (B : SeparatedChain D) {m : ℕ}
theorem cubeAround_subset_stage (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : D.cubeAround (D.scale n) y ⊆ B.stage n :=
  (cubeAround_subset_layer B hm hy).trans
    ((layer_eq_and_bounds B hm (le_top_of_mem_layerSites B hy)).2.2.trans inter_subset_left)
theorem disjoint_interior_siteCube (hm : D.blockNumber = D.L ^ m) {y y' : D.Space}
    (hy : y ∈ B.allSites) (hy' : y' ∈ B.allSites) (hne : y ≠ y') :
    Disjoint (interior (B.siteCube y)) (interior (B.siteCube y')) := by
  obtain ⟨n, hn⟩ := (mem_allSites_iff B).1 hy
  obtain ⟨n', hn'⟩ := (mem_allSites_iff B).1 hy'
  rw [siteCube_eq_cubeAround B hm hn, siteCube_eq_cubeAround B hm hn']
  rcases lt_trichotomy n n' with h | rfl | h
  · exact (disjoint_interior_of_lt B hm hn hn' h).mono_right interior_subset
  · have hf : EvenMultiple D.side (D.scale n) :=
      evenMultiple_scale hm (by have := le_top_of_mem_layerSites B hn; omega)
    have := disjoint_ball_cubeAround hf hn.1 hn'.1 hne
    rw [← interior_cubeAround hf] at this
    exact this.mono_right interior_subset
  · exact ((disjoint_interior_of_lt B hm hn' hn h).mono_right interior_subset).symm
theorem iUnion_siteCube_eq (hm : D.blockNumber = D.L ^ m) :
    (⋃ y ∈ B.allSites, B.siteCube y) = B.stage 0 := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun y hy => ?_
    obtain ⟨n, hn⟩ := (mem_allSites_iff B).1 hy
    rw [siteCube_eq_cubeAround B hm hn]
    exact (cubeAround_subset_stage B hm hn).trans
      (stage_anti B (Nat.zero_le n) (le_top_of_mem_layerSites B hn))
  · intro x hx
    obtain ⟨n, hn, hxl⟩ := exists_mem_layer B hm hx
    rw [(layerDecomposition B hm hn).2.2.2] at hxl
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hxl
    exact mem_iUnion₂.2 ⟨y, (mem_allSites_iff B).2 ⟨n, hy⟩, hxy⟩
theorem mem_interior_of_bareSite (hm : D.blockNumber = D.L ^ m) (x : D.BareSite) {n : ℕ}
    {y : D.Space} (hy : y ∈ B.layerSites n) (hx : (x : D.Space) ∈ D.cubeAround (D.scale n) y) :
    (x : D.Space) ∈ interior (D.cubeAround (D.scale n) y) := by
  have hn := le_top_of_mem_layerSites B hy
  obtain ⟨β, hβ, hint, huniq⟩ :=
    (refinementFacts_scale hm (Nat.zero_le n) (show n ≤ D.top + m by omega)).2.1 x x.2
  rw [huniq _ ⟨y, hy.1, rfl⟩ hx]
  exact hint
theorem siteCubesTile (hm : D.blockNumber = D.L ^ m) : B.SiteCubesTile := by
  refine ⟨fun y hy y' hy' hne => disjoint_interior_siteCube B hm hy hy' hne,
    iUnion_siteCube_eq B hm, ?_⟩
  intro x hx
  rw [← iUnion_siteCube_eq B hm] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  have hint : ∀ y' ∈ B.allSites, (x : D.Space) ∈ B.siteCube y' →
      (x : D.Space) ∈ interior (B.siteCube y') := by
    intro y' hy' h
    obtain ⟨n, hn⟩ := (mem_allSites_iff B).1 hy'
    rw [siteCube_eq_cubeAround B hm hn] at h ⊢
    exact mem_interior_of_bareSite B hm x hn h
  refine ⟨y, hy, hint y hy hxy, fun y' hy' hx' => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (disjoint_interior_siteCube B hm hy' hy hne) (hint y' hy' hx')
    (hint y hy hxy)
theorem blocksPartition (hm : D.blockNumber = D.L ^ m) : B.BlocksPartition := by
  have hC := siteCubesTile B hm
  refine ⟨?_, ?_⟩
  · intro y hy y' hy' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    have hx0 : (x : D.Space) ∈ B.stage 0 := by
      rw [← hC.2.1]
      exact mem_iUnion₂.2 ⟨y, hy, hx⟩
    obtain ⟨w, hw, -, hu⟩ := hC.2.2 x hx0
    exact hne ((hu y hy hx).trans (hu y' hy' hx').symm)
  · apply Subset.antisymm
    · refine iUnion₂_subset fun y hy x hx => ?_
      change (x : D.Space) ∈ B.stage 0
      rw [← hC.2.1]
      exact mem_iUnion₂.2 ⟨y, hy, hx⟩
    · intro x hx
      have hx0 : (x : D.Space) ∈ B.stage 0 := hx
      obtain ⟨w, hw, hint, -⟩ := hC.2.2 x hx0
      have hxw : (x : D.Space) ∈ B.siteCube w := interior_subset hint
      exact mem_iUnion₂.2 ⟨w, hw, hxw⟩
theorem mem_stage_bareLevel (hm : D.blockNumber = D.L ^ m) (x : D.BareSite)
    (hx : (x : D.Space) ∈ B.stage 0) : (x : D.Space) ∈ B.stage (B.bareLevel x) := by
  have hC := siteCubesTile B hm
  obtain ⟨w, hw, hint, -⟩ := hC.2.2 x hx
  have hxw : (x : D.Space) ∈ B.siteCube w := interior_subset hint
  have hex : ∃ y, y ∈ B.allSites ∧ x ∈ B.block y := ⟨w, hw, hxw⟩
  obtain ⟨hy, hxy⟩ : B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) :=
    Classical.epsilon_spec hex
  obtain ⟨n, hn⟩ := (mem_allSites_iff B).1 hy
  have hl : B.bareLevel x = n := sInf_level_eq B hm hn
  rw [hl]
  have hxy' : (x : D.Space) ∈ B.siteCube (B.blockCenter x) := hxy
  rw [siteCube_eq_cubeAround B hm hn] at hxy'
  exact cubeAround_subset_stage B hm hn hxy'
theorem blockDescription (hm : D.blockNumber = D.L ^ m) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : B.BlockDescription n y := by
  have hn := le_top_of_mem_layerSites B hy
  obtain ⟨p, hp, hpN⟩ := exists_pow_eq_odd (D := D) n
  have hξ : 0 < D.scale 0 := scale_pos 0
  have hq : D.scale n = (2 * (p : ℝ) + 1) * D.scale 0 := by
    have := scale_add (D := D) 0 n
    rw [zero_add] at this
    rw [this, hp]
  have hf0 : EvenMultiple D.side (D.scale 0) := evenMultiple_scale hm (by omega)
  have hfn : EvenMultiple D.side (D.scale n) := evenMultiple_scale hm (by omega)
  have hyl : y ∈ D.latticeAt (D.scale n) := hy.1
  have hy0 : y ∈ D.latticeAt (D.scale 0) := latticeAt_scale_anti (Nat.zero_le n) hy.1
  have hoff : D.blockOffsets n = {s | ∀ μ, |s μ| ≤ (p : ℤ)} := by
    have e : ((D.L : ℝ) ^ n - 1) / 2 = p := by
      rw [hp]
      ring
    ext s
    simp only [TorusData.blockOffsets, e, mem_ofPred_eq]
    constructor
    · intro h μ
      exact_mod_cast h μ
    · intro h μ
      exact_mod_cast h μ
  have himage : Subtype.val '' B.block y = D.shiftedSite y '' D.blockOffsets n := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : D.Space) ∈ D.cubeAround (D.scale n) y := by
        rw [← siteCube_eq_cubeAround B hm hy]
        exact hx
      rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm] at hx'
      have hb := norm_sub_le_mul_of_mem hf0 hq x.2 hyl hx'
      obtain ⟨w, hw, hw'⟩ := exists_lift_abs_eq_norm ((x : D.Space) - y)
      have hl : ∀ μ, ∃ l : ℤ, w μ = D.scale 0 * (l : ℝ) := fun μ =>
        hf0.exists_int_of_mem_grid (mem_latticeAt_iff.1 (sub_mem_latticeAt x.2 hy0) μ)
          (congrFun hw μ)
      choose l hl using hl
      refine ⟨l, ?_, ?_⟩
      · rw [hoff]
        intro μ
        have h1 : |w μ| ≤ (p : ℝ) * D.scale 0 := by
          rw [hw' μ]
          exact (norm_le_pi_norm _ μ).trans hb
        rw [hl μ, abs_mul, abs_of_pos hξ] at h1
        have h2 : |(l μ : ℝ)| ≤ p :=
          le_of_mul_le_mul_left (by linarith : D.scale 0 * |(l μ : ℝ)| ≤ D.scale 0 * p) hξ
        exact_mod_cast h2
      · change y + (torusProj D.side fun μ => D.scale 0 * (l μ : ℝ)) = x
        have : (torusProj D.side fun μ => D.scale 0 * (l μ : ℝ)) = (x : D.Space) - y := by
          rw [← hw]
          congr 1
          funext μ
          exact (hl μ).symm
        rw [this]
        abel
    · rintro _ ⟨s, hs, rfl⟩
      rw [hoff] at hs
      have hlat : D.shiftedSite y s ∈ D.latticeAt (D.scale 0) :=
        add_mem_latticeAt hy0 ⟨s, rfl⟩
      refine ⟨⟨_, hlat⟩, ?_, rfl⟩
      change D.shiftedSite y s ∈ B.siteCube y
      rw [siteCube_eq_cubeAround B hm hy, cubeAround_eq_closedBall, Metric.mem_closedBall,
        dist_eq_norm]
      have : D.shiftedSite y s - y = torusProj D.side fun μ => D.scale 0 * (s μ : ℝ) := by
        simp [TorusData.shiftedSite]
      rw [this]
      refine norm_torusProj_le (by have := scale_pos (D := D) n; positivity) fun μ => ?_
      rw [abs_mul, abs_of_pos hξ, hq]
      have h2 : |(s μ : ℝ)| ≤ p := by exact_mod_cast hs μ
      nlinarith
  have hinj : InjOn (D.shiftedSite y) (D.blockOffsets n) := by
    intro s hs s' hs' he
    rw [hoff] at hs hs'
    have h1 : (torusProj D.side fun μ => D.scale 0 * (s μ : ℝ)) =
        torusProj D.side fun μ => D.scale 0 * (s' μ : ℝ) := add_left_cancel he
    funext μ
    have h2 : ((D.scale 0 * (s μ : ℝ) : ℝ) : AddCircle D.side) =
        ((D.scale 0 * (s' μ : ℝ) : ℝ) : AddCircle D.side) := congrFun h1 μ
    obtain ⟨j, hj⟩ := exists_int_eq_add_mul_of_coe_eq h2
    have hS := hfn.two_mul_le
    have hS0 := hfn.pos
    have h3 : |(s μ : ℝ)| ≤ p := by exact_mod_cast hs μ
    have h4 : |(s' μ : ℝ)| ≤ p := by exact_mod_cast hs' μ
    have hd : |(s μ : ℝ) - s' μ| ≤ 2 * p := by
      refine (abs_sub _ _).trans ?_
      linarith
    have he' : D.scale 0 * ((s μ : ℝ) - s' μ) = j * D.side := by linarith
    have hj0 : j = 0 := by
      by_contra hne
      have h5 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      have h6 : D.scale 0 * |(s μ : ℝ) - s' μ| = |(j : ℝ)| * D.side := by
        have := congrArg abs he'
        rwa [abs_mul, abs_mul, abs_of_pos hξ, abs_of_pos hS0] at this
      have h7 : D.scale 0 * |(s μ : ℝ) - s' μ| ≤ D.scale 0 * (2 * p) :=
        mul_le_mul_of_nonneg_left hd hξ.le
      have h8 : D.side ≤ |(j : ℝ)| * D.side := le_mul_of_one_le_left hS0.le h5
      rw [hq] at hS
      nlinarith
    rw [hj0] at he'
    have h9 : D.scale 0 * ((s μ : ℝ) - s' μ) = 0 := by simpa using he'
    have h10 : (s μ : ℝ) - s' μ = 0 := (mul_eq_zero.1 h9).resolve_left hξ.ne'
    have h11 : (s μ : ℝ) = s' μ := by linarith
    exact_mod_cast h11
  have hcard : (B.block y).ncard = D.L ^ (n * 4) := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himage,
      hinj.ncard_image, hoff]
    have : {s : Fin 4 → ℤ | ∀ μ, |s μ| ≤ (p : ℤ)} =
        ↑(Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(p : ℤ)) p) := by
      ext s
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      simp only [mem_ofPred_eq, Finset.mem_Icc, abs_le]
    rw [this, Set.ncard_coe_finset, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : ((p : ℤ) + 1 - -(p : ℤ)).toNat = 2 * p + 1 := by omega
    rw [this, ← hpN, pow_mul]
  have hratio : (D.L : ℝ) ^ (n * 4) = (B.siteScale y / D.scale 0) ^ 4 := by
    rw [siteScale_eq B hm hy, pow_mul]
    congr 1
    have := scale_add (D := D) 0 n
    rw [zero_add] at this
    rw [this]
    field_simp
  have hcenter : y ∈ Subtype.val '' B.block y := by
    refine ⟨⟨y, hy0⟩, ?_, rfl⟩
    change y ∈ B.siteCube y
    rw [siteCube_eq_cubeAround B hm hy]
    exact center_mem_cubeAround hfn y
  refine ⟨himage, hinj, hcard, hratio, hcenter, ?_⟩
  have hsub : B.block y ⊆ D.bareSites (B.stage 0) := by
    intro x hx
    have hx' : (x : D.Space) ∈ B.siteCube y := hx
    rw [siteCube_eq_cubeAround B hm hy] at hx'
    exact stage_anti B (Nat.zero_le n) hn (cubeAround_subset_stage B hm hy hx')
  have hfin : Finite D.BareSite := (latticeAt_finite hf0).to_subtype
  have hsum : ∑ᶠ x ∈ D.bareSites (B.stage 0), B.blockIndicator y x * B.blockIndicator y x =
      ((B.block y).ncard : ℝ) := by
    have h1 : ∀ x, (D.bareSites (B.stage 0)).indicator
        (fun x => B.blockIndicator y x * B.blockIndicator y x) x =
        (B.block y).indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hb : x ∈ B.block y
      · simp [Set.indicator_of_mem (hsub hb), SeparatedChain.blockIndicator, hb]
      · by_cases hE : x ∈ D.bareSites (B.stage 0)
        · simp [Set.indicator_of_mem hE, SeparatedChain.blockIndicator, hb]
        · simp [hb, hE]
    rw [finsum_mem_def]
    simp_rw [h1]
    rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    simp
  unfold SeparatedChain.bareSpaceNorm SeparatedChain.bareInner
  rw [hsum, hcard, siteScale_eq B hm hy]
  have : D.scale 0 ^ 4 * ((D.L ^ (n * 4) : ℕ) : ℝ) = (D.scale n ^ 2) ^ 2 := by
    have h2 := scale_add (D := D) 0 n
    rw [zero_add] at h2
    rw [h2]
    push_cast
    rw [pow_mul]
    ring
  rw [this, Real.sqrt_sq (by positivity)]
end Layers
open Cube Scales
open Layers
theorem cubesLayersBlocksBallsHold : CubesLayersBlocksBallsHold := by
  intro D B m hm i i' hii hi'
  have hi'' := le_top_add_of_scale_le hm hi'
  refine ⟨partitionFacts (evenMultiple_scale hm (by omega)), refinementFacts_scale hm hii hi'',
    fun n hn => blockCubeFacts hm hn, fun n hn => layerDecomposition B hm hn,
    siteCubesTile B hm, blocksPartition B hm, fun n y hy => blockDescription B hm hy,
    fun x hx => mem_stage_bareLevel B hm x hx, ?_⟩
  intro j hj z hz
  have h : EvenMultiple D.side (D.blockSide j) := evenMultiple_blockSide hm hj
  obtain ⟨y, hy, hzy⟩ : ∃ y ∈ D.latticeAt (D.blockSide j),
      z ∈ D.cubeVertices (D.blockSide j) y := by
    simpa [TorusData.levelVertices] using hz
  exact ⟨fun r hr => supBall_isCubeUnionAt h hy hzy hr, supBall_one_eq h hy hzy,
    (cubes_at_vertex h hy hzy).2⟩
end Weighted.CubeGeometry
end YangMills.Construction
