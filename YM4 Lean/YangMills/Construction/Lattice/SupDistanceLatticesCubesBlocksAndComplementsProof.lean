import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Lattice.BondLengthAndFiniteLattices
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import YangMills.Construction.Lattice.SupDistanceLatticesCubesBlocksAndComplements
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice
namespace SupDistance
variable {L m : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem supDistScaled_eq_mul_dist (c : ℝ) (x y : FourTorus L m) :
    supDistScaled c x y = c * dist x y := by
  rw [supDistScaled, torusSupNorm_eq_norm, dist_eq_norm]
theorem isSupOpen_iff_isOpen {c : ℝ} (hc : 0 < c) (U : Set (FourTorus L m)) :
    IsSupOpen c U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r / c, div_pos hr hc, fun z hz => hU z ?_⟩
    rw [supDistScaled_eq_mul_dist]
    rw [Metric.mem_ball, lt_div_iff₀ hc] at hz
    linarith
  · intro h x hx
    obtain ⟨ε, hε, hball⟩ := h x hx
    refine ⟨c * ε, mul_pos hc hε, fun z hz => hball ?_⟩
    rw [supDistScaled_eq_mul_dist] at hz
    exact Metric.mem_ball.2 (lt_of_mul_lt_mul_left hz hc.le)
theorem isOpenQuotientMap_torusProj (S : ℝ) : IsOpenQuotientMap (torusProj S) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
theorem continuous_torusProj (S : ℝ) : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (k : ℕ) :
    meshSize L i = (L : ℝ) ^ k * meshSize L (i + k) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem meshSize_levelDepth (hL : 0 < L) (K n : ℕ) :
    meshSize L (levelDepth K n) = (L : ℝ) ^ n * meshSize L K := by
  have h := meshSize_eq_pow_mul hL (levelDepth K n) n
  have h' : levelDepth K n + (n : ℤ) = (K : ℤ) := by simp [levelDepth]
  rwa [h'] at h
theorem cubeAround_eq_closedBall {i : ℤ} (y : Site L m i) :
    cubeAround y = Metric.closedBall (y : FourTorus L m) (meshSize L i / 2) := by
  ext x
  simp only [cubeAround, mem_ofPred_eq, torusSupNorm_eq_norm, Metric.mem_closedBall, dist_eq_norm]
theorem sum_pointOnAxis (v : Fin 4 → ℝ) :
    ∑ μ, pointOnAxis L m μ (v μ) = torusProj (torusSide L m) v := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.sum_pointOnAxis <;> assumption
theorem finite_site_of_coordinates {i : ℤ} (h : SublatticeCoordinates L m i) :
    Finite (Site L m i) := by apply _root_.YangMills.SharedProofs.p63828 <;> assumption
theorem standardCubePartition_finite {i : ℤ} (h : SublatticeCoordinates L m i) :
    (standardCubePartition L m i).Finite := by
  have := finite_site_of_coordinates h
  exact finite_range _
theorem refinedBlock_eq_grid {i j : ℤ} {k : ℕ} (hj : i + k = j)
    (h : RefinementCubeFacts L m i k) (y : Site L m i) :
    refinedBlock k y = {x | ∃ ν : Fin 4 → ℤ, (∀ μ, |(ν μ : ℝ)| ≤ ((L : ℝ) ^ k - 1) / 2) ∧
      x = (y : FourTorus L m) + ∑ μ, pointOnAxis L m μ ((ν μ : ℝ) * meshSize L j)} := by
  subst hj
  rw [h.1 y]
  ext x
  simp only [blockAsGrid, mem_ofPred_eq, sum_pointOnAxis]
  constructor <;> rintro ⟨p, hp, rfl⟩ <;> refine ⟨p, hp, ?_⟩ <;> simp only [mul_comm]
theorem torusSupNorm_sub_lt_of_mem_refinedBlock (hL : 0 < L) {i : ℤ} {k : ℕ}
    (h : RefinementCubeFacts L m i k) (y : Site L m i) {x : FourTorus L m}
    (hx : x ∈ refinedBlock k y) :
    torusSupNorm (x - (y : FourTorus L m)) < meshSize L i / 2 := by
  rw [refinedBlock_eq_grid rfl h y] at hx
  obtain ⟨ν, hν, rfl⟩ := hx
  have hs := meshSize_pos hL (i + k)
  have hs' := meshSize_pos hL i
  rw [torusSupNorm_eq_norm, add_sub_cancel_left]
  rw [sum_pointOnAxis]
  refine (pi_norm_lt_iff (by linarith)).2 fun μ => ?_
  refine (addCircle_norm_coe_le_abs _).trans_lt ?_
  rw [abs_mul, abs_of_pos hs, meshSize_eq_pow_mul hL i k]
  nlinarith [hν μ]
theorem eq_sUnion_partitionCubesIn {i j : ℤ} {k : ℕ} (hj : i + k = j)
    (h : RefinementCubeFacts L m i k) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) : Q = ⋃₀ partitionCubesIn j Q := by
  subst hj
  obtain ⟨y, rfl⟩ := hQ
  have hy := h.2.1 y
  apply subset_antisymm
  · intro z hz
    have hz' : z ∈ ⋃ y' : Site L m (i + k),
        ⋃ _ : (y' : FourTorus L m) ∈ refinedBlock k y, cubeAround y' := by
      rw [← hy]
      exact hz
    obtain ⟨y', hy', hzy'⟩ := mem_iUnion₂.1 hz'
    refine ⟨cubeAround y', ⟨⟨y', rfl⟩, fun v hv => ?_⟩, hzy'⟩
    rw [hy]
    exact mem_iUnion₂.2 ⟨y', hy', hv⟩
  · rintro z ⟨Q', ⟨-, hsub⟩, hz⟩
    exact hsub hz
end SupDistance
end YangMills.Construction
end
