import YangMills.Construction.Dirichlet.CellSiteGrid
import YangMills.Construction.Dirichlet.LatticeSiteCells
import YangMills.Construction.Dirichlet.ShellCells
import YangMills.Construction.Torus.ChainScales
import YangMills.Construction.Torus.ChainShells
import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.NeighborCountStatement
import YangMills.Construction.Torus.PartitionsShellsCubes
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.PartitionsProof
theorem scaleSpacing_pos {L : ℕ} {ξ : ℝ} (hL : 3 ≤ L) (hξ : 0 < ξ) (i : ℤ) :
    0 < scaleSpacing L ξ i := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  exact mul_pos (zpow_pos hLpos i) hξ
theorem scaleSpacing_eq_pow_mul {L : ℕ} (hL : 3 ≤ L) (ξ : ℝ) {j i : ℤ} (hji : j ≤ i) :
    scaleSpacing L ξ i = ((L ^ (i - j).toNat : ℕ) : ℝ) * scaleSpacing L ξ j := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hcast : ((i - j).toNat : ℤ) = i - j := Int.toNat_of_nonneg (by omega)
  have hpow : (L : ℝ) ^ i = (L : ℝ) ^ ((i - j).toNat : ℤ) * (L : ℝ) ^ j := by
    rw [← zpow_add₀ hL0, hcast]; congr 1; ring
  simp only [scaleSpacing, Nat.cast_pow]
  rw [hpow, zpow_natCast]
  ring
theorem pow_mul_scaleSpacing {L : ℕ} (hL : 3 ≤ L) (ξ : ℝ) (u : ℕ) (i : ℤ) :
    ((L ^ u : ℕ) : ℝ) * scaleSpacing L ξ i = scaleSpacing L ξ (i + u) := by
  have h := scaleSpacing_eq_pow_mul hL ξ (j := i) (i := i + u) (by omega)
  have hu : (i + (u : ℤ) - i).toNat = u := by simp
  rw [hu] at h
  exact h.symm
theorem nestedPartitionFacts_of {d L : ℕ} {ξ S : ℝ} (hd : 0 < d) (hL : 3 ≤ L) (hodd : Odd L)
    (hξ : 0 < ξ) (one : CubePartition.PropertiesOfIntegerMultiple)
    (nest : NestedCubes.PropertiesOfOddRefinement)
    {j i : ℤ} (hji : j ≤ i) (hS : IsNatAtLeastTwo (S / scaleSpacing L ξ i)) :
    NestedPartitionFacts d L ξ S (scaleSpacing L ξ i) (scaleSpacing L ξ j) := by
  obtain ⟨k, hk, hSk⟩ := hS
  have hσ := scaleSpacing_pos hL hξ i
  have hσj := scaleSpacing_pos hL hξ j
  have hS : S = (k : ℝ) * scaleSpacing L ξ i := by
    rw [← hSk]; field_simp
  have hσσ := scaleSpacing_eq_pow_mul hL ξ hji
  have hO := one d S (scaleSpacing L ξ i) k hd hσ hk hS
  have hN := nest d S (scaleSpacing L ξ i) (scaleSpacing L ξ j) (L ^ (i - j).toNat) k hd hσj
    (hodd.pow) hσσ hk hS
  refine
    { div_eq_int := ⟨((L ^ (i - j).toNat * k : ℕ) : ℤ), ?_⟩
      spacingLattice_le := hN.spacingLattice_le
      not_mem_of_mem_interior := hO.interior_not_mem_of_ne
      eq_sUnion_finer := hN.cube_eq_sUnion
      isCubeUnion_finer := hN.isCubeUnion_of_coarse
      grid_in_cube := fun z hz w hw => ?_
      grid_subset_interior := hN.inter_cube_subset_interior
      closure_sdiff := hO.closure_diff_eq
      disjoint_interior := hO.disjoint_interior
      compl_subset := hO.compl_subset_cubeComplement
      frontier_subset := hO.frontier_subset_cubeComplement
      cubeComplement_anti := hO.cubeComplement_antitone
      cubeComplement_eq_closure := ?_ }
  · rw [hS, hσσ]
    push_cast
    field_simp
  · have h := hN.isCenteredGrid_inter_cube z hz w hw
    exact ⟨h.image_eq, h.injOn, h.ncard_eq⟩
  · rintro Y - τ ⟨m, rfl, n, hn, hSn⟩ hY
    have hτ := scaleSpacing_pos hL hξ m
    have hS' : S = (n : ℝ) * scaleSpacing L ξ m := by
      rw [← hSn]; field_simp
    exact (one d S (scaleSpacing L ξ m) n hd hτ hn hS').cubeComplement_eq_closure_compl Y hY
theorem scaleSideFacts_of {d L : ℕ} {ξ S : ℝ} (hd : 0 < d) (hL : 3 ≤ L) (hodd : Odd L)
    (hξ : 0 < ξ) (one : CubePartition.PropertiesOfIntegerMultiple)
    (nest : NestedCubes.PropertiesOfOddRefinement)
    {i : ℤ} {k : ℕ} (hk : 0 < k) (hS : S = 2 * (k : ℝ) * scaleSpacing L ξ i) :
    ScaleSideFacts d L ξ S (scaleSpacing L ξ i) := by
  have hσ := scaleSpacing_pos hL hξ i
  have hr : S / scaleSpacing L ξ i = 2 * (k : ℝ) := by
    rw [hS]; field_simp
  refine ⟨i, rfl, ⟨k, hk, hr⟩, fun j hji =>
    nestedPartitionFacts_of hd hL hodd hξ one nest hji ⟨2 * k, by omega, ?_⟩⟩
  rw [hr]; push_cast; ring
theorem projectionFacts_of {d : ℕ} {S : ℝ} (h : ProjCubes.ProjFacts d S) :
    ProjectionFacts d S where
  injOn := h.injOn_cube
  supNorm_eq := h.supNorm_eq
  lOneNorm_eq := h.lOneNorm_eq
  lOneNorm_le_length := by
    intro p q γ
    induction γ generalizing p with
    | nil =>
      intro hpq
      have hpq' : p = q := hpq
      have h0 := h.lOneNorm_proj_le 0
      have hz : torusProj d S (0 : Fin d → ℝ) = 0 := by
        funext μ; simp [torusProj]
      rw [hz] at h0
      simpa [hpq', segmentPathLength] using h0
    | cons s γ ih =>
      rintro ⟨hs, hγ⟩
      have h1 := ih _ hγ
      have h2 := h.lOneNorm_add_le (p - s.pointAt S 1) (s.pointAt S 1 - q)
      have h3 := h.lOneNorm_proj_le (-s.direction)
      have h4 : torusProj d S (-s.direction) = p - s.pointAt S 1 := by
        rw [← hs]
        funext μ
        simp [TorusSegment.pointAt, torusProj]
      rw [h4] at h3
      have h5 : p - s.pointAt S 1 + (s.pointAt S 1 - q) = p - q := by abel
      rw [h5] at h2
      have h6 : ∑ μ, |(-s.direction) μ| = s.lOneLength := by
        simp [TorusSegment.lOneLength]
      have h7 : segmentPathLength (s :: γ) = s.lOneLength + segmentPathLength γ := by
        simp [segmentPathLength]
      rw [h7]
      linarith
theorem partitionsHold (cov : ProjCubes.ProjFactsHold)
    (one : CubePartition.PropertiesOfIntegerMultiple)
    (nest : NestedCubes.PropertiesOfOddRefinement)
    (sides : ChainScales.ScalesStatement)
    (members : ChainShells.ShellsStatement)
    (cells : Dirichlet.ShellCells.AllShellCellFacts)
    (place : Dirichlet.LatticeSiteCells.AllLatticeSiteFacts)
    (grid : Dirichlet.CellSiteGrid.AllCellGridFacts)
    (nbrs : NeighborCountStatement) : PartitionsHold := by
  intro d L aMinus aPlus hpar ξ S hξ hSpos
  have hd : 0 < d := by have := hpar.three_le_dim; omega
  have hL := hpar.three_le_blockFactor
  have hodd := hpar.odd_blockFactor
  refine ⟨projectionFacts_of (cov d S hSpos),
    fun j i hji hS => nestedPartitionFacts_of hd hL hodd hξ one nest hji hS, ?_⟩
  intro M R₁ t Ω hΩ
  have hs := sides d L S ξ M R₁ t Ω (by omega) hΩ
  have hm := members d L S ξ M R₁ t Ω hd hL hodd hΩ
  have hc := cells d L S ξ M R₁ t Ω hd hL hodd hΩ
  have hp := place d L S ξ M R₁ t Ω hd hL hodd hΩ
  have hg := grid d L S ξ M R₁ t Ω hd hL hodd hΩ
  obtain ⟨u, hu, hMu, hev⟩ := hs.side_even_multiple
  have hMi : ∀ n : ℕ, (M : ℝ) * scaleSpacing L ξ n = scaleSpacing L ξ ((n : ℤ) + u) := by
    intro n
    rw [hMu]
    exact pow_mul_scaleSpacing hL ξ u n
  refine ⟨⟨?_, ?_, ?_, hs.two_mul_le_side⟩, ⟨hΩ.isCubeUnion, hm.succ_isCubeUnion,
    hm.shell_eq_sUnion, hm.shell_subset, hm.zero_eq_iUnion_shell, hm.shell_eq_empty⟩, ?_,
    ⟨hp.exists_cell_of_mem, hp.disjoint_of_not_mem⟩, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, hk, hSk⟩ := hev ((n : ℤ) + u) (by omega)
    rw [hMi n]
    exact scaleSideFacts_of hd hL hodd hξ one nest hk hSk
  · intro n hn
    obtain ⟨k, hk, hSk⟩ := hev (n : ℤ) (by omega)
    exact scaleSideFacts_of hd hL hodd hξ one nest hk hSk
  · obtain ⟨k, hk, hSk⟩ := hev ((lastNonemptyIndex Ω : ℤ) + 1) (by omega)
    exact scaleSideFacts_of hd hL hodd hξ one nest hk hSk
  · intro n hn
    have h := hc n hn
    exact ⟨h.cells_eq, h.shell_eq_iUnion, h.disjoint_cubeComplement, h.disjoint_nextDomain,
      h.disjoint_otherShell, h.disjoint_otherCell, h.mem_interior_shell⟩
  · intro n hn y hy z hz
    have h := hg n hn y hy z hz
    have hgrid := h.sites_eq_centeredGrid
    exact ⟨⟨hgrid.image_eq, hgrid.injOn, hgrid.ncard_eq⟩, h.isNeighbor_iff,
      h.exists_equiv_pathProduct, h.exists_path, h.lOneNorm_sub_le⟩
  · intro x
    refine nbrs d S ξ hξ ?_ x
    have h2 := hs.two_mul_le_side 0 hΩ.zero_nonempty
    have hM3 : (3 : ℝ) ≤ M := by
      have := hΩ.blockSize_isPowerGe.1
      exact_mod_cast (by omega : 3 ≤ M)
    rw [show scaleSpacing L ξ ((0 : ℕ) : ℤ) = ξ by simp [scaleSpacing]] at h2
    nlinarith
end YangMills.Construction.Torus.PartitionsProof
end
