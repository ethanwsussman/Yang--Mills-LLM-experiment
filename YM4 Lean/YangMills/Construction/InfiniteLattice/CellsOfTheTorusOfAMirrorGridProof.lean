import YangMills.Construction.InfiniteLattice.CellsOfTheTorusOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.SourcesObjectsOfAMirrorGridProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MultipleReflections
namespace TorusCells
open Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem mem_tile_iff (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ G.tile k ↔ ∀ μ, x μ - (G.shift μ + G.edge * k μ) ∈ Icc 0 G.edge := by
  refine forall_congr' fun μ => ?_
  simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
theorem tile_toChessboardGrid (k : Fin 4 → ℤ) : G.toChessboardGrid.cell k = G.tile k := by
  ext x
  rw [mem_tile_iff]
  simp only [ChessboardTori.ReflectionGrid.cell, mem_ofPred_eq, G.cellSide_toChessboardGrid]
  rfl
theorem cube_toCubicGrid (i : ℕ) (h : 2 * G.edge ≤ D.side) (k : Fin 4 → ℤ) :
    (G.toCubicGrid i h).cube k = G.tile k := by apply _root_.YangMills.Construction.MultipleReflections.GluingGrid.cube_eq <;> assumption
theorem exists_torusSide_eq_mul (h : 2 * G.edge ≤ D.side) :
    ∃ N : ℤ, 1 ≤ N ∧ D.side = N * G.edge := by
  obtain ⟨hj, he⟩ := tilesPerSide_eq G h G.edge_eq_zpow_edgeExp
  have hL := D.one_lt_L
  have hn : (0 : ℤ) ≤ ((D.m : ℕ) : ℤ) - G.edgeExp := by omega
  obtain ⟨n, hn'⟩ := Int.eq_ofNat_of_zero_le hn
  refine ⟨2 * (D.L : ℤ) ^ n, ?_, ?_⟩
  · have h1 : (1 : ℤ) ≤ (D.L : ℤ) := by exact_mod_cast hL.le
    have h2 : (1 : ℤ) ≤ (D.L : ℤ) ^ n := one_le_pow₀ h1
    omega
  · rw [hn', zpow_natCast] at he
    have hs := G.edge_pos
    have h3 : D.side / G.edge = 2 * (D.L : ℝ) ^ n := he
    rw [div_eq_iff hs.ne'] at h3
    rw [h3]
    push_cast
    ring
theorem tile_add_period {N : ℤ} (hN : D.side = N * G.edge) (k p : Fin 4 → ℤ) :
    G.tile (k + N • p) = (fun x : AmbientSpace => x + D.side • fun μ => (p μ : ℝ)) '' G.tile k := by
  ext x
  constructor
  · intro hx
    refine ⟨x - D.side • fun μ => (p μ : ℝ), ?_, by simp⟩
    rw [mem_tile_iff] at hx ⊢
    intro μ
    have := hx μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mem_Icc, Int.cast_add,
      Int.cast_mul, hN] at this ⊢
    constructor
    · nlinarith [this.1]
    · nlinarith [this.2]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_tile_iff] at hy ⊢
    intro μ
    have := hy μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc, Int.cast_add,
      Int.cast_mul, hN] at this ⊢
    constructor
    · nlinarith [this.1]
    · nlinarith [this.2]
theorem torusImage_translate (S : Set AmbientSpace) (v : Fin 4 → ℤ) :
    torusImage D ((fun x : AmbientSpace => x + D.side • fun μ => (v μ : ℝ)) '' S) =
      torusImage D S := by
  unfold torusImage
  rw [image_image]
  refine image_congr fun x _ => ?_
  have hv : (D.side • fun μ => (v μ : ℝ)) = TestFunctions.latticeTranslate D.side v := by
    funext μ
    simp [TestFunctions.latticeTranslate]
  rw [hv]
  exact TestFunctions.torusProj_add_latticeTranslate D.side x v
theorem bounds_of_mem_boxTileIndices {N : ℤ} (hN : D.side = N * G.edge) {k : Fin 4 → ℤ}
    (hk : k ∈ G.boxTileIndices) (μ : Fin 4) : 0 ≤ k μ ∧ k μ ≤ N - 1 := by
  have hs := G.edge_pos
  obtain ⟨h0, h1⟩ := hk μ
  have h2 : PeriodicLattice.torusSide D.L D.m / G.edge = N := by
    change D.side / G.edge = N
    rw [hN]
    field_simp
  rw [h2] at h1
  exact ⟨h0, by exact_mod_cast h1⟩
theorem index_eq_of_torusImage_eq {N : ℤ} (hN : D.side = N * G.edge) (hN1 : 1 ≤ N)
    {k k' : Fin 4 → ℤ} (hk : k ∈ G.boxTileIndices) (hk' : k' ∈ G.boxTileIndices)
    (he : torusImage D (G.tile k) = torusImage D (G.tile k')) : k = k' := by
  have hs := G.edge_pos
  let c : AmbientSpace := fun μ => G.shift μ + G.edge * k μ + G.edge / 2
  have hc : c ∈ G.tile k := by
    rw [mem_tile_iff]
    intro μ
    simp only [c, mem_Icc]
    constructor <;> linarith
  have hmem : D.coveringMap c ∈ torusImage D (G.tile k') := by
    rw [← he]
    exact mem_image_of_mem _ hc
  obtain ⟨y, hy, hyc⟩ := hmem
  obtain ⟨p, hp⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hyc
  rw [mem_tile_iff] at hy
  funext μ
  obtain ⟨h1, h2⟩ := hy μ
  have hyμ : y μ = c μ + D.side * (p μ : ℝ) := congrFun hp μ
  simp only [hyμ, c, hN] at h1 h2
  set t : ℤ := k μ + N * p μ - k' μ with ht
  have htr : (t : ℝ) = k μ + N * p μ - k' μ := by
    rw [ht]
    push_cast
    ring
  have h3 : 0 ≤ G.edge * ((t : ℝ) + 1 / 2) := by
    rw [htr]
    nlinarith
  have h4 : G.edge * ((t : ℝ) + 1 / 2) ≤ G.edge * 1 := by
    rw [htr]
    nlinarith
  have h5 : 0 ≤ (t : ℝ) + 1 / 2 := nonneg_of_mul_nonneg_right h3 hs
  have h6 : (t : ℝ) + 1 / 2 ≤ 1 := le_of_mul_le_mul_left h4 hs
  have h7 : (-1 : ℝ) < t := by linarith
  have h8 : (t : ℝ) < 1 := by linarith
  have h9 : -1 < t := by exact_mod_cast h7
  have h10 : t < 1 := by exact_mod_cast h8
  have ht0 : t = 0 := by omega
  obtain ⟨a0, a1⟩ := bounds_of_mem_boxTileIndices G hN hk μ
  obtain ⟨b0, b1⟩ := bounds_of_mem_boxTileIndices G hN hk' μ
  have hp0 : p μ = 0 := by
    rcases lt_trichotomy (p μ) 0 with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  rw [ht0, hp0] at ht
  omega
theorem exists_mem_boxTileIndices {N : ℤ} (hN : D.side = N * G.edge) (hN1 : 1 ≤ N) (k : Fin 4 → ℤ) :
    ∃ k' ∈ G.boxTileIndices, torusImage D (G.tile k') = torusImage D (G.tile k) := by
  have hs := G.edge_pos
  have hNpos : 0 < N := by omega
  have h2 : PeriodicLattice.torusSide D.L D.m / G.edge = N := by
    change D.side / G.edge = N
    rw [hN]
    field_simp
  refine ⟨fun μ => k μ % N, fun μ => ⟨Int.emod_nonneg _ hNpos.ne', ?_⟩, ?_⟩
  · rw [h2]
    have h3 : k μ % N ≤ N - 1 := by
      have := Int.emod_lt_of_pos (k μ) hNpos
      omega
    exact_mod_cast h3
  · have hk : k = (fun μ => k μ % N) + N • fun μ => k μ / N := by
      funext μ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (Int.emod_add_mul_ediv (k μ) N).symm
    conv_rhs => rw [hk, tile_add_period G hN]
    exact (torusImage_translate _ _).symm
end TorusCells
open TorusCells Setup.Grid in
theorem torusCellsHold : TorusCellsHold := by
  intro D G h i
  obtain ⟨N, hN1, hN⟩ := exists_torusSide_eq_mul G h
  show _ ∧ _ ∧ _ ∧ BijOn _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : G.toChessboardGrid.cellSet = G.tiling := by
      change range G.toChessboardGrid.cell = range G.tile
      rw [funext (tile_toChessboardGrid G)]
    change (fun S => D.toChessboardSetup.proj '' S) '' G.toChessboardGrid.cellSet = _
    rw [hc]
    rfl
  · have hc : (G.toCubicGrid i h).torusCube = fun k => torusImage D (G.tile k) := by
      funext k
      change (D.toGluingSetup i).proj '' (G.toCubicGrid i h).cube k = _
      rw [cube_toCubicGrid]
      rfl
    rw [hc]
    ext C
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨G.tile k, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  · rintro S S' ⟨-, -, v, rfl⟩
    exact (torusImage_translate S v).symm
  · refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨k, -, rfl⟩
      exact mem_image_of_mem _ ⟨k, rfl⟩
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ he
      rw [index_eq_of_torusImage_eq G hN hN1 hk hk' he]
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      obtain ⟨k', hk', he⟩ := exists_mem_boxTileIndices G hN hN1 k
      exact ⟨G.tile k', ⟨k', hk', rfl⟩, he⟩
end MultipleReflections
end YangMills.Construction
end
