import YangMills.Construction.Conventions.SignedConjugate
import YangMills.Construction.InfiniteLattice.ChessboardFunctionalOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.StandingConventionsOfMultipleReflections
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MultipleReflections.Setup
variable (D : Setup)
def IsTileEdge (l : ℝ) : Prop :=
  (∃ j : ℤ, l = (D.L : ℝ) ^ j) ∧ (D.L : ℝ) ^ 2 * D.mesh ≤ l
theorem one_lt_L : (1 : ℝ) < D.L := by
  have h := D.isAdmissible.2
  exact_mod_cast (by omega : 1 < D.L)
theorem isTileEdge_zpow_iff (j : ℤ) :
    D.IsTileEdge ((D.L : ℝ) ^ j) ↔ 2 - ((D.K : ℕ) : ℤ) ≤ j := by
  have hL := D.one_lt_L
  have hL0 : (D.L : ℝ) ≠ 0 := (zero_lt_one.trans hL).ne'
  have ha : (D.L : ℝ) ^ 2 * D.mesh = (D.L : ℝ) ^ (2 - ((D.K : ℕ) : ℤ)) := by
    have h2 : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
    rw [h2, sub_eq_add_neg, zpow_add₀ hL0]
    norm_cast
  constructor
  · rintro ⟨-, h⟩
    rw [ha] at h
    exact (zpow_le_zpow_iff_right₀ hL).1 h
  · intro h
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [ha]
    exact (zpow_le_zpow_iff_right₀ hL).2 h
theorem isAdmissibleSide_iff_isTileEdge (l : ℝ) :
    InfiniteLattice.ReflectionGrid.IsAdmissibleSide D.L (D.K : ℕ) l ↔ D.IsTileEdge l := by
  have hL : (0 : ℝ) < (D.L : ℝ) ^ 2 := pow_pos (zero_lt_one.trans D.one_lt_L) 2
  have ha : CutoffLattice.spacingAt D.L (D.K : ℕ) = D.mesh := rfl
  unfold InfiniteLattice.ReflectionGrid.IsAdmissibleSide IsTileEdge
  rw [ha, le_div_iff₀ hL, mul_comm D.mesh]
abbrev Grid : Type := InfiniteLattice.ReflectionGrid D.L (D.K : ℕ)
namespace Grid
variable {D} (G : D.Grid)
theorem isTileEdge_edge : D.IsTileEdge G.edge :=
  (D.isAdmissibleSide_iff_isTileEdge _).1 G.edge_admissible
theorem edge_pos : 0 < G.edge := by
  obtain ⟨⟨j, hj⟩, -⟩ := G.isTileEdge_edge
  rw [hj]
  exact zpow_pos (zero_lt_one.trans D.one_lt_L) j
theorem tile_injective : Function.Injective G.tile := by
  intro k k' h
  have hl := G.edge_pos
  have hmem : ∀ p q : Fin 4 → ℤ, G.tile p = G.tile q → ∀ μ, G.cornerAt q μ ≤ G.cornerAt p μ := by
    intro p q hpq μ
    have hp : G.cornerAt p ∈ G.tile p := fun ν => ⟨le_rfl, by linarith⟩
    rw [hpq] at hp
    exact (hp μ).1
  funext μ
  have h1 := hmem k k' h μ
  have h2 := hmem k' k h.symm μ
  have h3 : G.cornerAt k μ = G.cornerAt k' μ := le_antisymm h2 h1
  simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3
  have h4 : (k μ : ℝ) = k' μ := mul_left_cancel₀ hl.ne' (add_left_cancel h3)
  exact_mod_cast h4
def tileReflection (k k' : Fin 4 → ℤ) (x : AmbientSpace) : AmbientSpace := fun α =>
  if Even (k' α - k α) then x α + ((k' α - k α : ℤ) : ℝ) * G.edge
  else 2 * G.shift α + ((k α + k' α + 1 : ℤ) : ℝ) * G.edge - x α
def tileSign (k k' : Fin 4 → ℤ) : ℤˣ := (-1) ^ ∑ α, (k' α - k α)
theorem tileReflection_tileReflection (k k' : Fin 4 → ℤ) (x : AmbientSpace) :
    G.tileReflection k' k (G.tileReflection k k' x) = x := by
  funext α
  have he : Even (k α - k' α) ↔ Even (k' α - k α) := by
    rw [← neg_sub, even_neg]
  simp only [tileReflection, he]
  split_ifs
  · push_cast
    ring
  · push_cast
    ring
theorem tileReflection_mem_latticeAt (k k' : Fin 4 → ℤ) {x : AmbientSpace}
    (hx : x ∈ CutoffLattice.latticeAt D.L (D.K : ℕ)) :
    G.tileReflection k k' x ∈ CutoffLattice.latticeAt D.L (D.K : ℕ) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨N, hN⟩ := InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
  choose i hi using G.shift_mem
  refine ⟨fun α => if Even (k' α - k α) then n α + (k' α - k α) * N
    else 2 * i α + 1 + (k α + k' α + 1) * N - n α, fun α => ?_⟩
  simp only [tileReflection]
  split_ifs
  · rw [hn, hN]
    push_cast
    ring
  · rw [hn, hN, hi]
    push_cast
    ring
def tileSymmetry (k k' : Fin 4 → ℤ) : D.LatticeSymmetry where
  toFun := G.tileReflection k k'
  preservesDist x y := by
    unfold TorusMetric.euclidNormVec
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Pi.sub_apply, tileReflection]
    split_ifs <;> ring
  image_eq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact G.tileReflection_mem_latticeAt k k' hx
    · intro hy
      exact ⟨G.tileReflection k' k y, G.tileReflection_mem_latticeAt k' k hy,
        G.tileReflection_tileReflection k' k y⟩
def reflectedCopy (k k' : Fin 4 → ℤ) (F : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  Conventions.signedConjFun (tileSign k k') ((G.tileSymmetry k k').actOn F)
def tilesPerSide : ℝ := D.side / G.edge
theorem tilesPerSide_eq (h : 2 * G.edge ≤ D.side) {j : ℤ} (hj : G.edge = (D.L : ℝ) ^ j) :
    j ≤ ((D.m : ℕ) : ℤ) ∧ G.tilesPerSide = 2 * (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - j) := by
  have hL := D.one_lt_L
  have hL0 : (D.L : ℝ) ≠ 0 := (zero_lt_one.trans hL).ne'
  have hs : D.side = 2 * (D.L : ℝ) ^ ((D.m : ℕ) : ℤ) := by
    simp [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  refine ⟨?_, ?_⟩
  · rw [hs, hj] at h
    exact (zpow_le_zpow_iff_right₀ hL).1 (by linarith)
  · rw [tilesPerSide, hs, hj, zpow_sub₀ hL0]
    ring
abbrev boxTileIndices : Set (Fin 4 → ℤ) := G.torusTileIndices D.m
def boxTiles : Set (Set AmbientSpace) := G.tile '' G.boxTileIndices
def AreCongruent (S S' : Set AmbientSpace) : Prop :=
  S ∈ G.tiling ∧ S' ∈ G.tiling ∧
    ∃ v : Fin 4 → ℤ, S' = (fun x : AmbientSpace => x + D.side • fun μ => (v μ : ℝ)) '' S
def reflectedProduct (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  fun U => ∏ k' ∈ (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m).toFinset,
    G.reflectedCopy k k' F U
def chessboardNorm (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ) : ℝ :=
  ‖D.torusExpectation (G.reflectedProduct k F)‖ ^ (1 / G.tilesPerSide ^ 4)
def chessboardNormAt (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) (k : Fin 4 → ℤ)
    (F : D.GaugeField → ℂ) : ℝ :=
  chessboardNorm (D := D.atSide ℓ' hℓ') G k F
end Grid
end MultipleReflections.Setup
end YangMills.Construction
end
