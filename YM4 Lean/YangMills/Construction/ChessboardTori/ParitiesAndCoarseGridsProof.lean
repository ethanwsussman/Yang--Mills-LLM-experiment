import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.ChessboardTori.ParitiesAndCoarseGrids
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace CellParityAndCoarsening
theorem le_of_mul_le_mul_pos_left {c : ℝ} (hc : 0 < c) {m n : ℤ} (h : c * m ≤ c * n) : m ≤ n := by
  exact_mod_cast le_of_mul_le_mul_left h hc
theorem neg_one_zpow_sum_eq_pow_card_odd (e : Fin 4 → ℤ) :
    (-1 : ℤˣ) ^ (∑ μ, e μ) = (-1) ^ (Finset.univ.filter fun μ => Odd (e μ)).card := by
  have hz : ∀ n : ℤ, (-1 : ℤˣ) ^ n = if Odd n then -1 else 1 := by
    intro n
    split_ifs with hn
    · exact hn.neg_one_zpow
    · exact (Int.not_odd_iff_even.mp hn).neg_one_zpow
  calc (-1 : ℤˣ) ^ (∑ μ, e μ) = ∏ μ, (-1 : ℤˣ) ^ (e μ) := by
        simp only [Fin.sum_univ_four, Fin.prod_univ_four, zpow_add]
    _ = ∏ μ, (if Odd (e μ) then (-1 : ℤˣ) else 1) := by simp only [hz]
    _ = (-1) ^ (Finset.univ.filter fun μ => Odd (e μ)).card := by
        rw [Finset.prod_ite]
        simp
theorem exists_cell_index_of_mem {c : ℝ} (hc : 0 < c) (m N : ℤ) (hN : 1 ≤ N) (y : ℝ)
    (hlo : 0 ≤ y - c * m) (hhi : y - c * m ≤ N * c) :
    ∃ i : ℤ, m ≤ i ∧ i ≤ m + N - 1 ∧ y - c * i ∈ Icc 0 c := by
  have hfl : (⌊y / c⌋ : ℝ) * c ≤ y := (le_div_iff₀ hc).1 (Int.floor_le _)
  have hlt : y < ((⌊y / c⌋ : ℝ) + 1) * c := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  have hmf : m ≤ ⌊y / c⌋ := by
    apply Int.le_floor.2
    rw [le_div_iff₀ hc]
    linarith
  have hfm : ⌊y / c⌋ ≤ m + N := by
    apply le_of_mul_le_mul_pos_left hc
    push_cast
    linarith
  by_cases hf : ⌊y / c⌋ ≤ m + N - 1
  · exact ⟨⌊y / c⌋, hmf, hf, by linarith, by linarith⟩
  · have heq : ⌊y / c⌋ = m + N := by omega
    rw [heq] at hfl
    push_cast at hfl
    refine ⟨m + N - 1, by omega, le_rfl, ?_, ?_⟩ <;> push_cast <;> linarith
theorem eq_of_mul_le_of_le_mul_add {N n q q' : ℤ} (hN : 0 < N) (h : N * q ≤ n ∧ n ≤ N * q + N - 1)
    (h' : N * q' ≤ n ∧ n ≤ N * q' + N - 1) : q = q' := by
  have hl : q < q' + 1 := by
    apply lt_of_mul_lt_mul_left _ hN.le
    rw [mul_add]
    omega
  have hr : q' < q + 1 := by
    apply lt_of_mul_lt_mul_left _ hN.le
    rw [mul_add]
    omega
  omega
def swapNeighbour (k j : Fin 4 → ℤ) : Fin 4 → ℤ :=
  Function.update j 0 (if Even (j 0 - k 0) then j 0 + 1 else j 0 - 1)
theorem swapNeighbour_swapNeighbour (k j : Fin 4 → ℤ) :
    swapNeighbour k (swapNeighbour k j) = j := by
  funext μ
  by_cases hμ : μ = 0
  · subst hμ
    by_cases he : Even (j 0 - k 0)
    · have he' : ¬ Even (j 0 + 1 - k 0) := by
        rw [Int.even_iff] at he ⊢
        omega
      simp [swapNeighbour, he, he']
    · have he' : Even (j 0 - 1 - k 0) := by
        rw [Int.not_even_iff] at he
        rw [Int.even_iff]
        omega
      simp [swapNeighbour, he, he']
  · simp [swapNeighbour, Function.update_of_ne hμ]
theorem odd_sum_swapNeighbour_iff (k k' j : Fin 4 → ℤ) :
    Odd (∑ μ, (swapNeighbour k j μ - k' μ)) ↔ ¬ Odd (∑ μ, (j μ - k' μ)) := by
  have n1 : (1 : Fin 4) ≠ 0 := by decide
  have n2 : (2 : Fin 4) ≠ 0 := by decide
  have n3 : (3 : Fin 4) ≠ 0 := by decide
  simp only [Fin.sum_univ_four, swapNeighbour, Function.update_self, Function.update_of_ne n1,
    Function.update_of_ne n2, Function.update_of_ne n3]
  rw [Int.odd_iff, Int.odd_iff]
  split_ifs <;> omega
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem origin_corner_mem_cell (k : Fin 4 → ℤ) :
    (fun ν => g.origin ν + g.cellSide * k ν) ∈ g.cell k := fun ν => by
  simp [g.cellSide_pos.le]
theorem far_corner_mem_cell (k : Fin 4 → ℤ) :
    (fun ν => g.origin ν + g.cellSide * k ν + g.cellSide) ∈ g.cell k := fun ν => by
  simp [g.cellSide_pos.le]
theorem index_eq_of_actsOnCoord_shift {r : AmbientSpace → AmbientSpace} {k k' : Fin 4 → ℤ}
    (h : r '' g.cell k = g.cell k') {μ : Fin 4} {t : ℤ}
    (ha : g.ActsOnCoord r μ (g.coordShift t)) :
    k' μ = k μ + 2 * t := by
  have hc := g.cellSide_pos
  have m0 : r _ ∈ g.cell k' := h ▸ mem_image_of_mem r (origin_corner_mem_cell g k)
  have m1 : r _ ∈ g.cell k' := h ▸ mem_image_of_mem r (far_corner_mem_cell g k)
  have b0 := m0 μ
  have b1 := m1 μ
  have a0 := ha (fun ν => g.origin ν + g.cellSide * k ν)
  have a1 := ha (fun ν => g.origin ν + g.cellSide * k ν + g.cellSide)
  simp only [ReflectionGrid.coordShift, mem_Icc] at a0 a1 b0 b1
  apply le_antisymm
  · apply le_of_mul_le_mul_pos_left hc
    push_cast
    linarith [b0.1]
  · apply le_of_mul_le_mul_pos_left hc
    push_cast
    linarith [b1.2]
theorem index_eq_of_actsOnCoord_reflect {r : AmbientSpace → AmbientSpace} {k k' : Fin 4 → ℤ}
    (h : r '' g.cell k = g.cell k') {μ : Fin 4} {c : ℤ}
    (ha : g.ActsOnCoord r μ (g.coordReflect c)) :
    k' μ = 2 * c - k μ - 1 := by
  have hc := g.cellSide_pos
  have m0 : r _ ∈ g.cell k' := h ▸ mem_image_of_mem r (origin_corner_mem_cell g k)
  have m1 : r _ ∈ g.cell k' := h ▸ mem_image_of_mem r (far_corner_mem_cell g k)
  have b0 := m0 μ
  have b1 := m1 μ
  have a0 := ha (fun ν => g.origin ν + g.cellSide * k ν)
  have a1 := ha (fun ν => g.origin ν + g.cellSide * k ν + g.cellSide)
  simp only [ReflectionGrid.coordReflect, mem_Icc] at a0 a1 b0 b1
  apply le_antisymm
  · apply le_of_mul_le_mul_pos_left hc
    push_cast
    linarith [b1.1]
  · apply le_of_mul_le_mul_pos_left hc
    push_cast
    linarith [b0.2]
theorem reflectsCoord_iff_odd {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    {k k' : Fin 4 → ℤ} (h : r '' g.cell k = g.cell k') (μ : Fin 4) :
    g.ReflectsCoord r μ ↔ Odd (k' μ - k μ) := by
  constructor
  · rintro ⟨c, hc⟩
    have := index_eq_of_actsOnCoord_reflect g h hc
    rw [Int.odd_iff]
    omega
  · intro ho
    rcases hr μ with ⟨t, ht⟩ | hf
    · have := index_eq_of_actsOnCoord_shift g h ht
      rw [Int.odd_iff] at ho
      omega
    · exact hf
variable {g}
theorem orientationSign_eq_of_image (hC : g.ReflectionGroupCoordForm) {k k' : Fin 4 → ℤ}
    (r : g.reflectionGroup) (h : r.1 '' g.cell k = g.cell k') :
    orientationSign r.1 = (-1) ^ (∑ μ, (k' μ - k μ)) := by
  classical
  obtain ⟨hcw, -, hsg, -⟩ := hC
  rw [hsg r.1 r.2, neg_one_zpow_sum_eq_pow_card_odd, ReflectionGrid.numReflectedCoords]
  congr 2
  ext μ
  simp [reflectsCoord_iff_odd g (hcw r.1 r.2) h μ]
theorem moverSigns (hC : g.ReflectionGroupCoordForm) : g.MoverSigns := by
  intro k k' r h
  refine ⟨orientationSign_eq_of_image hC r h, fun he => ?_⟩
  funext x μ
  rcases hC.1 r.1 r.2 μ with ⟨t, ht⟩ | ⟨c, hc⟩
  · have e1 := index_eq_of_actsOnCoord_shift g h ht
    have e2 := ht x
    simp only [ReflectionGrid.coordShift] at e2
    simp only [translate, Pi.add_apply]
    rw [e1]
    push_cast
    linarith
  · have e1 := index_eq_of_actsOnCoord_reflect g h hc
    have e2 := he μ
    rw [Int.even_iff] at e2
    omega
theorem halfOddInBlock (hC : g.ReflectionGroupCoordForm) (hT : g.TorusSideCells)
    (hB : ∀ k, g.BlockEqUnionCells k) : g.HalfOddInBlock := by
  rintro _ ⟨k0, rfl⟩ _ ⟨k, rfl⟩
  obtain ⟨-, hn, heven, h2, -⟩ := hT
  obtain ⟨-, hin, hcard⟩ := hB k0
  have hnr : ((g.cell '' g.blockIndices k0).ncard : ℝ) = g.cellsAcross ^ 4 := by
    rw [hn]
    exact_mod_cast hcard
  have hinj := g.cell_injective
  rw [ncard_image_of_injective _ hinj] at hnr hcard
  have hfin : (g.blockIndices k0).Finite := by
    apply finite_of_ncard_ne_zero
    intro h0
    rw [h0] at hcard
    have : 0 < g.cellsPerTorusSide ^ 4 := pow_pos (by omega) 4
    simp only [Nat.cast_zero] at hcard
    omega
  refine ⟨by rw [hin, ncard_image_of_injective _ hinj]; exact hnr, ?_⟩
  have hset : {S' ∈ g.cellsWithin (g.block k0) |
      ∃ r : g.reflectionGroup, r.1 '' g.cell k = S' ∧ orientationSign r.1 = -1} =
      g.cell '' {j ∈ g.blockIndices k0 | Odd (∑ μ, (j μ - k μ))} := by
    ext S'
    constructor
    · rintro ⟨hS, r, hr, hsg⟩
      rw [hin] at hS
      obtain ⟨j, hj, rfl⟩ := hS
      refine ⟨j, ⟨hj, ?_⟩, rfl⟩
      by_contra ho
      have e := orientationSign_eq_of_image hC r hr
      rw [hsg, (Int.not_odd_iff_even.1 ho).neg_one_zpow] at e
      exact absurd e (by decide)
    · rintro ⟨j, ⟨hj, ho⟩, rfl⟩
      refine ⟨by rw [hin]; exact mem_image_of_mem _ hj, ?_⟩
      obtain ⟨r, hr, -⟩ := hC.2.2.2.2.2.2.1 _ ⟨k, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨r, hr, by rw [orientationSign_eq_of_image hC r hr, ho.neg_one_zpow]⟩
  have hmap : ∀ j ∈ g.blockIndices k0, swapNeighbour k0 j ∈ g.blockIndices k0 := by
    intro j hj μ
    have hj' : ∀ μ, k0 μ ≤ j μ ∧ j μ ≤ k0 μ + g.cellsPerTorusSide - 1 := hj
    by_cases hμ : μ = 0
    · subst hμ
      have e0 := hj' 0
      obtain ⟨a, ha⟩ := heven
      simp only [swapNeighbour, Function.update_self]
      split_ifs with he
      · obtain ⟨c, hc⟩ := he
        omega
      · rw [Int.not_even_iff] at he
        omega
    · simpa [swapNeighbour, Function.update_of_ne hμ] using hj' μ
  have himg : swapNeighbour k0 '' {j ∈ g.blockIndices k0 | Odd (∑ μ, (j μ - k μ))} =
      g.blockIndices k0 \ {j ∈ g.blockIndices k0 | Odd (∑ μ, (j μ - k μ))} := by
    ext j
    constructor
    · rintro ⟨a, ⟨haI, hao⟩, rfl⟩
      exact ⟨hmap a haI, fun e => (odd_sum_swapNeighbour_iff k0 k a).1 e.2 hao⟩
    · rintro ⟨hjI, hjA⟩
      exact ⟨swapNeighbour k0 j,
        ⟨hmap j hjI, (odd_sum_swapNeighbour_iff k0 k j).2 fun ho => hjA ⟨hjI, ho⟩⟩,
        swapNeighbour_swapNeighbour k0 j⟩
  have hinjS : Function.Injective (swapNeighbour k0) :=
    Function.LeftInverse.injective (swapNeighbour_swapNeighbour k0)
  have hsum := ncard_sdiff_add_ncard_of_subset
    (sep_subset (g.blockIndices k0) fun j => Odd (∑ μ, (j μ - k μ))) hfin
  rw [← himg, ncard_image_of_injective _ hinjS] at hsum
  rw [hset, ncard_image_of_injective _ hinj, ← hnr, ← hsum]
  push_cast
  ring
variable (g)
theorem coarsen_corner (b : ℕ) (k : Fin 4 → ℤ) (μ : Fin 4) (n : ℤ) :
    (g.coarsen b k).origin μ + (g.coarsen b k).cellSide * n =
      g.origin μ + g.cellSide * ((k μ + (D.L : ℤ) ^ b * n : ℤ) : ℝ) := by
  rw [g.cellSide_coarsen]
  show g.origin μ + g.cellSide * k μ + _ = _
  push_cast
  ring
theorem wall_coarsen (b : ℕ) (k : Fin 4 → ℤ) (μ : Fin 4) (n : ℤ) :
    (g.coarsen b k).wall μ n = g.wall μ (k μ + n * (D.L : ℤ) ^ b) := by
  have e := coarsen_corner g b k μ n
  ext x
  simp only [ReflectionGrid.wall, mem_ofPred_eq]
  rw [mul_comm (n : ℝ), e, mul_comm n, mul_comm (((k μ + (D.L : ℤ) ^ b * n : ℤ) : ℝ))]
theorem reflect_coarsen (b : ℕ) (k : Fin 4 → ℤ) (μ : Fin 4) (n : ℤ) :
    (g.coarsen b k).reflect μ n = g.reflect μ (k μ + n * (D.L : ℤ) ^ b) := by
  have e := coarsen_corner g b k μ n
  funext x
  simp only [ReflectionGrid.reflect]
  rw [show x μ - (g.coarsen b k).origin μ - n * (g.coarsen b k).cellSide =
      x μ - g.origin μ - ((k μ + n * (D.L : ℤ) ^ b : ℤ) : ℝ) * g.cellSide by
    rw [mul_comm n]
    linarith]
theorem reflectionGroup_coarsen_le (b : ℕ) (k : Fin 4 → ℤ) :
    (g.coarsen b k).reflectionGroup ≤ g.reflectionGroup := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨μ, n⟩, rfl⟩
  have e : (g.coarsen b k).reflectPerm μ n = g.reflectPerm μ (k μ + n * (D.L : ℤ) ^ b) :=
    Equiv.ext fun x => congrFun (reflect_coarsen g b k μ n) x
  show (g.coarsen b k).reflectPerm μ n ∈ g.reflectionGroup
  rw [e]
  exact Subgroup.subset_closure ⟨(μ, _), rfl⟩
theorem mem_coarsen_cell_iff (b : ℕ) (k j : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ (g.coarsen b k).cell j ↔ ∀ μ,
      x μ - (g.origin μ + g.cellSide * ((k μ + (D.L : ℤ) ^ b * j μ : ℤ) : ℝ)) ∈
        Icc 0 ((D.L : ℝ) ^ b * g.cellSide) := by
  refine forall_congr' fun μ => ?_
  rw [coarsen_corner g b k μ (j μ), g.cellSide_coarsen]
theorem one_le_L_pow (b : ℕ) : (1 : ℤ) ≤ (D.L : ℤ) ^ b := by
  have hL : (1 : ℤ) < D.L := by exact_mod_cast D.one_lt_factor
  exact one_le_pow₀ hL.le
theorem cell_subset_coarsen_cell {b : ℕ} {k j i : Fin 4 → ℤ}
    (hi : i ∈ coarseCellIndices D.L b k j) : g.cell i ⊆ (g.coarsen b k).cell j := by
  intro x hx
  rw [mem_coarsen_cell_iff]
  intro μ
  have hc := g.cellSide_pos
  obtain ⟨h1, h2⟩ := hi μ
  obtain ⟨h3, h4⟩ := hx μ
  have h1' : (((k μ + (D.L : ℤ) ^ b * j μ : ℤ)) : ℝ) ≤ i μ := by exact_mod_cast h1
  have h2' : (i μ : ℝ) + 1 ≤ ((k μ + (D.L : ℤ) ^ b * j μ : ℤ) : ℝ) + (D.L : ℝ) ^ b := by
    have : i μ + 1 ≤ (k μ + (D.L : ℤ) ^ b * j μ) + (D.L : ℤ) ^ b := by omega
    exact_mod_cast this
  have e1 := mul_le_mul_of_nonneg_left h1' hc.le
  have e2 := mul_le_mul_of_nonneg_left h2' hc.le
  constructor <;> nlinarith
theorem mem_coarseCellIndices_of_subset {b : ℕ} {k j i : Fin 4 → ℤ}
    (h : g.cell i ⊆ (g.coarsen b k).cell j) : i ∈ coarseCellIndices D.L b k j := by
  intro μ
  have hc := g.cellSide_pos
  have hl := (mem_coarsen_cell_iff g b k j _).1 (h (origin_corner_mem_cell g i)) μ
  have hu := (mem_coarsen_cell_iff g b k j _).1 (h (far_corner_mem_cell g i)) μ
  simp only [mem_Icc] at hl hu
  have a1 : k μ + (D.L : ℤ) ^ b * j μ ≤ i μ := by
    apply le_of_mul_le_mul_pos_left hc
    linarith [hl.1]
  have a2 : i μ + 1 ≤ k μ + (D.L : ℤ) ^ b * j μ + (D.L : ℤ) ^ b := by
    apply le_of_mul_le_mul_pos_left hc
    have := hu.2
    push_cast at this ⊢
    linarith
  omega
theorem coarsen_cell_eq_biUnion (b : ℕ) (k j : Fin 4 → ℤ) :
    (g.coarsen b k).cell j = ⋃ i ∈ coarseCellIndices D.L b k j, g.cell i := by
  have hc := g.cellSide_pos
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro hx
    have hch : ∀ μ, ∃ i : ℤ, k μ + (D.L : ℤ) ^ b * j μ ≤ i ∧
        i ≤ k μ + (D.L : ℤ) ^ b * j μ + (D.L : ℤ) ^ b - 1 ∧
        x μ - g.origin μ - g.cellSide * i ∈ Icc 0 g.cellSide := fun μ => by
      have e := (mem_coarsen_cell_iff g b k j x).1 hx μ
      refine exists_cell_index_of_mem hc _ ((D.L : ℤ) ^ b) (one_le_L_pow b) (x μ - g.origin μ)
        (by linarith [e.1]) ?_
      have e2 := e.2
      push_cast at e2 ⊢
      linarith
    choose i h1 h2 h3 using hch
    refine ⟨i, fun μ => ⟨h1 μ, h2 μ⟩, fun μ => ?_⟩
    have e := h3 μ
    rwa [sub_sub] at e
  · rintro ⟨i, hi, hx⟩
    exact cell_subset_coarsen_cell g hi hx
theorem ncard_coarseCellIndices (L b : ℕ) (k j : Fin 4 → ℤ) :
    (coarseCellIndices L b k j).ncard = L ^ (4 * b) := by
  have hset : coarseCellIndices L b k j = ↑(Fintype.piFinset fun μ =>
      Finset.Icc (k μ + (L : ℤ) ^ b * j μ) (k μ + (L : ℤ) ^ b * j μ + (L : ℤ) ^ b - 1)) := by
    ext i
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    exact Iff.rfl
  have hcard : ∀ μ, (Finset.Icc (k μ + (L : ℤ) ^ b * j μ)
      (k μ + (L : ℤ) ^ b * j μ + (L : ℤ) ^ b - 1)).card = L ^ b := by
    intro μ
    rw [Int.card_Icc]
    have e : k μ + (L : ℤ) ^ b * j μ + (L : ℤ) ^ b - 1 + 1 - (k μ + (L : ℤ) ^ b * j μ) =
        ((L ^ b : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e, Int.toNat_natCast]
  rw [hset, ncard_coe_finset, Fintype.card_piFinset]
  simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm]
theorem existsUnique_coarsen_cell (b : ℕ) (k i : Fin 4 → ℤ) :
    ∃! S', S' ∈ (g.coarsen b k).cellSet ∧ g.cell i ⊆ S' := by
  have hN : (0 : ℤ) < (D.L : ℤ) ^ b := by linarith [one_le_L_pow (D := D) b]
  have hj : i ∈ coarseCellIndices D.L b k fun μ => (i μ - k μ) / (D.L : ℤ) ^ b := by
    intro μ
    have e := Int.emod_add_mul_ediv (i μ - k μ) ((D.L : ℤ) ^ b)
    have p := Int.emod_nonneg (i μ - k μ) hN.ne'
    have q := Int.emod_lt_of_pos (i μ - k μ) hN
    show _ ≤ _ ∧ _ ≤ _
    generalize (D.L : ℤ) ^ b * ((i μ - k μ) / (D.L : ℤ) ^ b) = w at e ⊢
    generalize (i μ - k μ) % (D.L : ℤ) ^ b = v at e p q
    omega
  refine ⟨_, ⟨⟨_, rfl⟩, cell_subset_coarsen_cell g hj⟩, ?_⟩
  rintro _ ⟨⟨j', rfl⟩, hsub⟩
  have hj' := mem_coarseCellIndices_of_subset g hsub
  congr 1
  funext μ
  have a : k μ + (D.L : ℤ) ^ b * ((i μ - k μ) / (D.L : ℤ) ^ b) ≤ i μ ∧
      i μ ≤ k μ + (D.L : ℤ) ^ b * ((i μ - k μ) / (D.L : ℤ) ^ b) + (D.L : ℤ) ^ b - 1 := hj μ
  have c := hj' μ
  show j' μ = (i μ - k μ) / (D.L : ℤ) ^ b
  exact eq_of_mul_le_of_le_mul_add (n := i μ - k μ) hN (by omega) (by omega)
theorem coarsen_blocks_subset (b : ℕ) (k : Fin 4 → ℤ) : (g.coarsen b k).blocks ⊆ g.blocks := by
  rintro _ ⟨j, rfl⟩
  refine ⟨fun μ => k μ + (D.L : ℤ) ^ b * j μ, ?_⟩
  ext x
  simp only [ReflectionGrid.block, mem_ofPred_eq]
  refine forall_congr' fun μ => ?_
  rw [coarsen_corner g b k μ (j μ)]
variable {g}
theorem mover_image (hC : g.ReflectionGroupCoordForm) {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    (r : g.reflectionGroup) : g.mover S (r.1 '' S) = r := by
  have hr := hC.2.2.2.2.2.1 r.1 r.2 S hS
  have hspec : (g.mover S (r.1 '' S)).1 '' S = r.1 '' S :=
    Classical.epsilon_spec (p := fun r' : g.reflectionGroup => r'.1 '' S = r.1 '' S) ⟨r, rfl⟩
  exact (hC.2.2.2.2.2.2.1 S hS _ hr).unique hspec rfl
theorem coarseningTransports {b : ℕ} {k : Fin 4 → ℤ} (hC : g.ReflectionGroupCoordForm)
    (hC' : (g.coarsen b k).ReflectionGroupCoordForm) : g.CoarseningTransports b k := by
  have hle := reflectionGroup_coarsen_le g b k
  have hfine : ∀ (r : (g.coarsen b k).reflectionGroup) (S : Set AmbientSpace),
      S ∈ g.cellSet → r.1 '' S ∈ g.cellSet :=
    fun r S hS => hC.2.2.2.2.2.1 r.1 (hle r.2) S hS
  have hcoarse : ∀ (r : (g.coarsen b k).reflectionGroup) (S : Set AmbientSpace),
      S ∈ (g.coarsen b k).cellSet → r.1 '' S ∈ (g.coarsen b k).cellSet :=
    fun r S hS => hC'.2.2.2.2.2.1 r.1 r.2 S hS
  refine ⟨fun S hS S' hS' hsub F _ r => ⟨hfine r S hS, hcoarse r S' hS', image_mono hsub, ?_⟩, ?_⟩
  · have e1 : (g.coarsen b k).transportTo S' (r.1 '' S') F = (g.coarsen b k).transport r F := by
      rw [ReflectionGrid.transportTo, mover_image hC' hS' r]
    have e2 : g.transportTo S (r.1 '' S) F = g.transport ⟨r.1, hle r.2⟩ F := by
      rw [ReflectionGrid.transportTo]
      rw [show r.1 '' S = (⟨r.1, hle r.2⟩ : g.reflectionGroup).1 '' S from rfl, mover_image hC hS]
    rw [e1, e2]
    rfl
  · intro S' hS' r₁ r₂ S₁ S₂ h₁ h₁' h₂ h₂' hne heq
    obtain ⟨i, hi⟩ := hfine r₁ S₁ h₁
    have hu := existsUnique_coarsen_cell g b k i
    have a₁ : g.cell i ⊆ r₁.1 '' S' := hi ▸ image_mono h₁'
    have a₂ : g.cell i ⊆ r₂.1 '' S' := by
      rw [hi, heq]
      exact image_mono h₂'
    have hsame := hu.unique ⟨hcoarse r₁ S' hS', a₁⟩ ⟨hcoarse r₂ S' hS', a₂⟩
    have hr : r₁ = r₂ := (hC'.2.2.2.2.2.2.1 S' hS' _ (hcoarse r₂ S' hS')).unique hsame rfl
    subst hr
    exact hne (by rw [image_injective.2 r₁.1.injective heq])
theorem cellsInEnclosingBaseCell : g.CellsInEnclosingBaseCell := by
  intro O hO S hS
  obtain ⟨i, rfl⟩ := hO.2 hS
  have hi : i ∈ g.cellIndexSet O := hS
  have hfin := hO.finite_cellIndexSet
  have hL : 1 < D.L := by exact_mod_cast D.one_lt_factor
  show g.cell i ⊆ (g.coarsen _ _).cell 0
  apply cell_subset_coarsen_cell
  intro μ
  have h1 := (minCorner_isLeast hfin ⟨i, hi⟩ μ).2 ⟨i, hi, rfl⟩
  have h2 := (minScaleExponent_isLeast hL hfin).1 i hi μ
  simp only [Pi.zero_apply, mul_zero, add_zero]
  exact ⟨h1, by omega⟩
theorem statement_holds (hA : ReflectionGridArithmetic.Statement)
    (hE : GridBasicProperties.Statement) (hO : MeasurableObservablesAndLifts.Statement) :
    CellParityAndCoarsening.Statement := by
  intro D g hg
  have hC : ∀ g' : ReflectionGrid D, g'.ReflectionGroupCoordForm := fun g' => (hE D g').2.2.2.1
  refine ⟨moverSigns (hC g), fun h => ?_, fun b k => ⟨?_, ?_, ?_⟩, cellsInEnclosingBaseCell⟩
  · have hT := ((hA D).2.2.2 g).2 h
    exact halfOddInBlock (hC g) hT.1 hT.2
  · refine ⟨fun μ n => ⟨wall_coarsen g b k μ n, reflect_coarsen g b k μ n⟩,
      reflectionGroup_coarsen_le g b k, fun r => rfl⟩
  · refine ⟨fun j => ⟨coarsen_cell_eq_biUnion g b k j, ?_, ?_⟩, ?_, ?_, fun _ =>
      coarsen_blocks_subset g b k⟩
    · rw [ncard_image_of_injective _ g.cell_injective, ncard_coarseCellIndices]
    · ext S
      constructor
      · rintro ⟨⟨i, rfl⟩, h⟩
        exact ⟨i, mem_coarseCellIndices_of_subset g h, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, rfl⟩, cell_subset_coarsen_cell g hi⟩
    · rintro _ ⟨i, rfl⟩
      exact existsUnique_coarsen_cell g b k i
    · intro S hS S' hS' hsub
      exact (hO D).2.2.2.1 g (g.coarsen b k) hg (ReflectionGrid.IsCoarse.coarsen hg b k) S hS S' hS'
        (interior_mono hsub)
  · exact coarseningTransports (hC g) (hC _)
end CellParityAndCoarsening
end YangMills.Construction.ChessboardTori
end
