import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace CellsBlocksAndSigns
abbrev torusLength (D : ChessboardSetup) : ℝ := PeriodicLattice.torusSide D.L D.m
theorem int_eq_of_scaled_bounds {s : ℝ} (hs : 0 < s) {a b : ℤ} (h1 : s * b ≤ s * a + s / 2)
    (h2 : s * a + s / 2 ≤ s * b + s) : a = b := by
  have h3 : (b : ℝ) < a + 1 := by
    have : s * (b : ℝ) < s * (a + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  have h4 : (a : ℝ) < b + 1 := by
    have : s * (a : ℝ) < s * (b + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  have h5 : b < a + 1 := by exact_mod_cast h3
  have h6 : a < b + 1 := by exact_mod_cast h4
  omega
theorem exists_mod_decomp {n : ℤ} (hn : 0 < n) (a k : ℤ) :
    ∃ i j : ℤ, a ≤ i ∧ i ≤ a + n - 1 ∧ k = i + n * j := by
  have h1 := Int.emod_nonneg (k - a) hn.ne'
  have h2 := Int.emod_lt_of_pos (k - a) hn
  have h3 := Int.emod_add_mul_ediv (k - a) n
  exact ⟨a + (k - a) % n, (k - a) / n, by omega, by omega, by linarith⟩
theorem mod_decomp_unique {n a i i' j j' : ℤ} (hn : 0 < n) (h1 : a ≤ i) (h2 : i ≤ a + n - 1)
    (h3 : a ≤ i') (h4 : i' ≤ a + n - 1) (h : i + n * j = i' + n * j') : i = i' ∧ j = j' := by
  have hm : n * (j - j') = i' - i := by linarith
  have hj : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h5 | h5
    · have : j - j' ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ j - j' := by omega
      nlinarith
  subst hj
  exact ⟨by linarith, rfl⟩
theorem negOnePow_sum_eq_pow_card_odd (d : Fin 4 → ℤ) :
    (∑ μ, d μ).negOnePow = (-1 : ℤˣ) ^ (Finset.univ.filter fun μ => Odd (d μ)).card := by
  have key : ∀ s : Finset (Fin 4),
      (∑ μ ∈ s, d μ).negOnePow = (-1 : ℤˣ) ^ (s.filter fun μ => Odd (d μ)).card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Int.negOnePow_add, ih, Finset.filter_insert]
      by_cases h : Odd (d a)
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp [ha]), pow_succ,
          Int.negOnePow_odd _ h, mul_comm]
      · rw [if_neg h, Int.negOnePow_even _ (Int.not_odd_iff_even.mp h), one_mul]
  exact key _
def swapFirstIndex (k0 a : Fin 4 → ℤ) : Fin 4 → ℤ :=
  Function.update a 0 (if Even (a 0 - k0 0) then a 0 + 1 else a 0 - 1)
theorem swapFirstIndex_zero (k0 a : Fin 4 → ℤ) :
    swapFirstIndex k0 a 0 = if Even (a 0 - k0 0) then a 0 + 1 else a 0 - 1 := by
  simp [swapFirstIndex]
theorem swapFirstIndex_of_ne (k0 a : Fin 4 → ℤ) {μ : Fin 4} (h : μ ≠ 0) :
    swapFirstIndex k0 a μ = a μ := by
  simp [swapFirstIndex, Function.update_of_ne h]
theorem swapFirstIndex_swapFirstIndex (k0 a : Fin 4 → ℤ) :
    swapFirstIndex k0 (swapFirstIndex k0 a) = a := by
  funext μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [swapFirstIndex_zero, swapFirstIndex_zero]
    by_cases h : Even (a 0 - k0 0)
    · have h' : ¬ Even (a 0 + 1 - k0 0) := by
        rw [Int.even_iff] at h ⊢
        omega
      rw [if_pos h, if_neg h']
      ring
    · have h' : Even (a 0 - 1 - k0 0) := by
        rw [Int.even_iff] at h ⊢
        omega
      rw [if_neg h, if_pos h']
      ring
  · rw [swapFirstIndex_of_ne _ _ hμ, swapFirstIndex_of_ne _ _ hμ]
theorem odd_sum_swapFirstIndex_iff (k0 k1 a : Fin 4 → ℤ) :
    Odd (∑ μ, (swapFirstIndex k0 a μ - k1 μ)) ↔ ¬ Odd (∑ μ, (a μ - k1 μ)) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four, swapFirstIndex_zero,
    swapFirstIndex_of_ne _ _ (by decide : (1 : Fin 4) ≠ 0),
    swapFirstIndex_of_ne _ _ (by decide : (2 : Fin 4) ≠ 0),
    swapFirstIndex_of_ne _ _ (by decide : (3 : Fin 4) ≠ 0)]
  by_cases h : Even (a 0 - k0 0)
  · rw [if_pos h]
    simp only [Int.odd_iff]
    omega
  · rw [if_neg h]
    simp only [Int.odd_iff]
    omega
theorem two_mul_ncard_filter_of_involutive {I : Set (Fin 4 → ℤ)} (hI : I.Finite)
    {φ : (Fin 4 → ℤ) → Fin 4 → ℤ} (hφ : Function.Involutive φ) (hmap : ∀ a ∈ I, φ a ∈ I)
    {p : (Fin 4 → ℤ) → Prop} (hp : ∀ a, p (φ a) ↔ ¬ p a) :
    2 * {a ∈ I | p a}.ncard = I.ncard := by
  have himg : φ '' {a ∈ I | p a} = {a ∈ I | ¬ p a} := by
    ext b
    constructor
    · rintro ⟨a, ⟨ha, hpa⟩, rfl⟩
      exact ⟨hmap a ha, fun h => (hp a).mp h hpa⟩
    · rintro ⟨hb, hpb⟩
      refine ⟨φ b, ⟨hmap b hb, (hp b).mpr hpb⟩, hφ b⟩
  have hE : {a ∈ I | ¬ p a}.ncard = {a ∈ I | p a}.ncard := by
    rw [← himg]
    exact ncard_image_of_injective _ hφ.injective
  have hU : I = {a ∈ I | p a} ∪ {a ∈ I | ¬ p a} := by
    ext a
    by_cases h : p a <;> simp [h]
  have hD : Disjoint {a ∈ I | p a} {a ∈ I | ¬ p a} := by
    rw [Set.disjoint_left]
    rintro a ⟨-, h⟩ ⟨-, h'⟩
    exact h' h
  have := ncard_union_eq hD (hI.subset fun a h => h.1) (hI.subset fun a h => h.1)
  rw [← hU, hE] at this
  omega
section
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem mem_cell_iff {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ g.cell k ↔ ∀ μ, g.origin μ + g.cellSide * k μ ≤ x μ ∧
      x μ ≤ g.origin μ + g.cellSide * k μ + g.cellSide := by
  simp only [ReflectionGrid.cell, Set.mem_ofPred_eq, mem_Icc]
  refine forall_congr' fun μ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
def cellCentre (k : Fin 4 → ℤ) : AmbientSpace :=
  fun μ => g.origin μ + g.cellSide * k μ + g.cellSide / 2
theorem cellCentre_mem (k : Fin 4 → ℤ) : cellCentre g k ∈ g.cell k := by
  have hs := cellSide_pos g
  rw [mem_cell_iff]
  intro μ
  simp only [cellCentre]
  constructor <;> linarith
theorem eq_of_cellCentre_mem {k k' : Fin 4 → ℤ} (h : cellCentre g k ∈ g.cell k') : k = k' := by
  rw [mem_cell_iff] at h
  funext μ
  obtain ⟨h1, h2⟩ := h μ
  simp only [cellCentre] at h1 h2
  exact int_eq_of_scaled_bounds (cellSide_pos g) (by linarith) (by linarith)
theorem injective_cell : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
def transportMap (k k' : Fin 4 → ℤ) (x : AmbientSpace) : AmbientSpace := fun μ =>
  g.origin μ + if Even (k' μ - k μ) then g.coordShift ((k' μ - k μ) / 2) (x μ - g.origin μ)
    else g.coordReflect ((k μ + k' μ + 1) / 2) (x μ - g.origin μ)
theorem transportMap_actsOnCoord_of_even {k k' : Fin 4 → ℤ} {μ : Fin 4} (h : Even (k' μ - k μ)) :
    g.ActsOnCoord (transportMap g k k') μ (g.coordShift ((k' μ - k μ) / 2)) := by
  intro x
  simp only [transportMap, if_pos h, add_sub_cancel_left]
theorem transportMap_actsOnCoord_of_odd {k k' : Fin 4 → ℤ} {μ : Fin 4} (h : Odd (k' μ - k μ)) :
    g.ActsOnCoord (transportMap g k k') μ (g.coordReflect ((k μ + k' μ + 1) / 2)) := by
  intro x
  simp only [transportMap, if_neg (Int.not_even_iff_odd.mpr h), add_sub_cancel_left]
theorem transportMap_isProductOfCoordMaps (k k' : Fin 4 → ℤ) :
    g.IsProductOfCoordMaps (transportMap g k k') := by
  intro μ
  by_cases h : Even (k' μ - k μ)
  · exact Or.inl ⟨_, transportMap_actsOnCoord_of_even g h⟩
  · exact Or.inr ⟨_, transportMap_actsOnCoord_of_odd g (Int.not_even_iff_odd.mp h)⟩
theorem transportMap_mem_cell {k k' : Fin 4 → ℤ} {x : AmbientSpace} (hx : x ∈ g.cell k) :
    transportMap g k k' x ∈ g.cell k' := by
  rw [mem_cell_iff] at hx ⊢
  intro μ
  obtain ⟨h1, h2⟩ := hx μ
  by_cases h : Even (k' μ - k μ)
  · have hh := h
    obtain ⟨t, ht⟩ := hh
    have e : (k' μ - k μ) / 2 = t := by omega
    have e2 : (k' μ : ℝ) = k μ + 2 * t := by
      have : k' μ = k μ + 2 * t := by omega
      rw [this]
      push_cast
      ring
    simp only [transportMap, if_pos h, e, ReflectionGrid.coordShift, e2]
    constructor <;> linarith
  · obtain ⟨t, ht⟩ := Int.not_even_iff_odd.mp h
    have e : (k μ + k' μ + 1) / 2 = k μ + t + 1 := by omega
    have e2 : (k' μ : ℝ) = k μ + 2 * t + 1 := by
      have : k' μ = k μ + 2 * t + 1 := by omega
      rw [this]
      push_cast
      ring
    simp only [transportMap, if_neg h, e, ReflectionGrid.coordReflect, e2]
    push_cast
    constructor <;> linarith
theorem exists_mem_reflectionGroup_transport (cf : g.ReflectionGroupCoordForm) (k k' : Fin 4 → ℤ) :
    ∃ s ∈ g.reflectionGroup, (s : AmbientSpace → AmbientSpace) = transportMap g k k' ∧
      s '' g.cell k = g.cell k' := by
  obtain ⟨-, c2, -, -, -, c6, -, -⟩ := cf
  obtain ⟨s, hs, hf⟩ := c2 _ (transportMap_isProductOfCoordMaps g k k')
  refine ⟨s, hs, hf, ?_⟩
  obtain ⟨k'', h⟩ := c6 s hs _ ⟨k, rfl⟩
  have hsub : s '' g.cell k ⊆ g.cell k' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hf]
    exact transportMap_mem_cell g hx
  have hc : cellCentre g k'' ∈ g.cell k' := hsub (by rw [← h]; exact cellCentre_mem g k'')
  rw [← h, eq_of_cellCentre_mem g hc]
theorem coe_eq_transportMap (cf : g.ReflectionGroupCoordForm) {k k' : Fin 4 → ℤ}
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) (h : r '' g.cell k = g.cell k') :
    (r : AmbientSpace → AmbientSpace) = transportMap g k k' := by
  obtain ⟨s, hs, hf, him⟩ := exists_mem_reflectionGroup_transport g cf k k'
  obtain ⟨-, -, -, -, -, -, c7, -⟩ := cf
  have e := (c7 _ ⟨k, rfl⟩ _ ⟨k', rfl⟩).unique (y₁ := ⟨r, hr⟩) (y₂ := ⟨s, hs⟩) h him
  have e' : r = s := congrArg Subtype.val e
  rw [e', hf]
theorem reflectsCoord_transportMap_iff (k k' : Fin 4 → ℤ) (μ : Fin 4) :
    g.ReflectsCoord (transportMap g k k') μ ↔ Odd (k' μ - k μ) := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra h
    have he := Int.not_odd_iff_even.mp h
    have h0 := hc g.origin
    have h1 := hc (g.origin + coordVec μ)
    have a0 := transportMap_actsOnCoord_of_even g he g.origin
    have a1 := transportMap_actsOnCoord_of_even g he (g.origin + coordVec μ)
    simp only [ReflectionGrid.coordShift, ReflectionGrid.coordReflect, Pi.add_apply, coordVec,
      Pi.single_eq_same, sub_self, add_sub_cancel_left] at h0 h1 a0 a1
    linarith
  · intro h
    exact ⟨_, transportMap_actsOnCoord_of_odd g h⟩
theorem orientationSign_eq_negOnePow (cf : g.ReflectionGroupCoordForm) {k k' : Fin 4 → ℤ}
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) (h : r '' g.cell k = g.cell k') :
    orientationSign r = (∑ μ, (k' μ - k μ)).negOnePow := by
  have e := coe_eq_transportMap g cf hr h
  obtain ⟨-, -, c3, -⟩ := cf
  have hcard : g.numReflectedCoords r =
      (Finset.univ.filter fun μ => Odd (k' μ - k μ)).card := by
    rw [ReflectionGrid.numReflectedCoords, e]
    refine congrArg Finset.card ?_
    ext μ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact reflectsCoord_transportMap_iff g k k' μ
  rw [c3 r hr, negOnePow_sum_eq_pow_card_odd, hcard]
theorem cellCarrierForm (cf : g.ReflectionGroupCoordForm) : g.CellCarrierForm := by
  intro k k' r hr h
  have e := coe_eq_transportMap g cf hr h
  refine ⟨fun μ => ⟨fun he => ?_, fun ho => ?_⟩, orientationSign_eq_negOnePow g cf hr h⟩
  · rw [e]
    exact transportMap_actsOnCoord_of_even g he
  · rw [e]
    exact transportMap_actsOnCoord_of_odd g ho
def shiftIndex (n : ℤ) (k j : Fin 4 → ℤ) : Fin 4 → ℤ := fun μ => k μ + n * j μ
variable {g} {n : ℤ}
theorem image_translate_cell (hn : torusLength D = n * g.cellSide) (k j : Fin 4 → ℤ) :
    translate (TestFunctions.latticeTranslate (torusLength D) j) '' g.cell k =
      g.cell (shiftIndex n k j) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_cell_iff] at hx ⊢
    intro μ
    obtain ⟨h1, h2⟩ := hx μ
    simp only [translate, Pi.add_apply, TestFunctions.latticeTranslate, shiftIndex, hn]
    push_cast
    constructor <;> linarith
  · intro y hy
    rw [mem_cell_iff] at hy
    refine ⟨y - TestFunctions.latticeTranslate (torusLength D) j, ?_, by simp [translate]⟩
    rw [mem_cell_iff]
    intro μ
    obtain ⟨h1, h2⟩ := hy μ
    simp only [shiftIndex] at h1 h2
    push_cast at h1 h2
    simp only [Pi.sub_apply, TestFunctions.latticeTranslate, hn]
    constructor <;> linarith
theorem image_proj_translate (j : Fin 4 → ℤ) (A : Set AmbientSpace) :
    D.proj '' (translate (TestFunctions.latticeTranslate (torusLength D) j) '' A) =
      D.proj '' A := by
  rw [← image_comp]
  refine image_congr fun x _ => ?_
  exact TestFunctions.torusProj_add_latticeTranslate _ _ _
theorem image_translate_interior (v : AmbientSpace) (A : Set AmbientSpace) :
    translate v '' interior A = interior (translate v '' A) :=
  (Homeomorph.addRight v).image_interior A
theorem proj_image_cell_eq_iff (hn : torusLength D = n * g.cellSide) {k k' : Fin 4 → ℤ} :
    D.proj '' g.cell k = D.proj '' g.cell k' ↔ ∃ j, k' = shiftIndex n k j := by
  constructor
  · intro h
    have hu : D.proj (cellCentre g k) ∈ D.proj '' g.cell k' := by
      rw [← h]
      exact mem_image_of_mem _ (cellCentre_mem g k)
    obtain ⟨y, hy, hyu⟩ := hu
    obtain ⟨j, hj⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hyu
    refine ⟨j, ?_⟩
    subst hj
    rw [mem_cell_iff] at hy
    funext μ
    obtain ⟨h1, h2⟩ := hy μ
    simp only [cellCentre, Pi.add_apply, TestFunctions.latticeTranslate, hn] at h1 h2
    refine (int_eq_of_scaled_bounds (cellSide_pos g) ?_ ?_).symm
    · simp only [shiftIndex]
      push_cast
      linarith
    · simp only [shiftIndex]
      push_cast
      linarith
  · rintro ⟨j, rfl⟩
    rw [← image_translate_cell hn, image_proj_translate]
theorem sameTorusImageCriterion (hn : torusLength D = n * g.cellSide) (hcp : g.cellsAcross = n) :
    g.SameTorusImageCriterion := by
  intro k k'
  refine ⟨?_, ?_, ?_⟩
  · rw [proj_image_cell_eq_iff hn]
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j, fun μ => ?_⟩
      rw [hcp]
      simp only [shiftIndex]
      push_cast
      ring
    · rintro ⟨j, hj⟩
      refine ⟨j, funext fun μ => ?_⟩
      have h := hj μ
      rw [hcp] at h
      have h' : k' μ - k μ = n * j μ := by exact_mod_cast h
      simp only [shiftIndex]
      linarith
  · rw [proj_image_cell_eq_iff hn]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, (image_translate_cell hn k j).symm⟩
    · rintro ⟨_, ⟨j, rfl⟩, h⟩
      rw [image_translate_cell hn] at h
      exact ⟨j, injective_cell g h⟩
  · intro h
    obtain ⟨j, rfl⟩ := (proj_image_cell_eq_iff hn).mp h
    rw [← image_translate_cell hn, ← image_translate_interior, image_proj_translate]
theorem exists_blockIndex (hpos : 0 < g.cellsPerTorusSide) (k0 k : Fin 4 → ℤ) :
    ∃ i ∈ g.blockIndices k0, ∃ j, k = shiftIndex g.cellsPerTorusSide i j := by
  choose i j h1 h2 h3 using fun μ => exists_mod_decomp hpos (k0 μ) (k μ)
  exact ⟨i, fun μ => ⟨h1 μ, h2 μ⟩, j, funext h3⟩
theorem blockIndex_unique (hpos : 0 < g.cellsPerTorusSide) {k0 i i' j j' : Fin 4 → ℤ}
    (hi : i ∈ g.blockIndices k0) (hi' : i' ∈ g.blockIndices k0)
    (h : shiftIndex g.cellsPerTorusSide i j = shiftIndex g.cellsPerTorusSide i' j') :
    i = i' ∧ j = j' := by
  have e := fun μ => mod_decomp_unique hpos (hi μ).1 (hi μ).2 (hi' μ).1 (hi' μ).2 (congrFun h μ)
  exact ⟨funext fun μ => (e μ).1, funext fun μ => (e μ).2⟩
theorem blockCellsRepresent (hn : torusLength D = g.cellsPerTorusSide * g.cellSide)
    (hpos : 0 < g.cellsPerTorusSide) (k0 : Fin 4 → ℤ)
    (hc : g.cellsWithin (g.block k0) = g.cell '' g.blockIndices k0) :
    g.BlockCellsRepresent (g.block k0) := by
  refine ⟨?_, BijOn.mk ?_ ?_ ?_⟩
  · rintro _ ⟨k, rfl⟩
    obtain ⟨i, hi, j, rfl⟩ := exists_blockIndex hpos k0 k
    refine ⟨(g.cell i, TestFunctions.latticeTranslate (torusLength D) j),
      ⟨by rw [hc]; exact mem_image_of_mem _ hi, ⟨j, rfl⟩, (image_translate_cell hn i j).symm⟩, ?_⟩
    rintro ⟨S', v⟩ ⟨h1, ⟨j', rfl⟩, h3⟩
    dsimp only at h1 h3
    rw [hc] at h1
    obtain ⟨i', hi', rfl⟩ := h1
    rw [image_translate_cell hn] at h3
    obtain ⟨e1, e2⟩ := blockIndex_unique hpos hi' hi (injective_cell g h3).symm
    rw [e1, e2]
  · intro S hS
    exact mem_image_of_mem _ hS.1
  · intro S hS S' hS' e
    rw [hc] at hS hS'
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hS'
    obtain ⟨j, hj⟩ := (proj_image_cell_eq_iff hn).mp e
    have h0 : shiftIndex g.cellsPerTorusSide b 0 = shiftIndex g.cellsPerTorusSide a j := by
      rw [← hj]
      funext μ
      simp [shiftIndex]
    rw [(blockIndex_unique hpos hb ha h0).1]
  · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    obtain ⟨i, hi, j, rfl⟩ := exists_blockIndex hpos k0 k
    refine ⟨g.cell i, by rw [hc]; exact mem_image_of_mem _ hi, ?_⟩
    exact (proj_image_cell_eq_iff hn).mpr ⟨j, rfl⟩
theorem exists_translate_mem (cf : g.ReflectionGroupCoordForm)
    (hn : torusLength D = n * g.cellSide) (hev : Even n) (j : Fin 4 → ℤ) :
    ∃ t ∈ g.reflectionGroup, (t : AmbientSpace → AmbientSpace) =
      translate (TestFunctions.latticeTranslate (torusLength D) j) ∧ orientationSign t = 1 := by
  obtain ⟨h, hh⟩ := hev
  obtain ⟨-, -, -, -, -, -, -, c8⟩ := cf
  obtain ⟨t, ht, e, s⟩ := c8 fun μ => h * j μ
  refine ⟨t, ht, ?_, s⟩
  rw [e]
  congr 1
  funext μ
  simp only [TestFunctions.latticeTranslate, hn, hh]
  push_cast
  ring
theorem translate_translate_neg (j : Fin 4 → ℤ) (y : AmbientSpace) :
    translate (TestFunctions.latticeTranslate (torusLength D) j)
      (translate (TestFunctions.latticeTranslate (torusLength D) (-j)) y) = y := by
  funext μ
  simp only [translate, TestFunctions.latticeTranslate, Pi.add_apply, Pi.neg_apply]
  push_cast
  ring
theorem exists_translate_comp_block (cf : g.ReflectionGroupCoordForm)
    (hn : torusLength D = n * g.cellSide) (hev : Even n) {B S : Set AmbientSpace}
    (hB : g.BlockCellsRepresent B) (hS : S ∈ g.cellSet)
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    ∃ v ∈ D.periodVectors, ∃ r₀ ∈ g.elementsIntoBlock B S,
      (r : AmbientSpace → AmbientSpace) = translate v ∘ r₀ := by
  have c6 := cf.2.2.2.2.2.1
  obtain ⟨⟨S', v⟩, ⟨h1, ⟨j, rfl⟩, h3⟩, -⟩ := hB.1 (r '' S) (c6 r hr S hS)
  dsimp only at h1 h3
  obtain ⟨t, ht, e, -⟩ := exists_translate_mem cf hn hev (-j)
  have hcomp : translate (TestFunctions.latticeTranslate (torusLength D) (-j)) ∘
      translate (TestFunctions.latticeTranslate (torusLength D) j) = id := by
    funext y
    have h := translate_translate_neg (D := D) (-j) y
    rwa [neg_neg] at h
  have himg : ((t * r : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) '' S = S' := by
    rw [Equiv.Perm.coe_mul, image_comp, h3, e, ← image_comp, hcomp, image_id]
  refine ⟨_, ⟨j, rfl⟩, t * r, ⟨g.reflectionGroup.mul_mem ht hr, ?_⟩, ?_⟩
  · rw [himg]
    exact h1
  · funext x
    simp only [Function.comp, Equiv.Perm.coe_mul, e]
    exact (translate_translate_neg j (r x)).symm
theorem orientationSign_and_descend_eq (cf : g.ReflectionGroupCoordForm)
    (hn : torusLength D = n * g.cellSide) (hev : Even n) {r r₀ : Equiv.Perm AmbientSpace}
    (h₀ : r₀ ∈ g.reflectionGroup) {v : AmbientSpace} (hv : v ∈ D.periodVectors)
    (e : (r : AmbientSpace → AmbientSpace) = translate v ∘ r₀) :
    orientationSign r = orientationSign r₀ ∧
      ReflectionGrid.descendToTorus (D := D) r = ReflectionGrid.descendToTorus (D := D) r₀ := by
  obtain ⟨j, rfl⟩ := hv
  obtain ⟨t, ht, et, st⟩ := exists_translate_mem cf hn hev j
  have hmul : (r : AmbientSpace → AmbientSpace) =
      ((t * r₀ : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) := by
    rw [e, Equiv.Perm.coe_mul, et]
  refine ⟨?_, ?_⟩
  · rw [hmul, cf.2.2.2.1 t ht r₀ h₀, st, one_mul]
  · funext u
    change TorusMetric.torusProj _ (r (TestFunctions.liftPoint u)) =
      TorusMetric.torusProj _ (r₀ (TestFunctions.liftPoint u))
    rw [e]
    exact TestFunctions.torusProj_add_latticeTranslate _ _ _
theorem proj_comp_eq (ii : g.DescendsToTorus) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) :
    D.proj ∘ r = ReflectionGrid.descendToTorus (D := D) r ∘ D.proj := by
  obtain ⟨r', h, -⟩ := ii.2.2.1 r hr
  have key : ReflectionGrid.descendToTorus (D := D) r = r' := by
    funext u
    have hu : D.proj (TestFunctions.liftPoint u) = u := TestFunctions.torusProj_liftPoint u
    change D.proj (r (TestFunctions.liftPoint u)) = r' u
    have := congrFun h (TestFunctions.liftPoint u)
    simp only [Function.comp] at this
    rw [this, hu]
  rw [key, h]
theorem blockElementsRepresent (cf : g.ReflectionGroupCoordForm) (ii : g.DescendsToTorus)
    (hn : torusLength D = n * g.cellSide) (hev : Even n) {B S : Set AmbientSpace}
    (hB : g.BlockCellsRepresent B) (hS : S ∈ g.cellSet) :
    g.BlockElementsRepresent B S := by
  have c6 := cf.2.2.2.2.2.1
  have c7 := cf.2.2.2.2.2.2.1
  refine ⟨?_, ?_, BijOn.mk ?_ ?_ ?_⟩
  · intro r hr
    obtain ⟨v, hv, r₀, h₀, e⟩ := exists_translate_comp_block cf hn hev hB hS hr
    refine ⟨(v, r₀), ⟨hv, h₀, e⟩, ?_⟩
    rintro ⟨v', r₁⟩ ⟨hv', h₁, e'⟩
    dsimp only at hv' h₁ e'
    have i0 : r '' S = translate v '' (r₀ '' S) := by rw [e, image_comp]
    have i1 : r '' S = translate v' '' (r₁ '' S) := by rw [e', image_comp]
    have hu := (hB.1 (r '' S) (c6 r hr S hS)).unique (y₁ := (r₀ '' S, v)) (y₂ := (r₁ '' S, v'))
      ⟨h₀.2, hv, i0⟩ ⟨h₁.2, hv', i1⟩
    have hvv : v = v' := (Prod.ext_iff.mp hu).2
    subst hvv
    have hrr : r₀ = r₁ := Equiv.ext fun x => add_right_cancel (congrFun (e.symm.trans e') x)
    rw [hrr]
  · intro r _ v hv r₀ h₀ e
    exact orientationSign_and_descend_eq cf hn hev h₀.1 hv e
  · intro r₀ h₀
    exact ⟨r₀, h₀.1, proj_comp_eq ii h₀.1⟩
  · intro r₀ h₀ r₁ h₁ e
    have e' : ReflectionGrid.descendToTorus (D := D) r₀ =
        ReflectionGrid.descendToTorus (D := D) r₁ := e
    have imgs : D.proj '' (r₀ '' S) = D.proj '' (r₁ '' S) := by
      rw [← image_comp, ← image_comp, proj_comp_eq ii h₀.1, proj_comp_eq ii h₁.1, e']
    have hs : r₀ '' S = r₁ '' S := hB.2.injOn h₀.2 h₁.2 imgs
    have hu := (c7 S hS _ (c6 r₀ h₀.1 S hS)).unique (y₁ := ⟨r₀, h₀.1⟩) (y₂ := ⟨r₁, h₁.1⟩) rfl hs.symm
    exact congrArg Subtype.val hu
  · rintro r' ⟨r, hr, hc⟩
    obtain ⟨v, hv, r₀, h₀, e⟩ := exists_translate_comp_block cf hn hev hB hS hr
    refine ⟨r₀, h₀, ?_⟩
    have h1 := (orientationSign_and_descend_eq cf hn hev h₀.1 hv e).2
    have h2 : ReflectionGrid.descendToTorus (D := D) r = r' := by
      funext u
      obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
      have a1 := congrFun (proj_comp_eq ii hr) x
      have a2 := congrFun hc x
      exact a1.symm.trans a2
    exact h1.symm.trans h2
theorem swapFirstIndex_mem (hev : Even g.cellsPerTorusSide) {k0 a : Fin 4 → ℤ}
    (ha : a ∈ g.blockIndices k0) : swapFirstIndex k0 a ∈ g.blockIndices k0 := by
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    obtain ⟨h1, h2⟩ := ha 0
    obtain ⟨c, hc⟩ := hev
    rw [swapFirstIndex_zero]
    by_cases h : Even (a 0 - k0 0)
    · rw [if_pos h]
      obtain ⟨t, ht⟩ := h
      omega
    · rw [if_neg h]
      obtain ⟨t, ht⟩ := Int.not_even_iff_odd.mp h
      omega
  · rw [swapFirstIndex_of_ne _ _ hμ]
    exact ha μ
theorem oddCells_eq_image (cf : g.ReflectionGroupCoordForm) {k0 k1 : Fin 4 → ℤ}
    (hc : g.cellsWithin (g.block k0) = g.cell '' g.blockIndices k0) :
    {S' ∈ g.cellsWithin (g.block k0) |
        ∃ r ∈ g.reflectionGroup, orientationSign r = -1 ∧ S' = r '' g.cell k1} =
      g.cell '' {a ∈ g.blockIndices k0 | Odd (∑ μ, (a μ - k1 μ))} := by
  ext S'
  constructor
  · rintro ⟨h, r, hr, hs, rfl⟩
    rw [hc] at h
    obtain ⟨a, ha, e⟩ := h
    refine ⟨a, ⟨ha, ?_⟩, e⟩
    have h1 := orientationSign_eq_negOnePow g cf hr e.symm
    by_contra ho
    rw [Int.negOnePow_even _ (Int.not_odd_iff_even.mp ho), hs] at h1
    exact absurd h1 (by decide)
  · rintro ⟨a, ⟨ha, ho⟩, rfl⟩
    refine ⟨by rw [hc]; exact mem_image_of_mem _ ha, ?_⟩
    obtain ⟨s, hs, -, him⟩ := exists_mem_reflectionGroup_transport g cf k1 a
    exact ⟨s, hs, by rw [orientationSign_eq_negOnePow g cf hs him]; exact Int.negOnePow_odd _ ho,
      him.symm⟩
theorem torusSign_descendToTorus (gt : g.TorusGroupQuotient) (ii : g.DescendsToTorus)
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    g.torusSign (ReflectionGrid.descendToTorus (D := D) r) = orientationSign r := by
  have hspec : D.proj ∘ (g.inducingElement (ReflectionGrid.descendToTorus (D := D) r)).1 =
      ReflectionGrid.descendToTorus (D := D) r ∘ D.proj :=
    Classical.epsilon_spec (p := fun s : g.reflectionGroup =>
      D.proj ∘ s.1 = ReflectionGrid.descendToTorus (D := D) r ∘ D.proj)
      ⟨⟨r, hr⟩, proj_comp_eq ii hr⟩
  exact gt.2.2.2.1 _ (g.inducingElement _).2 r hr _ hspec (proj_comp_eq ii hr)
theorem halfOddCount (cf : g.ReflectionGroupCoordForm) (ii : g.DescendsToTorus)
    (gt : g.TorusGroupQuotient) (hcp : g.cellsAcross = g.cellsPerTorusSide)
    (hev : Even g.cellsPerTorusSide) {k0 k1 : Fin 4 → ℤ}
    (hc : g.cellsWithin (g.block k0) = g.cell '' g.blockIndices k0)
    (hcard : ((g.cell '' g.blockIndices k0).ncard : ℤ) = g.cellsPerTorusSide ^ 4)
    (hpos : 0 < g.cellsPerTorusSide)
    (hE : g.BlockElementsRepresent (g.block k0) (g.cell k1)) :
    g.HalfOddCount (g.block k0) (g.cell k1) := by
  have c6 := cf.2.2.2.2.2.1
  have c7 := cf.2.2.2.2.2.2.1
  have hI : (g.cell '' g.blockIndices k0).ncard = (g.blockIndices k0).ncard :=
    ncard_image_of_injective _ (injective_cell g)
  have hIpos : 0 < (g.blockIndices k0).ncard := by
    have h4 : 0 < g.cellsPerTorusSide ^ 4 := by positivity
    rw [← hcard, hI] at h4
    exact_mod_cast h4
  have hfin : (g.blockIndices k0).Finite := finite_of_ncard_pos hIpos
  have htwo := two_mul_ncard_filter_of_involutive hfin
    (φ := swapFirstIndex k0) (fun a => swapFirstIndex_swapFirstIndex k0 a)
    (fun a ha => swapFirstIndex_mem hev ha)
    (p := fun a => Odd (∑ μ, (a μ - k1 μ))) (fun a => odd_sum_swapFirstIndex_iff k0 k1 a)
  have hodd : ({S' ∈ g.cellsWithin (g.block k0) |
      ∃ r ∈ g.reflectionGroup, orientationSign r = -1 ∧ S' = r '' g.cell k1}.ncard : ℝ) =
      g.cellsAcross ^ 4 / 2 := by
    rw [oddCells_eq_image cf hc, ncard_image_of_injective _ (injective_cell g), hcp]
    have h1 : (2 * ({a ∈ g.blockIndices k0 | Odd (∑ μ, (a μ - k1 μ))}.ncard : ℤ)) =
        g.cellsPerTorusSide ^ 4 := by
      rw [← hcard, hI]
      exact_mod_cast htwo
    have h2 : (2 * ({a ∈ g.blockIndices k0 | Odd (∑ μ, (a μ - k1 μ))}.ncard : ℝ)) =
        (g.cellsPerTorusSide : ℝ) ^ 4 := by
      exact_mod_cast h1
    linarith
  refine ⟨?_, hodd, ?_, ?_⟩
  · rw [hc, hcp]
    exact_mod_cast hcard
  · rw [← gt.2.1, Nat.card_coe_set_eq]
  · rw [← hodd]
    have hbij := hE.2.2
    set Q : Set (Equiv.Perm AmbientSpace) :=
      {r₀ ∈ g.elementsIntoBlock (g.block k0) (g.cell k1) | orientationSign r₀ = -1} with hQ
    have hT : {r' ∈ g.inducedTorusMaps | g.torusSign r' = -1} =
        (fun r₀ : Equiv.Perm AmbientSpace => ReflectionGrid.descendToTorus (D := D) r₀) '' Q := by
      ext r'
      constructor
      · rintro ⟨hr', hs⟩
        obtain ⟨r₀, h₀, rfl⟩ := hbij.surjOn hr'
        exact ⟨r₀, ⟨h₀, by rw [← torusSign_descendToTorus gt ii h₀.1]; exact hs⟩, rfl⟩
      · rintro ⟨r₀, ⟨h₀, hs⟩, rfl⟩
        exact ⟨hbij.mapsTo h₀, by rw [torusSign_descendToTorus gt ii h₀.1]; exact hs⟩
    have hC : {S' ∈ g.cellsWithin (g.block k0) |
        ∃ r ∈ g.reflectionGroup, orientationSign r = -1 ∧ S' = r '' g.cell k1} =
        (fun r₀ : Equiv.Perm AmbientSpace => r₀ '' g.cell k1) '' Q := by
      ext S'
      constructor
      · rintro ⟨h, r, hr, hs, rfl⟩
        exact ⟨r, ⟨⟨hr, h⟩, hs⟩, rfl⟩
      · rintro ⟨r₀, ⟨h₀, hs⟩, rfl⟩
        exact ⟨h₀.2, r₀, h₀.1, hs, rfl⟩
    have hinjT := hbij.injOn.mono (show Q ⊆ _ from fun r h => h.1)
    have hinjC : InjOn (fun r₀ : Equiv.Perm AmbientSpace => r₀ '' g.cell k1) Q := by
      intro r₀ h₀ r₁ h₁ e
      have hu := (c7 _ ⟨k1, rfl⟩ _ (c6 r₀ h₀.1.1 _ ⟨k1, rfl⟩)).unique (y₁ := ⟨r₀, h₀.1.1⟩)
        (y₂ := ⟨r₁, h₁.1.1⟩) rfl e.symm
      exact congrArg Subtype.val hu
    rw [hT, hC, hinjT.ncard_image, hinjC.ncard_image]
end
theorem statement_holds (hG : GridBasicProperties.Statement)
    (hA : ReflectionGridArithmetic.Statement) : CellsBlocksAndSigns.Statement := by
  intro D g
  obtain ⟨-, -, -, cf, -, -, hside⟩ := hG D g
  refine ⟨cellCarrierForm g cf, fun h2 => ?_⟩
  obtain ⟨ii, gt, -⟩ := hside h2
  obtain ⟨hT, hBox⟩ := ((hA D).2.2.2 g).2 h2
  obtain ⟨-, hcp, hev, h2n, -⟩ := hT
  have hpos : 0 < g.cellsPerTorusSide := by omega
  have hn : torusLength D = g.cellsPerTorusSide * g.cellSide := by
    rw [← hcp, ReflectionGrid.cellsAcross, div_mul_cancel₀ _ (cellSide_pos g).ne']
  refine ⟨sameTorusImageCriterion hn hcp, ?_⟩
  rintro _ ⟨k0, rfl⟩
  obtain ⟨-, hc, hcard⟩ := hBox k0
  have hB := blockCellsRepresent hn hpos k0 hc
  refine ⟨hB, ?_⟩
  rintro _ ⟨k1, rfl⟩
  have hE := blockElementsRepresent cf ii hn hev hB ⟨k1, rfl⟩
  exact ⟨hE, halfOddCount cf ii gt hcp hev hc hcard hpos hE⟩
end CellsBlocksAndSigns
end YangMills.Construction.ChessboardTori
end
