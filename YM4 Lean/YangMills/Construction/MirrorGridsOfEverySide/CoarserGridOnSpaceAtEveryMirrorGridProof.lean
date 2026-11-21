import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnTheTorusAtEveryMirrorGridProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
variable {D : GridSetup}
private theorem cellSide_pos (g : ReflectionGrid D) : 0 < g.cellSide :=
  zpow_pos (by linarith [D.one_lt_factor]) _
private theorem origin_shift_of_wallSet_subset {g g' : ReflectionGrid D}
    (hsub : g'.wallSet ⊆ g.wallSet) (μ : Fin 4) :
    ∃ m : ℤ, g'.origin μ = g.origin μ + m * g.cellSide := by
  obtain ⟨⟨ν, n⟩, hn⟩ := hsub ⟨(μ, 0), rfl⟩
  replace hn : g.wall ν n = g'.wall μ 0 := hn
  by_cases hνμ : ν = μ
  · subst hνμ
    refine ⟨n, ?_⟩
    have hp : (fun _ => g.origin ν + n * g.cellSide : InfiniteLattice.AmbientSpace) ∈ g.wall ν n := rfl
    rw [hn] at hp
    have hp' : g.origin ν + n * g.cellSide = g'.origin ν + ((0 : ℤ) : ℝ) * g'.cellSide := hp
    simpa using hp'.symm
  · exfalso
    have hp : (Function.update (fun _ => g.origin ν + n * g.cellSide + 1) μ (g'.origin μ) :
        InfiniteLattice.AmbientSpace) ∈ g'.wall μ 0 := by
      simp [ReflectionGrid.wall]
    rw [← hn] at hp
    have hp' : Function.update (fun _ => g.origin ν + n * g.cellSide + 1) μ (g'.origin μ) ν =
        g.origin ν + n * g.cellSide := hp
    rw [Function.update_of_ne hνμ] at hp'
    linarith
private theorem cell_subset_coarse_cell {g g' : ReflectionGrid D} {m : Fin 4 → ℤ} {N : ℤ}
    (hm : ∀ μ, g'.origin μ = g.origin μ + m μ * g.cellSide) (hN : g'.cellSide = N * g.cellSide)
    {i i' : Fin 4 → ℤ}
    (hi : ∀ μ, 0 ≤ i μ - m μ - N * i' μ ∧ i μ - m μ - N * i' μ ≤ N - 1) :
    g.cell i ⊆ g'.cell i' := by
  intro y hy μ
  obtain ⟨hy0, hy1⟩ := hy μ
  have hpos := cellSide_pos g
  obtain ⟨hlo, hhi⟩ := hi μ
  have hlo' : (0 : ℝ) ≤ (i μ : ℝ) - m μ - N * i' μ := by exact_mod_cast hlo
  have hhi' : (i μ : ℝ) - m μ - N * i' μ ≤ N - 1 := by exact_mod_cast hhi
  have hprod := mul_nonneg hlo' hpos.le
  have hbound := mul_le_mul_of_nonneg_right hhi' hpos.le
  rw [hm μ, hN]
  constructor
  · nlinarith
  · nlinarith
private theorem cellCentre_mem_cell (g : ReflectionGrid D) (i : Fin 4 → ℤ) :
    g.cellCentre i ∈ g.cell i := by apply _root_.YangMills.Construction.MirrorGridsAllSides.CoarseningOnTorus.cellCentre_mem_cell <;> assumption
private theorem index_bounds_of_cell_subset {g g' : ReflectionGrid D} {m : Fin 4 → ℤ} {N : ℤ}
    (hm : ∀ μ, g'.origin μ = g.origin μ + m μ * g.cellSide) (hN : g'.cellSide = N * g.cellSide)
    {i i' : Fin 4 → ℤ} (hsub : g.cell i ⊆ g'.cell i') (μ : Fin 4) :
    0 ≤ i μ - m μ - N * i' μ ∧ i μ - m μ - N * i' μ ≤ N - 1 := by
  obtain ⟨hc0, hc1⟩ := hsub (cellCentre_mem_cell g i) μ
  simp only [ReflectionGrid.cellCentre] at hc0 hc1
  rw [hm μ, hN] at hc0 hc1
  have hpos := cellSide_pos g
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = i μ - m μ - N * i' μ := ⟨_, rfl⟩
  rw [← hr]
  have hrcast : (r : ℝ) = (i μ : ℝ) - m μ - N * i' μ := by
    rw [hr]
    push_cast
    ring
  have hdiff : g.origin μ + g.cellSide * i μ + g.cellSide / 2 -
      (g.origin μ + m μ * g.cellSide + N * g.cellSide * i' μ) = ((r : ℝ) + 1 / 2) * g.cellSide := by
    rw [hrcast]
    ring
  rw [hdiff] at hc0 hc1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) + 1 / 2 := (mul_nonneg_iff_of_pos_right hpos).mp hc0
  have hr1 : (r : ℝ) + 1 / 2 ≤ N := le_of_mul_le_mul_right hc1 hpos
  constructor
  · by_contra hneg
    have hle : r ≤ -1 := by omega
    have hle' : (r : ℝ) ≤ -1 := by exact_mod_cast hle
    linarith
  · by_contra hneg
    have hge : N ≤ r := by omega
    have hge' : (N : ℝ) ≤ r := by exact_mod_cast hge
    linarith
private theorem exists_unit_interval_index {t : ℝ} {N : ℤ} (hN : 1 ≤ N) (ht0 : 0 ≤ t) (ht1 : t ≤ N) :
    ∃ j : ℤ, 0 ≤ j ∧ j ≤ N - 1 ∧ (j : ℝ) ≤ t ∧ t ≤ j + 1 := by
  refine ⟨min ⌊t⌋ (N - 1), le_min (Int.floor_nonneg.mpr ht0) (by omega), min_le_right _ _, ?_, ?_⟩
  · exact (Int.cast_le.mpr (min_le_left _ _)).trans (Int.floor_le t)
  · rcases le_total ⌊t⌋ (N - 1) with hle | hle
    · rw [min_eq_left hle]
      exact (Int.lt_floor_add_one t).le
    · rw [min_eq_right hle]
      push_cast
      linarith
private theorem exists_fine_cell_of_mem {g g' : ReflectionGrid D} {m : Fin 4 → ℤ} {N : ℤ}
    (hm : ∀ μ, g'.origin μ = g.origin μ + m μ * g.cellSide) (hN : g'.cellSide = N * g.cellSide)
    (hN1 : 1 ≤ N) {i' : Fin 4 → ℤ} {y : InfiniteLattice.AmbientSpace} (hy : y ∈ g'.cell i') :
    ∃ i : Fin 4 → ℤ, y ∈ g.cell i ∧ g.cell i ⊆ g'.cell i' := by
  have hpos := cellSide_pos g
  have hj : ∀ μ, ∃ j : ℤ, 0 ≤ j ∧ j ≤ N - 1 ∧
      (j : ℝ) ≤ (y μ - (g'.origin μ + g'.cellSide * i' μ)) / g.cellSide ∧
      (y μ - (g'.origin μ + g'.cellSide * i' μ)) / g.cellSide ≤ j + 1 := by
    intro μ
    obtain ⟨hy0, hy1⟩ := hy μ
    refine exists_unit_interval_index hN1 (div_nonneg hy0 hpos.le) ?_
    rw [div_le_iff₀ hpos, ← hN]
    exact hy1
  choose j hj0 hj1 hj2 hj3 using hj
  refine ⟨fun μ => m μ + N * i' μ + j μ, fun μ => ?_, cell_subset_coarse_cell hm hN fun μ => ?_⟩
  · have hlow := (le_div_iff₀ hpos).mp (hj2 μ)
    have hupp := (div_le_iff₀ hpos).mp (hj3 μ)
    rw [hm μ, hN] at hlow hupp
    push_cast
    constructor
    · nlinarith
    · nlinarith
  · have := hj0 μ
    have := hj1 μ
    constructor <;> omega
private theorem cell_injective (g : ReflectionGrid D) : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
private theorem ncard_fine_cells_in_coarse_cell {g g' : ReflectionGrid D} {m : Fin 4 → ℤ} {M : ℕ}
    (hM : 0 < M) (hm : ∀ μ, g'.origin μ = g.origin μ + m μ * g.cellSide)
    (hN : g'.cellSide = ((M : ℤ) : ℝ) * g.cellSide) (i' : Fin 4 → ℤ) :
    {S | S ∈ g.cellSet ∧ S ⊆ g'.cell i'}.ncard = M ^ 4 := by
  let φ : (Fin 4 → Fin M) → Set InfiniteLattice.AmbientSpace :=
    fun j => g.cell fun μ => m μ + (M : ℤ) * i' μ + ((j μ : ℕ) : ℤ)
  have hφ : Function.Injective φ := by
    intro j j' heq
    have hc := cell_injective g heq
    funext μ
    have hcμ := congrFun hc μ
    exact Fin.ext (by omega)
  have himage : {S | S ∈ g.cellSet ∧ S ⊆ g'.cell i'} = φ '' univ := by
    ext S
    constructor
    · rintro ⟨⟨i, rfl⟩, hS⟩
      have hb := index_bounds_of_cell_subset hm hN hS
      refine ⟨fun μ => ⟨(i μ - m μ - (M : ℤ) * i' μ).toNat, ?_⟩, mem_univ _, ?_⟩
      · have := hb μ
        omega
      · refine congrArg g.cell (funext fun μ => ?_)
        have := hb μ
        simp only
        omega
    · rintro ⟨j, -, rfl⟩
      refine ⟨⟨_, rfl⟩, cell_subset_coarse_cell hm hN fun μ => ?_⟩
      have := (j μ).isLt
      omega
  rw [himage, ncard_image_of_injective _ hφ, ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
private theorem cellObservables_mono {S S' : Set InfiniteLattice.AmbientSpace} (hSS : S ⊆ S') :
    ReflectionGrid.cellObservables (D := D) S ⊆ ReflectionGrid.cellObservables (D := D) S' := by
  rintro F ⟨f, hf, ⟨C, hC⟩, rfl⟩
  have hlink : ∀ b : ReflectionGrid.interiorLinks (D := D) S,
      b.1 ∈ ReflectionGrid.interiorLinks (D := D) S' :=
    fun b => ⟨interior_mono hSS b.2.1, interior_mono hSS b.2.2⟩
  exact ⟨fun v => f fun b => v ⟨b.1, hlink b⟩,
    hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨C, fun v => hC _⟩, rfl⟩
private theorem reflectionGroup_le_of_coarser {g g' : ReflectionGrid D} {m : Fin 4 → ℤ} {N : ℤ}
    (hm : ∀ μ, g'.origin μ = g.origin μ + m μ * g.cellSide) (hN : g'.cellSide = N * g.cellSide) :
    g'.reflectionGroup ≤ g.reflectionGroup := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨⟨μ, n⟩, rfl⟩
  have heq : g'.reflectPerm μ n = g.reflectPerm μ (m μ + N * n) := by
    refine Equiv.ext fun y => ?_
    change g'.reflect μ n y = g.reflect μ (m μ + N * n) y
    have harg : 2 * (y μ - g'.origin μ - n * g'.cellSide) =
        2 * (y μ - g.origin μ - ((m μ + N * n : ℤ) : ℝ) * g.cellSide) := by
      rw [hm μ, hN]
      push_cast
      ring
    simp only [ReflectionGrid.reflect, harg]
  change g'.reflectPerm μ n ∈ g.reflectionGroup
  rw [heq]
  exact Subgroup.subset_closure ⟨(μ, _), rfl⟩
theorem allGridsCoarseningOnSpace_holds : AllGridsCoarseningOnSpace := by
  intro D g _ g' k₀ hcoarse hside
  choose m hm using origin_shift_of_wallSet_subset hcoarse.2
  have hL0 : 0 < D.L := by
    have hgt : (1 : ℝ) < D.L := D.one_lt_factor
    have hgt' : 1 < D.L := by exact_mod_cast hgt
    omega
  have hM : 0 < D.L ^ k₀ := pow_pos hL0 _
  have hN : g'.cellSide = (((D.L ^ k₀ : ℕ) : ℤ) : ℝ) * g.cellSide := by
    rw [hside]
    push_cast
    rfl
  have hN1 : (1 : ℤ) ≤ ((D.L ^ k₀ : ℕ) : ℤ) := by exact_mod_cast hM
  refine ⟨?_, reflectionGroup_le_of_coarser hm hN⟩
  rintro _ ⟨i', rfl⟩
  refine ⟨Subset.antisymm (fun y hy => ?_) (sUnion_subset fun S hS => hS.2), ?_, ?_⟩
  · obtain ⟨i, hyi, hi⟩ := exists_fine_cell_of_mem hm hN hN1 hy
    exact ⟨g.cell i, ⟨⟨i, rfl⟩, hi⟩, hyi⟩
  · rw [ncard_fine_cells_in_coarse_cell hM hm hN i', ← pow_mul, mul_comm k₀ 4]
  · intro S _ hS
    exact cellObservables_mono hS
end YangMills.Construction.MirrorGridsAllSides
end
