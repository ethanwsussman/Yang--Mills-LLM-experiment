import YangMills.Construction.MirrorGridsOfEverySide.IsometriesThatKeepTheFacePlanesAtEveryMirrorGridProof
import YangMills.Construction.ChessboardTori.CellsBoxesAndParitiesProof
import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGrids
import YangMills.Construction.ChessboardTori.ChessboardSeminormsOnATorus
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardBoundOnReflectionGrids
section
abbrev periodOf (D : ChessboardSetup) : ℝ := PeriodicLattice.torusSide D.L D.m
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem proj_add_translate (x : AmbientSpace) (j : Fin 4 → ℤ) :
    D.proj (x + TestFunctions.latticeTranslate (periodOf D) j) = D.proj x :=
  TestFunctions.torusProj_add_latticeTranslate _ _ _
theorem exists_translate_of_proj_eq {x y : AmbientSpace} (h : D.proj x = D.proj y) :
    ∃ j, x = y + TestFunctions.latticeTranslate (periodOf D) j :=
  TestFunctions.exists_latticeTranslate_of_torusProj_eq h
theorem proj_surjective : Function.Surjective D.proj :=
  TestFunctions.torusProj_surjective _
theorem interior_cell_eq_pi_Ioo (k : Fin 4 → ℤ) :
    interior (g.cell k) = Set.pi univ fun μ =>
      Ioo (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallPreserving.interior_cell <;> assumption
theorem mem_interior_cell_iff {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ interior (g.cell k) ↔ ∀ μ, g.origin μ + g.cellSide * k μ < x μ ∧
      x μ < g.origin μ + g.cellSide * k μ + g.cellSide := by
  rw [interior_cell_eq_pi_Ioo]
  simp only [Set.mem_pi, mem_univ, true_imp_iff, mem_Ioo]
theorem mem_cell_iff {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ g.cell k ↔ ∀ μ, g.origin μ + g.cellSide * k μ ≤ x μ ∧
      x μ ≤ g.origin μ + g.cellSide * k μ + g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.CellsBlocksAndSigns.mem_cell_iff <;> assumption
theorem closure_interior_cell_eq (k : Fin 4 → ℤ) : closure (interior (g.cell k)) = g.cell k := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallPreserving.closure_interior_cell <;> assumption
theorem index_eq_of_mem_interior {k k' : Fin 4 → ℤ} {u : AmbientSpace}
    (hu : u ∈ interior (g.cell k)) (hu' : u ∈ g.cell k') : k = k' := by
  have hs := cellSide_pos g
  rw [mem_interior_cell_iff] at hu
  rw [mem_cell_iff] at hu'
  funext μ
  obtain ⟨a1, a2⟩ := hu μ
  obtain ⟨b1, b2⟩ := hu' μ
  have h1 : (k μ : ℝ) < k' μ + 1 := by
    have : g.cellSide * (k μ : ℝ) < g.cellSide * (k' μ + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  have h2 : (k' μ : ℝ) < k μ + 1 := by
    have : g.cellSide * (k' μ : ℝ) < g.cellSide * (k μ + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  have h3 : k μ < k' μ + 1 := by exact_mod_cast h1
  have h4 : k' μ < k μ + 1 := by exact_mod_cast h2
  omega
def cellCentre (k : Fin 4 → ℤ) : AmbientSpace :=
  fun μ => g.origin μ + g.cellSide * k μ + g.cellSide / 2
theorem cellCentre_mem_interior (k : Fin 4 → ℤ) : cellCentre g k ∈ interior (g.cell k) := by
  have hs := cellSide_pos g
  rw [mem_interior_cell_iff]
  intro μ
  simp only [cellCentre]
  constructor <;> linarith
theorem interior_cell_subset (k : Fin 4 → ℤ) : interior (g.cell k) ⊆ g.cell k := interior_subset
def translateIndex (n : ℤ) (k j : Fin 4 → ℤ) : Fin 4 → ℤ := fun μ => k μ + n * j μ
variable {g} {n : ℤ}
theorem add_translate_mem_cell (hn : periodOf D = n * g.cellSide) {k : Fin 4 → ℤ}
    {x : AmbientSpace} (j : Fin 4 → ℤ) (hx : x ∈ g.cell k) :
    x + TestFunctions.latticeTranslate (periodOf D) j ∈ g.cell (translateIndex n k j) := by
  rw [mem_cell_iff] at hx ⊢
  intro μ
  obtain ⟨h1, h2⟩ := hx μ
  simp only [Pi.add_apply, TestFunctions.latticeTranslate, translateIndex, hn]
  push_cast
  constructor <;> nlinarith
theorem add_translate_mem_interior (hn : periodOf D = n * g.cellSide) {k : Fin 4 → ℤ}
    {x : AmbientSpace} (j : Fin 4 → ℤ) (hx : x ∈ interior (g.cell k)) :
    x + TestFunctions.latticeTranslate (periodOf D) j ∈
      interior (g.cell (translateIndex n k j)) := by
  rw [mem_interior_cell_iff] at hx ⊢
  intro μ
  obtain ⟨h1, h2⟩ := hx μ
  simp only [Pi.add_apply, TestFunctions.latticeTranslate, translateIndex, hn]
  push_cast
  constructor <;> nlinarith
theorem translateIndex_neg (k j : Fin 4 → ℤ) :
    translateIndex n (translateIndex n k j) (-j) = k := by
  funext μ
  simp only [translateIndex, Pi.neg_apply]
  ring
theorem proj_image_cell_translate (hn : periodOf D = n * g.cellSide) (k j : Fin 4 → ℤ) :
    D.proj '' g.cell (translateIndex n k j) = D.proj '' g.cell k := by
  have key : ∀ k j : Fin 4 → ℤ,
      D.proj '' g.cell k ⊆ D.proj '' g.cell (translateIndex n k j) := by
    rintro k j _ ⟨x, hx, rfl⟩
    exact ⟨_, add_translate_mem_cell hn j hx, proj_add_translate _ _⟩
  refine Subset.antisymm ?_ (key k j)
  have := key (translateIndex n k j) (-j)
  rwa [translateIndex_neg] at this
theorem proj_image_interior_translate (hn : periodOf D = n * g.cellSide) (k j : Fin 4 → ℤ) :
    D.proj '' interior (g.cell (translateIndex n k j)) =
      D.proj '' interior (g.cell k) := by
  have key : ∀ k j : Fin 4 → ℤ, D.proj '' interior (g.cell k) ⊆
      D.proj '' interior (g.cell (translateIndex n k j)) := by
    rintro k j _ ⟨x, hx, rfl⟩
    exact ⟨_, add_translate_mem_interior hn j hx, proj_add_translate _ _⟩
  refine Subset.antisymm ?_ (key k j)
  have := key (translateIndex n k j) (-j)
  rwa [translateIndex_neg] at this
theorem exists_translate_of_mem_image (hn : periodOf D = n * g.cellSide) {k k' : Fin 4 → ℤ}
    {u : AmbientSpace} (hu : u ∈ interior (g.cell k)) (hu' : D.proj u ∈ D.proj '' g.cell k') :
    ∃ j, k' = translateIndex n k j := by
  obtain ⟨y, hy, hyu⟩ := hu'
  obtain ⟨j, hj⟩ := exists_translate_of_proj_eq hyu
  refine ⟨j, ?_⟩
  have h1 := add_translate_mem_interior hn j hu
  rw [← hj] at h1
  exact (index_eq_of_mem_interior g h1 hy).symm
theorem exists_translate_of_image_eq (hn : periodOf D = n * g.cellSide) {k k' : Fin 4 → ℤ}
    (h : D.proj '' g.cell k = D.proj '' g.cell k') :
    ∃ j, k' = translateIndex n k j :=
  exists_translate_of_mem_image hn (cellCentre_mem_interior g k)
    (h ▸ mem_image_of_mem _ (interior_cell_subset g k (cellCentre_mem_interior g k)))
theorem torusCellInterior_proj_image (hn : periodOf D = n * g.cellSide) (k : Fin 4 → ℤ) :
    g.torusCellInterior (D.proj '' g.cell k) = D.proj '' interior (g.cell k) := by
  have hspec : g.liftCell (D.proj '' g.cell k) ∈ g.cellSet ∧
      D.proj '' g.liftCell (D.proj '' g.cell k) = D.proj '' g.cell k :=
    Classical.epsilon_spec (p := fun S : Set AmbientSpace =>
      S ∈ g.cellSet ∧ D.proj '' S = D.proj '' g.cell k) ⟨g.cell k, ⟨k, rfl⟩, rfl⟩
  obtain ⟨⟨k', hk'⟩, h2⟩ := hspec
  rw [ReflectionGrid.torusCellInterior, ← hk']
  rw [← hk'] at h2
  obtain ⟨j, rfl⟩ := exists_translate_of_image_eq hn h2.symm
  exact proj_image_interior_translate hn k j
theorem period_eq_mul_cellSide (hA : ReflectionGridArithmetic.Statement) (g : ReflectionGrid D)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    periodOf D = g.cellsPerTorusSide * g.cellSide := by
  have h := ((hA D).2.2.2 g).2 hside
  have h2 := h.1.2.1
  rw [ReflectionGrid.cellsAcross] at h2
  have hs := (cellSide_pos g).ne'
  field_simp at h2
  rw [mul_comm]
  exact h2
end
section
variable {D : ChessboardSetup} {g g' : ReflectionGrid D}
theorem wall_levels_of_coarse
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (μ : Fin 4) (k : ℤ) : ∃ k' : ℤ, g'.origin μ + k * g'.cellSide = g.origin μ + k' * g.cellSide := by
  obtain ⟨μ', k', h⟩ := hf μ k
  by_cases hμ : μ' = μ
  · subst hμ
    have hx : (fun _ => g'.origin μ' + k * g'.cellSide : AmbientSpace) ∈ g'.wall μ' k := rfl
    rw [h] at hx
    exact ⟨k', hx⟩
  · exfalso
    have hy : Function.update (fun _ => g'.origin μ + k * g'.cellSide : AmbientSpace) μ'
        (g.origin μ' + k' * g.cellSide + 1) ∈ g'.wall μ k := by
      change Function.update (fun _ => g'.origin μ + k * g'.cellSide : AmbientSpace) μ'
        (g.origin μ' + k' * g.cellSide + 1) μ = _
      rw [Function.update_of_ne (Ne.symm hμ)]
    rw [h] at hy
    have hy' : Function.update (fun _ => g'.origin μ + k * g'.cellSide : AmbientSpace) μ'
        (g.origin μ' + k' * g.cellSide + 1) μ' = g.origin μ' + k' * g.cellSide := hy
    rw [Function.update_self] at hy'
    linarith
theorem reflectPerm_mem_fine
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (μ : Fin 4) (k : ℤ) : g'.reflectPerm μ k ∈ g.reflectionGroup := by
  obtain ⟨k', h⟩ := wall_levels_of_coarse hf μ k
  have : g'.reflectPerm μ k = g.reflectPerm μ k' := by
    ext1 x
    change g'.reflect μ k x = g.reflect μ k' x
    simp only [ReflectionGrid.reflect]
    have : x μ - g'.origin μ - k * g'.cellSide = x μ - g.origin μ - k' * g.cellSide := by linarith
    rw [this]
  rw [this]
  exact Subgroup.subset_closure ⟨(μ, k'), rfl⟩
theorem reflectionGroup_le
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k') :
    g'.reflectionGroup ≤ g.reflectionGroup := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨⟨μ, k⟩, rfl⟩
  exact reflectPerm_mem_fine hf μ k
theorem inducedTorusMaps_subset
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k') :
    g'.inducedTorusMaps ⊆ g.inducedTorusMaps := by
  rintro r' ⟨r, hr, h⟩
  exact ⟨r, reflectionGroup_le hf hr, h⟩
theorem walls_subset
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k') :
    g'.walls ⊆ g.walls := by
  intro x hx
  simp only [ReflectionGrid.walls, mem_iUnion] at hx ⊢
  obtain ⟨μ, k, hx⟩ := hx
  obtain ⟨μ', k', h⟩ := hf μ k
  exact ⟨μ', k', h ▸ hx⟩
theorem interior_cell_disjoint_walls (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    Disjoint (interior (g.cell k)) g.walls := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallPreserving.disjoint_interior_cell_walls <;> assumption
theorem isClosed_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) : IsClosed (g.cell k) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallPreserving.isClosed_cell <;> assumption
theorem convex_interior_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    Convex ℝ (interior (g.cell k)) := by
  rw [interior_cell_eq_pi_Ioo]
  exact convex_pi fun _ _ => convex_Ioo _ _
theorem exists_coarse_cell_containing
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) (k : Fin 4 → ℤ) :
    ∃ K, interior (g.cell k) ⊆ interior (g'.cell K) ∧ g.cell k ⊆ g'.cell K := by
  have hd : Disjoint (interior (g.cell k)) g'.walls :=
    (interior_cell_disjoint_walls g k).mono_right (walls_subset hf)
  obtain ⟨S, ⟨K, rfl⟩, hS⟩ := hE.2.2.2 _ (convex_interior_cell g k) hd
  refine ⟨K, hS, ?_⟩
  rw [← closure_interior_cell_eq g k]
  exact closure_minimal (hS.trans interior_subset) (isClosed_cell g' K)
variable {n' : ℤ}
theorem coarse_image_eq_of_subset (hn' : periodOf D = n' * g'.cellSide) {k K K₂ : Fin 4 → ℤ}
    (hK : interior (g.cell k) ⊆ interior (g'.cell K))
    (h : D.proj '' g.cell k ⊆ D.proj '' g'.cell K₂) :
    D.proj '' g'.cell K₂ = D.proj '' g'.cell K := by
  obtain ⟨j, rfl⟩ := exists_translate_of_mem_image hn' (hK (cellCentre_mem_interior g k))
    (h (mem_image_of_mem _ (interior_cell_subset g k (cellCentre_mem_interior g k))))
  exact proj_image_cell_translate hn' K j
theorem torusCellInterior_subset {n : ℤ} (hn : periodOf D = n * g.cellSide)
    (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) {C Q : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hQ : Q ∈ g'.torusCellSet) (hCQ : C ⊆ Q) :
    g.torusCellInterior C ⊆ g'.torusCellInterior Q := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hC
  obtain ⟨_, ⟨K₂, rfl⟩, rfl⟩ := hQ
  obtain ⟨K, hK, -⟩ := exists_coarse_cell_containing (g := g) hf hE k
  have h := coarse_image_eq_of_subset hn' hK hCQ
  change g.torusCellInterior (D.proj '' g.cell k) ⊆ g'.torusCellInterior (D.proj '' g'.cell K₂)
  rw [h, torusCellInterior_proj_image hn, torusCellInterior_proj_image hn']
  exact image_mono hK
theorem torusCellLinks_subset {n : ℤ} (hn : periodOf D = n * g.cellSide)
    (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) {C Q : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hQ : Q ∈ g'.torusCellSet) (hCQ : C ⊆ Q) : g.torusCellLinks C ⊆ g'.torusCellLinks Q :=
  fun _ hb => ⟨torusCellInterior_subset hn hn' hf hE hC hQ hCQ hb.1,
    torusCellInterior_subset hn hn' hf hE hC hQ hCQ hb.2⟩
theorem prod_mem_torusCellObservables {n : ℤ} (hn : periodOf D = n * g.cellSide)
    (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) {Q : Set D.Torus} (hQ : Q ∈ g'.torusCellSet)
    [Finite (g.torusCellsWithin Q)]
    (F : g.torusCellsWithin Q → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (hF : ∀ C, F C ∈ g.torusCellObservables C.1) :
    (fun U => ∏ᶠ C, F C U) ∈ g'.torusCellObservables Q := by
  classical
  have := Fintype.ofFinite (g.torusCellsWithin Q)
  choose f hm hb hrep using hF
  choose c hc using hb
  have inc : ∀ C : g.torusCellsWithin Q, g.torusCellLinks C.1 ⊆ g'.torusCellLinks Q :=
    fun C => torusCellLinks_subset hn hn' hf hE C.2.1 hQ C.2.2
  refine ⟨fun w => ∏ C, f C fun b => w ⟨b.1, inc C b.2⟩, ?_, ⟨∏ C, |c C|, fun u => ?_⟩, fun U => ?_⟩
  · refine Finset.measurable_prod _ fun C _ => (hm C).comp ?_
    exact measurable_pi_lambda _ fun b => measurable_pi_apply _
  · rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun C _ => (hc C _).trans (le_abs_self _)
  · beta_reduce
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun C _ => hrep C U
end
section
variable {D : ChessboardSetup} {g g' : ReflectionGrid D} {n n' : ℤ}
theorem bijective_of_mem_inducedTorusMaps (hG : g.TorusGroupQuotient) {r' : D.Torus → D.Torus}
    (h : r' ∈ g.inducedTorusMaps) : Function.Bijective r' := by
  obtain ⟨⟨φ, -, -, hrange⟩, -⟩ := hG
  rw [← hrange] at h
  obtain ⟨e, -, rfl⟩ := h
  exact e.bijective
theorem exists_coarse_torusCell
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    ∃ Q ∈ g'.torusCellSet, C ⊆ Q := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hC
  obtain ⟨K, -, h⟩ := exists_coarse_cell_containing (g := g) hf hE k
  exact ⟨_, ⟨_, ⟨K, rfl⟩, rfl⟩, image_mono h⟩
theorem coarse_torusCell_unique (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) {C Q₁ Q₂ : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hQ₁ : Q₁ ∈ g'.torusCellSet) (hQ₂ : Q₂ ∈ g'.torusCellSet) (h₁ : C ⊆ Q₁) (h₂ : C ⊆ Q₂) :
    Q₁ = Q₂ := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hC
  obtain ⟨_, ⟨K₁, rfl⟩, rfl⟩ := hQ₁
  obtain ⟨_, ⟨K₂, rfl⟩, rfl⟩ := hQ₂
  obtain ⟨K, hK, -⟩ := exists_coarse_cell_containing (g := g) hf hE k
  exact (coarse_image_eq_of_subset hn' hK h₁).trans (coarse_image_eq_of_subset hn' hK h₂).symm
theorem image_mem_torusCellSet
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hG : g.TorusGroupQuotient) {Q : Set D.Torus}
    (p : g'.inducedTorusMaps × g.torusCellsWithin Q) :
    p.1.1 '' p.2.1 ∈ g.torusCellSet :=
  hG.2.2.2.2.2.1 p.1.1 (inducedTorusMaps_subset hf p.1.2) _ p.2.2.1
theorem cellPairing_bijective (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) (hG : g.TorusGroupQuotient) (hG' : g'.TorusGroupQuotient)
    (hCo : g.ReflectionGroupCoordForm) {Q : Set D.Torus} (hQ : Q ∈ g'.torusCellSet) :
    Function.Bijective (fun p : g'.inducedTorusMaps × g.torusCellsWithin Q =>
      (⟨p.1.1 '' p.2.1, image_mem_torusCellSet hf hG p⟩ : g.torusCellSet)) := by
  obtain ⟨-, -, -, -, -, c6', c7', -⟩ := hG'
  constructor
  · rintro ⟨a₁, C₁⟩ ⟨a₂, C₂⟩ h
    have h' : a₁.1 '' C₁.1 = a₂.1 '' C₂.1 := congrArg Subtype.val h
    have hq₁ : a₁.1 '' Q ∈ g'.torusCellSet := c6' a₁.1 a₁.2 Q hQ
    have hq₂ : a₂.1 '' Q ∈ g'.torusCellSet := c6' a₂.1 a₂.2 Q hQ
    have heq : a₁.1 '' Q = a₂.1 '' Q :=
      coarse_torusCell_unique hn' hf hE (image_mem_torusCellSet hf hG (a₁, C₁)) hq₁ hq₂
        (image_mono C₁.2.2) (h' ▸ image_mono C₂.2.2)
    have ha : a₁.1 = a₂.1 := (c7' Q hQ _ hq₁).unique ⟨a₁.2, rfl⟩ ⟨a₂.2, heq.symm⟩
    have ha' : a₁ = a₂ := Subtype.ext ha
    subst ha'
    have hc : C₁.1 = C₂.1 :=
      (bijective_of_mem_inducedTorusMaps hG (inducedTorusMaps_subset hf a₁.2)).injective.image_injective h'
    exact Prod.ext rfl (Subtype.ext hc)
  · rintro ⟨X, hX⟩
    obtain ⟨Q₁, hQ₁, hXQ⟩ := exists_coarse_torusCell (g := g) hf hE hX
    obtain ⟨a, ⟨ha, haQ⟩, -⟩ := c7' Q hQ Q₁ hQ₁
    have ha0 := ha
    obtain ⟨b, hb, hab⟩ := ha
    obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hX
    have hbi : (b⁻¹ : Equiv.Perm AmbientSpace) ∈ g.reflectionGroup :=
      reflectionGroup_le hf (inv_mem hb)
    have hS : (b⁻¹ : Equiv.Perm AmbientSpace) '' g.cell k ∈ g.cellSet :=
      hCo.2.2.2.2.2.1 _ hbi _ ⟨k, rfl⟩
    have hC : D.proj '' ((b⁻¹ : Equiv.Perm AmbientSpace) '' g.cell k) ∈ g.torusCellSet :=
      ⟨_, hS, rfl⟩
    have haC : a '' (D.proj '' ((b⁻¹ : Equiv.Perm AmbientSpace) '' g.cell k)) =
        D.proj '' g.cell k := by
      rw [← image_comp, ← hab, image_comp, ← image_comp (⇑b)]
      congr 1
      convert image_id _
      ext1 x
      simp
    have hCQ : D.proj '' ((b⁻¹ : Equiv.Perm AmbientSpace) '' g.cell k) ⊆ Q := by
      have hinj := (bijective_of_mem_inducedTorusMaps hG (inducedTorusMaps_subset hf ha0)).injective
      rw [← image_subset_image_iff hinj, haC, haQ]
      exact hXQ
    exact ⟨(⟨a, ha0⟩, ⟨_, hC, hCQ⟩), Subtype.ext haC⟩
theorem inducingElement_spec {g : ReflectionGrid D} {a : D.Torus → D.Torus}
    (ha : a ∈ g.inducedTorusMaps) :
    D.proj ∘ (g.inducingElement a).1 = a ∘ D.proj := by
  obtain ⟨r, hr, h⟩ := ha
  exact Classical.epsilon_spec
    (p := fun r : g.reflectionGroup => D.proj ∘ r.1 = a ∘ D.proj) ⟨⟨r, hr⟩, h⟩
theorem torusSign_eq_fine
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hG : g.TorusGroupQuotient) {a : D.Torus → D.Torus} (ha : a ∈ g'.inducedTorusMaps) :
    g'.torusSign a = g.torusSign a :=
  hG.2.2.2.1 _ (reflectionGroup_le hf (g'.inducingElement a).2) _ (g.inducingElement a).2 a
    (inducingElement_spec ha) (inducingElement_spec (inducedTorusMaps_subset hf ha))
theorem torusCarrier_image (hG : g.TorusGroupQuotient) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps) :
    g.torusCarrier C (a '' C) = a := by
  obtain ⟨-, -, -, -, -, c6, c7, -⟩ := hG
  have hex := c7 C hC _ (c6 a ha C hC)
  refine hex.unique ?_ ⟨ha, rfl⟩
  exact Classical.epsilon_spec (p := fun r' : D.Torus → D.Torus =>
    r' ∈ g.inducedTorusMaps ∧ r' '' C = a '' C) ⟨a, ha, rfl⟩
theorem torusTransportTo_image (hG : g.TorusGroupQuotient) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransportTo C (a '' C) F = g.torusTransport a F := by
  rw [ReflectionGrid.torusTransportTo, torusCarrier_image hG hC ha]
theorem signedConj_finprod {ι : Type*} [Finite ι] (σ : ℤˣ) (f : ι → ℂ) :
    Conventions.signedConj σ (∏ᶠ i, f i) = ∏ᶠ i, Conventions.signedConj σ (f i) := by
  classical
  have := Fintype.ofFinite ι
  simp only [finprod_eq_prod_of_fintype, Conventions.signedConj]
  by_cases h : σ = 1
  · simp [h]
  · simp [h, map_prod]
theorem finprod_equiv_prod {M α β γ : Type*} [CommMonoid M] [Finite α] [Finite β]
    (E : α × β ≃ γ) (h : γ → M) : ∏ᶠ x, h x = ∏ᶠ a, ∏ᶠ b, h (E (a, b)) := by
  rw [← finprod_comp_equiv E, finprod_curry _ (toFinite _)]
theorem cellsAcross_pos (g : ReflectionGrid D) : 0 < g.cellsAcross := by
  have hL := D.one_lt_factor
  exact div_pos (by rw [PeriodicLattice.torusSide]; positivity) (cellSide_pos g)
theorem card_inducedTorusMaps_ne_zero (hG : g.TorusGroupQuotient) :
    Nat.card g.inducedTorusMaps ≠ 0 := by
  intro h
  have h2 := hG.2.1
  rw [h] at h2
  have := cellsAcross_pos g
  simp only [Nat.cast_zero] at h2
  exact absurd h2.symm (by positivity)
theorem finite_inducedTorusMaps (hG : g.TorusGroupQuotient) : Finite g.inducedTorusMaps :=
  Nat.finite_of_card_ne_zero (card_inducedTorusMaps_ne_zero hG)
theorem finite_torusCellSet (hG : g.TorusGroupQuotient) : Finite g.torusCellSet := by
  refine Nat.finite_of_card_ne_zero fun h => ?_
  have h2 := hG.2.2.2.2.2.2.2
  rw [h] at h2
  have := cellsAcross_pos g
  simp only [Nat.cast_zero] at h2
  exact absurd h2.symm (by positivity)
theorem torusChessboardNorm_nonneg (g : ReflectionGrid D)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    0 ≤ g.torusChessboardNorm F :=
  Real.rpow_nonneg (norm_nonneg _) _
theorem coarse_bound (hn' : periodOf D = n' * g'.cellSide)
    (hf : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k')
    (hE : g'.DistToWalls) (hG : g.TorusGroupQuotient) (hG' : g'.TorusGroupQuotient)
    (hCo : g.ReflectionGroupCoordForm)
    (hBound : ∀ F : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
      (∀ C ∈ g.torusCellSet, F C ∈ g.torusCellObservables C) →
        ‖D.periodicExpectation fun U => ∏ᶠ C ∈ g.torusCellSet, F C U‖ ≤
          ∏ᶠ C ∈ g.torusCellSet, g.torusChessboardNorm (F C))
    (hCopy : ∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C, ∀ C' ∈ g.torusCellSet,
      g.torusChessboardNorm (g.torusTransportTo C C' F) = g.torusChessboardNorm F)
    (hMem : ∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C, ∀ a ∈ g.inducedTorusMaps,
      g.torusTransportTo C (a '' C) F ∈ g.torusCellObservables (a '' C))
    {Q : Set D.Torus} (hQ : Q ∈ g'.torusCellSet) [Finite (g.torusCellsWithin Q)]
    (F : g.torusCellsWithin Q → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (hF : ∀ C, F C ∈ g.torusCellObservables C.1) :
    g'.torusChessboardNorm (fun U => ∏ᶠ C, F C U) ≤ ∏ᶠ C, g.torusChessboardNorm (F C) := by
  classical
  have fG' := finite_inducedTorusMaps hG'
  let E := Equiv.ofBijective _ (cellPairing_bijective hn' hf hE hG hG' hCo hQ)
  let Φ : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun X =>
    if hX : X ∈ g.torusCellSet then g.torusTransport (E.symm ⟨X, hX⟩).1.1 (F (E.symm ⟨X, hX⟩).2)
    else fun _ => 0
  have hΦ : ∀ p, Φ (E p).1 = g.torusTransport p.1.1 (F p.2) := by
    intro p
    simp only [Φ, dif_pos (E p).2, Subtype.coe_eta, E.symm_apply_apply]
  have hImg : ∀ p, (E p).1 = p.1.1 '' p.2.1 := fun _ => rfl
  have hMemΦ : ∀ X ∈ g.torusCellSet, Φ X ∈ g.torusCellObservables X := by
    intro X hX
    obtain ⟨p, hp⟩ := E.surjective ⟨X, hX⟩
    have hX' : X = (E p).1 := (congrArg Subtype.val hp).symm
    subst hX'
    have ha := inducedTorusMaps_subset hf p.1.2
    rw [hΦ, hImg, ← torusTransportTo_image hG p.2.2.1 ha]
    exact hMem _ p.2.2.1 _ (hF p.2) _ ha
  have hPairs : ∀ {M : Type} [CommMonoid M] (h : Set D.Torus → M),
      ∏ᶠ X ∈ g.torusCellSet, h X =
        ∏ᶠ a : g'.inducedTorusMaps, ∏ᶠ c : g.torusCellsWithin Q, h (E (a, c)).1 := by
    intro M _ h
    rw [← finprod_set_coe_eq_finprod_mem]
    exact finprod_equiv_prod E fun x => h x.1
  have hArr : g'.torusProduct (fun U => ∏ᶠ C, F C U) =
      fun U => ∏ᶠ X ∈ g.torusCellSet, Φ X U := by
    funext U
    rw [hPairs (fun X => Φ X U), ReflectionGrid.torusProduct, ← finprod_set_coe_eq_finprod_mem]
    refine finprod_congr fun a => ?_
    simp only [hΦ]
    change Conventions.signedConj (g'.torusSign a.1) (∏ᶠ c, F c _) = _
    rw [signedConj_finprod, torusSign_eq_fine hf hG a.2]
    rfl
  have hVal : ∏ᶠ X ∈ g.torusCellSet, g.torusChessboardNorm (Φ X) =
      (∏ᶠ C, g.torusChessboardNorm (F C)) ^ Nat.card g'.inducedTorusMaps := by
    rw [hPairs (fun X => g.torusChessboardNorm (Φ X))]
    have h1 : ∀ (a : g'.inducedTorusMaps) (c : g.torusCellsWithin Q),
        g.torusChessboardNorm (Φ (E (a, c)).1) = g.torusChessboardNorm (F c) := by
      intro a c
      have ha := inducedTorusMaps_subset hf a.2
      rw [hΦ]
      change g.torusChessboardNorm (g.torusTransport a.1 (F c)) = _
      rw [← torusTransportTo_image hG c.2.1 ha]
      exact hCopy _ c.2.1 _ (hF c) _ (hG.2.2.2.2.2.1 _ ha _ c.2.1)
    simp only [h1]
    have := Fintype.ofFinite g'.inducedTorusMaps
    rw [finprod_eq_prod_of_fintype, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hB := hBound Φ hMemΦ
  rw [hVal, ← hArr] at hB
  have hV : 0 ≤ ∏ᶠ C, g.torusChessboardNorm (F C) :=
    finprod_induction (p := fun x : ℝ => 0 ≤ x) zero_le_one (fun _ _ => mul_nonneg)
      fun _ => torusChessboardNorm_nonneg g _
  have hN : Nat.card g'.inducedTorusMaps ≠ 0 := card_inducedTorusMaps_ne_zero hG'
  rw [ReflectionGrid.torusChessboardNorm, ← hG'.2.1, one_div]
  calc _ ≤ ((∏ᶠ C, g.torusChessboardNorm (F C)) ^ Nat.card g'.inducedTorusMaps) ^
        ((Nat.card g'.inducedTorusMaps : ℝ)⁻¹) :=
        Real.rpow_le_rpow (norm_nonneg _) hB (by positivity)
    _ = _ := Real.pow_rpow_inv_natCast hV hN
end
section
variable {D : ChessboardSetup} {g : ReflectionGrid D} {n : ℤ}
theorem intUnit_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
def IsSignedPermShift (g : ReflectionGrid D) (ρ : AmbientSpace → AmbientSpace)
    (p : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ) (t : Fin 4 → ℤ) : Prop :=
  ∀ x ν, ρ x ν = g.origin ν + ((e ν : ℤ) : ℝ) * (x (p ν) - g.origin (p ν)) + t ν * g.cellSide
theorem exists_signedPerm_form (ρ : D.LatticeSym) :
    ∃ (p : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ) (v : AmbientSpace),
      ∀ x ν, ρ.toFun x ν = ((e ν : ℤ) : ℝ) * x (p ν) + v ν := by
  obtain ⟨w, hw, v, hf⟩ := ρ.toFun_mem_latticeMotions D.mesh_pos.ne'
  obtain ⟨p, e, he⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  refine ⟨p, e, v.1, fun x ν => ?_⟩
  rw [hf]
  simp [InfiniteLattice.latticeMotion, he]
theorem isSignedPermShift_of_preserves (hn : periodOf D = n * g.cellSide)
    {r : D.Torus → D.Torus} (hr : g.PreservesLatticeAndWalls r) (ρ : D.LatticeSym)
    (hρ : D.proj ∘ ρ.toFun = r ∘ D.proj) :
    ∃ p e t, IsSignedPermShift g ρ.toFun p e t := by
  obtain ⟨p, e, v, hc⟩ := exists_signedPerm_form ρ
  have hs := cellSide_pos g
  have key : ∀ ν, ∃ t : ℤ, ((e ν : ℤ) : ℝ) * g.origin (p ν) + v ν =
      g.origin ν + t * g.cellSide := by
    intro ν
    have hmem : (fun P : Set D.Torus => r '' P) (g.torusWall (p ν) 0) ∈ g.torusWallFamily := by
      rw [← hr.2.2]
      exact ⟨_, ⟨(p ν, 0), rfl⟩, rfl⟩
    obtain ⟨⟨μ', k'⟩, hk⟩ := hmem
    have hk' : g.torusWall μ' k' = r '' g.torusWall (p ν) 0 := hk
    have hA : ∀ x : AmbientSpace, x (p ν) = g.origin (p ν) →
        ∃ κ : ℤ, ρ.toFun x μ' = g.origin μ' + κ * g.cellSide := by
      intro x hx
      have h1 : r (D.proj x) ∈ g.torusWall μ' k' := by
        rw [hk']
        refine ⟨_, ⟨x, ?_, rfl⟩, rfl⟩
        change x (p ν) = g.origin (p ν) + ((0 : ℤ) : ℝ) * g.cellSide
        simp [hx]
      obtain ⟨y, hy, hyx⟩ := h1
      have hy' : y μ' = g.origin μ' + k' * g.cellSide := hy
      have h2 : D.proj y = D.proj (ρ.toFun x) := hyx.trans (congrFun hρ x).symm
      obtain ⟨j, hj⟩ := exists_translate_of_proj_eq h2
      have h3 := congrFun hj μ'
      simp only [Pi.add_apply, TestFunctions.latticeTranslate, hn] at h3
      refine ⟨k' - n * j μ', ?_⟩
      push_cast
      linear_combination hy' - h3
    have hB : μ' = ν := by
      by_contra hne
      have hp : p μ' ≠ p ν := fun h => hne (p.injective h)
      obtain ⟨κ, hκ⟩ := hA (Function.update (fun _ => g.origin (p ν) : AmbientSpace) (p μ')
        (((e μ' : ℤ) : ℝ) * (g.origin μ' + g.cellSide / 2 - v μ')))
        (by rw [Function.update_of_ne hp.symm])
      rw [hc, Function.update_self, ← mul_assoc, intUnit_mul_self] at hκ
      have h4 : (2 * κ : ℝ) = 1 := by
        have : g.cellSide * (2 * κ : ℝ) = g.cellSide * 1 := by linarith
        exact mul_left_cancel₀ hs.ne' this
      have h5 : 2 * κ = 1 := by exact_mod_cast h4
      omega
    subst hB
    obtain ⟨κ, hκ⟩ := hA (fun _ => g.origin (p μ')) rfl
    rw [hc] at hκ
    exact ⟨κ, hκ⟩
  choose t ht using key
  refine ⟨p, e, t, fun x ν => ?_⟩
  rw [hc]
  linear_combination ht ν
def cellImageIndex (p : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ) (t k : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun ν => t ν + if e ν = 1 then k (p ν) else -k (p ν) - 1
variable {ρ : AmbientSpace → AmbientSpace} {p : Equiv.Perm (Fin 4)} {e : Fin 4 → ℤˣ}
  {t : Fin 4 → ℤ}
theorem mem_cell_image_iff (hc : IsSignedPermShift g ρ p e t) (k : Fin 4 → ℤ) (x : AmbientSpace) :
    ρ x ∈ g.cell (cellImageIndex p e t k) ↔ x ∈ g.cell k := by
  have coord : ∀ ν, (g.origin ν + g.cellSide * cellImageIndex p e t k ν ≤ ρ x ν ∧
      ρ x ν ≤ g.origin ν + g.cellSide * cellImageIndex p e t k ν + g.cellSide) ↔
      (g.origin (p ν) + g.cellSide * k (p ν) ≤ x (p ν) ∧
        x (p ν) ≤ g.origin (p ν) + g.cellSide * k (p ν) + g.cellSide) := by
    intro ν
    rw [hc x ν]
    simp only [cellImageIndex]
    rcases Int.units_eq_one_or (e ν) with h | h
    · simp only [h, if_true, Units.val_one, Int.cast_one, Int.cast_add]
      constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
    · simp only [h, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        Int.cast_add]
      have : (-1 : ℤˣ) ≠ 1 := by decide
      simp only [if_neg this, Int.cast_sub, Int.cast_neg, Int.cast_one]
      constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  rw [mem_cell_iff, mem_cell_iff]
  exact ⟨fun h μ => by simpa using (coord (p.symm μ)).1 (h _), fun h ν => (coord ν).2 (h _)⟩
theorem mem_interior_image_iff (hc : IsSignedPermShift g ρ p e t) (k : Fin 4 → ℤ)
    (x : AmbientSpace) :
    ρ x ∈ interior (g.cell (cellImageIndex p e t k)) ↔ x ∈ interior (g.cell k) := by
  have coord : ∀ ν, (g.origin ν + g.cellSide * cellImageIndex p e t k ν < ρ x ν ∧
      ρ x ν < g.origin ν + g.cellSide * cellImageIndex p e t k ν + g.cellSide) ↔
      (g.origin (p ν) + g.cellSide * k (p ν) < x (p ν) ∧
        x (p ν) < g.origin (p ν) + g.cellSide * k (p ν) + g.cellSide) := by
    intro ν
    rw [hc x ν]
    simp only [cellImageIndex]
    rcases Int.units_eq_one_or (e ν) with h | h
    · simp only [h, if_true, Units.val_one, Int.cast_one, Int.cast_add]
      constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
    · simp only [h, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        Int.cast_add]
      have : (-1 : ℤˣ) ≠ 1 := by decide
      simp only [if_neg this, Int.cast_sub, Int.cast_neg, Int.cast_one]
      constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  rw [mem_interior_cell_iff, mem_interior_cell_iff]
  exact ⟨fun h μ => by simpa using (coord (p.symm μ)).1 (h _), fun h ν => (coord ν).2 (h _)⟩
theorem image_eq_of_forall_mem_iff (hs : Function.Surjective ρ) {A B : Set AmbientSpace}
    (h : ∀ x, ρ x ∈ B ↔ x ∈ A) : ρ '' A = B := by
  ext y
  obtain ⟨x, rfl⟩ := hs y
  constructor
  · rintro ⟨x', hx', hxx⟩
    rw [← hxx]
    exact (h x').2 hx'
  · intro hy
    exact ⟨x, (h x).1 hy, rfl⟩
variable {a h : AmbientSpace → AmbientSpace}
theorem coordShift_forward (hc : IsSignedPermShift g ρ p e t) (hs : Function.Surjective ρ)
    (hh : ∀ x, h (ρ x) = ρ (a x)) {ν : Fin 4} {τ : ℤ}
    (ha : g.ActsOnCoord a (p ν) (g.coordShift τ)) :
    g.ActsOnCoord h ν (g.coordShift ((e ν : ℤ) * τ)) := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have h1 := ha x
  simp only [ReflectionGrid.coordShift] at h1 ⊢
  rw [hh x, hc (a x) ν, hc x ν]
  push_cast
  linear_combination ((e ν : ℤ) : ℝ) * h1
theorem coordReflect_forward (hc : IsSignedPermShift g ρ p e t) (hs : Function.Surjective ρ)
    (hh : ∀ x, h (ρ x) = ρ (a x)) {ν : Fin 4} {k : ℤ}
    (ha : g.ActsOnCoord a (p ν) (g.coordReflect k)) :
    g.ActsOnCoord h ν (g.coordReflect ((e ν : ℤ) * k + t ν)) := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have h1 := ha x
  simp only [ReflectionGrid.coordReflect] at h1 ⊢
  rw [hh x, hc (a x) ν, hc x ν]
  push_cast
  linear_combination ((e ν : ℤ) : ℝ) * h1
theorem coordShift_backward (hc : IsSignedPermShift g ρ p e t)
    (hh : ∀ x, h (ρ x) = ρ (a x)) {ν : Fin 4} {τ : ℤ}
    (ha : g.ActsOnCoord h ν (g.coordShift τ)) :
    g.ActsOnCoord a (p ν) (g.coordShift ((e ν : ℤ) * τ)) := by
  intro x
  have h1 := ha (ρ x)
  simp only [ReflectionGrid.coordShift] at h1 ⊢
  rw [hh x, hc (a x) ν, hc x ν] at h1
  have hu := intUnit_mul_self (e ν)
  push_cast
  linear_combination ((e ν : ℤ) : ℝ) * h1 -
    (a x (p ν) - g.origin (p ν) - (x (p ν) - g.origin (p ν))) * hu
theorem coordReflect_backward (hc : IsSignedPermShift g ρ p e t)
    (hh : ∀ x, h (ρ x) = ρ (a x)) {ν : Fin 4} {k : ℤ}
    (ha : g.ActsOnCoord h ν (g.coordReflect k)) :
    g.ActsOnCoord a (p ν) (g.coordReflect ((e ν : ℤ) * (k - t ν))) := by
  intro x
  have h1 := ha (ρ x)
  simp only [ReflectionGrid.coordReflect] at h1 ⊢
  rw [hh x, hc (a x) ν, hc x ν] at h1
  have hu := intUnit_mul_self (e ν)
  push_cast
  linear_combination ((e ν : ℤ) : ℝ) * h1 -
    (a x (p ν) - g.origin (p ν) + (x (p ν) - g.origin (p ν))) * hu
theorem isProductOfCoordMaps_forward (hc : IsSignedPermShift g ρ p e t)
    (hs : Function.Surjective ρ) (hh : ∀ x, h (ρ x) = ρ (a x))
    (ha : g.IsProductOfCoordMaps a) : g.IsProductOfCoordMaps h := by
  intro ν
  rcases ha (p ν) with ⟨τ, h1⟩ | ⟨k, h1⟩
  · exact Or.inl ⟨_, coordShift_forward hc hs hh h1⟩
  · exact Or.inr ⟨_, coordReflect_forward hc hs hh h1⟩
theorem isProductOfCoordMaps_backward (hc : IsSignedPermShift g ρ p e t)
    (hh : ∀ x, h (ρ x) = ρ (a x)) (ha : g.IsProductOfCoordMaps h) :
    g.IsProductOfCoordMaps a := by
  intro μ
  have hμ : μ = p (p.symm μ) := by simp
  rw [hμ]
  rcases ha (p.symm μ) with ⟨τ, h1⟩ | ⟨k, h1⟩
  · exact Or.inl ⟨_, coordShift_backward hc hh h1⟩
  · exact Or.inr ⟨_, coordReflect_backward hc hh h1⟩
theorem reflectsCoord_iff (hc : IsSignedPermShift g ρ p e t) (hs : Function.Surjective ρ)
    (hh : ∀ x, h (ρ x) = ρ (a x)) (ν : Fin 4) :
    g.ReflectsCoord a (p ν) ↔ g.ReflectsCoord h ν :=
  ⟨fun ⟨_, h1⟩ => ⟨_, coordReflect_forward hc hs hh h1⟩,
    fun ⟨_, h1⟩ => ⟨_, coordReflect_backward hc hh h1⟩⟩
theorem numReflectedCoords_eq (hc : IsSignedPermShift g ρ p e t) (hs : Function.Surjective ρ)
    (hh : ∀ x, h (ρ x) = ρ (a x)) : g.numReflectedCoords a = g.numReflectedCoords h := by
  classical
  simp only [ReflectionGrid.numReflectedCoords]
  refine Finset.card_equiv p.symm fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := reflectsCoord_iff hc hs hh (p.symm i)
  simpa using this
end
section
variable {D : ChessboardSetup} {g : ReflectionGrid D} {n : ℤ}
def HasLinkImages (D : ChessboardSetup) (r : D.Torus → D.Torus) : Prop :=
  ∀ b : D.PeriodicLink, ∃ b' : D.PeriodicLink,
    (b'.source : D.Torus) = r b.source ∧ (b'.target : D.Torus) = r b.target
theorem hasLinkImages_of {r : D.Torus → D.Torus} (hb : Function.Bijective r)
    (hi : D.IsTorusDistPreserving r)
    (ho : r '' (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
      PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ)) : HasLinkImages D r := by
  let D₂ : SourcesAndGluing.GluingSetup := ⟨D.toStandingParameters, D.β, D.beta_pos, 0⟩
  let R : SourcesAndGluing.GluingSetup.TorusLatticeIsometry D₂ := ⟨r, ⟨hb, hi⟩, ho⟩
  exact fun b => ⟨R.linkMap b, rfl, rfl⟩
theorem imageLink_spec {r : D.Torus → D.Torus} (h : HasLinkImages D r) (b : D.PeriodicLink) :
    ((D.imageLink r b).source : D.Torus) = r b.source ∧
      ((D.imageLink r b).target : D.Torus) = r b.target :=
  Classical.epsilon_spec (h b)
theorem link_eq_of_ends {b b' : D.PeriodicLink} (ht : (b.source : D.Torus) = b'.source)
    (hh : (b.target : D.Torus) = b'.target) : b = b' :=
  PeriodicLattice.Bond.ext (Subtype.ext ht) (Subtype.ext hh)
theorem pullbackField_comm {A B C E : D.Torus → D.Torus} (hA : HasLinkImages D A)
    (hB : HasLinkImages D B) (hC : HasLinkImages D C) (hE : HasLinkImages D E)
    (h : ∀ u, A (B u) = C (E u)) (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    D.pullbackField B (D.pullbackField A U) = D.pullbackField E (D.pullbackField C U) := by
  funext b
  change U (D.imageLink A (D.imageLink B b)) =
    U (D.imageLink C (D.imageLink E b))
  congr 1
  refine link_eq_of_ends ?_ ?_
  · rw [(imageLink_spec hA _).1, (imageLink_spec hC _).1, (imageLink_spec hB _).1,
      (imageLink_spec hE _).1, h]
  · rw [(imageLink_spec hA _).2, (imageLink_spec hC _).2, (imageLink_spec hB _).2,
      (imageLink_spec hE _).2, h]
theorem pullbackField_mem_compact {r : D.Torus → D.Torus} (h : HasLinkImages D r)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :
    D.pullbackField r U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (D.imageLink r b.opposite) = (U (D.imageLink r b))⁻¹
  have h1 : D.imageLink r b.opposite = (D.imageLink r b).opposite :=
    link_eq_of_ends ((imageLink_spec h _).1.trans (imageLink_spec h b).2.symm)
      ((imageLink_spec h _).2.trans (imageLink_spec h b).1.symm)
  rw [h1]
  exact hU.2 _ (mem_univ _)
theorem bondPreimage_symm_eq {σ : D.Torus ≃ D.Torus} (h : HasLinkImages D σ)
    (b : D.PeriodicLink) :
    PeriodicLattice.bondPreimage σ.symm b = D.imageLink σ b := by
  have hex : ∃ b' : D.PeriodicLink, (b'.source : D.Torus) = σ.symm.symm b.source ∧
      (b'.target : D.Torus) = σ.symm.symm b.target := h b
  rw [PeriodicLattice.bondPreimage, dif_pos hex]
  exact link_eq_of_ends (hex.choose_spec.1.trans (imageLink_spec h b).1.symm)
    (hex.choose_spec.2.trans (imageLink_spec h b).2.symm)
theorem pullbackObservable_eq_transport {σ : D.Torus ≃ D.Torus} (h : HasLinkImages D σ)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    D.pullbackObservable σ F = PeriodicLattice.transportObservable σ F := by
  funext U
  change F (D.pullbackField σ U) = F (PeriodicLattice.transportGaugeField σ.symm U)
  congr 1
  funext b
  change U (D.imageLink σ b) = U (PeriodicLattice.bondPreimage σ.symm b)
  rw [bondPreimage_symm_eq h]
def conjBy (σ : D.Torus ≃ D.Torus) (b : D.Torus → D.Torus) : D.Torus → D.Torus :=
  fun u => σ (b (σ.symm u))
def conjByInv (σ : D.Torus ≃ D.Torus) (c : D.Torus → D.Torus) : D.Torus → D.Torus :=
  fun u => σ.symm (c (σ u))
variable {E : AmbientSpace ≃ AmbientSpace} {σ : D.Torus ≃ D.Torus} {p : Equiv.Perm (Fin 4)}
  {e : Fin 4 → ℤˣ} {t : Fin 4 → ℤ}
theorem proj_symm_apply (hπ : ∀ x, D.proj (E x) = σ (D.proj x)) (x : AmbientSpace) :
    D.proj (E.symm x) = σ.symm (D.proj x) := by
  rw [Equiv.eq_symm_apply, ← hπ]
  simp
theorem conj_mem_reflectionGroup (hCo : g.ReflectionGroupCoordForm)
    (hc : IsSignedPermShift g E p e t) {a : Equiv.Perm AmbientSpace} (ha : a ∈ g.reflectionGroup) :
    ∃ s ∈ g.reflectionGroup, (s : AmbientSpace → AmbientSpace) = (fun x => E (a (E.symm x))) ∧
      orientationSign s = orientationSign a := by
  have hh : ∀ x, (fun x => E (a (E.symm x))) (E x) = E (a x) := by simp
  have acts := isProductOfCoordMaps_forward (h := fun x => E (a (E.symm x))) (a := a) hc
    E.surjective hh (hCo.1 a ha)
  obtain ⟨s, hs, hsf⟩ := hCo.2.1 _ acts
  refine ⟨s, hs, hsf, ?_⟩
  rw [hCo.2.2.1 s hs, hCo.2.2.1 a ha, hsf,
    numReflectedCoords_eq (h := fun x => E (a (E.symm x))) (a := a) hc E.surjective hh]
theorem conjInv_mem_reflectionGroup (hCo : g.ReflectionGroupCoordForm)
    (hc : IsSignedPermShift g E p e t) {a : Equiv.Perm AmbientSpace} (ha : a ∈ g.reflectionGroup) :
    ∃ s ∈ g.reflectionGroup, (s : AmbientSpace → AmbientSpace) = fun x => E.symm (a (E x)) := by
  have hh : ∀ x, a (E x) = E ((fun x => E.symm (a (E x))) x) := by simp
  exact hCo.2.1 _
    (isProductOfCoordMaps_backward (h := a) (a := fun x => E.symm (a (E x))) hc hh (hCo.1 a ha))
theorem conj_descends (hπ : ∀ x, D.proj (E x) = σ (D.proj x))
    {a : AmbientSpace → AmbientSpace} {b : D.Torus → D.Torus} (hab : D.proj ∘ a = b ∘ D.proj) :
    D.proj ∘ (fun x => E (a (E.symm x))) = conjBy σ b ∘ D.proj := by
  funext x
  have h1 := congrFun hab (E.symm x)
  simp only [Function.comp] at h1 ⊢
  rw [hπ, h1, proj_symm_apply hπ, conjBy]
theorem conjBy_mem (hCo : g.ReflectionGroupCoordForm) (hc : IsSignedPermShift g E p e t)
    (hπ : ∀ x, D.proj (E x) = σ (D.proj x)) {b : D.Torus → D.Torus}
    (hb : b ∈ g.inducedTorusMaps) : conjBy σ b ∈ g.inducedTorusMaps := by
  obtain ⟨a, ha, hab⟩ := hb
  obtain ⟨s, hs, hsf, -⟩ := conj_mem_reflectionGroup hCo hc ha
  exact ⟨s, hs, hsf ▸ conj_descends hπ hab⟩
theorem conjByInv_mem (hCo : g.ReflectionGroupCoordForm) (hc : IsSignedPermShift g E p e t)
    (hπ : ∀ x, D.proj (E x) = σ (D.proj x)) {b : D.Torus → D.Torus}
    (hb : b ∈ g.inducedTorusMaps) : conjByInv σ b ∈ g.inducedTorusMaps := by
  obtain ⟨a, ha, hab⟩ := hb
  obtain ⟨s, hs, hsf⟩ := conjInv_mem_reflectionGroup hCo hc ha
  refine ⟨s, hs, ?_⟩
  rw [hsf]
  funext x
  have h1 := congrFun hab (E x)
  simp only [Function.comp] at h1 ⊢
  rw [proj_symm_apply hπ, h1, hπ, conjByInv]
theorem conjBy_bijOn (hCo : g.ReflectionGroupCoordForm) (hc : IsSignedPermShift g E p e t)
    (hπ : ∀ x, D.proj (E x) = σ (D.proj x)) :
    BijOn (conjBy σ) g.inducedTorusMaps g.inducedTorusMaps := by
  refine InvOn.bijOn (f' := conjByInv σ) ⟨fun b _ => ?_, fun b _ => ?_⟩
    (fun b hb => conjBy_mem hCo hc hπ hb) (fun b hb => conjByInv_mem hCo hc hπ hb)
  · funext u
    simp [conjBy, conjByInv]
  · funext u
    simp [conjBy, conjByInv]
theorem torusSign_conjBy (hG : g.TorusGroupQuotient) (hCo : g.ReflectionGroupCoordForm)
    (hc : IsSignedPermShift g E p e t) (hπ : ∀ x, D.proj (E x) = σ (D.proj x))
    {b : D.Torus → D.Torus} (hb : b ∈ g.inducedTorusMaps) :
    g.torusSign (conjBy σ b) = g.torusSign b := by
  obtain ⟨s, hs, hsf, hsgn⟩ := conj_mem_reflectionGroup hCo hc (g.inducingElement b).2
  have h1 : D.proj ∘ s = conjBy σ b ∘ D.proj := by
    rw [hsf]
    exact conj_descends hπ (inducingElement_spec hb)
  have h2 := hG.2.2.2.1 _ (g.inducingElement (conjBy σ b)).2 _ hs (conjBy σ b)
    (inducingElement_spec (conjBy_mem hCo hc hπ hb)) h1
  exact h2.trans hsgn
theorem torusProduct_pullback_comm (hG : g.TorusGroupQuotient) (hCo : g.ReflectionGroupCoordForm)
    (hc : IsSignedPermShift g E p e t) (hπ : ∀ x, D.proj (E x) = σ (D.proj x))
    (hl : HasLinkImages D σ) (hlG : ∀ b ∈ g.inducedTorusMaps, HasLinkImages D b)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusProduct (D.pullbackObservable σ F) = D.pullbackObservable σ (g.torusProduct F) := by
  funext U
  symm
  refine finprod_mem_eq_of_bijOn (conjBy σ) (conjBy_bijOn hCo hc hπ) fun b hb => ?_
  change Conventions.signedConj (g.torusSign b) (F (D.pullbackField b (D.pullbackField σ U))) =
    Conventions.signedConj (g.torusSign (conjBy σ b))
      (F (D.pullbackField σ (D.pullbackField (conjBy σ b) U)))
  rw [torusSign_conjBy hG hCo hc hπ hb,
    pullbackField_comm (hlG _ (conjBy_mem hCo hc hπ hb)) hl hl (hlG b hb)
      (fun u => by simp [conjBy]) U]
theorem periodicExpectation_congr (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {A B : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (h : ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), A U = B U) :
    D.periodicExpectation A = D.periodicExpectation B := by
  have h1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hnull := (hW D.L D.m D.K D.β h1 D.m.pos D.K.pos).2.2.2.2.2.2.2.2.1
  have hae : ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β),
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
    rw [ae_iff]
    exact hnull
  refine integral_congr_ae ?_
  filter_upwards [hae] with U hU using h U hU
theorem measurable_pullbackField (r : D.Torus → D.Torus) : Measurable (D.pullbackField r) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem measurable_torusTransport (r : D.Torus → D.Torus)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : Measurable F) : Measurable (g.torusTransport r F) := by
  have h1 : Measurable (D.pullbackObservable r F) := hF.comp (measurable_pullbackField r)
  by_cases h : g.torusSign r = 1
  · have : g.torusTransport r F = D.pullbackObservable r F := by
      funext U
      simp [ReflectionGrid.torusTransport, Conventions.signedConjFun, Conventions.signedConj, h]
    rwa [this]
  · have : g.torusTransport r F = fun U => starRingEnd ℂ (D.pullbackObservable r F U) := by
      funext U
      simp [ReflectionGrid.torusTransport, Conventions.signedConjFun, Conventions.signedConj, h]
    rw [this]
    exact Complex.continuous_conj.measurable.comp h1
theorem norm_signedConj (s : ℤˣ) (z : ℂ) : ‖Conventions.signedConj s z‖ = ‖z‖ := by
  by_cases h : s = 1 <;> simp [Conventions.signedConj, h]
theorem torusProduct_isPeriodicObservable (hfin : g.inducedTorusMaps.Finite)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : Measurable F) {c : ℝ} (hc : ∀ U, ‖F U‖ ≤ c) :
    InfiniteLattice.IsPeriodicObservable (g.torusProduct F) := by
  have h1 : g.torusProduct F = fun U => ∏ r' ∈ hfin.toFinset, g.torusTransport r' F U :=
    funext fun U => finprod_mem_eq_finite_toFinset_prod _ hfin
  rw [h1]
  refine ⟨Finset.measurable_prod _ fun r' _ => measurable_torusTransport r' hF,
    ∏ _r' ∈ hfin.toFinset, |c|, fun U _ => ?_⟩
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r' _ => ?_
  change ‖Conventions.signedConj _ (F _)‖ ≤ _
  rw [norm_signedConj]
  exact (hc _).trans (le_abs_self _)
theorem torusProduct_congr (hlG : ∀ b ∈ g.inducedTorusMaps, HasLinkImages D b)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (h : ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), F U = F' U)
    (U : D.PeriodicLink → Matrices.ComplexMatrix2)
    (hU : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :
    g.torusProduct F U = g.torusProduct F' U := by
  refine finprod_mem_congr rfl fun b hb => ?_
  change Conventions.signedConj _ (F _) = Conventions.signedConj _ (F' _)
  rw [h _ (pullbackField_mem_compact (hlG b hb) hU)]
theorem exists_measurable_representative {S : Set AmbientSpace}
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hBr : ∀ F' ∈ g.torusCellObservables (D.proj '' S),
      ∃ F ∈ ReflectionGrid.cellObservables (D := D) S,
        D.AgreeOnCompactFields (D.liftedObservable F) F')
    (hF : F ∈ g.torusCellObservables (D.proj '' S)) :
    ∃ F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, Measurable F' ∧
      (∃ c : ℝ, ∀ U, ‖F' U‖ ≤ c) ∧
      ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), F' U = F U := by
  obtain ⟨F₀, ⟨f, hm, ⟨c, hc⟩, rfl⟩, hsame⟩ := hBr F hF
  refine ⟨D.liftedObservable (f ∘ ReflectionGrid.restrictField S), ?_, ⟨c, fun U => hc _⟩, hsame⟩
  have h1 : Measurable (ReflectionGrid.restrictField (D := D) S) := by
    refine measurable_pi_lambda _ fun b => Continuous.measurable ?_
    exact (continuous_apply b.1).comp continuous_subtype_val
  exact (hm.comp h1).comp (InfiniteLattice.measurable_liftField _ _ _)
end
section
variable {D : ChessboardSetup} {g : ReflectionGrid D} {n : ℤ} {p : Equiv.Perm (Fin 4)}
  {e : Fin 4 → ℤˣ} {t : Fin 4 → ℤ}
theorem bijective_of_isSignedPermShift {r : D.Torus → D.Torus}
    {ρ : AmbientSpace → AmbientSpace} (hs : Function.Surjective ρ)
    (hc : IsSignedPermShift g ρ p e t)
    (hρ : D.proj ∘ ρ = r ∘ D.proj) : Function.Bijective r := by
  constructor
  · intro u v huv
    obtain ⟨x, rfl⟩ := proj_surjective (D := D) u
    obtain ⟨y, rfl⟩ := proj_surjective (D := D) v
    have h1 : D.proj (ρ x) = D.proj (ρ y) := by
      have a1 := congrFun hρ x
      have a2 := congrFun hρ y
      simp only [Function.comp] at a1 a2
      rw [a1, a2, huv]
    obtain ⟨j, hj⟩ := exists_translate_of_proj_eq h1
    have h2 : x = y + TestFunctions.latticeTranslate (periodOf D)
        (fun μ => (e (p.symm μ) : ℤ) * j (p.symm μ)) := by
      funext μ
      obtain ⟨ν, rfl⟩ := p.surjective μ
      have h3 := congrFun hj ν
      simp only [Pi.add_apply, TestFunctions.latticeTranslate] at h3 ⊢
      rw [hc x ν, hc y ν] at h3
      simp only [Equiv.symm_apply_apply]
      push_cast
      have hu := intUnit_mul_self (e ν)
      linear_combination ((e ν : ℤ) : ℝ) * h3 - (x (p ν) - y (p ν)) * hu
    rw [h2]
    exact proj_add_translate y _
  · intro u
    obtain ⟨y, rfl⟩ := proj_surjective (D := D) u
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨D.proj x, (congrFun hρ x).symm⟩
theorem chessboardEstimate_preserved
    (hBr : ∀ S ∈ g.cellSet, ∀ F' ∈ g.torusCellObservables (D.proj '' S),
      ∃ F ∈ ReflectionGrid.cellObservables (D := D) S,
        D.AgreeOnCompactFields (D.liftedObservable F) F')
    (hI : QuotientMapsStatement) (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hn : periodOf D = n * g.cellSide) (hG : g.TorusGroupQuotient)
    (hCo : g.ReflectionGroupCoordForm)
    {r : D.Torus → D.Torus} (hr : g.PreservesLatticeAndWalls r) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) :
    ∃ (_ : r '' C ∈ g.torusCellSet)
      (_ : D.pullbackObservable r F ∈ g.torusCellObservables (r '' C)),
      (∃ σ : D.Torus ≃ D.Torus, ⇑σ = r ∧
        D.pullbackObservable r F = PeriodicLattice.transportObservable σ F) ∧
      g.torusChessboardNorm (D.pullbackObservable r F) = g.torusChessboardNorm F := by
  obtain ⟨ρ, hρ⟩ := (hI D).2.2.2.2 ⟨r, hr.1, hr.2.1⟩
  have hρ' : D.proj ∘ ρ.toFun = r ∘ D.proj := hρ
  obtain ⟨p, e, t, hc⟩ := isSignedPermShift_of_preserves hn hr ρ hρ'
  have hsurj : Function.Surjective ρ.toFun := ρ.toFun_bijective.2
  have hbij := bijective_of_isSignedPermShift hsurj hc hρ'
  let σ : D.Torus ≃ D.Torus := Equiv.ofBijective r hbij
  let E : AmbientSpace ≃ AmbientSpace := ρ.toEquivAmbient
  have hcE : IsSignedPermShift g E p e t := hc
  have hπ : ∀ x, D.proj (E x) = σ (D.proj x) := fun x => congrFun hρ' x
  have hl' : HasLinkImages D r := hasLinkImages_of hbij hr.1 hr.2.1
  have hl : HasLinkImages D σ := hl'
  have hlG : ∀ b ∈ g.inducedTorusMaps, HasLinkImages D b := fun b hb =>
    hasLinkImages_of (bijective_of_mem_inducedTorusMaps hG hb) (hG.2.2.1 b hb)
      (hG.2.2.2.2.1 b hb).1
  obtain ⟨S, hS, rfl⟩ := hC
  obtain ⟨k, rfl⟩ := hS
  have hImg : r '' (D.proj '' g.cell k) = D.proj '' g.cell (cellImageIndex p e t k) := by
    rw [← image_comp, ← hρ', image_comp,
      image_eq_of_forall_mem_iff hsurj (mem_cell_image_iff hc k)]
  have hImgO : r '' (D.proj '' interior (g.cell k)) =
      D.proj '' interior (g.cell (cellImageIndex p e t k)) := by
    rw [← image_comp, ← hρ', image_comp,
      image_eq_of_forall_mem_iff hsurj (mem_interior_image_iff hc k)]
  have hrC : r '' (D.proj '' g.cell k) ∈ g.torusCellSet := by
    rw [hImg]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hOpen : ∀ u ∈ g.torusCellInterior (D.proj '' g.cell k),
      r u ∈ g.torusCellInterior (r '' (D.proj '' g.cell k)) := by
    intro u hu
    rw [hImg, torusCellInterior_proj_image hn, ← hImgO]
    rw [torusCellInterior_proj_image hn] at hu
    exact mem_image_of_mem r hu
  have hlinks : ∀ b ∈ g.torusCellLinks (D.proj '' g.cell k),
      D.imageLink r b ∈ g.torusCellLinks (r '' (D.proj '' g.cell k)) := by
    intro b hb
    refine ⟨?_, ?_⟩
    · rw [(imageLink_spec hl' b).1]
      exact hOpen _ hb.1
    · rw [(imageLink_spec hl' b).2]
      exact hOpen _ hb.2
  have hrF : D.pullbackObservable r F ∈
      g.torusCellObservables (r '' (D.proj '' g.cell k)) := by
    obtain ⟨f, hm, ⟨c, hcb⟩, hrep⟩ := hF
    refine ⟨fun w => f fun b => w ⟨D.imageLink r b.1, hlinks b.1 b.2⟩,
      hm.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨c, fun _ => hcb _⟩,
      fun U => ?_⟩
    exact hrep ⟨_, pullbackField_mem_compact hl' U.2⟩
  refine ⟨hrC, hrF, ⟨σ, rfl, pullbackObservable_eq_transport hl F⟩, ?_⟩
  have hfG := finite_inducedTorusMaps hG
  obtain ⟨F', hm', ⟨c', hc'⟩, hsame⟩ := exists_measurable_representative (hBr _ ⟨k, rfl⟩) hF
  have hObs := torusProduct_isPeriodicObservable (g := g) (toFinite _) hm' hc'
  obtain ⟨s, hs1, hs2⟩ := (hI D).2.1 ρ ((hI D).2.2.2.1 ρ)
  have hsr : s = r := by
    funext u
    obtain ⟨x, rfl⟩ := proj_surjective (D := D) u
    exact (congrFun hs1 x).symm.trans (congrFun hρ' x)
  rw [hsr] at hs2
  have hInv := hs2 _ hObs
  have hArr : g.torusProduct (D.pullbackObservable r F) =
      D.pullbackObservable r (g.torusProduct F) :=
    torusProduct_pullback_comm hG hCo hcE hπ hl hlG F
  have e1 : D.periodicExpectation (g.torusProduct (D.pullbackObservable r F)) =
      D.periodicExpectation (g.torusProduct F) := by
    rw [hArr]
    calc D.periodicExpectation (D.pullbackObservable r (g.torusProduct F))
        = D.periodicExpectation (D.pullbackObservable r (g.torusProduct F')) :=
          periodicExpectation_congr hW fun U hU =>
            torusProduct_congr hlG (fun V hV => (hsame V hV).symm) _
              (pullbackField_mem_compact hl' hU)
      _ = D.periodicExpectation (g.torusProduct F') := hInv
      _ = D.periodicExpectation (g.torusProduct F) :=
          periodicExpectation_congr hW fun U hU => torusProduct_congr hlG hsame U hU
  simp only [ReflectionGrid.torusChessboardNorm, e1]
end
end ChessboardBoundOnReflectionGrids
theorem ChessboardBoundOnReflectionGrids.proof
    (hB : TorusReduction.Statement)
    (hS : TorusChessboardSeminorms.Statement)
    (hI : QuotientMapsStatement)
    (hE : GridBasicProperties.Statement)
    (hA : ReflectionGridArithmetic.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    ChessboardBoundOnReflectionGrids.Statement := by
  open ChessboardBoundOnReflectionGrids in
  intro D g hside
  obtain ⟨b1, -, -, -, -, b6, b7⟩ := hB D g hside
  have hEg := hE D g
  have hCo := hEg.2.2.2.1
  obtain ⟨-, hG, -⟩ := hEg.2.2.2.2.2.2 hside
  have hn := period_eq_mul_cellSide hA g hside
  refine ⟨fun F hF => ?_, fun C hC F hF z => ?_, fun k₀ g' hs' hside' hwalls Q hQ F hF => ?_⟩
  · classical
    let Fe : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun C =>
      if h : C ∈ g.torusCellSet then F ⟨C, h⟩ else fun _ => 0
    have hFe : ∀ C : g.torusCellSet, Fe C.1 = F C := fun C => by
      simp only [Fe, dif_pos C.2, Subtype.coe_eta]
    have hMem : ∀ C ∈ g.torusCellSet, Fe C ∈ g.torusCellObservables C := fun C hC => by
      have := hFe ⟨C, hC⟩
      simp only at this
      rw [this]
      exact hF ⟨C, hC⟩
    have h1 := b7 Fe hMem
    have h2 : (fun U => ∏ᶠ C ∈ g.torusCellSet, Fe C U) = fun U => ∏ᶠ C, F C U := by
      funext U
      rw [← finprod_set_coe_eq_finprod_mem]
      simp only [hFe]
    rw [h2, ← finprod_set_coe_eq_finprod_mem] at h1
    simp only [hFe] at h1
    exact h1
  · obtain ⟨-, -, s3, s4, -⟩ := hS D g hside C hC
    obtain ⟨a1, -, a3, a4, -⟩ := s3 F hF F hF z
    obtain ⟨f, hm, ⟨c, hcb⟩, hrep⟩ := id hF
    refine ⟨a4, ⟨⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, fun _ => rfl⟩, s4⟩,
      ⟨⟨fun w => z * f w, hm.const_mul z, ⟨‖z‖ * c, fun u => ?_⟩, fun U => ?_⟩, a1⟩,
      ⟨⟨fun w => starRingEnd ℂ (f w), Complex.continuous_conj.measurable.comp hm,
        ⟨c, fun u => by simpa using hcb u⟩, fun U => ?_⟩, (s3 F hF F hF 0).2.2.1⟩,
      fun r hr => ?_⟩
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hcb u) (norm_nonneg _)
    · beta_reduce
      rw [hrep U]
    · beta_reduce
      rw [hrep U]
    · obtain ⟨S, hS', rfl⟩ := hC
      exact chessboardEstimate_preserved (fun S hS => (b1 S hS).2.2.2.2) hI hW hn hG hCo hr ⟨S, hS', rfl⟩ hF
  · have hn' := period_eq_mul_cellSide hA g' hside'
    have hEg' := hE D g'
    obtain ⟨-, hG', -⟩ := hEg'.2.2.2.2.2.2 hside'
    have hD' := hEg'.2.2.2.2.2.1
    have fC := finite_torusCellSet hG
    have fQ : Finite (g.torusCellsWithin Q) :=
      ((toFinite g.torusCellSet).subset fun C hC => hC.1).to_subtype
    exact ⟨prod_mem_torusCellObservables hn hn' hwalls hD' hQ F hF,
      coarse_bound hn' hwalls hD' hG hG' hCo b7
        (fun C hC F hF C' hC' => (b6 C hC F hF).2.2.1 C' hC')
        (fun C hC F hF a ha => ((hS D g hside C hC).1 F hF F hF 0 a ha C hC).1) hQ F hF⟩
end YangMills.Construction.ChessboardTori
end
