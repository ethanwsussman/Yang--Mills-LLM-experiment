import YangMills.Construction.InequalityOnMirroredCopies.ArrayMeanIsTheMeanOnTheTorusProof
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.Lattice.GridDataOfEqualSides
import YangMills.Construction.Lattice.WeightsAsFunctionsOfTheConfigurationAndSourcedIntegrals
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGridArithmetic
theorem pullbackField_comp {a : ℝ} (r r' : InfiniteLattice.LatticeSymmetry a)
    (U : InfiniteLattice.GaugeField a) :
    r'.pullbackField (r.pullbackField U) = (r.comp r').pullbackField U := rfl
def invSymmetry {a : ℝ} (r : InfiniteLattice.LatticeSymmetry a) :
    InfiniteLattice.LatticeSymmetry a where
  toFun := r.toEquivAmbient.symm
  preservesDist x y := by
    obtain ⟨u, rfl⟩ := r.toEquivAmbient.surjective x
    obtain ⟨v, rfl⟩ := r.toEquivAmbient.surjective y
    simp only [Equiv.symm_apply_apply]
    exact (r.preservesDist u v).symm
  image_eq := by
    have h : (r.toEquivAmbient : AmbientSpace → AmbientSpace) ''
        (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) =
        InfiniteLattice.latticeSubgroup a := r.image_eq
    conv_lhs => rw [← h]
    rw [← image_comp]
    simp
theorem invSymmetry_comp {a : ℝ} (r : InfiniteLattice.LatticeSymmetry a) :
    (invSymmetry r).toFun ∘ r.toFun = id :=
  funext fun x => r.toEquivAmbient.symm_apply_apply x
theorem comp_invSymmetry {a : ℝ} (r : InfiniteLattice.LatticeSymmetry a) :
    r.toFun ∘ (invSymmetry r).toFun = id :=
  funext fun x => r.toEquivAmbient.apply_symm_apply x
theorem pullbackField_of_eq_id {a : ℝ} (c : InfiniteLattice.LatticeSymmetry a)
    (h : c.toFun = id) (U : InfiniteLattice.GaugeField a) : c.pullbackField U = U := by
  refine Subtype.ext (funext fun b => ?_)
  have e : c.linkMap b = b :=
    InfiniteLattice.Link.ext (Subtype.ext (congrFun h _)) (Subtype.ext (congrFun h _))
  change U.1 (c.linkMap b) = U.1 b
  rw [e]
theorem continuous_pullbackField {a : ℝ} (s : InfiniteLattice.LatticeSymmetry a) :
    Continuous s.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem latticeSymGroupLaws (D : ChessboardSetup) : D.LatticeSymGroupLaws := by
  intro r r'
  refine ⟨⟨r.comp r', rfl, fun U => rfl, fun F => rfl⟩, invSymmetry r, invSymmetry_comp r,
    comp_invSymmetry r,
    ⟨⟨r.pullbackField, (invSymmetry r).pullbackField, fun U => ?_, fun U => ?_⟩,
      continuous_pullbackField r, continuous_pullbackField (invSymmetry r)⟩, rfl, rfl⟩
  · change (invSymmetry r).pullbackField (r.pullbackField U) = U
    rw [pullbackField_comp]
    exact pullbackField_of_eq_id _ (comp_invSymmetry r) U
  · change r.pullbackField ((invSymmetry r).pullbackField U) = U
    rw [pullbackField_comp]
    exact pullbackField_of_eq_id _ (invSymmetry_comp r) U
theorem exists_reflectionGrid (D : ChessboardSetup) :
    ∃ g : ReflectionGrid D, g.cellSide = (D.L : ℝ) * D.mesh ∧
      g.origin = (D.mesh / 2) • ∑ μ, coordVec μ := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  refine ⟨⟨1 - ((D.K : ℕ) : ℤ), le_rfl, (D.mesh / 2) • ∑ μ, coordVec μ, fun μ => ⟨0, ?_⟩⟩,
    ?_, rfl⟩
  · have h : (∑ ν, coordVec ν) μ = 1 := by
      simp [coordVec, Finset.sum_apply, Pi.single_apply]
    simp only [Pi.smul_apply, h, smul_eq_mul]
    push_cast
    ring
  · simp only [ReflectionGrid.cellSide, ChessboardSetup.mesh, PeriodicLattice.meshSize]
    rw [sub_eq_add_neg, zpow_add₀ hL, zpow_one]
theorem ratioAndPeriods {D : ChessboardSetup} (g : ReflectionGrid D) : g.RatioAndPeriods := by
  have ha : D.mesh ≠ 0 := D.mesh_pos.ne'
  have hq : 0 ≤ g.q + ((D.K : ℕ) : ℤ) := by linarith [g.one_sub_K_le_q]
  refine ⟨?_, ?_, g.two_le_cellRatio, ⟨g.cellRatio, g.cellSide_eq⟩, fun n hn => ⟨?_, fun μ =>
    ⟨rfl, (g.boxPeriods n hn).four_le_mult μ⟩⟩⟩
  · rw [g.cellSide_eq]
    field_simp
  · simp only [ReflectionGrid.cellRatio]
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg hq]
  · change BoxTorus.periods (D.periodLengths _) = _
    congr 1
    funext μ
    simp only [ChessboardSetup.periodLengths, ReflectionGrid.boxPeriods, g.cellSide_eq]
    push_cast
    ring
section Blocks
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem torusSide_eq_zpow :
    PeriodicLattice.torusSide D.L D.m = 2 * (D.L : ℝ) ^ (((D.m : ℕ) : ℤ)) := by
  simp [PeriodicLattice.torusSide]
theorem q_le_m (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    g.q ≤ ((D.m : ℕ) : ℤ) := by
  rw [torusSide_eq_zpow] at h
  have h1 : (D.L : ℝ) ^ g.q ≤ (D.L : ℝ) ^ (((D.m : ℕ) : ℤ)) := by
    exact show g.cellSide ≤ (D.L : ℝ) ^ (((D.m : ℕ) : ℤ)) from by linarith
  exact (zpow_le_zpow_iff_right₀ D.one_lt_factor).mp h1
theorem cellsPerTorusSide_mul_cellSide (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    (g.cellsPerTorusSide : ℝ) * g.cellSide = PeriodicLattice.torusSide D.L D.m := by
  have hq := q_le_m g h
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  have hn : 0 ≤ ((D.m : ℕ) : ℤ) - g.q := by omega
  have h1 : (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - g.q).toNat =
      (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - g.q) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hn]
  rw [torusSide_eq_zpow]
  simp only [ReflectionGrid.cellsPerTorusSide, ReflectionGrid.cellSide]
  push_cast
  rw [h1, mul_assoc, ← zpow_add₀ hL]
  simp
theorem cellsAcross_eq (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    g.cellsAcross = (g.cellsPerTorusSide : ℝ) := by
  rw [ReflectionGrid.cellsAcross, ← cellsPerTorusSide_mul_cellSide g h]
  have := (cellSide_pos g).ne'
  field_simp
theorem even_cellsPerTorusSide : Even g.cellsPerTorusSide := even_two_mul _
theorem two_le_cellsPerTorusSide : 2 ≤ g.cellsPerTorusSide := by
  have hL : (1 : ℤ) ≤ D.L := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  have h : (1 : ℤ) ≤ (D.L : ℤ) ^ (((D.m : ℕ) : ℤ) - g.q).toNat := one_le_pow₀ hL
  simp only [ReflectionGrid.cellsPerTorusSide]
  omega
theorem periodSubgroup_ext {P Q : PeriodSubgroup D} (h : P.mult = Q.mult) : P = Q := by apply _root_.YangMills.SharedProofs.p50270 <;> assumption
theorem boxPeriods_eq_cubicPeriod (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (hn : 2 ≤ g.cellsPerTorusSide) :
    g.boxPeriods (fun _ => g.cellsPerTorusSide) (fun _ => hn) = D.cubicPeriod := by
  refine periodSubgroup_ext (funext fun μ => ?_)
  have hq := q_le_m g h
  have h1 := g.one_sub_K_le_q
  have e : (((D.m : ℕ) : ℤ) - g.q).toNat + (g.q + ((D.K : ℕ) : ℤ)).toNat =
      (D.m : ℕ) + (D.K : ℕ) := by omega
  change g.cellsPerTorusSide * g.cellRatio = 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ))
  rw [ReflectionGrid.cellsPerTorusSide, ReflectionGrid.cellRatio, mul_assoc, ← pow_add, e]
theorem exists_int_index {N : ℤ} {s t : ℝ} (hN : 1 ≤ N) (hs : 0 < s) (h0 : 0 ≤ t)
    (h1 : t ≤ (N : ℝ) * s) :
    ∃ i : ℤ, 0 ≤ i ∧ i ≤ N - 1 ∧ 0 ≤ t - s * i ∧ t - s * i ≤ s := by
  have hdiv : t / s ≤ N := (div_le_iff₀ hs).mpr h1
  have hd0 : 0 ≤ t / s := div_nonneg h0 hs.le
  have hf0 : 0 ≤ ⌊t / s⌋ := Int.floor_nonneg.mpr hd0
  have hle : (min ⌊t / s⌋ (N - 1) : ℤ) ≤ ⌊t / s⌋ := min_le_left _ _
  refine ⟨min ⌊t / s⌋ (N - 1), le_min hf0 (by omega), min_le_right _ _, ?_, ?_⟩
  · have h2 : ((min ⌊t / s⌋ (N - 1) : ℤ) : ℝ) ≤ t / s :=
      le_trans (by exact_mod_cast hle) (Int.floor_le _)
    have h3 := (le_div_iff₀ hs).mp h2
    linarith
  · have h2 : t / s ≤ ((min ⌊t / s⌋ (N - 1) : ℤ) : ℝ) + 1 := by
      rcases le_total ⌊t / s⌋ (N - 1) with h | h
      · rw [min_eq_left h]
        exact (Int.lt_floor_add_one _).le
      · rw [min_eq_right h]
        push_cast
        linarith
    have h3 := (div_le_iff₀ hs).mp h2
    nlinarith
theorem exists_cell_of_mem_block (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (k : Fin 4 → ℤ) {x : AmbientSpace} (hx : x ∈ g.block k) :
    ∃ j ∈ g.blockIndices k, x ∈ g.cell j := by
  have hN := two_le_cellsPerTorusSide g
  have hs := cellSide_pos g
  have hc := cellsPerTorusSide_mul_cellSide g h
  have hi : ∀ μ, ∃ i : ℤ, 0 ≤ i ∧ i ≤ g.cellsPerTorusSide - 1 ∧
      0 ≤ (x μ - (g.origin μ + g.cellSide * k μ)) - g.cellSide * i ∧
      (x μ - (g.origin μ + g.cellSide * k μ)) - g.cellSide * i ≤ g.cellSide := fun μ =>
    exists_int_index (by omega) hs (hx μ).1 (by rw [hc]; exact (hx μ).2)
  choose i h0 h1 h2 h3 using hi
  refine ⟨fun μ => k μ + i μ, fun μ => ⟨by have := h0 μ; show k μ ≤ k μ + i μ; omega,
      by have := h1 μ; show k μ + i μ ≤ k μ + g.cellsPerTorusSide - 1; omega⟩,
    fun μ => ⟨?_, ?_⟩⟩
  · have := h2 μ
    push_cast
    linarith
  · have := h3 μ
    push_cast
    linarith
theorem cell_subset_block (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (k : Fin 4 → ℤ) {j : Fin 4 → ℤ} (hj : j ∈ g.blockIndices k) : g.cell j ⊆ g.block k := by
  have hs := cellSide_pos g
  have hc := cellsPerTorusSide_mul_cellSide g h
  intro x hx μ
  obtain ⟨h1, h2⟩ := hx μ
  obtain ⟨h3, h4⟩ := hj μ
  have h3' : (k μ : ℝ) ≤ j μ := by exact_mod_cast h3
  have h4' : (j μ : ℝ) + 1 ≤ k μ + g.cellsPerTorusSide := by
    have : j μ + 1 ≤ k μ + g.cellsPerTorusSide := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · nlinarith
  · rw [← hc]
    nlinarith
def lowerCorner (j : Fin 4 → ℤ) : AmbientSpace := fun μ => g.origin μ + g.cellSide * j μ
def upperCorner (j : Fin 4 → ℤ) : AmbientSpace := fun μ => g.origin μ + g.cellSide * (j μ + 1)
theorem lowerCorner_mem (j : Fin 4 → ℤ) : lowerCorner g j ∈ g.cell j := fun μ => by
  have := cellSide_pos g
  simp [lowerCorner, this.le]
theorem upperCorner_mem (j : Fin 4 → ℤ) : upperCorner g j ∈ g.cell j := fun μ => by
  have := cellSide_pos g
  refine ⟨?_, ?_⟩ <;> simp only [upperCorner] <;> nlinarith
theorem mem_blockIndices_of_cell_subset (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (k j : Fin 4 → ℤ) (hsub : g.cell j ⊆ g.block k) : j ∈ g.blockIndices k := by
  have hs := cellSide_pos g
  have hc := cellsPerTorusSide_mul_cellSide g h
  intro μ
  have h1 := (hsub (lowerCorner_mem g j) μ).1
  have h2 := (hsub (upperCorner_mem g j) μ).2
  simp only [lowerCorner, upperCorner] at h1 h2
  rw [← hc] at h2
  have h1' : (k μ : ℝ) ≤ j μ := by
    by_contra hn
    have hn := not_le.mp hn
    nlinarith
  have h2' : (j μ : ℝ) + 1 ≤ k μ + g.cellsPerTorusSide := by
    by_contra hn
    have hn := not_le.mp hn
    nlinarith
  have h3 : k μ ≤ j μ := by exact_mod_cast h1'
  have h4 : j μ + 1 ≤ k μ + g.cellsPerTorusSide := by exact_mod_cast h2'
  exact ⟨h3, by omega⟩
theorem cell_injective : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
theorem ncard_blockIndices (k : Fin 4 → ℤ) :
    ((g.blockIndices k).ncard : ℤ) = g.cellsPerTorusSide ^ 4 := by
  have hN := two_le_cellsPerTorusSide g
  have e : g.blockIndices k = ((Fintype.piFinset fun μ =>
      Finset.Icc (k μ) (k μ + g.cellsPerTorusSide - 1) : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)) := by
    ext j
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    simp only [Finset.mem_Icc]
    rfl
  rw [e, Set.ncard_coe_finset, Fintype.card_piFinset]
  have h1 : ∀ μ, (Finset.Icc (k μ) (k μ + g.cellsPerTorusSide - 1)).card =
      g.cellsPerTorusSide.toNat := fun μ => by
    rw [Int.card_Icc]
    congr 1
    ring
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (by omega)]
theorem blockEqUnionCells (h : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (k : Fin 4 → ℤ) : g.BlockEqUnionCells k := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun hx => exists_cell_of_mem_block g h k hx,
      fun ⟨j, hj, hx⟩ => cell_subset_block g h k hj hx⟩
  · ext S
    constructor
    · rintro ⟨⟨j, rfl⟩, hsub⟩
      exact ⟨j, mem_blockIndices_of_cell_subset g h k j hsub, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, cell_subset_block g h k hj⟩
  · rw [Set.ncard_image_of_injective _ (cell_injective g)]
    exact ncard_blockIndices g k
end Blocks
abbrev cutoffInt (D : ChessboardSetup) : ℤ := ((D.K : ℕ) : ℤ)
def edgeFamily (D : ChessboardSetup) {σ : Fin 4 → ℝ}
    (eL : BoxTorus.DirectedEdge D.L (cutoffInt D) σ ≃ D.PeriodicLink)
    (U : BoxTorus.GaugeConfig D.L (cutoffInt D) σ) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun b => (BoxTorus.edgeVariable U (eL.symm b) : Matrices.ComplexMatrix2)
structure TorusIdentification (D : ChessboardSetup) (σ : Fin 4 → ℝ)
    (e : BoxTorus.Space σ ≃+ D.Torus)
    (eL : BoxTorus.DirectedEdge D.L (cutoffInt D) σ ≃ D.PeriodicLink)
    (eP : BoxTorus.Face D.L (cutoffInt D) σ ≃ D.PeriodicPlaquette) : Prop where
  finite_faces : Finite (BoxTorus.Face D.L (cutoffInt D) σ)
  isHomeomorph : IsHomeomorph e
  proj_eq : ∀ y, e (BoxTorus.projection σ y) = D.proj y
  gridSubgroup_image : e '' (BoxTorus.gridSubgroup D.L (cutoffInt D) σ : Set (BoxTorus.Space σ)) =
    (PeriodicLattice.sublattice D.L D.m (cutoffInt D) : Set D.Torus)
  endpoints : ∀ b : BoxTorus.DirectedEdge D.L (cutoffInt D) σ,
    ((eL b).source : D.Torus) = e (b.source : BoxTorus.Space σ) ∧
      ((eL b).target : D.Torus) = e (b.target : BoxTorus.Space σ)
  forward_iff : ∀ b, b.IsForward ↔ (eL b).IsPositivelyOriented
  flip_eq : ∀ b, eL b.flip = (eL b).opposite
  corner_eq : ∀ p : BoxTorus.Face D.L (cutoffInt D) σ,
    ((eP p).origin : D.Torus) = e (p.corner : BoxTorus.Space σ)
  dir₁_eq : ∀ p, (eP p).firstAxis = p.dir₁
  dir₂_eq : ∀ p, (eP p).secondAxis = p.dir₂
  bijOn : BijOn (edgeFamily D eL) univ (PeriodicLattice.compactGaugeFields D.L D.m (cutoffInt D))
  map_haar : (BoxTorus.haarConfigMeasure D.L (cutoffInt D) σ).map (edgeFamily D eL) =
    PeriodicLattice.productHaarMeasure D.L D.m (cutoffInt D)
  holonomy_eq : ∀ (U : BoxTorus.GaugeConfig D.L (cutoffInt D) σ) p,
    (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy (edgeFamily D eL U) (eP p)
def cubicGrid (D : ChessboardSetup) : CellGrid D.L (cutoffInt D) where
  admissible := D.isAdmissible
  cellLength := D.mesh
  cellLength_pos := D.mesh_pos
  cellLength_div_meshSize := ⟨1, by
    have := D.mesh_pos
    simp only [Int.cast_one]
    exact div_self this.ne'⟩
  counts _ := 2 * D.L ^ ((D.m : ℕ) + (D.K : ℕ))
  counts_pos _ := by
    have h := D.isAdmissible.2
    have : 0 < D.L := by omega
    positivity
  counts_even _ := even_two_mul _
  four_meshSize_le μ := by
    have h : (4 : ℤ) ≤ 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) := D.cubicPeriod.four_le_mult μ
    have h' : (4 : ℝ) ≤ ((2 * D.L ^ ((D.m : ℕ) + (D.K : ℕ)) : ℕ) : ℝ) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h' D.mesh_pos.le
  centre _ := D.mesh * (((0 : ℤ) : ℝ) + 1 / 2)
  centre_mem _ := ⟨0, rfl⟩
theorem sideLengths_cubicGrid (D : ChessboardSetup) :
    (cubicGrid D).sideLengths = D.cubicPeriod.sideLengths := by
  funext μ
  simp only [CellGrid.sideLengths, cubicGrid, PeriodSubgroup.sideLengths,
    ChessboardSetup.periodLengths, ChessboardSetup.cubicPeriod]
  push_cast
  rfl
theorem hasEqualSides_cubicGrid (D : ChessboardSetup) :
    (cubicGrid D).HasEqualSides (D.m : ℕ) := fun μ => by
  rw [sideLengths_cubicGrid, D.sideLengths_cubicPeriod]
def faceEquiv (D : ChessboardSetup) :
    (cubicGrid D).Face ≃ D.PeriodicPlaquette where
  toFun := CellGrid.plaquetteOfFace (hasEqualSides_cubicGrid D)
  invFun p := ⟨(CellGrid.gridPointEquivSite (hasEqualSides_cubicGrid D)).symm p.origin,
    p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  left_inv _ := BoxTorus.Face.ext
    ((CellGrid.gridPointEquivSite (hasEqualSides_cubicGrid D)).symm_apply_apply _) rfl rfl
  right_inv _ := PeriodicLattice.Plaquette.ext
    ((CellGrid.gridPointEquivSite (hasEqualSides_cubicGrid D)).apply_symm_apply _) rfl rfl
theorem identification_cubicGrid (hG : EqualSideGrids.Statement) (D : ChessboardSetup) :
    TorusIdentification D (cubicGrid D).sideLengths
      (CellGrid.spaceEquivTorus (hasEqualSides_cubicGrid D))
      (CellGrid.edgeEquivBond (hasEqualSides_cubicGrid D)) (faceEquiv D) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6⟩, h7, -⟩ :=
    hG D.toStandingParameters (cubicGrid D) (hasEqualSides_cubicGrid D) D.β D.beta_pos
  exact
    { finite_faces := inferInstanceAs (Finite (cubicGrid D).Face)
      isHomeomorph := h1
      proj_eq := fun _ => rfl
      gridSubgroup_image := h2
      endpoints := fun _ => ⟨rfl, rfl⟩
      forward_iff := h3
      flip_eq := h4
      corner_eq := fun _ => rfl
      dir₁_eq := fun _ => rfl
      dir₂_eq := fun _ => rfl
      bijOn := h5
      map_haar := h6
      holonomy_eq := fun U p => (h7 U p).1 }
theorem exists_identification (hG : EqualSideGrids.Statement) (D : ChessboardSetup) :
    ∃ e eL eP, TorusIdentification D D.cubicPeriod.sideLengths e eL eP := by
  have h : ∃ e eL eP, TorusIdentification D (cubicGrid D).sideLengths e eL eP :=
    ⟨_, _, _, identification_cubicGrid hG D⟩
  rwa [sideLengths_cubicGrid] at h
section Facts
variable {D : ChessboardSetup} {σ : Fin 4 → ℝ} {e : BoxTorus.Space σ ≃+ D.Torus}
  {eL : BoxTorus.DirectedEdge D.L (cutoffInt D) σ ≃ D.PeriodicLink}
  {eP : BoxTorus.Face D.L (cutoffInt D) σ ≃ D.PeriodicPlaquette}
theorem TorusIdentification.torusDist_eq (R : TorusIdentification D σ e eL eP)
    (u v : BoxTorus.Space σ) :
    BoxTorus.torusDist u v = TorusMetric.torusEuclidNorm (e u - e v) := by
  have h : {z : Fin 4 → ℝ | BoxTorus.IsLiftOf z (u - v)} =
      TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) ⁻¹' {e u - e v} := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, BoxTorus.IsLiftOf]
    rw [← map_sub, ← e.injective.eq_iff, R.proj_eq]
    rfl
  rw [BoxTorus.torusDist, h]
  rfl
theorem TorusIdentification.map_axisPoint (R : TorusIdentification D σ e eL eP) (ν : Fin 4)
    (t : ℝ) :
    e (BoxTorus.projection σ (t • BoxTorus.basisVector ν)) =
      PeriodicLattice.pointOnAxis D.L D.m ν t := by
  rw [R.proj_eq]
  funext μ
  by_cases h : μ = ν
  · subst h
    simp [ChessboardSetup.proj, TorusMetric.torusProj, PeriodicLattice.pointOnAxis,
      BoxTorus.basisVector]
  · simp [ChessboardSetup.proj, TorusMetric.torusProj, PeriodicLattice.pointOnAxis,
      BoxTorus.basisVector, Pi.single_eq_of_ne h]
theorem TorusIdentification.map_gridStep (R : TorusIdentification D σ e eL eP) (ν : Fin 4) :
    e (BoxTorus.gridStep D.L (cutoffInt D) σ ν : BoxTorus.Space σ) =
      (PeriodicLattice.unitStep D.L D.m (cutoffInt D) ν : D.Torus) :=
  R.map_axisPoint ν _
theorem TorusIdentification.image_vertexSet (R : TorusIdentification D σ e eL eP)
    (p : BoxTorus.Face D.L (cutoffInt D) σ) :
    (fun x : BoxTorus.GridPoint D.L (cutoffInt D) σ => e (x : BoxTorus.Space σ)) ''
        p.vertexSet =
      (fun y : PeriodicLattice.Site D.L D.m (cutoffInt D) => (y : D.Torus)) ''
        (eP p).vertices := by
  simp only [BoxTorus.Face.vertexSet, PeriodicLattice.Plaquette.vertices, image_insert_eq,
    image_singleton, AddSubgroup.coe_add, map_add, R.corner_eq, R.dir₁_eq, R.dir₂_eq,
    R.map_gridStep]
theorem TorusIdentification.map_faceCenter (R : TorusIdentification D σ e eL eP)
    (p : BoxTorus.Face D.L (cutoffInt D) σ) :
    e (BoxTorus.translate (p.corner : BoxTorus.Space σ)
        ((D.mesh / 2) • (BoxTorus.basisVector p.dir₁ +
          BoxTorus.basisVector p.dir₂))) = (eP p).barycenter := by
  rw [BoxTorus.translate, smul_add, map_add, map_add, map_add, R.map_axisPoint,
    R.map_axisPoint]
  simp only [PeriodicLattice.Plaquette.barycenter, R.corner_eq, R.dir₁_eq, R.dir₂_eq]
  rw [add_assoc]
  rfl
theorem TorusIdentification.faceEnergy_eq (R : TorusIdentification D σ e eL eP)
    (U : BoxTorus.GaugeConfig D.L (cutoffInt D) σ)
    (p : BoxTorus.Face D.L (cutoffInt D) σ) :
    BoxTorus.faceEnergy U p =
      PeriodicLattice.plaquetteCost (edgeFamily D eL U) (eP p) := by
  rw [BoxTorus.faceEnergy, PeriodicLattice.plaquetteCost, R.holonomy_eq]
theorem TorusIdentification.wilsonAction_eq (R : TorusIdentification D σ e eL eP)
    (U : BoxTorus.GaugeConfig D.L (cutoffInt D) σ) :
    BoxTorus.wilsonAction U = PeriodicLattice.wilsonAction (edgeFamily D eL U) := by
  rw [BoxTorus.wilsonAction, PeriodicLattice.wilsonAction, ← finsum_comp_equiv eP]
  exact finsum_congr fun p => R.faceEnergy_eq U p
theorem measurable_edgeFamily
    (eL : BoxTorus.DirectedEdge D.L (cutoffInt D) σ ≃ D.PeriodicLink) :
    Measurable (edgeFamily D eL) := by
  have hv : Measurable (fun g : Matrices.ComplexMatrix2.specialUnitary =>
      (g : Matrices.ComplexMatrix2)) := continuous_subtype_val.measurable
  have hi : Measurable (fun g : Matrices.ComplexMatrix2.specialUnitary =>
      ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)) :=
    (continuous_subtype_val.comp continuous_inv).measurable
  refine measurable_pi_lambda _ fun b => ?_
  unfold edgeFamily BoxTorus.edgeVariable
  by_cases h : (eL.symm b).IsForward
  · simp only [dif_pos h]
    exact hv.comp (measurable_pi_apply _)
  · simp only [dif_neg h]
    exact hi.comp (measurable_pi_apply _)
theorem im_fullTrace_eq_zero (V : Matrices.ComplexMatrix2)
    (hV : V ∈ Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace V).im = 0 := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.fullTrace_im_eq_zero_of_mem_specialUnitary <;> assumption
end Facts
theorem cubicPeriodIsPeriodSubgroup (D : ChessboardSetup) : D.CubicPeriodIsPeriodSubgroup := by
  refine ⟨?_, fun μ => ⟨?_, rfl⟩⟩
  · ext x
    have hs : ∀ μ, ChessboardSetup.periodLengths D D.cubicPeriod.mult μ =
        PeriodicLattice.torusSide D.L D.m :=
      D.sideLengths_cubicPeriod
    simp only [SetLike.mem_coe, PeriodSubgroup.subgroup, ChessboardSetup.periodGroup,
      BoxTorus.periods, AddSubgroup.mem_pi, mem_univ, forall_const, mem_range, hs,
      AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro h
      choose k hk using h
      refine ⟨k, funext fun μ => ?_⟩
      rw [← hk μ, zsmul_eq_mul, TestFunctions.latticeTranslate]
      ring
    · rintro ⟨k, rfl⟩ μ
      refine ⟨k μ, ?_⟩
      rw [zsmul_eq_mul, TestFunctions.latticeTranslate]
      ring
  · have h : ((D.cubicPeriod.mult μ : ℤ) : ℝ) * D.mesh = PeriodicLattice.torusSide D.L D.m :=
      D.sideLengths_cubicPeriod μ
    rw [eq_div_iff D.mesh_pos.ne', h]
section Cubic
variable {D : ChessboardSetup} {e : BoxTorus.Space D.cubicPeriod.sideLengths ≃+ D.Torus}
  {eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink}
  {eP : D.cubicPeriod.Face ≃ D.PeriodicPlaquette}
theorem TorusIdentification.projEdge_eq
    (R : TorusIdentification D D.cubicPeriod.sideLengths e eL eP) (b : D.Link) :
    eL (D.cubicPeriod.projEdge b) = D.projLink b := by
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [(R.endpoints _).1]
    exact R.proj_eq _
  · rw [(R.endpoints _).2]
    exact R.proj_eq _
theorem TorusIdentification.liftField_eq
    (R : TorusIdentification D D.cubicPeriod.sideLengths e eL eP)
    (U : D.cubicPeriod.GaugeConfig) (b : D.Link) :
    (D.liftField (D.linkFamily eL U)) b = D.cubicPeriod.liftField U b := by
  have hU : D.linkFamily eL U ∈
      PeriodicLattice.compactGaugeFields D.L D.m (cutoffInt D) := R.bijOn.mapsTo (mem_univ U)
  apply Subtype.ext
  have h : D.liftField (D.linkFamily eL U) = _ :=
    dif_pos hU
  rw [h]
  show D.linkFamily eL U (D.projLink b) = _
  rw [← R.projEdge_eq b]
  simp only [ChessboardSetup.linkFamily, Equiv.symm_apply_apply]
  rfl
theorem TorusIdentification.descend_eq
    (R : TorusIdentification D D.cubicPeriod.sideLengths e eL eP) {W : AmbientSpace → ℂ}
    (hW : ∀ x, ∀ v ∈ D.cubicPeriod.subgroup, W (x + v) = W x) (u : D.cubicPeriod.TorusSpace) :
    D.cubicPeriod.descend W u = D.descend W (e u) := by
  have hW' : ∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      W (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) = W x :=
    fun x k => by
    refine hW x _ ?_
    exact show TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k ∈
        (D.cubicPeriod.subgroup : Set AmbientSpace) from by
      rw [(cubicPeriodIsPeriodSubgroup D).1]
      exact ⟨k, rfl⟩
  obtain ⟨x, rfl⟩ := BoxTorus.projection_surjective _ u
  have h1 := D.cubicPeriod.descend_proj hW x
  have h2 := congrFun (D.descend_comp_proj hW') x
  have h3 := R.proj_eq x
  rw [h3]
  exact h1.trans h2.symm
theorem measurable_sourcedBoltzmannWeight [Finite D.PeriodicPlaquette] (w : D.Torus → ℂ) :
    Measurable (PeriodicLattice.sourcedBoltzmannWeight D.β w :
      (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hb : ∀ b : D.PeriodicLink,
      Continuous fun U : D.PeriodicLink → Matrices.ComplexMatrix2 => U b :=
    fun b => continuous_apply b
  have hv : ∀ p : D.PeriodicPlaquette,
      Continuous fun U : D.PeriodicLink → Matrices.ComplexMatrix2 =>
        PeriodicLattice.plaquetteHolonomy U p := fun p => by
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    exact (hb _).matrix_mul ((hb _).matrix_mul ((hb _).matrix_mul (hb _)))
  have hA : Continuous fun U : D.PeriodicLink → Matrices.ComplexMatrix2 =>
      PeriodicLattice.barycenterWeightedEnergy (fun x => (D.β : ℂ) - w x) U := by
    cases nonempty_fintype D.PeriodicPlaquette
    have e : (fun U : D.PeriodicLink → Matrices.ComplexMatrix2 =>
        PeriodicLattice.barycenterWeightedEnergy (fun x => (D.β : ℂ) - w x) U) =
        fun U => ∑ p : D.PeriodicPlaquette, ((D.β : ℂ) - w p.barycenter) *
          PeriodicLattice.plaquetteEnergy U p :=
      funext fun U => finsum_eq_sum_of_fintype _
    rw [e]
    refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
    unfold PeriodicLattice.plaquetteEnergy
    exact continuous_const.sub (continuous_const.mul (hv p).matrix_trace)
  exact (Complex.continuous_exp.comp hA.neg).measurable
theorem TorusIdentification.weightedPartition_eq
    (R : TorusIdentification D D.cubicPeriod.sideLengths e eL eP) {W : AmbientSpace → ℂ}
    (hW : ∀ x, ∀ v ∈ D.cubicPeriod.subgroup, W (x + v) = W x) :
    D.cubicPeriod.weightedPartition W = D.partitionFunctionOfPeriodic W := by
  have hfin := R.finite_faces
  have : Finite D.PeriodicPlaquette := Finite.of_equiv _ eP
  rw [ChessboardSetup.partitionFunctionOfPeriodic, ChessboardSetup.partitionFunction,
    PeriodicLattice.generatingFunctionOfSource]
  have hmap := R.map_haar
  change _ = ∫ V, PeriodicLattice.sourcedBoltzmannWeight D.β (D.descend W) V
    ∂PeriodicLattice.productHaarMeasure D.L D.m (cutoffInt D)
  rw [← hmap, integral_map (measurable_edgeFamily eL).aemeasurable
    (measurable_sourcedBoltzmannWeight _).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [PeriodicLattice.sourcedBoltzmannWeight, PeriodicLattice.barycenterWeightedEnergy,
    PeriodicLattice.plaquetteWeightedEnergy]
  congr 1
  rw [← finsum_comp_equiv eP, ← finsum_neg_distrib]
  refine finsum_congr fun p => ?_
  have ht : (Matrices.ComplexMatrix2.fullTrace
      (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2)).im = 0 :=
    im_fullTrace_eq_zero _ (BoxTorus.faceHolonomy U p).2
  have hr : (((Matrices.ComplexMatrix2.fullTrace
      (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2)).re : ℝ) : ℂ) =
      Matrices.ComplexMatrix2.fullTrace (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) :=
    Complex.ext rfl (by simpa using ht.symm)
  have hb : D.descend W (eP p).barycenter =
      D.cubicPeriod.descend W (D.cubicPeriod.faceCenter p) := by
    rw [R.descend_eq hW]
    exact congrArg _ (R.map_faceCenter p).symm
  rw [hb, PeriodicLattice.plaquetteEnergy, ← R.holonomy_eq, ← hr]
  simp only [PeriodSubgroup.faceEnergy, BoxTorus.faceEnergy]
  push_cast
  ring
end Cubic
theorem cubicPeriodMatches (hG : EqualSideGrids.Statement) (D : ChessboardSetup) :
    D.CubicPeriodMatches := by
  obtain ⟨e, eL, eP, R⟩ := exists_identification hG D
  exact ⟨cubicPeriodIsPeriodSubgroup D, e, eL, eP,
    ⟨R.isHomeomorph, R.proj_eq, R.gridSubgroup_image, fun u v => R.torusDist_eq u v⟩,
    ⟨R.endpoints, R.forward_iff, R.flip_eq⟩,
    fun p => ⟨R.corner_eq p, R.dir₁_eq p, R.dir₂_eq p, R.image_vertexSet p, R.map_faceCenter p⟩,
    ⟨R.bijOn, R.map_haar⟩,
    ⟨fun U p => ⟨R.holonomy_eq U p, R.faceEnergy_eq U p⟩, fun U => R.wilsonAction_eq U⟩,
    R.projEdge_eq, R.liftField_eq⟩
theorem weightedPartition_cubicPeriod (hG : EqualSideGrids.Statement) (D : ChessboardSetup)
    {W : AmbientSpace → ℂ} (hW : ∀ x, ∀ v ∈ D.cubicPeriod.subgroup, W (x + v) = W x) :
    D.cubicPeriod.weightedPartition W = D.partitionFunctionOfPeriodic W := by
  obtain ⟨e, eL, eP, R⟩ := exists_identification hG D
  exact R.weightedPartition_eq hW
theorem holds (hG : EqualSideGrids.Statement) : ReflectionGridArithmetic.Statement := by
  intro D
  refine ⟨cubicPeriodMatches hG D, latticeSymGroupLaws D, exists_reflectionGrid D, fun g =>
    ⟨ratioAndPeriods g, fun h => ⟨?_, fun k => blockEqUnionCells g h k⟩⟩⟩
  have hn : 2 ≤ g.cellsPerTorusSide := two_le_cellsPerTorusSide g
  refine ⟨q_le_m g h, cellsAcross_eq g h, even_cellsPerTorusSide g, hn,
    boxPeriods_eq_cubicPeriod g h hn, fun W _ hW => ?_⟩
  rw [boxPeriods_eq_cubicPeriod g h hn]
  exact weightedPartition_cubicPeriod hG D hW
end ReflectionGridArithmetic
end YangMills.Construction.ChessboardTori
end
