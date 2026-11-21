import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.MirrorGridsOfEverySide.FacePlanesAreLinkMirrorsAtEveryMirrorGridProof
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfToriProof
import YangMills.Construction.SourcesAndGluing.GridsAndTheirGroups
import YangMills.Construction.SourcesAndGluing.LatticeIsometries
import YangMills.Construction.SourcesAndGluing.PropertiesOfLatticeSimilaritiesForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open Set TorusLifts TorusMetric
open InfiniteLattice (AmbientSpace)
namespace CubicGridsAndReflectionGroups
section CubesAndPeriods
variable {D : GluingSetup}
theorem L_pos_real (D : GluingSetup) : (0 : ℝ) < D.L := by
  linarith [D.one_lt_L]
theorem scaleExponent_bounds (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    -((D.K : ℕ) : ℤ) ≤ j ∧ j ≤ ((D.m : ℕ) : ℤ) :=
  (D.isGridScale_zpow_iff j).1 (hj ▸ g.isGridScale)
theorem edge_pos (g : CubicGrid D) : 0 < g.edge := lt_of_lt_of_le D.mesh_pos g.isGridScale.2.1
theorem edge_div_mesh (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    g.edge / D.mesh = (D.L : ℝ) ^ (((D.K : ℕ) : ℤ) + j) := by
  have hL := (L_pos_real D).ne'
  have hm : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  rw [hj, hm, ← zpow_sub₀ hL]
  congr 1
  ring
theorem exists_nat_edge_div_mesh (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    ∃ N : ℕ, 0 < N ∧ g.edge / D.mesh = N := by
  have hb := scaleExponent_bounds g j hj
  have hLpos : 0 < D.L := by exact_mod_cast L_pos_real D
  refine ⟨D.L ^ (((D.K : ℕ) : ℤ) + j).toNat, pow_pos hLpos _, ?_⟩
  rw [edge_div_mesh g j hj]
  push_cast
  rw [← zpow_natCast]
  congr 1
  omega
theorem cellCount_eq_two_mul_zpow (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    D.cellCount g.edge = 2 * (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - j) := by
  have hL := (L_pos_real D).ne'
  have hs : D.side = 2 * (D.L : ℝ) ^ ((D.m : ℕ) : ℤ) := by
    simp [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  rw [GluingSetup.cellCount, hs, hj, mul_div_assoc, ← zpow_sub₀ hL]
theorem cubesPerSide_eq (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    g.cubesPerSide = 2 * D.L ^ (((D.m : ℕ) : ℤ) - j).toNat := by
  have hb := scaleExponent_bounds g j hj
  have h : D.cellCount g.edge = ((2 * D.L ^ (((D.m : ℕ) : ℤ) - j).toNat : ℕ) : ℝ) := by
    rw [cellCount_eq_two_mul_zpow g j hj]
    push_cast
    rw [← zpow_natCast]
    congr 2
    omega
  rw [CubicGrid.cubesPerSide, h, Nat.floor_natCast]
theorem cubesPerSide_cast (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    (g.cubesPerSide : ℝ) = D.cellCount g.edge := by
  rw [cubesPerSide_eq g j hj, cellCount_eq_two_mul_zpow g j hj]
  have hb := scaleExponent_bounds g j hj
  push_cast
  rw [← zpow_natCast]
  congr 2
  omega
theorem torusSide_eq_cubesPerSide_mul (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    PeriodicLattice.torusSide D.L D.m = (g.cubesPerSide : ℝ) * g.edge := by
  rw [cubesPerSide_cast g j hj, GluingSetup.cellCount, div_mul_cancel₀ _ (edge_pos g).ne']
  rfl
theorem cubesPerSide_pos (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    0 < g.cubesPerSide := by
  have hLpos : 0 < D.L := by exact_mod_cast L_pos_real D
  rw [cubesPerSide_eq g j hj]
  positivity
theorem wall_disjoint_gridPoints (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    ∀ P ∈ g.walls, Disjoint P (D.gridPoints : Set AmbientSpace) := by
  rintro _ ⟨⟨μ, n⟩, rfl⟩
  obtain ⟨N, -, hN⟩ := exists_nat_edge_div_mesh g j hj
  have hc : g.edge = N * D.mesh := by
    rw [← hN, div_mul_cancel₀ _ D.mesh_pos.ne']
  rw [Set.disjoint_left]
  rintro x hx ⟨n', hn'⟩
  have hx' : x μ = g.origin μ + n * g.edge := hx
  apply g.origin_ne μ (n' μ - n * N)
  have := hn' μ
  push_cast
  rw [hc] at hx'
  linarith [hx', this, mul_comm D.mesh ((n' μ : ℝ) - n * N)]
theorem image_cube_add_translate (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j)
    (t k : Fin 4 → ℤ) :
    (fun x => x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) '' g.cube k =
      g.cube (k + (g.cubesPerSide : ℤ) • t) := by
  have hkey : ∀ (y : AmbientSpace) (μ : Fin 4),
      (y + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) μ -
        (g.origin μ + g.edge * (((k + (g.cubesPerSide : ℤ) • t) μ : ℤ) : ℝ)) =
      y μ - (g.origin μ + g.edge * (k μ : ℝ)) := by
    intro y μ
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, torusSide_eq_cubesPerSide_mul g j hj,
      Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ μ
    rw [hkey]
    exact hy μ
  · intro hx
    refine ⟨x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t,
      fun μ => ?_, by simp⟩
    have := hkey (x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) μ
    rw [sub_add_cancel] at this
    rw [← this]
    exact hx μ
theorem image_wall_add_translate (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j)
    (t : Fin 4 → ℤ) (μ : Fin 4) (n : ℤ) :
    (fun x => x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) '' g.wall μ n =
      g.wall μ (n + (g.cubesPerSide : ℤ) * t μ) := by
  have hkey : ∀ y : AmbientSpace,
      (y + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) μ =
        y μ + (g.cubesPerSide : ℝ) * (t μ : ℝ) * g.edge := by
    intro y
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, torusSide_eq_cubesPerSide_mul g j hj]
    ring
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y μ = g.origin μ + n * g.edge := hy
    change (y + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t) μ = _
    rw [hkey, hy']
    push_cast
    ring
  · intro hx
    have hx' : x μ = g.origin μ + ((n + (g.cubesPerSide : ℤ) * t μ : ℤ) : ℝ) * g.edge := hx
    refine ⟨x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t, ?_, by simp⟩
    have := hkey (x - TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t)
    rw [sub_add_cancel] at this
    change _ = _
    push_cast at hx'
    linarith
theorem image_walls_add_translate (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j)
    (t : Fin 4 → ℤ) :
    image (image fun x => x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t)
      g.walls = g.walls := by
  ext P
  constructor
  · rintro ⟨_, ⟨⟨μ, n⟩, rfl⟩, rfl⟩
    exact ⟨⟨μ, n + (g.cubesPerSide : ℤ) * t μ⟩, (image_wall_add_translate g j hj t μ n).symm⟩
  · rintro ⟨⟨μ, n⟩, rfl⟩
    refine ⟨_, ⟨⟨μ, n - (g.cubesPerSide : ℤ) * t μ⟩, rfl⟩, ?_⟩
    change _ '' g.wall μ _ = g.wall μ n
    rw [image_wall_add_translate g j hj t μ]
    congr 1
    ring
theorem torusCube_eq_iff (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) (k k' : Fin 4 → ℤ) :
    g.torusCube k = g.torusCube k' ↔ ∃ t : Fin 4 → ℤ, k - k' = (g.cubesPerSide : ℤ) • t := by
  have hc := edge_pos g
  constructor
  · intro h
    have hz : g.cubeCenter k ∈ g.cube k := by
      intro μ
      have : g.cubeCenter k μ - (g.origin μ + g.edge * (k μ : ℝ)) = g.edge / 2 := by
        simp only [CubicGrid.cubeCenter]
        ring
      rw [this]
      constructor <;> linarith
    have hz' : D.proj (g.cubeCenter k) ∈ g.torusCube k' := h ▸ ⟨_, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hz'
    obtain ⟨t, ht⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
      (ℓ := PeriodicLattice.torusSide D.L D.m) (v := g.cubeCenter k) (w := y) hyz.symm
    refine ⟨t, funext fun μ => ?_⟩
    obtain ⟨h0, h1⟩ := hy μ
    have hzμ := congrFun ht μ
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, torusSide_eq_cubesPerSide_mul g j hj,
      CubicGrid.cubeCenter] at hzμ
    have hyμ : y μ = g.origin μ + g.edge * ((k μ : ℝ) + 1 / 2) -
        (g.cubesPerSide : ℝ) * g.edge * (t μ : ℝ) := by linarith
    rw [hyμ] at h0 h1
    set d : ℤ := k μ - k' μ - (g.cubesPerSide : ℤ) * t μ with hd
    have hdr : (d : ℝ) = (k μ : ℝ) - k' μ - (g.cubesPerSide : ℝ) * t μ := by
      rw [hd]
      push_cast
      ring
    have e0 : 0 ≤ g.edge * ((d : ℝ) + 1 / 2) := by rw [hdr]; nlinarith
    have e1 : g.edge * ((d : ℝ) + 1 / 2) ≤ g.edge * 1 := by rw [hdr]; nlinarith
    have f0 : 0 ≤ (d : ℝ) + 1 / 2 := nonneg_of_mul_nonneg_right e0 hc
    have f1 : (d : ℝ) + 1 / 2 ≤ 1 := le_of_mul_le_mul_left e1 hc
    have g0 : (-1 : ℝ) < d := by linarith
    have g1 : (d : ℝ) < 1 := by linarith
    have g0' : (-1 : ℤ) < d := by exact_mod_cast g0
    have g1' : d < 1 := by exact_mod_cast g1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    omega
  · rintro ⟨t, ht⟩
    have hk : k = k' + (g.cubesPerSide : ℤ) • t := by rw [← ht]; abel
    rw [hk]
    change D.proj '' _ = D.proj '' _
    rw [← image_cube_add_translate g j hj t k', image_image]
    refine image_congr fun x _ => ?_
    exact TestFunctions.torusProj_add_latticeTranslate _ x t
theorem exists_sub_eq_smul_iff_zmod (N : ℕ) (k k' : Fin 4 → ℤ) :
    (∃ t : Fin 4 → ℤ, k - k' = (N : ℤ) • t) ↔ ∀ μ, (k μ : ZMod N) = (k' μ : ZMod N) := by
  constructor
  · rintro ⟨t, ht⟩ μ
    have h := congrFun ht μ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    have : k μ = k' μ + (N : ℤ) * t μ := by omega
    rw [this]
    simp
  · intro h
    have h' : ∀ μ, (N : ℤ) ∣ k μ - k' μ := fun μ =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h μ).symm
    choose t ht using h'
    exact ⟨t, funext fun μ => by simp [ht μ]⟩
theorem exists_equiv_torusCubes (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    ∃ e : (Fin 4 → ZMod g.cubesPerSide) ≃ range g.torusCube,
      ∀ k : Fin 4 → ℤ, (e fun μ => (k μ : ZMod g.cubesPerSide) : Set D.Torus) = g.torusCube k := by
  have : NeZero g.cubesPerSide := ⟨(cubesPerSide_pos g j hj).ne'⟩
  have hcls : ∀ k k' : Fin 4 → ℤ, g.torusCube k = g.torusCube k' ↔
      ∀ μ, (k μ : ZMod g.cubesPerSide) = (k' μ : ZMod g.cubesPerSide) := fun k k' =>
    (torusCube_eq_iff g j hj k k').trans (exists_sub_eq_smul_iff_zmod _ k k')
  let rep : (Fin 4 → ZMod g.cubesPerSide) → Fin 4 → ℤ := fun z μ => ((z μ).cast : ℤ)
  have hrep : ∀ (z : Fin 4 → ZMod g.cubesPerSide) μ, ((rep z μ : ℤ) : ZMod g.cubesPerSide) = z μ :=
    fun z μ => ZMod.intCast_cast _ |>.trans (by simp)
  let f : (Fin 4 → ZMod g.cubesPerSide) → range g.torusCube :=
    fun z => ⟨g.torusCube (rep z), _, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' h
      have h' := (hcls _ _).1 (congrArg Subtype.val h)
      funext μ
      rw [← hrep z μ, ← hrep z' μ, h' μ]
    · rintro ⟨_, k, rfl⟩
      refine ⟨fun μ => (k μ : ZMod g.cubesPerSide), Subtype.ext ?_⟩
      exact (hcls _ _).2 fun μ => hrep (fun μ => (k μ : ZMod g.cubesPerSide)) μ
  refine ⟨Equiv.ofBijective f hf, fun k => ?_⟩
  exact (hcls _ _).2 fun μ => hrep (fun μ => (k μ : ZMod g.cubesPerSide)) μ
theorem ncard_range_torusCube (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    (range g.torusCube).ncard = g.cubesPerSide ^ 4 := by
  have : NeZero g.cubesPerSide := ⟨(cubesPerSide_pos g j hj).ne'⟩
  obtain ⟨e, -⟩ := exists_equiv_torusCubes g j hj
  rw [← _root_.Nat.card_coe_set_eq, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [ZMod.card]
theorem cubesAndPeriods (g : CubicGrid D) (j : ℤ) (hj : g.edge = (D.L : ℝ) ^ j) :
    g.CubesAndPeriods j := by
  have hN := cubesPerSide_eq g j hj
  refine ⟨edge_div_mesh g j hj, exists_nat_edge_div_mesh g j hj, cellCount_eq_two_mul_zpow g j hj,
    cubesPerSide_cast g j hj, cubesPerSide_pos g j hj, ?_, wall_disjoint_gridPoints g j hj,
    fun t k => image_cube_add_translate g j hj t k, image_walls_add_translate g j hj,
    torusCube_eq_iff g j hj, exists_equiv_torusCubes g j hj, ncard_range_torusCube g j hj⟩
  rw [hN]
  exact even_two_mul _
end CubesAndPeriods
section WallsCubesAndProjection
theorem exists_edge_eq_mesh_mul {D : GluingSetup} (g : CubicGrid D) :
    ∃ N : ℤ, g.edge = D.mesh * (N : ℝ) := by
  obtain ⟨⟨j, hj⟩, h1, -⟩ := g.isGridScale
  have hL := D.one_lt_L
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have hm : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  have hk : -((D.K : ℕ) : ℤ) ≤ j := by
    rw [hm, hj] at h1
    exact (zpow_le_zpow_iff_right₀ hL).1 h1
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j + ((D.K : ℕ) : ℤ))
  refine ⟨((D.L : ℕ) : ℤ) ^ n, ?_⟩
  rw [hj, hm]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ hL0]
  congr 1
  omega
theorem int_mul_ne_mul_half_odd {a : ℝ} (ha : 0 < a) (n i : ℤ) :
    (n : ℝ) * a ≠ a * ((i : ℝ) + 1 / 2) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallsBisectLinks.intMul_ne_halfInt <;> assumption
theorem exists_terminal_sub_initial {a : ℝ} (b : InfiniteLattice.Link a) :
    ∃ ν : Fin 4, (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = Pi.single ν a ∨
      (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = -(Pi.single ν a) := by
  obtain ⟨ν, h | h⟩ := b.isAdjacent
  · exact ⟨ν, Or.inl (congrArg Subtype.val h)⟩
  · exact ⟨ν, Or.inr (congrArg Subtype.val h)⟩
theorem smul_stdBasis (a : ℝ) (μ : Fin 4) : a • stdBasis μ = Pi.single μ a := by apply _root_.YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfTori.smul_stdBasis <;> assumption
theorem convexComb_eq_midpoint {a : ℝ} (ha : 0 < a) (μ : Fin 4) (i : ℤ) {x y : AmbientSpace} (n : ℤ)
    (hx : x μ = (n : ℝ) * a) (hy : y - x = Pi.single μ a ∨ y - x = -(Pi.single μ a))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hp : (s • x + t • y) μ = a * ((i : ℝ) + 1 / 2)) :
    s • x + t • y = midpoint ℝ x y := by
  have hhalf : t = 1 / 2 := by
    have hs' : s = 1 - t := by linarith
    rcases hy with hy | hy
    · have hyμ : y μ = x μ + a := by
        have := congrFun hy μ
        simp at this
        linarith
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp
      rw [hyμ, hx, hs'] at hp
      have h1 : (n : ℝ) + t = (i : ℝ) + 1 / 2 := by
        have : a * ((n : ℝ) + t) = a * ((i : ℝ) + 1 / 2) := by linarith
        exact mul_left_cancel₀ ha.ne' this
      have h2 : ((-1 : ℤ) : ℝ) < ((i - n : ℤ) : ℝ) := by
        push_cast
        linarith
      have h3 : ((i - n : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have h4 : i - n = 0 := by
        have h5 : (-1 : ℤ) < i - n := by exact_mod_cast h2
        have h6 : i - n < (1 : ℤ) := by exact_mod_cast h3
        omega
      have h7 : (i : ℝ) = n := by exact_mod_cast (by omega : i = n)
      linarith
    · have hyμ : y μ = x μ - a := by
        have := congrFun hy μ
        simp at this
        linarith
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp
      rw [hyμ, hx, hs'] at hp
      have h1 : (n : ℝ) - t = (i : ℝ) + 1 / 2 := by
        have : a * ((n : ℝ) - t) = a * ((i : ℝ) + 1 / 2) := by linarith
        exact mul_left_cancel₀ ha.ne' this
      have h2 : ((0 : ℤ) : ℝ) < ((n - i : ℤ) : ℝ) := by
        push_cast
        linarith
      have h3 : ((n - i : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
        push_cast
        linarith
      have h4 : n - i = 1 := by
        have h5 : (0 : ℤ) < n - i := by exact_mod_cast h2
        have h6 : n - i < (2 : ℤ) := by exact_mod_cast h3
        omega
      have h7 : (n : ℝ) = i + 1 := by exact_mod_cast (by omega : n = i + 1)
      linarith
  have hs2 : s = 1 / 2 := by linarith
  rw [midpoint_eq_smul_add, hs2, hhalf, smul_add]
  simp
theorem link_axis_of_meets_plane {D : GluingSetup} (μ : Fin 4) (i : ℤ) (b : InfiniteLattice.Link D.mesh)
    (h : (segment ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace) ∩
      coordPlane μ (D.mesh * ((i : ℝ) + 1 / 2))).Nonempty) :
    (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = Pi.single μ D.mesh ∨
      (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = -(Pi.single μ D.mesh) := by
  obtain ⟨ν, hν⟩ := exists_terminal_sub_initial b
  by_cases hνμ : ν = μ
  · subst hνμ
    exact hν
  exfalso
  obtain ⟨p, ⟨s, t, hs, ht, hst, rfl⟩, hp⟩ := h
  obtain ⟨n, hn⟩ := b.initial.2
  have hμ : (b.terminal : AmbientSpace) μ = (b.initial : AmbientSpace) μ := by
    have hne : μ ≠ ν := fun e => hνμ e.symm
    rcases hν with hν | hν
    · have := congrFun hν μ
      simp [Pi.single_eq_of_ne hne] at this
      linarith
    · have := congrFun hν μ
      simp [Pi.single_eq_of_ne hne] at this
      linarith
  have hp' : s * (b.initial : AmbientSpace) μ + t * (b.terminal : AmbientSpace) μ =
      D.mesh * ((i : ℝ) + 1 / 2) := by
    simpa [coordPlane] using hp
  rw [hμ, ← add_mul, hst, one_mul, hn μ] at hp'
  exact int_mul_ne_mul_half_odd D.mesh_pos _ _ hp'
theorem coordPlaneReflection_apply_self (μ : Fin 4) (c : ℝ) (x : AmbientSpace) :
    coordPlaneReflection μ c x μ = 2 * c - x μ := by
  simp [coordPlaneReflection, stdBasis]
  ring
theorem coordPlaneReflection_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (c : ℝ) (x : AmbientSpace) :
    coordPlaneReflection μ c x ν = x ν := by
  simp [coordPlaneReflection, stdBasis, Pi.single_eq_of_ne h]
theorem coordPlaneReflection_involutive (μ : Fin 4) (c : ℝ) :
    Function.Involutive (coordPlaneReflection μ c) := by
  intro x
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [coordPlaneReflection_apply_self, coordPlaneReflection_apply_self]
    ring
  · rw [coordPlaneReflection_apply_of_ne h, coordPlaneReflection_apply_of_ne h]
theorem disjoint_and_reflect_gridPoints_iff (D : GluingSetup) (μ : Fin 4) (c : ℝ) :
    (Disjoint (coordPlane μ c) (D.gridPoints : Set AmbientSpace) ∧
      coordPlaneReflection μ c '' (D.gridPoints : Set AmbientSpace) =
        (D.gridPoints : Set AmbientSpace)) ↔
      c ∈ D.halfIntegerMeshPoints := by
  have ha := D.mesh_pos
  constructor
  · rintro ⟨hd, hr⟩
    have h0 : coordPlaneReflection μ c 0 ∈ (D.gridPoints : Set AmbientSpace) := by
      rw [← hr]
      exact ⟨0, D.gridPoints.zero_mem, rfl⟩
    obtain ⟨n, hn⟩ := h0
    have h2c : 2 * c = (n μ : ℝ) * D.mesh := by
      have := hn μ
      rw [coordPlaneReflection_apply_self] at this
      simpa using this
    rcases Int.even_or_odd' (n μ) with ⟨i, hi | hi⟩
    · exfalso
      have hc : c = (i : ℝ) * D.mesh := by
        rw [hi] at h2c
        push_cast at h2c
        linarith
      have hd' := Set.disjoint_left.1 hd
      refine hd' (a := Pi.single μ ((i : ℝ) * D.mesh)) ?_ ?_
      · simp [coordPlane, hc]
      · refine ⟨Pi.single μ i, fun ν => ?_⟩
        by_cases h : ν = μ
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
    · refine ⟨i, ?_⟩
      rw [hi] at h2c
      push_cast at h2c
      linarith
  · rintro ⟨i, rfl⟩
    have hsub : ∀ x ∈ (D.gridPoints : Set AmbientSpace),
        coordPlaneReflection μ (D.mesh * ((i : ℝ) + 1 / 2)) x ∈
          (D.gridPoints : Set AmbientSpace) := by
      rintro x ⟨n, hn⟩
      refine ⟨Function.update n μ (2 * i + 1 - n μ), fun ν => ?_⟩
      by_cases h : ν = μ
      · subst h
        rw [coordPlaneReflection_apply_self, hn ν]
        simp
        ring
      · rw [coordPlaneReflection_apply_of_ne h, hn ν, Function.update_of_ne h]
    refine ⟨Set.disjoint_left.2 ?_, ?_⟩
    · rintro x hx ⟨n, hn⟩
      have h1 : x μ = D.mesh * ((i : ℝ) + 1 / 2) := hx
      rw [hn μ] at h1
      exact int_mul_ne_mul_half_odd ha _ _ h1
    · apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hsub x hx
      · intro x hx
        exact ⟨_, hsub x hx, coordPlaneReflection_involutive μ _ x⟩
theorem mirrorWallsAndLinks (D : GluingSetup) : D.MirrorWallsAndLinks := by
  refine ⟨?_, ?_, disjoint_and_reflect_gridPoints_iff D⟩
  · rintro g hg _ ⟨⟨μ, n⟩, rfl⟩
    obtain ⟨i, hi⟩ := hg μ
    obtain ⟨N, hN⟩ := exists_edge_eq_mesh_mul g
    refine ⟨μ, g.origin μ + n * g.edge, ⟨i + n * N, ?_⟩, rfl⟩
    rw [hi, hN]
    push_cast
    ring
  · rintro μ _ ⟨i, rfl⟩ b hne
    have hl := link_axis_of_meets_plane μ i b hne
    refine ⟨?_, ?_⟩
    · rw [smul_stdBasis]
      exact hl
    · have hsub : segment ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace) ∩
          coordPlane μ (D.mesh * ((i : ℝ) + 1 / 2)) ⊆
          {midpoint ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace)} := by
        rintro p ⟨⟨s, t, hs, ht, hst, rfl⟩, hp⟩
        obtain ⟨n, hn⟩ := b.initial.2
        exact convexComb_eq_midpoint D.mesh_pos μ i (n μ) (hn μ) hl hs ht hst hp
      exact hne.subset_singleton_iff.1 hsub
theorem origin_floor_bounds {D : GluingSetup} (g : CubicGrid D) (μ : Fin 4) :
    D.mesh * (⌊g.origin μ / D.mesh⌋ : ℝ) < g.origin μ ∧
      g.origin μ < D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1) := by
  have ha := D.mesh_pos
  have h1 := Int.floor_le (g.origin μ / D.mesh)
  have h2 := Int.lt_floor_add_one (g.origin μ / D.mesh)
  have h3 : D.mesh * (g.origin μ / D.mesh) = g.origin μ := by field_simp
  constructor
  · refine lt_of_le_of_ne ?_ (fun e => g.origin_ne μ _ e.symm)
    calc D.mesh * (⌊g.origin μ / D.mesh⌋ : ℝ) ≤ D.mesh * (g.origin μ / D.mesh) :=
          mul_le_mul_of_nonneg_left h1 ha.le
      _ = g.origin μ := h3
  · calc g.origin μ = D.mesh * (g.origin μ / D.mesh) := h3.symm
      _ < D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left h2 ha
theorem wall_between_lattice_planes {D : GluingSetup} (g : CubicGrid D) (μ : Fin 4) (n : ℤ) :
    ∃ i : ℤ, D.mesh * (i : ℝ) < g.origin μ + (n : ℝ) * g.edge ∧
      g.origin μ + (n : ℝ) * g.edge < D.mesh * ((i : ℝ) + 1) ∧
      g.mirrorOrigin μ + (n : ℝ) * g.edge = D.mesh * ((i : ℝ) + 1 / 2) := by
  obtain ⟨N, hN⟩ := exists_edge_eq_mesh_mul g
  obtain ⟨h1, h2⟩ := origin_floor_bounds g μ
  have ho : g.mirrorOrigin μ = D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1 / 2) := rfl
  refine ⟨⌊g.origin μ / D.mesh⌋ + n * N, ?_, ?_, ?_⟩
  · push_cast
    rw [hN]
    linarith
  · push_cast
    rw [hN]
    linarith
  · push_cast
    rw [hN, ho]
    ring
theorem int_mul_compare_in_gap {a : ℝ} (ha : 0 < a) {i n : ℤ} {w : ℝ} (h1 : a * (i : ℝ) < w)
    (h2 : w < a * ((i : ℝ) + 1)) :
    (w < (n : ℝ) * a ↔ i + 1 ≤ n) ∧ ((n : ℝ) * a < w ↔ n ≤ i) := by
  constructor
  · constructor
    · intro h
      have h3 : a * (i : ℝ) < a * (n : ℝ) := by linarith
      have h4 : (i : ℝ) < n := lt_of_mul_lt_mul_left h3 ha.le
      have h5 : i < n := by exact_mod_cast h4
      omega
    · intro h
      have h3 : ((i + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast h
      push_cast at h3
      have h4 : a * ((i : ℝ) + 1) ≤ a * (n : ℝ) := mul_le_mul_of_nonneg_left h3 ha.le
      linarith
  · constructor
    · intro h
      have h3 : a * (n : ℝ) < a * ((i : ℝ) + 1) := by linarith
      have h4 : (n : ℝ) < (i : ℝ) + 1 := lt_of_mul_lt_mul_left h3 ha.le
      have h5 : (n : ℝ) < ((i + 1 : ℤ) : ℝ) := by
        push_cast
        exact h4
      have h6 : n < i + 1 := by exact_mod_cast h5
      omega
    · intro h
      have h3 : (n : ℝ) ≤ i := by exact_mod_cast h
      have h4 : a * (n : ℝ) ≤ a * (i : ℝ) := mul_le_mul_of_nonneg_left h3 ha.le
      linarith
theorem grid_coord_mem_Ioo_iff {D : GluingSetup} (g : CubicGrid D) (μ : Fin 4) (k n : ℤ) :
    (n : ℝ) * D.mesh - (g.origin μ + g.edge * (k : ℝ)) ∈ Ioo 0 g.edge ↔
      (n : ℝ) * D.mesh - (g.mirrorOrigin μ + g.edge * (k : ℝ)) ∈ Ioo 0 g.edge := by
  have ha := D.mesh_pos
  obtain ⟨i, h1, h2, h3⟩ := wall_between_lattice_planes g μ k
  obtain ⟨i', h1', h2', h3'⟩ := wall_between_lattice_planes g μ (k + 1)
  have h4 : D.mesh * (i : ℝ) < g.mirrorOrigin μ + (k : ℝ) * g.edge := by
    rw [h3]
    linarith
  have h5 : g.mirrorOrigin μ + (k : ℝ) * g.edge < D.mesh * ((i : ℝ) + 1) := by
    rw [h3]
    linarith
  have h4' : D.mesh * (i' : ℝ) < g.mirrorOrigin μ + ((k + 1 : ℤ) : ℝ) * g.edge := by
    rw [h3']
    linarith
  have h5' : g.mirrorOrigin μ + ((k + 1 : ℤ) : ℝ) * g.edge < D.mesh * ((i' : ℝ) + 1) := by
    rw [h3']
    linarith
  have c1 := (int_mul_compare_in_gap (n := n) ha h1 h2).1
  have c2 := (int_mul_compare_in_gap (n := n) ha h4 h5).1
  have c3 := (int_mul_compare_in_gap (n := n) ha h1' h2').2
  have c4 := (int_mul_compare_in_gap (n := n) ha h4' h5').2
  push_cast at c3 c4
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨?_, ?_⟩
    · have : g.origin μ + (k : ℝ) * g.edge < (n : ℝ) * D.mesh := by linarith
      have := c2.2 (c1.1 this)
      linarith
    · have : (n : ℝ) * D.mesh < g.origin μ + ((k : ℝ) + 1) * g.edge := by linarith
      have := c4.2 (c3.1 this)
      linarith
  · rintro ⟨hl, hu⟩
    refine ⟨?_, ?_⟩
    · have : g.mirrorOrigin μ + (k : ℝ) * g.edge < (n : ℝ) * D.mesh := by linarith
      have := c1.2 (c2.1 this)
      linarith
    · have : (n : ℝ) * D.mesh < g.mirrorOrigin μ + ((k : ℝ) + 1) * g.edge := by linarith
      have := c3.2 (c4.1 this)
      linarith
theorem mem_openCube_iff_mirror {D : GluingSetup} (g : CubicGrid D) (k : Fin 4 → ℤ) (x : AmbientSpace)
    (hx : x ∈ (D.gridPoints : Set AmbientSpace)) :
    x ∈ g.openCube k ↔ x ∈ g.toMirror.openCube k := by
  obtain ⟨n, hn⟩ := hx
  change (∀ μ, x μ - (g.origin μ + g.edge * (k μ : ℝ)) ∈ Ioo 0 g.edge) ↔
    ∀ μ, x μ - (g.mirrorOrigin μ + g.edge * (k μ : ℝ)) ∈ Ioo 0 g.edge
  refine forall_congr' fun μ => ?_
  rw [hn μ]
  exact grid_coord_mem_Ioo_iff g μ (k μ) (n μ)
theorem euclidNorm_cubeCenter_sub_lt {D : GluingSetup} (g : CubicGrid D) (k : Fin 4 → ℤ) :
    euclidNorm (g.cubeCenter k - g.toMirror.cubeCenter k) < D.mesh := by
  have ha := D.mesh_pos
  have hc : ∀ μ, (g.cubeCenter k - g.toMirror.cubeCenter k) μ = g.origin μ - g.mirrorOrigin μ := by
    intro μ
    change g.origin μ + g.edge * ((k μ : ℝ) + 1 / 2) -
      (g.mirrorOrigin μ + g.edge * ((k μ : ℝ) + 1 / 2)) = _
    ring
  have hsq : ∀ μ, (g.origin μ - g.mirrorOrigin μ) ^ 2 < D.mesh ^ 2 / 4 := by
    intro μ
    obtain ⟨h1, h2⟩ := origin_floor_bounds g μ
    have ho : g.mirrorOrigin μ = D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1 / 2) := rfl
    have h3 : -(D.mesh / 2) < g.origin μ - g.mirrorOrigin μ := by
      rw [ho]
      linarith
    have h4 : g.origin μ - g.mirrorOrigin μ < D.mesh / 2 := by
      rw [ho]
      linarith
    nlinarith
  change Real.sqrt (∑ μ, (g.cubeCenter k - g.toMirror.cubeCenter k) μ ^ 2) < D.mesh
  rw [Real.sqrt_lt' ha]
  simp only [hc, Fin.sum_univ_four]
  linarith [hsq 0, hsq 1, hsq 2, hsq 3]
theorem mirrorWallsAndCubes {D : GluingSetup} (g : CubicGrid D) : g.MirrorWallsAndCubes := by
  refine ⟨wall_between_lattice_planes g, fun k x hx => mem_openCube_iff_mirror g k x hx,
    euclidNorm_cubeCenter_sub_lt g, fun k => ?_⟩
  have hl : (InfiniteLattice.linksWithin (g.openCube k) : Set (InfiniteLattice.Link D.mesh)) =
      InfiniteLattice.linksWithin (g.toMirror.openCube k) := by
    ext b
    change ((b.initial : AmbientSpace) ∈ g.openCube k ∧ (b.terminal : AmbientSpace) ∈ g.openCube k) ↔
      ((b.initial : AmbientSpace) ∈ g.toMirror.openCube k ∧
        (b.terminal : AmbientSpace) ∈ g.toMirror.openCube k)
    rw [mem_openCube_iff_mirror g k _ b.initial.2, mem_openCube_iff_mirror g k _ b.terminal.2]
  simp only [CubicGrid.cubeAlgebra, hl]
theorem projOnLatticeAndOpenCubes (hLifts : TorusLifts.LiftsAndDescendedMaps.Statement)
    {D : GluingSetup} (g : CubicGrid D) : g.ProjOnLatticeAndOpenCubes := by
  obtain ⟨h1, -, h3, -, h5, h6⟩ := (hLifts D.toStandingParameters).2.2.2.2.2
  refine ⟨h1, h3, h5, h6, fun k x hx y hy hxy => ?_⟩
  obtain ⟨t, ht⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (show torusProj (PeriodicLattice.torusSide D.L D.m) x =
      torusProj (PeriodicLattice.torusSide D.L D.m) y from hxy)
  have hs := edge_pos g
  have hle : g.edge ≤ PeriodicLattice.torusSide D.L D.m / 2 := g.isGridScale.2.2
  funext μ
  have hxμ : x μ = y μ + PeriodicLattice.torusSide D.L D.m * (t μ : ℝ) := by
    simpa [TestFunctions.latticeTranslate] using congrFun ht μ
  have ht0 : t μ = 0 := by
    by_contra hne
    have h1' : (1 : ℝ) ≤ |(t μ : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hx1 := hx μ
    have hy1 := hy μ
    have habs : |x μ - y μ| < g.edge := abs_lt.2
      ⟨by linarith [hx1.1, hx1.2, hy1.1, hy1.2], by linarith [hx1.1, hx1.2, hy1.1, hy1.2]⟩
    have hpos : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
    have h2 : |x μ - y μ| = PeriodicLattice.torusSide D.L D.m * |(t μ : ℝ)| := by
      rw [hxμ, add_sub_cancel_left, abs_mul, abs_of_pos hpos]
    nlinarith
  rw [hxμ, ht0]
  simp
end WallsCubesAndProjection
section ReflectionsAsASet
variable {D : GluingSetup} (g : CubicGrid D)
theorem affineReflection_add_latticeTranslate (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (ℓ : ℝ)
    (x : AmbientSpace) (k : Fin 4 → ℤ) :
    g.affineReflection ε n (x + TestFunctions.latticeTranslate ℓ k) =
      g.affineReflection ε n x +
        TestFunctions.latticeTranslate ℓ (fun μ => ((ε μ : ℤˣ) : ℤ) * k μ) := by
  funext μ
  simp only [CubicGrid.affineReflection, Pi.add_apply, TestFunctions.latticeTranslate, Int.cast_mul]
  ring
theorem descendedReflection_torusProj (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (x : AmbientSpace) :
    g.descendedReflection ε n (torusProj (PeriodicLattice.torusSide D.L D.m) x) =
      torusProj (PeriodicLattice.torusSide D.L D.m) (g.affineReflection ε n x) := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (TestFunctions.torusProj_liftPoint (torusProj (PeriodicLattice.torusSide D.L D.m) x))
  rw [CubicGrid.descendedReflection, descendedMap, hk, affineReflection_add_latticeTranslate,
    TestFunctions.torusProj_add_latticeTranslate]
theorem descends_affineReflection (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) :
    Descends (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m)
      (g.affineReflection ε n) (g.descendedReflection ε n) :=
  funext fun x => descendedReflection_torusProj g ε n x
theorem affineReflection_comp (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ) (x : AmbientSpace) :
    g.affineReflection ε n (g.affineReflection ε' n' x) =
      g.affineReflection (ε * ε') (n + fun μ => ((ε μ : ℤˣ) : ℤ) * n' μ) x := by
  funext μ
  simp only [CubicGrid.affineReflection, Pi.mul_apply, Pi.add_apply, Units.val_mul, Int.cast_mul,
    Int.cast_add]
  ring
theorem affineReflection_one_zero (x : AmbientSpace) : g.affineReflection 1 0 x = x := by
  funext μ
  simp [CubicGrid.affineReflection]
theorem unit_cast_mul_self (e : ℤˣ) : ((e : ℤ) : ℝ) * ((e : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or e with h | h <;> simp [h]
theorem affineReflection_inv_left (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (x : AmbientSpace) :
    g.affineReflection ε (fun μ => -(((ε μ : ℤˣ) : ℤ) * n μ)) (g.affineReflection ε n x) = x := by
  funext μ
  have h := unit_cast_mul_self (ε μ)
  simp only [CubicGrid.affineReflection, Int.cast_neg, Int.cast_mul]
  linear_combination (x μ - g.mirrorOrigin μ) * h
theorem affineReflection_inv_right (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (x : AmbientSpace) :
    g.affineReflection ε n (g.affineReflection ε (fun μ => -(((ε μ : ℤˣ) : ℤ) * n μ)) x) = x := by
  funext μ
  have h := unit_cast_mul_self (ε μ)
  simp only [CubicGrid.affineReflection, Int.cast_neg, Int.cast_mul]
  linear_combination (x μ - g.mirrorOrigin μ - 2 * (n μ : ℝ) * g.edge) * h
def reflectionEquiv (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) : Equiv.Perm D.Torus where
  toFun := g.descendedReflection ε n
  invFun := g.descendedReflection ε fun μ => -(((ε μ : ℤˣ) : ℤ) * n μ)
  left_inv u := by
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [descendedReflection_torusProj, descendedReflection_torusProj, affineReflection_inv_left]
  right_inv u := by
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [descendedReflection_torusProj, descendedReflection_torusProj, affineReflection_inv_right]
theorem reflectionEquiv_apply (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (u : D.Torus) :
    reflectionEquiv g ε n u = g.descendedReflection ε n u := rfl
theorem reflectionEquiv_mul (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ) :
    reflectionEquiv g ε n * reflectionEquiv g ε' n' =
      reflectionEquiv g (ε * ε') (n + fun μ => ((ε μ : ℤˣ) : ℤ) * n' μ) := by
  refine Equiv.ext fun u => ?_
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [Equiv.Perm.mul_apply, reflectionEquiv_apply, reflectionEquiv_apply, reflectionEquiv_apply,
    descendedReflection_torusProj, descendedReflection_torusProj, descendedReflection_torusProj,
    affineReflection_comp]
theorem reflectionEquiv_one_zero : reflectionEquiv g 1 0 = 1 := by
  refine Equiv.ext fun u => ?_
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [reflectionEquiv_apply, descendedReflection_torusProj, affineReflection_one_zero]
  rfl
theorem wallReflection_eq_affineReflection (μ : Fin 4) (m : ℤ) :
    g.wallReflection μ m = g.affineReflection (Function.update 1 μ (-1)) (Pi.single μ m) := by
  funext x ν
  by_cases h : ν = μ
  · subst h
    simp [CubicGrid.wallReflection, CubicGrid.affineReflection, stdBasis]
    ring
  · simp [CubicGrid.wallReflection, CubicGrid.affineReflection, stdBasis, Pi.single_eq_of_ne h,
      Function.update_of_ne h]
theorem torusWallReflection_eq_reflectionEquiv (μ : Fin 4) (m : ℤ) :
    g.torusWallReflection μ m = reflectionEquiv g (Function.update 1 μ (-1)) (Pi.single μ m) := by
  refine Equiv.ext fun u => ?_
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [reflectionEquiv_apply, descendedReflection_torusProj, ← wallReflection_eq_affineReflection]
  exact g.descendedMap_wallReflection_torusProj μ m _ x
def reflectionFamily : Subgroup (Equiv.Perm D.Torus) where
  carrier := range fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => reflectionEquiv g p.1 p.2
  mul_mem' := by
    rintro _ _ ⟨⟨ε, n⟩, rfl⟩ ⟨⟨ε', n'⟩, rfl⟩
    exact ⟨(_, _), (reflectionEquiv_mul g ε ε' n n').symm⟩
  one_mem' := ⟨(1, 0), reflectionEquiv_one_zero g⟩
  inv_mem' := by
    rintro _ ⟨⟨ε, n⟩, rfl⟩
    exact ⟨(ε, fun μ => -(((ε μ : ℤˣ) : ℤ) * n μ)), Equiv.ext fun u => rfl⟩
theorem reflectionGroup_le_reflectionFamily : g.reflectionGroup ≤ reflectionFamily g := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨μ, m⟩, rfl⟩
  exact ⟨(_, _), (torusWallReflection_eq_reflectionEquiv g μ m).symm⟩
theorem reflectionEquiv_update_mem (μ : Fin 4) (e : ℤˣ) (m : ℤ) :
    reflectionEquiv g (Function.update 1 μ e) (Pi.single μ m) ∈ g.reflectionGroup := by
  have hgen : ∀ k : ℤ, reflectionEquiv g (Function.update 1 μ (-1)) (Pi.single μ k) ∈
      g.reflectionGroup := fun k => by
    rw [← torusWallReflection_eq_reflectionEquiv]
    exact Subgroup.subset_closure ⟨(μ, k), rfl⟩
  rcases Int.units_eq_one_or e with rfl | rfl
  · have h := mul_mem (hgen m) (hgen 0)
    rw [reflectionEquiv_mul] at h
    convert h using 2
    · funext ν
      by_cases hν : ν = μ
      · subst hν
        simp
      · simp [Function.update_of_ne hν]
    · funext ν
      by_cases hν : ν = μ
      · subst hν
        simp
      · simp [Pi.single_eq_of_ne hν]
  · exact hgen m
theorem reflectionEquiv_mem (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) :
    reflectionEquiv g ε n ∈ g.reflectionGroup := by
  have h := mul_mem (mul_mem (mul_mem (reflectionEquiv_update_mem g 0 (ε 0) (n 0))
    (reflectionEquiv_update_mem g 1 (ε 1) (n 1))) (reflectionEquiv_update_mem g 2 (ε 2) (n 2)))
    (reflectionEquiv_update_mem g 3 (ε 3) (n 3))
  simp only [reflectionEquiv_mul] at h
  convert h using 2
  · funext ν
    fin_cases ν <;> simp [Function.update]
  · funext ν
    fin_cases ν <;> simp [Function.update, Pi.single_apply]
theorem coe_reflectionGroup_eq_range :
    (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
        (g.reflectionGroup : Set (Equiv.Perm D.Torus)) =
      range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => g.descendedReflection p.1 p.2) := by
  ext f
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨⟨ε, n⟩, rfl⟩ := reflectionGroup_le_reflectionFamily g hr
    exact ⟨(ε, n), rfl⟩
  · rintro ⟨⟨ε, n⟩, rfl⟩
    exact ⟨reflectionEquiv g ε n, reflectionEquiv_mem g ε n, rfl⟩
theorem exists_scaledLatticeMotion (hN : ∃ N : ℕ, 0 < N ∧ g.edge / D.mesh = N) (ε : Fin 4 → ℤˣ)
    (n : Fin 4 → ℤ) :
    ∃ Φ : ScaledLatticeMotion D.trivialExponent,
      Φ.rotation = signedCoordinateEquiv 1 ε ∧ Φ.onSpace = g.affineReflection ε n := by
  obtain ⟨N, -, hN⟩ := hN
  have hs : g.edge = (N : ℝ) * D.mesh := by
    rw [← hN, div_mul_cancel₀ _ D.mesh_pos.ne']
  have hmem : (fun μ => (1 - (((ε μ : ℤˣ) : ℤ) : ℝ)) * g.mirrorOrigin μ + 2 * (n μ : ℝ) * g.edge) ∈
      D.gridPoints := by
    refine ⟨fun μ => (1 - ((ε μ : ℤˣ) : ℤ)) * ⌊g.origin μ / D.mesh⌋ +
      (1 - ((ε μ : ℤˣ) : ℤ)) / 2 + 2 * n μ * N, fun μ => ?_⟩
    rcases Int.units_eq_one_or (ε μ) with h | h
    · simp [h, hs]
      ring
    · simp [h, hs, CubicGrid.mirrorOrigin]
      ring
  refine ⟨⟨signedCoordinateEquiv 1 ε, ⟨1, ε, rfl⟩, _, hmem⟩, rfl, ?_⟩
  funext x μ
  have h1 : (signedCoordinateEquiv 1 ε) x μ = (((ε μ : ℤˣ) : ℤ) : ℝ) * x μ := rfl
  change ((D.L : ℝ) ^ (0 : ℤ) • (signedCoordinateEquiv 1 ε) x) μ +
    ((1 - (((ε μ : ℤˣ) : ℤ) : ℝ)) * g.mirrorOrigin μ + 2 * (n μ : ℝ) * g.edge) = _
  simp only [zpow_zero, one_smul, h1, CubicGrid.affineReflection]
  ring
theorem onTorus_eq_descendedReflection {ε : Fin 4 → ℤˣ} {n : Fin 4 → ℤ}
    {Φ : ScaledLatticeMotion D.trivialExponent} (h : Φ.onSpace = g.affineReflection ε n) :
    Φ.onTorus = g.descendedReflection ε n := by
  change descendedMap _ _ Φ.onSpace = _
  rw [h]
  rfl
theorem exists_torusLatticeIsometry_of_mem (hIso : IsometryInvariance.IsometryInvarianceHolds)
    (hN : ∃ N : ℕ, 0 < N ∧ g.edge / D.mesh = N) {r : Equiv.Perm D.Torus}
    (hr : r ∈ g.reflectionGroup) : ∃ ρ : D.TorusLatticeIsometry, ρ.toEquiv = r := by
  obtain ⟨⟨ε, n⟩, rfl⟩ := reflectionGroup_le_reflectionFamily g hr
  obtain ⟨Φ, -, hΦ⟩ := exists_scaledLatticeMotion g hN ε n
  obtain ⟨ρ, hρ⟩ := ((hIso D).1 (g.descendedReflection ε n)).2
    ⟨_, Φ, rfl, onTorus_eq_descendedReflection g hΦ⟩
  refine ⟨ρ, Equiv.ext fun u => ?_⟩
  change ρ.toFun u = g.descendedReflection ε n u
  rw [hρ]
theorem rotationDet_signedCoordinateEquiv_one (ε : Fin 4 → ℤˣ) :
    rotationDet (signedCoordinateEquiv 1 ε) = (((∏ μ, ε μ : ℤˣ) : ℤ) : ℝ) := by
  have hM : (Matrix.of fun ν μ => signedCoordinateEquiv 1 ε (stdBasis μ) ν :
      Matrix (Fin 4) (Fin 4) ℝ) = Matrix.diagonal fun ν => (((ε ν : ℤˣ) : ℤ) : ℝ) := by
    ext ν μ
    simp [signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean, stdBasis,
      Matrix.diagonal_apply, Pi.single_apply]
  rw [rotationDet, hM, Matrix.det_diagonal]
  push_cast
  simp
theorem orientationSign_descendedReflection (hProps : ScaledMotionPropertiesClaim)
    (hN : ∃ N : ℕ, 0 < N ∧ g.edge / D.mesh = N) (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) :
    orientationSign (g.descendedReflection ε n) = ∏ μ, ε μ := by
  obtain ⟨Φ, hS, hmap⟩ := exists_scaledLatticeMotion g hN ε n
  have hT := onTorus_eq_descendedReflection g hmap
  have hH : HasRotationPart (g.descendedReflection ε n) (signedCoordinateEquiv 1 ε) :=
    ⟨Φ, hS, by rw [hmap]; exact descends_affineReflection g ε n⟩
  have hr : HasRotationPart (g.descendedReflection ε n) (rotationPart (g.descendedReflection ε n)) :=
    Classical.epsilon_spec ⟨_, hH⟩
  obtain ⟨Ψ, hΨ, hI⟩ := hr
  have hΨT : Ψ.onTorus = g.descendedReflection ε n := by
    funext u
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    exact (Ψ.onTorus_torusProj x).trans (congrFun hI x).symm
  have hlin : Ψ.rotation = Φ.rotation :=
    (hProps D _ Φ).2.2.1.2 Ψ (hΨT.trans hT.symm)
  have h := orientationSign_eq_rotationDet hH
  rw [← hΨ, hlin, hS, rotationDet_signedCoordinateEquiv_one] at h
  exact Units.ext (Int.cast_injective h)
theorem torusSide_eq_mul_edge {j : ℤ} (hA : g.CubesAndPeriods j) :
    PeriodicLattice.torusSide D.L D.m = (g.cubesPerSide : ℝ) * g.edge := by
  have hpos : 0 < g.edge := lt_of_lt_of_le D.mesh_pos g.isGridScale.2.1
  have h := hA.2.2.2.1
  rw [h, GluingSetup.cellCount, div_mul_cancel₀ _ hpos.ne']
  rfl
theorem descendedReflection_eq_iff (hProps : ScaledMotionPropertiesClaim) {j : ℤ}
    (hA : g.CubesAndPeriods j) (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ) :
    g.descendedReflection ε n = g.descendedReflection ε' n' ↔
      ε = ε' ∧ ∃ t : Fin 4 → ℤ, n - n' = ((g.cubesPerSide / 2 : ℕ) : ℤ) • t := by
  have hpos : 0 < g.edge := lt_of_lt_of_le D.mesh_pos g.isGridScale.2.1
  have hℓ := torusSide_eq_mul_edge g hA
  obtain ⟨h, hh⟩ := hA.2.2.2.2.2.1
  have hdiv : g.cubesPerSide / 2 = h := by omega
  have hcast : (g.cubesPerSide : ℝ) = 2 * (h : ℝ) := by
    rw [hh]
    push_cast
    ring
  rw [hdiv]
  constructor
  · intro heq
    obtain ⟨Φ, hS, hmap⟩ := exists_scaledLatticeMotion g hA.2.1 ε n
    obtain ⟨Φ', hS', hmap'⟩ := exists_scaledLatticeMotion g hA.2.1 ε' n'
    have hlin : Φ'.rotation = Φ.rotation := (hProps D _ Φ).2.2.1.2 Φ'
      ((onTorus_eq_descendedReflection g hmap').trans
        (heq.symm.trans (onTorus_eq_descendedReflection g hmap).symm))
    have hεε : ε = ε' := by
      rw [hS, hS'] at hlin
      funext μ
      have h1 := congrFun (congrArg (fun S : Equiv.Perm AmbientSpace => S (fun _ => 1)) hlin) μ
      have h2 : (((ε' μ : ℤˣ) : ℤ) : ℝ) * 1 = (((ε μ : ℤˣ) : ℤ) : ℝ) * 1 := h1
      rw [mul_one, mul_one] at h2
      exact (Units.ext (Int.cast_injective h2)).symm
    subst hεε
    refine ⟨rfl, ?_⟩
    have hc : torusProj (PeriodicLattice.torusSide D.L D.m) (g.affineReflection ε n 0) =
        torusProj (PeriodicLattice.torusSide D.L D.m) (g.affineReflection ε n' 0) := by
      rw [← descendedReflection_torusProj, ← descendedReflection_torusProj, heq]
    obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hc
    refine ⟨k, ?_⟩
    funext μ
    have h1 := congrFun hk μ
    simp only [CubicGrid.affineReflection, Pi.add_apply, TestFunctions.latticeTranslate, hℓ,
      hcast] at h1
    have h2 : (2 * g.edge) * ((n μ : ℝ) - (n' μ : ℝ) - (h : ℝ) * (k μ : ℝ)) = 0 := by
      linear_combination h1
    have h3 : (n μ : ℝ) - (n' μ : ℝ) - (h : ℝ) * (k μ : ℝ) = 0 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · exact absurd h4 (by positivity)
      · exact h4
    have h5 : n μ - n' μ - (h : ℤ) * k μ = 0 := by exact_mod_cast h3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · rintro ⟨rfl, t, ht⟩
    funext u
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [descendedReflection_torusProj, descendedReflection_torusProj]
    have hx : g.affineReflection ε n x = g.affineReflection ε n' x +
        TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) t := by
      funext μ
      have h1 : n μ = n' μ + (h : ℤ) * t μ := by
        have := congrFun ht μ
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        linarith
      simp only [CubicGrid.affineReflection, Pi.add_apply, TestFunctions.latticeTranslate, hℓ,
        hcast, h1]
      push_cast
      ring
    rw [hx, TestFunctions.torusProj_add_latticeTranslate]
end ReflectionsAsASet
section ReflectionsOnCubes
def cubeIndexShift (ε : ℤˣ) (n k : ℤ) : ℤ := if ε = 1 then k + 2 * n else 2 * n - 1 - k
theorem mem_Icc_cubeIndexShift (ε : ℤˣ) (n k : ℤ) (t o c : ℝ) :
    ((((ε : ℤˣ) : ℤ) : ℝ) * (t - o) + o + 2 * (n : ℝ) * c) - (o + c * (cubeIndexShift ε n k : ℤ)) ∈
        Icc 0 c ↔ t - (o + c * (k : ℤ)) ∈ Icc 0 c := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have e : ((((1 : ℤˣ) : ℤ) : ℝ) * (t - o) + o + 2 * (n : ℝ) * c) -
        (o + c * (cubeIndexShift 1 n k : ℤ)) = t - (o + c * (k : ℤ)) := by
      simp [cubeIndexShift]
      ring
    rw [e]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    have e : ((((-1 : ℤˣ) : ℤ) : ℝ) * (t - o) + o + 2 * (n : ℝ) * c) -
        (o + c * (cubeIndexShift (-1) n k : ℤ)) = c - (t - (o + c * (k : ℤ))) := by
      simp [cubeIndexShift, hne]
      ring
    rw [e]
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
theorem exists_cubeIndexShift (k k' : ℤ) : ∃ (ε : ℤˣ) (n : ℤ), cubeIndexShift ε n k = k' := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.emod_two_eq_zero_or_one (k' - k) with h | h
  · refine ⟨1, (k' - k) / 2, ?_⟩
    simp only [cubeIndexShift, if_true]
    omega
  · refine ⟨-1, (k' + k + 1) / 2, ?_⟩
    simp only [cubeIndexShift, hne, if_false]
    omega
theorem eq_of_cubeIndexShift_sub (ε ε' : ℤˣ) (n n' k H t : ℤ)
    (h : cubeIndexShift ε n k - cubeIndexShift ε' n' k = (H + H) * t) :
    ε = ε' ∧ n - n' = H * t := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hm : (H + H) * t = 2 * (H * t) := by ring
  rw [hm] at h
  generalize H * t = u at h ⊢
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    simp only [cubeIndexShift, hne, if_true, if_false] at h
  · exact ⟨rfl, by omega⟩
  · omega
  · omega
  · exact ⟨rfl, by omega⟩
variable {D : GluingSetup} (g : CubicGrid D)
theorem affineReflection_mem_cube_iff (ε : Fin 4 → ℤˣ) (n k : Fin 4 → ℤ) (x : AmbientSpace) :
    g.affineReflection ε n x ∈ g.toMirror.cube (fun μ => cubeIndexShift (ε μ) (n μ) (k μ)) ↔
      x ∈ g.toMirror.cube k := by
  simp only [CubicGrid.cube, Set.mem_ofPred_eq]
  exact forall_congr' fun μ =>
    mem_Icc_cubeIndexShift (ε μ) (n μ) (k μ) (x μ) (g.mirrorOrigin μ) g.edge
theorem affineReflection_surjective (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) :
    Function.Surjective (g.affineReflection ε n) := by
  intro y
  refine ⟨fun μ => (((ε μ : ℤˣ) : ℤ) : ℝ) * (y μ - g.mirrorOrigin μ - 2 * (n μ : ℝ) * g.edge) +
    g.mirrorOrigin μ, ?_⟩
  funext μ
  rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [CubicGrid.affineReflection, h] <;> ring
theorem image_affineReflection_cube (ε : Fin 4 → ℤˣ) (n k : Fin 4 → ℤ) :
    g.affineReflection ε n '' g.toMirror.cube k =
      g.toMirror.cube (fun μ => cubeIndexShift (ε μ) (n μ) (k μ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (affineReflection_mem_cube_iff g ε n k x).2 hx
  · intro hy
    obtain ⟨x, rfl⟩ := affineReflection_surjective g ε n y
    exact ⟨x, (affineReflection_mem_cube_iff g ε n k x).1 hy, rfl⟩
theorem image_descendedReflection_torusCube (ε : Fin 4 → ℤˣ) (n k : Fin 4 → ℤ) :
    g.descendedReflection ε n '' g.toMirror.torusCube k =
      g.toMirror.torusCube (fun μ => cubeIndexShift (ε μ) (n μ) (k μ)) := by
  rw [CubicGrid.torusCube, CubicGrid.torusCube, ← image_affineReflection_cube, image_image,
    image_image]
  exact image_congr fun x _ => descendedReflection_torusProj g ε n x
theorem affineReflection_affineReflection (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ) (x : AmbientSpace) :
    g.affineReflection ε n (g.affineReflection ε' n' x) =
      g.affineReflection (ε * ε') (fun μ => n μ + ((ε μ : ℤˣ) : ℤ) * n' μ) x := by
  funext μ
  simp only [CubicGrid.affineReflection, Pi.mul_apply, Units.val_mul, Int.cast_mul, Int.cast_add]
  ring
theorem descendedReflection_comp (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ) (u : D.Torus) :
    g.descendedReflection ε n (g.descendedReflection ε' n' u) =
      g.descendedReflection (ε * ε') (fun μ => n μ + ((ε μ : ℤˣ) : ℤ) * n' μ) u := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [descendedReflection_torusProj, descendedReflection_torusProj, descendedReflection_torusProj,
    affineReflection_affineReflection]
theorem coe_torusWallReflection_eq (μ : Fin 4) (n : ℤ) :
    ((g.torusWallReflection μ n : Equiv.Perm D.Torus) : D.Torus → D.Torus) =
      g.descendedReflection (Function.update 1 μ (-1)) (Pi.single μ n) := by
  funext u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [descendedReflection_torusProj]
  have h := congrFun (g.descends_torusWallReflection μ n) x
  simp only [Function.comp_apply] at h
  rw [h]
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [CubicGrid.wallReflection, CubicGrid.affineReflection, stdBasis]
    ring
  · simp [CubicGrid.wallReflection, CubicGrid.affineReflection, stdBasis, Pi.single_eq_of_ne hν,
      Function.update_of_ne hν]
theorem reflectionGroup_acts_on_cubes {D : GluingSetup} (g : CubicGrid D) {j : ℤ}
    (hA : g.toMirror.CubesAndPeriods j)
    (h2 : (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
        (g.reflectionGroup : Set (Equiv.Perm D.Torus)) =
      range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => g.descendedReflection p.1 p.2))
    (h3 : ∀ (ε ε' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ),
      g.descendedReflection ε n = g.descendedReflection ε' n' ↔
        ε = ε' ∧ ∃ t : Fin 4 → ℤ, n - n' = ((g.cubesPerSide / 2 : ℕ) : ℤ) • t)
    (h5 : ∀ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
      orientationSign (g.descendedReflection ε n) = ∏ μ, ε μ) :
    (∀ r ∈ g.reflectionGroup, ∀ C ∈ g.mirrorTorusCubes, r '' C ∈ g.mirrorTorusCubes) ∧
    (∀ C ∈ g.mirrorTorusCubes, ∀ C' ∈ g.mirrorTorusCubes,
      ∃! r : g.reflectionGroup, (r : Equiv.Perm D.Torus) '' C = C') ∧
    g.mirrorTorusCubes.ncard = g.cubesPerSide ^ 4 ∧
    Nat.card g.reflectionGroup = g.cubesPerSide ^ 4 ∧
    ∀ s : ℤˣ,
      Nat.card {r : g.reflectionGroup //
          orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = s} =
        g.cubesPerSide ^ 4 / 2 := by
  obtain ⟨-, -, -, -, hpos, heven, -, -, -, hk, -, hcard⟩ := hA
  have hpos' : 0 < g.cubesPerSide := hpos
  have hr : ∀ r ∈ g.reflectionGroup, ∃ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
      (r : D.Torus → D.Torus) = g.descendedReflection ε n := fun r hrm => by
    have hmem : (r : D.Torus → D.Torus) ∈
        range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => g.descendedReflection p.1 p.2) :=
      h2 ▸ mem_image_of_mem _ hrm
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p.1, p.2, hp.symm⟩
  have hr' : ∀ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ), ∃ r ∈ g.reflectionGroup,
      (r : D.Torus → D.Torus) = g.descendedReflection ε n := fun ε n => by
    have hmem : g.descendedReflection ε n ∈
        (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
          (g.reflectionGroup : Set (Equiv.Perm D.Torus)) := h2.symm ▸ ⟨(ε, n), rfl⟩
    obtain ⟨r, hrm, e⟩ := hmem
    exact ⟨r, hrm, e⟩
  have h6 : ∀ r ∈ g.reflectionGroup, ∀ C ∈ g.mirrorTorusCubes,
      r '' C ∈ g.mirrorTorusCubes := by
    rintro r hrm _ ⟨k, rfl⟩
    obtain ⟨ε, n, e⟩ := hr r hrm
    rw [e, image_descendedReflection_torusCube]
    exact ⟨_, rfl⟩
  have h7 : ∀ C ∈ g.mirrorTorusCubes, ∀ C' ∈ g.mirrorTorusCubes,
      ∃! r : g.reflectionGroup, (r : Equiv.Perm D.Torus) '' C = C' := by
    rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
    choose ε n h using fun μ => exists_cubeIndexShift (k μ) (k' μ)
    obtain ⟨r, hrm, e⟩ := hr' ε n
    have hshift : (fun μ => cubeIndexShift (ε μ) (n μ) (k μ)) = k' := funext h
    refine ⟨⟨r, hrm⟩, ?_, ?_⟩
    · change r '' _ = _
      rw [e, image_descendedReflection_torusCube, hshift]
    · rintro ⟨r', hrm'⟩ e'
      obtain ⟨ε', n', e2⟩ := hr r' hrm'
      have e3 : g.toMirror.torusCube (fun μ => cubeIndexShift (ε' μ) (n' μ) (k μ)) =
          g.toMirror.torusCube k' := by
        rw [← image_descendedReflection_torusCube, ← e2]
        exact e'
      obtain ⟨H, hH⟩ := heven
      have hH2 : g.cubesPerSide / 2 = H := by
        have : g.cubesPerSide = H + H := hH
        omega
      obtain ⟨t, ht⟩ := (hk _ _).1 (e3.trans (by rw [hshift]) :
        g.toMirror.torusCube (fun μ => cubeIndexShift (ε' μ) (n' μ) (k μ)) =
          g.toMirror.torusCube (fun μ => cubeIndexShift (ε μ) (n μ) (k μ)))
      have hμ : ∀ μ, ε' μ = ε μ ∧ n' μ - n μ = (H : ℤ) * t μ := fun μ => by
        refine eq_of_cubeIndexShift_sub _ _ _ _ (k μ) _ _ ?_
        have := congrFun ht μ
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hH] at this
        push_cast at this
        exact this
      have hε : ε' = ε := funext fun μ => (hμ μ).1
      have hind : g.descendedReflection ε' n' = g.descendedReflection ε n := by
        refine (h3 _ _ _ _).2 ⟨hε, t, ?_⟩
        rw [hH2]
        funext μ
        simpa using (hμ μ).2
      refine Subtype.ext (Equiv.coe_fn_injective ?_)
      exact e2.trans (hind.trans e.symm)
  have h8 : g.mirrorTorusCubes.ncard = g.cubesPerSide ^ 4 := hcard
  have h9 : Nat.card g.reflectionGroup = g.cubesPerSide ^ 4 := by
    have hC0 : g.toMirror.torusCube 0 ∈ g.mirrorTorusCubes := ⟨0, rfl⟩
    let f : g.reflectionGroup → g.mirrorTorusCubes := fun r =>
      ⟨(r : Equiv.Perm D.Torus) '' g.toMirror.torusCube 0, h6 _ r.2 _ hC0⟩
    have hf : Function.Bijective f := by
      constructor
      · intro r r' e
        have e' : (r : Equiv.Perm D.Torus) '' g.toMirror.torusCube 0 =
            (r' : Equiv.Perm D.Torus) '' g.toMirror.torusCube 0 := congrArg Subtype.val e
        exact (h7 _ hC0 _ (h6 _ r'.2 _ hC0)).unique e' rfl
      · rintro ⟨C, hC⟩
        obtain ⟨r, hr1, -⟩ := h7 _ hC0 _ hC
        exact ⟨r, Subtype.ext hr1⟩
    rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_coe_set_eq, h8]
  refine ⟨h6, h7, h8, h9, ?_⟩
  have hpos4 : 0 < g.cubesPerSide ^ 4 := pow_pos hpos' 4
  have : Finite g.reflectionGroup := Nat.finite_of_card_ne_zero (by omega)
  let θ : g.reflectionGroup :=
    ⟨g.torusWallReflection 0 0, Subgroup.subset_closure ⟨(0, 0), rfl⟩⟩
  have hflip : ∀ r : g.reflectionGroup,
      orientationSign (((θ * r : g.reflectionGroup) : Equiv.Perm D.Torus) : D.Torus → D.Torus) =
        -orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) := by
    intro r
    obtain ⟨ε, n, e⟩ := hr r r.2
    have hcomp : (((θ * r : g.reflectionGroup) : Equiv.Perm D.Torus) : D.Torus → D.Torus) =
        g.descendedReflection ((Function.update 1 0 (-1) : Fin 4 → ℤˣ) * ε)
          (fun μ => (Pi.single (0 : Fin 4) (0 : ℤ) : Fin 4 → ℤ) μ +
            (((Function.update 1 0 (-1) : Fin 4 → ℤˣ) μ : ℤˣ) : ℤ) * n μ) := by
      funext u
      have h1 : (((θ * r : g.reflectionGroup) : Equiv.Perm D.Torus) : D.Torus → D.Torus) u =
          (g.torusWallReflection 0 0 : Equiv.Perm D.Torus)
            (((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) u) := rfl
      rw [h1, coe_torusWallReflection_eq, e, descendedReflection_comp]
    rw [hcomp, h5, e, h5]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]
    have h0 : ∏ μ, (Function.update 1 0 (-1) : Fin 4 → ℤˣ) μ = -1 := by
      simp [Function.update]
    rw [h0]
    simp
  have hval : ∀ x : ℤˣ, x ≠ 1 ↔ x = -1 := fun x => by
    rcases Int.units_eq_one_or x with rfl | rfl <;> decide
  have hnn : ∀ x : ℤˣ, -x = -1 ↔ x = 1 := fun x => by
    rcases Int.units_eq_one_or x with rfl | rfl <;> decide
  have hequiv : Nat.card {r : g.reflectionGroup //
        orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = 1} =
      Nat.card {r : g.reflectionGroup //
        orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = -1} :=
    Nat.card_congr ((Equiv.mulLeft θ).subtypeEquiv fun r => by
      simp only [Equiv.coe_mulLeft, hflip, hnn])
  have hsum : Nat.card {r : g.reflectionGroup //
        orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = 1} +
      Nat.card {r : g.reflectionGroup //
        ¬ orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = 1} =
      g.cubesPerSide ^ 4 := by
    rw [← h9, ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl _)
  have hneg : Nat.card {r : g.reflectionGroup //
        ¬ orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = 1} =
      Nat.card {r : g.reflectionGroup //
        orientationSign ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) = -1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun r => hval _)
  intro s
  rcases Int.units_eq_one_or s with rfl | rfl <;> omega
end ReflectionsOnCubes
section CubeObservables
open MeasureTheory
theorem isProbabilityMeasure_wilsonGibbsMeasure
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (D : GluingSetup) :
    IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) := by
  obtain ⟨-, -, -, -, -, -, -, hP, -⟩ := hW D.L D.m D.K D.β
    (by exact_mod_cast D.one_lt_L) D.m.pos D.K.pos
  exact hP
theorem norm_le_supNorm {a : ℝ} {F : InfiniteLattice.GaugeField a → ℂ}
    (hF : InfiniteLattice.IsBoundedObservable F) (U : InfiniteLattice.GaugeField a) :
    ‖F U‖ ≤ InfiniteLattice.observableSupNorm F := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem norm_signedConj (s : ℤˣ) (ξ : ℂ) : ‖Conventions.signedConj s ξ‖ = ‖ξ‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
variable {D : GluingSetup}
theorem measurable_pullToTorus {F : D.GridField → ℂ} (hF : Measurable F) :
    Measurable (D.pullToTorus F) :=
  hF.comp (InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ))
theorem measurable_transportObservable (r : D.Torus ≃ D.Torus)
    {A : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hA : Measurable A) :
    Measurable (PeriodicLattice.transportObservable r A) :=
  hA.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
theorem measurable_signedCopy (r : Equiv.Perm D.Torus) {F : D.GridField → ℂ}
    (hF : Measurable F) : Measurable (signedCopy r F) := by
  have h := measurable_transportObservable r (measurable_pullToTorus hF)
  unfold signedCopy Conventions.signedConjFun Conventions.signedConj
  split_ifs
  · exact h
  · exact Complex.continuous_conj.measurable.comp h
theorem norm_signedCopy_le (r : Equiv.Perm D.Torus) {F : D.GridField → ℂ}
    (hF : InfiniteLattice.IsBoundedObservable F) (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    ‖signedCopy r F U‖ ≤ InfiniteLattice.observableSupNorm F := by
  change ‖Conventions.signedConj _ _‖ ≤ _
  rw [norm_signedConj]
  exact norm_le_supNorm hF _
theorem reflectionProduct_eq_prod (g : CubicGrid D) [Fintype g.reflectionGroup]
    (F : D.GridField → ℂ) :
    g.reflectionProduct F = fun U => ∏ r : g.reflectionGroup, signedCopy (r : Equiv.Perm D.Torus) F U := by
  funext U
  exact finprod_eq_prod_of_fintype _
theorem cubeObservablesOnTorus (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {D : GluingSetup} (g : CubicGrid D) (hcard : Nat.card g.reflectionGroup = g.cubesPerSide ^ 4)
    (hpos : 0 < g.cubesPerSide) (hn : (g.cubesPerSide : ℝ) = D.cellCount g.edge) :
    g.CubeObservablesOnTorus := by
  have hne : g.cubesPerSide ^ 4 ≠ 0 := pow_ne_zero _ hpos.ne'
  have hfin : Finite g.reflectionGroup := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  have : Fintype g.reflectionGroup := Fintype.ofFinite _
  have := isProbabilityMeasure_wilsonGibbsMeasure hW D
  have hprod : ∀ F : D.GridField → ℂ, InfiniteLattice.IsBoundedObservable F →
      ∀ U, ‖g.reflectionProduct F U‖ ≤ InfiniteLattice.observableSupNorm F ^ (g.cubesPerSide ^ 4) := by
    intro F hF U
    rw [reflectionProduct_eq_prod g F, norm_prod]
    have h := Finset.prod_le_prod (s := (Finset.univ : Finset g.reflectionGroup))
      (f := fun r : g.reflectionGroup => ‖signedCopy (r : Equiv.Perm D.Torus) F U‖)
      (g := fun _ => InfiniteLattice.observableSupNorm F) (fun _ _ => norm_nonneg _)
      (fun r _ => norm_signedCopy_le _ hF U)
    rwa [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h
  refine ⟨fun k F hF => ?_, ?_⟩
  · have hO : InfiniteLattice.IsBoundedObservable F := hF.1
    have hS : 0 ≤ InfiniteLattice.observableSupNorm F :=
      (norm_nonneg _).trans (norm_le_supNorm hO
        ⟨fun _ => 1, fun _ => by simp⟩)
    refine ⟨⟨measurable_pullToTorus hO.1,
        InfiniteLattice.observableSupNorm F, fun U _ => norm_le_supNorm hO _⟩,
      fun r _ => ⟨measurable_transportObservable r (measurable_pullToTorus hO.1),
        InfiniteLattice.observableSupNorm F, fun U _ => norm_le_supNorm hO _⟩,
      ⟨?_, _, fun U _ => hprod F hO U⟩, ?_⟩
    · rw [reflectionProduct_eq_prod g F]
      exact Finset.measurable_fun_prod _ fun r _ => measurable_signedCopy _ hO.1
    · have hE : ‖D.expectation (g.reflectionProduct F)‖ ≤
          InfiniteLattice.observableSupNorm F ^ (g.cubesPerSide ^ 4) := by
        have h := norm_integral_le_of_norm_le_const
          (μ := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β)
          (Filter.Eventually.of_forall (hprod F hO))
        simp at h
        exact h
      have hN : (1 / D.cellCount g.edge ^ 4) = (((g.cubesPerSide ^ 4 : ℕ) : ℝ))⁻¹ := by
        rw [← hn]
        push_cast
        simp
      rw [CubicGrid.chessboardNorm, hN]
      calc ‖D.expectation (g.reflectionProduct F)‖ ^ (((g.cubesPerSide ^ 4 : ℕ) : ℝ))⁻¹
          ≤ (InfiniteLattice.observableSupNorm F ^ (g.cubesPerSide ^ 4)) ^
              (((g.cubesPerSide ^ 4 : ℕ) : ℝ))⁻¹ :=
            Real.rpow_le_rpow (norm_nonneg _) hE (by positivity)
        _ = InfiniteLattice.observableSupNorm F := Real.pow_rpow_inv_natCast hS hne
  · have h1 : g.reflectionProduct (fun _ => 1) = fun _ => 1 := by
      funext U
      have : ∀ r : g.reflectionGroup,
          signedCopy (r : Equiv.Perm D.Torus) (fun _ => (1 : ℂ)) U = 1 := by
        intro r
        change Conventions.signedConj _ 1 = 1
        unfold Conventions.signedConj
        split_ifs <;> simp
      simp [CubicGrid.reflectionProduct, this]
    rw [CubicGrid.chessboardNorm, h1]
    have hE : D.expectation (fun _ : D.PeriodicLink → Matrices.ComplexMatrix2 => (1 : ℂ)) = 1 := by
      change ∫ _, (1 : ℂ) ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β = 1
      simp
    rw [hE]
    simp
end CubeObservables
theorem statement_holds (hLifts : TorusLifts.LiftsAndDescendedMaps.Statement)
    (hProps : ScaledMotionPropertiesClaim) (hIso : IsometryInvariance.IsometryInvarianceHolds)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    CubicGridsAndReflectionGroups.Statement := by
  intro D g j hj
  have hA := cubesAndPeriods g j hj
  have hA' : g.toMirror.CubesAndPeriods j := cubesAndPeriods g.toMirror j hj
  have hN := hA.2.1
  have h2 := coe_reflectionGroup_eq_range g
  have h3 := descendedReflection_eq_iff g hProps hA
  have h5 := orientationSign_descendedReflection g hProps hN
  obtain ⟨h6, h7, h8, h9, h10⟩ := reflectionGroup_acts_on_cubes g hA' h2 h3 h5
  exact ⟨hA, mirrorWallsAndLinks D, mirrorWallsAndCubes g,
    projOnLatticeAndOpenCubes hLifts g,
    ⟨descends_affineReflection g, h2, h3,
      fun r hr => exists_torusLatticeIsometry_of_mem g hIso hN hr, h5, h6, h7, h8, h9,
      h10⟩,
    cubeObservablesOnTorus hW g h9 hA.2.2.2.2.1 hA.2.2.2.1⟩
end CubicGridsAndReflectionGroups
end YangMills.Construction.SourcesAndGluing
end
