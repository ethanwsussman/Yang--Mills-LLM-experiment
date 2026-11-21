import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotient
import YangMills.Construction.ChessboardTori.InducedIsometriesOfTheTorus
import YangMills.Construction.ChessboardTori.SitesOffTheFacePlanes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace TorusReflectionGroup
variable {D : ChessboardSetup}
theorem proj_surj : Function.Surjective D.proj := fun x =>
  ⟨TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) x, TestFunctions.torusProj_liftPoint x⟩
theorem proj_add_latticeTranslate (v : AmbientSpace) (k : Fin 4 → ℤ) :
    D.proj (v + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) =
      D.proj v := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.proj_add_translate <;> assumption
theorem descended_unique {r : AmbientSpace → AmbientSpace} {r' s' : D.Torus → D.Torus}
    (h : D.proj ∘ r = r' ∘ D.proj)
    (h' : D.proj ∘ r = s' ∘ D.proj) : r' = s' :=
  proj_surj.injective_comp_right (h.symm.trans h')
theorem image_proj_of_descends {r : AmbientSpace → AmbientSpace} {r' : D.Torus → D.Torus}
    (h : D.proj ∘ r = r' ∘ D.proj) (A : Set AmbientSpace) :
    r' '' (D.proj '' A) = D.proj '' (r '' A) := by
  rw [← image_comp, ← image_comp, h]
theorem sublattice_eq_image_proj :
    (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
      D.proj '' (D.gridPoints : Set AmbientSpace) := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨fun μ => (n μ : ℝ) * D.mesh, ⟨n, fun _ => rfl⟩, ?_⟩
    funext μ
    exact (hn μ).symm
  · rintro ⟨y, ⟨n, hn⟩, rfl⟩
    refine ⟨n, fun μ => ?_⟩
    change ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = _
    rw [hn μ]
    rfl
variable {g : ReflectionGrid D}
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem add_latticeTranslate_mem_cell {N : ℤ} (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    (k j : Fin 4 → ℤ) {x : AmbientSpace} (hx : x ∈ g.cell k) :
    x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) j ∈ g.cell (k + N • j) := by
  intro μ
  have e : (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) j) μ -
      (g.origin μ + g.cellSide * ((k + N • j) μ : ℤ)) = x μ - (g.origin μ + g.cellSide * (k μ : ℤ)) := by
    simp only [Pi.add_apply, Pi.smul_apply, TestFunctions.latticeTranslate, smul_eq_mul, hℓ]
    push_cast
    ring
  rw [e]
  exact hx μ
theorem translate_image_cell {N : ℤ} (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    (k j : Fin 4 → ℤ) :
    translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) j) '' g.cell k =
      g.cell (k + N • j) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact add_latticeTranslate_mem_cell hℓ k j hy
  · intro hx
    refine ⟨x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) (-j), ?_, ?_⟩
    · simpa using add_latticeTranslate_mem_cell hℓ (k + N • j) (-j) hx
    · funext μ
      simp [translate, TestFunctions.latticeTranslate]
theorem proj_image_cell_add {N : ℤ} (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    (k j : Fin 4 → ℤ) :
    D.proj '' g.cell (k + N • j) = D.proj '' g.cell k := by
  rw [← translate_image_cell hℓ, ← image_comp]
  exact image_congr fun x _ => proj_add_latticeTranslate x j
theorem exists_shift_of_proj_image_cell_eq {N : ℤ} (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    {k k' : Fin 4 → ℤ} (h : D.proj '' g.cell k = D.proj '' g.cell k') :
    ∃ j : Fin 4 → ℤ, k' = k + N • j := by
  have hs : 0 < g.cellSide := cellSide_pos
  let u : AmbientSpace := fun μ => g.origin μ + g.cellSide * ((k μ : ℝ) + 1 / 2)
  have hu : u ∈ g.cell k := by
    intro μ
    have e : u μ - (g.origin μ + g.cellSide * (k μ : ℤ)) = g.cellSide / 2 := by
      simp only [u]
      ring
    rw [e]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨v, hv, hvu⟩ : D.proj u ∈ D.proj '' g.cell k' :=
    h ▸ mem_image_of_mem _ hu
  obtain ⟨j, hj⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (ℓ := PeriodicLattice.torusSide D.L D.m) hvu
  refine ⟨j, funext fun μ => ?_⟩
  obtain ⟨h2, h3⟩ := hv μ
  have e : v μ - (g.origin μ + g.cellSide * (k' μ : ℤ)) =
      g.cellSide * (((k μ + N * j μ - k' μ : ℤ) : ℝ) + 1 / 2) := by
    rw [hj]
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, hℓ, u]
    push_cast
    ring
  rw [e] at h2 h3
  have h4 : (0 : ℝ) ≤ ((k μ + N * j μ - k' μ : ℤ) : ℝ) + 1 / 2 :=
    nonneg_of_mul_nonneg_right h2 hs
  have h5 : ((k μ + N * j μ - k' μ : ℤ) : ℝ) + 1 / 2 ≤ 1 :=
    le_of_mul_le_mul_left (by simpa using h3) hs
  have h6 : (-1 : ℤ) < k μ + N * j μ - k' μ := by
    have : ((-1 : ℤ) : ℝ) < ((k μ + N * j μ - k' μ : ℤ) : ℝ) := by
      push_cast at h4 ⊢
      linarith
    exact_mod_cast this
  have h7 : k μ + N * j μ - k' μ < (1 : ℤ) := by
    have : ((k μ + N * j μ - k' μ : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      push_cast at h5 ⊢
      linarith
    exact_mod_cast this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega
theorem card_torusCellSet {N : ℤ} (hN : 2 ≤ N)
    (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide) :
    (Nat.card g.torusCellSet : ℝ) = (N : ℝ) ^ 4 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n := ⟨N.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have : NeZero n := ⟨by omega⟩
  let h : (Fin 4 → ZMod n) → Set D.Torus :=
    fun z => D.proj '' g.cell (fun μ => ((z μ).val : ℤ))
  have hinj : Function.Injective h := by
    intro z z' e
    obtain ⟨j, hj⟩ := exists_shift_of_proj_image_cell_eq hℓ e
    funext μ
    have h1 := congrFun hj μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : ((((z' μ).val : ℤ)) : ZMod n) = ((((z μ).val : ℤ) + (n : ℤ) * j μ : ℤ) : ZMod n) :=
      congrArg _ h1
    simpa using h2.symm
  have hrange : range h = g.torusCellSet := by
    ext C
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨fun μ => (k μ : ZMod n), ?_⟩
      have hk : k = (fun μ => (((k μ : ZMod n).val : ℕ) : ℤ)) +
          (n : ℤ) • (fun μ => k μ / (n : ℤ)) := by
        funext μ
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ZMod.val_intCast]
        exact (Int.emod_add_mul_ediv _ _).symm
      change D.proj '' g.cell _ = D.proj '' g.cell k
      conv_rhs => rw [hk]
      exact (proj_image_cell_add hℓ _ _).symm
  rw [← hrange, Nat.card_congr (Equiv.ofInjective h hinj).symm]
  simp
theorem exists_mem_translate (hC : g.ReflectionGroupCoordForm) {N : ℤ} (hE : Even N)
    (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide) (j : Fin 4 → ℤ) :
    ∃ u ∈ g.reflectionGroup, (u : AmbientSpace → AmbientSpace) =
      translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) j) ∧ orientationSign u = 1 := by
  obtain ⟨M, rfl⟩ := hE
  obtain ⟨u, hu, h1, h2⟩ := hC.2.2.2.2.2.2.2 (fun μ => M * j μ)
  refine ⟨u, hu, ?_, h2⟩
  rw [h1]
  congr 1
  funext μ
  simp only [TestFunctions.latticeTranslate, hℓ]
  push_cast
  ring
def descent (hI : g.DescendsToTorus) (r : g.reflectionGroup) : D.Torus → D.Torus :=
  Classical.choose (hI.2.2.1 r.1 r.2)
theorem descent_spec (hI : g.DescendsToTorus) (r : g.reflectionGroup) :
    D.proj ∘ r.1 = descent hI r ∘ D.proj :=
  (Classical.choose_spec (hI.2.2.1 r.1 r.2)).1
theorem descent_apply (hI : g.DescendsToTorus) (r : g.reflectionGroup) (x : AmbientSpace) :
    descent hI r (D.proj x) = D.proj (r.1 x) :=
  (congrFun (descent_spec hI r) x).symm
theorem descent_one (hI : g.DescendsToTorus) : descent hI 1 = id :=
  descended_unique (descent_spec hI 1) rfl
theorem descent_mul (hI : g.DescendsToTorus) (r s : g.reflectionGroup) :
    descent hI (r * s) = descent hI r ∘ descent hI s := by
  funext x
  obtain ⟨y, rfl⟩ := proj_surj x
  simp only [Function.comp, descent_apply]
  rfl
def descentPerm (hI : g.DescendsToTorus) (r : g.reflectionGroup) : Equiv.Perm D.Torus where
  toFun := descent hI r
  invFun := descent hI r⁻¹
  left_inv x := by
    have h := congrFun (descent_mul hI r⁻¹ r) x
    rw [inv_mul_cancel, descent_one] at h
    exact h.symm
  right_inv x := by
    have h := congrFun (descent_mul hI r r⁻¹) x
    rw [mul_inv_cancel, descent_one] at h
    exact h.symm
def descentHom (hI : g.DescendsToTorus) : g.reflectionGroup →* Equiv.Perm D.Torus :=
  MonoidHom.mk' (descentPerm hI) fun r s =>
    Equiv.ext fun x => congrFun (descent_mul hI r s) x
theorem exists_descentHom (hI : g.DescendsToTorus) :
    ∃ φ : g.reflectionGroup →* Equiv.Perm D.Torus,
      (∀ r : g.reflectionGroup, D.proj ∘ r.1 = φ r ∘ D.proj) ∧
      φ.ker = D.periodTranslations.subgroupOf g.reflectionGroup ∧
      (fun e : Equiv.Perm D.Torus => (e : D.Torus → D.Torus)) '' (φ.range : Set _) =
        g.inducedTorusMaps := by
  refine ⟨descentHom hI, fun r => descent_spec hI r, ?_, ?_⟩
  · ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h := hI.2.2.2 r.1 r.2 1 g.reflectionGroup.one_mem (descent hI r) id (descent_spec hI r) rfl
    rw [inv_one, one_mul] at h
    rw [← h]
    constructor
    · intro e
      funext x
      exact congrArg (fun e : Equiv.Perm D.Torus => e x) e
    · intro e
      exact Equiv.ext fun x => congrFun e x
  · ext r'
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r.1, r.2, descent_spec hI r⟩
    · rintro ⟨r, hr, h⟩
      refine ⟨descentHom hI ⟨r, hr⟩, ⟨_, rfl⟩, ?_⟩
      exact descended_unique (descent_spec hI ⟨r, hr⟩) h
theorem orientationSign_eq_of_descent_eq (hC : g.ReflectionGroupCoordForm) (hI : g.DescendsToTorus)
    {N : ℤ} (hE : Even N) (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    {r s : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) (hs : s ∈ g.reflectionGroup)
    {r' : D.Torus → D.Torus}
    (h1 : D.proj ∘ r = r' ∘ D.proj)
    (h2 : D.proj ∘ s = r' ∘ D.proj) : orientationSign r = orientationSign s := by
  obtain ⟨k, hk⟩ := (hI.2.2.2 r hr s hs r' r' h1 h2).1 rfl
  obtain ⟨u, -, hu, hu1⟩ := exists_mem_translate hC hE hℓ k
  have h3 : orientationSign (s⁻¹ * r : Equiv.Perm AmbientSpace) = 1 := by
    rw [hk, ← hu, hu1]
  have h4 := hC.2.2.2.1 s hs (s⁻¹ * r) (g.reflectionGroup.mul_mem (g.reflectionGroup.inv_mem hs) hr)
  rw [mul_inv_cancel_left, h3, mul_one] at h4
  exact h4
theorem descent_eq_of_image_eq (hC : g.ReflectionGroupCoordForm) {N : ℤ} (hE : Even N)
    (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide) {r s : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) (hs : s ∈ g.reflectionGroup) {r' s' : D.Torus → D.Torus}
    (h1 : D.proj ∘ r = r' ∘ D.proj)
    (h2 : D.proj ∘ s = s' ∘ D.proj) {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    (he : D.proj '' (r '' S) = D.proj '' (s '' S)) : r' = s' := by
  obtain ⟨k, hk⟩ := hC.2.2.2.2.2.1 r hr S hS
  obtain ⟨k', hk'⟩ := hC.2.2.2.2.2.1 s hs S hS
  rw [← hk, ← hk'] at he
  obtain ⟨j, hj⟩ := exists_shift_of_proj_image_cell_eq hℓ he
  obtain ⟨u, hu, hu1, -⟩ := exists_mem_translate hC hE hℓ j
  have hur : (u * r : Equiv.Perm AmbientSpace) '' S = s '' S := by
    rw [Equiv.Perm.coe_mul, image_comp, ← hk, hu1, translate_image_cell hℓ, ← hj, hk']
  have hS' : s '' S ∈ g.cellSet := hC.2.2.2.2.2.1 s hs S hS
  have hus : u * r = s := by
    have h3 := (hC.2.2.2.2.2.2.1 S hS (s '' S) hS').unique
      (y₁ := ⟨u * r, g.reflectionGroup.mul_mem hu hr⟩) (y₂ := ⟨s, hs⟩) hur rfl
    exact congrArg Subtype.val h3
  refine descended_unique (r := s) ?_ h2
  rw [← hus]
  funext x
  rw [← congrFun h1 x]
  change D.proj (u (r x)) = D.proj (r x)
  rw [hu1]
  exact proj_add_latticeTranslate (r x) j
theorem image_mem_torusCellSet (hC : g.ReflectionGroupCoordForm) {r' : D.Torus → D.Torus}
    (hr' : r' ∈ g.inducedTorusMaps) {C : Set D.Torus} (hc : C ∈ g.torusCellSet) :
    r' '' C ∈ g.torusCellSet := by
  obtain ⟨r, hr, h⟩ := hr'
  obtain ⟨S, hS, rfl⟩ := hc
  exact ⟨r '' S, hC.2.2.2.2.2.1 r hr S hS, (image_proj_of_descends h S).symm⟩
theorem existsUnique_map_torusCellSet (hC : g.ReflectionGroupCoordForm) (hI : g.DescendsToTorus)
    {N : ℤ} (hE : Even N) (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide)
    {C C' : Set D.Torus} (hc : C ∈ g.torusCellSet) (hc' : C' ∈ g.torusCellSet) :
    ∃! r', r' ∈ g.inducedTorusMaps ∧ r' '' C = C' := by
  obtain ⟨S, hS, rfl⟩ := hc
  obtain ⟨S', hS', rfl⟩ := hc'
  obtain ⟨r, hr, -⟩ := hC.2.2.2.2.2.2.1 S hS S' hS'
  refine ⟨descent hI r, ⟨⟨r.1, r.2, descent_spec hI r⟩, ?_⟩, ?_⟩
  · exact (image_proj_of_descends (descent_spec hI r) S).trans (congrArg _ hr)
  · rintro s' ⟨⟨s, hs, h⟩, he⟩
    have he' : s' '' (D.proj '' S) = D.proj '' S' := he
    refine descent_eq_of_image_eq hC hE hℓ hs r.2 h (descent_spec hI r) hS ?_
    rw [← image_proj_of_descends h, he', hr]
theorem card_inducedTorusMaps (hC : g.ReflectionGroupCoordForm) (hI : g.DescendsToTorus)
    {N : ℤ} (hE : Even N) (hℓ : PeriodicLattice.torusSide D.L D.m = (N : ℝ) * g.cellSide) :
    Nat.card g.inducedTorusMaps = Nat.card g.torusCellSet := by
  have h0 : D.proj '' g.cell 0 ∈ g.torusCellSet := ⟨_, ⟨0, rfl⟩, rfl⟩
  have hmap : ∀ r' : g.inducedTorusMaps, r'.1 '' (D.proj '' g.cell 0) ∈ g.torusCellSet :=
    fun r' => image_mem_torusCellSet hC r'.2 h0
  refine Nat.card_congr (Equiv.ofBijective (fun r' => ⟨_, hmap r'⟩) ⟨?_, ?_⟩)
  · intro a b e
    exact Subtype.ext ((existsUnique_map_torusCellSet hC hI hE hℓ h0 (hmap a)).unique
      ⟨a.2, rfl⟩ ⟨b.2, (congrArg Subtype.val e).symm⟩)
  · rintro ⟨C, hc⟩
    obtain ⟨r', ⟨h1, h2⟩, -⟩ := existsUnique_map_torusCellSet hC hI hE hℓ h0 hc
    exact ⟨⟨r', h1⟩, Subtype.ext h2⟩
theorem holds (hA : ReflectionGridArithmetic.Statement)
    (hC : ReflectionGroupCoordinates.Statement) (hI : TorusInducedSymmetries.Statement)
    (hS : PointsOffWalls.Statement) : Statement := by
  intro D g hside
  obtain ⟨-, hN, hE, hN2, -⟩ := (((hA D).2.2.2 g).2 hside).1
  have hℓ : PeriodicLattice.torusSide D.L D.m = (g.cellsPerTorusSide : ℝ) * g.cellSide :=
    (div_eq_iff (cellSide_pos (g := g)).ne').1 hN
  have C := hC D g
  have I := hI D g hside
  have Z := hS D g
  have hcells := card_torusCellSet hN2 hℓ
  refine ⟨exists_descentHom I, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_inducedTorusMaps C I hE hℓ, hcells, hN]
  · rintro r' ⟨r, hr, h⟩
    obtain ⟨s', hs', hiso⟩ := I.2.2.1 r hr
    rw [descended_unique h hs']
    exact hiso
  · intro r hr s hs r' h1 h2
    exact orientationSign_eq_of_descent_eq C I hE hℓ hr hs h1 h2
  · rintro r' ⟨r, hr, h⟩
    constructor
    · rw [sublattice_eq_image_proj, image_proj_of_descends h, (Z.2.1 r hr).2]
    · rw [image_proj_of_descends h, C.2.2.2.2.1 r hr]
  · intro r' hr' c hc
    exact image_mem_torusCellSet C hr' hc
  · intro c hc c' hc'
    exact existsUnique_map_torusCellSet C I hE hℓ hc hc'
  · rw [hcells, hN]
end TorusReflectionGroup
end YangMills.Construction.ChessboardTori
end
