import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGrids
import YangMills.Construction.InfiniteLattice.ChessboardEstimateAndRulesOnMirrorGrids
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfAGridOfMultipleReflections
import YangMills.Construction.InfiniteLattice.GroupCopiesAndCellsOfTheBoxOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorus
import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridOnTheTorus
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesOnTheTorusAtEveryMirrorGridProof
import Mathlib
set_option autoImplicit false
open Set Function
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MultipleReflections
namespace ChessboardBoundProof
open Setup Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem signedConj_mul (s : ℤˣ) (a b : ℂ) :
    Conventions.signedConj s (a * b) = Conventions.signedConj s a * Conventions.signedConj s b := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_mul <;> assumption
theorem signedConj_add (s : ℤˣ) (a b : ℂ) :
    Conventions.signedConj s (a + b) = Conventions.signedConj s a + Conventions.signedConj s b := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_add <;> assumption
theorem latticeSymmetry_ext {s t : D.LatticeSymmetry} (h : s.toFun = t.toFun) : s = t := by
  cases s
  cases t
  simp only at h
  subst h
  rfl
theorem orientationUnit_eq (g : G.reflectionGroup) (s : ℤˣ) (h : G.orientation g = ((s : ℤ) : ℝ)) :
    G.orientationUnit g = s := by
  unfold Setup.Grid.orientationUnit
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [h]
  · have h1 : G.orientation g ≠ 1 := by
      rw [h]
      norm_num
    simp [h1]
variable {G}
theorem reflectedCopy_reflectedCopy (hE : G.UniqueElementBetweenTiles) (hC : G.ReflectedCopyRules)
    {k k' k'' : Fin 4 → ℤ} {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) :
    G.reflectedCopy k' k'' (G.reflectedCopy k k' F) = G.reflectedCopy k k'' F := by
  obtain ⟨g, hu, hm, hs⟩ := hE k' k''
  have himg : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'' := (hu g).2 rfl
  have h := (hC k k' F hF).2.2.2 g k'' himg
  have e : G.toLatticeSymmetry D.isAdmissible g = G.tileSymmetry k' k'' :=
    latticeSymmetry_ext hm
  rw [orientationUnit_eq G g _ hs, e] at h
  exact h
theorem copyRules (hE : G.UniqueElementBetweenTiles)
    (hC : G.ReflectedCopyRules) : G.CopyRules := by
  intro k k' k'' F F' z hF hF'
  refine ⟨reflectedCopy_reflectedCopy hE hC hF, ?_, ?_, ?_, ?_⟩
  · funext U
    exact signedConj_mul _ _ _
  · funext U
    exact signedConj_add _ _ _
  · intro hs
    funext U
    simp [Setup.Grid.reflectedCopy, hs, Conventions.signedConjFun, Conventions.signedConj,
      InfiniteLattice.LatticeSymmetry.actOn]
  · intro hs
    funext U
    simp [Setup.Grid.reflectedCopy, hs, Conventions.signedConjFun, Conventions.signedConj,
      InfiniteLattice.LatticeSymmetry.actOn]
theorem signsBalanced (hH : ∀ k : Fin 4 → ℤ, G.BoxTilesSignBalanced k) :
    G.SignsBalanced := by
  intro k s
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact (hH k).2.1
  · exact (hH k).2.2
theorem copiesCommuteWithPeriods (hC : G.ReflectedCopyRules) (hT : G.PeriodShiftsInGroup)
    (hN : D.PeriodShiftsInvisible) : G.CopiesCommuteWithPeriods := by
  rintro k k' F hF v ⟨n, hn⟩
  have hvs : (v : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup D.side :=
    ⟨n, fun μ => by rw [hn]; simp [mul_comm]⟩
  obtain ⟨hv, ⟨g, hgm, hgs⟩, q, -, -, hcell⟩ := hT v hvs
  have e1 : G.reflectedCopy k (k' + q) F =
      (InfiniteLattice.shift v).actOn (G.reflectedCopy k k' F) := by
    have himg : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile (k' + q) := by
      rw [hgm]
      exact hcell k'
    have h := (hC k k' F hF).2.2.2 g _ himg
    have e : G.toLatticeSymmetry D.isAdmissible g = InfiniteLattice.shift v :=
      latticeSymmetry_ext hgm
    rw [orientationUnit_eq G g 1 (by simpa using hgs), e] at h
    rw [← h]
    funext U
    simp [Conventions.signedConjFun, Conventions.signedConj]
    rfl
  refine ⟨k' + q, (hcell k').symm, e1, ?_⟩
  have hobs := ((InfiniteLattice.ReflectionGrid.mem_tileAlgebra G).1 (hC k k' F hF).1).1
  rw [e1]
  refine hN.2 v n ?_ _ hobs
  rw [hn]
  funext μ
  simp [TestFunctions.latticeTranslate]
theorem chessboardNorm_eq_torus {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    {k : Fin 4 → ℤ} {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) :
    G.chessboardNorm k F = G.toChessboardGrid.torusChessboardNorm (D.liftToLinks F) := by
  obtain ⟨-, hC, hF', e⟩ := hA k F hF
  exact e
theorem bound_of_bijOn (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    (hR : LiftsCommuteWithCopies G) (C : Set (Fin 4 → ℤ))
    (hC : BijOn (fun k => torusImage D (G.tile k)) C G.toChessboardGrid.torusCellSet)
    (F : (Fin 4 → ℤ) → D.GaugeField → ℂ) (hF : ∀ k ∈ C, F k ∈ G.tileAlgebra k) :
    ‖D.torusExpectation fun U => ∏ᶠ k ∈ C, F k U‖ ≤ ∏ᶠ k ∈ C, G.chessboardNorm k (F k) := by
  classical
  let e : C ≃ G.toChessboardGrid.torusCellSet := hC.equiv _
  have himg : ∀ T : G.toChessboardGrid.torusCellSet,
      torusImage D (G.tile (e.symm T : Fin 4 → ℤ)) = T.1 := fun T =>
    congrArg Subtype.val (e.apply_symm_apply T)
  let Fam : G.toChessboardGrid.torusCellSet →
      (D.toChessboardSetup.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    fun T => D.liftToLinks (F (e.symm T : Fin 4 → ℤ))
  have hFam : ∀ T, Fam T ∈ G.toChessboardGrid.torusCellObservables T.1 := fun T => by
    have h := (hR _ 0 _ (hF _ (e.symm T).2)).1
    rwa [himg T] at h
  have key := (hM D.toChessboardSetup G.toChessboardGrid
    (G.two_mul_cellSide_le_torusSide hfit)).1 Fam hFam
  have lhs : (fun U => ∏ᶠ T, Fam T U) =
      fun U => ∏ᶠ k ∈ C, F k (InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U) := by
    funext U
    rw [← finprod_set_coe_eq_finprod_mem C]
    exact finprod_comp_equiv e.symm
      (f := fun k : C => F k (InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U))
  have rhs : ∏ᶠ T, G.toChessboardGrid.torusChessboardNormAtSide
      (G.two_mul_cellSide_le_torusSide hfit) T.2
      (Fam T) (hFam T) = ∏ᶠ k ∈ C, G.chessboardNorm k (F k) := by
    rw [← finprod_set_coe_eq_finprod_mem C]
    have h := finprod_comp_equiv e.symm (f := fun k : C => G.chessboardNorm k (F k))
    rw [← h]
    refine finprod_congr fun T => ?_
    exact (chessboardNorm_eq_torus hA (hF _ (e.symm T).2)).symm
  rw [lhs, rhs] at key
  exact key
theorem areCongruent_of_common {S S' T : Set AmbientSpace} (h : G.AreCongruent S T)
    (h' : G.AreCongruent S' T) : G.AreCongruent S S' := by
  obtain ⟨hS, hT, v, hv⟩ := h
  obtain ⟨hS', -, w, hw⟩ := h'
  refine ⟨hS, hS', v - w, ?_⟩
  ext y
  constructor
  · intro hy
    have hm : y + D.side • (fun μ => (w μ : ℝ)) ∈ T := by
      rw [hw]
      exact ⟨y, hy, rfl⟩
    rw [hv] at hm
    obtain ⟨x, hx, hxy⟩ := hm
    refine ⟨x, hx, ?_⟩
    funext μ
    have := congrFun hxy μ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    push_cast
    linarith
  · rintro ⟨x, hx, rfl⟩
    have hm : x + D.side • (fun μ => (v μ : ℝ)) ∈ T := by
      rw [hv]
      exact ⟨x, hx, rfl⟩
    rw [hw] at hm
    obtain ⟨y, hy, hxy⟩ := hm
    convert hy using 1
    funext μ
    have := congrFun hxy μ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    push_cast
    linarith
theorem areCongruent_of_torusImage_eq (hB : G.TilesCongruentToBoxTile)
    (hImg : ∀ S S' : Set AmbientSpace, G.AreCongruent S S' → torusImage D S = torusImage D S')
    (hBij : BijOn (torusImage D) G.boxTiles (torusImage D '' G.tiling))
    {k k' : Fin 4 → ℤ} (h : torusImage D (G.tile k) = torusImage D (G.tile k')) :
    G.AreCongruent (G.tile k) (G.tile k') := by
  obtain ⟨S, ⟨hS, hSc⟩, -⟩ := hB.2 (G.tile k) ⟨k, rfl⟩
  obtain ⟨S', ⟨hS', hSc'⟩, -⟩ := hB.2 (G.tile k') ⟨k', rfl⟩
  have e : S = S' := hBij.injOn hS hS' (by rw [← hImg _ _ hSc, ← hImg _ _ hSc', h])
  subst e
  exact areCongruent_of_common hSc hSc'
theorem areCongruent_refl (k : Fin 4 → ℤ) : G.AreCongruent (G.tile k) (G.tile k) := by
  refine ⟨⟨k, rfl⟩, ⟨k, rfl⟩, 0, ?_⟩
  have h : (fun x : AmbientSpace => x + D.side • fun μ => (((0 : Fin 4 → ℤ) μ : ℤ) : ℝ)) = id := by
    funext x μ
    simp
  rw [h, image_id]
theorem bijOn_boxTileIndices (hT : G.toChessboardGrid.torusCellSet = torusImage D '' G.tiling)
    (hBij : BijOn (torusImage D) G.boxTiles (torusImage D '' G.tiling)) :
    BijOn (fun k => torusImage D (G.tile k)) G.boxTileIndices G.toChessboardGrid.torusCellSet := by
  rw [hT]
  exact hBij.comp (G.tile_injective.injOn.bijOn_image)
theorem boundOnBox (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    (hR : LiftsCommuteWithCopies G)
    (hC : BijOn (fun k => torusImage D (G.tile k)) G.boxTileIndices
      G.toChessboardGrid.torusCellSet) :
    G.ChessboardBoundOnBox := by
  intro F hF
  have h := bound_of_bijOn hM hA hR _ hC F hF
  simp only [finprod_mem_eq_finite_toFinset_prod _
    (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m)] at h
  exact h
theorem boundOnTransversal (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    (hR : LiftsCommuteWithCopies G) (hB : G.TilesCongruentToBoxTile)
    (hImg : ∀ S S' : Set AmbientSpace, G.AreCongruent S S' → torusImage D S = torusImage D S')
    (hT : G.toChessboardGrid.torusCellSet = torusImage D '' G.tiling)
    (hBij : BijOn (torusImage D) G.boxTiles (torusImage D '' G.tiling)) :
    G.ChessboardBoundOnTransversal := by
  intro C hC F hF
  refine bound_of_bijOn hM hA hR C ⟨?_, ?_, ?_⟩ F hF
  · intro k _
    rw [hT]
    exact ⟨G.tile k, ⟨k, rfl⟩, rfl⟩
  · intro k hk k' hk' h
    obtain ⟨p, -, hp⟩ := hC k
    have h1 := hp k ⟨hk, areCongruent_refl k⟩
    have h2 := hp k' ⟨hk', areCongruent_of_torusImage_eq hB hImg hBij h⟩
    exact h1.trans h2.symm
  · intro T hTm
    rw [hT] at hTm
    obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hTm
    obtain ⟨p, ⟨hp, hc⟩, -⟩ := hC k
    exact ⟨p, hp, (hImg _ _ hc).symm⟩
theorem normRules (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    (hR : LiftsCommuteWithCopies G)
    (hE : G.UniqueElementBetweenTiles) (hC : G.ReflectedCopyRules)
    (hRead : D.PullbackRespectsAlgebra)
    (hT : G.toChessboardGrid.torusCellSet = torusImage D '' G.tiling) :
    G.ChessboardNormRules := by
  intro k k' F z hF
  have hTk : torusImage D (G.tile k) ∈ G.toChessboardGrid.torusCellSet := by
    rw [hT]
    exact ⟨G.tile k, ⟨k, rfl⟩, rfl⟩
  obtain ⟨hle, ⟨h1, e1⟩, ⟨hz, ez⟩, -, -⟩ :=
    (hM D.toChessboardSetup G.toChessboardGrid (G.two_mul_cellSide_le_torusSide hfit)).2.1 _ hTk
      (D.liftToLinks F) (hR k 0 F hF).1 z
  have hone : (fun _ => (1 : ℂ)) ∈ G.tileAlgebra k := (G.tileAlgebra k).one_mem
  have hzF : (fun U => z * F U) ∈ G.tileAlgebra k :=
    (G.tileAlgebra k).smul_mem hF z
  refine ⟨?_, ?_, ?_, ?_⟩
  · have harr : G.reflectedProduct k' (G.reflectedCopy k k' F) = G.reflectedProduct k F := by
      funext U
      unfold Setup.Grid.reflectedProduct
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [reflectedCopy_reflectedCopy hE hC hF]
    simp only [Setup.Grid.chessboardNorm, harr]
  · exact (chessboardNorm_eq_torus hA hone).trans e1
  · rw [chessboardNorm_eq_torus hA hF]
    refine hle.trans ?_
    exact ((hRead.2 F F ((InfiniteLattice.ReflectionGrid.mem_tileAlgebra G).1 hF).1
      ((InfiniteLattice.ReflectionGrid.mem_tileAlgebra G).1 hF).1 0).2.2.1)
  · rw [chessboardNorm_eq_torus hA hzF, chessboardNorm_eq_torus hA hF]
    exact ez
theorem finprod_eq_of_injective {α β M : Type*} [CommMonoid M] (ι : α → β) (hι : Injective ι)
    (φ : β → M) (h : ∀ t, t ∉ range ι → φ t = 1) : ∏ᶠ t, φ t = ∏ᶠ a, φ (ι a) := by
  rw [← finprod_mem_range hι, ← finprod_mem_univ]
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ?_
  simp only [mem_univ, true_iff]
  by_contra hn
  exact hx (h x hn)
theorem finite_of_subset_tile (G G' : D.Grid) (q : Fin 4 → ℤ) (O : Set (Fin 4 → ℤ))
    (hO : ∀ k ∈ O, G.tile k ⊆ G'.tile q) : O.Finite := by
  have hl := G.edge_pos
  refine (Set.finite_Icc (fun μ => ⌊(G'.cornerAt q μ - G.shift μ) / G.edge⌋)
    (fun μ => ⌈(G'.cornerAt q μ + G'.edge - G.shift μ) / G.edge⌉)).subset ?_
  intro k hk
  have hc : G.cornerAt k ∈ G'.tile q := hO k hk (fun ν => ⟨le_rfl, by linarith⟩)
  have e : ∀ μ, G.cornerAt k μ = G.shift μ + G.edge * k μ := fun μ => by
    simp [InfiniteLattice.ReflectionGrid.cornerAt]
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · have h1 := (hc μ).1
    rw [e] at h1
    refine Int.cast_le.1 ((Int.floor_le _).trans ?_ : _ ≤ ((k μ : ℤ) : ℝ))
    rw [div_le_iff₀ hl]
    linarith
  · have h1 := (hc μ).2
    rw [e] at h1
    refine Int.cast_le.1 (le_trans ?_ (Int.le_ceil _) : ((k μ : ℤ) : ℝ) ≤ _)
    rw [le_div_iff₀ hl]
    linarith
theorem tileInterior_subset (G G' : D.Grid) {k q : Fin 4 → ℤ} (hsub : G.tile k ⊆ G'.tile q) :
    G.tileInterior k ⊆ G'.tileInterior q := by
  have hl := G.edge_pos
  have h1 : G.cornerAt k ∈ G.tile k := fun ν => ⟨le_rfl, by linarith⟩
  have h2 : (G.cornerAt k + fun _ => G.edge) ∈ G.tile k := fun ν =>
    ⟨by simp only [Pi.add_apply]; linarith, by simp only [Pi.add_apply]; exact le_rfl⟩
  intro x hx μ
  have a := (hsub h1 μ).1
  have b := (hsub h2 μ).2
  simp only [Pi.add_apply] at b
  have c := hx μ
  exact ⟨by linarith [c.1], by linarith [c.2]⟩
theorem tileAlgebra_mono (G G' : D.Grid) {k q : Fin 4 → ℤ} (hsub : G.tile k ⊆ G'.tile q)
    {A : D.GaugeField → ℂ} (hA : A ∈ G.tileAlgebra k) : A ∈ G'.tileAlgebra q := by
  have hA' := (InfiniteLattice.ReflectionGrid.mem_tileAlgebra G).1 hA
  refine (InfiniteLattice.ReflectionGrid.mem_tileAlgebra G').2 ⟨hA'.1, ?_⟩
  have hle : InfiniteLattice.regionSigma (a := D.mesh) (G.tileInterior k) ≤
      InfiniteLattice.regionSigma (a := D.mesh) (G'.tileInterior q) :=
    biSup_mono fun b hb => ⟨tileInterior_subset G G' hsub hb.1, tileInterior_subset G G' hsub hb.2⟩
  exact Measurable.mono hA'.2 hle le_rfl
theorem eq_of_areCongruent_of_subset (G G' : D.Grid) (h2 : 2 * G'.edge ≤ D.side)
    {q k k' : Fin 4 → ℤ}
    (hk : G.tile k ⊆ G'.tile q) (hk' : G.tile k' ⊆ G'.tile q)
    (hc : G.AreCongruent (G.tile k) (G.tile k')) : k = k' := by
  obtain ⟨-, -, v, hv⟩ := hc
  have hl := G.edge_pos
  have hl' := G'.edge_pos
  have hs : 0 < D.side := by linarith
  have h1 : G.cornerAt k ∈ G.tile k := fun ν => ⟨le_rfl, by linarith⟩
  have h3 : G.cornerAt k + D.side • (fun μ => (v μ : ℝ)) ∈ G.tile k' := by
    rw [hv]
    exact ⟨_, h1, rfl⟩
  have a := hk h1
  have b := hk' h3
  have hv0 : v = 0 := by
    funext μ
    have a1 := a μ
    have b1 := b μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at b1
    have h4 : D.side * |(v μ : ℝ)| ≤ D.side / 2 := by
      have : |D.side * (v μ : ℝ)| ≤ G'.edge := by
        rw [abs_le]
        constructor <;> linarith [a1.1, a1.2, b1.1, b1.2]
      rw [abs_mul, abs_of_pos hs] at this
      linarith
    have h5 : |(v μ : ℝ)| ≤ 1 / 2 := by
      have : D.side * |(v μ : ℝ)| ≤ D.side * (1 / 2) := by linarith
      exact le_of_mul_le_mul_left this hs
    have h6 : |v μ| < 1 := by
      have : ((|v μ| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]
        linarith
      exact_mod_cast this
    simpa using Int.abs_lt_one_iff.1 h6
  subst hv0
  have h7 : (fun x : AmbientSpace => x + D.side • fun μ => (((0 : Fin 4 → ℤ) μ : ℤ) : ℝ)) = id := by
    funext x μ
    simp
  rw [h7, image_id] at hv
  exact G.tile_injective hv.symm
theorem coarseTileProductBound (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    (hO' : TorusGridObjectsAgree)
    {hfit : 2 * G.edge ≤ D.side} (hA : ProductLiftsToTorus G hfit)
    (hR : LiftsCommuteWithCopies G) (hB : G.TilesCongruentToBoxTile)
    (hC : G.ReflectedCopyRules)
    (hImg : ∀ S S' : Set AmbientSpace, G.AreCongruent S S' → torusImage D S = torusImage D S')
    (hT : G.toChessboardGrid.torusCellSet = torusImage D '' G.tiling)
    (hBij : BijOn (torusImage D) G.boxTiles (torusImage D '' G.tiling))
    (hRules : G.ChessboardNormRules) :
    G.CoarseTileProductBound := by
  classical
  intro k₀ G' hside' h2' hplanes q O hO o E hE'
  have hfin : O.Finite := finite_of_subset_tile G G' q O hO
  have hcopy : ∀ k, G.reflectedCopy o k E ∈ G.tileAlgebra k := fun k => (hC o k E hE').1
  have hP : (fun U => ∏ᶠ k ∈ O, G.reflectedCopy o k E U) ∈ G'.tileAlgebra q := by
    have e : (fun U => ∏ᶠ k ∈ O, G.reflectedCopy o k E U) =
        ∏ k ∈ hfin.toFinset, G.reflectedCopy o k E := by
      funext U
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_apply]
    rw [e]
    exact prod_mem fun k hk =>
      tileAlgebra_mono G G' (hO k (hfin.mem_toFinset.1 hk)) (hcopy k)
  refine ⟨hP, ?_⟩
  obtain ⟨hAgree', hR', hA', -, hOther'⟩ := hO' D G' h2'
  obtain ⟨hAgree, -, -, -, -⟩ := hO' D G hfit
  have hT' := (hOther' 0).2.1.1
  have hs : G'.toChessboardGrid.cellSide = (D.L : ℝ) ^ k₀ * G.toChessboardGrid.cellSide := by
    rw [G.cellSide_toChessboardGrid, G'.cellSide_toChessboardGrid, hside']
  have hpl : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ),
      G'.toChessboardGrid.wall μ k = G.toChessboardGrid.wall μ' k' := by
    intro μ k
    obtain ⟨μ', k', e⟩ := hplanes μ k
    refine ⟨μ', k', ?_⟩
    rw [hAgree'.2.2.1 μ k, hAgree.2.2.1 μ' k', e]
  have hQ : torusImage D (G'.tile q) ∈ G'.toChessboardGrid.torusCellSet := by
    rw [hT']
    exact ⟨G'.tile q, ⟨q, rfl⟩, rfl⟩
  have hinj : InjOn (fun k => torusImage D (G.tile k)) O := fun k hk k' hk' h =>
    eq_of_areCongruent_of_subset G G' h2' (hO k hk) (hO k' hk')
      (areCongruent_of_torusImage_eq hB hImg hBij h)
  have hcell : ∀ k, torusImage D (G.tile k) ∈ G.toChessboardGrid.torusCellSet := fun k => by
    rw [hT]
    exact ⟨G.tile k, ⟨k, rfl⟩, rfl⟩
  let ι : O → G.toChessboardGrid.torusCellsWithin (torusImage D (G'.tile q)) := fun k =>
    ⟨torusImage D (G.tile k), hcell k, image_mono (hO k k.2)⟩
  have hι : Injective ι := fun a b h =>
    Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h))
  let Fam : G.toChessboardGrid.torusCellsWithin (torusImage D (G'.tile q)) →
      (D.toChessboardSetup.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun T =>
    if h : ∃ k ∈ O, torusImage D (G.tile k) = T.1 then
      D.liftToLinks (G.reflectedCopy o h.choose E) else fun _ => 1
  have hFamι : ∀ k : O, Fam (ι k) = D.liftToLinks (G.reflectedCopy o k E) := by
    intro k
    have h : ∃ p ∈ O, torusImage D (G.tile p) = (ι k).1 := ⟨k, k.2, rfl⟩
    have e : h.choose = k := hinj h.choose_spec.1 k.2 h.choose_spec.2
    simp only [Fam, dif_pos h, e]
  have hFam1 : ∀ T, T ∉ range ι → Fam T = fun _ => 1 := by
    intro T hT'
    have h : ¬ ∃ k ∈ O, torusImage D (G.tile k) = T.1 := by
      rintro ⟨k, hk, e⟩
      exact hT' ⟨⟨k, hk⟩, Subtype.ext e⟩
    simp only [Fam, dif_neg h]
  have hone : ∀ k, (fun _ => (1 : ℂ)) ∈ G.tileAlgebra k := fun k => (G.tileAlgebra k).one_mem
  have hFam : ∀ T, Fam T ∈ G.toChessboardGrid.torusCellObservables T.1 := by
    intro T
    by_cases h : ∃ k ∈ O, torusImage D (G.tile k) = T.1
    · have e : Fam T = D.liftToLinks (G.reflectedCopy o h.choose E) := by
        simp only [Fam, dif_pos h]
      have h1 := (hR _ 0 _ (hcopy h.choose)).1
      rw [h.choose_spec.2] at h1
      rw [e]
      exact h1
    · have e : Fam T = fun _ => 1 := by
        simp only [Fam, dif_neg h]
      have hTm := T.2.1
      rw [hT] at hTm
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hTm
      rw [e, ← hk]
      exact (hR k 0 _ (hone k)).1
  obtain ⟨hprod, hbound⟩ := (hM D.toChessboardSetup G.toChessboardGrid
    (G.two_mul_cellSide_le_torusSide hfit)).2.2 k₀ G'.toChessboardGrid hs
    (G'.two_mul_cellSide_le_torusSide h2') hpl _ hQ Fam hFam
  have hread : (fun U => ∏ᶠ T, Fam T U) =
      D.liftToLinks (fun U => ∏ᶠ k ∈ O, G.reflectedCopy o k E U) := by
    funext U
    rw [finprod_eq_of_injective ι hι (fun T => Fam T U)
      (fun T hT' => by simp only [hFam1 T hT'])]
    simp only [hFamι]
    exact finprod_set_coe_eq_finprod_mem O
      (f := fun k => G.reflectedCopy o k E (D.toChessboardSetup.liftField U))
  have hvals : ∏ᶠ T, G.toChessboardGrid.torusChessboardNormAtSide
      (G.two_mul_cellSide_le_torusSide hfit)
      T.2.1 (Fam T) (hFam T) = G.chessboardNorm o E ^ O.ncard := by
    have hv1 : ∀ T, T ∉ range ι →
        G.toChessboardGrid.torusChessboardNorm (Fam T) = 1 := by
      intro T hT'
      rw [hFam1 T hT']
      have h := chessboardNorm_eq_torus hA (hone o)
      exact h.symm.trans (hRules o o E 0 hE').2.1
    have hv2 : ∀ k : O, G.toChessboardGrid.torusChessboardNorm (Fam (ι k)) =
        G.chessboardNorm o E := by
      intro k
      rw [hFamι k, ← chessboardNorm_eq_torus hA (hcopy k)]
      exact (hRules o k E 0 hE').1
    have h := finprod_eq_of_injective ι hι
      (fun T => G.toChessboardGrid.torusChessboardNorm (Fam T)) hv1
    refine h.trans ?_
    simp only [hv2]
    rw [finprod_set_coe_eq_finprod_mem O (f := fun _ => G.chessboardNorm o E),
      finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_const,
      Set.ncard_eq_toFinset_card O hfin]
  rw [chessboardNorm_eq_torus hA' hP, ← hvals, ← hread]
  exact hbound
end ChessboardBoundProof
theorem chessboardBoundAndRules_holds
    (hMirror : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    (hObjects : TorusGridObjectsAgree)
    (hFacts : GridElementaryFacts)
    (hGroup : GridGroupAndBoxTiles)
    (hPullback : SymmetriesAndTorusPullback) :
    ChessboardBoundAndRules := by
  intro D G hfit
  obtain ⟨-, hR, hA, -, hOther⟩ := hObjects D G hfit
  obtain ⟨-, ⟨hT, -, hImg, hBij⟩, -, -⟩ := hOther 0
  obtain ⟨-, -, -, hE, -⟩ := hFacts D G G.edgeExp G.edge_eq_zpow_edgeExp
  obtain ⟨-, -, -, hC, hFit⟩ := hGroup D G G.edgeExp G.edge_eq_zpow_edgeExp
  obtain ⟨-, hTr, hB, hH⟩ := hFit hfit
  obtain ⟨hRead, -, -, -, -, hN, -, -⟩ := hPullback D
  have hBox := ChessboardBoundProof.bijOn_boxTileIndices hT hBij
  have hRules := ChessboardBoundProof.normRules hMirror hA hR hE hC hRead hT
  exact ⟨ChessboardBoundProof.copyRules hE hC,
    ChessboardBoundProof.signsBalanced hH,
    ChessboardBoundProof.copiesCommuteWithPeriods hC hTr hN, hR,
    ChessboardBoundProof.boundOnBox hMirror hA hR hBox,
    ChessboardBoundProof.boundOnTransversal hMirror hA hR hB hImg hT hBij,
    hRules,
    ChessboardBoundProof.coarseTileProductBound hMirror hObjects hA hR hB hC hImg hT hBij hRules⟩
end MultipleReflections
end YangMills.Construction
end
