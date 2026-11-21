import YangMills.Construction.InfiniteLattice.ChessboardObjectsOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.ChessboardValueOfTheEstimate
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem isBoundedObservable_reflectedCopy (k k' : Fin 4 → ℤ) {F : D.GaugeField → ℂ}
    (hF : InfiniteLattice.IsBoundedObservable F) :
    InfiniteLattice.IsBoundedObservable (G.reflectedCopy k k' F) := by
  obtain ⟨hmeas, C, hbound⟩ := hF
  have hcont : Continuous (G.tileSymmetry k k').pullbackField := by
    have hval : Continuous (Subtype.val : D.GaugeField → _) := continuous_subtype_val
    refine continuous_induced_rng.2 (continuous_pi fun l => ?_)
    exact (continuous_apply ((G.tileSymmetry k k').linkMap l)).comp hval
  have hmeas' : Measurable ((G.tileSymmetry k k').actOn F) := hmeas.comp hcont.measurable
  refine ⟨?_, C, fun U => ?_⟩
  · unfold reflectedCopy Conventions.signedConjFun Conventions.signedConj
    split_ifs
    · exact hmeas'
    · exact Complex.continuous_conj.measurable.comp hmeas'
  · unfold reflectedCopy Conventions.signedConjFun Conventions.signedConj
    split_ifs
    · exact hbound _
    · rw [RCLike.norm_conj]
      exact hbound _
theorem isBoundedObservable_reflectedProduct (k : Fin 4 → ℤ) {F : D.GaugeField → ℂ}
    (hF : InfiniteLattice.IsBoundedObservable F) :
    InfiniteLattice.IsBoundedObservable (G.reflectedProduct k F) := by
  have h := fun k' => G.isBoundedObservable_reflectedCopy k k' hF
  choose hmeas C hbound using h
  refine ⟨?_, ∏ k' ∈ (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m).toFinset, C k',
    fun U => ?_⟩
  · exact Finset.measurable_fun_prod _ fun k' _ => hmeas k'
  · unfold reflectedProduct
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k' _ => hbound k' U
theorem tile_subset_block_iff (k : Fin 4 → ℤ) :
    G.tile k ⊆ G.toChessboardGrid.block 0 ↔ k ∈ G.boxTileIndices := by
  have hpos := G.edge_pos
  have horigin : G.toChessboardGrid.origin = G.shift := rfl
  have hmem : ∀ x : InfiniteLattice.AmbientSpace, x ∈ G.tile k ↔
      ∀ μ, G.shift μ + G.edge * k μ ≤ x μ ∧ x μ ≤ G.shift μ + G.edge * k μ + G.edge := by
    intro x
    simp only [InfiniteLattice.ReflectionGrid.tile, InfiniteLattice.cube,
      InfiniteLattice.ReflectionGrid.cornerAt, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hblock : ∀ x : InfiniteLattice.AmbientSpace, x ∈ G.toChessboardGrid.block 0 ↔
      ∀ μ, 0 ≤ x μ - G.shift μ ∧ x μ - G.shift μ ≤ D.side := by
    intro x
    simp only [ChessboardTori.ReflectionGrid.block, mem_ofPred_eq, mem_Icc, horigin, Pi.zero_apply,
      Int.cast_zero, mul_zero, add_zero]
    rfl
  constructor
  · intro hsub μ
    have hlow : G.cornerAt k ∈ G.tile k := by
      rw [hmem]
      intro ν
      simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ⟨le_rfl, by linarith⟩
    have hhigh : G.cornerAt k + (fun _ => G.edge) ∈ G.tile k := by
      rw [hmem]
      intro ν
      simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ⟨by linarith, le_rfl⟩
    have hlow' := ((hblock _).1 (hsub hlow) μ).1
    have hhigh' := ((hblock _).1 (hsub hhigh) μ).2
    simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hlow' hhigh'
    refine ⟨?_, ?_⟩
    · have hnn : (0 : ℝ) ≤ k μ := by
        have hprod : 0 ≤ G.edge * k μ := by linarith
        exact nonneg_of_mul_nonneg_right hprod hpos
      exact_mod_cast hnn
    · have hmul : ((k μ : ℝ) + 1) * G.edge ≤ D.side := by linarith
      have hdiv : (k μ : ℝ) + 1 ≤ D.side / G.edge := (le_div_iff₀ hpos).2 hmul
      change (k μ : ℝ) ≤ D.side / G.edge - 1
      linarith
  · intro hk x hx
    rw [hblock]
    rw [hmem] at hx
    intro μ
    have hnn : (0 : ℝ) ≤ k μ := by exact_mod_cast (hk μ).1
    have hup : (k μ : ℝ) ≤ D.side / G.edge - 1 := (hk μ).2
    have hmul : ((k μ : ℝ) + 1) * G.edge ≤ D.side :=
      (le_div_iff₀ hpos).1 (by linarith)
    have hx' := hx μ
    have hprod : 0 ≤ G.edge * k μ := mul_nonneg hpos.le hnn
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
theorem cellsWithin_block_eq (hcell : ∀ k : Fin 4 → ℤ, G.toChessboardGrid.cell k = G.tile k) :
    G.toChessboardGrid.cellsWithin (G.toChessboardGrid.block 0) = G.tile '' G.boxTileIndices := by
  ext S
  constructor
  · rintro ⟨⟨k, rfl⟩, hsub⟩
    rw [hcell] at hsub ⊢
    exact ⟨k, (G.tile_subset_block_iff k).1 hsub, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, hcell k⟩, (G.tile_subset_block_iff k).2 hk⟩
theorem productOfTransports_eq_reflectedProduct
    (hcell : ∀ k : Fin 4 → ℤ, G.toChessboardGrid.cell k = G.tile k)
    (htransport : ∀ (k k' : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
      G.toChessboardGrid.transportTo (G.toChessboardGrid.cell k) (G.toChessboardGrid.cell k') F =
        G.reflectedCopy k k' F)
    (k : Fin 4 → ℤ) {F : D.GaugeField → ℂ} (hF : F ∈ G.tileObservables k) :
    G.toChessboardGrid.productOfTransports (G.toChessboardGrid.cell k)
      (G.toChessboardGrid.block 0) F = G.reflectedProduct k F := by
  funext U
  unfold ChessboardTori.ReflectionGrid.productOfTransports reflectedProduct
  rw [G.cellsWithin_block_eq hcell, finprod_mem_image G.tile_injective.injOn,
    finprod_mem_eq_finite_toFinset_prod _ (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m)]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [← hcell k', htransport k k' F hF]
theorem liftedExpectation_eq_torusExpectation {H : D.GaugeField → ℂ}
    (hH : InfiniteLattice.IsBoundedObservable H) :
    D.toChessboardSetup.liftedExpectation H = D.torusExpectation H :=
  InfiniteLattice.integral_liftedWilsonMeasure D.L D.m D.K D.β hH
theorem toChessboardGrid_isCoarse (h : 1 ≤ G.edge) : G.toChessboardGrid.IsCoarse := by
  have hL := D.one_lt_L
  rw [G.edge_eq_zpow_edgeExp] at h
  change 0 ≤ G.edgeExp
  by_contra hneg
  have hlt : (D.L : ℝ) ^ G.edgeExp < (D.L : ℝ) ^ (0 : ℤ) :=
    zpow_lt_zpow_right₀ hL (not_le.1 hneg)
  rw [zpow_zero] at hlt
  linarith
end Setup.Grid
theorem estimateNormHolds_of_chessboardInequality
    (hObjects : ChessboardObjectsHold)
    (hInequality : ChessboardTori.ChessboardInequality.Statement) :
    EstimateNormHolds := by
  intro D G hedge k F hF
  obtain ⟨-, -, -, -, -, hcell, -, halg, htransport⟩ := hObjects D G
  have hobs : InfiniteLattice.IsBoundedObservable F := hF.1
  have hexp : G.toChessboardGrid.chessboardExpectation (G.toChessboardGrid.cell k)
      (G.toChessboardGrid.block 0) F = D.torusExpectation (G.reflectedProduct k F) := by
    unfold ChessboardTori.ReflectionGrid.chessboardExpectation
    rw [G.productOfTransports_eq_reflectedProduct hcell htransport k hF]
    exact Setup.Grid.liftedExpectation_eq_torusExpectation (G.isBoundedObservable_reflectedProduct k hobs)
  have hineq := (hInequality D.toChessboardSetup G.toChessboardGrid
    (G.two_mul_cellSide_le_torusSide hedge)).1
    (G.toChessboardGrid.block 0) ⟨0, rfl⟩ (G.toChessboardGrid.cell k) ⟨k, rfl⟩ F
    (by rw [halg k]; exact hF)
  have hnormeq : G.toChessboardGrid.chessboardNorm (G.toChessboardGrid.cell k) F =
      G.chessboardNorm k F := by
    unfold ChessboardTori.ReflectionGrid.chessboardNorm Setup.Grid.chessboardNorm
    rw [hexp] at hineq ⊢
    have habs : ‖D.torusExpectation (G.reflectedProduct k F)‖ =
        (D.torusExpectation (G.reflectedProduct k F)).re := by
      conv_lhs => rw [show D.torusExpectation (G.reflectedProduct k F) =
        ((D.torusExpectation (G.reflectedProduct k F)).re : ℂ) from
          Complex.ext (by simp) (by simp [hineq.1])]
      rw [Complex.norm_real, Real.norm_of_nonneg hineq.2.1]
    have hcount : G.toChessboardGrid.cellsAcross = G.tilesPerSide := by
      unfold ChessboardTori.ReflectionGrid.cellsAcross Setup.Grid.tilesPerSide
      rw [G.cellSide_toChessboardGrid]
      rfl
    rw [hcount, habs]
  exact ⟨hexp, hnormeq, fun h1 => ⟨G.toChessboardGrid_isCoarse h1, hnormeq⟩⟩
end YangMills.Construction.MultipleReflections
end
