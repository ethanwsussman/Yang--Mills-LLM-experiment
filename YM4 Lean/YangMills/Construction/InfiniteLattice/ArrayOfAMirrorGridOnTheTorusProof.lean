import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellFunctionsOnTheToriProof
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.InfiniteLattice.ArrayOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.CellsOfTheTorusOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.EvaluationsOnTheCopiesOfAMirrorGrid
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace TorusProduct
theorem bijOn_torusCarrier {E : ChessboardTori.ChessboardSetup} (g : ChessboardTori.ReflectionGrid E)
    {C₀ : Set E.Torus} (hC₀ : C₀ ∈ g.torusCellSet)
    (hact : ∀ r' ∈ g.inducedTorusMaps, ∀ C ∈ g.torusCellSet, r' '' C ∈ g.torusCellSet)
    (hsimple : ∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet,
      ∃! r', r' ∈ g.inducedTorusMaps ∧ r' '' C = C') :
    BijOn (g.torusCarrier C₀) g.torusCellSet g.inducedTorusMaps := by
  have spec : ∀ C ∈ g.torusCellSet,
      g.torusCarrier C₀ C ∈ g.inducedTorusMaps ∧ g.torusCarrier C₀ C '' C₀ = C := fun C hC => by
    obtain ⟨r, hr, -⟩ := hsimple C₀ hC₀ C hC
    exact Classical.epsilon_spec
      (p := fun r' : E.Torus → E.Torus => r' ∈ g.inducedTorusMaps ∧ r' '' C₀ = C) ⟨r, hr⟩
  refine ⟨fun C hC => (spec C hC).1, fun C hC C' hC' h => ?_, fun r' hr' => ?_⟩
  · calc C = g.torusCarrier C₀ C '' C₀ := (spec C hC).2.symm
      _ = g.torusCarrier C₀ C' '' C₀ := by rw [h]
      _ = C' := (spec C' hC').2
  · have hC := hact r' hr' C₀ hC₀
    exact ⟨r' '' C₀, hC, (hsimple C₀ hC₀ _ hC).unique (spec _ hC) ⟨hr', rfl⟩⟩
theorem periodicExpectation_congr (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (E : ChessboardTori.ChessboardSetup) {H H' : (E.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (h : ∀ U ∈ PeriodicLattice.compactGaugeFields E.L E.m ((E.K : ℕ) : ℤ), H U = H' U) :
    E.periodicExpectation H = E.periodicExpectation H' := by apply _root_.YangMills.Construction.MirrorGridsAllSides.CellObservablesTorus.periodicExpectation_congr <;> assumption
end TorusProduct
open Setup.Grid in
theorem productOnTorusHolds_of
    (h₁ : ChessboardTori.GridBasicProperties.Statement)
    (h₂ : LiftsCommuteHolds)
    (h₃ : TorusCellsHold)
    (h₄ : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : ProductOnTorusHolds := by
  intro D G h k F hF
  have hs := G.two_mul_cellSide_le_torusSide h
  obtain ⟨-, -, -, -, -, -, hT⟩ := h₁ D.toChessboardSetup G.toChessboardGrid
  obtain ⟨-, hGT, -⟩ := hT hs
  obtain ⟨-, -, -, -, -, hact, hsimple, -⟩ := hGT
  obtain ⟨hcells, -, -, hbij⟩ := h₃ D G h 0
  have hC₀ : torusImage D (G.tile k) ∈ G.toChessboardGrid.torusCellSet := by
    rw [hcells]
    exact ⟨G.tile k, ⟨k, rfl⟩, rfl⟩
  have hcar := TorusProduct.bijOn_torusCarrier G.toChessboardGrid hC₀ hact hsimple
  have hb : BijOn (fun k' : Fin 4 → ℤ => torusImage D (G.tile k')) G.boxTileIndices
      G.toChessboardGrid.torusCellSet := by
    rw [hcells]
    exact hbij.comp G.tile_injective.injOn.bijOn_image
  have hread := h₂ D G h
  have harray : ∀ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      D.liftToLinks (G.reflectedProduct k F) U.1 =
        G.toChessboardGrid.torusProduct (D.liftToLinks F) U.1 := by
    intro U
    change (∏ k' ∈ (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m).toFinset,
        D.liftToLinks (G.reflectedCopy k k' F) U.1) =
      ∏ᶠ r' ∈ G.toChessboardGrid.inducedTorusMaps,
        G.toChessboardGrid.torusTransport r' (D.liftToLinks F) U.1
    rw [← finprod_mem_eq_finite_toFinset_prod]
    exact finprod_mem_eq_of_bijOn _ (hcar.comp hb) fun k' _ => (hread k k' F hF).2 U
  refine ⟨harray, hC₀, (hread k k F hF).1, ?_⟩
  have hexp : D.torusExpectation (G.reflectedProduct k F) =
      D.toChessboardSetup.periodicExpectation
        (G.toChessboardGrid.torusProduct (D.liftToLinks F)) :=
    TorusProduct.periodicExpectation_congr h₄ D.toChessboardSetup
      (H := D.liftToLinks (G.reflectedProduct k F)) fun U hU => harray ⟨U, hU⟩
  have hn : G.tilesPerSide = G.toChessboardGrid.cellsAcross := by
    rw [Setup.Grid.tilesPerSide, ChessboardTori.ReflectionGrid.cellsAcross, G.cellSide_toChessboardGrid]
    rfl
  rw [ChessboardTori.ReflectionGrid.torusChessboardNormAtSide_eq, Setup.Grid.chessboardNorm, hexp, hn]
end YangMills.Construction.MultipleReflections
end
