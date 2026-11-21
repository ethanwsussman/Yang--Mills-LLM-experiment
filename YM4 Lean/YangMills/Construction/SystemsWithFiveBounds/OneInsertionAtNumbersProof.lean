import YangMills.Construction.InequalityOnMirroredCopies.ObservableOffTheFacesIsInTheCellProof
import YangMills.Construction.InfiniteLattice.SmearedDensityOfAFunctionCarriedWellInsideACell
import YangMills.Construction.SystemsWithFiveBounds.OneInsertionAtNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open Filter MeasureTheory Set TestFunctions
private theorem continuous_of_isLipschitzFor {h : InfiniteLattice.AmbientSpace → ℝ}
    (hh : IsLipschitzFor euclidDistR4 h) : Continuous h := by apply _root_.YangMills.SharedProofs.p29528 <;> assumption
private theorem isBoundedFun_of_isLipschitzFor {h : InfiniteLattice.AmbientSpace → ℝ}
    {y : InfiniteLattice.AmbientSpace} {r : ℝ} (hh : IsLipschitzFor euclidDistR4 h)
    (hv : ∀ x, x ∉ closedBallR4 y r → h x = 0) :
    IsBoundedFun h := by apply _root_.YangMills.SharedProofs.p118540 <;> assumption
private theorem regionSigma_mono {a : ℝ} {S S' : Set InfiniteLattice.AmbientSpace} (h : S ⊆ S') :
    InfiniteLattice.regionSigma (a := a) S ≤ InfiniteLattice.regionSigma (a := a) S' := by apply _root_.YangMills.Construction.InfiniteLattice.regionSigma_mono <;> assumption
private theorem complexSmeared_mem_cellObservables {D : ChessboardTori.ChessboardSetup}
    (hcell : MultipleReflections.SmearedEnergyWellInsideTile.Statement)
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement)
    (c : ChessboardTori.GridCell D) {h : InfiniteLattice.AmbientSpace → ℝ}
    (hh : IsLipschitzFor euclidDistR4 h)
    (hs : tsupport h ⊆ closedBallR4 c.centre (c.side / 4)) :
    ReflectionsAndOneInsertion.complexSmeared D h ∈
      ChessboardTori.ReflectionGrid.cellObservables (D := D) c.cell := by
  let D' : ReflectionPositivity.AxisMirror.MirrorData := ⟨D.toStandingParameters, D.β, D.beta_pos⟩
  let G : MultipleReflections.Setup.Grid D' :=
    ⟨c.side, c.hasAdmissibleSide, c.origin, c.grid.origin_mem⟩
  have hcent : G.tileCenter c.index = c.centre := by
    funext μ
    simp [InfiniteLattice.ReflectionGrid.tileCenter, InfiniteLattice.ReflectionGrid.cornerAt,
      InfiniteLattice.ReflectionGrid.basisVec, G,
      ChessboardTori.GridCell.centre, ChessboardTori.ReflectionGrid.cellCentre,
      ChessboardTori.GridCell.side, ChessboardTori.GridCell.origin, Finset.sum_apply,
      Pi.single_apply]
  have hv : ∀ x, x ∉ closedBallR4 (G.tileCenter c.index) (G.edge / 4) → h x = 0 := fun x hx => by
    rw [hcent] at hx
    by_contra hne
    exact hx (hs (subset_tsupport _ hne))
  obtain ⟨-, hmem, -, -⟩ := hcell D' G c.index h (continuous_of_isLipschitzFor hh).measurable
    (isBoundedFun_of_isLipschitzFor hh hv) hv
  obtain ⟨-, -, -, hW, -, -⟩ := hmaps D
  have hset := hW.2.2.2 c.grid c.hasAdmissibleSide c.cell c.cell_mem_cellSet
  rw [hset]
  have hsub : G.tileInterior c.index ⊆ interior c.cell := by
    refine interior_maximal (fun x hx μ => ?_) ?_
    · have := hx μ
      simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        G, ChessboardTori.GridCell.side, ChessboardTori.GridCell.origin] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · have : G.tileInterior c.index = ⋂ μ, {x : InfiniteLattice.AmbientSpace |
          G.cornerAt c.index μ < x μ ∧ x μ < G.cornerAt c.index μ + G.edge} := by
        ext x
        simp [InfiniteLattice.ReflectionGrid.tileInterior]
      rw [this]
      refine isOpen_iInter_of_finite fun μ => ?_
      exact (isOpen_lt continuous_const (continuous_apply μ)).inter
        (isOpen_lt (continuous_apply μ) continuous_const)
  exact ⟨hmem.1, Measurable.mono hmem.2 (regionSigma_mono hsub) le_rfl⟩
theorem singleInsertionWithConstants_holds
    (hcell : MultipleReflections.SmearedEnergyWellInsideTile.Statement)
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement) :
    SingleInsertionWithConstants := by
  intro F N B D hL hD c h hh hs hside
  have hpos : 0 < c.side := zpow_pos (by linarith [D.one_lt_factor]) _
  have hfr := B.admissible_constants.insertionRadiusRatio_mem.2
  have hs' : tsupport h ⊆ closedBallR4 c.centre (c.side / 4) := fun z hz => by
    have h₁ : euclidDistR4 z c.centre ≤ N.insertionRadiusRatio * c.side := hs hz
    have h₂ : N.insertionRadiusRatio * c.side ≤ c.side / 4 := by nlinarith
    exact h₁.trans h₂
  have hO := complexSmeared_mem_cellObservables hcell hmaps c hh hs'
  obtain ⟨-, -, -, hW, -, -⟩ := hmaps D
  have hOobs : InfiniteLattice.IsBoundedObservable (ReflectionsAndOneInsertion.complexSmeared D h) := by
    have hset := hW.2.2.2 c.grid c.hasAdmissibleSide c.cell c.cell_mem_cellSet
    have h1 : ReflectionsAndOneInsertion.complexSmeared D h ∈
        {A : D.GaugeField → ℂ | InfiniteLattice.IsBoundedObservable A ∧
          InfiniteLattice.IsRegionMeasurable (interior c.cell) A} := hset ▸ hO
    exact h1.1
  exact ⟨hOobs, fun ρ hρ ν hν P hP Q hQ => B.insertion_le D hL hD c h hh hs hside ρ hρ ν hν P hP Q hQ⟩
end YangMills.Construction.SystemsWithFiveBounds
end
