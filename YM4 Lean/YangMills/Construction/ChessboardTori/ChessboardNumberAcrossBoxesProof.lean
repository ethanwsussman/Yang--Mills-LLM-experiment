import YangMills.Construction.MirrorGridsOfEverySide.DominationByTheChessboardProof
import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.ChessboardNumberAcrossBoxes
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Function
noncomputable section
namespace YangMills.Construction.ChessboardTori.ChessboardBlockInvariance
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TestFunctions (latticeTranslate)
def periodPoint (D : ChessboardSetup) (k : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨latticeTranslate D.torusPeriod k, fun μ => 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) * k μ, fun μ => by
    have hLpos : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    have hper := SourcesAndGluing.torusSide_eq_intCast_mul_meshSize hLpos D.m D.K
    have hper' : D.torusPeriod = ((2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) : ℤ) : ℝ) * D.mesh := hper
    simp only [latticeTranslate]
    rw [hper']
    push_cast
    ring⟩
theorem liftedExpectation_congr (hWilson : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (D : ChessboardSetup)
    {H H' : D.GaugeField → ℂ} (hH : Measurable H) (hH' : Measurable H')
    (h : ∀ U ∈ D.compactFields, H (D.liftField U) = H' (D.liftField U)) :
    D.liftedExpectation H = D.liftedExpectation H' := by
  have hLone : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hnull := (hWilson D.L D.m D.K D.β hLone D.m.pos D.K.pos).2.2.2.2.2.2.2.2.1
  have hae : ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β), U ∈ D.compactFields :=
    mem_ae_iff.mpr hnull
  have hlift := InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)
  have hrepr : ∀ {G : D.GaugeField → ℂ}, Measurable G → D.liftedExpectation G =
      ∫ U, G (D.liftField U) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) :=
    fun hG => integral_map hlift.aemeasurable hG.aestronglyMeasurable
  rw [hrepr hH, hrepr hH']
  exact integral_congr_ae (hae.mono fun U hU => h U hU)
theorem measurable_of_mem_cellObservables {D : ChessboardSetup} {S : Set AmbientSpace}
    {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : Measurable F := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ChessboardDomination.measurable_of_mem_cellObservables <;> assumption
theorem measurable_finprod_cells {D : ChessboardSetup} {T : Set (Set AmbientSpace)} (hT : T.Finite)
    {F : Set AmbientSpace → D.GaugeField → ℂ} (hF : ∀ S ∈ T, Measurable (F S)) :
    Measurable fun U => ∏ᶠ S ∈ T, F S U := by
  have heq : (fun U => ∏ᶠ S ∈ T, F S U) = fun U => ∏ S ∈ hT.toFinset, F S U :=
    funext fun U => finprod_mem_eq_finite_toFinset_prod _ hT
  rw [heq]
  exact Finset.measurable_fun_prod _ fun S hS => hF S (hT.mem_toFinset.mp hS)
theorem chessboardBlockInvariance_holds (hArith : ReflectionGridArithmetic.Statement)
    (hSigns : CellsBlocksAndSigns.Statement) (hLift : LiftingRules.Statement)
    (hBasic : GridBasicProperties.Statement)
    (hWilson : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : Statement := by
  intro D g hside B hB B' hB' S hS F hF
  obtain ⟨-, -, -, hcoord, hrules, -, -⟩ := hBasic D g
  obtain ⟨hsame, hblocks⟩ := (hSigns D g).2 hside
  obtain ⟨-, -, -, harith⟩ := hArith D
  have hfree := hcoord.2.2.2.2.2.2.1
  have hfin : ∀ B ∈ g.blocks, (g.cellsWithin B).Finite := by
    rintro _ ⟨k, rfl⟩
    rw [((harith g).2 hside).2 k |>.2.1]
    exact ((Set.finite_Icc k (fun μ => k μ + g.cellsPerTorusSide - 1)).subset
      fun j hj => ⟨fun μ => (hj μ).1, fun μ => (hj μ).2⟩).image _
  have hmeas : ∀ C ∈ g.blocks,
      Measurable fun U => ∏ᶠ S' ∈ g.cellsWithin C, g.transportTo S S' F U := by
    intro C hC
    refine measurable_finprod_cells (hfin C hC) fun S' hS' => ?_
    obtain ⟨r, hr⟩ := (hfree S hS S' hS'.1).exists
    exact measurable_of_mem_cellObservables (hrules S hS S' hS'.1 S' hS'.1 r hr F hF F hF 0).1
  refine liftedExpectation_congr hWilson D (hmeas B' hB') (hmeas B hB) fun U hU => ?_
  have hbij := (hblocks B hB).1.2
  have hbij' := (hblocks B' hB').1.2
  have hinv := hbij'.invOn_invFunOn
  have hback : BijOn (invFunOn (fun C => D.proj '' C) (g.cellsWithin B')) g.torusCellSet
      (g.cellsWithin B') := (bijOn_comm hinv).mpr hbij'
  refine (finprod_mem_eq_of_bijOn _ (hback.comp hbij) fun T hT => ?_).symm
  have hT' := hback.mapsTo (hbij.mapsTo hT)
  have himage : D.proj '' (invFunOn (fun C => D.proj '' C) (g.cellsWithin B')
      (D.proj '' T)) = D.proj '' T := hinv.2 (hbij.mapsTo hT)
  change g.transportTo S T F _ = g.transportTo S (invFunOn (fun C => D.proj '' C) (g.cellsWithin B')
    (D.proj '' T)) F _
  generalize invFunOn (fun C => D.proj '' C) (g.cellsWithin B') (D.proj '' T) = T'
    at hT' himage ⊢
  obtain ⟨k, rfl⟩ := hT.1
  obtain ⟨k', rfl⟩ := hT'.1
  obtain ⟨_, ⟨j, rfl⟩, hv⟩ := ((hsame k' k).2.1).mp himage
  have hcopy := (hLift D).2.2.1 g hside U hU (periodPoint D j) ⟨j, rfl⟩
  have hc := hcopy.2 S hS F hF (g.cell k') ⟨k', rfl⟩
  have hv' : g.cell k =
      translate ((periodPoint D j : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) '' g.cell k' :=
    hv
  rw [hv']
  exact hc.1.trans hc.2
end YangMills.Construction.ChessboardTori.ChessboardBlockInvariance
end
