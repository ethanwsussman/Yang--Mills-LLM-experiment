import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySideProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesSidesAndOffsetsProof
import YangMills.Construction.ChessboardTori.BoundByMultipleReflections
import YangMills.Construction.ChessboardTori.ColumnAndMomentsOfACellDatum
import YangMills.Construction.InfiniteLattice.FunctionOfOneCellBetweenTwoHalfSpaces
import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridOnTheTorus
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set
open InfiniteLattice (localObsAbove reflectionSeminorm timeConj timeStep)
open MirrorGridsAllSides (TorusGroupActsOnCells WallPreservingSymmetries)
namespace ChessboardTori
namespace MultipleReflectionBound
variable {D : ChessboardSetup}
theorem bijOn_image_cell {g : ReflectionGrid D} (hG : TorusGroupActsOnCells g)
    (hK : WallPreservingSymmetries g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    BijOn (fun r' : D.Torus → D.Torus => r' '' C) g.inducedTorusMaps g.torusCellSet := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ChessboardAllSides.image_bijOn <;> assumption
theorem exponent_eq_of_torusSide_eq {i k : ℕ}
    (h : PeriodicLattice.torusSide D.L i = PeriodicLattice.torusSide D.L k) : i = k := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  simp only [PeriodicLattice.torusSide] at h
  have hpow : (D.L : ℝ) ^ i = (D.L : ℝ) ^ k := by linarith
  exact pow_right_injective₀ (by linarith) hL.ne' hpow
theorem torusSide_mem_torusSides (p : ℕ+) :
    PeriodicLattice.torusSide D.L p ∈ PeriodicLattice.torusSides D.L :=
  ⟨p, p.pos, rfl⟩
theorem reflectionGrid_ext {g g' : ReflectionGrid D} (hq : g.q = g'.q)
    (ho : g.origin = g'.origin) : g = g' := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingSidesCentres.reflectionGrid_ext <;> assumption
abbrev sectionSetup (D : ChessboardSetup) (p : ℕ+) : MultipleReflections.Setup :=
  (D.withExponent p).toReflectionSetup
def stackGridAt (c : GridCell D) (p : ℕ+) : (sectionSetup D p).Grid := c.stackGrid
variable (c : GridCell D)
theorem chessboardNormAt_torusSide_eq (p : ℕ+) (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ) :
    MultipleReflections.Setup.Grid.chessboardNormAt (D := D.toReflectionSetup) c.stackGrid
        (PeriodicLattice.torusSide D.L p) (torusSide_mem_torusSides p) k F =
      MultipleReflections.Setup.Grid.chessboardNorm (stackGridAt c p) k F := by
  have key : ∀ q : ℕ+, q = p →
      MultipleReflections.Setup.Grid.chessboardNorm
          (D := ⟨⟨D.L, D.isAdmissible, D.K, q⟩, D.β, D.beta_pos⟩) c.stackGrid k F =
        MultipleReflections.Setup.Grid.chessboardNorm (stackGridAt c p) k F := by
    rintro _ rfl
    rfl
  have hs := torusSide_mem_torusSides (D := D) p
  refine key ⟨hs.choose, hs.choose_spec.1⟩ (PNat.eq ?_)
  exact exponent_eq_of_torusSide_eq (D := D) hs.choose_spec.2.symm
variable {c}
theorem mem_tileObservables (hobj : MultipleReflections.TorusGridObjectsAgree)
    {p : ℕ+} (hle : 2 * c.side ≤ PeriodicLattice.torusSide D.L p) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell) :
    F ∈ MultipleReflections.Setup.Grid.tileObservables (stackGridAt c p) c.index := by
  obtain ⟨-, -, -, -, -, hcell, -, halg, -⟩ := (hobj (sectionSetup D p) (stackGridAt c p) hle).1
  rw [← halg c.index, hcell c.index]
  have key : ∀ S : Set InfiniteLattice.AmbientSpace, S = c.cell →
      F ∈ ReflectionGrid.cellObservables (D := D) S := by
    rintro _ rfl
    exact hF
  exact key _ c.stackGrid_tile
theorem toChessboardGrid_stackGridAt (p : ℕ+) :
    (MultipleReflections.Setup.Grid.toChessboardGrid (stackGridAt c p) :
        ReflectionGrid (D.withExponent p)) = c.grid.withExponent p := by
  refine reflectionGrid_ext ?_ rfl
  have hedge := MultipleReflections.Setup.Grid.edge_eq_zpow_edgeExp (stackGridAt c p)
  have hq : (stackGridAt c p).edge = (D.L : ℝ) ^ c.grid.q := rfl
  rw [hq] at hedge
  exact (zpow_right_injective₀ (zero_lt_one.trans D.one_lt_factor)
    D.one_lt_factor.ne' hedge).symm
theorem chessboardNormOfCell_eq_chessboardNorm
    (hobj : MultipleReflections.TorusGridObjectsAgree)
    (hfacts : MirrorGridsAllSides.ReflectionGridProperties)
    {p : ℕ+} (hle : 2 * c.side ≤ PeriodicLattice.torusSide D.L p) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell) :
    (c.grid.withExponent p).chessboardNormOfCell c.cell F =
        MultipleReflections.Setup.Grid.chessboardNorm (stackGridAt c p) c.index F ∧
      (D.withExponent p).liftedObservable F ∈
        (c.grid.withExponent p).torusCellObservables ((D.withExponent p).proj '' c.cell) := by
  obtain ⟨-, -, hA, -, -⟩ := hobj (sectionSetup D p) (stackGridAt c p) hle
  obtain ⟨-, hC, hFr, hval⟩ := hA c.index F (mem_tileObservables hobj hle hF)
  have hg := toChessboardGrid_stackGridAt (c := c) p
  have hside : (c.grid.withExponent p).HasAdmissibleSide := c.hasAdmissibleSide
  have hle' : 2 * (c.grid.withExponent p).cellSide ≤
      PeriodicLattice.torusSide (D.withExponent p).L (D.withExponent p).m := hle
  obtain ⟨-, -, -, -, -, -, hT, -, -⟩ := hfacts (D.withExponent p) (c.grid.withExponent p) hside
  obtain ⟨-, hG, -, -, -, -, hK⟩ := hT hle'
  have hC' : (D.withExponent p).proj '' c.cell ∈ (c.grid.withExponent p).torusCellSet :=
    ⟨c.cell, c.cell_mem_cellSet, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hval]
    have h := (c.grid.withExponent p).chessboardNorm_eq_torusChessboardNorm
      (bijOn_image_cell hG hK hC') ((D.withExponent p).liftedObservable F)
    refine h.trans ?_
    exact congrArg (fun g : ReflectionGrid (D.withExponent p) =>
      g.torusChessboardNorm ((D.withExponent p).liftedObservable F)) hg.symm
  · have key : ∀ (g : ReflectionGrid (D.withExponent p)) (S : Set InfiniteLattice.AmbientSpace),
        g = c.grid.withExponent p → S = c.cell →
        (D.withExponent p).liftedObservable F ∈
          g.torusCellObservables ((D.withExponent p).proj '' S) →
        (D.withExponent p).liftedObservable F ∈
          (c.grid.withExponent p).torusCellObservables ((D.withExponent p).proj '' c.cell) := by
      rintro _ _ rfl rfl h
      exact h
    exact key _ _ hg c.stackGrid_tile hFr
theorem chessboardNormAt_bounded
    (hobj : MultipleReflections.TorusGridObjectsAgree)
    (hfacts : MirrorGridsAllSides.ReflectionGridProperties)
    (hest : MirrorGridsAllSides.chessboardEstimate_allSides)
    {m : ℕ+ → ℕ+} (hm : c.IsAdmissibleSideSequence m) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell) :
    ∃ C : ℝ, ∀ r, 0 ≤ c.chessboardNormAt m F r ∧ c.chessboardNormAt m F r ≤ C := by
  obtain ⟨f, -, ⟨C, hC⟩, hf⟩ := id hF
  have hFC : ∀ V, ‖F V‖ ≤ C := fun V => by
    rw [hf]
    exact hC _
  refine ⟨max C 0, fun r => ⟨Real.rpow_nonneg (norm_nonneg _) _, ?_⟩⟩
  have hle := hm.1 r
  have hread := (chessboardNormOfCell_eq_chessboardNorm hobj hfacts hle hF).2
  have hchess := hest (D.withExponent (m r)) (c.grid.withExponent (m r)) c.hasAdmissibleSide hle
  have hC' : (D.withExponent (m r)).proj '' c.cell ∈ (c.grid.withExponent (m r)).torusCellSet :=
    ⟨c.cell, c.cell_mem_cellSet, rfl⟩
  have hbound := ((hchess.2.1 _ hC').1 _ hread).2.2.1
  refine hbound.trans (Real.iSup_le (fun U => ?_) (le_max_right _ _))
  exact (hFC _).trans (le_max_left _ _)
theorem exists_monotone_subseq {m : ℕ+ → ℕ+}
    (hm : Tendsto (fun r => PeriodicLattice.torusSide D.L (m r)) atTop atTop) :
    ∃ ψ : ℕ+ → ℕ+, Tendsto ψ atTop atTop ∧
      ∀ k, PeriodicLattice.torusSide D.L (m (ψ k)) ≤
        PeriodicLattice.torusSide D.L (m (ψ (k + 1))) := by
  have hs : Tendsto Nat.succPNat atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by
      rw [← PNat.coe_le_coe, Nat.succPNat_coe]
      omega⟩
  obtain ⟨φ, hφ, hu⟩ := Filter.strictMono_subseq_of_tendsto_atTop (hm.comp hs)
  refine ⟨fun k => (φ k).succPNat, tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => ?_⟩,
    fun k => ?_⟩
  · have h1 : (k : ℕ) ≤ φ k := hφ.le_apply
    have h2 : (b : ℕ) ≤ k := hk
    rw [← PNat.coe_le_coe, Nat.succPNat_coe]
    omega
  · have h1 : ((k : ℕ)) < ((k + 1 : ℕ+) : ℕ) := by
      rw [PNat.add_coe]
      simp
    exact (hu h1).le
end MultipleReflectionBound
theorem MultipleReflectionBound.holds
    (hcol : MultipleReflections.CellObservableBetweenHalfSpaces)
    (hobj : MultipleReflections.TorusGridObjectsAgree)
    (hest : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hfacts : MirrorGridsAllSides.ReflectionGridProperties) :
    MultipleReflectionBound.Statement := by
  intro D ν hν c t ht u hu m hm
  have ht' : t = c.baseLevel := Subtype.ext (ht.trans c.baseLevel_coe.symm)
  have hu' : u = c.sideMultiple := Subtype.ext (hu.trans c.sideMultiple_coe.symm)
  subst ht' hu'
  obtain ⟨-, hsecond, hthird, -⟩ := hcol D.toReflectionSetup ν hν c.stackGrid c.index
  have hshift : MultipleReflections.Setup.Grid.stackShift c.stackGrid 1 =
      InfiniteLattice.shift (timeStep c.sideMultiple) := by
    unfold MultipleReflections.Setup.Grid.stackShift
    rw [one_zsmul]
    rfl
  have hone : (1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) c.cell :=
    ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, rfl⟩
  refine ⟨fun F hF A hA B hB => ?_, ⟨hone, ?_⟩, fun A hA B hB => ?_⟩
  · obtain ⟨ψ, hψ, hmono⟩ := MultipleReflectionBound.exists_monotone_subseq hm.2
    obtain ⟨C, hC⟩ := MultipleReflectionBound.chessboardNormAt_bounded hobj hfacts hest hm hF
    let ℓ : ℕ+ → PeriodicLattice.torusSides D.L := fun k =>
      ⟨PeriodicLattice.torusSide D.L (m (ψ k)), MultipleReflectionBound.torusSide_mem_torusSides _⟩
    have hseq : MultipleReflections.Setup.Grid.IsStackSideSequence (D := D.toReflectionSetup)
        c.stackGrid ℓ := ⟨⟨hmono, hm.2.comp hψ⟩, fun k => hm.1 (ψ k)⟩
    have hFG : F ∈ InfiniteLattice.ReflectionGrid.tileAlgebra c.stackGrid c.index :=
      MultipleReflectionBound.mem_tileObservables hobj (hm.1 1) hF
    have hval : MultipleReflections.Setup.Grid.limsupStackNorm (D := D.toReflectionSetup)
        c.stackGrid c.index ℓ F = limsup (c.chessboardNormAt m F ∘ ψ) atTop := by
      unfold MultipleReflections.Setup.Grid.limsupStackNorm
      congr 1
      funext k
      exact (MultipleReflectionBound.chessboardNormAt_torusSide_eq c (m (ψ k)) c.index F).trans
        (MultipleReflectionBound.chessboardNormOfCell_eq_chessboardNorm hobj hfacts
          (hm.1 (ψ k)) hF).1.symm
    have hq : MultipleReflections.Setup.Grid.limsupStackNorm (D := D.toReflectionSetup)
        c.stackGrid c.index ℓ F ≤ c.limsupChessboardNorm m hm F hF := by
      rw [hval, limsup_comp]
      exact limsup_le_limsup_of_le hψ
        (isBoundedUnder_of ⟨0, fun r => (hC r).1⟩ :
          IsBoundedUnder (· ≥ ·) (map ψ atTop) _).isCoboundedUnder_le
        (isBoundedUnder_of ⟨C, fun r => (hC r).2⟩)
    have hb := hsecond F hFG A hA B hB ℓ hseq
    rw [hshift] at hb
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · have hfun : c.chessboardNormAt m 1 = fun _ => 1 := by
      funext r
      have hle := hm.1 r
      have hchess := hest (D.withExponent (m r)) (c.grid.withExponent (m r))
        c.hasAdmissibleSide hle
      have hC' : (D.withExponent (m r)).proj '' c.cell ∈
          (c.grid.withExponent (m r)).torusCellSet :=
        ⟨c.cell, c.cell_mem_cellSet, rfl⟩
      exact (hchess.2.1 _ hC').2.2
    change limsup (c.chessboardNormAt m 1) atTop = 1
    rw [hfun, limsup_const]
  · have hb := hthird A hA B hB
    rw [hshift] at hb
    exact hb
end ChessboardTori
end YangMills.Construction
end
