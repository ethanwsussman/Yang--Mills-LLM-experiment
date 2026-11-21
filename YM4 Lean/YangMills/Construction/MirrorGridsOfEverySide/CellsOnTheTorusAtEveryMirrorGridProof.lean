import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGrid
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
namespace TorusCells
theorem torusEuclidNorm_zero (S : ℝ) :
    TorusMetric.torusEuclidNorm (0 : TorusMetric.Torus4 S) = 0 := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_zero <;> assumption
theorem eq_zero_of_euclidNormVec_eq_zero {w : Fin 4 → ℝ}
    (hw : TorusMetric.euclidNormVec w = 0) : w = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem torusCellCentre_eq_of_sub {D : GridSetup} (Γ : ChessboardTori.ReflectionGrid D)
    {k k' j : Fin 4 → ℤ}
    (hdiff : ∀ μ, ((k' μ - k μ : ℤ) : ℝ) = Γ.cellsAcross * (j μ : ℝ)) :
    Γ.torusCellCentre k = Γ.torusCellCentre k' := by
  have hne : Γ.cellSide ≠ 0 := (zpow_pos (by linarith [D.one_lt_factor]) _).ne'
  have hshift : Γ.cellCentre k' = Γ.cellCentre k +
      TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) j := by
    funext μ
    have hμ := hdiff μ
    push_cast at hμ
    have hscaled : Γ.cellSide * ((k' μ : ℝ) - k μ) = PeriodicLattice.torusSide D.L D.m * j μ := by
      rw [hμ, ChessboardTori.ReflectionGrid.cellsAcross]
      field_simp
    simp only [ChessboardTori.ReflectionGrid.cellCentre, Pi.add_apply,
      TestFunctions.latticeTranslate]
    linarith
  have hproj := TestFunctions.torusProj_add_latticeTranslate
    (PeriodicLattice.torusSide D.L D.m) (Γ.cellCentre k) j
  show D.proj (Γ.cellCentre k) = D.proj (Γ.cellCentre k')
  rw [hshift]
  exact hproj.symm
end TorusCells
theorem allGridsTorusCellStructure_holds
    (hArith : ChessboardTori.ReflectionGridArithmetic.Statement)
    (hProj : ChessboardTori.ProjOnGridCells.Statement)
    (hBlocks : ChessboardTori.CellsBlocksAndSigns.Statement) :
    AllGridsTorusCellStructure := by
  intro D Γ _ hside
  have hT := ((hArith D).2.2.2 Γ).2 hside
  have hcov := hProj D Γ hside
  have hB := (hBlocks D Γ).2 hside
  have hsame := hB.1
  refine ⟨⟨Γ.cellsPerTorusSide, hT.1.2.2.1, hT.1.2.1⟩, ?_, ?_, ?_, ?_⟩
  · intro k x hx y hy hxy
    have hdist := hcov.2.1 (Γ.cell k) ⟨k, rfl⟩ x hx y hy
    rw [hxy, sub_self] at hdist
    have hnorm : TorusMetric.euclidNormVec (x - y) = 0 := by
      rw [← hdist]
      exact TorusCells.torusEuclidNorm_zero _
    exact sub_eq_zero.mp (TorusCells.eq_zero_of_euclidNormVec_eq_zero hnorm)
  · intro k k'
    rw [eq_comm]
    exact (hsame k' k).1
  · have hblock := hB.2 (Γ.block 0) ⟨0, rfl⟩
    have hcell := (hblock.2 (Γ.cell 0) ⟨0, rfl⟩).2
    have hbij := hblock.1.2
    have hcard : Nat.card (Γ.cellsWithin (Γ.block 0)) = Nat.card Γ.torusCellSet :=
      Nat.card_congr (hbij.equiv _)
    rw [← hcard, Nat.card_coe_set_eq]
    exact hcell.1
  · intro k k' himage
    have hint := ((hsame k k').2.2 himage).symm
    refine ⟨hint, ?_, ?_⟩
    · have hspec := Classical.epsilon_spec (p := fun S : Set InfiniteLattice.AmbientSpace =>
        S ∈ Γ.cellSet ∧ D.proj '' S = D.proj '' Γ.cell k) ⟨Γ.cell k, ⟨k, rfl⟩, rfl⟩
      obtain ⟨⟨k'', hk''⟩, himg⟩ := hspec
      show D.proj '' interior (Γ.liftCell (D.proj '' Γ.cell k)) = _
      have hlift : Γ.liftCell (D.proj '' Γ.cell k) = Γ.cell k'' := hk''.symm
      rw [hlift]
      rw [← hk''] at himg
      exact (hsame k k'').2.2 himg.symm
    · obtain ⟨j, hj⟩ := (hsame k k').1.mp himage
      exact TorusCells.torusCellCentre_eq_of_sub Γ hj
end YangMills.Construction.MirrorGridsAllSides
end
