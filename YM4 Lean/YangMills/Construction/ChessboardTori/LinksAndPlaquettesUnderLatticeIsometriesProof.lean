import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice
namespace ChessboardSetup
variable (D : ChessboardSetup)
theorem faceCorners_eq_cornerSet (p : D.Plaquette) : D.faceCorners p = p.cornerSet := by
  rfl
theorem imageFace_eq (hmove : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes D.mesh)
    (r : D.LatticeSym) (p : D.Plaquette) : D.imageFace r p = r.plaquetteMap p := by
  obtain ⟨huniq, hcorners⟩ := (hmove r).1 p
  have hspec : D.faceCorners (D.imageFace r p) = r.pointMap '' D.faceCorners p :=
    Classical.epsilon_spec (p := fun q => D.faceCorners q = r.pointMap '' D.faceCorners p)
      ⟨r.plaquetteMap p, by simpa only [faceCorners_eq_cornerSet] using hcorners⟩
  simp only [faceCorners_eq_cornerSet] at hspec
  exact huniq.unique hspec hcorners
end ChessboardSetup
theorem LatticeSymmetryAction.statement_holds
    (hmoves : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes) :
    LatticeSymmetryAction.Statement := by
  intro D r
  obtain ⟨-, hlinks, hfaces⟩ := hmoves D.mesh D.mesh_pos
  have hmap := D.imageFace_eq hfaces r
  obtain ⟨hcorners, hbij, -, hact, hbary, -⟩ := hfaces r
  refine ⟨(hlinks.1 r).1.2, ?_, fun p => ?_, fun p => ?_, fun p U => ?_⟩
  · have : D.imageFace r = r.plaquetteMap := funext hmap
    rw [this]
    exact hbij.2
  · rw [hmap]
    simpa only [ChessboardSetup.faceCorners_eq_cornerSet] using (hcorners p).2
  · rw [hmap]
    exact hbary p
  · rw [hmap]
    exact congrFun (hact p) U
end YangMills.Construction.ChessboardTori
end
