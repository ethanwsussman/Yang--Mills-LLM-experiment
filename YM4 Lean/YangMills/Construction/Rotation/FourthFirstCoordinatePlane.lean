import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.PositiveDefinite.HalfPlaneKernelDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPlane
def planeComponent (x : Fin 4 → ℝ) : RealPlane := !₂[x 3, x 0]
def orthogonalComponent (x : Fin 4 → ℝ) : RealPlane := !₂[x 1, x 2]
def ofComponents (y z : RealPlane) : Fin 4 → ℝ := ![y 1, z 0, z 1, y 0]
def embedFour (y : RealPlane) : Fin 4 → ℝ :=
  y 0 • PeriodicLattice.coordVec 3 + y 1 • PeriodicLattice.coordVec 0
def rotate (t : ℝ) (y : RealPlane) : RealPlane :=
  !₂[y 0 * Real.cos t - y 1 * Real.sin t, y 0 * Real.sin t + y 1 * Real.cos t]
def rotateFour (t : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ofComponents (rotate t (planeComponent x)) (orthogonalComponent x)
theorem ofComponents_planeComponent_orthogonalComponent (x : Fin 4 → ℝ) :
    ofComponents (planeComponent x) (orthogonalComponent x) = x := by
  funext i
  fin_cases i <;> simp [ofComponents, planeComponent, orthogonalComponent]
theorem planeComponent_ofComponents (y z : RealPlane) : planeComponent (ofComponents y z) = y := by
  ext i
  fin_cases i <;> simp [ofComponents, planeComponent]
theorem orthogonalComponent_ofComponents (y z : RealPlane) :
    orthogonalComponent (ofComponents y z) = z := by
  ext i
  fin_cases i <;> simp [ofComponents, orthogonalComponent]
theorem embedFour_eq_ofComponents (y : RealPlane) : embedFour y = ofComponents y 0 := by
  funext i
  fin_cases i <;> simp [embedFour, ofComponents, PeriodicLattice.coordVec]
end YangMills.Construction.RealPlane
end
