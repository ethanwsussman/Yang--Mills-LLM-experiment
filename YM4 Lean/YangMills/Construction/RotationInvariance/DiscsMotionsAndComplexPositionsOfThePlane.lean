import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.Rotation.FourthFirstCoordinatePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RealPlane
def openDiscAt (c : RealPlane) (r : ℝ) : Set RealPlane := {p | ‖p - c‖ < r}
def closedDiscAt (c : RealPlane) (r : ℝ) : Set RealPlane := {p | ‖p - c‖ ≤ r}
def liftFour (f : RealPlane → RealPlane) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ofComponents (f (planeComponent v)) (orthogonalComponent v)
theorem liftFour_add (q : RealPlane) (v : Fin 4 → ℝ) :
    liftFour (fun p => p + q) v = v + embedFour q := by
  funext k
  fin_cases k <;>
    simp [liftFour, ofComponents, planeComponent, orthogonalComponent, embedFour,
      PeriodicLattice.coordVec, add_comm]
end RealPlane
namespace EuclideanFunctionals
open RealPlane
def planeShift (q : RealPlane) : EuclidMotion := EuclidMotion.transl (embedFour q)
def rotateLin (θ : ℝ) : R4 →ₗ[ℝ] R4 where
  toFun := rotateFour θ
  map_add' v w := by
    funext k
    fin_cases k <;>
      simp [rotateFour, ofComponents, RealPlane.rotate, planeComponent, orthogonalComponent] <;> ring
  map_smul' c v := by
    funext k
    fin_cases k <;>
      simp [rotateFour, ofComponents, RealPlane.rotate, planeComponent, orthogonalComponent] <;> ring
def rotateMotion (θ : ℝ) : EuclidMotion where
  lin := rotateLin θ
  offset := 0
  lin_norm v := by
    simp only [TorusMetric.euclidNormVec, Fin.sum_univ_four]
    congr 1
    have hθ := Real.sin_sq_add_cos_sq θ
    simp [rotateLin, rotateFour, ofComponents, RealPlane.rotate, planeComponent, orthogonalComponent]
    linear_combination (v 3 ^ 2 + v 0 ^ 2) * hθ
theorem rotateMotion_apply (θ : ℝ) (v : R4) :
    rotateMotion θ v = rotateFour θ v :=
  add_zero _
theorem liftFour_reflectFirst (v : R4) : liftFour RealPlane.reflectFirst v = timeFlip v := by
  rw [timeFlip_apply]
  funext k
  fin_cases k <;>
    simp [liftFour, ofComponents, RealPlane.reflectFirst, planeComponent, orthogonalComponent,
      PeriodicLattice.coordVec]
  ring
end EuclideanFunctionals
end YangMills.Construction
