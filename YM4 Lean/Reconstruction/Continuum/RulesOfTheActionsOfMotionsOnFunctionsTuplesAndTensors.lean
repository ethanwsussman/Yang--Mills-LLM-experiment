import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Conventions.SpatialRotationDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.UpperHalfTensors
open TestSpaces Motions RotationNotation
def compMotion (r r' : RigidMotion) : RigidMotion :=
  ⟨r.mat * r'.mat, mul_mem r.mat_mem r'.mat_mem, r.mat.mulVec r'.shift + r.shift⟩
theorem compMotion_toFun (r r' : RigidMotion) (x : Point4) :
    (compMotion r r').toFun x = r.toFun (r'.toFun x) := by
  simp [compMotion, RigidMotion.toFun, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
end YangMills.Construction.UpperHalfTensors
