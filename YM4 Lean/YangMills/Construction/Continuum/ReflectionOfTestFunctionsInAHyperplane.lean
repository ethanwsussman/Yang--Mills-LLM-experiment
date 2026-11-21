import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.HyperplaneReflection
variable {q q' : ℕ}
def reflectArgs (μ : Fin 4) (c : ℝ) (x : TestSpaces.PointTuple q) : TestSpaces.PointTuple q :=
  fun i => ReflectionPositivity.AxisMirror.euclidReflect μ c (x i)
def conjReflect (μ : Fin 4) (c : ℝ) (F : TestSpaces.PointTuple q → ℂ) :
    TestSpaces.PointTuple q → ℂ :=
  fun x => conj (F (reflectArgs μ c x))
def conjReflectScalar (z : ℂ) : ℂ := conj z
def conjReflectVal (μ : Fin 4) (c : ℝ) : {q : ℕ} → Motions.TensorVal ℂ q → Motions.TensorVal ℂ q
  | 0, z => conjReflectScalar z
  | _ + 1, F => conjReflect μ c F
def valToFun : {q : ℕ} → Motions.TensorVal ℂ q → TestSpaces.PointTuple q → ℂ
  | 0, c => fun _ => c
  | _ + 1, F => F
def funToVal : {q : ℕ} → (TestSpaces.PointTuple q → ℂ) → Motions.TensorVal ℂ q
  | 0, f => f default
  | _ + 1, f => f
theorem valToFun_funToVal (f : TestSpaces.PointTuple q → ℂ) :
    valToFun (funToVal f) = f := by
  cases q with
  | zero => exact funext fun x => congrArg f (Subsingleton.elim _ _)
  | succ q => rfl
def tensorVal (F : Motions.TensorVal ℂ q) (F' : Motions.TensorVal ℂ q') :
    Motions.TensorVal ℂ (q + q') :=
  funToVal (TestSpaces.tensorFun (valToFun F) (valToFun F'))
theorem valToFun_tensorVal (F : Motions.TensorVal ℂ q) (F' : Motions.TensorVal ℂ q')
    (x : TestSpaces.PointTuple q) (x' : TestSpaces.PointTuple q') :
    valToFun (tensorVal F F') (TestSpaces.appendTuples x x') = valToFun F x * valToFun F' x' := by
  rw [tensorVal, valToFun_funToVal, TestSpaces.tensorFun_appendTuples]
end YangMills.Construction.HyperplaneReflection
