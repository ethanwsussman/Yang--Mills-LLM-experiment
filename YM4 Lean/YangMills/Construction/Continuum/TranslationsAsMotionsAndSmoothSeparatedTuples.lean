import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.SmoothSeparatedTuples
def pureTranslation (v : Fin 4 → ℝ) : Motions.RigidMotion := ⟨1, one_mem _, v⟩
theorem pureTranslation_toFun (v : Fin 4 → ℝ) :
    (pureTranslation v).toFun = SeparatedTuples.translate v := by
  funext u
  simp [Motions.RigidMotion.toFun, pureTranslation, SeparatedTuples.translate]
theorem pureTranslation_invFun (v u : Fin 4 → ℝ) :
    (pureTranslation v).invFun u = u - v := by
  simp [Motions.RigidMotion.invFun, pureTranslation]
section Functions
variable {n : ℕ} {F : Type*}
def translateFun (v : Fin 4 → ℝ) (φ : TestSpaces.PointTuple n → F) : TestSpaces.PointTuple n → F :=
  Motions.actOnFun (pureTranslation v) φ
theorem translateFun_apply (v : Fin 4 → ℝ) (φ : TestSpaces.PointTuple n → F)
    (x : TestSpaces.PointTuple n) :
    translateFun v φ x = φ fun i => x i - v := by
  simp only [translateFun, Motions.actOnFun, pureTranslation_invFun]
theorem translateFun_eq_shiftAct (v : Fin 4 → ℝ) (φ : TestSpaces.PointTuple n → F) :
    translateFun v φ = ConfigSpace.shiftAct v φ := by
  funext x
  rw [translateFun_apply, ConfigSpace.shiftAct_apply]
end Functions
def actOnScalar (_r : Motions.RigidMotion) (c : ℂ) : ℂ := c
def actOnTensorVal (r : Motions.RigidMotion) : {q : ℕ} → Motions.TensorVal ℂ q → Motions.TensorVal ℂ q
  | 0, c => actOnScalar r c
  | _ + 1, φ => Motions.actOnFun r φ
def translateTensorVal (v : Fin 4 → ℝ) {q : ℕ} (φ : Motions.TensorVal ℂ q) : Motions.TensorVal ℂ q :=
  actOnTensorVal (pureTranslation v) φ
def translateFamily {F : Type*} {q : ℕ} (v : Fin 4 → ℝ) (X : Fin q → (Fin 4 → ℝ) → F) :
    Fin q → (Fin 4 → ℝ) → F :=
  Motions.actOnTuple (pureTranslation v) X
def smoothSupportedIn (O : Set (Fin 4 → ℝ)) : Set SeparatedTuples.SepTuple :=
  {X | X ∈ SeparatedTuples.supportedIn O ∧ ∀ f ∈ X.1, ContDiff ℝ ∞ f}
def smoothSupportedInOfSize (O : Set (Fin 4 → ℝ)) (n : ℕ) : Set SeparatedTuples.SepTuple :=
  {X | X ∈ smoothSupportedIn O ∧ X.size = n}
end YangMills.Construction.SmoothSeparatedTuples
end
