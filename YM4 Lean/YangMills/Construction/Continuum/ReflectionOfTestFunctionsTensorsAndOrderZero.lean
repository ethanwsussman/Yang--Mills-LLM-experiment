import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.Continuum.TorusTransportData
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.TorusTransport.TestFunctionOrders
abbrev Configuration (q : ℕ) : Type := Fin q → Fin 4 → ℝ
abbrev OrderedTestFun : ℕ → Type
  | 0 => ℂ
  | q + 1 => ComplexFun (Configuration (q + 1))
abbrev TestFamily : Type := ∀ q : ℕ, OrderedTestFun q
def initPoints {p q : ℕ} (x : Configuration (p + q)) : Configuration p :=
  fun i => x (Fin.castAdd q i)
def tailPoints {p q : ℕ} (x : Configuration (p + q)) : Configuration q :=
  fun j => x (Fin.natAdd p j)
def tensor {p q : ℕ} (F : ComplexFun (Configuration p)) (G : ComplexFun (Configuration q)) :
    ComplexFun (Configuration (p + q)) :=
  fun x => F (initPoints x) * G (tailPoints x)
theorem tensor_append {p q : ℕ} (F : ComplexFun (Configuration p))
    (G : ComplexFun (Configuration q)) (x : Configuration p) (y : Configuration q) :
    tensor F G (Fin.append x y) = F x * G y := by apply _root_.YangMills.Construction.ConfigSpace.tensorFn_concatConfig <;> assumption
def prodTensor {q : ℕ} (f : Fin q → ComplexFun (Fin 4 → ℝ)) :
    ComplexFun (Configuration q) :=
  fun x => ∏ i, f i (x i)
theorem tensor_prodTensor {p q : ℕ} (f : Fin p → ComplexFun (Fin 4 → ℝ))
    (g : Fin q → ComplexFun (Fin 4 → ℝ)) :
    tensor (prodTensor f) (prodTensor g) = prodTensor (Fin.append f g) := by
  funext x
  simp [tensor, prodTensor, initPoints, tailPoints, Fin.prod_univ_add]
abbrev GradedTestFun : Type := Σ q : ℕ, OrderedTestFun q
def gradedTensor : GradedTestFun → GradedTestFun → GradedTestFun
  | ⟨0, c⟩, ⟨0, d⟩ => ⟨0, (c : ℂ) * (d : ℂ)⟩
  | ⟨0, c⟩, ⟨q + 1, F⟩ => ⟨q + 1, fun x => (c : ℂ) * F x⟩
  | ⟨p + 1, F⟩, ⟨0, c⟩ => ⟨p + 1, fun x => (c : ℂ) * F x⟩
  | ⟨p + 1, F⟩, ⟨q + 1, G⟩ => ⟨p + 1 + (q + 1), tensor (p := p + 1) (q := q + 1) F G⟩
theorem gradedTensor_fst (A B : GradedTestFun) :
    (gradedTensor A B).1 = A.1 + B.1 := by
  obtain ⟨_ | p, F⟩ := A <;> obtain ⟨_ | q, G⟩ := B <;>
    first | rfl | simp [gradedTensor]
abbrev AnyTuple (X : Type*) : Type _ := Σ q : ℕ, Fin q → X
def nilTuple (X : Type*) : AnyTuple X := ⟨0, Fin.elim0⟩
theorem fst_eq_zero_iff {X : Type*} (t : AnyTuple X) : t.1 = 0 ↔ t = nilTuple X := by
  constructor
  · obtain ⟨q, t⟩ := t
    rintro rfl
    exact congrArg (Sigma.mk 0) (Subsingleton.elim _ _)
  · rintro rfl
    rfl
end YangMills.Construction.TorusTransport.TestFunctionOrders
end
