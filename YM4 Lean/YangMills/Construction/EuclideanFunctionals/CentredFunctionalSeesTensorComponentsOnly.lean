import YangMills.Construction.EuclideanFunctionals.CentredFunctionalOnSeparatedTensors
import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TensorComponents
def IsRealMultilinear (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (i : Fin n) (f : Fin n → R4 → ℝ) (g : R4 → ℝ),
    List.ofFn f ∈ sepN n → List.ofFn (Function.update f i g) ∈ sepN n →
    ∀ b b' : ℝ,
      List.ofFn (Function.update f i (b • f i + b' • g)) ∈ sepN n ∧
      centeredAt S (List.ofFn (Function.update f i (b • f i + b' • g))) =
        b * centeredAt S (List.ofFn f) +
          b' * centeredAt S (List.ofFn (Function.update f i g)) ∧
      ∀ hn : 2 ≤ n,
        ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn n hn)
            (List.ofFn (Function.update f i (b • f i + b' • g))) =
          b * ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn n hn) (List.ofFn f) +
            b' * ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn n hn)
              (List.ofFn (Function.update f i g))
def RespectsSameTensors (S : ConnFamily) : Prop :=
  ∀ F F' : FreeSep, SameTensors F F' → centeredFnFree S F = centeredFnFree S F'
def TensorRealizedAsSoleComp (q : ℕ) : Prop :=
  ∀ A ∈ sepTensorSpan q, ∃ F, HasSoleTensorComp q A F
def ValueIndepOfRealization (S : ConnFamily) (q : ℕ) : Prop :=
  ∀ A ∈ sepTensorSpan q, ∀ F F', HasSoleTensorComp q A F →
    HasSoleTensorComp q A F' → centeredFnFree S F = centeredFnFree S F'
def LinearOnSepSpan (S : ConnFamily) (q : ℕ) : Prop :=
  ∀ A ∈ sepTensorSpan q, ∀ A' ∈ sepTensorSpan q, ∀ z z' : ℂ,
    centeredOnTensor S q (z • A + z' • A') =
      z * centeredOnTensor S q A + z' * centeredOnTensor S q A'
def ValueAtScalar (S : ConnFamily) : Prop :=
  ∀ (A : TestSpaces.PointTuple 0 → ℂ) (e : TestSpaces.PointTuple 0), centeredOnTensor S 0 A = A e
def ValueAtSepTensor (S : ConnFamily) : Prop :=
  ∀ (q : ℕ) (h : Fin q → R4 → ℂ), ComplexComponents h →
    centeredOnTensor S q (tensorOfFns h) =
      centeredFnFree S (complexTuple h)
def CompsInSepSpan : Prop :=
  ∀ (F : FreeSep) (q : ℕ), tensorComp q F ∈ sepTensorSpan q
def EqFinsumOverOrders (S : ConnFamily) : Prop :=
  ∀ F : FreeSep,
    (Function.support fun q => centeredOnTensor S q (tensorComp q F)).Finite ∧
      centeredFnFree S F = ∑ᶠ q, centeredOnTensor S q (tensorComp q F)
def IsComplexMultilinear (S : ConnFamily) : Prop :=
  ∀ (n : ℕ) (i : Fin n) (b b' : ℂ) (h : Fin n → R4 → ℂ) (g : R4 → ℂ),
    ComplexComponents h → ComplexComponents (Function.update h i g) →
      (Pairwise fun k l => Disjoint (supp (Function.update h i (b • h i + b' • g) k))
        (supp (Function.update h i (b • h i + b' • g) l))) ∧
      centeredFnFree S (complexTuple (Function.update h i (b • h i + b' • g))) =
        b * centeredFnFree S (complexTuple h) +
          b' * centeredFnFree S (complexTuple (Function.update h i g))
def ExpandsOverReImParts (S : ConnFamily) : Prop :=
  ∀ (n : ℕ) (h : Fin n → R4 → ℂ), ComplexComponents h →
    centeredFnFree S (complexTuple h) =
      ∑ ε : Fin n → Fin 2, (Complex.I ^ ∑ l, (ε l : ℕ)) *
        centeredFnFree S (toFree (List.ofFn fun l => reOrImPart (ε l) (h l)))
def CenteredSeesTensorComps : Prop :=
  ∀ S : ConnFamily,
    IsRealMultilinear S ∧
    RespectsSameTensors S ∧
    ((∀ q, TensorRealizedAsSoleComp q ∧ ValueIndepOfRealization S q ∧
        LinearOnSepSpan S q) ∧
      ValueAtScalar S ∧ ValueAtSepTensor S ∧ CompsInSepSpan ∧
      EqFinsumOverOrders S) ∧
    IsComplexMultilinear S ∧ ExpandsOverReImParts S
end YangMills.Construction.EuclideanFunctionals.TensorComponents
