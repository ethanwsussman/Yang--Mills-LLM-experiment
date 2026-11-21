import YangMills.Construction.GrowingTori.TensorsAndCentredLatticePolynomials
import YangMills.Construction.GrowingTori.TorusFunctionalsReadOnTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.LatticePolynomialCalculus
open TorusTransport TorusTransport.TestFunctionOrders
open CentredTensorMoments
open CentredTensorMoments.TorusFunctionals (linComb conjFn)
open BallTuples (FnTuple lipTuplesBall)
open SourcesAndGluing (ballR4)
structure Laws (D : Setup) (K m : ℕ+) (β : ℝ) (hβ : 0 < β) : Prop where
  map_linComb : ∀ (q n : ℕ) (c : Fin n → ℂ) (T : Fin n → OrderedTestFun q),
    (∀ b, IsBallTensorSum (D.latticeRadius m) q (T b)) → ∀ U,
      D.centredPolynomial K m β hβ (linComb c T) U =
        ∑ b, c b * D.centredPolynomial K m β hβ (T b) U
  mul_eq : ∀ (q q' : ℕ) (F : OrderedTestFun q) (F' : OrderedTestFun q'),
    IsBallTensorSum (D.latticeRadius m) q F →
    IsBallTensorSum (D.latticeRadius m) q' F' → ∀ U,
      D.centredPolynomial K m β hβ F U * D.centredPolynomial K m β hβ F' U =
        D.centredPolynomial K m β hβ (gradedTensor ⟨q, F⟩ ⟨q', F'⟩).2 U
  conj_eq : ∀ (q : ℕ) (F : OrderedTestFun q),
    IsBallTensorSum (D.latticeRadius m) q F → ∀ U,
      conj (D.centredPolynomial K m β hβ F U) =
        D.centredPolynomial K m β hβ (conjFn F) U
  tensor_eq : ∀ (q : ℕ) (f : Fin q → ComplexFun (Fin 4 → ℝ)),
    (∀ l, TestFunctions.IsBoundedFun (f l) ∧
      SourcesAndGluing.HasCompactSupportIn (f l) (ballR4 (D.latticeRadius m))) → ∀ U,
      D.centredPolynomial K m β hβ (tupleTensor f) U =
        ∏ l, (D.momentSetup K m β hβ).atCutoff.centredObservable
          (TestFunctions.periodize (D.momentSetup K m β hβ).side (f l)) U
  tensorMoment_linComb : ∀ (q n : ℕ) (c : Fin n → ℂ) (X : Fin n → FnTuple q),
    (∀ b, X b ∈ lipTuplesBall q (D.latticeRadius m)) →
      D.tensorMoment K m β hβ (linComb c fun b => realTupleTensor (X b)) =
        ∑ b, c b * D.centredOnFourSpace K m β (X b)
def Holds : Prop :=
  ∀ (D : Setup) (K m : ℕ+) (β : ℝ) (hβ : 0 < β), Laws D K m β hβ
end YangMills.Construction.ToriLimits.LatticePolynomialCalculus
end
