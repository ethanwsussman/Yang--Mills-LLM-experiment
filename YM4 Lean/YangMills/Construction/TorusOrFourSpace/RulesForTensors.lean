import YangMills.Construction.Continuum.TensorProductOfTwoFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.PointsPairsAndMultiIndicesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Euclid
variable (D : Params) (n n' : ℕ+)
def tensorMul {n n' : ℕ+} (F : Kind.Tuple D Kind.euclidean n → ℂ)
    (H : Kind.Tuple D Kind.euclidean n' → ℂ) : Kind.Tuple D Kind.euclidean (n + n') → ℂ :=
  TorusTransport.TestFunctionOrders.tensorMulti n.pos n'.pos F H
def TensorFnOfOne : Prop :=
  ∀ f : Fin 1 → Kind.Pt D Kind.euclidean → ℂ,
    Kind.tensorFn D .euclidean f = Kind.Tuple.ofSingle D .euclidean (f 0)
def TensorMulOfTensorFns : Prop :=
  ∀ (f : Fin (n : ℕ) → Kind.Pt D Kind.euclidean → ℂ) (g : Fin (n' : ℕ) → Kind.Pt D Kind.euclidean → ℂ),
    tensorMul (n := n) (n' := n') D (Kind.tensorFn D .euclidean f) (Kind.tensorFn D .euclidean g) =
      Kind.tensorFn D .euclidean (Fin.append f g)
def TensorMulLinear : Prop :=
  (∀ H : Kind.Tuple D Kind.euclidean n' → ℂ,
    IsLinearMap ℂ fun F : Kind.Tuple D Kind.euclidean n → ℂ => tensorMul D F H) ∧
  ∀ F : Kind.Tuple D Kind.euclidean n → ℂ,
    IsLinearMap ℂ fun H : Kind.Tuple D Kind.euclidean n' → ℂ => tensorMul D F H
def TensorFnLinearInEntry : Prop :=
  ∀ (f : Fin (n : ℕ) → Kind.Pt D Kind.euclidean → ℂ) (i : Fin (n : ℕ)),
    IsLinearMap ℂ fun u : Kind.Pt D Kind.euclidean → ℂ =>
      Kind.tensorFn D .euclidean (Function.update f i u)
def TensorFnMul : Prop :=
  ∀ f h : Fin (n : ℕ) → Kind.Pt D Kind.euclidean → ℂ,
    Kind.tensorFn D .euclidean f * Kind.tensorFn D .euclidean h =
      Kind.tensorFn D .euclidean fun i => f i * h i
def SupportTensorMul : Prop :=
  ∀ (F : Kind.Tuple D Kind.euclidean n → ℂ) (H : Kind.Tuple D Kind.euclidean n' → ℂ),
    Kind.Tuple.supportT D .euclidean (tensorMul D F H) =
      Set.image2 (Euclid.appendPts D) (Kind.Tuple.supportT D .euclidean F)
        (Kind.Tuple.supportT D .euclidean H)
def SupportTensorFn : Prop :=
  ∀ f : Fin (n : ℕ) → Kind.Pt D Kind.euclidean → ℂ,
    Kind.Tuple.supportT (p := n) D .euclidean (Kind.tensorFn D .euclidean f) =
      Set.univ.pi fun i => Kind.supportQ D .euclidean (f i)
def DerivTensorMul : Prop :=
  ∀ (F : Kind.Tuple D Kind.euclidean n → ℂ) (H : Kind.Tuple D Kind.euclidean n' → ℂ),
    Kind.Tuple.IsSmoothT D .euclidean F → Kind.Tuple.IsSmoothT D .euclidean H →
      Kind.Tuple.IsSmoothT D .euclidean (tensorMul D F H) ∧
        ∀ (α : CoordIndex n) (α' : CoordIndex n'),
          Kind.Tuple.partialDeriv D .euclidean (Euclid.appendIdx α α')
              (tensorMul D F H) =
            tensorMul D (Kind.Tuple.partialDeriv D .euclidean α F)
              (Kind.Tuple.partialDeriv D .euclidean α' H)
def TensorFnSmooth : Prop :=
  ∀ f : Fin (n : ℕ) → Kind.Pt D Kind.euclidean → ℂ,
    (∀ i, Kind.Tuple.IsSmoothT D .euclidean
      (Kind.Tuple.ofSingle D .euclidean (f i))) →
    Kind.Tuple.IsSmoothT (p := n) D .euclidean (Kind.tensorFn D .euclidean f)
def NormTensorMulLE : Prop :=
  ∀ (F : Kind.Tuple D Kind.euclidean n → ℂ) (H : Kind.Tuple D Kind.euclidean n' → ℂ)
    (k : ℕ),
    Kind.Tuple.IsSmoothT D .euclidean F → Kind.Tuple.IsSmoothT D .euclidean H →
      Kind.Tuple.cNorm D .euclidean k F < ∞ →
      Kind.Tuple.cNorm D .euclidean k H < ∞ →
      Kind.Tuple.cNorm D .euclidean k (tensorMul D F H) ≤
        Kind.Tuple.cNorm D .euclidean k F *
          Kind.Tuple.cNorm D .euclidean k H
end Euclid
namespace TensorRules
open Euclid
def AllRules : Prop :=
  ∀ (D : Params) (n n' : ℕ+),
    TensorFnOfOne D ∧
    TensorMulOfTensorFns D n n' ∧
    TensorMulLinear D n n' ∧
    TensorFnLinearInEntry D n ∧
    TensorFnMul D n ∧
    SupportTensorMul D n n' ∧
    SupportTensorFn D n ∧
    DerivTensorMul D n n' ∧
    TensorFnSmooth D n ∧
    NormTensorMulLE D n n'
end TensorRules
end YangMills.Construction.PeriodicSpace
end
