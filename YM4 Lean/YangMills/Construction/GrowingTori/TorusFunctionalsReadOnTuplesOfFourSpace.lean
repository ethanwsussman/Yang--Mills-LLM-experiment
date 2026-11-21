import YangMills.Construction.GrowingTori.CentredTensorMomentsOnATorusAndTheReflectionOfTestFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.CentredTensorMoments
open TorusTransport TorusTransport.TestFunctionOrders
open BallTuples (FnTuple R4Fun fnSupport lipTuplesBall subTupleOn)
open SourcesAndGluing (ballR4)
namespace TorusFunctionals
def linComb : {q : ℕ} → {n : ℕ} → (Fin n → ℂ) → (Fin n → OrderedTestFun q) →
    OrderedTestFun q
  | 0, _, c, T => ∑ b, c b * (T b : ℂ)
  | _ + 1, _, c, T => fun x => ∑ b, c b * T b x
def conjFn : {q : ℕ} → OrderedTestFun q → OrderedTestFun q
  | 0, F => conj (F : ℂ)
  | _ + 1, F => fun x => conj (F x)
def IsBallTupleCombination (ρ : ℝ) (A : GradedTestFun) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (X : Fin n → FnTuple A.1),
    (∀ b, X b ∈ lipTuplesBall A.1 ρ) ∧
      A.2 = linComb c fun b => realTupleTensor (X b)
def IsHalfSpaceComponent (ρ : ℝ) (μ : Fin 4) (c : ℝ) (f : R4Fun) : Prop :=
  fnSupport f ⊆ ballR4 ρ ∩ {x | c < x μ} ∧
    fnSupport (f ∘ (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ))) ⊆
      ballR4 ρ
def IsHalfSpaceCombination (ρ : ℝ) (μ : Fin 4) (c : ℝ) : (q : ℕ) → OrderedTestFun q → Prop
  | 0, _ => True
  | q + 1, F => ∃ (n : ℕ) (a : Fin n → ℂ) (X : Fin n → FnTuple (q + 1)),
      (∀ b, BallTuples.IsSepLipschitz (X b)) ∧
        (∀ b l, IsHalfSpaceComponent ρ μ c (X b l)) ∧
          F = linComb a fun b => realTupleTensor (X b)
def IsLatticeSymmetry (D : MomentData) (s : TorusPeriodization.euclideanMotions) : Prop :=
  (∃ k : Fin 4 → ℤ, ∀ x, (s : Equiv.Perm (Fin 4 → ℝ)) x = x + fun ν => D.atCutoff.spacing * (k ν : ℝ)) ∨
    (s : Equiv.Perm (Fin 4 → ℝ)) ∈ TorusLifts.hyperoctahedralGroupEuclidean ∨
      ∃ (μ : Fin 4) (c : ℝ) (k : ℤ), 2 * c = D.atCutoff.spacing * (k : ℝ) ∧
        s = BallPeriodization.hyperplaneReflection μ c
variable (D : MomentData)
def connectedReal (ρ : ℝ) {n : ℕ} (X : lipTuplesBall n ρ) : ℝ :=
  (BallTuples.connectedFn D.toParams D.K D.β X.1).re
def seqObservable (ρ : ℝ) {q₀ : ℕ} (F : TestSeq q₀) (U : D.BondField) : ℂ :=
  ∑ q, D.tensorObservable ρ (F q) U
def reflectionPairing (ρ : ℝ) {μ : Fin 4} {c : ℝ} (h : D.ReflectionIsSymmetry μ c) {q₀ : ℕ}
    (F F' : TestSeq q₀) : ℂ :=
  D.expectation fun U =>
    conj (D.compPullback h.toSymmetry (seqObservable D ρ F) U) *
      seqObservable D ρ F' U
def reflectedTensorProd (μ : Fin 4) (c : ℝ) {q₀ : ℕ} (F F' : TestSeq q₀) (q q' : Fin (q₀ + 1)) :
    GradedTestFun :=
  gradedTensor ⟨q, conjReflectSeq μ c F q⟩ ⟨q', F' q'⟩
structure ConnectedProperties (ρ : ℝ) (n : ℕ) : Prop where
  im_eq_zero : ∀ X ∈ lipTuplesBall n ρ,
    (BallTuples.connectedFn D.toParams D.K D.β X).im = 0
  perm_invariant : BallTuples.IsLipPermInvariant
    (connectedReal D ρ (n := n))
  disjoint_multilinear : BallTuples.IsLipDisjointMultilinear D.toParams
    (connectedReal D ρ (n := n))
  radius_indep : ∀ ρ', D.IsRadius ρ' → ∀ (X : FnTuple n) (h : X ∈ lipTuplesBall n ρ)
    (h' : X ∈ lipTuplesBall n ρ'),
    connectedReal D ρ ⟨X, h⟩ = connectedReal D ρ' ⟨X, h'⟩
def MomentPartitionExpansion (ρ : ℝ) : Prop :=
  ∀ (q : ℕ), ∀ X ∈ lipTuplesBall q ρ,
    ((D.functionalOfPeriodized X : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
        BallTuples.connectedFn D.toParams D.K D.β (subTupleOn X J)
structure TensorObservableCalculus (ρ : ℝ) : Prop where
  map_linComb : ∀ (q n : ℕ) (c : Fin n → ℂ) (T : Fin n → OrderedTestFun q),
    (∀ b, IsBallTensorSum ρ q (T b)) → ∀ U,
      D.tensorObservable ρ (linComb c T) U = ∑ b, c b * D.tensorObservable ρ (T b) U
  radius_indep : ∀ ρ', D.IsRadius ρ' → ∀ (q : ℕ) (F : OrderedTestFun q),
    IsBallTensorSum ρ q F → IsBallTensorSum ρ' q F →
      D.tensorObservable ρ F = D.tensorObservable ρ' F
  mul_eq : ∀ (q q' : ℕ) (F : OrderedTestFun q) (F' : OrderedTestFun q'),
    IsBallTensorSum ρ q F → IsBallTensorSum ρ q' F' → ∀ U,
      D.tensorObservable ρ F U * D.tensorObservable ρ F' U =
        D.tensorObservable ρ (gradedTensor ⟨q, F⟩ ⟨q', F'⟩).2 U
  conj_eq : ∀ (q : ℕ) (F : OrderedTestFun q), IsBallTensorSum ρ q F → ∀ U,
    conj (D.tensorObservable ρ F U) = D.tensorObservable ρ (conjFn F) U
  tensor_eq : ∀ (q : ℕ) (f : Fin q → ComplexFun (Fin 4 → ℝ)),
    (∀ l, TestFunctions.IsBoundedFun (f l) ∧ SourcesAndGluing.HasCompactSupportIn (f l) (ballR4 ρ)) →
    ∀ U, D.tensorObservable ρ (tupleTensor f) U =
      ∏ l, D.atCutoff.centredObservable (TestFunctions.periodize D.side (f l)) U
  moment_realTuple : ∀ (q : ℕ), ∀ X ∈ lipTuplesBall q ρ,
    D.centredTensorMoment ρ (realTupleTensor X) = ((D.functionalOfPeriodized X : ℝ) : ℂ)
  moment_linComb : ∀ (q n : ℕ) (c : Fin n → ℂ) (X : Fin n → FnTuple q),
    (∀ b, X b ∈ lipTuplesBall q ρ) →
      ∑ b, c b * ((D.functionalOfPeriodized (X b) : ℝ) : ℂ) =
        D.centredTensorMoment ρ (linComb c fun b => realTupleTensor (X b))
def ConnectedInvariance (ρ : ℝ) (n : ℕ) : Prop :=
  ∀ s, IsLatticeSymmetry D s → ∀ X ∈ lipTuplesBall n ρ,
    BallPeriodization.tupleComp X s ∈ lipTuplesBall n ρ →
      BallTuples.connectedFn D.toParams D.K D.β (BallPeriodization.tupleComp X s) =
        BallTuples.connectedFn D.toParams D.K D.β X
def ReflectionPositivity (ρ : ℝ) : Prop :=
  ∀ (μ : Fin 4) (c : ℝ), D.atCutoff.IsLinkLevel c →
    ∀ (q₀ : ℕ) (F F' : TestSeq q₀),
      (∀ q : Fin (q₀ + 1), IsHalfSpaceCombination ρ μ c q (F q)) →
      (∀ q : Fin (q₀ + 1), IsHalfSpaceCombination ρ μ c q (F' q)) →
      ∃ h : D.ReflectionIsSymmetry μ c,
        (∀ q q', IsBallTupleCombination ρ (reflectedTensorProd μ c F F' q q')) ∧
        reflectionPairing D ρ h F F' =
          ∑ q, ∑ q', D.centredTensorMoment ρ (reflectedTensorProd μ c F F' q q').2 ∧
        (reflectionPairing D ρ h F F).im = 0 ∧ 0 ≤ (reflectionPairing D ρ h F F).re
def Statement : Prop :=
  ∀ (D : MomentData) (ρ : ℝ), D.IsRadius ρ →
    (∀ n, 2 ≤ n → ConnectedProperties D ρ n) ∧ MomentPartitionExpansion D ρ ∧
      TensorObservableCalculus D ρ ∧ (∀ n, 2 ≤ n → ConnectedInvariance D ρ n) ∧
        ReflectionPositivity D ρ
end TorusFunctionals
end YangMills.Construction.CentredTensorMoments
end
