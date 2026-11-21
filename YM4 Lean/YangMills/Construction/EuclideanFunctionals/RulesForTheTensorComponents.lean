import YangMills.Construction.EuclideanFunctionals.TensorsAndTensorComponentsOfTheFreeSpace
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TensorCompRules
def ConjRule : Prop :=
  ∀ F : FreeSep,
    tensorCompZero (freeConj F) = conj (tensorCompZero F) ∧
    ∀ n, 1 ≤ n → tensorComp n (freeConj F) = fun x => conj (tensorComp n F x)
def MotionRule : Prop :=
  ∀ (g : EuclidMotion) (F : FreeSep),
    tensorCompZero (g.actFree F) = tensorCompZero F ∧
    ∀ n, 1 ≤ n → ∀ x : TestSpaces.PointTuple n,
      tensorComp n (g.actFree F) x = tensorComp n F fun i => g⁻¹ (x i)
def splitTerm (F G : FreeSep) (n : ℕ) (k : Fin (n + 1)) : TestSpaces.PointTuple n → ℂ :=
  if (k : ℕ) = 0 then
    TestSpaces.scalarTensorLeft (tensorCompZero F) (tensorComp n G)
  else if (k : ℕ) = n then
    TestSpaces.scalarTensorRight (tensorComp n F) (tensorCompZero G)
  else fun x =>
    TestSpaces.tensorFun (tensorComp k F) (tensorComp (n - k) G)
      fun i => x (Fin.cast (Nat.add_sub_of_le (Nat.lt_succ_iff.1 k.2)) i)
def MulRule : Prop :=
  ∀ U V : Set R4, IsOpen U → IsOpen V → Disjoint U V →
    ∀ F ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V,
      tensorCompZero (freeMul F G) = tensorCompZero F * tensorCompZero G ∧
      ∀ n, 1 ≤ n → tensorComp n (freeMul F G) = ∑ k, splitTerm F G n k
def ComplexListRule : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ h : Fin k → R4 → ℂ, (∀ l, h l ∈ C1c ℂ) →
    (Pairwise fun l m => Disjoint (supp (h l)) (supp (h m))) →
    tensorComp k (complexList h) = tensorOfFns h ∧
    tensorCompZero (complexList h) = 0 ∧
    ∀ n, 1 ≤ n → n ≠ k → tensorComp n (complexList h) = 0
def Holds : Prop :=
  ConjRule ∧ MotionRule ∧ MulRule ∧ ComplexListRule
end YangMills.Construction.EuclideanFunctionals.TensorCompRules
