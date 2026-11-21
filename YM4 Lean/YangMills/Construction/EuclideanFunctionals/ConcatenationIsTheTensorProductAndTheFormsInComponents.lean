import YangMills.Construction.EuclideanFunctionals.CentredFunctionalOnSeparatedTensors
import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import YangMills.Construction.EuclideanFunctionals.RulesForTheTensorComponents
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MulTensor
open TensorCompRules (splitTerm)
def MulComponents : Prop :=
  ∀ F A : FreeSep, MulDefined F A →
    tensorCompZero (freeMul F A) = tensorCompZero F * tensorCompZero A ∧
    (∀ r, 1 ≤ r → tensorComp r (freeMul F A) = ∑ k, splitTerm F A r k) ∧
    ∀ (r : ℕ) (k : Fin (r + 1)), splitTerm F A r k ∈ sepTensorSpan r
def FlipConjComponents : Prop :=
  ∀ F ∈ finCombIn upperHalf,
    flipConj F ∈ finCombIn {x | x 3 < 0} ∧
    tensorCompZero (flipConj F) = conj (tensorCompZero F) ∧
    ∀ q, 1 ≤ q → ∀ x : TestSpaces.PointTuple q,
      tensorComp q (flipConj F) x = conj (tensorComp q F fun i => timeFlip (x i))
def innerTerm (S : ConnFamily) (F A : FreeSep) (p : ℕ × ℕ) : ℂ :=
  centeredOnTensor S (p.1 + p.2)
    (splitTerm (flipConj F) A (p.1 + p.2) ⟨p.1, by omega⟩)
def tensorWithInsert (F : FreeSep) (h : R4 → ℂ) (A : FreeSep) (q q' : ℕ) :
    TestSpaces.PointTuple (q + 1 + q') → ℂ :=
  TestSpaces.tensorFun
    (TestSpaces.tensorFun (tensorComp q (flipConj F))
      (tensorOfFns fun _ : Fin 1 => h))
    (tensorComp q' A)
def insertionTerm (S : ConnFamily) (F : FreeSep) (h : R4 → ℂ) (A : FreeSep) (p : ℕ × ℕ) : ℂ :=
  centeredOnTensor S (p.1 + 1 + p.2) (tensorWithInsert F h A p.1 p.2)
def InnerInComponents {s : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon s S) : Prop :=
  ∀ F ∈ finCombIn upperHalf, ∀ A ∈ finCombIn upperHalf,
    (Function.support (innerTerm S F A)).Finite ∧
      ⟪reconClass σ F, reconClass σ A⟫_ℂ = ∑ᶠ p, innerTerm S F A p
def InsertionInComponents (S : ConnFamily) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ F ∈ finCombIn {x | c < x 3}, ∀ A ∈ finCombIn {x | c < x 3},
    ∀ h ∈ C1c ℂ, supp h ⊆ {x | |x 3| < c} →
      (Function.support (insertionTerm S F h A)).Finite ∧
        insertion S F h A = ∑ᶠ p, insertionTerm S F h A p
def Holds : Prop :=
  ∀ (s : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon s S),
    MulComponents ∧ FlipConjComponents ∧
      InnerInComponents σ ∧ InsertionInComponents S
end YangMills.Construction.EuclideanFunctionals.MulTensor
