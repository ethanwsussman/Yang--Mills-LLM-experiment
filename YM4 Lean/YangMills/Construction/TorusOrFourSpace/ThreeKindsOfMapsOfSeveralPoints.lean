import YangMills.Construction.TorusOrFourSpace.PermutationsDiagonalActionsTranslationsAndInvariance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
open PeriodicLattice (SignedFrame)
namespace TupleMap
variable {D : Params} {E : Kind} {n : ℕ+}
def symm : TupleMap D E n → TupleMap D E n
  | permute τ => permute τ⁻¹
  | frameDiag w => frameDiag (frameInv w)
  | translate v => translate (subPt D E (E.quotMap D 0) v)
end TupleMap
namespace TupleMapFacts
variable (D : Params) (E : Kind)
def LiftIndependent : Prop :=
  (∀ (w : SignedFrame) (y : E.Pt D) (x : Fin 4 → ℝ), IsLift D E y x →
    frameAct D E w y = E.quotMap D (w.actOnVector x)) ∧
  ∀ (y v : E.Pt D) (x b : Fin 4 → ℝ), IsLift D E y x → IsLift D E v b →
    addPt D E y v = E.quotMap D (x + b) ∧
      subPt D E y v = E.quotMap D (x - b)
variable {D E} {n : ℕ+}
def LiftsToSignedPerm (ψ : TupleMap D E n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (4 * (n : ℕ)))) (ε : Fin (4 * (n : ℕ)) → ℤˣ) (b : Coords n)
    (A : Coords n →ₗ[ℝ] Coords n),
    (∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ)) ∧
    (∀ x, ψ.actPts (Tuple.proj D E x) =
      Tuple.proj D E (A x + b)) ∧
    (∀ x, Real.sqrt (∑ j, A x j ^ 2) = Real.sqrt (∑ j, x j ^ 2)) ∧
    A '' Tuple.periodSet D E n = Tuple.periodSet D E n
def IsIsometricEquiv (ψ : TupleMap D E n) : Prop :=
  Function.Bijective ψ.actPts ∧
  (∀ y y', Tuple.tupleDist D E (ψ.actPts y) (ψ.actPts y') =
    Tuple.tupleDist D E y y') ∧
  Function.LeftInverse ψ.symm.actPts ψ.actPts ∧
  Function.RightInverse ψ.symm.actPts ψ.actPts ∧
  ψ.actPts '' pairwiseDistinct D E n = pairwiseDistinct D E n
def PreservesFunctionClasses (ψ : TupleMap D E n) : Prop :=
  (∀ F : E.Tuple D n → ℂ,
    Tuple.supportT D E (F ∘ ψ.actPts) = ψ.actPts ⁻¹' Tuple.supportT D E F) ∧
  (∀ (ν : ℕ) (F : E.Tuple D n → ℂ), Tuple.IsClassC D E ν F →
    Tuple.IsClassC D E ν (F ∘ ψ.actPts) ∧
      Tuple.cNorm D E ν (F ∘ ψ.actPts) = Tuple.cNorm D E ν F) ∧
  Tuple.IsOpenT D E (pairwiseDistinct D E n) ∧
  (∀ F ∈ Tuple.testFns D E (pairwiseDistinct D E n),
    F ∘ ψ.actPts ∈ Tuple.testFns D E (pairwiseDistinct D E n)) ∧
  (∀ F G : E.Tuple D n → ℂ,
    (F + G) ∘ ψ.actPts = F ∘ ψ.actPts + G ∘ ψ.actPts) ∧
  ∀ (c : ℂ) (F : E.Tuple D n → ℂ), (c • F) ∘ ψ.actPts = c • (F ∘ ψ.actPts)
def PreservesTuples (ψ : TupleMap D E n) : Prop :=
  (∀ f ∈ sepC1Tuples D E (n : ℕ), ψ.actFns f ∈ sepC1Tuples D E (n : ℕ)) ∧
  (∀ f : FnTuple D E (n : ℕ),
    (∀ i, Tuple.IsSmoothT D E (Tuple.ofSingle D E fun y => (f i y : ℂ))) →
      ∀ i, Tuple.IsSmoothT D E
        (Tuple.ofSingle D E fun y => ((ψ.actFns f i y : ℝ) : ℂ))) ∧
  (∀ f : Fin (n : ℕ) → E.Pt D → ℂ,
    (∀ i, Tuple.IsSmoothT D E (Tuple.ofSingle D E (f i))) →
      ∀ i, Tuple.IsSmoothT D E (Tuple.ofSingle D E (ψ.actFns f i))) ∧
  ∀ f : Fin (n : ℕ) → E.Pt D → ℂ,
    Tuple.tensorProd D E (ψ.actFns f) =
        Tuple.tensorProd D E f ∘ ψ.symm.actPts ∧
      ψ.symm.actFns (ψ.actFns f) = f
def Claim : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ+) (ψ : TupleMap D E n),
    LiftIndependent D E ∧ LiftsToSignedPerm ψ ∧ IsIsometricEquiv ψ ∧
      PreservesFunctionClasses ψ ∧ PreservesTuples ψ
end TupleMapFacts
end YangMills.Construction.PeriodicSpace.Kind
