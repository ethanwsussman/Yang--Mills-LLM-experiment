import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.TupleInequality
variable {D : MirrorData} (C : LinkLevel D)
def IsPosSideArgs {q : ℕ} (h : Fin q → D.Torus → ℝ) : Prop :=
  D.IsAdmissibleArg h ∧ ∀ l, D.supp (h l) ⊆ C.openSlab .pos
def tupleCombination {t : ℕ} (X : Fin t → D.FunTuple ℝ) (ζ : Fin t → ℂ) : D.FieldSpace → ℂ :=
  fun U => ∑ i, ζ i * MirrorData.FunTuple.prodOver (X i) fun f => ((D.centredObservable f U.1 : ℝ) : ℂ)
def pairSum {t : ℕ} (X : Fin t → D.FunTuple ℝ) (ζ : Fin t → ℂ) (σ : D.FunTuple ℝ → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (ζ i) * ζ j * σ (C.reflectTuple (X i) ++ X j)
def PairSumIsThetaForm {t : ℕ} (X : Fin t → D.FunTuple ℝ) (ζ : Fin t → ℂ)
    (σ : D.FunTuple ℝ → ℂ) : Prop :=
  pairSum C X ζ σ = C.thetaForm (tupleCombination X ζ) (tupleCombination X ζ) ∧
    0 ≤ C.thetaForm (tupleCombination X ζ) (tupleCombination X ζ)
def PositiveOnTuples (C : LinkLevel D) : Prop :=
  ∀ (t : ℕ), 1 ≤ t → ∀ (X : Fin t → D.FunTuple ℝ) (ζ : Fin t → ℂ),
    (∀ i, IsPosSideArgs C (X i).get) →
    (∀ i j, D.IsAdmissibleArg (C.reflectTuple (X i) ++ X j).get) ∧
    tupleCombination X ζ ∈ C.halfAlgebra .pos ∧
    PairSumIsThetaForm C X ζ (fun Y => ((D.gibbsFunctionalList Y : ℝ) : ℂ)) ∧
    PairSumIsThetaForm C X ζ D.truncatedFunctionalList
def selectTuple {q : ℕ} (h : Fin q → D.Torus → ℝ) (A : Finset (Fin q)) : D.FunTuple ℝ :=
  (A.sort (· ≤ ·)).map h
def PositiveOnSubtuples (C : LinkLevel D) : Prop :=
  ∀ (q : ℕ), 1 ≤ q → ∀ (f : Fin q → D.Torus → ℝ) (ζ : Finset (Fin q) → ℂ),
    IsPosSideArgs C f →
    0 ≤ ∑ A : Finset (Fin q), ∑ A' : Finset (Fin q), conj (ζ A) * ζ A' *
      D.truncatedFunctionalList
        (selectTuple (fun i => C.reflectFn (f i)) A ++ selectTuple f A')
def twoIndexMoment {q : ℕ} (f : Fin q → D.Torus → ℝ) (η η' : Fin q → ℕ) : ℝ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling fun U : D.BondField =>
    (∏ i, PeriodicLattice.smearedObservable (C.reflectFn (f i)) U ^ η i) *
      ∏ i', PeriodicLattice.smearedObservable (f i') U ^ η' i'
def PositiveOnPolynomials (C : LinkLevel D) : Prop :=
  ∀ (q : ℕ), 1 ≤ q → ∀ (f : Fin q → D.Torus → ℝ) (S : Finset (Fin q → ℕ))
    (ξ : (Fin q → ℕ) → ℂ), IsPosSideArgs C f →
    0 ≤ ∑ η ∈ S, ∑ η' ∈ S, conj (ξ η) * ξ η' * ((twoIndexMoment C f η η' : ℝ) : ℂ)
def Statement : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D), PositiveOnTuples C ∧ PositiveOnSubtuples C ∧ PositiveOnPolynomials C
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.TupleInequality
end
