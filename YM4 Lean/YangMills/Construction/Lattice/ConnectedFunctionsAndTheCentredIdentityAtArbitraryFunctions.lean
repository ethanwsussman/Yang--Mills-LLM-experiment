import YangMills.Construction.Lattice.CentredMomentAndCentredFunctional
import YangMills.Construction.Lattice.KernelsLocalLogarithmAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ConnectedFunctions
namespace CouplingData
variable (D : CouplingData) {n : ℕ}
def ofRealFun (f : D.Torus → ℝ) : D.Torus → ℂ := fun x => (f x : ℂ)
def ofRealTuple (f : Fin n → D.Torus → ℝ) : Fin n → D.Torus → ℂ := fun i => D.ofRealFun (f i)
abbrev LatticePlaq : Type := PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)
def fieldObservable (f : D.Torus → ℝ) :
    PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ) → ℝ :=
  PeriodicLattice.observableOnFields (J := (D.K : ℕ)) f
def ObservableLinearAtBarycenters : Prop :=
  (∀ f : D.Torus → ℝ, Probability.IsBoundedRealRV (D.fieldObservable f)) ∧
    (range fun p : D.LatticePlaq => p.barycenter).Finite ∧
    (∀ f g : D.Torus → ℝ, (∀ p : D.LatticePlaq, f p.barycenter = g p.barycenter) →
      D.fieldObservable f = D.fieldObservable g) ∧
    IsLinearMap ℝ D.fieldObservable
def RealSymmMultilinearOn (n : ℕ) (R : Set (D.Torus → ℝ)) : Prop :=
  (∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) → (D.connected (D.ofRealTuple f)).im = 0) ∧
  (∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) → ∀ σ : Equiv.Perm (Fin n),
    D.connected (D.ofRealTuple (f ∘ σ)) = D.connected (D.ofRealTuple f)) ∧
  (∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) → ∀ (i : Fin n) (g g' : D.Torus → ℝ), g ∈ R → g' ∈ R →
    D.connected (D.ofRealTuple (Function.update f i (g + g'))) =
      D.connected (D.ofRealTuple (Function.update f i g)) +
        D.connected (D.ofRealTuple (Function.update f i g'))) ∧
  ∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) → ∀ (i : Fin n) (g : D.Torus → ℝ) (a : ℝ), g ∈ R →
    D.connected (D.ofRealTuple (Function.update f i (a • g))) =
      (a : ℂ) * D.connected (D.ofRealTuple (Function.update f i g))
def ComplexMultilinearOn (C : Set (D.Torus → ℂ)) (Ψ : (Fin n → D.Torus → ℂ) → ℂ) : Prop :=
  (∀ f : Fin n → D.Torus → ℂ, (∀ k, f k ∈ C) → ∀ (i : Fin n) (g g' : D.Torus → ℂ), g ∈ C → g' ∈ C →
    Ψ (Function.update f i (g + g')) = Ψ (Function.update f i g) + Ψ (Function.update f i g')) ∧
  ∀ f : Fin n → D.Torus → ℂ, (∀ k, f k ∈ C) → ∀ (i : Fin n) (g : D.Torus → ℂ) (a : ℂ), g ∈ C →
    Ψ (Function.update f i (a • g)) = a * Ψ (Function.update f i g)
def faceCumulant (p : Fin n → D.LatticePlaq) : ℂ :=
  PeriodicLattice.gibbsCumulant D.L D.m D.K D.coupling fun l U => PeriodicLattice.plaquetteCost U (p l)
def faceSum (f : Fin n → D.Torus → ℂ) : ℂ :=
  ∑ᶠ p : Fin n → D.LatticePlaq, (∏ l, f l (p l).barycenter) * D.faceCumulant p
def ConnectedPropertiesOn (n : ℕ) (R : Set (D.Torus → ℝ)) (C : Set (D.Torus → ℂ)) : Prop :=
  D.RealSymmMultilinearOn n R ∧
    (∀ f : Fin n → D.Torus → ℂ, (∀ k, f k ∈ C) → D.connected f = D.faceSum f) ∧
    (∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) →
      D.connected (D.ofRealTuple f) = D.markSum (D.ofRealTuple f)) ∧
    D.ComplexMultilinearOn C (D.connected (n := n))
def complexification (H : Set (D.Torus → ℝ)) : Set (D.Torus → ℂ) :=
  {f | markPart f 0 ∈ H ∧ markPart f 1 ∈ H}
def ComplexificationIsSubspace (H : Submodule ℝ (D.Torus → ℝ)) : Prop :=
  (∃ W : Submodule ℂ (D.Torus → ℂ), (W : Set (D.Torus → ℂ)) = D.complexification H) ∧
    ∀ f ∈ H, D.ofRealFun f ∈ D.complexification H
def EqOnRealTuples (R : Set (D.Torus → ℝ)) (Ψ : (Fin n → D.Torus → ℂ) → ℂ) : Prop :=
  ∀ f : Fin n → D.Torus → ℝ, (∀ k, f k ∈ R) →
    Ψ (D.ofRealTuple f) = D.connected (D.ofRealTuple f)
def UniqueExtensionOnComplexification (n : ℕ) (H : Set (D.Torus → ℝ)) : Prop :=
  D.ComplexMultilinearOn (D.complexification H) (D.connected (n := n)) ∧
    ∀ Ψ : (Fin n → D.Torus → ℂ) → ℂ, D.ComplexMultilinearOn (D.complexification H) Ψ →
      D.EqOnRealTuples H Ψ → ∀ f : Fin n → D.Torus → ℂ, (∀ k, f k ∈ D.complexification H) →
        Ψ f = D.connected f
def UniqueExtension (n : ℕ) : Prop :=
  ∀ Ψ : (Fin n → D.Torus → ℂ) → ℂ, D.ComplexMultilinearOn univ Ψ →
    D.EqOnRealTuples univ Ψ → Ψ = D.connected
def CentredIdentityOn (C : Set (D.Torus → ℂ)) : Prop :=
  ∀ (q : ℕ) (h : Fin q → D.Torus → ℂ), (∀ l, h l ∈ C) →
    D.centredMomentFn h = D.centredFunctionalFn h
def boundedRealFuns : Set (D.Torus → ℝ) := {f | TestFunctions.IsBoundedFun f}
def boundedComplexFuns : Set (D.Torus → ℂ) := {f | TestFunctions.IsBoundedFun f}
def BoundedComponents : Prop :=
  (∃ H : Submodule ℝ (D.Torus → ℝ), (H : Set (D.Torus → ℝ)) = D.boundedRealFuns ∧
    D.complexification H = D.boundedComplexFuns ∧ D.ComplexificationIsSubspace H ∧
    ∀ n : ℕ, 2 ≤ n → D.UniqueExtensionOnComplexification n H) ∧
  (∀ n : ℕ, 2 ≤ n →
    D.ConnectedPropertiesOn n D.boundedRealFuns D.boundedComplexFuns) ∧
  D.CentredIdentityOn D.boundedComplexFuns
def C1Components : Prop :=
  (∀ (q : ℕ) (h : Fin q → D.Torus → ℝ), (∀ l, D.IsC1 (h l)) →
    ReflectionPositivity.CutoffMirrors.MirrorData.PairwiseDisjointSupp (D := D.withDir 0) h →
      D.centredMomentFn (D.ofRealTuple h) = D.centredFunctionalFn (D.ofRealTuple h)) ∧
  ∀ h : D.Torus → ℝ, D.IsC1 h →
    TestFunctions.IsLipschitzFor (D.withDir 0).torusDist h
end CouplingData
open CouplingData
def CentredIdentityAtAllFunctions : Prop :=
  ∀ D : CouplingData, D.ObservableLinearAtBarycenters ∧
    (∀ n : ℕ, 2 ≤ n → D.ConnectedPropertiesOn n univ univ ∧
      (∀ H : Submodule ℝ (D.Torus → ℝ), D.ComplexificationIsSubspace H ∧
        D.UniqueExtensionOnComplexification n H) ∧
      D.UniqueExtension n) ∧
    D.CentredIdentityOn univ ∧
    (∀ f : D.Torus → ℝ, D.connected (fun _ : Fin 1 => D.ofRealFun f) =
      D.expect (D.obs (D.ofRealFun f))) ∧
    D.BoundedComponents ∧ D.C1Components
end YangMills.Construction.ConnectedFunctions
end
