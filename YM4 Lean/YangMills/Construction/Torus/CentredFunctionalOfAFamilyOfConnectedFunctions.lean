import YangMills.Construction.Cumulants.TwoMutuallyInversePolynomialSubstitutions
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient}
def ConnectedFamily.cumulantNumbers (S : ConnectedFamily s E) {q : ℕ}
    (f : separatedTuples s E q) : Cumulants.SubsetFamily q :=
  fun J => (S.blockFactor f J.1 : ℂ)
def CentredOfConnectedFamilyProperties : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (S : ConnectedFamily s E),
    S.centred ⟨nilTuple s E, nilTuple_mem_allSeparatedTuples⟩ = 1 ∧
    (∀ f : separatedTuples s E 1, S.centred (toAllSeparated f) = 0) ∧
    (∀ q : ℕ, 1 ≤ q → IsTupleMultilinear (ofLength S.centred q)) ∧
    IsTupleFunctional S.centred ∧
    (∀ (q : ℕ) (hq : 1 ≤ q) (f : separatedTuples s E q),
      (∀ J : Cumulants.NonemptyFinSubset q,
        Cumulants.expDerivFamily (S.cumulantNumbers f) J =
          (S.centred (toAllSeparated (restrictSeparated f J.1)) : ℝ)) ∧
      (connectedOf S.centred q f : ℂ) =
        S.cumulantNumbers f (Cumulants.univSubset hq)) ∧
    (∀ f : separatedTuples s E 1, connectedOf S.centred 1 f = 0) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s E n),
      connectedOf S.centred n f = S.fn n hn f) ∧
    (IsSymmetricTupleFunctional S.centred ↔
      ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleSymmetric (S.fn n hn)) ∧
    ∀ r : Pt s E ≃ Pt s E, IsDistIsometry r →
      (IsInvariantTupleFunctional r S.centred ↔
        ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleInvariant r (S.fn n hn))
end YangMills.Construction.AmbientPoints
