import YangMills.Construction.Conventions.TorusBoundDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeveralComplexVariables
open ComplexVariables Coordinates TorusBoundNotation
variable {n : ℕ}
def affineParam {k : ℕ} (a : ComplexCoordinates n) (b : Fin k → ComplexCoordinates n) :
    ComplexCoordinates k → ComplexCoordinates n :=
  fun t => a + ∑ l, t l • b l
def ClosedUnderAlgebra (O : Set (ComplexCoordinates n)) (F H : ComplexCoordinates n → ℂ) :
    Prop :=
  (∀ c : ℂ, IsHolomorphicScalar O fun z => F z + c * H z) ∧
    IsHolomorphicScalar O (fun z => F z * H z) ∧ IsHolomorphicScalar O (expComp F)
def HolomorphicOnOpenSubsets (O : Set (ComplexCoordinates n)) (F : ComplexCoordinates n → ℂ) :
    Prop :=
  ∀ O₁ : Set (ComplexCoordinates n), IsOpen O₁ → O₁ ⊆ O → IsHolomorphicScalar O₁ F
def HolomorphicGluing (O : Set (ComplexCoordinates n)) : Prop :=
  ∀ (G : ComplexCoordinates n → ℂ) (𝒰 : Set (Set (ComplexCoordinates n))), (∀ U ∈ 𝒰, IsOpen U) →
    ⋃₀ 𝒰 = O → (∀ U ∈ 𝒰, IsHolomorphicScalar U G) → IsHolomorphicScalar O G
def HolomorphicPostcomp (O : Set (ComplexCoordinates n))
    (F : ComplexCoordinates n → ℂ) : Prop :=
  ∀ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V → DifferentiableOn ℂ g V → MapsTo F O V →
    IsHolomorphicScalar O (g ∘ F)
def HolomorphicAffinePrecomp (O : Set (ComplexCoordinates n)) (F : ComplexCoordinates n → ℂ) :
    Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (a : ComplexCoordinates n) (b : Fin k → ComplexCoordinates n),
    IsOpen (affineParam a b ⁻¹' O) ∧
      IsHolomorphicScalar (affineParam a b ⁻¹' O) (F ∘ affineParam a b)
def PartialDerivsHolomorphicComm (O : Set (ComplexCoordinates n))
    (F : ComplexCoordinates n → ℂ) : Prop :=
  (∀ i : Fin n, IsHolomorphicScalar O (coordDeriv i F)) ∧
    ∀ i j : Fin n,
      EqOn (coordDeriv i (coordDeriv j F)) (coordDeriv j (coordDeriv i F)) O
def MixedDerivWellFormed (O : Set (ComplexCoordinates n)) (F : ComplexCoordinates n → ℂ) :
    Prop :=
  MixedDerivFormed O F ∧ IsHolomorphicScalar O (mixedDeriv F) ∧
    ∀ l : List (Fin n), l.Perm (List.finRange n) →
      FormedSuccessively O F l ∧ EqOn (l.foldr coordDeriv F) (mixedDeriv F) O
def MixedDerivLinearLocal (O : Set (ComplexCoordinates n))
    (F H : ComplexCoordinates n → ℂ) : Prop :=
  (∀ c : ℂ,
    EqOn (mixedDeriv fun z => F z + c * H z)
      (fun z => mixedDeriv F z + c * mixedDeriv H z) O) ∧
    ∀ O₁ : Set (ComplexCoordinates n), IsOpen O₁ → O₁ ⊆ O → EqOn F H O₁ →
      EqOn (mixedDeriv F) (mixedDeriv H) O₁
def DerivsVanishOfIndependent (O : Set (ComplexCoordinates n))
    (F : ComplexCoordinates n → ℂ) : Prop :=
  ∀ i : Fin n, (∀ z ∈ O, ∀ w ∈ O, (∀ j, j ≠ i → z j = w j) → F z = F w) →
    EqOn (coordDeriv i F) 0 O ∧ EqOn (mixedDeriv F) 0 O
def PrincipalLogProperties : Prop :=
  DifferentiableOn ℂ principalLog discAtOne ∧
    (∀ u ∈ discAtOne, Complex.exp (principalLog u) = u) ∧ principalLog 1 = 0 ∧
    ∀ u : ℂ, ‖u - 1‖ ≤ 1 / 2 → ‖principalLog u‖ ≤ Real.log 2
def HolomorphicCalculusRules : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ O : Set (ComplexCoordinates n), IsOpen O →
    ∀ F H : ComplexCoordinates n → ℂ, IsHolomorphicScalar O F → IsHolomorphicScalar O H →
      ClosedUnderAlgebra O F H ∧ HolomorphicOnOpenSubsets O F ∧ HolomorphicGluing O ∧
        HolomorphicPostcomp O F ∧ HolomorphicAffinePrecomp O F ∧
        PartialDerivsHolomorphicComm O F ∧ MixedDerivWellFormed O F ∧
        MixedDerivLinearLocal O F H ∧ DerivsVanishOfIndependent O F ∧
        PrincipalLogProperties
end YangMills.Construction.SeveralComplexVariables
end
