import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open Filter Set
namespace YangMills.Construction.SeveralComplexVariables
def realPoints (ι : Type) : Set (ι → ℂ) := {z | ∀ i, (z i).im = 0}
namespace HolomorphicCalculus
def HolomorphicOfLocallyUniformLimit : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (ι → ℂ)), IsOpen U →
    ∀ (F : ℕ → (ι → ℂ) → ℂ) (f : (ι → ℂ) → ℂ),
      (∀ n, IsHolomorphicOnOpen U (F n)) →
      (∀ z ∈ U, ∃ V : Set (ι → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        TendstoUniformlyOn F f atTop V) →
      IsHolomorphicOnOpen U f
def PartialDerivsHolomorphicAndCommute : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (ι → ℂ)), IsOpen U →
    ∀ f : (ι → ℂ) → ℂ, IsHolomorphicOnOpen U f →
      (∀ i : ι, IsHolomorphicOnOpen U (partialDeriv i f)) ∧
      ∀ i j : ι, ∀ z ∈ U,
        partialDeriv i (partialDeriv j f) z =
          partialDeriv j (partialDeriv i f) z
def MvPolynomialEvalIsEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (p : MvPolynomial ι ℂ),
    IsEntire fun z : ι → ℂ => MvPolynomial.eval z p
def AddMulDivHolomorphic : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (ι → ℂ)), IsOpen U →
    ∀ f g : (ι → ℂ) → ℂ, IsHolomorphicOnOpen U f → IsHolomorphicOnOpen U g →
      IsHolomorphicOnOpen U (fun z => f z + g z) ∧
      IsHolomorphicOnOpen U (fun z => f z * g z) ∧
      ((∀ z ∈ U, g z ≠ 0) → IsHolomorphicOnOpen U (fun z => f z / g z))
def CompHolomorphicAndChainRule : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (ι → ℂ)), IsOpen U →
    ∀ (κ : Type) [Fintype κ] [Nonempty κ] (V : Set (κ → ℂ)), IsOpen V →
      ∀ (φ : (ι → ℂ) → κ → ℂ) (f : (κ → ℂ) → ℂ),
        IsHolomorphicOnOpen U φ → MapsTo φ U V → IsHolomorphicOnOpen V f →
          IsHolomorphicOnOpen U (fun z => f (φ z)) ∧
          ∀ z ∈ U, ∀ i : ι,
            partialDeriv i (fun w => f (φ w)) z =
              ∑ k : κ, partialDeriv k f (φ z) *
                partialDeriv i (fun w => φ w k) z
def PartialDerivRealOfReal : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (ι → ℂ)), IsOpen U →
    ∀ f : (ι → ℂ) → ℂ, IsHolomorphicOnOpen U f →
      (∀ z ∈ U ∩ realPoints ι, (f z).im = 0) →
      ∀ i : ι, ∀ z ∈ U ∩ realPoints ι, (partialDeriv i f z).im = 0
def LogSeriesProperties : Prop :=
  DifferentiableOn ℂ logSeries (disc 1 1) ∧
  IsHolomorphicOnOpen {z : Unit → ℂ | z () ∈ disc 1 1} (fun z => logSeries (z ())) ∧
  (∀ w ∈ disc 1 1, Complex.exp (logSeries w) = w) ∧
  logSeries 1 = 0 ∧
  ∀ x : ℝ, 0 < x → x < 2 → (logSeries (x : ℂ)).im = 0
def Statement : Prop :=
  HolomorphicOfLocallyUniformLimit ∧ PartialDerivsHolomorphicAndCommute ∧
    MvPolynomialEvalIsEntire ∧ AddMulDivHolomorphic ∧
    CompHolomorphicAndChainRule ∧ PartialDerivRealOfReal ∧ LogSeriesProperties
end HolomorphicCalculus
end YangMills.Construction.SeveralComplexVariables
