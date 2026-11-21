import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TestSpaces
namespace DerivRules
def RulesOver (F : Type) [NormedField F] [NormedAlgebra ℝ F] : Prop :=
  ∀ (n : ℕ) (g : PointTuple n → F), ContDiff ℝ ∞ g →
    (∀ (i : Fin n) (μ : Fin 4) (x : PointTuple n),
      coordDeriv i μ g x = fderiv ℝ g x (Pi.single i (Pi.single μ 1))) ∧
    (∀ (i : Fin n) (μ : Fin 4), ContDiff ℝ ∞ (coordDeriv i μ g)) ∧
    (∀ α : MultiIdx4 n, ContDiff ℝ ∞ (multiDeriv α g)) ∧
    (∀ (i j : Fin n) (μ ν : Fin 4),
      coordDeriv i μ (coordDeriv j ν g) = coordDeriv j ν (coordDeriv i μ g)) ∧
    (∀ α γ : MultiIdx4 n, multiDeriv α (multiDeriv γ g) = multiDeriv (α + γ) g) ∧
    (∀ h : PointTuple n → F, ContDiff ℝ ∞ h → ∀ α : MultiIdx4 n,
      multiDeriv α (g + h) = multiDeriv α g + multiDeriv α h) ∧
    (∀ (c : F) (α : MultiIdx4 n),
      multiDeriv α (fun x => c * g x) = fun x => c * multiDeriv α g x) ∧
    (∀ U : Set (PointTuple n), IsOpen U → (∀ x ∈ U, g x = 0) →
      ∀ (α : MultiIdx4 n), ∀ x ∈ U, multiDeriv α g x = 0)
def LeibnizProp : Prop :=
  ∀ (n : ℕ) (χ : PointTuple n → ℝ) (φ : PointTuple n → ℂ), ContDiff ℝ ∞ χ → ContDiff ℝ ∞ φ →
    ∀ (α : MultiIdx4 n) (x : PointTuple n),
      multiDeriv α (fun y => (χ y : ℂ) * φ y) x =
        ∑ γ ∈ Finset.Icc 0 α,
          (idxChoose α γ : ℂ) * ((multiDeriv γ χ x : ℝ) : ℂ) * multiDeriv (α - γ) φ x
def ChooseSumProp : Prop :=
  ∀ (n : ℕ) (α : MultiIdx4 n), ∑ γ ∈ Finset.Icc 0 α, idxChoose α γ = 2 ^ idxOrder α
end DerivRules
open DerivRules in
def DerivRules.Combined : Prop :=
  RulesOver ℝ ∧ RulesOver ℂ ∧ LeibnizProp ∧ ChooseSumProp
end YangMills.Construction.TestSpaces
