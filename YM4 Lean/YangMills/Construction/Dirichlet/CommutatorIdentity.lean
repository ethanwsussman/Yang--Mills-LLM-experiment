import YangMills.Construction.Dirichlet.CubeCoverAndWalks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
open Torus
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure VanishesForRule (𝒮 : BlockSetting d L aMinus aPlus S) (W : Set (PeriodicTorus d S))
    (E : Set (LatticeBond d S 𝒮.ξ)) (h : LatticeSite d S 𝒮.ξ → ℝ) : Prop where
  eq_zero_off : ∀ x : LatticeSite d S 𝒮.ξ,
    (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 → (x : PeriodicTorus d S) ∉ W → h x = 0
  eq_zero_innerEnd : ∀ b : LatticeBond d S 𝒮.ξ, IsBoundaryBond W b → b ∉ E → h (innerEnd W b) = 0
def CommutatorFormula (𝒮 : BlockSetting d L aMinus aPlus S) (W : Set (PeriodicTorus d S))
    (E : Set (LatticeBond d S 𝒮.ξ)) (h : LatticeSite d S 𝒮.ξ → ℝ) : Prop :=
  ∀ ψ : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff W ψ →
    ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
      𝒮.fullOperator (restrictTo (𝒮.Ω 0) (pointwiseMul h ψ)) x =
        pointwiseMul h (𝒮.blockOperator W E ψ) x - 𝒮.commutatorOp h ψ x
def CommutatorDivForm (𝒮 : BlockSetting d L aMinus aPlus S)
    (h : LatticeSite d S 𝒮.ξ → ℝ) : Prop :=
  ∀ ψ : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) ψ →
    ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
      𝒮.commutatorOp h ψ x =
        -(∑ μ, backwardDiff μ (fun z => forwardDiff μ h z * (ψ z + translateForward μ ψ z)) x) +
          ψ x * latticeLaplacian h x -
          𝒮.a (𝒮.centreIndex (𝒮.centreOf x)) * (𝒮.centreSpacing (𝒮.centreOf x) ^ 2)⁻¹ *
            (𝒮.ξ / 𝒮.centreSpacing (𝒮.centreOf x)) ^ d *
            ∑ᶠ x' ∈ {x' : LatticeSite d S 𝒮.ξ |
                (x' : PeriodicTorus d S) ∈ 𝒮.cell (𝒮.centreOf x)},
              (h x' - h x) * ψ x'
def CommutatorFormulasHold : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S) (W : Set (PeriodicTorus d S))
      (E : Set (LatticeBond d S 𝒮.ξ)) (h : LatticeSite d S 𝒮.ξ → ℝ),
      𝒮.IsCellUnion W → IsBoundaryRule (𝒮.Ω 0) W E → VanishesForRule 𝒮 W E h →
        CommutatorFormula 𝒮 W E h ∧ CommutatorDivForm 𝒮 h
end Dirichlet
end YangMills.Construction
