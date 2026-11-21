import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.Forms
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure AveragingOpFacts (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  innerSum_eq : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ,
    innerSum g (𝒮.averagingOp f) =
      ∑ᶠ y ∈ 𝒮.centres, 𝒮.a (𝒮.centreIndex y) * 𝒮.centreSpacing y ^ ((d : ℤ) - 2) *
        𝒮.cellAverage g y * 𝒮.cellAverage f y
  abs_cellAverage_le : ∀ (f : LatticeSite d S 𝒮.ξ → ℝ), ∀ y ∈ 𝒮.centres,
    |𝒮.cellAverage f y| ≤
      min (supNormOn (𝒮.cell y) f) (𝒮.centreSpacing y ^ (-(d : ℝ) / 2) * siteNormOn (𝒮.cell y) f)
  sq_norm_decomp : ∀ (f : LatticeSite d S 𝒮.ξ → ℝ), ∀ y ∈ 𝒮.centres,
    siteNormOn (𝒮.cell y) f ^ 2 =
      siteNormOn (𝒮.cell y) (fun x => f x - 𝒮.cellAverage f y) ^ 2 +
        𝒮.centreSpacing y ^ d * |𝒮.cellAverage f y| ^ 2
  symm : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ,
    innerSum g (𝒮.averagingOp f) = innerSum (𝒮.averagingOp g) f
  nonneg : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, 0 ≤ innerSum f (𝒮.averagingOp f)
structure DirichletLaplacianFacts {ξ : ℝ} (W : Set (PeriodicTorus d S))
    (E : Set (LatticeBond d S ξ)) : Prop where
  innerSum_eq : ∀ f g : LatticeSite d S ξ → ℝ, VanishesOff W f → VanishesOff W g →
    innerSum g (dirichletLaplacian W E f) =
      ξ ^ ((d : ℤ) - 2) *
          ∑ᶠ b ∈ {b : LatticeBond d S ξ | (b.source : PeriodicTorus d S) ∈ W ∧
              (b.target : PeriodicTorus d S) ∈ W},
            (g b.target - g b.source) * (f b.target - f b.source) +
        ξ ^ ((d : ℤ) - 2) * ∑ᶠ b ∈ E, g (innerEnd W b) * f (innerEnd W b)
  apply_eq : ∀ f : LatticeSite d S ξ → ℝ, VanishesOff W f →
    ∀ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∈ W →
      dirichletLaplacian W E f x =
        (ξ ^ 2)⁻¹ *
          ((∑ᶠ x' ∈ {x' : LatticeSite d S ξ | IsNeighbor x x' ∧ (x' : PeriodicTorus d S) ∈ W},
              (f x - f x')) +
            (boundaryCount E x : ℝ) * f x)
  eq_latticeLaplacian : ∀ f : LatticeSite d S ξ → ℝ, VanishesOff W f →
    ∀ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∈ W →
      (∀ b : LatticeBond d S ξ, IsBoundaryBond W b → innerEnd W b = x → b ∈ E) →
        dirichletLaplacian W E f x = latticeLaplacian f x
structure BaseRegionFacts (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  isCellUnion : 𝒮.IsCellUnion (𝒮.Ω 0)
  rule_iff : ∀ E : Set (LatticeBond d S 𝒮.ξ),
    IsBoundaryRule (𝒮.Ω 0) (𝒮.Ω 0) E ↔ E = boundaryBonds (𝒮.Ω 0)
  dirichletLaplacian_eq : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    dirichletLaplacian (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) f =
      restrictTo (𝒮.Ω 0) (latticeLaplacian (restrictTo (𝒮.Ω 0) f))
  fullOperator_eq_blockOperator :
    𝒮.fullOperator = 𝒮.blockOperator (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0))
  fullOperator_apply : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    𝒮.fullOperator f =
      restrictTo (𝒮.Ω 0)
        (latticeLaplacian (restrictTo (𝒮.Ω 0) f) + 𝒮.averagingOp (restrictTo (𝒮.Ω 0) f))
def FormsAndOperatorsHold : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus S : ℝ), Parameters d L aMinus aPlus →
    ∀ 𝒮 : BlockSetting d L aMinus aPlus S,
      AveragingOpFacts 𝒮 ∧
      (∀ (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ)), 𝒮.IsCellUnion W →
        IsBoundaryRule (𝒮.Ω 0) W E → DirichletLaplacianFacts W E) ∧
      BaseRegionFacts 𝒮
end YangMills.Construction.Dirichlet.Forms
