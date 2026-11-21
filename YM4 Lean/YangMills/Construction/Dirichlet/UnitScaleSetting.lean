import YangMills.Construction.Dirichlet.LatticeCalculus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
variable {d : ℕ} {S ξ : ℝ}
structure UnitScaleSetting (d L : ℕ) (lower upper : ℝ) (K m level : ℕ) extends
    toBlockSetting : BlockSetting d L lower upper (Torus.unitSide L m K level) where
  t_eq : t = level
  level_le : level ≤ K
  ξ_eq : ξ = Torus.unitSpacing L level
  lower_pos : 0 < lower
namespace BlockSetting
variable {L : ℕ} {lower upper : ℝ} (𝒮 : BlockSetting d L lower upper S)
def siteBox (y : Torus.PeriodicTorus d S) (s : ℝ) : Set (Torus.PeriodicTorus d S) :=
  {x | x ∈ Torus.spacingLattice d S 𝒮.ξ ∧ Torus.supNorm (x - y) ≤ s}
end BlockSetting
abbrev TwoTensorField (d : ℕ) (S ξ : ℝ) : Type := Fin d → Fin d → LatticeSite d S ξ → ℝ
def secondDiff (f : LatticeSite d S ξ → ℝ) : TwoTensorField d S ξ :=
  fun μ ν => forwardDiff μ (forwardDiff ν f)
def twoTensorDiv (Φ : TwoTensorField d S ξ) : LatticeSite d S ξ → ℝ :=
  fun x => ∑ μ, ∑ ν, backwardDiff μ (backwardDiff ν (Φ μ ν)) x
def twoTensorInner (Φ Ψ : TwoTensorField d S ξ) : ℝ := ∑ μ, ∑ ν, innerSum (Φ μ ν) (Ψ μ ν)
def unitScaleHolder (σ : ℝ) (D : LatticeSite d S ξ → ℝ) : ℝ := scaledHolderSeminorm σ 1 D
end Dirichlet
end YangMills.Construction
