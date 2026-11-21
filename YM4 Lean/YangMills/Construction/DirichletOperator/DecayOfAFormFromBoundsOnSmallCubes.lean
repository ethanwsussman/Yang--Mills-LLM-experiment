import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.DirichletOperator
open Set
open RegionSequence RegionSequence.NestedRegions PartitionCubes Dirichlet
noncomputable section
namespace SmallCubeDecay
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
def weightFrom (Q : LevelCube 𝒮 M) (L : ℕ) (o : Q.system.setting.Point) (y' : 𝒮.Point) : ℝ :=
  Real.exp (-(YangMills.Construction.CubeOperators.chosenConstants L).δ *
    Q.torusDist o (Q.system.embed y'))
def PointwiseBounds (Q : LevelCube 𝒮 M) (L : ℕ) (y' : 𝒮.Point) (A₀ A₁ : ℝ)
    (u : Q.system.setting.FineBond → ℝ) : Prop :=
  ∀ o : Q.system.setting.Point, ∀ x : Q.system.setting.FineBond,
    AnchoredIn (cubeHalfSide o (𝒮.scale (Q.level + 1))) x →
      |u x| ≤ A₀ * weightFrom Q L o y' ∧
        YangMills.Construction.CubeTorus.tensorModulusAt (nablaOne u) x ≤ A₁ * weightFrom Q L o y'
def L2Bounds (Q : LevelCube 𝒮 M) (L : ℕ) (y' : 𝒮.Point) (A₀ A₁ : ℝ)
    (u : Q.system.setting.FineBond → ℝ) : Prop :=
  ∀ o : Q.system.setting.Point, ∀ ζ : Q.system.setting.FineSite → ℝ,
    VanishesOff (cubeHalfSide o (𝒮.scale (Q.level + 1))) ζ →
      ltwoBond (smulSiteBond ζ u) ≤ A₀ * supSite ζ * weightFrom Q L o y' ∧
        ltwoTensor (smulSiteTensor ζ (nablaOne u)) ≤ A₁ * supSite ζ * weightFrom Q L o y'
end SmallCubeDecay
end
end YangMills.Construction.DirichletOperator
