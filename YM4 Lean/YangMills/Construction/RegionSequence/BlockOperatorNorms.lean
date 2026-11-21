import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus
namespace RegionSequence.NestedRegions
inductive NormExponent where
  | two
  | sup
structure CutSpace (𝒮 : NestedRegions) where
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [module : Module ℝ Carrier]
  space : Submodule ℝ Carrier
  cut : 𝒮.allCentres → Carrier → Carrier
  twoNorm : Carrier → ℝ
  supNorm : Carrier → ℝ
attribute [instance] CutSpace.addCommGroup CutSpace.module
variable {𝒮 : NestedRegions}
def CutSpace.pNorm (X : CutSpace 𝒮) : NormExponent → X.Carrier → ℝ
  | .two => X.twoNorm
  | .sup => X.supNorm
variable (𝒮)
def formCutSpace : CutSpace 𝒮 where
  Carrier := 𝒮.FineBond → ℝ
  space := 𝒮.oneForms
  cut y := cellCutBond (y : 𝒮.Point)
  twoNorm := ltwoBond
  supNorm := linftyBond
def supportedTensors (r : ℕ) : Submodule ℝ (𝒮.Tensor r) where
  carrier := {J | ∀ ν, AnchorSupported (𝒮.Ω 0) (J ν)}
  add_mem' := fun hJ hK ν b hb => by simp [hJ ν b hb, hK ν b hb]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c _ hJ ν b hb => by simp [hJ ν b hb]
def tensorCutSpace (r : ℕ) : CutSpace 𝒮 where
  Carrier := 𝒮.Tensor r
  space := 𝒮.supportedTensors r
  cut y := cellCutTensor (y : 𝒮.Point)
  twoNorm := ltwoTensor
  supNorm := linftyTensor
variable {𝒮}
variable {X X' : CutSpace 𝒮}
def cellNorm (p : NormExponent) (O : X'.space →ₗ[ℝ] X.space) (y y' : 𝒮.allCentres) : ℝ :=
  sSup {a | ∃ f : X'.space, (f : X'.Carrier) = X'.cut y' f ∧ X'.pNorm p f ≤ 1 ∧
    a = X.pNorm p (X.cut y (O f))}
end RegionSequence.NestedRegions
end YangMills.Construction
