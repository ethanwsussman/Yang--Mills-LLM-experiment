import YangMills.Construction.DirichletOperator.SettingsOfASeparatedSequence
import YangMills.Construction.Torus.OneFormsOfTheSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusDataKernel
variable {𝒮 : NestedRegions} {M R₁ : ℕ} {h : 𝒮.IsTorusData M R₁}
def SameEnds (b : 𝒮.FineBond) (c : h.toTorusData.Bond) : Prop :=
  (b.source : 𝒮.Point) = (c.source : h.toTorusData.Space) ∧
    (b.target : 𝒮.Point) = (c.target : h.toTorusData.Space)
def LongKernelMatchesData : Prop :=
  ∀ (𝒮 : NestedRegions) (M R₁ : ℕ) (h : 𝒮.IsTorusData M R₁)
    (B : Weighted.SeparatedChain h.toTorusData),
    𝒮.IsGapSeparated M R₁ → (𝒮.Ω 0).Nonempty → B.stage = 𝒮.Ω →
    NestedRegions.AgreesWithTorusData B →
    ∀ b ∈ 𝒮.bonds, ∀ b' ∈ 𝒮.bonds, ∀ c c' : ↥B.starBonds,
      SameEnds (h := h) b (c : h.toTorusData.Bond) →
      SameEnds (h := h) b' (c' : h.toTorusData.Bond) →
      NestedRegions.longOp (Set.indicator {b'} fun _ => 1) b =
        B.gradKernelGradAdjoint B.avgProj c c'
end YangMills.Construction.RegionSequence.TorusDataKernel
