import YangMills.Construction.DirichletOperator.SettingsOfASeparatedSequence
import YangMills.Construction.Torus.OperatorsOfTheSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusDataComparison
variable {𝒮 : NestedRegions} {M R₁ : ℕ} {h : 𝒮.IsTorusData M R₁}
def EqOnLayerSites (B : Weighted.SeparatedChain h.toTorusData) (ω : 𝒮.Coarse)
    (ω' : B.LayerFn) : Prop :=
  ∀ (y : ↥𝒮.allCentres) (y' : ↥B.allSites), (y : 𝒮.Point) = (y' : h.toTorusData.Space) → ω y = ω' y'
end YangMills.Construction.RegionSequence.TorusDataComparison
