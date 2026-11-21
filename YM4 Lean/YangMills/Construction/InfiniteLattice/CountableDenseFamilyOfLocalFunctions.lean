import YangMills.Construction.InfiniteLattice.DataLatticeAndStatesOfTheSetOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.PeriodicGibbsStateSpace.DenseLocalFamily
variable {a : ℝ}
def IsRealValued (F : YangMills.Construction.InfiniteLattice.GaugeField a → ℂ) : Prop := ∀ U, (F U).im = 0
def IsUniformSeqLimit (𝒟 : Set (YangMills.Construction.InfiniteLattice.GaugeField a → ℂ))
    (F : YangMills.Construction.InfiniteLattice.GaugeField a → ℂ) : Prop :=
  ∃ H : ℕ → YangMills.Construction.InfiniteLattice.GaugeField a → ℂ, (∀ n, H n ∈ 𝒟) ∧ TendstoUniformly H F atTop
def IsCountableRealDense (𝒟 : Set (YangMills.Construction.InfiniteLattice.GaugeField a → ℂ)) : Prop :=
  𝒟.Countable ∧ 𝒟 ⊆ YangMills.Construction.GibbsAtFixedSpacing.continuousLocal a ∧ (∀ F ∈ 𝒟, IsRealValued F) ∧
    (fun _ => (1 : ℂ)) ∈ 𝒟 ∧
    (∀ F ∈ 𝒟, ∀ F' ∈ 𝒟, ∀ q : ℚ, (fun U => F U + (q : ℂ) * F' U) ∈ 𝒟) ∧
    ∀ F ∈ YangMills.Construction.GibbsAtFixedSpacing.continuousFns a, IsRealValued F → IsUniformSeqLimit 𝒟 F
def complexSpan (𝒟 : Set (YangMills.Construction.InfiniteLattice.GaugeField a → ℂ)) :
    Set (YangMills.Construction.InfiniteLattice.GaugeField a → ℂ) :=
  {H | ∃ F ∈ 𝒟, ∃ F' ∈ 𝒟, H = fun U => F U + Complex.I * F' U}
def denseFamilyStatement : Prop :=
  ∀ D : YangMills.Construction.PeriodicGibbsStateSpace.Params,
    (∃ 𝒟 : Set (YangMills.Construction.InfiniteLattice.GaugeField D.mesh → ℂ), IsCountableRealDense 𝒟) ∧
    ∀ 𝒟 : Set (YangMills.Construction.InfiniteLattice.GaugeField D.mesh → ℂ), IsCountableRealDense 𝒟 →
      (complexSpan 𝒟).Countable ∧
      complexSpan 𝒟 ⊆ YangMills.Construction.GibbsAtFixedSpacing.continuousLocal D.mesh ∧
      YangMills.Construction.GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures.IsSupNormDense (complexSpan 𝒟) ∧
      ∀ ν ν' : YangMills.Construction.GibbsAtFixedSpacing.BorelProb D.mesh,
        (∀ F ∈ 𝒟, ν.integral F = ν'.integral F) → ν = ν'
end YangMills.Construction.PeriodicGibbsStateSpace.DenseLocalFamily
