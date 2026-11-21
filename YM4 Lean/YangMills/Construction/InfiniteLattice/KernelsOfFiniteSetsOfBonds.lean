import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
variable {a : ℝ}
def IsRealLocalContinuous (W : GaugeField a → ℝ) : Prop :=
  (fun U => (W U : ℂ)) ∈ continuousLocal a
def linkKernel (Λ : Finset (Link a)) (hΛ : HasNoOppositePairs (Λ : Set (Link a)))
    (W : GaugeField a → ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  (∫ V, F (overwriteLinks hΛ V U) * (Real.exp (-W (overwriteLinks hΛ V U)) : ℂ)
      ∂LinkVariables.haarMeasure (Λ : Set (Link a))) /
    ((∫ V, Real.exp (-W (overwriteLinks hΛ V U)) ∂LinkVariables.haarMeasure (Λ : Set (Link a)) : ℝ) : ℂ)
def plaquettesTouching (Λ : Finset (Link a)) : Set (ElementaryPlaquette a) :=
  {p | ∃ e ∈ edgesOf p, e ∈ Λ ∨ e.opposite ∈ Λ}
def wilsonLinkEnergy (β : ℝ) (Λ : Finset (Link a)) (U : GaugeField a) : ℝ :=
  β * ∑ᶠ p ∈ plaquettesTouching Λ, faceEnergy U p
def wilsonLinkKernel (β : ℝ) (Λ : Finset (Link a))
    (hΛ : HasNoOppositePairs (Λ : Set (Link a))) (F : GaugeField a → ℂ)
    (U : GaugeField a) : ℂ :=
  linkKernel Λ hΛ (wilsonLinkEnergy β Λ) F U
theorem wilsonLinkKernel_apply (β : ℝ) (Λ : Finset (Link a))
    (hΛ : HasNoOppositePairs (Λ : Set (Link a))) (F : GaugeField a → ℂ)
    (U : GaugeField a) :
    wilsonLinkKernel β Λ hΛ F U =
      (∫ V, F (overwriteLinks hΛ V U) *
          (Real.exp (-β * ∑ᶠ p ∈ plaquettesTouching Λ,
            faceEnergy (overwriteLinks hΛ V U) p) : ℂ) ∂LinkVariables.haarMeasure (Λ : Set (Link a))) /
        ((∫ V, Real.exp (-β * ∑ᶠ p ∈ plaquettesTouching Λ,
            faceEnergy (overwriteLinks hΛ V U) p)
          ∂LinkVariables.haarMeasure (Λ : Set (Link a)) : ℝ) : ℂ) := by
  simp only [wilsonLinkKernel, linkKernel, wilsonLinkEnergy, neg_mul]
end YangMills.Construction.GibbsAtFixedSpacing
