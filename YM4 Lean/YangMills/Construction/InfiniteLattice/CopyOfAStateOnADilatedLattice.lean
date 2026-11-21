import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.Dilation
variable {a c r : ℝ}
def ScaleBijectsCells (r : ℝ) (hsc : c = r * a) : Prop :=
  Function.Bijective (pointScale (a := a) r hsc) ∧
    Function.Bijective (linkScale (a := a) r hsc) ∧
    linkScale r hsc '' {l : Link a | l.IsPositivelyOriented} = {l : Link c | l.IsPositivelyOriented} ∧
    (∀ l : Link a, linkScale r hsc l.opposite = (linkScale r hsc l).opposite) ∧
    Function.Bijective (plaquetteScale (a := a) r hsc) ∧
    ∀ q : ElementaryPlaquette a, (plaquetteScale r hsc q).edges = q.edges.map (linkScale r hsc) ∧
      (plaquetteScale r hsc q).center = r • q.center
def GaugeFieldScaleHomeomorph (hr : 0 < r) (hsc : c = r * a) : Prop :=
  (∃ e : GaugeField a ≃ₜ GaugeField c, ⇑e = gaugeFieldScale hr hsc ∧
    ⇑e.symm = gaugeFieldScale (inv_pos.2 hr) (spacing_eq_inv_mul hr hsc)) ∧
    ∀ (q : ElementaryPlaquette a) (V : GaugeField a),
      faceHolonomy (gaugeFieldScale hr hsc V) (plaquetteScale r hsc q) = faceHolonomy V q ∧
        faceEnergy (gaugeFieldScale hr hsc V) (plaquetteScale r hsc q) = faceEnergy V q
def SmearedEnergyScales (E : Type) [NormedAddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (hr : 0 < r) (hsc : c = r * a) : Prop :=
  ∀ f : AmbientSpace → E, IsBoundedBorelCompactlySupported f →
    IsBoundedBorelCompactlySupported (fun x => f (r • x)) ∧
      ∀ V : GaugeField a,
        smearedEnergy f (gaugeFieldScale hr hsc V) = smearedEnergy (fun x => f (r • x)) V
def ScaledStateCumulants (hr : 0 < r) (hsc : c = r * a) : Prop :=
  ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
    IsProbabilityMeasure (scaledState hr hsc μ) ∧
      scaledState (inv_pos.2 hr) (spacing_eq_inv_mul hr hsc) (scaledState hr hsc μ) = μ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, IsBoundedBorelCompactlySupported (f i)) →
        smearedEnergyCumulant (scaledState hr hsc μ) f = smearedEnergyCumulant μ fun i x => f i (r • x)
def ScaledStateGibbsIff (hr : 0 < r) (hsc : c = r * a) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
    (IsGibbs β μ ↔ IsGibbs β (scaledState hr hsc μ))
def ScaledStateSymmetryIff (hr : 0 < r) (hsc : c = r * a) : Prop :=
  (∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
    (∀ v : LatticePoint a, IsSymmetricUnder μ (shift v) ↔
      IsSymmetricUnder (scaledState hr hsc μ) (shift (pointScale r hsc v))) ∧
      (IsPeriodicMeasure μ ↔ IsPeriodicMeasure (scaledState hr hsc μ))) ∧
    ∀ β : ℝ, 0 < β →
      BijOn (scaledState hr hsc) {μ : Measure (GaugeField a) | IsPeriodicGibbs β μ}
        {μ' : Measure (GaugeField c) | IsPeriodicGibbs β μ'}
def DilatedStateProperties : Prop :=
  ∀ a r c : ℝ, 0 < a → ∀ (hr : 0 < r) (hsc : c = r * a),
    ScaleBijectsCells r hsc ∧
      GaugeFieldScaleHomeomorph hr hsc ∧
      SmearedEnergyScales ℝ hr hsc ∧
      SmearedEnergyScales ℂ hr hsc ∧
      ScaledStateCumulants hr hsc ∧
      ScaledStateGibbsIff hr hsc ∧
      ScaledStateSymmetryIff hr hsc
end YangMills.Construction.InfiniteLattice.Dilation
