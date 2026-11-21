import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.SpecificationOnObservables
import YangMills.Construction.InfiniteLattice.WilsonSpecificationAsAnOperatorAtEverySpacing
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open GibbsAtFixedSpacing (BorelProb)
variable {a : ℝ}
namespace GibbsEquations
def FacesUnderRescaling (ha : 0 < a) (W : LinkWindow a) : Prop :=
  (∀ p : ElementaryPlaquette a,
    Continuous (fun U : GaugeField a => faceEnergy U p) ∧
    (∀ U : GaugeField a, faceEnergy U p ∈ Set.Icc (0 : ℝ) 2) ∧
    pointToUnit ha '' p.cornerSet = (rescaledPlaquette ha p).cornerSet ∧
    (rescaledPlaquette ha p).center = inverseScaling ha p.center ∧
    pullToUnit ha (fun U : GaugeField a => faceEnergy U p) =
      (fun V : GaugeField 1 => faceEnergy V (rescaledPlaquette ha p)) ∧
    (p ∈ W.faces ↔ rescaledPlaquette ha p ∈ (W.rescaleToUnit ha).faces)) ∧
  ∀ q : ElementaryPlaquette 1, ∃! p : ElementaryPlaquette a, rescaledPlaquette ha p = q
def ConditionalAverageProperties (ha : 0 < a) (β : ℝ) (W : LinkWindow a) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    IsBoundedObservable (W.conditionalAverage ha β F) ∧
    W.IsInsensitive ha (W.conditionalAverage ha β F) ∧
    observableSupNorm (W.conditionalAverage ha β F) ≤ observableSupNorm F) ∧
  (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    W.conditionalAverage ha β (F + G) =
      W.conditionalAverage ha β F + W.conditionalAverage ha β G) ∧
  (∀ (z : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    W.conditionalAverage ha β (z • F) = z • W.conditionalAverage ha β F) ∧
  W.conditionalAverage ha β 1 = 1 ∧
  (∀ (Fs : ℕ → GaugeField a → ℂ) (F : GaugeField a → ℂ), (∀ n, IsBoundedObservable (Fs n)) →
    (∃ C : ℝ, ∀ n U, ‖Fs n U‖ ≤ C) → (∀ U, Tendsto (fun n => Fs n U) atTop (𝓝 (F U))) →
    ∀ U, Tendsto (fun n => W.conditionalAverage ha β (Fs n) U) atTop
      (𝓝 (W.conditionalAverage ha β F U))) ∧
  (∀ G F : GaugeField a → ℂ, IsBoundedObservable G → IsBoundedObservable F → W.IsInsensitive ha G →
    W.conditionalAverage ha β (G * F) = G * W.conditionalAverage ha β F) ∧
  (∀ G : GaugeField a → ℂ, IsBoundedObservable G →
    (W.IsInsensitive ha G ↔ Measurable[W.exteriorSigma] G)) ∧
  ∀ Q : Set AmbientSpace, (∀ b ∈ W.links, ¬ ((b.initial : AmbientSpace) ∈ Q ∧ (b.terminal : AmbientSpace) ∈ Q)) →
    ∀ G ∈ regionObservables a Q, W.IsInsensitive ha G
def DLREquations (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ ν : BorelProb a, IsGibbs β ν.1 ↔
    ∀ (W' : LinkWindow a) (F : GaugeField a → ℂ), IsBoundedObservable F →
      ν.integral (W'.conditionalAverage ha β F) = ν.integral F
def ConditionalAverageUnderRescaling (ha : 0 < a) (β : ℝ) (W : LinkWindow a) : Prop :=
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    pullToUnit ha (W.conditionalAverage ha β F) =
      (W.rescaleToUnit ha).conditionalAverage one_pos β (pullToUnit ha F)
def GibbsEquationsAndRescaling : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ W : LinkWindow a,
    FacesUnderRescaling ha W ∧
      ConditionalAverageProperties ha β W ∧
      DLREquations ha β ∧
      ConditionalAverageUnderRescaling ha β W
end GibbsEquations
end YangMills.Construction.InfiniteLattice
