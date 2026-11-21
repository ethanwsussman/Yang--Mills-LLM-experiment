import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields
variable {m : ℕ}
def wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : Measure (TorusField m) :=
  (fieldHaar m).withDensity fun W =>
    ENNReal.ofReal (Real.exp (-β * wilsonAction Finset.univ W) /
      ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar m))
def curvatureObservable [NeZero m] (h : PlaquetteWeight m) (W : TorusField m) : ℝ :=
  ∑ p ∈ plaquettesIn Finset.univ, h p * plaquetteEnergyOf W p
def connectedCurvature (β : ℝ) (m : ℕ) [NeZero m] {k : ℕ} (h : Fin k → PlaquetteWeight m) : ℂ :=
  Cumulants.mixedCumulant (wilsonLaw β m) fun i => curvatureObservable (h i)
def SupportsSeparated (L t : ℕ) (d : ℝ) (h h' : PlaquetteWeight m) : Prop :=
  ∀ p p' : OrientedPlaquette m, h p.1 ≠ 0 → h' p'.1 ≠ 0 → d ≤ barycentreDist L t p.1 p'.1
end WeightedResponses
end YangMills.Construction
end
