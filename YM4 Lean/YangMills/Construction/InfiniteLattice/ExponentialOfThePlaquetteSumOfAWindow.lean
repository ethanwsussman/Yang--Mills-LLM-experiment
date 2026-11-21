import YangMills.Construction.InfiniteLattice.WindowsOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks.CutoffData.CutoffWindow
variable {d : CutoffData} (W : d.CutoffWindow)
def fieldOf (V : LinkVariables W.links) (ξ : LinkVariables W.rim) : GaugeField d.spacing :=
  d.replaceOn W.subset_links V (d.extendByOne W.rim_subset_links ξ)
def faceSum (U : GaugeField d.spacing) : ℝ :=
  ∑ᶠ p ∈ W.faces,
    (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re
def boltzmannFactor (V : LinkVariables W.links) (ξ : LinkVariables W.rim) : ℝ :=
  Real.exp (d.coupling * W.faceSum (W.fieldOf V ξ))
end YangMills.Construction.CutoffLinks.CutoffData.CutoffWindow
