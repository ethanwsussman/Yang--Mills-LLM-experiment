import YangMills.Construction.InfiniteLattice.ExponentialOfThePlaquetteSumOfAWindow
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CutoffLinks
open Set InfiniteLattice
variable {a : ℝ}
def spannedFace (y : LatticePoint a) (κ ι : Fin 4) (h : ι ≠ κ) : ElementaryPlaquette a :=
  if hlt : κ < ι then plaquetteOf y κ ι hlt
  else plaquetteOf y ι κ (lt_of_le_of_ne (not_lt.mp hlt) h)
def cyclicCorner (p : ElementaryPlaquette a) : Fin 4 → LatticePoint a :=
  ![p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
    p.corner + axisStep a p.highAxis]
def cyclicLink (p : ElementaryPlaquette a) : Fin 4 → Link a :=
  ![Link.forwardFrom p.corner p.lowAxis, Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
    (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite,
    (Link.forwardFrom p.corner p.highAxis).opposite]
def holonomyForward (U : GaugeField a) (p : ElementaryPlaquette a) (i : Fin 4) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (cyclicLink p i) * U (cyclicLink p (i + 1)) * U (cyclicLink p (i + 2)) *
    U (cyclicLink p (i + 3))
def holonomyBackward (U : GaugeField a) (p : ElementaryPlaquette a) (i : Fin 4) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (cyclicLink p (i - 1)).opposite * U (cyclicLink p (i - 2)).opposite *
    U (cyclicLink p (i - 3)).opposite * U (cyclicLink p i).opposite
def halfReTrace (g : Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)).re
def FacesOfWindows.Statement : Prop :=
  ∀ (d : CutoffData) (W : d.CutoffWindow),
    (∀ (x y : LatticePoint d.spacing) (μ μ' ν ν' : Fin 4) (h : μ < μ') (h' : ν < ν'),
      (plaquetteOf x μ μ' h = plaquetteOf y ν ν' h' → x = y ∧ μ = ν ∧ μ' = ν') ∧
      (Tower.FullSpace.faceCorners (plaquetteOf x μ μ' h) =
          Tower.FullSpace.faceCorners (plaquetteOf y ν ν' h') →
        x = y ∧ μ = ν ∧ μ' = ν')) ∧
    (∀ (x : LatticePoint d.spacing) (κ : Fin 4),
      {p : ElementaryPlaquette d.spacing | ContainsLink p (Link.forwardFrom x κ)} =
        {p | ∃ (ι : Fin 4) (h : ι ≠ κ),
          p = spannedFace x κ ι h ∨ p = spannedFace (x - axisStep d.spacing ι) κ ι h} ∧
      {p : ElementaryPlaquette d.spacing | ContainsLink p (Link.forwardFrom x κ)}.ncard = 6) ∧
    (W.faces.Finite ∧ W.faceCount ≤ 6 * W.links.ncard) ∧
    (W.links ∩ W.rim = ∅ ∧
      (W.links ∪ W.rim).Finite ∧
      ∀ p ∈ W.faces, ∀ b, ContainsLink p b → b ∈ W.links ∪ W.rim) ∧
    ((∀ U U' : GaugeField d.spacing,
        restrictField U W.links = restrictField U' W.links →
        restrictField U W.rim = restrictField U' W.rim →
        W.faceSum U = W.faceSum U') ∧
      (∀ (V : LinkVariables W.links) (ξ : LinkVariables W.rim),
        ∃ U : GaugeField d.spacing,
          restrictField U W.links = V ∧ restrictField U W.rim = ξ) ∧
      (∃! f : LinkVariables W.links × LinkVariables W.rim → ℝ,
        ∀ U : GaugeField d.spacing,
          f (restrictField U W.links, restrictField U W.rim) =
            Real.exp (d.coupling * W.faceSum U)) ∧
      (∀ U : GaugeField d.spacing,
        W.boltzmannFactor (restrictField U W.links) (restrictField U W.rim) =
          Real.exp (d.coupling * W.faceSum U)) ∧
      (∀ (V : LinkVariables W.links) (ξ : LinkVariables W.rim),
        0 < W.boltzmannFactor V ξ) ∧
      Continuous fun q : LinkVariables W.links × LinkVariables W.rim =>
        W.boltzmannFactor q.1 q.2) ∧
    (∀ (p : ElementaryPlaquette d.spacing) (U : GaugeField d.spacing),
      (∀ i : Fin 4, (cyclicLink p i).initial = cyclicCorner p i ∧
        (cyclicLink p i).terminal = cyclicCorner p (i + 1)) ∧
      ∀ i : Fin 4,
        halfReTrace (holonomyForward U p i) = halfReTrace (faceHolonomy U p) ∧
        halfReTrace (holonomyBackward U p i) = halfReTrace (faceHolonomy U p))
end YangMills.Construction.CutoffLinks
