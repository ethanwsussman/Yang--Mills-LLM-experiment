import YangMills.Construction.Lattice.SidesOfALinkMirrorOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BoxTorus
namespace MirrorLayers
open GridMirror TorusDescent
variable {L : ℕ} {κ : ℤ}
def IsMirrorLayering {d : CellGrid L κ} (g : d.GridSymmetry) (μ : Fin 4) (c : ℝ) (h : ℕ)
    (ℓ : d.GridPoint → ZMod (2 * h)) : Prop :=
  (∀ p : d.GridPoint, ℓ (p + gridStep L κ d.sideLengths μ) = ℓ p + 1) ∧
  (∀ (p : d.GridPoint) (ν : Fin 4), ν ≠ μ → ℓ (p + gridStep L κ d.sideLengths ν) = ℓ p) ∧
  (∀ p : d.GridPoint, ℓ (g.pointImage p) = 1 - ℓ p) ∧
  (∀ (p : d.GridPoint) (ν : Fin 4), ν ≠ μ →
    g.pointImage (p + gridStep L κ d.sideLengths ν) = g.pointImage p + gridStep L κ d.sideLengths ν) ∧
  (∀ p : d.GridPoint,
    g.pointImage (p + gridStep L κ d.sideLengths μ) = g.pointImage p - gridStep L κ d.sideLengths μ) ∧
  (∀ p : d.GridPoint, g.pointImage (g.pointImage p) = p) ∧
  (∀ p : d.GridPoint, (p : d.Space) ∈ posHalf d μ c ↔ (ℓ p).val ∈ Finset.Icc 1 h) ∧
  (∀ p : d.GridPoint, (p : d.Space) ∈ negHalf d μ c ↔ (ℓ p).val ∉ Finset.Icc 1 h) ∧
  (∀ p : d.GridPoint, ℓ p = 1 → g.pointImage p = p - gridStep L κ d.sideLengths μ) ∧
  (∀ p : d.GridPoint, ℓ p = (h : ZMod (2 * h)) → g.pointImage p = p + gridStep L κ d.sideLengths μ) ∧
  (∀ e : d.DirectedEdge, e.LiesIn (posHalf d μ c) ↔
    (e.source : d.Space) ∈ posHalf d μ c ∧ (e.target : d.Space) ∈ posHalf d μ c) ∧
  ∀ e : d.DirectedEdge, e.LiesIn (negHalf d μ c) ↔
    (e.source : d.Space) ∈ negHalf d μ c ∧ (e.target : d.Space) ∈ negHalf d μ c
def LayeringTheorem : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (g : d.GridSymmetry) (μ : Fin 4) (c : ℝ),
    IsMirrorReflection g μ c →
      ∃ h : ℕ, 2 ≤ h ∧ ∃ ℓ : d.GridPoint → ZMod (2 * h), IsMirrorLayering g μ c h ℓ
end MirrorLayers
end YangMills.Construction
end
