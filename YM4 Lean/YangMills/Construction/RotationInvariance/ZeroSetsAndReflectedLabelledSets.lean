import YangMills.Construction.RotationInvariance.KernelOfTheHarmonicsTopHarmonicAndLinesOfThePlane
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube
noncomputable section
namespace YangMills.Construction.RealPlane
def reflectLabelled (L : Set RealPlane) (P : Set (RealPlane × realLabels)) :
    Set (RealPlane × realLabels) :=
  (fun p => (lineReflection L p.1, p.2)) '' P
end YangMills.Construction.RealPlane
namespace YangMills.Construction.EuclideanFunctionals
def topLabelledHarmonic (S : ConnFamily) (θ : RealPlane.openingAngles) (k : ℕ)
    (Y : Set (RealPlane × RealPlane.realLabels)) : ℂ :=
  labelledSetHarmonic S θ (-(topIndex S θ k : ℤ)) (2 * k) Y
structure IsVanishingSet (S : ConnFamily) (θ : RealPlane.openingAngles) (k : ℕ)
    (P : Set (RealPlane × RealPlane.realLabels)) : Prop where
  exists_size_le : ∃ m ≤ 2 * k, RealPlane.IsDistinctLabelledSet m P
  harmonic_vanishes : ∀ Y : Set (RealPlane × RealPlane.realLabels),
    RealPlane.IsDistinctLabelledSet (2 * k) Y → P ⊆ Y → topLabelledHarmonic S θ k Y = 0
end YangMills.Construction.EuclideanFunctionals
end
