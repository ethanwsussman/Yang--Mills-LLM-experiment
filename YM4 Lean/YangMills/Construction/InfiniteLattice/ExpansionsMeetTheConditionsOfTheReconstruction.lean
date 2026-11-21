import YangMills.Construction.InfiniteLattice.ConditionsOfTheReconstructionAtALatticeMirror
import YangMills.Construction.InfiniteLattice.DataOfTheThreePictures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace MirrorExpansions
structure IsPictureExpansion (a : Spacing) {ι : Type} [Fintype ι] (row : ReflectionPictureData ι)
    (n : Point) (l : ℝ) (k : ℕ) : Prop where
  plane_normal : row.plane.normal = n
  midPlane_normal : row.midPlane.normal = n
  plane_isLatticeMirror : row.plane.IsLatticeMirror (a : ℝ)
  midPlane_isLatticeMirror : row.midPlane.IsLatticeMirror (a : ℝ)
  normalStep_outward : row.plane.IsOutwardNormalStep (a : ℝ) row.normalStep
  euclidDot_normalStep : euclidDot n row.normalStep = l
  midPlane_isMid : row.midPlane.IsMidPlaneOf (a : ℝ) row.plane row.normalStep
  tangentStep_mem : ∀ i, row.tangentStep i ∈ InfiniteLattice.latticeSubgroup (a : ℝ)
  euclidDot_tangentStep : ∀ i, euclidDot n (row.tangentStep i) = 0
  hyps : MirrorReconstructionHyps (a : ℝ) row.plane row.normalStep row.midPlane
    row.tangentStep
  card_eq : Fintype.card ι = k
def IsNextMirror (a : ℝ) (n : Point) (P P' : NormalHyperplane) : Prop :=
  P' ∈ NormalHyperplane.mirrorsWithNormal a n ∧ P.level < P'.level ∧
    ∀ R ∈ NormalHyperplane.mirrorsWithNormal a n, ¬(P.level < R.level ∧ R.level < P'.level)
def MidPlaneIsLatticeMirror : Prop :=
  ∀ (a : Spacing) (P : NormalHyperplane) (v : Point), P.IsLatticeMirror (a : ℝ) →
    P.IsOutwardNormalStep (a : ℝ) v → (P.midPlane v).IsLatticeMirror (a : ℝ)
def PictureExpansionsHold : Prop :=
  ∀ (a : Spacing) (μ ν : Direction) (hne : μ ≠ ν) (c : ℝ)
    (hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ)),
    IsPictureExpansion a (linkPicture a μ) (basisVector μ) (a : ℝ) 3 ∧
      IsPictureExpansion a (sitePicture a μ) (basisVector μ) (a : ℝ) 3 ∧
      IsPictureExpansion a (diagonalPicture a μ ν hne c hc)
        (basisVector μ + basisVector ν) (2 * (a : ℝ)) 1
def MidPlanesOfAxialAndDiagonal : Prop :=
  ∀ (a : Spacing) (μ ν : Direction) (hne : μ ≠ ν),
    (∀ t : ℝ, (NormalHyperplane.axial μ t).IsEdgeMirror (a : ℝ) →
      (NormalHyperplane.axial μ (t + (a : ℝ) / 2)).IsMidPlaneOf (a : ℝ)
          (NormalHyperplane.axial μ t) ((a : ℝ) • basisVector μ) ∧
        (NormalHyperplane.axial μ (t + (a : ℝ) / 2)).IsVertexMirror (a : ℝ)) ∧
    (∀ t : ℝ, (NormalHyperplane.axial μ t).IsVertexMirror (a : ℝ) →
      (NormalHyperplane.axial μ (t + (a : ℝ) / 2)).IsMidPlaneOf (a : ℝ)
          (NormalHyperplane.axial μ t) ((a : ℝ) • basisVector μ) ∧
        (NormalHyperplane.axial μ (t + (a : ℝ) / 2)).IsEdgeMirror (a : ℝ)) ∧
    (∀ c : ℝ, (∃ q : ℤ, c = (q : ℝ) * (a : ℝ)) →
      (NormalHyperplane.diagonal μ ν hne (c + (a : ℝ))).IsMidPlaneOf (a : ℝ)
          (NormalHyperplane.diagonal μ ν hne c)
          ((a : ℝ) • (basisVector μ + basisVector ν)) ∧
        (NormalHyperplane.diagonal μ ν hne (c + (a : ℝ))).IsLatticeMirror (a : ℝ) ∧
        IsNextMirror (a : ℝ) (basisVector μ + basisVector ν)
          (NormalHyperplane.diagonal μ ν hne c)
          (NormalHyperplane.diagonal μ ν hne (c + (a : ℝ))))
def Statement : Prop :=
  MidPlaneIsLatticeMirror ∧ PictureExpansionsHold ∧ MidPlanesOfAxialAndDiagonal
end MirrorExpansions
end YangMills.Construction.LatticeConventions
end
