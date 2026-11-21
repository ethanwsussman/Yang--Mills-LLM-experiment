import YangMills.Construction.InfiniteLattice.HalfWayHyperplaneOfAMirrorAndAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeConventions
structure MirrorReconstructionHyps (a : ℝ) {ι : Type} [Fintype ι]
    (S : NormalHyperplane) (h : Point) (S' : NormalHyperplane) (w : ι → Point) : Prop where
  isMidPlane : S'.IsMidPlaneOf a S h
  midPlane_isLatticeMirror : S'.IsLatticeMirror a
  one_le_card : 1 ≤ Fintype.card ι
  step_mem : ∀ i, w i ∈ InfiniteLattice.latticeSubgroup a
  euclidDot_step : ∀ i, euclidDot S.normal (w i) = 0
end YangMills.Construction.LatticeConventions
end
