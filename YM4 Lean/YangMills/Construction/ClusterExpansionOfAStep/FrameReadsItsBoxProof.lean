import YangMills.Construction.ClusterExpansionOfAStep.FrameReadsItsBox
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps TorusMirror StepCosts
namespace FrameLocality
theorem mirrorField_eq_of_fieldsAgreeNear {n n' r : ℕ} (hr : 0 < r) (U : TorusField n) (U' : TorusField n')
    (x : TorusSite n) (x' : TorusSite n') (hagree : FieldsAgreeNear U U' x x' r) :
    mirrorField r x U = mirrorField r x' U' := by
  haveI : NeZero (4 * r) := ⟨by omega⟩
  funext z i
  have hinBox := foldSite_inBox hr
  have hstep : foldSite r (z + TorusFields.unitStep (4 * r) i) i = foldSite r z i + 1 ∨
      foldSite r (z + TorusFields.unitStep (4 * r) i) i = foldSite r z i - 1 := by
    rw [foldSite_add_unitStep_self hr]
    exact triangleFold_add_one r _
  unfold mirrorField
  by_cases hup : foldSite r (z + TorusFields.unitStep (4 * r) i) i = foldSite r z i + 1
  · rw [if_pos hup, if_pos hup]
    have hbond : TorusFields.BondOffsetInBox r (foldSite r z, i) := ⟨hinBox z, by
      simp only
      rw [← foldSite_of_up hup]
      exact hinBox _⟩
    exact hagree _ hbond
  · rw [if_neg hup, if_neg hup]
    have hdown := hstep.resolve_left hup
    have hbond : TorusFields.BondOffsetInBox r (foldSite r (z + TorusFields.unitStep (4 * r) i), i) := ⟨hinBox _, by
      simp only
      rw [← foldSite_of_down hdown]
      exact hinBox z⟩
    exact congrArg (·⁻¹) (hagree _ hbond)
theorem frameCoordLocal_holds : FrameCoordLocal := by
  intro p ρ d r n n' _ _ U U' b b' hfit hr hlarge hlarge' hdir hoff hagree
  have hext : ∀ i, (torusFrame p.side d n).extent i = n := fun _ => rfl
  have hext' : ∀ i, (torusFrame p.side d n').extent i = n' := fun _ => rfl
  have hside : 0 < p.side := hfit.L_odd.pos
  haveI hne : NeZero (n * p.side) := ⟨(Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne n)) hside).ne'⟩
  haveI hne' : NeZero (n' * p.side) := ⟨(Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne n')) hside).ne'⟩
  haveI : NeZero (n * (torusFrame p.side d n).blockSide) := hne
  haveI : NeZero (n' * (torusFrame p.side d n').blockSide) := hne'
  have hbig : ∀ i, 4 * r + 5 < (torusFrame p.side d n).extent i := fun _ => hlarge
  have hbig' : ∀ i, 4 * r + 5 < (torusFrame p.side d n').extent i := fun _ => hlarge'
  have hcell : enclosingCell (torusSiteInFrame (torusFrame p.side d n) (torusFrame p.side d n).depth b.1) =
      torusSiteInFrame (torusFrame p.side d n) (torusFrame p.side d n).top (parentBlock p.side b.1) :=
    enclosingCell_torusSiteInFrame hext b.1
  have hcell' : enclosingCell (torusSiteInFrame (torusFrame p.side d n') (torusFrame p.side d n').depth b'.1) =
      torusSiteInFrame (torusFrame p.side d n') (torusFrame p.side d n').top (parentBlock p.side b'.1) :=
    enclosingCell_torusSiteInFrame hext' b'.1
  unfold StepCosts.frameCoord ColdStepAtMirrorFrames.bondFrameCoord
  rw [if_pos hbig, if_pos hbig']
  unfold ColdStepAtMirrorFrames.reflectedBondCoord
  simp only
  rw [hcell, hcell', reflectedField_readAtLevel hext hr, reflectedField_readAtLevel hext' hr,
    mirrorField_eq_of_fieldsAgreeNear hr U U' _ _ hagree]
  unfold ColdStepAtMirrorFrames.reflectedBond
  simp only
  rw [hoff, hdir]
  rfl
end FrameLocality
end YangMills.Construction
end
