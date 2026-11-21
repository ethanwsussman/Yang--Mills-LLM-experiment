import YangMills.Construction.ColdStepAtMirrorFrames.GlueOfTwoCharts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem twoChartsGlue (hOff : TorusOffsetsAboutCell) (hIm : ImaginaryCoordinatesIsometric) :
    TwoChartsGlue := by
  classical
  intro F F' Y Y' r θ w w' hL hodd hs hθ hnear
  obtain ⟨_, _, hnorm, honto, _, _, _⟩ := hIm
  obtain ⟨c1, u1, d1, _⟩ := hOff F r Y hodd hs
  let P : F.Site F.depth → Prop := fun x =>
    ∃ p : (Fin 4 → ℤ) × (Fin 4 → ℤ), WithinRadius r p.1 ∧ p.2 ∈ centredCube F.blockSide ∧
      (fineBondAt Y p.1 p.2 0).1 = x
  let wx : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i =>
    if H : P x then w' (fineBondAt Y' H.choose.1 H.choose.2 i).1 i else w x i
  let Δ : StepVariable (finiteCells F) := fun b => (honto (wx b.1.1 b.1.2 - w b.1.1 b.1.2)).choose
  have hΔ : ∀ b, toImaginary (Δ b) = wx b.1.1 b.1.2 - w b.1.1 b.1.2 := fun b =>
    (honto (wx b.1.1 b.1.2 - w b.1.1 b.1.2)).choose_spec
  have hnoP : ∀ b : ↥(chordBonds (finiteCells F)), ¬ P b.1.1 → ‖Δ b‖ = 0 := fun b hP => by
    rw [← hnorm, hΔ b]
    have : wx b.1.1 b.1.2 = w b.1.1 b.1.2 := dif_neg hP
    rw [this, sub_self, norm_zero]
  refine ⟨Δ, wx, fun b => ?_, fun b hb => ?_, fun b hb => ?_, fun h o i hh ho => ?_⟩
  · by_cases hP : P b.1.1
    · rw [← hnorm, hΔ b]
      have hspec := hP.choose_spec
      have e1 : wx b.1.1 b.1.2 = w' (fineBondAt Y' hP.choose.1 hP.choose.2 b.1.2).1 b.1.2 := dif_pos hP
      have e2 : fineBondAt Y hP.choose.1 hP.choose.2 b.1.2 = b.1 :=
        Prod.ext hspec.2.2 rfl
      have h3 := hnear hP.choose.1 hP.choose.2 b.1.2 hspec.1 hspec.2.1 (by rw [e2]; exact b.2)
      rw [e2] at h3
      rw [e1]
      have e3 : ‖w' (fineBondAt Y' hP.choose.1 hP.choose.2 b.1.2).1 b.1.2 - w b.1.1 b.1.2‖ =
          ‖(w b.1.1 b.1.2 : ℍ[ℝ]) - w' (fineBondAt Y' hP.choose.1 hP.choose.2 b.1.2).1 b.1.2‖ := by
        rw [norm_sub_rev]
        rfl
      rw [e3]
      exact h3
    · rw [hnoP b hP]
      exact hθ
  · have hP : ¬ P b.1.1 := by
      rintro ⟨p, hp1, hp2, hp3⟩
      apply hb
      unfold ballChordBonds
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have e1 := (c1 p.1 p.2 0 hp2).1
      rw [hp3] at e1
      rw [e1, (d1 p.1 hp1).1]
      refine Finset.sup_le fun i _ => ?_
      have := hp1 i
      rw [Int.abs_eq_natAbs] at this
      omega
    exact norm_eq_zero.1 (hnoP b hP)
  · unfold shiftCoordinates stepCoordinates
    rw [dif_pos (show (b.1, b.2) ∈ chordBonds (finiteCells F) from hb)]
    have := hΔ ⟨b, hb⟩
    simp only [this]
    abel
  · have hP : P (fineBondAt Y h o i).1 := ⟨(h, o), hh, ho, rfl⟩
    have hspec := hP.choose_spec
    have e1 : wx (fineBondAt Y h o i).1 i = w' (fineBondAt Y' hP.choose.1 hP.choose.2 i).1 i := dif_pos hP
    obtain ⟨q1, q2⟩ := u1 _ _ _ _ 0 i hspec.1 hh hspec.2.1 ho hspec.2.2
    rw [e1, q1, q2]
end YangMills.Construction.ColdStepAtMirrorFrames
end
