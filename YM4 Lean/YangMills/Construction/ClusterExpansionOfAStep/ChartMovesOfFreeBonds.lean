import YangMills.Construction.ClusterExpansionOfAStep.ChartOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.FreeBondCharts
variable {m : ℕ}
section Calculus
variable (I : Finset (TorusFields.TorusBond m)) (w : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions)
def leftMoveCoords (p η : I → QuaternionLogarithm.ImaginaryCoord) : I → QuaternionLogarithm.ImaginaryCoord :=
  fun b => QuaternionLogarithm.chartTranslate (w b.1) (η b - p b)
theorem leftMoveCoords_self (p : I → QuaternionLogarithm.ImaginaryCoord) : leftMoveCoords I w p p = 0 := by
  funext b
  simp [leftMoveCoords, QuaternionLogarithm.chartTranslate_zero]
def leftMoveComponent (b : I) (p : I → QuaternionLogarithm.ImaginaryCoord)
    (η : I → QuaternionLogarithm.ImaginaryCoord) : QuaternionLogarithm.ImaginaryCoord :=
  QuaternionLogarithm.chartTranslate (w b.1) (η b - p b)
theorem contDiffAt_leftMoveComponent (b : I) (p : I → QuaternionLogarithm.ImaginaryCoord) :
    ContDiffAt ℝ 3 (leftMoveComponent I w b p) p := by
  have h1 : ContDiff ℝ 3 fun η : I → QuaternionLogarithm.ImaginaryCoord => η b - p b :=
    (ContinuousLinearMap.proj b :
      (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord).contDiff.sub contDiff_const
  have h2 : ContDiffAt ℝ 3 (QuaternionLogarithm.chartTranslate (w b.1)) (p b - p b) := by
    rw [sub_self]
    exact QuaternionLogarithm.contDiffAt_chartTranslate _
  exact h2.comp p h1.contDiffAt
theorem contDiffAt_leftMoveCoords (p : I → QuaternionLogarithm.ImaginaryCoord) :
    ContDiffAt ℝ 3 (leftMoveCoords I w p) p :=
  contDiffAt_pi.mpr fun b => contDiffAt_leftMoveComponent I w b p
def coordShift (b : I) (p : I → QuaternionLogarithm.ImaginaryCoord)
    (η : I → QuaternionLogarithm.ImaginaryCoord) : QuaternionLogarithm.ImaginaryCoord := η b - p b
theorem hasFDerivAt_coordShift (b : I) (p q : I → QuaternionLogarithm.ImaginaryCoord) :
    HasFDerivAt (coordShift I b p)
      (ContinuousLinearMap.proj b :
        (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) q :=
  ((ContinuousLinearMap.proj b :
    (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord).hasFDerivAt).sub_const _
theorem leftMoveComponent_eq_comp (b : I) (p : I → QuaternionLogarithm.ImaginaryCoord) :
    leftMoveComponent I w b p = QuaternionLogarithm.chartTranslate (w b.1) ∘ coordShift I b p := rfl
theorem contDiffAt_coordShift (b : I) (p : I → QuaternionLogarithm.ImaginaryCoord) :
    ContDiffAt ℝ 2 (coordShift I b p) p :=
  ((ContinuousLinearMap.proj b :
    (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord).contDiff.sub
      contDiff_const).contDiffAt
theorem fderiv_leftMoveCoords_apply (b : I) (p v : I → QuaternionLogarithm.ImaginaryCoord) :
    fderiv ℝ (leftMoveCoords I w p) p v b = fderiv ℝ (QuaternionLogarithm.chartTranslate (w b.1)) 0 (v b) := by
  have hd : DifferentiableAt ℝ (leftMoveCoords I w p) p :=
    (contDiffAt_leftMoveCoords I w p).differentiableAt (by norm_num)
  have h1 := QuaternionLogarithm.fderiv_clm_comp_apply (ContinuousLinearMap.proj b :
    (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) hd v
  have h2 : (ContinuousLinearMap.proj b :
      (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) ∘ leftMoveCoords I w p =
      leftMoveComponent I w b p := rfl
  rw [h2, leftMoveComponent_eq_comp] at h1
  have hs : coordShift I b p p = 0 := sub_self _
  have hc : DifferentiableAt ℝ (QuaternionLogarithm.chartTranslate (w b.1)) (coordShift I b p p) := by
    rw [hs]
    exact (QuaternionLogarithm.contDiffAt_chartTranslate _).differentiableAt (by norm_num)
  have h3 := LineCalculus.fderiv_of_eventuallyEq_comp
    (f := QuaternionLogarithm.chartTranslate (w b.1) ∘ coordShift I b p)
    (g := QuaternionLogarithm.chartTranslate (w b.1)) (h := coordShift I b p) (x := p)
    (Filter.EventuallyEq.refl _ _) hc (hasFDerivAt_coordShift I b p p).differentiableAt
  rw [h3, hs, (hasFDerivAt_coordShift I b p p).fderiv] at h1
  exact h1.symm
theorem second_fderiv_leftMoveCoords_apply (b : I) (p v v' : I → QuaternionLogarithm.ImaginaryCoord) :
    fderiv ℝ (fderiv ℝ (leftMoveCoords I w p)) p v v' b =
      fderiv ℝ (fderiv ℝ (QuaternionLogarithm.chartTranslate (w b.1))) 0 (v b) (v' b) := by
  have hd : ContDiffAt ℝ 2 (leftMoveCoords I w p) p := (contDiffAt_leftMoveCoords I w p).of_le (by norm_num)
  have h1 := QuaternionLogarithm.second_fderiv_clm_comp_apply (ContinuousLinearMap.proj b :
    (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) hd v v'
  have h2 : (ContinuousLinearMap.proj b :
      (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) ∘ leftMoveCoords I w p =
      leftMoveComponent I w b p := rfl
  rw [h2, leftMoveComponent_eq_comp] at h1
  have hs : coordShift I b p p = 0 := sub_self _
  have hc : ContDiffAt ℝ 2 (QuaternionLogarithm.chartTranslate (w b.1)) (coordShift I b p p) := by
    rw [hs]
    exact (QuaternionLogarithm.contDiffAt_chartTranslate _).of_le (by norm_num)
  have h3 := LineCalculus.second_fderiv_of_eventuallyEq_comp
    (f := QuaternionLogarithm.chartTranslate (w b.1) ∘ coordShift I b p)
    (g := QuaternionLogarithm.chartTranslate (w b.1)) (h := coordShift I b p)
    (x := p) (Filter.EventuallyEq.refl _ _) hc (contDiffAt_coordShift I b p) v v'
  have h4 : fderiv ℝ (coordShift I b p) = fun _ => (ContinuousLinearMap.proj b :
      (I → QuaternionLogarithm.ImaginaryCoord) →L[ℝ] QuaternionLogarithm.ImaginaryCoord) :=
    funext fun q => (hasFDerivAt_coordShift I b p q).fderiv
  have h5 : fderiv ℝ (fderiv ℝ (coordShift I b p)) p = 0 := by
    rw [h4]
    simp
  rw [h3, hs, h5, h4] at h1
  simpa using h1.symm
end Calculus
section Chart
variable {n : ℕ} [NeZero n] {L : ℕ}
open Classical in
def shiftedCoords (I : Finset (TorusFields.TorusBond (n * L)))
    (w : TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions)
    (ζ : I → QuaternionLogarithm.ImaginaryCoord) (b : TorusFields.TorusBond (n * L)) :
    BlockAverages.imaginaryQuaternions :=
  if h : b ∈ I then w b + ColdStepAtMirrorFrames.toImaginary (ζ ⟨b, h⟩) else w b
theorem torusChart_shiftedCoords_eventually (I : Finset (TorusFields.TorusBond (n * L)))
    (hI : ∀ b ∈ I, ¬ TorusCharts.IsBlockTreeBond L b.1 b.2)
    (w : TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions) (V : TorusFields.TorusField n)
    (p : I → QuaternionLogarithm.ImaginaryCoord) :
    ∀ᶠ η in 𝓝 p, TorusCharts.torusChart L (shiftedCoords I w fun b => η b - p b) V =
      FreeBondMoves.leftMovesAt I (leftMoveCoords I w p η) (TorusCharts.torusChart L w V) := by
  classical
  have hall : ∀ b : I, ∀ᶠ η in 𝓝 p, BlockAverages.expUnit (w b.1 + ColdStepAtMirrorFrames.toImaginary (η b - p b)) =
      BlockAverages.expUnit (ColdStepAtMirrorFrames.toImaginary
        (QuaternionLogarithm.chartTranslate (w b.1) (η b - p b))) * BlockAverages.expUnit (w b.1) := by
    intro b
    have hc : Filter.Tendsto (fun η : I → QuaternionLogarithm.ImaginaryCoord => η b - p b) (𝓝 p) (𝓝 0) := by
      have : Continuous fun η : I → QuaternionLogarithm.ImaginaryCoord => η b - p b := by fun_prop
      simpa using this.tendsto p
    exact hc.eventually (QuaternionLogarithm.eventually_expUnit_add_eq (w b.1))
  filter_upwards [Filter.eventually_all.mpr hall] with η hη
  funext x i
  unfold FreeBondMoves.leftMovesAt
  by_cases hx : (x, i) ∈ I
  · have hnt := hI _ hx
    have hv : shiftedCoords I w (fun b => η b - p b) (x, i) =
        w (x, i) + ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hx⟩ - p ⟨(x, i), hx⟩) := by
      unfold shiftedCoords
      rw [dif_pos hx]
    have he := hη ⟨(x, i), hx⟩
    rw [dif_pos hx]
    unfold TorusCharts.torusChart
    simp only [hv]
    have hm : leftMoveCoords I w p η ⟨(x, i), hx⟩ =
        QuaternionLogarithm.chartTranslate (w (x, i)) (η ⟨(x, i), hx⟩ - p ⟨(x, i), hx⟩) := rfl
    rw [hm]
    by_cases hc : TorusCharts.IsBlockEndBond L x i
    · rw [if_pos hc, if_pos hc, he, mul_assoc]
    · rw [if_neg hc, if_neg hc, if_neg hnt, if_neg hnt, he]
  · rw [dif_neg hx]
    refine TorusCharts.torusChart_congr V ?_
    unfold shiftedCoords
    rw [dif_neg hx]
end Chart
end YangMills.Construction.FreeBondCharts
end
