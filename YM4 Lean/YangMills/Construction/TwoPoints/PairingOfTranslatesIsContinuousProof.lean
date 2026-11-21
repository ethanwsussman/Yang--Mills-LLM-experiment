import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace ShiftPairingContinuity
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem continuous_euclidNorm : Continuous (euclidNorm : AmbientSpace → ℝ) := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.continuous_euclidNorm <;> assumption
theorem euclidNorm_pos {ξ : AmbientSpace} (hξ : ξ ≠ 0) : 0 < euclidNorm ξ := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_pos <;> assumption
theorem sharpNorm_nonneg (F : FixedScale) (f : AmbientSpace → ℂ) : 0 ≤ F.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem euclidNorm_sub_lt_of_mem_shifted {ε : ℝ} {φ : AmbientSpace → ℂ} {z y : AmbientSpace}
    (hφ : tsupport φ ⊆ euclidOpenBall (0 : AmbientSpace) ε)
    (hy : y ∈ minkowskiSum (tsupport φ) {z}) : euclidNorm (y - z) < ε := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  have hb' : b = z := hb
  subst hb'
  have h := hφ ha
  have h' : euclidNorm (a - 0) < ε := h
  simpa using h'
end ShiftPairingContinuity
open ShiftPairingContinuity in
theorem ShiftPairingContinuity.proof (hmod : TranslationModulusProperties.Statement)
    (hcons : AdmissibleFormConsequences.Statement) :
    ShiftPairingContinuity.Statement := by
  intro F S hS hP ε hε f hf g hg
  have hf' : ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧
      tsupport f ⊆ euclidOpenBall (0 : AmbientSpace) ε := hf
  have hg' : ContDiff ℝ 1 g ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ euclidOpenBall (0 : AmbientSpace) ε := hg
  have hcf : f ∈ compactC1Complex := ⟨hf'.1, hf'.2.1, subset_univ _⟩
  have hcg : g ∈ compactC1Complex := ⟨hg'.1, hg'.2.1, subset_univ _⟩
  have hmaps := (hcons.2.2.2.1 F).1 g hcg
  have hmem : ∀ z : AmbientSpace, translateFun z g ∈ compactC1Complex :=
    fun z => (hmaps.1 z).1.mem
  have hsupp : ∀ z : AmbientSpace, tsupport (translateFun z g) = minkowskiSum (tsupport g) {z} :=
    fun z => (hmaps.1 z).2.2
  have hnear : ∀ z y : AmbientSpace, y ∈ tsupport (translateFun z g) → euclidNorm (y - z) < ε := by
    intro z y hy
    rw [hsupp z] at hy
    exact euclidNorm_sub_lt_of_mem_shifted hg'.2.2 hy
  have hsmall : ∀ y ∈ tsupport f, euclidNorm y < ε := by
    intro y hy
    have h : euclidNorm (y - 0) < ε := hf'.2.2 hy
    simpa using h
  have hdisj : ∀ z ∈ farShifts ε, DisjointSupports f (translateFun z g) := by
    intro z hz
    refine Set.disjoint_left.2 fun y hy hy' => ?_
    have hz' : 2 * ε ≤ euclidNorm z := hz
    have h1 := hsmall y hy
    have h2 := hnear z y hy'
    have h3 : euclidNorm z ≤ euclidNorm y + euclidNorm (y - z) := by
      have h := euclidNorm_add_le y (-(y - z))
      rw [euclidNorm_neg] at h
      simpa using h
    linarith
  refine ⟨fun z hz => ⟨hmem z, hdisj z hz⟩, ?_⟩
  obtain ⟨C, hC⟩ := hP.ballDecay
  obtain ⟨⟨-, hlin, -, -, hbound⟩, -⟩ := hcons.2.2.2.2 F S C hS hP hC
  intro z₀ hz₀
  have hz₀' : 2 * ε < euclidNorm z₀ := hz₀
  refine ContinuousAt.continuousWithinAt ?_
  set δ : ℝ := (euclidNorm z₀ - 2 * ε) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hRpos : 0 < ε + δ := by linarith
  set K : ℝ := 4 * C δ (ε + δ) * F.sharpNorm f with hK
  have hKnn : 0 ≤ K :=
    mul_nonneg (mul_nonneg (by norm_num) (hC.1 _ _ hδpos hRpos)) (sharpNorm_nonneg F _)
  have hclose : ∀ z : AmbientSpace, euclidNorm (z - z₀) < δ →
      ‖shiftPairing S f g z - shiftPairing S f g z₀‖ ≤
        K * F.translationModulus g (euclidNorm (z - z₀)) := by
    intro z hz
    have hzfar : z ∈ farShifts ε := by
      show 2 * ε ≤ euclidNorm z
      have h := euclidNorm_add_le z (-(z - z₀))
      rw [euclidNorm_neg] at h
      have h' : euclidNorm z₀ ≤ euclidNorm z + euclidNorm (z - z₀) := by
        simpa using h
      rw [hδ] at hz
      linarith
    have hz₀far : z₀ ∈ farShifts ε := hz₀'.le
    have hpair : ∀ w ∈ farShifts ε,
        IsDisjointSupportPair (translateFun w g) f := fun w hw =>
      ⟨hmem w, hcf, (hdisj w hw).symm⟩
    obtain ⟨-, -, hval⟩ := hlin 1 (-1) _ _ f (hpair z hzfar) (hpair z₀ hz₀far)
    have hG : (1 : ℂ) • translateFun z g + (-1 : ℂ) • translateFun z₀ g =
        translateFun z g - translateFun z₀ g := by
      simp [sub_eq_add_neg]
    rw [hG] at hval
    have hdiff : shiftPairing S f g z - shiftPairing S f g z₀ =
        complexifyForm S f (translateFun z g - translateFun z₀ g) := by
      rw [hval]
      simp [shiftPairing, sub_eq_add_neg]
    have hGsupp : tsupport (translateFun z g - translateFun z₀ g) ⊆
        euclidClosedBall z₀ (ε + δ) := by
      have hs : tsupport (translateFun z g - translateFun z₀ g) ⊆
          tsupport (translateFun z g) ∪ tsupport (translateFun z₀ g) := by
        simp only [tsupport]
        rw [← closure_union]
        exact closure_mono (Function.support_sub _ _)
      intro y hy
      show euclidNorm (y - z₀) ≤ ε + δ
      rcases hs hy with hy | hy
      · have h1 := hnear z y hy
        have h2 := euclidNorm_add_le (y - z) (z - z₀)
        have h3 : y - z + (z - z₀) = y - z₀ := by abel
        rw [h3] at h2
        linarith
      · have h1 := hnear z₀ y hy
        linarith
    have hfsupp : tsupport f ⊆ euclidClosedBall (0 : AmbientSpace) (ε + δ) := by
      intro y hy
      show euclidNorm (y - 0) ≤ ε + δ
      have h := hsmall y hy
      simp only [sub_zero]
      linarith
    have hdist : SeparatedBy δ (tsupport f)
        (tsupport (translateFun z g - translateFun z₀ g)) := by
      intro y hy y' hy'
      have h1 := hsmall y hy
      have h2 : euclidNorm (y' - z₀) ≤ ε + δ := hGsupp hy'
      have h3 : euclidNorm z₀ ≤ euclidNorm y + euclidNorm (y - y') +
          euclidNorm (y' - z₀) := by
        have a := euclidNorm_add_le (y + -(y - y')) (-(y' - z₀))
        have b := euclidNorm_add_le y (-(y - y'))
        rw [euclidNorm_neg] at a b
        have c : y + -(y - y') + -(y' - z₀) = z₀ := by abel
        rw [c] at a
        linarith
      have h4 : euclidNorm z₀ = 2 * ε + 2 * δ := by rw [hδ]; ring
      linarith
    have hb := hbound δ (ε + δ) hδpos hRpos 0 z₀ f hcf _
      (compactC1Complex.sub_mem (hmem z) (hmem z₀)) hfsupp hGsupp hdist
    have hm := ((hmod F g hcg).1).2.2.2.2.1 z z₀
    rw [hdiff]
    exact hb.trans (mul_le_mul_of_nonneg_left hm hKnn)
  have htend : Tendsto (fun z : AmbientSpace => euclidNorm (z - z₀)) (𝓝[≠] z₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous fun z : AmbientSpace => euclidNorm (z - z₀) :=
        continuous_euclidNorm.comp (continuous_id.sub continuous_const)
      have h0 : euclidNorm (z₀ - z₀) = 0 := by simp [euclidNorm]
      have h := hcont.tendsto z₀
      simp only [h0] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact euclidNorm_pos (sub_ne_zero.2 hz)
  have hupper : Tendsto (fun z : AmbientSpace => K * F.translationModulus g (euclidNorm (z - z₀)))
      (𝓝[≠] z₀) (𝓝 0) := by
    have h := (((hmod F g hcg).1).2.2.2.2.2.comp htend).const_mul K
    simpa using h
  have hnear₀ : ∀ᶠ z in 𝓝[≠] z₀, euclidNorm (z - z₀) < δ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδpos)
  rw [continuousAt_iff_punctured_nhds, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hnear₀.mono fun z hz => hclose z hz) hupper
end YangMills.Construction.TwoPoints
end
