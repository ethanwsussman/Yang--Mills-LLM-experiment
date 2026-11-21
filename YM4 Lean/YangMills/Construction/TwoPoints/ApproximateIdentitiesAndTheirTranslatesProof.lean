import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TwoPoints.ApproximateIdentitiesAndTheirTranslates
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace MollifierBump
theorem euclidNorm_eq_norm_toLp (x : AmbientSpace) :
    euclidNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNorm_le_add (x v : AmbientSpace) :
    euclidNorm v ≤ euclidNorm x + euclidNorm (x - v) := by
  rw [euclidNorm_eq_norm_toLp, euclidNorm_eq_norm_toLp, euclidNorm_eq_norm_toLp]
  have hsplit : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (x - v) := by
    rw [← WithLp.toLp_sub]
    simp
  rw [hsplit]
  exact norm_sub_le _ _
theorem exists_normalized_bump {r : ℝ} (hr : 0 < r) :
    ∃ f : AmbientSpace → ℂ, f ∈ realValuedPart (ccInfIn (euclidOpenBall (0 : AmbientSpace) r)) ∧
      (∀ x, IsRealNonneg (f x)) ∧ lebesgueIntegral f = 1 := by
  set g : AmbientSpace → ℝ := fun x => expNegInvGlue ((r / 2) ^ 2 - ∑ i, x i ^ 2) with hg
  have hgsmooth : ContDiff ℝ ∞ g := by
    refine expNegInvGlue.contDiff.comp ?_
    refine contDiff_const.sub (ContDiff.sum fun i _ => ?_)
    exact (contDiff_apply ℝ ℝ i).pow 2
  have hgcont : Continuous g := hgsmooth.continuous
  have hgnn : ∀ x, 0 ≤ g x := fun x => expNegInvGlue.nonneg _
  have hgsupp : tsupport g ⊆ {x : AmbientSpace | ∑ i, x i ^ 2 ≤ (r / 2) ^ 2} := by
    refine closure_minimal ?_ (isClosed_le (by fun_prop) continuous_const)
    intro x hx
    by_contra hnot
    have hlt : (r / 2) ^ 2 < ∑ i, x i ^ 2 := not_le.1 hnot
    exact hx (expNegInvGlue.zero_of_nonpos (by linarith))
  have hgcpt : HasCompactSupport g := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : AmbientSpace) (r / 2))
      (isClosed_tsupport _) ?_
    intro x hx
    have hxs : ∑ i, x i ^ 2 ≤ (r / 2) ^ 2 := hgsupp hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hi : x i ^ 2 ≤ (r / 2) ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun k => x k ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)) hxs
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq hi (by positivity)
  have hgzero : g 0 ≠ 0 := by
    have hpos : 0 < g 0 := by
      refine expNegInvGlue.pos_of_pos ?_
      simp only [Pi.zero_apply]
      have hsq : (0 : ℝ) < (r / 2) ^ 2 := by positivity
      simpa using hsq
    exact hpos.ne'
  have hmass : 0 < ∫ x, g x :=
    hgcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hgcpt hgnn hgzero
  set m : ℝ := ∫ x, g x with hm
  let f : AmbientSpace → ℂ := fun x => ((g x / m : ℝ) : ℂ)
  have hfsupp : Function.support f ⊆ Function.support g := by
    intro x hx hgx
    exact hx (by simp [f, show g x = 0 from hgx])
  have hftsupp : tsupport f ⊆ tsupport g := closure_mono hfsupp
  refine ⟨f, ?_, fun x => ⟨by simp [f], ?_⟩, ?_⟩
  · show (ContDiff ℝ ∞ f ∧ IsCompact (tsupport f) ∧
        tsupport f ⊆ euclidOpenBall (0 : AmbientSpace) r) ∧ ∀ x, (f x).im = 0
    refine ⟨⟨?_, ?_, ?_⟩, fun x => by simp [f]⟩
    · exact Complex.ofRealCLM.contDiff.comp (hgsmooth.div_const m)
    · exact hgcpt.of_isClosed_subset (isClosed_tsupport _) hftsupp
    · intro x hx
      have hxs : ∑ i, x i ^ 2 ≤ (r / 2) ^ 2 := hgsupp (hftsupp hx)
      show euclidNorm (x - 0) < r
      have hhalf : euclidNorm (x - 0) ≤ r / 2 := by
        simp only [sub_zero, euclidNorm]
        exact Real.sqrt_le_iff.2 ⟨by positivity, hxs⟩
      linarith
  · have hq : 0 ≤ g x / m := div_nonneg (hgnn x) hmass.le
    simpa [f] using hq
  · show ∫ x, f x = 1
    have hcast : ∫ x, f x = ((∫ x, g x / m : ℝ) : ℂ) := integral_ofReal
    rw [hcast, integral_div, ← hm, div_self hmass.ne']
    simp
theorem euclidNorm_pos {v : AmbientSpace} (hv : v ≠ 0) : 0 < euclidNorm v := by apply _root_.YangMills.Construction.TorusTransport.euclidNormVec_pos <;> assumption
end MollifierBump
open MollifierBump in
theorem MollifierTranslatesDisjoint.holds :
    MollifierTranslatesDisjoint.Statement := by
  refine ⟨?_, ?_⟩
  · have hex : ∀ n : ℕ, ∃ f : AmbientSpace → ℂ, 1 ≤ n →
        f ∈ realValuedPart (ccInfIn (euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ)))) ∧
          (∀ x, IsRealNonneg (f x)) ∧ lebesgueIntegral f = 1 := by
      intro n
      by_cases hn : 1 ≤ n
      · have hrad : (0 : ℝ) < 1 / (n : ℝ) := by
          positivity
        obtain ⟨f, hf⟩ := exists_normalized_bump hrad
        exact ⟨f, fun _ => hf⟩
      · exact ⟨0, fun h => absurd h hn⟩
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · intro v hv ρ hρ n hn
    have hvpos := euclidNorm_pos hv
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
    have hone : 1 ≤ n := by exact_mod_cast hnpos
    have hmem : ContDiff ℝ ∞ (ρ n) ∧ IsCompact (tsupport (ρ n)) ∧
        tsupport (ρ n) ⊆ euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ)) := (hρ n hone).1.1
    have hreal : ∀ x, (ρ n x).im = 0 := (hρ n hone).1.2
    obtain ⟨hsmooth, hcpt, hball⟩ := hmem
    have hC1 : ContDiff ℝ 1 (ρ n) := hsmooth.of_le (by exact_mod_cast le_top)
    have hts : tsupport (translateFun v (ρ n)) = (Homeomorph.subRight v) ⁻¹' tsupport (ρ n) :=
      tsupport_comp_eq_preimage (ρ n) (Homeomorph.subRight v)
    refine ⟨?_, ?_, ?_⟩
    · show (ContDiff ℝ 1 (ρ n) ∧ IsCompact (tsupport (ρ n)) ∧ tsupport (ρ n) ⊆ univ) ∧
        ∀ x, (ρ n x).im = 0
      exact ⟨⟨hC1, hcpt, subset_univ _⟩, hreal⟩
    · show (ContDiff ℝ 1 (translateFun v (ρ n)) ∧ IsCompact (tsupport (translateFun v (ρ n))) ∧
        tsupport (translateFun v (ρ n)) ⊆ univ) ∧ ∀ x, (translateFun v (ρ n) x).im = 0
      refine ⟨⟨?_, ?_, subset_univ _⟩, fun x => hreal _⟩
      · exact hC1.comp (contDiff_id.sub contDiff_const)
      · rw [hts]
        exact (Homeomorph.subRight v).isCompact_preimage.2 hcpt
    · show Disjoint (tsupport (ρ n)) (tsupport (translateFun v (ρ n)))
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [hts] at hx'
      have ha : euclidNorm (x - 0) < 1 / (n : ℝ) := hball hx
      have hb : euclidNorm ((x - v) - 0) < 1 / (n : ℝ) := hball hx'
      rw [sub_zero] at ha hb
      have htri := euclidNorm_le_add x v
      have hfar : 2 / (n : ℝ) ≤ euclidNorm v := by
        rw [div_le_iff₀ hvpos] at hn
        rw [div_le_iff₀ hnpos]
        linarith
      have hsum : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
      linarith
end YangMills.Construction.TwoPoints
end
