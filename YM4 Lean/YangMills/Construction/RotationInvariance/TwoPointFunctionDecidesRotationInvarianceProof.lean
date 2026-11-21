import YangMills.Construction.EuclideanFunctionals.PlateBoundWithDataAndThePlateBoundWithAnExponent
import YangMills.Construction.LimitTheorem.RotationInvarianceOfACentredLimitProof
import YangMills.Construction.RotationInvariance.FromOnePlaneToTheFullOrthogonalGroup
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZero
import YangMills.Construction.RotationInvariance.LawOfTheTopFrequencies
import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.PlaneDataAreDataOfTheTwoSettings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane
namespace EuclideanFunctionals.TwoPointRotationCriterion
open MomentSymmetry
theorem exists_orthogonalMatrix_of_offset_eq_zero (r : EuclidMotion) (h : r.offset = 0) :
    ∃ R : Matrix.orthogonalGroup (Fin 4) ℝ, EuclidMotion.ofOrthogonalMatrix R = r := by apply _root_.YangMills.Construction.FirstPassageSeqs.CenteredLimitRotation.exists_orthogonalMatrix_of_offset_eq_zero <;> assumption
theorem imagePlaneRotation_offset (w : hyperoctahedral) (t : ℝ) :
    (imagePlaneRotation w t).offset = 0 := by
  have hs : ∀ r : EuclidMotion, r.offset = r 0 := fun r => by
    rw [r.apply_def, map_zero, zero_add]
  obtain ⟨fr, hfr⟩ := w.2
  have hw : (w : EuclidMotion) 0 = 0 := by
    rw [← hfr, ← hs]
    rfl
  have hw' : (w : EuclidMotion)⁻¹ 0 = 0 := by
    have h1 := EuclidMotion.inv_apply_apply (w : EuclidMotion) 0
    rwa [hw] at h1
  have hr : rotateMotion t 0 = 0 := by
    rw [← hs]
    rfl
  rw [hs, imagePlaneRotation, EuclidMotion.mul_apply, EuclidMotion.mul_apply, hw', hr, hw]
theorem twoPointCriterion_holds (hInv : MomentSymmetry.ReductionHolds)
    (hBound : ProductBoundExponent.Main)
    (hData : PlaneDataAsStandingData.ExistsStandingAndApertureData)
    (hTwo : TwoPointTopFrequency.Holds)
    (hLaw : MaxFrequencyLaw.Holds)
    (hPlane : FullOrthogonalInvariance.Holds)
    (hMoments : OrthogonalInvariance.OrthogonalMapStatement) : TwoPointCriterion := by
  intro m S σ hcone w p c hp hc hbound
  obtain ⟨-, -, hInvB, hInvT⟩ := hInv m S σ
  have hW : ProductBoundWithExponent σ hp hc := (hInvB w p c hp hc).2.2.1 hbound
  obtain ⟨C, hC⟩ := ((hBound m S σ).1 c hc p hp).1 hW
  have hcl : ∀ φ ∈ realLabels, labelConstants (fun φ : realLabels => C φ.1) φ = C φ :=
    fun φ h => by simp [labelConstants, h]
  let d : ProductPlaneData m S :=
    { fnl := σ
      coneCond := hcone
      exponent := p
      labelBound := fun φ => C φ.1
      fraction := c
      productBound :=
        { pos_exponent := hC.pos_exponent
          nonneg_constant := fun φ h => by
            rw [hcl φ h]
            exact hC.nonneg_constant φ h
          pos_fraction := hC.pos_fraction
          fraction_lt_quarter := hC.fraction_lt_quarter
          le_bound := fun η h0 h1 φ hφ α hα hs F hF A hA => by
            rw [hcl φ hφ]
            exact hC.le_bound η h0 h1 φ hφ α hα hs F hF A hA } }
  let φ₀ : openingAngles := ⟨Real.pi / 8, by
    constructor
    · positivity
    · linarith [Real.pi_pos]⟩
  have hForward : TwoPointLocallyRotationInvariant S w →
      OrthogonalInvariantConnected S := by
    rintro ⟨t₀, ht₀, hinv⟩
    have hnear : TwoPointTopFrequency.InvariantNearZero S := by
      refine ⟨t₀, ht₀, fun t ht => (hInvT w t).1 ?_⟩
      intro f₁ f₂ hf
      obtain ⟨-, hsep, hpw⟩ := hf
      exact hinv t ht f₁ f₂ (hsep f₁ (List.mem_cons.2 (Or.inl rfl)))
        (hsep f₂ (List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))) (List.rel_of_pairwise_cons hpw (List.mem_singleton.2 rfl))
    have h2 := hTwo m S d φ₀ hnear
    obtain ⟨e, -, he⟩ := (hData m S d).2 φ₀
    have hlaw := (hLaw m S e).2
    rw [he] at hlaw
    have hzero : ∀ n : ℕ, 2 ≤ n → maxFrequency S φ₀ n = 0 := by
      intro n _
      have h3 := hlaw n
      rw [h2] at h3
      simpa using h3
    intro n hn R X hX
    exact (hPlane m S d φ₀ hzero n hn R).2 X hX
  have hBack : OrthogonalInvariantConnected S →
      TwoPointLocallyRotationInvariant S w := by
    intro h2
    refine ⟨1, one_pos, fun t _ f g hf hg hd => ?_⟩
    obtain ⟨R, hR⟩ := exists_orthogonalMatrix_of_offset_eq_zero (imagePlaneRotation w t)
      (imagePlaneRotation_offset w t)
    have hX : [f, g] ∈ sepN 2 := by
      refine ⟨rfl, ?_, ?_⟩
      · intro k hk
        rcases List.mem_pair.1 hk with rfl | rfl
        · exact hf
        · exact hg
      · exact List.Pairwise.cons (fun k hk => by
          rw [List.mem_singleton.1 hk]
          exact hd) (List.Pairwise.cons (fun _ hk => absurd hk List.not_mem_nil) List.Pairwise.nil)
    have h3 := h2 2 le_rfl R [f, g] hX
    rw [hR] at h3
    exact h3
  refine ⟨⟨hForward, hBack⟩, fun _ h2 R n h hh => ?_⟩
  have hM := hMoments m S σ R
  have hα : OrthogonalInvariance.CumulantsInvariant S
      (EuclidMotion.ofOrthogonalMatrix R) := by
    intro k hk f hf
    have h3 := h2 k hk R (List.ofFn f) hf
    have e : (EuclidMotion.ofOrthogonalMatrix R).actList (List.ofFn f) =
        List.ofFn fun l => (EuclidMotion.ofOrthogonalMatrix R).actFn (f l) := by
      simp [EuclidMotion.actList, List.map_ofFn, Function.comp_def]
    rw [e] at h3
    simp only [Ambient.ConnectedFamily.evalAt, dif_pos hk]
    exact h3
  exact (hM.2.2.1 hα (hM.2.1.1 hα)).2 n h hh
end EuclideanFunctionals.TwoPointRotationCriterion
end YangMills.Construction
end
