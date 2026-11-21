import YangMills.Construction.ClusterExpansionOfAStep.CutOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.IntegralOfACutPotential
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace FintypeInstance
theorem integral_pi_fintype_congr {ι : Type} (i₁ i₂ : Fintype ι) (F : (ι → EuclideanSpace ℝ (Fin 3)) → ℝ) :
    (∫ x, F x ∂(@Measure.pi ι (fun _ => EuclideanSpace ℝ (Fin 3)) i₁ _ fun _ => volume)) =
      ∫ x, F x ∂(@Measure.pi ι (fun _ => EuclideanSpace ℝ (Fin 3)) i₂ _ fun _ => volume) := by
  obtain rfl := Subsingleton.elim i₁ i₂
  rfl
theorem prod_univ_fintype_congr {α : Type} (i₁ i₂ : Fintype α) (g : α → ℝ) :
    @Finset.prod _ _ _ (@Finset.univ α i₁) g = @Finset.prod _ _ _ (@Finset.univ α i₂) g := by
  obtain rfl := Subsingleton.elim i₁ i₂
  rfl
end FintypeInstance
open FintypeInstance in
theorem cutPotentialIntegralFactors_holds : CutPotentialIntegralFactors := by
  intro R n _ s lam N
  classical
  let X := s.freeNear N
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨p, hp⟩ : ∃ p : s.free → Prop, p = fun b => b ∈ X := ⟨_, rfl⟩
  have hpX : ∀ b, p b ↔ b ∈ X := fun b => by rw [hp]
  have mp := volume_preserving_piEquivPiSubtypeProd (fun _ : s.free => E) p
  obtain ⟨toN, htoN⟩ : ∃ toN : ({b // p b} → E) → (s.freeNear N → E), toN = fun a b =>
      a ⟨b.1, (hpX _).2 b.2⟩ := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ({b // p b} → E) → ℝ, f = fun a =>
      (∏ b : {b // p b}, ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn
        (StepSettings.coordNorm (a b))) *
        Real.exp (-s.potential (s.extendByZero N (toN a))) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : E → ℝ, h = fun z =>
      ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn (StepSettings.coordNorm z) *
        Real.exp (-(R.coupling * lam / 2 * ‖z‖ ^ 2)) := ⟨_, rfl⟩
  have key : ∀ z : ({b // p b} → E) × ({b // ¬ p b} → E),
      (fun η : StepSettings.FreeCoords s.free =>
        cutoffProd η * Real.exp (-(s.restrictedSplit lam X).potential η))
        ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : s.free => E) p).symm z) =
      f z.1 * (fun c : {b // ¬ p b} → E => ∏ b, h (c b)) z.2 := by
    rintro ⟨a, c⟩
    set η := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : s.free => E) p).symm (a, c) with hη
    have hin : ∀ b (hb : p b), η b = a ⟨b, hb⟩ := by
      intro b hb
      simp [hη, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hb]
    have hout : ∀ b (hb : ¬ p b), η b = c ⟨b, hb⟩ := by
      intro b hb
      simp [hη, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hb]
    have hcut : s.restrictTo X η = s.extendByZero N (toN a) := by
      funext b
      by_cases hb : b ∈ X
      · simp only [StepSettings.ChartSetting.restrictTo, StepSettings.ChartSetting.extendByZero]
        rw [if_pos hb, dif_pos hb, hin b ((hpX b).2 hb), htoN]
      · simp only [StepSettings.ChartSetting.restrictTo, StepSettings.ChartSetting.extendByZero]
        rw [if_neg hb, dif_neg hb]
    have hcuts : cutoffProd (R := R) η =
        (∏ b : {b // p b}, ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn
          (StepSettings.coordNorm (a b))) *
        ∏ b : {b // ¬ p b}, ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn
          (StepSettings.coordNorm (c b)) := by
      rw [cutoffProd, ← Fintype.prod_subtype_mul_prod_subtype p]
      congr 1
      · exact Finset.prod_congr rfl fun b _ => by rw [hin b.1 b.2]
      · exact Finset.prod_congr rfl fun b _ => by rw [hout b.1 b.2]
    have hsum : ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 = ∑ b : {b // ¬ p b}, ‖c b‖ ^ 2 := by
      have h1 : ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 =
          ∑ b ∈ Finset.univ.filter (fun b => ¬ p b), ‖η b‖ ^ 2 := by
        apply Finset.sum_congr _ fun _ _ => rfl
        ext b
        simp [hpX]
      rw [h1, Finset.sum_subtype (p := fun b => ¬ p b) _ (by simp)]
      exact Finset.sum_congr rfl fun b _ => by rw [hout b.1 b.2]
    show cutoffProd η * Real.exp (-(s.restrictedSplit lam X).potential η) = _
    rw [Restriction.restrictedSplit_potential_eq, hcut, hsum, hcuts, hf, hh]
    simp only
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, neg_add, Real.exp_add]
    have h2 : ∑ b : {b // ¬ p b}, -(R.coupling * lam / 2 * ‖c b‖ ^ 2) =
        -(R.coupling * lam / 2 * ∑ b : {b // ¬ p b}, ‖c b‖ ^ 2) := by
      rw [Finset.sum_neg_distrib, Finset.mul_sum]
    rw [h2]
    ring
  have hA : (∫ η, cutoffProd (R := R) η * Real.exp (-(s.restrictedSplit lam X).potential η)) =
      (∫ x, f x) * ∫ c : {b // ¬ p b} → E, ∏ b, h (c b) := by
    have e1 := mp.symm.integral_comp' (g := fun η : StepSettings.FreeCoords s.free =>
      cutoffProd η * Real.exp (-(s.restrictedSplit lam X).potential η))
    refine e1.symm.trans ?_
    refine (integral_congr_ae (Filter.Eventually.of_forall key)).trans ?_
    exact integral_prod_mul (μ := volume) (ν := volume) f (fun c : {b // ¬ p b} → E => ∏ b, h (c b))
  have hcard : (Finset.univ.filter fun b : s.free => ¬ p b) = Finset.univ \ s.freeNear N := by
    ext b
    simp [hpX, X]
  rw [hA, integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : {b // ¬ p b} => E) fun _ => h,
    Finset.prod_const, Finset.card_univ, Fintype.card_subtype, hcard]
  have hG : ∫ z, h z = R.bondGaussian lam := by rw [hh]; rfl
  rw [hG]
  congr 1
  subst hp
  subst htoN
  subst hf
  refine (integral_pi_fintype_congr _ (inferInstanceAs (Fintype ↥(s.freeNear N))) _).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ * _ = _ * _
  congr 1
  exact prod_univ_fintype_congr _ _ _
end YangMills.Construction.ClusterExpansionOfAStep
end
