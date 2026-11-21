import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace PushforwardField
variable {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
def pushforwardLinear (j : κ → ι) : BondField κ →ₗ[ℝ] BondField ι where
  toFun := pushforwardField j
  map_add' ξ ζ := by
    funext b
    simp only [pushforwardField, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  map_smul' v ξ := by
    funext b
    simp only [pushforwardField, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
def pushforwardCLM (j : κ → ι) : BondField κ →L[ℝ] BondField ι :=
  LinearMap.toContinuousLinearMap (pushforwardLinear j)
theorem secondDerivAlong_comp_pushforward (j : κ → ι) {f : BondField ι → ℝ} {ξ : BondField κ}
    (hf : ContDiffAt ℝ 2 f (pushforwardCLM j ξ)) (u v : BondField κ) :
    secondDerivAlong (fun z => f (pushforwardCLM j z)) ξ u v =
      secondDerivAlong f (pushforwardCLM j ξ) (pushforwardCLM j u) (pushforwardCLM j v) := by
  have hev : ∀ᶠ z in nhds ξ, fderiv ℝ (fun z => f (pushforwardCLM j z)) z u =
      fderiv ℝ f (pushforwardCLM j z) (pushforwardCLM j u) := by
    have hdiff : ∀ᶠ y in nhds (pushforwardCLM j ξ), DifferentiableAt ℝ f y := by
      have := hf.eventually (by simp)
      filter_upwards [this] with y hy
      exact hy.differentiableAt (by norm_num)
    have hpull := (pushforwardCLM j).continuous.continuousAt.eventually hdiff
    filter_upwards [hpull] with z hz
    have := (hz.hasFDerivAt.comp z (pushforwardCLM j).hasFDerivAt).fderiv
    have e : (fun z => f (pushforwardCLM j z)) = f ∘ pushforwardCLM j := rfl
    rw [e, this]
    rfl
  have hdir : DifferentiableAt ℝ (fun y => fderiv ℝ f y (pushforwardCLM j u))
      (pushforwardCLM j ξ) := by
    have hC1 : ContDiffAt ℝ 1 (fderiv ℝ f) (pushforwardCLM j ξ) := hf.fderiv_right (by norm_num)
    exact (hC1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  unfold secondDerivAlong
  rw [Filter.EventuallyEq.fderiv_eq (show (fun ζ => fderiv ℝ (fun z => f (pushforwardCLM j z)) ζ u)
    =ᶠ[nhds ξ] fun ζ => fderiv ℝ f (pushforwardCLM j ζ) (pushforwardCLM j u) from hev)]
  have := (hdir.hasFDerivAt.comp ξ (pushforwardCLM j).hasFDerivAt).fderiv
  have e : (fun ζ => fderiv ℝ f (pushforwardCLM j ζ) (pushforwardCLM j u)) =
      (fun y => fderiv ℝ f y (pushforwardCLM j u)) ∘ pushforwardCLM j := rfl
  rw [e, this]
  rfl
theorem thirdDerivAlong_comp_pushforward (j : κ → ι) {f : BondField ι → ℝ} {ξ : BondField κ}
    (hf : ContDiffAt ℝ 3 f (pushforwardCLM j ξ)) (u v z : BondField κ) :
    thirdDerivAlong (fun z => f (pushforwardCLM j z)) ξ u v z =
      thirdDerivAlong f (pushforwardCLM j ξ) (pushforwardCLM j u) (pushforwardCLM j v)
        (pushforwardCLM j z) := by
  have hev : (fun ζ => secondDerivAlong (fun z => f (pushforwardCLM j z)) ζ u v) =ᶠ[nhds ξ]
      fun ζ => secondDerivAlong f (pushforwardCLM j ζ) (pushforwardCLM j u) (pushforwardCLM j v) := by
    have hC2 : ∀ᶠ y in nhds (pushforwardCLM j ξ), ContDiffAt ℝ 2 f y := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact hy.of_le (by norm_num)
    have hpull := (pushforwardCLM j).continuous.continuousAt.eventually hC2
    filter_upwards [hpull] with ζ hζ
    exact secondDerivAlong_comp_pushforward j hζ u v
  have hdir : DifferentiableAt ℝ
      (fun y => secondDerivAlong f y (pushforwardCLM j u) (pushforwardCLM j v))
      (pushforwardCLM j ξ) := by
    have hC1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) (pushforwardCLM j ξ) :=
      (hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
    have hform : ∀ᶠ y in nhds (pushforwardCLM j ξ),
        secondDerivAlong f y (pushforwardCLM j u) (pushforwardCLM j v) =
          fderiv ℝ (fderiv ℝ f) y (pushforwardCLM j v) (pushforwardCLM j u) := by
      filter_upwards [hf.eventually (by simp)] with y hy
      have hdf : DifferentiableAt ℝ (fderiv ℝ f) y :=
        ((hy.of_le (by norm_num) : ContDiffAt ℝ 2 f y).fderiv_right (m := 1)
          (by norm_num)).differentiableAt (by norm_num)
      have := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const (pushforwardCLM j u) y)).fderiv
      unfold secondDerivAlong
      rw [this]
      simp
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hform
    have hdd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) (pushforwardCLM j ξ) :=
      hC1.differentiableAt (by norm_num)
    exact (hdd.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  unfold thirdDerivAlong
  rw [hev.fderiv_eq]
  have := (hdir.hasFDerivAt.comp ξ (pushforwardCLM j).hasFDerivAt).fderiv
  have e : (fun ζ => secondDerivAlong f (pushforwardCLM j ζ) (pushforwardCLM j u)
        (pushforwardCLM j v)) =
      (fun y => secondDerivAlong f y (pushforwardCLM j u) (pushforwardCLM j v)) ∘
        pushforwardCLM j := rfl
  rw [e, this]
  rfl
end PushforwardField
open PushforwardField in
theorem pushforwardFieldProperties_holds : PushforwardFieldProperties := by
  intro κ ι _ _ _ _ j hj
  refine ⟨(pushforwardLinear j).map_add, fun v ξ => (pushforwardLinear j).map_smul v ξ,
    ?_, ?_, ?_, (pushforwardCLM j).continuous, ?_⟩
  · intro k e
    funext b
    simp only [pushforwardField, bondVariation]
    by_cases hb : j k = b
    · subst hb
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'
        have : j k' ≠ j k := fun h => hk' (hj h)
        simp [this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [Pi.single_apply, Ne.symm hb]
      · intro k' _
        split_ifs with h
        · subst h
          have : k' ≠ k := fun h => hb (congrArg j h.symm)
          simp [Pi.single_apply, this]
        · rfl
  · intro ξ k
    simp only [pushforwardField]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      have : j k' ≠ j k := fun h => hk' (hj h)
      simp [this]
    · simp
  · intro ξ b hb
    simp only [pushforwardField]
    exact Finset.sum_eq_zero fun k _ => by simp [hb k]
  · intro n f ξ hf
    have hc : ContDiffAt ℝ n (fun z => f (pushforwardCLM j z)) ξ :=
      ContDiffAt.comp ξ hf (pushforwardCLM j).contDiff.contDiffAt
    refine ⟨hc, fun h1 u => ?_, fun h2 u v => ?_, fun h3 u v z => ?_⟩
    · have hd : DifferentiableAt ℝ f (pushforwardCLM j ξ) := hf.differentiableAt (fun h => by
        rw [h] at h1
        norm_num at h1)
      have := (hd.hasFDerivAt.comp ξ (pushforwardCLM j).hasFDerivAt).fderiv
      show fderiv ℝ (fun z => f (pushforwardCLM j z)) ξ u =
        fderiv ℝ f (pushforwardCLM j ξ) (pushforwardCLM j u)
      have e : (fun z => f (pushforwardCLM j z)) = f ∘ pushforwardCLM j := rfl
      rw [e, this]
      rfl
    · exact secondDerivAlong_comp_pushforward j (hf.of_le h2) u v
    · exact thirdDerivAlong_comp_pushforward j (hf.of_le h3) u v z
end YangMills.Construction.ColdStepAtMirrorFrames
end
