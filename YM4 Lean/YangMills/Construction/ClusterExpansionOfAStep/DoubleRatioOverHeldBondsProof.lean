import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatioOverHeldBonds
import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatioUnderIntegrals
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames DisjointUnionIntegrals ConvexPotentials IteratedIntegral
namespace HeldBondSplitting
variable {α : Type} [DecidableEq α]
theorem joinFields_of_mem_left (C T : Finset α) (a : C → BondVector) (ξ : T → BondVector) {x : α} (hx : x ∈ C) :
    joinFields C T a ξ x = a ⟨x, hx⟩ := by
  simp only [joinFields, dif_pos hx]
theorem joinFields_of_mem_right {C T : Finset α} (hCT : Disjoint C T) (a : C → BondVector) (ξ : T → BondVector)
    {x : α} (hx : x ∈ T) : joinFields C T a ξ x = ξ ⟨x, hx⟩ := by
  have hC : x ∉ C := fun hc => Finset.disjoint_left.mp hCT hc hx
  simp only [joinFields, dif_neg hC, dif_pos hx]
theorem radialWeightProd_joinFields (r : ℝ → ℝ) {S C T : Finset α} (hS : S = C ∪ T) (hCT : Disjoint C T)
    (a : C → BondVector) (ξ : T → BondVector) :
    radialWeightProd r (fun x : S => joinFields C T a ξ x) = radialWeightProd r a * radialWeightProd r ξ := by
  subst hS
  unfold radialWeightProd
  rw [Finset.prod_coe_sort (C ∪ T) fun x => r ‖joinFields C T a ξ x‖, Finset.prod_union hCT,
    ← Finset.prod_coe_sort C fun x => r ‖joinFields C T a ξ x‖,
    ← Finset.prod_coe_sort T fun x => r ‖joinFields C T a ξ x‖]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [joinFields_of_mem_left C T a ξ x.2]
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [joinFields_of_mem_right hCT a ξ x.2]
theorem continuous_joinFields {S C T : Finset α} (a : C → BondVector) :
    Continuous fun ξ : T → BondVector => fun x : S => joinFields C T a ξ x := by
  refine continuous_pi fun x => ?_
  by_cases hC : (x : α) ∈ C
  · simp only [joinFields, dif_pos hC]
    exact continuous_const
  · by_cases hT : (x : α) ∈ T
    · simp only [joinFields, dif_neg hC, dif_pos hT]
      exact continuous_apply _
    · simp only [joinFields, dif_neg hC, dif_neg hT]
      exact continuous_const
variable {ι : Type} [Fintype ι]
theorem continuous_radialWeightProd {ρ : ℝ} {r : ℝ → ℝ} (hr : Continuous fun u => r (max u 0)) :
    Continuous (radialWeightProd (ι := ι) r) := by
  have : radialWeightProd (ι := ι) r = fun η => ∏ b, r (max ‖η b‖ 0) := by
    funext η
    unfold radialWeightProd
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [max_eq_left (norm_nonneg _)]
  rw [this]
  exact continuous_finset_prod _ fun b _ => hr.comp (continuous_apply b).norm
theorem radialWeightProd_cutoffFactor_props {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hRad : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)) :
    Continuous (radialWeightProd (ι := ι) (cutoffFactor ρ p)) ∧
      HasCompactSupport (radialWeightProd (ι := ι) (cutoffFactor ρ p)) ∧
      (∀ η, 0 ≤ radialWeightProd (ι := ι) (cutoffFactor ρ p) η) ∧
      ∀ η : BondField ι, (¬ ∀ b, ‖η b‖ < ρ) → radialWeightProd (ι := ι) (cutoffFactor ρ p) η = 0 := by
  have hzero : ∀ η : BondField ι, (¬ ∀ b, ‖η b‖ < ρ) → radialWeightProd (ι := ι) (cutoffFactor ρ p) η = 0 := by
    intro η h
    push Not at h
    obtain ⟨b, hb⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    have := hRad.zero _ hb
    rw [max_eq_left (norm_nonneg _)] at this
    exact this
  refine ⟨continuous_radialWeightProd (ρ := ρ) hRad.smooth.continuous, ?_, fun η => ?_, hzero⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    apply hzero
    intro hall
    apply hη
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hall b).le
  · refine Finset.prod_nonneg fun b _ => ?_
    by_cases h : ‖η b‖ < ρ
    · have := hRad.pos _ (norm_nonneg _) h
      rw [max_eq_left (norm_nonneg _)] at this
      exact this.le
    · have := hRad.zero _ (not_lt.mp h)
      rw [max_eq_left (norm_nonneg _)] at this
      exact this.ge
end HeldBondSplitting
open HeldBondSplitting in
theorem doubleRatioPassesToFullIntegrals_holds (hI : IntegralSplitsOverDisjointUnion)
    (hD : CrossRatioIntegralStatement) (hrad : CutoffFactorIsRadialCutoff) :
    DoubleRatioPassesToFullIntegrals := by
  intro α _ S C C' F Ψ ρ c p hρ hp hS hd hd' hΨ hmain
  have hRad := hrad ρ p hρ hp
  set r : ℝ → ℝ := cutoffFactor ρ p with hr
  let Rw : ∀ i j, (C i → BondVector) → (C' j → BondVector) → ℝ := fun i j a b =>
    radialWeightProd r a * radialWeightProd r b *
      cutoffIntegral ρ p (fun ξ => Ψ i j fun x => assembledField (C i) (C' j) F a b ξ x)
  have split : ∀ i j, (∀ a, Integrable (Rw i j a)) ∧ Integrable (fun a => ∫ b, Rw i j a b) ∧
      cutoffIntegral ρ p (Ψ i j) = ∫ a, ∫ b, Rw i j a b := by
    intro i j
    have hG : Integrable (ballDensity r (Ψ i j)) :=
      ((radialWeightProd_cutoffFactor_props hρ hRad).1.mul
        (Real.continuous_exp.comp (hΨ i j).neg)).integrable_of_hasCompactSupport
        (radialWeightProd_cutoffFactor_props hρ hRad).2.1.mul_right
    obtain ⟨int1, eq1⟩ := hI α (S i j) (C i) (C' j ∪ F) (ballDensity r (Ψ i j)) (hS i j) (hd i j) hG
    have hH : ∀ a q, ballDensity r (Ψ i j) (fun x => joinFields (C i) (C' j ∪ F) a q x) =
        radialWeightProd r a *
          (radialWeightProd r q * Real.exp (-(Ψ i j fun x => joinFields (C i) (C' j ∪ F) a q x))) := by
      intro a q
      simp only [ballDensity]
      rw [radialWeightProd_joinFields r (hS i j) (hd i j) a q]
      ring
    have inner : ∀ a, Integrable (Rw i j a) ∧
        ∫ q, ballDensity r (Ψ i j) (fun x => joinFields (C i) (C' j ∪ F) a q x) = ∫ b, Rw i j a b := by
      intro a
      have hc : Continuous fun q : (↥(C' j ∪ F) → BondVector) =>
          Ψ i j fun x => joinFields (C i) (C' j ∪ F) a q x := (hΨ i j).comp (continuous_joinFields a)
      have hHi : Integrable fun q : (↥(C' j ∪ F) → BondVector) =>
          ballDensity r (Ψ i j) (fun x => joinFields (C i) (C' j ∪ F) a q x) := by
        simp only [hH]
        refine Integrable.const_mul ?_ _
        exact ((radialWeightProd_cutoffFactor_props hρ hRad).1.mul
          (Real.continuous_exp.comp hc.neg)).integrable_of_hasCompactSupport
          (radialWeightProd_cutoffFactor_props hρ hRad).2.1.mul_right
      obtain ⟨int2, eq2⟩ := hI α (C' j ∪ F) (C' j) F _ rfl (hd' j) hHi
      have hval : ∀ b : (C' j → BondVector), ∫ ξ,
          ballDensity r (Ψ i j) (fun x => joinFields (C i) (C' j ∪ F) a
            (fun y => joinFields (C' j) F b ξ y) x) = Rw i j a b := by
        intro b
        show _ = radialWeightProd r a * radialWeightProd r b * ∫ ξ, ballDensity r _ ξ
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        beta_reduce
        rw [hH a (fun y => joinFields (C' j) F b ξ y), radialWeightProd_joinFields r rfl (hd' j) b ξ]
        simp only [ballDensity, assembledField]
        ring
      constructor
      · have := int2.integral_prod_left
        refine this.congr (Filter.Eventually.of_forall fun b => ?_)
        exact hval b
      · rw [eq2]
        rw [show (volume : Measure ((C' j → BondVector) × (F → BondVector))) = volume.prod volume from rfl]
        rw [integral_prod _ int2]
        exact integral_congr_ae (Filter.Eventually.of_forall fun b => hval b)
    refine ⟨fun a => (inner a).1, ?_, ?_⟩
    · have := int1.integral_prod_left
      refine this.congr (Filter.Eventually.of_forall fun a => ?_)
      exact (inner a).2
    · show ∫ η, ballDensity r (Ψ i j) η = _
      rw [eq1]
      rw [show (volume : Measure ((C i → BondVector) × (↥(C' j ∪ F) → BondVector))) = volume.prod volume from rfl]
      rw [integral_prod _ int1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => (inner a).2)
  have hfinal := hD (C 1 → BondVector) (C 0 → BondVector) (C' 1 → BondVector) (C' 0 → BondVector)
    volume volume volume volume (Rw 1 1) (Rw 1 0) (Rw 0 1) (Rw 0 0) c
    (split 1 1).1 (split 1 0).1 (split 0 1).1 (split 0 0).1
    (split 1 1).2.1 (split 1 0).2.1 (split 0 1).2.1 (split 0 0).2.1 ?_
  · rw [(split 1 1).2.2, (split 0 0).2.2, (split 1 0).2.2, (split 0 1).2.2]
    exact hfinal
  · intro a₁ a₀ b₁ b₀
    have hn : ∀ {ι : Type} [Fintype ι] (η : BondField ι), 0 ≤ radialWeightProd r η :=
      fun η => (radialWeightProd_cutoffFactor_props hρ hRad).2.2.1 η
    have hz : ∀ {ι : Type} [Fintype ι] (η : BondField ι), (¬ ∀ b, ‖η b‖ < ρ) → radialWeightProd r η = 0 :=
      fun η h => (radialWeightProd_cutoffFactor_props hρ hRad).2.2.2 η h
    simp only [Rw]
    by_cases h1 : ∀ x, ‖a₁ x‖ < ρ
    · by_cases h2 : ∀ x, ‖a₀ x‖ < ρ
      · by_cases h3 : ∀ x, ‖b₁ x‖ < ρ
        · by_cases h4 : ∀ x, ‖b₀ x‖ < ρ
          · have hm := hmain a₁ a₀ b₁ b₀ h1 h2 h3 h4
            have hW : 0 ≤ radialWeightProd r a₁ * radialWeightProd r b₁ *
                (radialWeightProd r a₀ * radialWeightProd r b₀) :=
              mul_nonneg (mul_nonneg (hn _) (hn _)) (mul_nonneg (hn _) (hn _))
            have := mul_le_mul_of_nonneg_left hm hW
            calc _ = radialWeightProd r a₁ * radialWeightProd r b₁ *
                  (radialWeightProd r a₀ * radialWeightProd r b₀) *
                  (cutoffIntegral ρ p (fun ξ => Ψ 1 1 fun x => assembledField (C 1) (C' 1) F a₁ b₁ ξ x) *
                    cutoffIntegral ρ p (fun ξ => Ψ 0 0 fun x => assembledField (C 0) (C' 0) F a₀ b₀ ξ x)) := by
                  ring
              _ ≤ _ := this
              _ = _ := by ring
          · simp [hz b₀ h4]
        · simp [hz b₁ h3]
      · simp [hz a₀ h2]
    · simp [hz a₁ h1]
end YangMills.Construction.ClusterExpansionOfAStep
end
