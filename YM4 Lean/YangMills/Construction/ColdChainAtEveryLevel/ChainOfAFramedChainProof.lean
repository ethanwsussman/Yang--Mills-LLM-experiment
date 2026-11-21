import YangMills.Construction.ColdChainAtEveryLevel.ChainOfAFramedChain
import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace ChainOfGaugedChain
variable {F : BlockFrame}
theorem re_mul_swap (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem gaugedBlockFit_gaugeTransform {j : ℕ} (γ : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit X (fun y => γ y * k y) (gaugeTransform γ X') c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.gaugedBlockFit_gaugeTransform <;> assumption
theorem blockFit_gaugeTransform_eq (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (γ : F.Site j → UnitQuaternion) (k : F.Site (j + 1) → UnitQuaternion)
    (hγ : ∀ y, γ (refineSite y) = k y)
    (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (gaugeTransform γ X) X' c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.blockFit_gaugeTransform_eq <;> assumption
theorem re_plaquetteHolonomy_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    ((plaquetteHolonomy (gaugeTransform γ U) p : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]).re := by
  obtain ⟨-, -, h, -⟩ := hG F 0 (Nat.succ_pos _) hL
  rw [h γ U p]
  simp only [Submonoid.coe_mul]
  rw [mul_assoc, re_mul_swap, mul_assoc, coe_inv_mul_coe, mul_one]
theorem exists_chain_matching_gauged (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) :
    ∀ j, j ≤ F.top → ∀ (X : F.FieldChain) (k : F.SiteGauge), ∃ X' : F.FieldChain, (∀ m, j ≤ m → X' m = X m) ∧
      (∀ p, ((plaquetteHolonomy (X' 0) p : UnitQuaternion) : ℍ[ℝ]).re =
        ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) ∧
      ∀ i, i < j → ∀ c, blockFit (X' i) (X' (i + 1)) c = gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ X k
    exact ⟨X, fun _ _ => rfl, fun _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj X k
    have hinj := (hG F j (by omega) hL).1
    set γ : F.Site j → UnitQuaternion := fun z => if h : ∃ y, refineSite y = z then k (j + 1) h.choose else 1 with hγ
    have hγd : ∀ y, γ (refineSite y) = k (j + 1) y := by
      intro y
      have hex : ∃ y', refineSite y' = refineSite y := ⟨y, rfl⟩
      simp only [hγ, dif_pos hex]
      rw [hinj hex.choose_spec]
    set X2 : F.FieldChain := Function.update X j (gaugeTransform γ (X j)) with hX2
    set k2 : F.SiteGauge := Function.update k j (fun y => γ y * k j y) with hk2
    have hX2j : X2 j = gaugeTransform γ (X j) := by simp [hX2]
    have hX2o : ∀ m, m ≠ j → X2 m = X m := fun m hm => Function.update_of_ne hm _ _
    have hk2o : ∀ m, m ≠ j → k2 m = k m := fun m hm => Function.update_of_ne hm _ _
    have hk2j : k2 j = fun y => γ y * k j y := by simp [hk2]
    obtain ⟨X', h1, h2, h3⟩ := ih (by omega) X2 k2
    refine ⟨X', fun m hm => ?_, fun p => ?_, fun i hi c => ?_⟩
    · rw [h1 m (by omega), hX2o m (by omega)]
    · rw [h2 p]
      cases j with
      | zero =>
        rw [hX2j]
        exact re_plaquetteHolonomy_gaugeTransform hG hL γ (X 0) p
      | succ i => rw [hX2o 0 (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · rw [h3 i hlt c, hX2o i (by omega)]
        by_cases hs : i + 1 = j
        · subst hs
          rw [hX2j, hk2j]
          exact gaugedBlockFit_gaugeTransform γ _ _ _ c
        · rw [hX2o (i + 1) hs, hk2o (i + 1) hs]
      · rw [h1 i le_rfl, h1 (i + 1) (by omega), hX2j, hX2o (i + 1) (by omega)]
        exact blockFit_gaugeTransform_eq hG hL (by omega) γ _ hγd _ _ c
end ChainOfGaugedChain
theorem chainOfGaugedChainStatement_holds (hG : gaugeCovarianceStatement) : chainOfGaugedChainStatement := by
  intro F hL X k
  obtain ⟨X', h1, h2, h3⟩ := ChainOfGaugedChain.exists_chain_matching_gauged hG hL F.top le_rfl X k
  exact ⟨X', h1 _ le_rfl, h2, h3⟩
end YangMills.Construction.BlockAverages
end
