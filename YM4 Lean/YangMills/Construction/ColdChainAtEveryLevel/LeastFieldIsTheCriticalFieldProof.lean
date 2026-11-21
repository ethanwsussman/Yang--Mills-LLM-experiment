import YangMills.Construction.ColdChainAtEveryLevel.EveryHotPlaquetteCostsProof
import YangMills.Construction.ColdChainAtEveryLevel.FramingsOfNoEnergyAgree
import YangMills.Construction.ColdChainAtEveryLevel.LeastFieldIsTheCriticalField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.MinimalField
variable {F : BlockFrame}
theorem exists_chain_chainAction_eq_blockEnergy (hMin : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) : ∃ X : F.FieldChain,
      X F.depth = W ∧ X F.top = V ∧ chainAction a S X = blockEnergy a S F.depth W V := by apply _root_.YangMills.Construction.BlockAverages.HotPlaquetteCost.exists_chain_through <;> assumption
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
theorem relativeEnergy_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain)
    (gW : F.SiteGauge) (X : F.FieldChain) (g Γ : F.SiteGauge) : 0 ≤ relativeEnergy a S z W gW X g Γ := by apply _root_.YangMills.Construction.BlockAverages.relativeEnergy_nonneg_of_nonneg <;> assumption
theorem minimalField_isCritical (hCrit : criticalChainMinimalityStatement)
    (hVal : criticalValueEqMinimalActionStatement) (hAgree : zeroEnergyFramingsAgreeStatement)
    (hMin : minimalChainExistenceStatement) (hLow : gaugedChainLowerBoundStatement) :
    minimalFieldIsCriticalStatement := by
  classical
  intro a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  obtain ⟨L₁, hCrit'⟩ := hCrit a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  obtain ⟨L₂, hVal'⟩ := hVal a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  obtain ⟨L₃, hAgree'⟩ := hAgree a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  refine ⟨max L₁ (max L₂ L₃), fun L hL hge C₁ hC₁ => ?_⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_right (le_of_max_le_right hge)
  obtain ⟨ε, σ₁, C, c, hε, hσ₁, hC, hc, hBound⟩ := hCrit' L hL g1 C₁ hC₁
  obtain ⟨σ₂, hσ₂, hv⟩ := hVal' L hL g2 C₁ hC₁
  obtain ⟨σ₃, hσ₃, hag⟩ := hAgree' L hL g3 C₁ C hC₁ hC
  refine ⟨min σ₁ (min σ₂ σ₃), lt_min hσ₁ (lt_min hσ₂ hσ₃), ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold U hU W' hW'
  have k1 : s ≤ σ₁ := hsσ.trans (min_le_left _ _)
  have k2 : s ≤ σ₂ := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have k3 : s ≤ σ₃ := hsσ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSidePos : 0 < F.blockSide := by
    rw [hFL]
    exact hL.pos
  have hU' : IsCriticalChainOverTop a θ δ Ca C₁ s S V
      (rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V) U := by
    rw [rotatedField_zero]
    exact hU
  have hv0 : ∀ (y : F.Site F.top) (i : Fin 4), ‖(0 : imaginaryQuaternions)‖ ≤ s :=
    fun _ _ => by simpa using hs.le
  have hleast := (hv F m S hFL hamb hm hreg s V (fun _ _ => 0) hs k2 hcold hv0 U hU').1
  rw [rotatedField_zero] at hleast
  obtain ⟨X, hXt, hXn, hAct⟩ := exists_chain_chainAction_eq_blockEnergy hMin a ha.le S W' V
  have hXn' : X F.top = rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V := by
    rw [rotatedField_zero]; exact hXn
  obtain ⟨Γ, hfr, hex⟩ := hBound F m S hFL hamb hm hreg s V (fun _ _ => 0) hs k1 hcold hv0 U hU'
    X (fun _ _ => 1) hXn'
  rw [rotatedField_zero] at hfr hex
  have hGauged : gaugedChainAction a S X (fun _ _ => 1) = blockEnergy a S F.depth W' V := by
    rw [(hLow F a S ha.le hSidePos).2 X, hAct]
  obtain ⟨W0, hW0, -⟩ := (hMin F a S ha.le).2.2.1 F.depth V
  have hExcess : gaugedChainAction a S X (fun _ _ => 1) -
      chartAction a S (referenceFieldChain S V) U V ≤ 0 := by
    have h1 : blockEnergy a S F.depth W' V ≤ blockEnergy a S F.depth W0 V := hW' W0
    have h2 : blockEnergy a S F.depth W0 V = chartAction a S (referenceFieldChain S V) U V :=
      hW0.trans hleast
    rw [hGauged]
    linarith
  set D : F.Cell → ℝ := fun z => relativeEnergy a S z (chartChain (referenceFieldChain S V) U V)
    (chartGauge (referenceFieldChain S V) U) X (fun _ _ => 1) (Γ z) with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z => relativeEnergy_nonneg a ha.le S z _ _ X _ _
  set B := highEnergyCells a ε S X (fun _ _ => 1) with hB
  set Far := cellsFarFromHighEnergy a ε S X (fun _ _ => 1) with hFar
  have hSum0 : 0 ≤ ∑ z ∈ Far, D z := Finset.sum_nonneg fun z _ => hDnn z
  have hCard0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hAll : (B.card : ℝ) + ∑ z ∈ Far, D z ≤ 0 := by
    have := hex.trans hExcess
    by_contra hNo
    push Not at hNo
    have := mul_pos hc hNo
    linarith
  have hBEmpty : B = ∅ := by
    have h1 : (B.card : ℝ) ≤ 0 := by linarith
    have h2 : B.card = 0 := by exact_mod_cast le_antisymm h1 hCard0
    exact Finset.card_eq_zero.1 h2
  have hFarS : ∀ z ∈ S, z ∈ Far := by
    intro z hz
    refine Finset.mem_filter.2 ⟨hz, fun y hy => ?_⟩
    rw [← hB, hBEmpty] at hy
    exact absurd hy (Finset.notMem_empty y)
  have hSumZero : ∑ z ∈ Far, D z = 0 := by linarith
  have hDz : ∀ z ∈ S, D z = 0 := fun z hz =>
    (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hDnn z).1 hSumZero z (hFarS z hz)
  obtain ⟨γ, hγ, hSame⟩ := hag F m S hFL hamb hm hreg s V hs k3 hcold U hU X Γ hXn
    (fun z hz => hfr z (hFarS z hz)) hDz
  rw [hXt] at hSame
  exact ⟨γ, hγ, hSame⟩
end YangMills.Construction.BlockAverages.MinimalField
end
