import YangMills.Construction.RunningCouplingSlope.IteratesOfThePlainAverage
import YangMills.Construction.RunningCouplingSlope.LogarithmsOfThePlainIterates
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProducts
import YangMills.Construction.RunningCouplingSlope.PlainExpansionsDetermineTheBlocks
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadius
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.PlainMeanIterates
open Matrices
open Tower
open Tower.IteratedSmallFieldMeans (smallFormBall)
open Tower.SmoothingContraction (TorusOpNormLE)
variable {L n k j : ℕ}
theorem matExp_inv_eq_matExp_neg (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem norm_expTwist_sub_one_le (hexp : ComplexMatrix2.ExpLogEstimates)
    (A : Edge L n k j → ComplexMatrix2) (hA : A ∈ complexEdgeForms L n k j) (a : ℝ) (ha : a ≤ 1)
    (hbound : ∀ e, ‖A e‖ ≤ a) (e : Edge L n k j) :
    ‖PeriodicLattice.expTwist A (fun _ => 1) e - 1‖ ≤ 2 * a := by
  have hodd : ∀ e, A e.opposite = -A e := hA.2
  have hV : PeriodicLattice.expTwist A (fun _ => 1) e =
      ComplexMatrix2.matExp (Complex.I • A e) := by
    simp only [PeriodicLattice.expTwist, mul_one]
    split_ifs with h
    · rfl
    · rw [matExp_inv_eq_matExp_neg, hodd]
      congr 1
      simp
  rw [hV]
  have h1 := (hexp.1 (Complex.I • A e)).2
  have hn1 : ComplexMatrix2.operatorNorm (Complex.I • A e) = ‖A e‖ := by
    change ‖Complex.I • A e‖ = _
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn1] at h1
  have h5 : |‖A e‖| ≤ 1 := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (hbound e).trans ha
  have h6 := Real.abs_exp_sub_one_le h5
  rw [abs_of_nonneg (norm_nonneg _)] at h6
  have h7 := (abs_le.mp h6).2
  have := hbound e
  linarith
theorem claim_holds (hlog : MeanIterateLogarithms)
    (hnorm : MeanKernelNormBounds)
    (hhol : MeanIteratesHolomorphicOfNear.Claim)
    (hrows : MeanExpansionsLocal.Claim)
    (hexp : ComplexMatrix2.ExpLogEstimates) :
    PlainMeanIterates.Claim := by
  intro L hL
  obtain ⟨ρ₁, hρ₁, H₁⟩ := hlog L hL
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, H₂⟩ := hnorm L hL
  obtain ⟨r, hr, H₃⟩ := hhol L hL
  obtain ⟨ρ₄, hρ₄, H₄⟩ := hrows L hL
  set ρ : ℝ := min (min ρ₁ ρ₂) (min ρ₄ (min (r / 40) (1 / 20))) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₄ (lt_min (by positivity) (by norm_num)))
  have hρa : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρb : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hρc : ρ ≤ ρ₄ := (min_le_right _ _).trans (min_le_left _ _)
  have hρd : ρ ≤ r / 40 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρe : ρ ≤ 1 / 20 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLpos : 0 < L := by have := hL.2; omega
  refine ⟨ρ, max C₂ 2, hρ0, hC₂.trans (le_max_left _ _), fun k n hk hn => ?_⟩
  have hsmall : ∀ {ρ' : ℝ}, ρ ≤ ρ' → ∀ v ∈ smallFormBall L n k ρ, v ∈ smallFormBall L n k ρ' :=
    fun h v hv => ⟨hv.1, hv.2.trans (ENNReal.ofReal_le_ofReal h)⟩
  have hmesh : ∀ j ≤ k, meshAt L k j ≤ 1 := fun j hj => by
    have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
    exact zpow_le_one_of_nonpos₀ h1 (by omega)
  have hmesh0 : ∀ j, 0 ≤ meshAt L k j := fun j => by
    have : (0 : ℝ) ≤ L := by positivity
    exact zpow_nonneg this _
  have hW : ∀ v ∈ smallFormBall L n k ρ, ∀ j ≤ k, ∀ e,
      ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField v) j e - 1) ≤
        20 * meshAt L k j * (maxOperatorNorm v).toReal := by
    intro v hv j hj e
    obtain ⟨A, hA, he, hs⟩ := (H₁ n k hn hk v (hsmall hρa v hv)).1 j hj
    have ht : (maxOperatorNorm v).toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ0.le hv.2
    have ht0 : 0 ≤ (maxOperatorNorm v).toReal := ENNReal.toReal_nonneg
    have hpos : 0 ≤ 10 * meshAt L k j * (maxOperatorNorm v).toReal := by
      have := hmesh0 j
      positivity
    have hbound : ∀ e, ‖A e‖ ≤ 10 * meshAt L k j * (maxOperatorNorm v).toReal := by
      intro e
      have h1 : ENNReal.ofReal ‖A e‖ ≤ maxOperatorNorm A :=
        le_iSup (fun e => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A e))) e
      exact (ENNReal.ofReal_le_ofReal_iff hpos).mp (h1.trans hs)
    have ha : 10 * meshAt L k j * (maxOperatorNorm v).toReal ≤ 1 := by
      have h1 := hmesh j hj
      have h2 := hmesh0 j
      nlinarith
    rw [he]
    have := norm_expTwist_sub_one_le hexp A hA _ ha hbound e
    have e2 : 2 * (10 * meshAt L k j * (maxOperatorNorm v).toReal) =
        20 * meshAt L k j * (maxOperatorNorm v).toReal := by ring
    rw [e2] at this
    exact this
  refine ⟨fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := H₁ n k hn hk v (hsmall hρa v hv)
    have ht : (maxOperatorNorm v).toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ0.le hv.2
    obtain ⟨n1, n2, n3⟩ := H₂ n k hn hk (remainderGaugeField v) (maxOperatorNorm v).toReal
      ENNReal.toReal_nonneg (ht.trans hρb) (fun j hj => (h2 j hj).1)
      (fun j hj e => hW v hv j hj.le e)
    have hmono : ∀ {a a' : ℝ} {σ σ' : Type}
        {T : PeriodicOperators.KernelMatrix (Fin 3 × σ) (Fin 3 × σ')},
        TorusOpNormLE a a' T C₂ → TorusOpNormLE a a' T (max C₂ 2) :=
      fun h => ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    exact ⟨h1, h2, fun j hj c => ⟨(h3 j hj c).1, (h3 j hj c).2.trans (le_max_right _ _)⟩,
      hmono n1, hmono n2, fun s m hsm => hmono (n3 s m hsm)⟩
  · have hhyp : ∀ v ∈ complexEdgeForms L n k 0, maxOperatorNorm v < ENNReal.ofReal ρ → ∀ j < k,
        meanIterate (remainderGaugeField v) j ∈
            fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
          ∀ e, ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField v) j e - 1) < r := by
      intro v hv hs j hj
      have hv' : v ∈ smallFormBall L n k ρ := ⟨hv, hs.le⟩
      refine ⟨((H₁ n k hn hk v (hsmall hρa v hv')).2.1 j hj).1, fun e => ?_⟩
      have h1 := hW v hv' j hj.le e
      have ht : (maxOperatorNorm v).toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ0.le hs.le
      have ht0 : 0 ≤ (maxOperatorNorm v).toReal := ENNReal.toReal_nonneg
      have h2 := hmesh j hj.le
      have h3 := hmesh0 j
      have h4 : meshAt L k j * (maxOperatorNorm v).toReal ≤ ρ := by nlinarith
      nlinarith
    obtain ⟨c1, c2, c3⟩ := H₃ ρ hρ0 n k hn hk hhyp
    exact ⟨c1, c2, c3⟩
  · obtain ⟨r1, r2, r3⟩ := H₄ n k hn hk
    exact ⟨fun c v hv v' hv' => r1 c v (hsmall hρc v hv) v' (hsmall hρc v' hv'),
      fun y v hv v' hv' => r2 y v (hsmall hρc v hv) v' (hsmall hρc v' hv'),
      fun j hj c v hv v' hv' => r3 j hj c v (hsmall hρc v hv) v' (hsmall hρc v' hv')⟩
end YangMills.Construction.RunningCouplingSlope.PlainMeanIterates
end
