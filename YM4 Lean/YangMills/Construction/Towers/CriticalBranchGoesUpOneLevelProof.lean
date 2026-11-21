import YangMills.Construction.Towers.AxialGaugeOfTheLift
import YangMills.Construction.Towers.CriticalBranchGoesUpOneLevel
import YangMills.Construction.Towers.ExtendedFamilyKeepsTheLowerLevels
import YangMills.Construction.Towers.GaugeCovarianceOfTheLift
import YangMills.Construction.Towers.IsometryCovarianceOfTheLift
import YangMills.Construction.Towers.MinimisersOnTheFibresNearOne
import YangMills.Construction.Towers.MultiplierOfTheNextLevel
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranch
import YangMills.Construction.Towers.SecondFormOfTheNextLevel
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.Tower.CriticalBranchData
variable {L n k i : ℕ} (b : CriticalBranchData L n k)
  (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2)
theorem extendLevel_energy_succ :
    (b.extendLevel i p).energy (i + 1) = fun U => b.gaugeFixedEnergy i (p U) := by
  simp [extendLevel]
theorem extendLevel_energy_of_le {j : ℕ} (hji : j ≤ i) :
    (b.extendLevel i p).energy j = b.energy j := by
  have hne : j ≠ i + 1 := by omega
  simp [extendLevel, Function.update_of_ne hne]
theorem extendLevel_prolong_self : (b.extendLevel i p).prolong i = p := by
  simp [extendLevel]
theorem extendLevel_gaugeFixedEnergy :
    (b.extendLevel i p).gaugeFixedEnergy i = b.gaugeFixedEnergy i := by
  funext V
  simp [gaugeFixedEnergy, extendLevel_energy_of_le b p le_rfl]
theorem extendLevel_hessianAtOne_succ :
    (b.extendLevel i p).hessianAtOne (i + 1) =
      leftSecondDeriv (fun U => b.gaugeFixedEnergy i (p U)) (trivialField L n k (i + 1)) := by
  funext e e'
  simp [hessianAtOne, extendLevel_energy_succ]
theorem extendLevel_stepQuadratic : (b.extendLevel i p).stepQuadratic i = b.stepQuadratic i := by
  funext ξ
  simp [stepQuadratic, hessianAtOne, extendLevel_energy_of_le b p le_rfl]
end YangMills.Construction.Tower.CriticalBranchData
namespace YangMills.Construction.Tower
theorem criticalBranchUpOneLevel_of_steps
    (hForm : StepQuadraticForm)
    (hMin : FibreMinimisersNearOne)
    (hLow : ExtendLevelPreservesLower)
    (hAxial : AxialGaugeOfProlongation)
    (hGauge : LiftGaugeCovariance.Statement)
    (hIso : LiftSymmetryCovariance.Statement)
    (hSecond : NextLevelHessian.Statement)
    (hMult : NextLevelComposite.Statement) :
    CriticalBranchUpOneLevel := by
  intro L n k i hL hn hi b hb
  obtain ⟨han, -, hgrad, hsec, hpos⟩ := hForm L n k i hL hn hi b hb
  obtain ⟨𝒰, ε, p, hp⟩ := hMin L n k i hL hn hi (b.gaugeFixedEnergy i) han hgrad
    fun ξ hξ hq h0 => by rw [hsec ξ hξ]; exact hpos ξ hξ hq h0
  have hlow := hLow L n k i b p hb
  have hax := hAxial L n k i hL hn hi b 𝒰 ε p hb hp
  have hg := hGauge L n k i hL hn hi b 𝒰 ε p hb hp
  have his := hIso L n k i hL hn hi b 𝒰 ε p hb hp
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hSecond L n k i hL hn hi b 𝒰 ε p hb hp
  obtain ⟨m1, m2, m3⟩ := hMult L n k i hL hn hi b 𝒰 ε p hb hp
  have hE := CriticalBranchData.extendLevel_energy_succ b p
  have hEi := CriticalBranchData.extendLevel_energy_of_le b p (le_refl i)
  have hpr := CriticalBranchData.extendLevel_prolong_self b p
  have hfx := CriticalBranchData.extendLevel_gaugeFixedEnergy b p
  have hhs := CriticalBranchData.extendLevel_hessianAtOne_succ b p
  have hsq := CriticalBranchData.extendLevel_stepQuadratic b p
  refine ⟨b.extendLevel i p, ?_⟩
  constructor
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.analytic_energy j hj
    · rw [hE]; exact s1
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.energy_nonneg j hj
    · rw [hE]; exact s2
  · exact hlow.energy_bottom
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.analytic_prolong j hj
    · rw [hpr]; exact hp.analytic_section
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.prolong_trivial j hj
    · rw [hpr]; exact hp.section_trivial
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.prolong_section j hj
    · rw [hpr, hE, hEi, hfx]
      filter_upwards [hp.smoothing_section, hax] with U h1 h2
      exact ⟨h1, h2.1, h2.2, rfl⟩
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.fibre_structure j hj
    · rw [hpr, hfx]
      exact ⟨𝒰, hp.isOpenNhd, hp.fibre_structure, nearIdentityBall L n k j ε, hp.ball_mem_nhds,
        hp.unique_critical⟩
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.energy_gauge_invariant j hj
    · rw [hE]
      exact ⟨hg.1.mono fun q h => h.2, hg.2.mono fun U h v hv hc => (h v hv hc).2⟩
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.prolong_gauge_equivariant j hj
    · rw [hpr]
      exact ⟨hg.1.mono fun q h => h.1, hg.2.mono fun U h v hv hc => (h v hv hc).1⟩
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.energy_symmetry_invariant j hj
    · rw [hE]
      exact his.mono fun U h f hf => (h f hf).2
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.prolong_symmetry_equivariant j hj
    · rw [hpr]
      exact his.mono fun U h f hf => (h f hf).1
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.energy_trivial j hj
    · rw [hE]; exact s3
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.gradient_trivial j hj
    · simp only [CriticalBranchData.energyGradient, hE]; exact s4
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.hessianAtOne_nonneg j hj
    · rw [hhs]; exact s5
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.hessianAtOne_null_iff j hj
    · rw [hhs]; exact s6
  · exact hlow.hessianAtOne_bottom
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.hessianAtOne_isLeast j hj
    · rw [hhs, hsq]; exact s7
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.hessianAtOne_minimizer_iff j hj
    · rw [hhs, hsq, hpr]; exact s8
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.prolongComp_section j hj
    · exact m1
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow.prolongComp_lift j hj
    · rw [hpr]; exact m2
  · intro j hj
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact hlow.prolongComp_critical j hj
    · exact m3
end YangMills.Construction.Tower
end
