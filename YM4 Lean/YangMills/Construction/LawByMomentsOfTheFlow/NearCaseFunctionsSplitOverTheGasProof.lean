import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ClassesAreCountedAtTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.GasSumsAtABlockProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansInTheSettingsAreBorel
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesOnTwoToriProof
import YangMills.Construction.LawByMomentsOfTheFlow.NearCaseFunctionsSplitOverTheGas
import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsInTwoSettings
import YangMills.Construction.LawInAState.CellsOfAPair
import YangMills.Construction.TransfersOffTheWalk.FunctionsOfFarSpinsSplit
import YangMills.Construction.TransfersOffTheWalk.SettingsOfConfigurationsAgree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Dobrushin TorusFields TorusLumps StepGas StepSettings RenormalizationStepParameters WeightedResponses MomentLaw
  BlockOffsets CoreColumns
namespace MomentLaw
namespace CaseSplit
section Means
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def configMean (G : GasGround R n) (F : CaseFunction R n) (σ : G.Config) : ℝ :=
  FreeEnergies.settingMean (configSetting G σ) (G.badBondsOf σ) F
private theorem abs_configMean_le {F : CaseFunction R n} {y : TorusSite (n * R.params.side)} {K : ℝ} {ρ : ℕ}
    (hK : 0 ≤ K) (hF : IsNearlyLocalCaseFunction R y ρ K F) (G : GasGround R n) (σ : G.Config) :
    |configMean G F σ| ≤ K :=
  abs_weightedMean_le hK fun _ => hF.abs_le _ _ _ _ _
end Means
section Spins
private theorem isAdmissible_vacateOutside {I : Type} [DecidableEq I] {S : I → Type} (A : PairConstraint S)
    (M : Finset I) {σ : ∀ i, S i} (h : A.IsAdmissible σ) : A.IsAdmissible (vacateOutside A M σ) := by
  intro i j hij
  unfold vacateOutside
  by_cases hi : i ∈ M
  · by_cases hj : j ∈ M
    · simpa [hi, hj] using h i j hij
    · simp only [hi, hj, if_true, if_false]
      exact A.compatible_symm _ _ _ _ (A.vacant_compatible j i _)
  · simp only [hi, if_false]
    exact A.vacant_compatible i j _
abbrev _root_.YangMills.SharedProofs.p71124 := @isAdmissible_vacateOutside
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
private def nearSpins (G : GasGround R n) (Y : TorusSite n) (m : ℕ) : Finset G.GasSpin :=
  Finset.univ.filter fun i => ∃ h, OffsetInBox m h ∧ Y + siteOfInt h ∈ i.1.core
private theorem sum_nearSpins_le (G : GasGround R n) {f : G.GasSpin → ℝ} (hf : ∀ i, 0 ≤ f i) {e₀ : ℝ}
    (he : ∀ u : TorusSite n, ∑ i : G.GasSpin with u ∈ i.1.core, f i ≤ e₀) (h0 : 0 ≤ e₀) (Y : TorusSite n) (m : ℕ) :
    ∑ i ∈ nearSpins G Y m, f i ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 4 * e₀ := by
  classical
  set B := thickening m ({Y} : Finset (TorusSite n)) with hB
  have hnn : ∀ (i : G.GasSpin) (u : TorusSite n), 0 ≤ if u ∈ i.1.core then f i else 0 := fun i u => by
    split_ifs
    · exact hf i
    · exact le_rfl
  have h1 : ∀ i ∈ nearSpins G Y m, f i ≤ ∑ u ∈ B, if u ∈ i.1.core then f i else 0 := by
    intro i hi
    obtain ⟨h, hh, hm⟩ := (Finset.mem_filter.mp hi).2
    have hu : Y + siteOfInt h ∈ B := by
      refine (mem_thickening _ _ _).mpr ⟨Y, Finset.mem_singleton_self _, ?_⟩
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact supDist_add_siteOfInt_le Y h m fun l => by
        have h1 : |h l| ≤ (m : ℤ) := hh l
        rw [Int.abs_eq_natAbs] at h1
        omega
    calc f i = if Y + siteOfInt h ∈ i.1.core then f i else 0 := by rw [if_pos hm]
      _ ≤ _ := Finset.single_le_sum (f := fun u => if u ∈ i.1.core then f i else 0) (fun u _ => hnn i u) hu
  calc ∑ i ∈ nearSpins G Y m, f i ≤ ∑ i ∈ nearSpins G Y m, ∑ u ∈ B, (if u ∈ i.1.core then f i else 0) :=
        Finset.sum_le_sum h1
    _ ≤ ∑ i, ∑ u ∈ B, (if u ∈ i.1.core then f i else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
          Finset.sum_nonneg fun u _ => hnn i u
    _ = ∑ u ∈ B, ∑ i, (if u ∈ i.1.core then f i else 0) := Finset.sum_comm
    _ = ∑ u ∈ B, ∑ i : G.GasSpin with u ∈ i.1.core, f i := by simp only [Finset.sum_filter]
    _ ≤ ∑ _u ∈ B, e₀ := Finset.sum_le_sum fun u _ => he u
    _ = (B.card : ℝ) * e₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast TorusCounting.card_thickening_singleton_le m Y) h0
private theorem coreWeight_le_of_near (G : GasGround R n) {Y Y' : TorusSite n} {m D : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hY : D ≤ supDist Y Y') (i : G.GasSpin) (hc : i.1.core.Nonempty) (hi : i ∈ nearSpins G Y' m) :
    coreWeight κ Y i.1.core ≤
      (i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * Real.exp (-(κ * ((D : ℝ) - m))) := by
  classical
  obtain ⟨h, hh, hm⟩ := (Finset.mem_filter.mp hi).2
  have hne : {d | ∃ y ∈ ({Y} : Finset (TorusSite n)), ∃ y' ∈ i.1.core, supDist y y' = d}.Nonempty := by
    obtain ⟨u, hu⟩ := hc
    exact ⟨_, Y, Finset.mem_singleton_self _, u, hu, rfl⟩
  obtain ⟨y, hy, u', hu', hgap⟩ := Nat.sInf_mem hne
  rw [Finset.mem_singleton.mp hy] at hgap
  have hg : supDist Y u' = setGap {Y} i.1.core := hgap
  have h1 : supDist Y' (Y' + siteOfInt h) ≤ m := supDist_add_siteOfInt_le Y' h m fun l => by
    have h1 : |h l| ≤ (m : ℤ) := hh l
    rw [Int.abs_eq_natAbs] at h1
    omega
  have h2 : supDist u' (Y' + siteOfInt h) ≤ siteDiameter i.1.core := by
    unfold siteDiameter
    exact (Finset.le_sup (f := fun z => supDist u' z) hm).trans
      (Finset.le_sup (f := fun y => i.1.core.sup fun z => supDist y z) hu')
  have h3 := supDist_triangle Y u' Y'
  have h4 := supDist_triangle u' (Y' + siteOfInt h) Y'
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm (Y' + siteOfInt h) Y'] at h4
  have h5 : D ≤ setGap {Y} i.1.core + siteDiameter i.1.core + m := by omega
  have h5' : (D : ℝ) ≤ (setGap {Y} i.1.core : ℝ) + siteDiameter i.1.core + m := by exact_mod_cast h5
  unfold coreWeight
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  nlinarith
private theorem occupies_iff_of_eq {γ γ' : GasFamily R n} {θ : GasSupport R n} (h : γ θ = γ' θ) :
    γ.Occupies θ ↔ γ'.Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.occupies_congr <;> assumption
private theorem baseAt_eq_of_core {γ γ' : GasFamily R n} {y : TorusSite n}
    (h : ∀ θ : GasSupport R n, y ∈ θ.core → γ θ = γ' θ) : γ.baseAt y = γ'.baseAt y := by apply _root_.YangMills.Construction.InBoxTransfer.baseAt_congr <;> assumption
private theorem familyOf_eq_vacateOutside (G : GasGround R n) {σ : G.Config} {Y : TorusSite n} {m : ℕ}
    {M : Finset G.GasSpin} (hM : M = nearSpins G Y m) {θ : GasSupport R n} {e : Fin 4 → ℤ}
    (he : OffsetInBox m e) (hc : Y + siteOfInt e ∈ θ.core) :
    G.familyOf σ θ = G.familyOf (vacateOutside G.pairConstraint M σ) θ := by
  classical
  unfold GasGround.familyOf
  by_cases hs : G.IsGasSupport θ
  · have him : (⟨θ, hs⟩ : G.GasSpin) ∈ M := by
      rw [hM]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, hc⟩
    rw [dif_pos hs, dif_pos hs]
    simp [vacateOutside, him]
  · rw [dif_neg hs, dif_neg hs]
end Spins
section Numbers
private def decouplingBound : ℝ := 2 * 16 * 2 + 96 * 16 ^ 2 + 16 * 4 ^ 16
private theorem decouplingBound_nonneg : 0 ≤ decouplingBound := by
  unfold decouplingBound
  positivity
private theorem decouplingConstant_le {Q : ℕ} (hQ : Q ≤ 16) : decouplingConstant 0 Q ≤ decouplingBound := by
  have hQ' : (Q : ℝ) ≤ 16 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have h4 : ((2 : ℝ) * 2) ^ Q ≤ 4 ^ 16 := by
    have : ((2 : ℝ) * 2) = 4 := by norm_num
    rw [this]
    exact pow_le_pow_right₀ (by norm_num) hQ
  have h1 : (0 : ℝ) ≤ ((2 : ℝ) * 2) ^ Q := by positivity
  unfold decouplingConstant polyMomentConstant decouplingBound
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
  have h2 : (Q : ℝ) ^ 2 ≤ 16 ^ 2 := pow_le_pow_left₀ hQ0 hQ' 2
  have h3 : (Q : ℝ) * ((2 : ℝ) * 2) ^ Q ≤ 16 * 4 ^ 16 := mul_le_mul hQ' h4 h1 (by norm_num)
  nlinarith
private theorem far_tail_le {rt E₀ : ℝ} (hrt : 0 < rt) (hE₀ : 0 ≤ E₀) (hE₁ : E₀ ≤ 1) (D : ℕ) :
    4 * Real.exp (-(rt * ((D / 8 : ℕ) : ℝ) / 2 ^ 4)) + Real.exp (-(rt * D / 2 ^ 6 / 2)) +
        (1 + rt * D / 2 ^ 6) ^ 0 * (Real.exp (-(rt / 2 ^ 6 * ((D : ℝ) - 2 * ((D / 8 : ℕ) : ℝ)))) *
          (((2 * (D / 8) + 1 : ℕ) : ℝ) ^ 4 * E₀)) ≤
      (4 * Real.exp (rt / 2 ^ 4) + 1 + 24 / (rt / 2 ^ 8) ^ 4 * Real.exp (rt / 2 ^ 8)) *
        Real.exp (-(rt * D / 2 ^ 7)) := by
  set m := D / 8 with hm
  set r7 := Real.exp (-(rt * D / 2 ^ 7)) with hr7
  have hm1 : (m : ℝ) ≤ D / 8 := by
    have h : 8 * m ≤ D := by omega
    have h' : (8 : ℝ) * m ≤ D := by exact_mod_cast h
    linarith
  have hm2 : (D : ℝ) / 8 - 1 ≤ m := by
    have h : D ≤ 8 * m + 7 := by omega
    have h' : (D : ℝ) ≤ 8 * m + 7 := by exact_mod_cast h
    linarith
  have t1 : Real.exp (-(rt * (m : ℝ) / 2 ^ 4)) ≤ Real.exp (rt / 2 ^ 4) * r7 := by
    rw [hr7, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hm2 hrt.le
    nlinarith
  have t2 : Real.exp (-(rt * D / 2 ^ 6 / 2)) = r7 := by
    rw [hr7]
    congr 1
    ring
  set a := rt / 2 ^ 8 with ha
  have hy0 : 0 ≤ a * ((D : ℝ) + 1) := by positivity
  have hfac := Real.pow_div_factorial_le_exp _ hy0 4
  have hfac' : (a * ((D : ℝ) + 1)) ^ 4 / 24 ≤ Real.exp (a * ((D : ℝ) + 1)) := by
    have e : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rwa [e] at hfac
  have ha4 : 0 < a ^ 4 := by positivity
  have hp : ((D : ℝ) + 1) ^ 4 ≤ 24 / a ^ 4 * Real.exp (a * ((D : ℝ) + 1)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha4]
    have e : (a * ((D : ℝ) + 1)) ^ 4 = ((D : ℝ) + 1) ^ 4 * a ^ 4 := by ring
    rw [e] at hfac'
    linarith
  have hm3 : ((2 * m + 1 : ℕ) : ℝ) ≤ (D : ℝ) + 1 := by
    push_cast
    linarith
  have hm4 : ((2 * m + 1 : ℕ) : ℝ) ^ 4 ≤ ((D : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm3 4
  have hK0 : 0 ≤ 24 / a ^ 4 := by positivity
  set ex := Real.exp (-(rt / 2 ^ 6 * ((D : ℝ) - 2 * (m : ℝ)))) with hex
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have t3 : ex * (((2 * m + 1 : ℕ) : ℝ) ^ 4 * E₀) ≤ 24 / a ^ 4 * Real.exp a * r7 := by
    have h1 : ((2 * m + 1 : ℕ) : ℝ) ^ 4 * E₀ ≤ 24 / a ^ 4 * Real.exp (a * ((D : ℝ) + 1)) := by
      calc _ ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 4 * 1 := mul_le_mul_of_nonneg_left hE₁ (by positivity)
        _ = ((2 * m + 1 : ℕ) : ℝ) ^ 4 := mul_one _
        _ ≤ _ := hm4.trans hp
    have h2 : ex * Real.exp (a * ((D : ℝ) + 1)) ≤ Real.exp a * r7 := by
      rw [hex, hr7, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hm1 hrt.le
      rw [ha]
      nlinarith
    calc ex * (((2 * m + 1 : ℕ) : ℝ) ^ 4 * E₀) ≤ ex * (24 / a ^ 4 * Real.exp (a * ((D : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1 hex0
      _ = 24 / a ^ 4 * (ex * Real.exp (a * ((D : ℝ) + 1))) := by ring
      _ ≤ 24 / a ^ 4 * (Real.exp a * r7) := mul_le_mul_of_nonneg_left h2 hK0
      _ = _ := by ring
  rw [t2, pow_zero, one_mul]
  nlinarith
private theorem gasRate_nonneg (T : ParameterAssignment) (hD : T.Admissible) : 0 ≤ T.gasRate := by apply _root_.YangMills.SharedProofs.p19490 <;> assumption
end Numbers
section Core
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem parentBlock_mem_core (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) :
    parentBlock R.params.side z ∈ θ.core := by apply _root_.YangMills.Construction.StepGas.GasSupport.parentBlock_mem_core <;> assumption
private theorem mem_badBondsOf_iff (G : GasGround R n) {σ σ' : G.Config} {c : TorusBond (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, parentBlock R.params.side c.1 ∈ θ.core → G.familyOf σ θ = G.familyOf σ' θ) :
    c ∈ G.badBondsOf σ ↔ c ∈ G.badBondsOf σ' := by
  classical
  have key : ∀ {τ τ' : G.Config},
      (∀ θ : GasSupport R n, parentBlock R.params.side c.1 ∈ θ.core → G.familyOf τ θ = G.familyOf τ' θ) →
      c ∈ G.badBondsOf τ → c ∈ G.badBondsOf τ' := by
    intro τ τ' hh hc
    unfold GasGround.badBondsOf at hc ⊢
    rcases Finset.mem_union.mp hc with h1 | h1
    · exact Finset.mem_union_left _ h1
    · obtain ⟨θ, hθ, hcθ⟩ := Finset.mem_biUnion.mp h1
      have hcore : parentBlock R.params.side c.1 ∈ θ.core :=
        parentBlock_mem_core θ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcθ))
      refine Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hcθ⟩)
      exact (occupies_iff_of_eq (hh θ hcore)).mp (Finset.mem_filter.mp hθ).2
  exact ⟨key h, key fun θ hθ => (h θ hθ).symm⟩
private theorem core_nonempty (G : GasGround R n) (i : G.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
private theorem sum_core_weighted_le (G : GasGround R n) {c κ e₀ : ℝ} (hκ : κ ≤ 2 * R.params.rt) (hκ0 : 0 ≤ κ)
    (hcnt : ∀ u : TorusSite n, ∑ θ ∈ supportsAtBlock R.params.side (clusterRange R.coupling) u,
      clusterWeight R.params.side c R.coupling (clusterRange R.coupling) θ *
        ((supportCore R.params.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
        Real.exp (2 * R.params.rt * (siteDiameter (supportCore R.params.side (clusterRange R.coupling) θ) : ℝ)) ≤ e₀)
    (u : TorusSite n) :
    ∑ i : G.GasSpin with u ∈ i.1.core,
      (i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity c i ≤ e₀ := by
  classical
  refine le_trans ?_ (hcnt u)
  set F : Finset G.GasSpin := Finset.univ.filter fun i : G.GasSpin => u ∈ i.1.core with hF
  have hinj : Set.InjOn (Subtype.val : G.GasSpin → GasSupport R n) F := Subtype.val_injective.injOn
  have e1 := Finset.sum_image (f := fun θ : GasSupport R n =>
      clusterWeight R.params.side c R.coupling (clusterRange R.coupling) θ *
      ((supportCore R.params.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
      Real.exp (2 * R.params.rt * (siteDiameter (supportCore R.params.side (clusterRange R.coupling) θ) : ℝ))) hinj
  have hsub : ∑ i ∈ F, clusterWeight R.params.side c R.coupling (clusterRange R.coupling) i.1 *
      ((supportCore R.params.side (clusterRange R.coupling) i.1).card : ℝ) ^ 4 *
      Real.exp (2 * R.params.rt * (siteDiameter (supportCore R.params.side (clusterRange R.coupling) i.1) : ℝ)) ≤
      ∑ θ ∈ supportsAtBlock R.params.side (clusterRange R.coupling) u,
        clusterWeight R.params.side c R.coupling (clusterRange R.coupling) θ *
        ((supportCore R.params.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
        Real.exp (2 * R.params.rt * (siteDiameter (supportCore R.params.side (clusterRange R.coupling) θ) : ℝ)) := by
    refine le_trans (le_of_eq e1.symm) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun θ _ _ => ?_
    · intro θ hθ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2.isCluster, (Finset.mem_filter.mp hi).2⟩
    · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg _) 4)) (Real.exp_pos _).le
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hsub
  have hc1 : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty G i).card_pos
  have hc4 : (i.1.core.card : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := by
    calc (i.1.core.card : ℝ) = (i.1.core.card : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hc1 (by norm_num)
  have he : Real.exp (κ * (siteDiameter i.1.core : ℝ)) ≤ Real.exp (2 * R.params.rt * (siteDiameter i.1.core : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg _))
  have hz0 : 0 ≤ G.spinActivity c i := (Real.exp_pos _).le
  calc (i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity c i
      ≤ (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (siteDiameter i.1.core : ℝ)) * G.spinActivity c i :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc4 he (Real.exp_pos _).le (by positivity)) hz0
    _ = G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 *
        Real.exp (2 * R.params.rt * (siteDiameter i.1.core : ℝ)) := by ring
end Core
section Main
set_option maxHeartbeats 4000000 in
private theorem split_main (hB : nearFunctionsTwoSettingsStatement)
    (hfs : LocalFunctionsDecoupleStatement)
    (hsa : LocalSettingsAgree)
    (hbor : FreeEnergies.settingMeanMeasurableStatement) (hcol : ClusterExpansionOfAStep.GasColumnsSmall)
    (hset : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hcnt : ClusterBounds.ClusterSumBound) :
    nearCaseFunctionsSplitStatement := by
  classical
  obtain ⟨r₁, p₁, g₁⟩ := hB
  obtain ⟨r₂, p₂, g₂⟩ := hbor
  obtain ⟨r₃, p₃, g₃⟩ := hcol
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hT hrt Kr => ?_⟩
  obtain ⟨y₁, H₁⟩ := g₁ T hT (hrt.trans (min_le_left _ _)) Kr
  obtain ⟨y₂, H₂⟩ := g₂ T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) Kr
  obtain ⟨y₃, H₃⟩ := g₃ T hT (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y₄, H₄⟩ := hset T hT
  obtain ⟨y₅, H₅⟩ := hcnt T hT
  have hrt0 := hT.rt_pos
  have hch := gasRate_nonneg T hT
  obtain ⟨Cf, hCfd⟩ : ∃ Cf : ℝ, Cf = decouplingBound *
      (4 * Real.exp (T.rt / 2 ^ 4) + 1 + 24 / (T.rt / 2 ^ 8) ^ 4 * Real.exp (T.rt / 2 ^ 8)) := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by
    rw [hCfd]
    exact mul_nonneg decouplingBound_nonneg (by positivity)
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ T.floorMin) (200 * T.B)), Cf, hCf0,
    fun y hy R A hAK hAt n _ G hGr p Q z K ra D hp16 hQ hD hap => ?_⟩
  have hra0 : (0 : ℝ) ≤ ra := Nat.cast_nonneg _
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨hy1, hy2⟩, hy3, hy4⟩, ⟨hy5, hy0⟩, hyB⟩ := hy
  have hRT := hAt.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hRT
  have hB1 : (1 : ℝ) ≤ T.B := hT.B_ge
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have hx0 : 0 < R.coupling := by linarith
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hσR : 0 < R.params.threshold := by rw [hRσ]; exact hT.σ_pos
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have hrow := hstep.1
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hGr with h | h
    · exact h.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ hLpos) h.isBlockSide.2
  set off : G.GasSpin → Prop := fun j => j.1.Touches (∅ : Finset (TorusSite n)) with hoff
  obtain ⟨h, hc⟩ := H₃ y hy3 R hRT hxx n G hGr off
  have : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight) :=
    hc.isProbabilityMeasure
  have hae : ∀ᵐ σ ∂G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight, G.pairConstraint.IsAdmissible σ :=
    hc.isSpecification.ae_admissible
  have hexp0 := Real.exp_pos (-(R.params.rt * D / 2 ^ 7))
  by_cases hcard : p ≤ 1
  · interval_cases p
    · have e : G.expectation ∅ (fun _ => (1 : ℝ)) = 1 := by
        show ∫ _σ, (1 : ℝ) ∂G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight = 1
        simp
      simp only [Finset.univ_eq_empty, Finset.prod_empty, e, sub_self, abs_zero, pow_zero, mul_one]
      positivity
    · have hK0 : 0 ≤ K := (abs_nonneg _).trans
        ((hQ 0).abs_le (trivialField _) ∅ (StateLaws.emptyLabelling R.labels.Ω) ∅ (fun c => G.groundBases c))
      simp only [Fin.prod_univ_one, sub_self, abs_zero]
      positivity
  have hp2 : 2 ≤ p := by omega
  have hK0 : 0 ≤ K := (abs_nonneg _).trans
    ((hQ ⟨0, by omega⟩).abs_le (trivialField _) ∅ (StateLaws.emptyLabelling R.labels.Ω) ∅ (fun c => G.groundBases c))
  have hx1 : (1 : ℝ) ≤ R.range := by
    have : 1 ≤ R.range := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
    exact_mod_cast this
  have hDr : 2 ^ 10 ≤ (D : ℝ) := by nlinarith
  have hDbig : 2 ^ 10 ≤ D := by exact_mod_cast hDr
  set m := D / 8 with hm
  have hmD : (D : ℝ) / 8 - 1 ≤ m := by
    have h1 : D ≤ 8 * m + 7 := by omega
    have h2 : (D : ℝ) ≤ 8 * m + 7 := by exact_mod_cast h1
    linarith
  set Yb : Fin p → TorusSite n := fun i => parentBlock R.params.side (z i) with hYb
  obtain ⟨i₁, i₂, hi12⟩ : ∃ i₁ i₂ : Fin p, i₁ ≠ i₂ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hkn : 2 * m + 2 < n := by
    have h1 := hap i₁ i₂ hi12
    have h2 := SettingShifts.two_mul_supDist_le (parentBlock R.params.side (z i₁)) (parentBlock R.params.side (z i₂))
    omega
  have hm4 : (ra : ℝ) / 4 + (R.range : ℝ) / (4 * R.params.side) ≤ m := by
    have hL1 : (1 : ℝ) ≤ R.params.side := by exact_mod_cast hLpos
    have h1 : (R.range : ℝ) / (4 * R.params.side) ≤ R.range := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hm1 : 1 ≤ m := by omega
  have hram : (ra : ℝ) ≤ m := by nlinarith
  set κ := R.params.rt / 2 ^ 6 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Em := Real.exp (κ * (m : ℝ)) with hEm
  have hEm0 : 0 < Em := Real.exp_pos _
  set M : Fin p → Finset G.GasSpin := fun i => nearSpins G (Yb i) m with hM
  set w : Fin p → G.GasSpin → ℝ := fun i j => Em * G.coreWeightFrom (Yb i) j with hw
  set pc : Fin p → G.Config → ℝ := fun i σ =>
    if G.pairConstraint.IsAdmissible σ then configMean G (Q i) σ else 0 with hpc'
  set ee := Real.exp (-(8 * T.gasRate * R.coupling)) with hee
  have hee0 : 0 ≤ ee := (Real.exp_pos _).le
  have hee1 : ee ≤ 1 := by
    rw [hee, Real.exp_le_one_iff]
    have : 0 ≤ 8 * T.gasRate * R.coupling := by positivity
    linarith
  set ε := 4 * Real.exp (-(R.params.rt * (m : ℝ) / 2 ^ 4)) with hε
  set δ := Real.exp (-(κ * ((D : ℝ) - 2 * (m : ℝ)))) * (((2 * m + 1 : ℕ) : ℝ) ^ 4 * ee) with hδ
  set t := R.params.rt * D / 2 ^ 6 with ht
  have hcols : ∀ g, G.pairConstraint.HasDobrushinColumns (G.referenceMeasureOff off) h.measurable_weightDensity
      (G.influenceMatrix T.gasRate) (w g) := by
    intro g
    refine ⟨hc.influenceMatrix_nonneg, fun i => ?_, hc.kernel_le, fun j => ?_⟩
    · have hc1 : 0 < (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty G i).card_pos
      exact mul_pos hEm0 (mul_pos hc1 (Real.exp_pos _))
    · have h1 := hc.column_le (Yb g) j
      have h2 : 0 ≤ G.coreWeightFrom (Yb g) j := by
        unfold GasGround.coreWeightFrom coreWeight
        positivity
      have h3 : G.coreWeightFrom (Yb g) j * Real.exp (-(6 * T.gasRate * R.coupling)) ≤
          G.coreWeightFrom (Yb g) j * (1 / 2) :=
        mul_le_mul_of_nonneg_left hc.exp_le_half h2
      calc ∑ i, w g i * G.influenceMatrix T.gasRate i j =
            Em * ∑ i, G.coreWeightFrom (Yb g) i * G.influenceMatrix T.gasRate i j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by simp only [hw]; ring
        _ ≤ Em * (G.coreWeightFrom (Yb g) j * (1 / 2)) := mul_le_mul_of_nonneg_left (h1.trans h3) hEm0.le
        _ = w g j / 2 := by simp only [hw]; ring
  have hw1 : ∀ g, ∀ i ∈ M g, 1 ≤ w g i := by
    intro g i hi
    obtain ⟨h', hh, hm'⟩ := (Finset.mem_filter.mp hi).2
    have hgap : setGap {Yb g} i.1.core ≤ m := by
      have h0 : setGap {Yb g} i.1.core ≤ supDist (Yb g) (Yb g + siteOfInt h') :=
        Nat.sInf_le ⟨Yb g, Finset.mem_singleton_self _, _, hm', rfl⟩
      refine h0.trans ?_
      exact supDist_add_siteOfInt_le _ h' m fun l => by
        have h1 : |h' l| ≤ (m : ℤ) := hh l
        rw [Int.abs_eq_natAbs] at h1
        omega
    have hgap' : (setGap {Yb g} i.1.core : ℝ) ≤ m := by exact_mod_cast hgap
    have hc1 : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty G i).card_pos
    have h2 : 1 ≤ Em * Real.exp (-(κ * (setGap {Yb g} i.1.core : ℝ))) := by
      rw [hEm, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have h3 : 0 ≤ Em * Real.exp (-(κ * (setGap {Yb g} i.1.core : ℝ))) := by positivity
    show 1 ≤ Em * ((i.1.core.card : ℝ) * Real.exp (-(κ * (setGap {Yb g} i.1.core : ℝ))))
    nlinarith
  have hδle : ∀ g g', g ≠ g' → ∑ i ∈ M g', w g i * G.spinActivity T.gasRate i ≤ δ := by
    intro g g' hgg
    have hf : ∀ i ∈ M g', w g i * G.spinActivity T.gasRate i ≤ Real.exp (-(κ * ((D : ℝ) - 2 * (m : ℝ)))) *
        ((i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity T.gasRate i) := by
      intro i hi
      have hs := coreWeight_le_of_near G hκ0 (hap g g' hgg) i (core_nonempty G i) hi
      have hz0 : 0 ≤ G.spinActivity T.gasRate i := (Real.exp_pos _).le
      have e : Em * Real.exp (-(κ * ((D : ℝ) - m))) = Real.exp (-(κ * ((D : ℝ) - 2 * (m : ℝ)))) := by
        rw [hEm, ← Real.exp_add]
        congr 1
        ring
      calc w g i * G.spinActivity T.gasRate i ≤ Em * ((i.1.core.card : ℝ) *
            Real.exp (κ * (siteDiameter i.1.core : ℝ)) *
            Real.exp (-(κ * ((D : ℝ) - m)))) * G.spinActivity T.gasRate i :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hEm0.le) hz0
        _ = (Em * Real.exp (-(κ * ((D : ℝ) - m)))) *
            ((i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity T.gasRate i) := by
            ring
        _ = _ := by rw [e]
    have hcount : ∀ u : TorusSite n, ∑ θ ∈ supportsAtBlock R.params.side (clusterRange R.coupling) u,
        clusterWeight R.params.side T.gasRate R.coupling (clusterRange R.coupling) θ *
          ((supportCore R.params.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
          Real.exp (2 * R.params.rt *
            (siteDiameter (supportCore R.params.side (clusterRange R.coupling) θ) : ℝ)) ≤ ee := by
      intro u
      have h1 : ∀ q : TorusLumps.StepParameters, q = T.stepParameters y →
          ∑ θ ∈ supportsAtBlock q.side (clusterRange R.coupling) u,
          clusterWeight q.side T.gasRate R.coupling (clusterRange R.coupling) θ *
            ((supportCore q.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
            Real.exp (2 * T.rt * (siteDiameter (supportCore q.side (clusterRange R.coupling) θ) : ℝ)) ≤ ee := by
        rintro _ rfl
        exact H₅ y hy5 R.coupling hyx n u
      rw [hRrt]
      exact h1 R.params hR
    have hsum := sum_nearSpins_le G
      (f := fun i => (i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity T.gasRate i)
      (fun i => mul_nonneg (by positivity) (Real.exp_pos _).le)
      (sum_core_weighted_le G (by rw [hκ]; nlinarith) hκ0 hcount) hee0 (Yb g') m
    calc _ ≤ ∑ i ∈ M g', Real.exp (-(κ * ((D : ℝ) - 2 * (m : ℝ)))) *
          ((i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity T.gasRate i) :=
          Finset.sum_le_sum hf
      _ = Real.exp (-(κ * ((D : ℝ) - 2 * (m : ℝ)))) * ∑ i ∈ M g',
          ((i.1.core.card : ℝ) * Real.exp (κ * (siteDiameter i.1.core : ℝ)) * G.spinActivity T.gasRate i) := by
          rw [Finset.mul_sum]
      _ ≤ δ := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
  have hpm : ∀ g, Measurable (pc g) := fun g =>
    H₂ y hy2 R A hAK hAt n G hGr (Q g) fun Yt bad b => (hQ g).measurable Yt bad b
  have hsz : ∀ g σ, G.pairConstraint.IsAdmissible σ → |pc g σ| ≤ K * (1 + 0) ^ 0 := fun g σ hσ => by
    simp only [hpc', if_pos hσ]
    simpa using abs_configMean_le hK0 (hQ g) G σ
  have hmove : ∀ g σ, G.pairConstraint.IsAdmissible σ →
      |pc g σ - pc g (vacateOutside G.pairConstraint (M g) σ)| ≤ ε * (K * (1 + 0) ^ 0) := by
    intro g σ hσ
    have hσ' := isAdmissible_vacateOutside G.pairConstraint (M g) hσ
    have hs : (configSetting G σ).IsAdmissible := H₄ y hy4 R hRT hxx n G hGr σ hσ
    have hs' : (configSetting G (vacateOutside G.pairConstraint (M g) σ)).IsAdmissible :=
      H₄ y hy4 R hRT hxx n G hGr _ hσ'
    simp only [hpc', if_pos hσ, if_pos hσ']
    have hag := hsa R n G σ (vacateOutside G.pairConstraint (M g) σ) (Yb g) m hodd hkn fun i hi => by
      have him : i ∈ M g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      simp [vacateOutside, him]
    have hpr : ∀ (W W' : TorusField (n * R.params.side)) (A₁ A₂ : Finset (TorusSite (n * R.params.side)))
        (ω : A₁ → R.labels.Ω) (ω' : A₂ → R.labels.Ω) (k : ℕ),
        IsLiveState R.params R.coupling R.labelWeight W A₁ ω →
        IsLiveState R.params R.coupling R.labelWeight W' A₂ ω' →
        (ra : ℝ) + (clusterRange R.coupling : ℝ) / 64 ≤ k → k ≤ R.params.side * m - R.params.side →
        StatesAgreeNear R.params W W' A₁ A₂ ω ω' (z g) (z g) k →
        |Q g W A₁ ω (G.badBondsOf σ) (configSetting G σ).bases -
            Q g W' A₂ ω' (G.badBondsOf (vacateOutside G.pairConstraint (M g) σ))
              (configSetting G (vacateOutside G.pairConstraint (M g) σ)).bases| ≤
          K * Real.exp (-R.params.decayRate * ((k : ℝ) - ra)) := by
      intro W W' A₁ A₂ ω ω' k hl hl' hk1 hk2 hst
      refine (hQ g).abs_sub_le_of_statesAgree hl hl' hk1 hst (fun c hc => ?_) (fun c hc => ?_)
      · obtain ⟨e, he, ex⟩ := exists_offsetInBox_of_supDist_le (k := k) (Finset.mem_filter.mp hc).2
        obtain ⟨o, ho, hzo⟩ := exists_fineSite_of_parentBlock hodd (Yb g) (z g) rfl
        have he' : OffsetInBox (R.params.side * m - R.params.side) e := fun l =>
          (he l).trans (by exact_mod_cast hk2)
        obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hm1 ho he'
        have hblock : parentBlock R.params.side c.1 = Yb g + siteOfInt kk := by
          rw [ex, hzo, hx n (Yb g)]
          exact parentBlock_fineSite hodd (Yb g) kk o' ho'
        refine mem_badBondsOf_iff G fun θ hθ => ?_
        rw [hblock] at hθ
        exact familyOf_eq_vacateOutside G rfl (fun l => by
          have := hkk l
          omega) hθ
      · have hbm : (supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (Yb g) : ℝ) ≤ m :=
          hc.trans hram
        obtain ⟨e, he, ex⟩ := exists_offsetInBox_of_supDist_le hbm
        show (G.settingOf (G.familyOf σ)).bases c = (G.settingOf (G.familyOf _)).bases c
        have hb := baseAt_eq_of_core (γ := G.familyOf σ)
          (γ' := G.familyOf (vacateOutside G.pairConstraint (M g) σ))
          (y := toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) fun θ hθ => by
            rw [ex] at hθ
            exact familyOf_eq_vacateOutside G rfl he hθ
        show (match (G.familyOf σ).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
          | Sum.inr o => frameBlockSite R.params.side n
              (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
          | Sum.inl _ => G.groundBases c) =
          (match (G.familyOf _).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
          | Sum.inr o => frameBlockSite R.params.side n
              (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
          | Sum.inl _ => G.groundBases c)
        rw [hb]
    have h1 := H₁ y hy1 R A hAK hAt n
      (fun W A₁ ω => Q g W A₁ ω (G.badBondsOf σ) (configSetting G σ).bases)
      (fun W A₁ ω => Q g W A₁ ω (G.badBondsOf (vacateOutside G.pairConstraint (M g) σ))
        (configSetting G (vacateOutside G.pairConstraint (M g) σ)).bases) (z g) K ra hn₀ hra0
      ((hQ g).toStateFunction _ _) ((hQ g).toStateFunction _ _) _ _ m hs hs' hm4 hag hpr
    refine h1.trans (le_of_eq ?_)
    simp only [hε]
    ring
  have hmom : ∫⁻ σ, ENNReal.ofReal (Real.exp ((fun _ => (0 : ℝ)) σ))
      ∂G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight ≤ 2 := by
    simp
  have hε0 : 0 ≤ ε := by positivity
  have hδ0 : 0 ≤ δ := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hmain := hfs G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff off) G.weight
    (G.spinActivity T.gasRate) h (G.influenceMatrix T.gasRate) p
    (fun _ => 0) M w pc (fun _ => K) (fun _ => 0) ε δ t hcols hw1 hδle hpm measurable_const (fun _ => le_rfl)
    (fun _ => hK0) hε0 hδ0 ht0 (fun _ _ => le_rfl) hsz hmove hmom
  have e1 : G.expectation ∅ (fun σ => ∏ i, FreeEnergies.settingMean (configSetting G σ) (G.badBondsOf σ) (Q i)) =
      ∫ σ, ∏ g, pc g σ ∂G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with σ hσ
    refine Finset.prod_congr rfl fun g _ => ?_
    simp only [hpc', if_pos hσ]
    rfl
  have e2 : ∀ g, G.expectation ∅ (fun σ => FreeEnergies.settingMean (configSetting G σ) (G.badBondsOf σ) (Q g)) =
      ∫ σ, pc g σ ∂G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight := by
    intro g
    refine integral_congr_ae ?_
    filter_upwards [hae] with σ hσ
    simp only [hpc', if_pos hσ]
    rfl
  rw [e1, Finset.prod_congr rfl fun g _ => e2 g]
  refine hmain.trans ?_
  have hs0 : (∑ g : Fin p, (fun _ : Fin p => (0 : ℕ)) g) = 0 := by simp
  have hprod : ∏ g : Fin p, (fun _ : Fin p => K) g = K ^ p := by simp
  rw [hs0, hprod]
  have hnum := far_tail_le hrtR hee0 hee1 D
  have hSp := decouplingConstant_le hp16
  have hKp : 0 ≤ K ^ p := by positivity
  have hS0 : 0 ≤ ε + Real.exp (-(t / 2)) + (1 + t) ^ 0 * δ := by positivity
  rw [hCfd, ← hRrt]
  calc _ ≤ decouplingBound * K ^ p * (ε + Real.exp (-(t / 2)) + (1 + t) ^ 0 * δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSp hKp) hS0
    _ ≤ decouplingBound * K ^ p * ((4 * Real.exp (R.params.rt / 2 ^ 4) + 1 +
          24 / (R.params.rt / 2 ^ 8) ^ 4 * Real.exp (R.params.rt / 2 ^ 8)) *
          Real.exp (-(R.params.rt * D / 2 ^ 7))) :=
        mul_le_mul_of_nonneg_left hnum (mul_nonneg decouplingBound_nonneg hKp)
    _ = _ := by ring
end Main
end CaseSplit
theorem nearCaseFunctionsSplit (hB : nearFunctionsTwoSettingsStatement)
    (hfs : LocalFunctionsDecoupleStatement)
    (hsa : LocalSettingsAgree)
    (hbor : FreeEnergies.settingMeanMeasurableStatement) (hcol : ClusterExpansionOfAStep.GasColumnsSmall)
    (hset : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hcnt : ClusterBounds.ClusterSumBound) :
    nearCaseFunctionsSplitStatement :=
  CaseSplit.split_main hB hfs hsa hbor hcol hset hcnt
end MomentLaw
end YangMills.Construction
end
