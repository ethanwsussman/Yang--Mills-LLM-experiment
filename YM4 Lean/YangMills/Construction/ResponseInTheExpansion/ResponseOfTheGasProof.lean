import YangMills.Construction.ResponseInTheExpansion.GasResponseReadsItsSiteProof
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeightProof
import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.MeansOverTheGasAreBorel
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheGasAreColdMeansProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ResponseReadsItsSite
import YangMills.Construction.ResponseInTheExpansion.SettingsOfASharedConfiguration
import YangMills.Construction.ResponseInTheExpansion.WeightAtASiteExtends
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps CoreColumns WeightedResponses
  BlockAverages BlockOffsets SettingShifts ClusterExpansionOfAStep
namespace GasResponse
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem familyOf_allVacant (G : GasGround R n) : G.familyOf G.allVacant = GasFamily.empty := by apply _root_.YangMills.SharedProofs.p24466 <;> assumption
theorem configSetting_allVacant (G : GasGround R n) : configSetting G G.allVacant = G.groundSetting := by apply _root_.YangMills.DeltaSharedProofs.p176 <;> assumption
theorem isGasFamily_familyOf (G : GasGround R n) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) :
    G.IsGasFamily (G.familyOf σ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.isGasFamily_familyOf <;> assumption
theorem isAdmissible_update_vacant (G : GasGround R n) {σ : G.Config} (i : G.GasSpin)
    (hσ : G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasActivity.isAdmissible_update_vacant <;> assumption
theorem core_nonempty (G : GasGround R n) (i : G.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem mem_core_of_meets (G : GasGround R n) (i : G.GasSpin) {Y : TorusSite n} (h : i.1.Meets Y) :
    Y ∈ i.1.core := by apply _root_.YangMills.Construction.GasComparison.mem_core_of_meets <;> assumption
theorem exists_supDist_eq_setGap (Y : TorusSite n) {X : Finset (TorusSite n)} (h : X.Nonempty) :
    ∃ y ∈ X, supDist Y y = setGap {Y} X := by apply _root_.YangMills.Construction.StepGas.exists_mem_supDist_eq_setGap <;> assumption
theorem setGap_le_supDist (Y : TorusSite n) {X : Finset (TorusSite n)} {y : TorusSite n} (h : y ∈ X) :
    setGap {Y} X ≤ supDist y Y := by
  unfold setGap
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  exact Nat.sInf_le ⟨Y, by simp, y, h, rfl⟩
theorem supDist_le_half (x y : TorusSite n) : supDist x y ≤ n / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
theorem settingsAgreeNear_update_vacant (hcl : ComponentBesideFamily) {G : GasGround R n}
    (hG : G.IsAdmissibleGround) (hr : 2 ^ 8 * R.params.side ≤ R.range) (hρ : 0 < R.ballRadius)
    (hodd : Odd R.params.side) (hL : 2 ≤ R.params.side)
    (hconf : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible)
    (Y : TorusSite n) (i : G.GasSpin) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) {m : ℕ}
    (hm : ∀ y ∈ i.1.core, m + 2 ≤ supDist y Y) (hn : 2 * m + 2 < n) :
    SettingsAgreeNear (configSetting G σ)
      (configSetting G (Function.update σ i (G.pairConstraint.vacant i))) Y Y m := by
  classical
  set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
  have adm₀ : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant G i hσ
  rcases hv : σ i with u | v
  · have e : σ₀ = σ := by
      rw [hσ₀]
      have : G.pairConstraint.vacant i = σ i := by rw [hv]; rfl
      rw [this, Function.update_eq_self]
    rw [e]
    exact settingsAgreeNear_refl _ (hconf σ hσ) Y m hn
  · have e : σ = Function.update σ₀ i (Sum.inr v) := by
      rw [hσ₀, Function.update_idem, ← hv, Function.update_eq_self]
    have hg : G.familyOf σ = (G.familyOf σ₀).insertClass i.1 v.1 := by
      rw [e]
      exact G.familyOf_update σ₀ i v
    have hap : ∀ θ', (G.familyOf σ₀).Occupies θ' → i.1.FarApart θ' := by
      intro θ' h
      obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
      have hji : j ≠ i := by
        intro c
        apply hj
        rw [c, hσ₀, Function.update_self]
        rfl
      have hj' : σ j = σ₀ j := by rw [hσ₀, Function.update_of_ne hji]
      rcases hσ i j hji.symm with a | a | a
      · rw [hv] at a
        cases a
      · rw [hj'] at a
        exact absurd a hj
      · exact a
    have key := (hcl R n G (G.familyOf σ₀) hr hρ hodd hL hG (isGasFamily_familyOf G adm₀)).2.2.2 i.1 v.1 i.2
      hap (hconf σ₀ adm₀)
    have h3 := key.2.2.1 Y m hm hn
    unfold configSetting
    rw [hg]
    exact h3
theorem forgets_spin_of_agree (hcl : ComponentBesideFamily) {G : GasGround R n} (hG : G.IsAdmissibleGround)
    (hr : 2 ^ 8 * R.params.side ≤ R.range) (hρ : 0 < R.ballRadius) (hodd : Odd R.params.side)
    (hL : 2 ≤ R.params.side) (hrt : 0 < R.params.rt)
    (hconf : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible)
    (Y : TorusSite n) {q : ℕ}
    {p s : G.Config → ℝ} {u : ℝ} (hu : 0 ≤ u) (hs0 : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 ≤ s σ)
    (hag : ∀ (σ σ₀ : G.Config) (m : ℕ), G.pairConstraint.IsAdmissible σ → G.pairConstraint.IsAdmissible σ₀ →
      q ≤ m → SettingsAgreeNear (configSetting G σ) (configSetting G σ₀) Y Y m →
      s σ = s σ₀ ∧ |p σ - p σ₀| ≤ (1 + s σ) * Real.exp (-(R.params.rt * m / 2 ^ 5)) * u)
    (i : G.GasSpin) (σ σ' : G.Config) (hσ : G.pairConstraint.IsAdmissible σ)
    (hσ' : G.pairConstraint.IsAdmissible σ')
    (hd : ∀ j, j ≠ i → σ j = σ' j) (hgap : q + 4 ≤ setGap {Y} i.1.core) :
    s σ = s σ' ∧ |p σ - p σ'| ≤ 2 * (1 + s σ) * G.coreWeightFrom Y i * u := by
  classical
  set m := setGap {Y} i.1.core - 2 with hmdef
  have hm : ∀ y ∈ i.1.core, m + 2 ≤ supDist y Y := fun y hy => by
    have := setGap_le_supDist Y hy
    omega
  obtain ⟨y₀, hy₀, e₀⟩ := exists_supDist_eq_setGap Y (core_nonempty G i)
  have hhalf := supDist_le_half Y y₀
  have hnpos : setGap {Y} i.1.core ≤ n / 2 := by omega
  have hn : 2 * m + 2 < n := by
    have h1 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    omega
  set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
  have e₀' : Function.update σ' i (G.pairConstraint.vacant i) = σ₀ := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [hσ₀, Function.update_self, Function.update_self]
    · rw [hσ₀, Function.update_of_ne hj, Function.update_of_ne hj, hd j hj]
  have adm₀ : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant G i hσ
  have a₁ := settingsAgreeNear_update_vacant hcl hG hr hρ hodd hL hconf Y i hσ hm hn
  have a₂ := settingsAgreeNear_update_vacant hcl hG hr hρ hodd hL hconf Y i hσ' hm hn
  rw [e₀'] at a₂
  have hqm : q ≤ m := by omega
  obtain ⟨e1, b1⟩ := hag σ σ₀ m hσ adm₀ hqm a₁
  obtain ⟨e2, b2⟩ := hag σ' σ₀ m hσ' adm₀ hqm a₂
  have hss : s σ = s σ' := e1.trans e2.symm
  refine ⟨hss, ?_⟩
  have hcard : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
  have hexp : Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤ G.coreWeightFrom Y i := by
    unfold GasGround.coreWeightFrom coreWeight
    have h1 : Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤
        Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      have h2 : (setGap {Y} i.1.core : ℝ) ≤ 2 * m := by
        have : setGap {Y} i.1.core ≤ 2 * m := by omega
        exact_mod_cast this
      have h3 : R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ) ≤ R.params.rt / 2 ^ 6 * (2 * m) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : R.params.rt / 2 ^ 6 * (2 * (m : ℝ)) = R.params.rt * m / 2 ^ 5 := by ring
      linarith
    exact h1.trans (le_mul_of_one_le_left (Real.exp_pos _).le hcard)
  have h0 := hs0 σ hσ
  have hb : ∀ {a : ℝ}, a ≤ (1 + s σ) * Real.exp (-(R.params.rt * m / 2 ^ 5)) * u →
      a ≤ (1 + s σ) * G.coreWeightFrom Y i * u := by
    intro a ha
    refine ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by linarith)) hu)
  have c1 := hb b1
  have c2 := hb (by rw [hss]; exact b2 : |p σ' - p σ₀| ≤ _)
  have tri : |p σ - p σ'| ≤ |p σ - p σ₀| + |p σ' - p σ₀| := by
    have h1 := abs_sub_le (p σ) (p σ₀) (p σ')
    rw [abs_sub_comm (p σ₀) (p σ')] at h1
    exact h1
  calc _ ≤ _ := tri
    _ ≤ _ := add_le_add c1 c2
    _ = _ := by ring
section Scores
variable (A : ResponseSetup R)
  (hpr : PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity A.score)
include hpr in
theorem siteScore_nonneg {m : ℕ} (Y : Finset (TorusSite m)) (ω : Y → R.labels.Ω) (y : TorusSite m) :
    0 ≤ siteScore A.score Y ω y := by
  classical
  unfold siteScore
  split_ifs
  · exact hpr.nonneg _
  · exact le_rfl
theorem chartSiteScore_of_not_mem_sites (G : GasGround R n) (σ : G.Config) (y : TorusSite (n * R.params.side))
    (hy : y ∉ (G.familyOf σ).sites) :
    chartSiteScore A (configSetting G σ) y = recordedSiteScore A G y := by
  classical
  unfold chartSiteScore recordedSiteScore siteScore
  by_cases h : y ∈ G.recordedSites
  · have h' : y ∈ (configSetting G σ).support := Finset.mem_union_left _ h
    rw [dif_pos h', dif_pos h]
    congr 1
    change (if hh : y ∈ (G.familyOf σ).sites then _ else _) = _
    rw [dif_neg hy]
  · have h' : y ∉ (configSetting G σ).support := by
      intro c
      rcases Finset.mem_union.mp c with c | c
      · exact h c
      · exact hy c
    rw [dif_neg h', dif_neg h]
theorem not_mem_sites_allVacant (G : GasGround R n) (y : TorusSite (n * R.params.side)) :
    y ∉ (G.familyOf G.allVacant).sites := by
  intro h
  obtain ⟨θ, hθ, -⟩ := GasFamily.exists_of_mem_sites h
  obtain ⟨j, -, hj⟩ := G.exists_spin_of_occupies hθ
  exact hj rfl
theorem getRight_eq_of_eq_inr {α β : Type} {x : α ⊕ β} {a : β} (e : x = Sum.inr a) (h : x.isRight = true) :
    x.getRight h = a := by
  subst e
  rfl
include hpr in
theorem label_score_le_spinScore (G : GasGround R n) (σ : G.Config) (y : TorusSite (n * R.params.side))
    (j : G.GasSpin) (h1 : (G.familyOf σ).Occupies j.1) (h2 : y ∈ j.1.2) :
    A.score (((G.familyOf σ).state h1).2.1 ⟨y, h2⟩) ≤ _root_.YangMills.Construction.WeightedResponses.spinScore A j (σ j) := by
  classical
  rcases hv : σ j with u | v
  · exfalso
    unfold GasFamily.Occupies GasGround.familyOf at h1
    rw [dif_pos j.2] at h1
    have : σ ⟨j.1, j.2⟩ = Sum.inl u := hv
    rw [this] at h1
    simp at h1
  · have e : G.familyOf σ j.1 = Sum.inr v.1 := by
      unfold GasGround.familyOf
      rw [dif_pos j.2]
      have : σ ⟨j.1, j.2⟩ = Sum.inr v := hv
      rw [this]
    have e2 : (G.familyOf σ).state h1 = v.1 := getRight_eq_of_eq_inr e h1
    rw [e2]
    change _ ≤ ∑ z : j.1.2, A.score (v.1.2.1 z)
    exact Finset.single_le_sum (f := fun z : j.1.2 => A.score (v.1.2.1 z)) (fun z _ => hpr.nonneg _)
      (Finset.mem_univ _)
include hpr in
theorem exists_classesControlScore (hodd : Odd R.params.side) {ch : ℝ} (G : GasGround R n) (Y : TorusSite n)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube R.params.side)
    (hpaid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (_root_.YangMills.Construction.WeightedResponses.spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
        ENNReal.ofReal (G.spinActivity ch i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) :
    ∃ H e, ClassesControlScore G Y ch (recordedSiteScore A G (fineSite R.params.side Y 0 o))
      (fun σ => chartSiteScore A (configSetting G σ) (fineSite R.params.side Y 0 o)) H e := by
  classical
  set y := fineSite R.params.side Y 0 o with hy
  have hblock : parentBlock R.params.side y = Y := by
    rw [hy, parentBlock_fineSite hodd Y 0 o ho, siteOfInt_zero_offset, add_zero]
  refine ⟨Finset.univ.filter fun i : G.GasSpin => y ∈ i.1.2, fun i => _root_.YangMills.Construction.WeightedResponses.spinScore A i, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    exact mem_core_of_meets G i (Or.inr ⟨y, (Finset.mem_filter.mp hi).2, hblock⟩)
  · intro i
    have : _root_.YangMills.Construction.WeightedResponses.spinScore A i = Sum.elim (fun _ => 0) (fun v : G.SpinState i => ∑ z : i.1.2, A.score (v.1.2.1 z)) := by
      funext v
      cases v <;> rfl
    rw [this]
    refine Measurable.sumElim measurable_const (Finset.measurable_sum _ fun z _ => ?_)
    exact hpr.borel.comp ((measurable_pi_apply z).comp (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)))
  · intro i v
    rcases v with u | v
    · exact le_rfl
    · exact Finset.sum_nonneg fun z _ => hpr.nonneg _
  · intro i
    rfl
  · intro σ hσ
    by_cases hys : y ∈ (G.familyOf σ).sites
    · right
      obtain ⟨h1, h2⟩ := (GasFamily.exists_of_mem_sites hys).choose_spec
      set θ := (GasFamily.exists_of_mem_sites hys).choose with hθ
      obtain ⟨j, hj, hne⟩ := G.exists_spin_of_occupies h1
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ h2⟩, hne, ?_⟩
      have hYt : y ∈ (configSetting G σ).support := Finset.mem_union_right _ hys
      have e1 : chartSiteScore A (configSetting G σ) y = A.score ((G.familyOf σ).labelAt hys) := by
        unfold chartSiteScore siteScore
        rw [dif_pos hYt]
        congr 1
        change (if hh : y ∈ (G.familyOf σ).sites then _ else _) = _
        rw [dif_pos hys]
      rw [e1]
      have key : ∀ (θ' : GasSupport R n) (h1' : (G.familyOf σ).Occupies θ') (h2' : y ∈ θ'.2), j.1 = θ' →
          A.score (((G.familyOf σ).state h1').2.1 ⟨y, h2'⟩) ≤ _root_.YangMills.Construction.WeightedResponses.spinScore A j (σ j) := by
        intro θ' h1' h2' e
        subst e
        exact label_score_le_spinScore A hpr G σ y j h1' h2'
      exact key _ _ _ hj
    · left
      exact le_of_eq (chartSiteScore_of_not_mem_sites A G σ y hys)
  · intro i _ σ hσ
    exact hpaid i σ hσ
end Scores
theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
section Shared
variable {n' : ℕ} [NeZero n'] {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'}
  {N m : ℕ} {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
theorem extendFirst_vacant (g : SharedInnerGas G G' Y Y' N m A A') :
    g.extendFirst (fun _ => Sum.inl ()) = G.allVacant := by
  funext i
  unfold SharedInnerGas.extendFirst PairConstraint.embedConfig
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : ∀ (j' : G.InnerSpin Y m A) (e : j'.1 = j.1), (e ▸ (Sum.inl () : G.SpinValue j'.1)) =
        (Sum.inl () : G.SpinValue j.1) := by
      intro j' e
      obtain rfl := Subtype.ext e
      rfl
    exact this _ _
  · rfl
theorem extendSecond_vacant (g : SharedInnerGas G G' Y Y' N m A A') :
    g.extendSecond (fun _ => Sum.inl ()) = G'.allVacant := by
  funext i
  unfold SharedInnerGas.extendSecond PairConstraint.embedConfig
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : ∀ (j' : G.InnerSpin Y m A) (e : (g.spinEquiv j').1 = (g.spinEquiv j).1),
        (e ▸ g.valueEquiv j' (Sum.inl ()) : G'.SpinValue (g.spinEquiv j).1) =
          (Sum.inl () : G'.SpinValue (g.spinEquiv j).1) := by
      intro j' e
      obtain rfl := g.spinEquiv.injective (Subtype.ext e)
      exact g.map_vacant j'
    exact this _ _
  · rfl
end Shared
theorem abs_weightedMean_le_two {m : ℕ} {free : Finset (TorusBond m)} (d F : FreeCoords free → ℝ)
    (hd : ∀ η, 0 ≤ d η) (hF : ∀ η, |F η| ≤ 2) : |weightedMean d F| ≤ 2 := by
  unfold weightedMean
  by_cases hi : Integrable d
  · have h1 : |∫ η, F η * d η| ≤ 2 * ∫ η, d η := by
      have h2 : ∀ η, ‖F η * d η‖ ≤ 2 * d η := fun η => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd η)]
        exact mul_le_mul_of_nonneg_right (hF η) (hd η)
      have h3 := norm_integral_le_of_norm_le (hi.const_mul 2) (ae_of_all _ h2)
      rw [integral_const_mul] at h3
      exact h3
    have h0 : 0 ≤ ∫ η, d η := integral_nonneg hd
    rw [abs_div, abs_of_nonneg h0]
    by_cases hz : (∫ η, d η) = 0
    · rw [hz, div_zero]
      norm_num
    · exact (div_le_iff₀ (lt_of_le_of_ne h0 (Ne.symm hz))).mpr h1
  · rw [integral_undef hi, div_zero, abs_zero]
    norm_num
end GasResponse
set_option maxHeartbeats 4000000 in
open GasResponse in
theorem gasResponseBounds_of_components (hObs : gasObservableBoundsStatement)
    (hAB : ChartResponseComparison) (hPaid : clusterScoreIntegralBound) (hBor : GasMeansMeasurable)
    (hShare : SharedConfigurationSettingsAgree) (hRead : chartResponseDependsOnlyOnSite)
    (hExt : agreeingWeightExtensionStatement) (hConf : GasConfigIsAdmissibleSetting)
    (hCl : ComponentBesideFamily) (hScore : BondScoreProperties) (hCF : CouplingFloorExists) :
    GasResponseBounds := by
  classical
  obtain ⟨r₁, p₁, h₁⟩ := hObs
  obtain ⟨r₂, p₂, h₂⟩ := hAB
  obtain ⟨r₃, p₃, h₃⟩ := hPaid
  obtain ⟨r₄, p₄, h₄⟩ := hBor
  obtain ⟨r₅, p₅, h₅⟩ := hRead
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c)))),
    fun T hT hle K => ?_⟩
  have c₁ := hle.trans (min_le_left _ _)
  have hle₂ := hle.trans (min_le_right _ _)
  have c₂ := hle₂.trans (min_le_left _ _)
  have hle₃ := hle₂.trans (min_le_right _ _)
  have c₃ := hle₃.trans (min_le_left _ _)
  have hle₄ := hle₃.trans (min_le_right _ _)
  have c₄ := hle₄.trans (min_le_left _ _)
  have c₅ := hle₄.trans (min_le_right _ _)
  obtain ⟨y₁, hy₁⟩ := h₁ T hT c₁ K.C₀
  obtain ⟨y₁', hy₁'⟩ := h₁ T hT c₁ 2
  obtain ⟨y₂, hy₂⟩ := h₂ T hT c₂ K
  obtain ⟨y₃, hy₃⟩ := h₃ T hT c₃ K
  obtain ⟨y₄, hy₄⟩ := h₄ T hT c₄ K
  obtain ⟨y₅, hy₅⟩ := h₅ T hT c₅ K
  obtain ⟨y₆, hy₆⟩ := hConf T hT
  obtain ⟨y₇, hy₇⟩ := hShare T hT
  have hrt := hT.rt_pos
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  obtain ⟨y₈, hy₈⟩ := hCF T.gasRate (2 ^ 8 * T.side) T.rt hch
  refine ⟨max y₁ (max y₁' (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈
    (max T.floorMin (max 1 (200 * T.B))))))))))),
    fun y hy R A hK hAt => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₁', hy⟩ := max_le_iff.mp hy
  obtain ⟨a₂, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₃, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₄, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₅, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₆, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₇, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₈, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₉, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₁₀, a₁₁⟩ := max_le_iff.mp hy
  have hR := hAt.onFamily
  have hx : y ≤ R.coupling := hR.le_coupling
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 : 200 * T.B ≤ R.coupling := a₁₁.trans hx
    have h3 : 0 < R.coupling := by linarith
    linarith
  have hLL : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hrtR : R.params.rt = T.rt := by
    rw [hR.params_eq]
    rfl
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₉
  have hodd : Odd R.params.side := hfit.L_odd
  have hL16 : 2 ^ 16 ≤ R.params.side := hfit.L_ge
  have hL2 : 2 ≤ R.params.side := by omega
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    have := hfit.σ_pos
    positivity
  have hrtR0 : 0 < R.params.rt := hrtR ▸ hrt
  obtain ⟨hr8, hfl⟩ := hy₈ R.coupling (a₈.trans hx)
  have hr : 2 ^ 8 * R.params.side ≤ R.range := by
    rw [hLL]
    exact hr8
  have hresp := hAt.admissible
  have hpr := hresp.price
  have hlet := hresp.params_admissible
  have hC₀ : 1 ≤ K.C₀ := by
    rw [← hK] at *
    rw [hlet.C₀_eq]
    have := hfit.a_ge
    have := hlet.N₀_nonneg
    have := hlet.Kc_ge
    linarith
  have hCK : A.responseParams.C₀ = K.C₀ := by rw [hK]
  have hab := hy₂ y a₂ R A hK hAt
  have hpaid := hy₃ y a₃ R A hK hAt
  have hbor := hy₄ y a₄ R A hK hAt
  have hrd := hy₅ y a₅ R A hK hAt
  have hside : ∀ (p : ℕ) [NeZero p] (H : GasGround R p), H.IsAdmissibleGround → R.params.n₀ ≤ p := by
    intro p _ H hH
    rcases hH with h | h
    · exact h.n₀_le
    · have h1 := h.isBlockSide.2
      have h2 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      exact (Nat.le_mul_of_pos_left _ h2).trans h1
  have hconf : ∀ (p : ℕ) [NeZero p] (H : GasGround R p), H.IsAdmissibleGround → ∀ σ : H.Config,
      H.pairConstraint.IsAdmissible σ → (configSetting H σ).IsAdmissible :=
    fun p _ H hH σ hσ => hy₆ y a₆ R hR hx' p H hH σ hσ
  set q : ℕ := ⌈(R.range : ℝ) / (4 * R.params.side)⌉₊ with hq
  have hq1 : (R.range : ℝ) / (4 * R.params.side) ≤ q := Nat.le_ceil _
  have hLpos : (0 : ℝ) < R.params.side := by
    have : 0 < R.params.side := by omega
    exact_mod_cast this
  have hr1 : 1 ≤ R.range := by omega
  have hqr : q ≤ R.range := by
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ R.params.side := by exact_mod_cast (by omega : 1 ≤ R.params.side)
    have h2 : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
    nlinarith
  have hD : T.rt / 2 ^ 6 * ((q + 4 : ℕ) : ℝ) ≤ T.gasRate * R.coupling := by
    have h1 : ((q + 4 : ℕ) : ℝ) ≤ 5 * (R.range : ℝ) ^ 4 := by
      have h2 : ((q + 4 : ℕ) : ℝ) ≤ (R.range : ℝ) + 4 := by
        push_cast
        have : (q : ℝ) ≤ R.range := by exact_mod_cast hqr
        linarith
      have h3 : (1 : ℝ) ≤ R.range := by exact_mod_cast hr1
      have h4 : (R.range : ℝ) ≤ (R.range : ℝ) ^ 4 := le_self_pow₀ h3 (by norm_num)
      have h5 : (1 : ℝ) ≤ (R.range : ℝ) ^ 4 := one_le_pow₀ h3
      linarith
    have h2 : T.rt / 2 ^ 6 * ((q + 4 : ℕ) : ℝ) ≤ T.rt / 2 ^ 6 * (5 * (R.range : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 0 ≤ T.rt * (R.range : ℝ) ^ 4 := by positivity
    have h4 : 0 ≤ (R.range : ℝ) ^ 4 := by positivity
    have h5 : (2 ^ 16 + 2 ^ 7 * T.rt) * (R.range : ℝ) ^ 4 ≤ T.gasRate * R.coupling := hfl
    have e1 : (2 ^ 16 + 2 ^ 7 * T.rt) * (R.range : ℝ) ^ 4 =
        2 ^ 16 * (R.range : ℝ) ^ 4 + 2 ^ 7 * (T.rt * (R.range : ℝ) ^ 4) := by ring
    have e2 : T.rt / 2 ^ 6 * (5 * (R.range : ℝ) ^ 4) = 5 / 64 * (T.rt * (R.range : ℝ) ^ 4) := by ring
    linarith
  have respObs : ∀ (p : ℕ) [NeZero p] (H : GasGround R p) (Z : TorusSite p) (o : Fin 4 → ℤ)
      (h h₀ : PlaquetteWeight (fineSide R.params.side R.depth (p * R.params.side))) (u : ℝ),
      H.IsAdmissibleGround → o ∈ centredCube R.params.side →
      (∀ s : ChartSetting R p, s.IsAdmissible → chartResponse A s (fineSite R.params.side Z 0 o) h =
        chartResponse A s (fineSite R.params.side Z 0 o) h₀) →
      weightNorm R.params.side R.depth h₀ ≤ u → 0 ≤ u →
      IsGasObservable H Z T.gasRate K.C₀ u (recordedSiteScore A H (fineSite R.params.side Z 0 o)) (q + 4)
        (fun σ => chartResponse A (configSetting H σ) (fineSite R.params.side Z 0 o) h)
        (fun σ => chartSiteScore A (configSetting H σ) (fineSite R.params.side Z 0 o)) := by
    intro p _ H Z o h h₀ u hH ho hread hu hu0
    have hs0 : ∀ σ : H.Config, H.pairConstraint.IsAdmissible σ →
        0 ≤ chartSiteScore A (configSetting H σ) (fineSite R.params.side Z 0 o) :=
      fun σ _ => siteScore_nonneg A hpr _ _ _
    have hn₀ := hside p H hH
    have hsz0 : 0 ≤ weightNorm R.params.side R.depth h₀ ∨ True := Or.inr trivial
    refine ⟨hC₀, hu0, siteScore_nonneg A hpr _ _ _, (hbor p H hH).1 _ _, (hbor p H hH).2.2 _, hs0, ?_, ?_, ?_⟩
    · intro σ hσ
      have hs := hconf p H hH σ hσ
      rw [hread _ hs]
      have h1 := hab.1 p (configSetting H σ) hn₀ hs (fineSite R.params.side Z 0 o) h₀
      rw [hCK] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left hu ?_)
      have := hs0 σ hσ
      linarith
    · exact exists_classesControlScore A hpr hodd H Z ho (hpaid p H hH)
    · intro i σ σ' hσ hσ' hd hgap
      refine forgets_spin_of_agree hCl hH hr hρ hodd hL2 hrtR0 (hconf p H hH) Z (q := q)
        (p := fun σ => chartResponse A (configSetting H σ) (fineSite R.params.side Z 0 o) h) hu0 hs0 ?_
        i σ σ' hσ hσ' hd hgap
      intro σ₁ σ₀ m h₁' h₀' hqm ag
      have hs₁ := hconf p H hH σ₁ h₁'
      have hs₀' := hconf p H hH σ₀ h₀'
      have hsc : chartSiteScore A (configSetting H σ₁) (fineSite R.params.side Z 0 o) =
          chartSiteScore A (configSetting H σ₀) (fineSite R.params.side Z 0 o) := by
        have hb0 : OffsetInBox m (0 : Fin 4 → ℤ) := fun i => by simp
        unfold chartSiteScore siteScore
        by_cases hz : fineSite R.params.side Z 0 o ∈ (configSetting H σ₁).support
        · have hz' := (ag.support_iff 0 o hb0 ho).mp hz
          rw [dif_pos hz, dif_pos hz', ag.labelling_eq 0 o hz hz' hb0 ho]
        · have hz' : fineSite R.params.side Z 0 o ∉ (configSetting H σ₀).support :=
            fun c => hz ((ag.support_iff 0 o hb0 ho).mpr c)
          rw [dif_neg hz, dif_neg hz']
      refine ⟨hsc, ?_⟩
      rw [hread _ hs₁, hread _ hs₀']
      have hqm' : (R.range : ℝ) / (4 * R.params.side) ≤ m := hq1.trans (by exact_mod_cast hqm)
      have key := (((hab.2 p p (configSetting H σ₁) (configSetting H σ₀) Z Z m hn₀ hn₀ hs₁ hs₀').1
        ag hqm').1 o ho h₀ h₀ (by unfold WeightsAgreeAt; intros; rfl))
      refine key.trans (mul_le_mul_of_nonneg_left hu ?_)
      have := hs0 σ₁ h₁'
      positivity
  have scoreObs : ∀ (p : ℕ) [NeZero p] (H : GasGround R p) (Z : TorusSite p) (c : (Fin 4 → ℤ) × Fin 4),
      H.IsAdmissibleGround → IsBondAtOrigin c → IsGasObservable H Z T.gasRate 2 1 0 (q + 4)
        (fun σ => chartBondScore (configSetting H σ) (bondFrom Z c)) (fun _ => 0) := by
    intro p _ H Z c hH hc
    have hn₀ := hside p H hH
    have hz : Measurable (restrictAdmissible H fun _ => (0 : ℝ)) := by
      have : restrictAdmissible H (fun _ => (0 : ℝ)) = fun _ => 0 := by
        funext σ
        unfold restrictAdmissible
        split_ifs <;> rfl
      rw [this]
      exact measurable_const
    refine ⟨by norm_num, zero_le_one, le_rfl, (hbor p H hH).2.1 _, hz, fun _ _ => le_rfl, ?_, ?_, ?_⟩
    · intro σ _
      have hsc := fun (W : TorusField (p * R.params.side)) (V : TorusField p) b =>
        (hScore R.params hfit R.coupling p b (bondFrom Z c)).2.2.1 W V
      simp only [add_zero, mul_one]
      exact abs_weightedMean_le_two _ _ (chartDensity_nonneg _) fun η => hsc _ _ _
    · refine ⟨∅, fun _ _ => 0, ⟨by simp, fun _ => measurable_const, fun _ _ => le_rfl, fun _ => rfl,
        fun _ _ => Or.inl le_rfl, by simp⟩⟩
    · intro i σ σ' hσ hσ' hd hgap
      refine forgets_spin_of_agree hCl hH hr hρ hodd hL2 hrtR0 (hconf p H hH) Z (q := q)
        (p := fun σ => chartBondScore (configSetting H σ) (bondFrom Z c)) (s := fun _ => 0) zero_le_one
        (fun _ _ => le_rfl) ?_ i σ σ' hσ hσ' hd hgap
      intro σ₁ σ₀ m h₁' h₀' hqm ag
      have hs₁ := hconf p H hH σ₁ h₁'
      have hs₀' := hconf p H hH σ₀ h₀'
      have hqm' : (R.range : ℝ) / (4 * R.params.side) ≤ m := hq1.trans (by exact_mod_cast hqm)
      have key := (((hab.2 p p (configSetting H σ₁) (configSetting H σ₀) Z Z m hn₀ hn₀ hs₁ hs₀').1
        ag hqm').2 c hc)
      refine ⟨rfl, ?_⟩
      simpa using key
  have hOb := hy₁ y a₁ R hR hx'
  have hOb₂ := hy₁' y a₁' R hR hx'
  have hDT : T.rt / 2 ^ 6 * ((q + 4 : ℕ) : ℝ) ≤ T.gasRate * R.coupling := hD
  refine ⟨?_, ?_⟩
  · intro n _ G hG
    refine ⟨fun y' h => ?_, fun c => ?_⟩
    · obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd (parentBlock R.params.side y') y' rfl
      have hsz : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg _ _ h
      have ob := respObs n G (parentBlock R.params.side y') o h h _ hG ho (fun _ _ => rfl) le_rfl hsz
      rw [← e] at ob
      have res := hOb.1 n G (parentBlock R.params.side y') _ _ _ _ _ hG ob hDT
      obtain ⟨b1, b2⟩ := res
      refine ⟨?_, by rw [hCK]; exact b2⟩
      unfold gasResponseShift
      rw [← configSetting_allVacant G]
      exact b1
    · have hc : bondFrom c.1 ((0 : Fin 4 → ℤ), c.2) = c := by
        unfold bondFrom
        simp [siteOfInt_zero_offset]
      have ob := scoreObs n G c.1 (0, c.2) hG (Or.inl rfl)
      rw [hc] at ob
      obtain ⟨b1, b2⟩ := hOb₂.1 n G c.1 _ _ _ _ _ hG ob hDT
      refine ⟨?_, ?_⟩
      · unfold gasBondScoreShift
        rw [← configSetting_allVacant G]
        simpa using b1
      · simpa using b2
  · intro n n' _ _ G G' Y Y' m hG hG' hAg hm
    have hn₀ := hside n G hG
    have hn₀' := hside n' G' hG'
    obtain ⟨g, hg⟩ := hOb.2 n n' G G' Y Y' m hG hG' hm hAg
    obtain ⟨g₂, hg₂⟩ := hOb₂.2 n n' G G' Y Y' m hG hG' hm hAg
    refine ⟨fun o ho h h' hW => ?_, fun c hc => ?_⟩
    · have hn8 : 8 ≤ n * R.params.side := by
        have : 4096 ≤ R.params.n₀ := hfit.n₀_ge
        have h2 : n ≤ n * R.params.side := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hn8' : 8 ≤ n' * R.params.side := by
        have : 4096 ≤ R.params.n₀ := hfit.n₀_ge
        have h2 : n' ≤ n' * R.params.side := Nat.le_mul_of_pos_right _ (by omega)
        omega
      obtain ⟨h'', e'', hle⟩ := hExt R.params.side R.depth (n * R.params.side) (n' * R.params.side) _ _ h h'
        hodd hn8 hn8' hW
      have hsz : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg _ _ h
      have ob := respObs n G Y o h h _ hG ho (fun _ _ => rfl) le_rfl hsz
      have ob' := respObs n' G' Y' o h' h'' (weightNorm R.params.side R.depth h) hG' ho
        (fun s hs => hrd n' s hn₀' hs _ h' h'' fun p hp => (e'' p hp).symm) hle hsz
      have hsame : ∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
          chartSiteScore A (configSetting G (g.extendFirst τ)) (fineSite R.params.side Y 0 o) =
            chartSiteScore A (configSetting G' (g.extendSecond τ)) (fineSite R.params.side Y' 0 o) := by
        intro τ hτ
        have ag := hy₇ y a₇ R hR hx' n n' G G' Y Y' m g τ hG hG' hm hAg hτ
        have hb0 : OffsetInBox m (0 : Fin 4 → ℤ) := fun i => by simp
        unfold chartSiteScore siteScore
        by_cases hz : fineSite R.params.side Y 0 o ∈ (configSetting G (g.extendFirst τ)).support
        · have hz' := (ag.support_iff 0 o hb0 ho).mp hz
          rw [dif_pos hz, dif_pos hz', ag.labelling_eq 0 o hz hz' hb0 ho]
        · have hz' : fineSite R.params.side Y' 0 o ∉ (configSetting G' (g.extendSecond τ)).support :=
            fun c => hz ((ag.support_iff 0 o hb0 ho).mpr c)
          rw [dif_neg hz, dif_neg hz']
      have hs₀ : recordedSiteScore A G' (fineSite R.params.side Y' 0 o) =
          recordedSiteScore A G (fineSite R.params.side Y 0 o) := by
        have hfa : G.pairConstraint.IsAdmissible (g.extendFirst fun _ => Sum.inl ()) := by
          rw [extendFirst_vacant g]
          exact fun i j _ => G.pairConstraint.vacant_compatible i j _
        have h1 := hsame (fun _ => Sum.inl ()) hfa
        rw [extendFirst_vacant, extendSecond_vacant g,
          chartSiteScore_of_not_mem_sites A G _ _ (not_mem_sites_allVacant G _),
          chartSiteScore_of_not_mem_sites A G' _ _ (not_mem_sites_allVacant G' _)] at h1
        exact h1.symm
      rw [hs₀] at ob'
      have res := hg _ _ _ _ _ _ _ ob ob' hDT (fun τ hτ hτ' => ?_)
      · unfold gasResponseShift
        rw [← configSetting_allVacant G, ← configSetting_allVacant G', hrtR]
        exact res
      · have ag := hy₇ y a₇ R hR hx' n n' G G' Y Y' m g τ hG hG' hm hAg hτ
        have hsτ := hconf n G hG _ hτ
        have hsτ' := hconf n' G' hG' _ hτ'
        have key := (((hab.2 n n' _ _ Y Y' m hn₀ hn₀' hsτ hsτ').2 ag hm).1 o ho h h' hW)
        refine ⟨hsame τ hτ, ?_⟩
        rw [← hrtR]
        exact key
    · have ob := scoreObs n G Y c hG hc
      have ob' := scoreObs n' G' Y' c hG' hc
      have res := hg₂ _ _ _ _ _ _ _ ob ob' hDT (fun τ hτ hτ' => ?_)
      · unfold gasBondScoreShift
        rw [← configSetting_allVacant G, ← configSetting_allVacant G', hrtR]
        simpa using res
      · have ag := hy₇ y a₇ R hR hx' n n' G G' Y Y' m g₂ τ hG hG' hm hAg hτ
        have hsτ := hconf n G hG _ hτ
        have hsτ' := hconf n' G' hG' _ hτ'
        have key := (((hab.2 n n' _ _ Y Y' m hn₀ hn₀' hsτ hsτ').2 ag hm).2 c hc)
        refine ⟨rfl, ?_⟩
        rw [← hrtR]
        simpa using key
end YangMills.Construction.ResponseInTheExpansion
end
