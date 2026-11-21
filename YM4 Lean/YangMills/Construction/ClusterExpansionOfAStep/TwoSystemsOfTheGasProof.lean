import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGases
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.MassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfASharedGasProof
import YangMills.Construction.ClusterExpansionOfAStep.TwoGroundsShareAGas
import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGas
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Dobrushin StepGas StepSettings RenormalizationStepParameters StepFloors TorusLumps TorusFields CoreColumns
namespace GasComparison
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
section Embedding
variable {I J : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {T : J → Type} (P : PairConstraint S) {e : J → I}
theorem embedConfig_apply_of_injective (v : ∀ j, T j → S (e j)) (he : Function.Injective e) (τ : ∀ j, T j)
    (j : J) : P.embedConfig e v τ (e j) = v j (τ j) := by
  have key : ∀ (j' : J) (hj : e j' = e j), (hj ▸ v j' (τ j') : S (e j)) = v j (τ j) := by
    intro j' hj
    obtain rfl := he hj
    rfl
  unfold PairConstraint.embedConfig
  rw [dif_pos ⟨j, rfl⟩]
  exact key _ _
theorem embedConfig_of_not_mem_range (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) {i : I} (h : ∀ j, e j ≠ i) :
    P.embedConfig e v τ i = P.vacant i := by
  unfold PairConstraint.embedConfig
  rw [dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj
end Embedding
abbrev InnerGasSpin (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) : Type :=
  {i : G.GasSpin // G.IsInnerSpin Y m A i}
instance instFintypeInnerGasSpin (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) :
    Fintype (InnerGasSpin G Y m A) :=
  Fintype.ofFinite _
theorem mem_core_of_meets (G : GasGround R n) (i : G.GasSpin) {Y : TorusSite n} (h : i.1.Meets Y) :
    Y ∈ i.1.core := by
  classical
  have hz : ∃ z ∈ i.1.sites, parentBlock R.params.side z = Y := by
    rcases h with ⟨b, hb, e⟩ | ⟨z, hz, e⟩
    · exact ⟨b.1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb), e⟩
    · exact ⟨z, Finset.mem_union_right _ hz, e⟩
  obtain ⟨z, hz, rfl⟩ := hz
  simp only [GasSupport.core, supportCore, coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [sitesInBlocks]
  · exact (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
theorem core_nonempty (G : GasGround R n) (i : G.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem coreWeightFrom_pos (G : GasGround R n) (Y : TorusSite n) (i : G.GasSpin) : 0 < G.coreWeightFrom Y i := by
  unfold GasGround.coreWeightFrom coreWeight
  have : 0 < (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
  positivity
theorem one_le_coreWeightFrom_of_meets (G : GasGround R n) {Y : TorusSite n} (i : G.GasSpin) (h : i.1.Meets Y) :
    1 ≤ G.coreWeightFrom Y i := by
  unfold GasGround.coreWeightFrom coreWeight
  have hY := mem_core_of_meets G i h
  have h0 : setGap {Y} i.1.core = 0 := by
    unfold setGap
    refine Nat.le_zero.mp (Nat.sInf_le ⟨Y, by simp, Y, hY, supDist_self Y⟩)
  rw [h0]
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact_mod_cast Finset.card_pos.mpr ⟨Y, hY⟩
theorem isLocalObservable_of_readsComponentsAt (G : GasGround R n) (Y : TorusSite n) {F : G.Config → ℝ}
    (hF : G.ReadsComponentsAt Y F) :
    letI : DecidablePred fun i : G.GasSpin => i.1.Meets Y := Classical.decPred _
    G.pairConstraint.IsLocalObservable (Finset.univ.filter fun i : G.GasSpin => i.1.Meets Y)
      (G.coreWeightFrom Y) F := by
  classical
  refine ⟨hF.measurable, hF.abs_le_one, ⟨fun i => ?_, ?_⟩, fun i hi => ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · intro i σ σ' _ _ hd
    dsimp only
    by_cases hi : i ∈ Finset.univ.filter fun i : G.GasSpin => i.1.Meets Y
    · rw [if_pos hi]
      have h1 := hF.abs_le_one σ
      have h2 := hF.abs_le_one σ'
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [if_neg hi, hF.eq_of_agree σ σ' fun k hk => hd k fun e => hi (by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, e ▸ hk⟩)]
      simp
  · exact one_le_coreWeightFrom_of_meets G i (Finset.mem_filter.mp hi).2
section Compare
variable {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ}
  {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
theorem extendSecond_index_injective (g : SharedInnerGas G G' Y Y' N m A A') :
    Function.Injective fun j => (g.spinEquiv j).1 :=
  Subtype.val_injective.comp g.spinEquiv.injective
theorem extendFirst_inner (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : InnerGasSpin G Y m A) :
    g.extendFirst τ j.1 = τ j := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendFirst_apply <;> assumption
theorem extendSecond_inner (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : InnerGasSpin G Y m A) :
    g.extendSecond τ (g.spinEquiv j).1 = g.valueEquiv j (τ j) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_apply <;> assumption
theorem extendFirst_of_not_inner (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G.GasSpin}
    (h : ¬ G.IsInnerSpin Y m A i) : g.extendFirst τ i = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendFirst_of_not_inner <;> assumption
theorem extendSecond_of_not_mem_range (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G'.GasSpin}
    (h : ∀ j : InnerGasSpin G Y m A, (g.spinEquiv j).1 ≠ i) : g.extendSecond τ i = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_of_forall_ne <;> assumption
theorem componentsMatch_extend (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) :
    ComponentsMatch G G' Y Y' N (g.extendFirst τ) (g.extendSecond τ) := by
  have core : ∀ j : InnerGasSpin G Y m A, τ j ≠ Sum.inl () →
      ComponentIn G G' Y Y' N (g.extendFirst τ) (g.extendSecond τ) j.1 (g.spinEquiv j).1 := by
    intro j hj
    rcases hτ : τ j with u | s
    · exact absurd hτ hj
    · obtain ⟨s', hs', hst⟩ := g.map_occupied j s
      have hs'' : g.valueEquiv j (Sum.inr s) = Sum.inr s' := hs'
      exact ⟨g.sameSupport j, s, s', by rw [extendFirst_inner g τ j, hτ],
        by rw [extendSecond_inner g τ j, hτ, hs''], hst⟩
  refine ⟨fun i hi hne => ?_, fun i' hi' hne => ?_⟩
  · by_cases hin : G.IsInnerSpin Y m A i
    · have hj : τ ⟨i, hin⟩ ≠ Sum.inl () := by
        rw [← extendFirst_inner g τ ⟨i, hin⟩]
        exact hne
      exact ⟨(g.spinEquiv ⟨i, hin⟩).1, (g.meets_iff ⟨i, hin⟩).mp hi, core ⟨i, hin⟩ hj⟩
    · exact absurd (extendFirst_of_not_inner g τ hin) hne
  · by_cases h1 : ∃ j : InnerGasSpin G Y m A, (g.spinEquiv j).1 = i'
    · obtain ⟨j, rfl⟩ := h1
      have hj : τ j ≠ Sum.inl () := by
        intro h
        apply hne
        rw [extendSecond_inner g τ j, h]
        exact g.map_vacant j
      exact ⟨j.1, (g.meets_iff j).mpr hi', core j hj⟩
    · exact absurd (extendSecond_of_not_mem_range g τ fun j hj => h1 ⟨j, hj⟩) hne
end Compare
section Numbers
theorem mul_le_exp_mul_of_abs_log_sub_le {a b a' b' ε : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a')
    (hb' : 0 < b') (h : |(Real.log b - Real.log a) - (Real.log b' - Real.log a')| ≤ ε) :
    b * a' ≤ Real.exp ε * (a * b') ∧ b' * a ≤ Real.exp ε * (a' * b) := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  have e : ∀ p q : ℝ, 0 < p → 0 < q → Real.log p ≤ Real.log q + ε → p ≤ Real.exp ε * q := by
    intro p q hp hq hl
    have : Real.exp (Real.log p) ≤ Real.exp (Real.log q + ε) := Real.exp_le_exp.mpr hl
    rw [Real.exp_log hp, Real.exp_add, Real.exp_log hq] at this
    linarith
  constructor
  · refine e _ _ (mul_pos hb ha') (mul_pos ha hb') ?_
    rw [Real.log_mul hb.ne' ha'.ne', Real.log_mul ha.ne' hb'.ne']
    linarith
  · refine e _ _ (mul_pos hb' ha) (mul_pos ha' hb) ?_
    rw [Real.log_mul hb'.ne' ha.ne', Real.log_mul ha'.ne' hb.ne']
    linarith
theorem exists_polyExp_sum_le_one {ρ K : ℝ} (hρ : 0 < ρ) : ∃ Lc : ℕ, ∀ l : ℕ, Lc ≤ l →
    32 * ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * ρ * l)) + K * Real.exp (-(ρ * l)) ≤ 1 := by
  have hnat : Filter.Tendsto (fun l : ℕ => (l : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have t2 : Filter.Tendsto (fun l : ℕ => K * Real.exp (-(ρ * l))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun l : ℕ => -(ρ * (l : ℝ))) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp (hnat.const_mul_atTop hρ)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul K
    simpa using h2
  have t1 : Filter.Tendsto (fun l : ℕ => 32 * ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * ρ * l))) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun l : ℕ => 2 * ρ * ((l : ℝ) + 1)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_atTop_add_const_right _ 1 hnat).const_mul_atTop (by positivity)
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp h1).const_mul
      (32 * Real.exp (2 * ρ) / (2 * ρ) ^ 4)
    have e : ∀ l : ℕ, 32 * Real.exp (2 * ρ) / (2 * ρ) ^ 4 *
        ((fun x : ℝ => x ^ 4 * Real.exp (-x)) ∘ fun l : ℕ => 2 * ρ * ((l : ℝ) + 1)) l =
        32 * ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * ρ * l)) := by
      intro l
      simp only [Function.comp]
      have e1 : Real.exp (-(2 * ρ * ((l : ℝ) + 1))) = Real.exp (-(2 * ρ * l)) * Real.exp (-(2 * ρ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e2 : Real.exp (2 * ρ) * Real.exp (-(2 * ρ)) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [e1]
      field_simp
      exact e2
    simp only [mul_zero] at h2
    exact h2.congr e
  have t := t1.add t2
  simp only [add_zero] at t
  have hev := t.eventually (gt_mem_nhds (zero_lt_one))
  obtain ⟨Lc, hLc⟩ := Filter.eventually_atTop.mp hev
  exact ⟨Lc, fun l hl => (hLc l hl).le⟩
theorem exp_sub_one_le_two_mul {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : Real.exp ε - 1 ≤ 2 * ε := by
  have h2 := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have h3 : 1 / (1 - ε) ≤ 1 + 2 * ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
variable {G : GasGround R n}
theorem supDist_le_coreDiam {i : GasSupport R n} {y z : TorusSite n} (hy : y ∈ i.core) (hz : z ∈ i.core) :
    supDist y z ≤ i.coreDiam :=
  (Finset.le_sup (f := fun z => supDist y z) hz).trans
    (Finset.le_sup (f := fun y => i.core.sup fun z => supDist y z) hy)
theorem exists_supDist_eq_setGap (Y : TorusSite n) {X : Finset (TorusSite n)} (h : X.Nonempty) :
    ∃ y ∈ X, supDist Y y = setGap {Y} X := by apply _root_.YangMills.Construction.StepGas.exists_mem_supDist_eq_setGap <;> assumption
theorem le_setGap_add_coreDiam (Y : TorusSite n) (i : G.GasSpin) {D : ℕ}
    (h : ∃ y ∈ i.1.core, D ≤ supDist y Y) : D ≤ setGap {Y} i.1.core + i.1.coreDiam := by
  obtain ⟨y, hy, hD⟩ := h
  obtain ⟨y₁, hy₁, e⟩ := exists_supDist_eq_setGap Y (core_nonempty G i)
  have h1 := supDist_triangle y y₁ Y
  have h2 := supDist_le_coreDiam hy hy₁
  rw [supDist_comm y₁ Y, e] at h1
  omega
theorem spinActivity_nonneg (i : G.GasSpin) (c : ℝ) : 0 ≤ G.spinActivity c i := by
  unfold GasGround.spinActivity clusterWeight
  positivity
theorem coreWeightFrom_mul_activity_le_far (Y : TorusSite n) (i : G.GasSpin) {c : ℝ} {D : ℕ}
    (hrt : 0 < R.params.rt) (h : ∃ y ∈ i.1.core, D ≤ supDist y Y) :
    G.coreWeightFrom Y i * G.spinActivity c i ≤ Real.exp (-(3 * (R.params.rt / 2 ^ 8) * D)) *
      (G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) *
      Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
  have hg : (D : ℝ) ≤ (setGap {Y} i.1.core : ℝ) + i.1.coreDiam := by
    exact_mod_cast le_setGap_add_coreDiam Y i h
  have hd : (0 : ℝ) ≤ i.1.coreDiam := Nat.cast_nonneg _
  have hg0 : (0 : ℝ) ≤ setGap {Y} i.1.core := Nat.cast_nonneg _
  unfold GasGround.coreWeightFrom coreWeight
  have ha : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
  have ha4 : (i.1.core.card : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := le_self_pow₀ ha (by norm_num)
  have hz := spinActivity_nonneg (G := G) i c
  have he : Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) ≤
      Real.exp (-(3 * (R.params.rt / 2 ^ 8) * D)) * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) *
        Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hrt.le hd, mul_nonneg hrt.le hg0]
  have h1 := mul_le_mul ha4 he (Real.exp_pos _).le (by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 hz
  refine h2.trans (le_of_eq ?_)
  ring
theorem coreWeightFrom_mul_activity_le_near (Y : TorusSite n) (i : G.GasSpin) {c : ℝ} {D l N₂ : ℕ}
    (hrt : 0 < R.params.rt) (h : ∃ y ∈ i.1.core, D ≤ supDist y Y) (hN : N₂ ≤ l + D) :
    G.coreWeightFrom Y i *
        (2 * ((i.1.core.card : ℝ) * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * l))) * G.spinActivity c i) ≤
      2 * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * N₂)) *
        (G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) *
        Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
  have hg : (D : ℝ) ≤ (setGap {Y} i.1.core : ℝ) + i.1.coreDiam := by
    exact_mod_cast le_setGap_add_coreDiam Y i h
  have hN' : (N₂ : ℝ) ≤ l + D := by exact_mod_cast hN
  have hd : (0 : ℝ) ≤ i.1.coreDiam := Nat.cast_nonneg _
  have hg0 : (0 : ℝ) ≤ setGap {Y} i.1.core := Nat.cast_nonneg _
  unfold GasGround.coreWeightFrom coreWeight
  have ha : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
  have ha4 : (i.1.core.card : ℝ) * (i.1.core.card : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := by
    have : (i.1.core.card : ℝ) ^ 2 ≤ (i.1.core.card : ℝ) ^ 4 := pow_le_pow_right₀ ha (by norm_num)
    nlinarith
  have hz := spinActivity_nonneg (G := G) i c
  have he : Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) *
        Real.exp (-(2 * (R.params.rt / 2 ^ 8) * l)) ≤
      Real.exp (-(2 * (R.params.rt / 2 ^ 8) * N₂)) * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) *
        Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hrt.le hd, mul_nonneg hrt.le hg0]
  have h1 := mul_le_mul ha4 he (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hz)
  refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_))
  · ring
  · ring
theorem exists_offset_of_supDist_le {p : ℕ} [NeZero p] (y Y : TorusSite p) (m : ℕ) (h : supDist y Y ≤ m) :
    ∃ g, OffsetInBox m g ∧ y = Y + siteOfInt g := by
  have hle := (supDist_le_iff y Y m).mp h
  refine ⟨fun i => (y i - Y i).valMinAbs, fun i => ?_, ?_⟩
  · have := hle i
    change |(y i - Y i).valMinAbs| ≤ _
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  · funext i
    have hp : (((y i - Y i).valMinAbs : ℤ) : ZMod p) = y i - Y i := ZMod.coe_valMinAbs _
    change y i = Y i + (((y i - Y i).valMinAbs : ℤ) : ZMod p)
    rw [hp]
    ring
theorem range_ceil_le {r L Lc m₀ : ℕ} (hL : 2 ^ 40 ≤ L) (hdiv : r < 2 ^ 11 * (m₀ + 1)) (hm1 : 1 ≤ m₀)
    (hm0 : Lc + 9 ≤ m₀) : Lc + 2 * ⌈(r : ℝ) / (4 * (L : ℝ))⌉₊ + 6 ≤ 5 * m₀ := by
  have hLbig : (2 : ℝ) ^ 40 ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < 4 * (L : ℝ) := by positivity
  have hq2 : ((⌈(r : ℝ) / (4 * (L : ℝ))⌉₊ : ℕ) : ℝ) < (r : ℝ) / (4 * (L : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hr' : (r : ℝ) < 2 ^ 11 * ((m₀ : ℝ) + 1) := by exact_mod_cast hdiv
  have hq3 : (r : ℝ) / (4 * (L : ℝ)) ≤ ((m₀ : ℝ) + 1) / 4 := by
    rw [div_le_iff₀ hLpos]
    have hm : (0 : ℝ) ≤ (m₀ : ℝ) + 1 := by positivity
    nlinarith
  have hq4 : 2 * ((⌈(r : ℝ) / (4 * (L : ℝ))⌉₊ : ℕ) : ℝ) ≤ (m₀ : ℝ) + 3 := by
    have : (1 : ℝ) ≤ m₀ := by exact_mod_cast hm1
    linarith
  have hq5 : 2 * ⌈(r : ℝ) / (4 * (L : ℝ))⌉₊ ≤ m₀ + 3 := by exact_mod_cast hq4
  omega
theorem eight_mul_sub_one_le {e z E : ℝ} (hz : 0 ≤ z) (he : 0 ≤ e) (hE : E - 1 ≤ 2 * e) :
    8 * (E - 1) * z ≤ 32 * e * z := by
  have h9 := mul_le_mul_of_nonneg_right hE hz
  have h10 : 0 ≤ e * z := mul_nonneg he hz
  nlinarith [h9, h10]
theorem exp_neg_three_le_exp_neg_two {ρ D N : ℝ} (hρ : 0 ≤ ρ) (h : 2 * N ≤ 3 * D) :
    Real.exp (-(3 * ρ * D)) ≤ Real.exp (-(2 * ρ * N)) := by
  refine Real.exp_le_exp.mpr ?_
  nlinarith
end Numbers
section Main
end Main
end GasComparison
end YangMills.Construction
end
