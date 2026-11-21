import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.CaseMassWithAFunctionIsBorelForm
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheStates
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped ENNReal
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepCosts TorusFields TorusLumps StepGas WeightedResponses ColdStepAtMirrorFrames ClusterExpansionOfAStep StateMeasurability
namespace StepMeanOfStates
section General
private theorem withDensity_integral_of_quotient {P : Type} [MeasurableSpace P] {lam : Measure P} {d Ap An : P → ℝ≥0∞} {H : P → ℝ}
    (hd : Measurable d) (hdt : ∀ p, d p ≠ ⊤) (hAp : Measurable Ap) (hAn : Measurable An)
    (hfp : ∫⁻ p, Ap p ∂lam ≠ ⊤) (hfn : ∫⁻ p, An p ∂lam ≠ ⊤)
    (hz : ∀ᵐ p ∂lam, d p = 0 → Ap p = 0 ∧ An p = 0)
    (hH : ∀ᵐ p ∂lam, d p ≠ 0 → H p = ((Ap p).toReal - (An p).toReal) / (d p).toReal) :
    Integrable H (lam.withDensity d) ∧
      ∫ p, H p ∂(lam.withDensity d) = (∫⁻ p, Ap p ∂lam).toReal - (∫⁻ p, An p ∂lam).toReal := by
  set Ht : P → ℝ := fun p => ((Ap p).toReal - (An p).toReal) / (d p).toReal with hHt
  have hae : H =ᵐ[lam.withDensity d] Ht := (ae_withDensity_iff hd).mpr hH
  have hpt : ∀ᵐ p ∂lam, (d p).toReal • Ht p = (Ap p).toReal - (An p).toReal := by
    filter_upwards [hz] with p hp
    by_cases h0 : d p = 0
    · simp [h0, (hp h0).1, (hp h0).2]
    · have h1 : (d p).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h0, hdt p⟩
      simp only [hHt, smul_eq_mul]
      field_simp
  have hi1 : Integrable (fun p => (Ap p).toReal) lam := integrable_toReal_of_lintegral_ne_top hAp.aemeasurable hfp
  have hi2 : Integrable (fun p => (An p).toReal) lam := integrable_toReal_of_lintegral_ne_top hAn.aemeasurable hfn
  have hlt : ∀ᵐ p ∂lam, d p < ⊤ := Filter.Eventually.of_forall fun p => lt_top_iff_ne_top.mpr (hdt p)
  have hI : Integrable Ht (lam.withDensity d) := by
    rw [integrable_withDensity_iff_integrable_smul' hd hlt]
    exact (hi1.sub hi2).congr (hpt.mono fun p hp => hp.symm)
  refine ⟨hI.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_withDensity_eq_integral_toReal_smul hd hlt, integral_congr_ae hpt,
    integral_sub hi1 hi2, integral_toReal hAp.aemeasurable (ae_lt_top hAp hfp),
    integral_toReal hAn.aemeasurable (ae_lt_top hAn hfn)]
private theorem integral_iterated_eq_posPart_sub_negPart {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {u : X × Y → ℝ} (hu : Measurable u)
    (hp : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (u (x, y)) ∂ν ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (-u (x, y)) ∂ν ∂μ ≠ ⊤) :
    Integrable (fun x => ∫ y, u (x, y) ∂ν) μ ∧
      ∫ x, ∫ y, u (x, y) ∂ν ∂μ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (u (x, y)) ∂ν ∂μ).toReal -
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-u (x, y)) ∂ν ∂μ).toReal := by
  have e1 : ∫⁻ p, ENNReal.ofReal (u p) ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (u (x, y)) ∂ν ∂μ :=
    lintegral_prod _ (ENNReal.measurable_ofReal.comp hu).aemeasurable
  have e2 : ∫⁻ p, ENNReal.ofReal (-u p) ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (-u (x, y)) ∂ν ∂μ :=
    lintegral_prod _ (ENNReal.measurable_ofReal.comp hu.neg).aemeasurable
  have hi : Integrable u (μ.prod ν) := by
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ p, ‖u p‖ₑ ≤ ENNReal.ofReal (u p) + ENNReal.ofReal (-u p) := by
      intro p
      rw [Real.enorm_eq_ofReal_abs]
      rcases le_total 0 (u p) with h | h
      · rw [abs_of_nonneg h]
        exact le_self_add
      · rw [abs_of_nonpos h]
        exact le_add_self
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    have hm1 : Measurable fun p => ENNReal.ofReal (u p) := ENNReal.measurable_ofReal.comp hu
    rw [lintegral_add_left hm1, e1, e2]
    exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hp, lt_top_iff_ne_top.mpr hn⟩
  refine ⟨hi.integral_prod_left, ?_⟩
  rw [← integral_prod _ hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  simp only [e1, e2]
private theorem sum_lintegral_lintegral {ι X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite ν] (S : Finset ι) (F : ι → X → Y → ℝ≥0∞) (hF : ∀ i, Measurable fun p : X × Y => F i p.1 p.2) :
    ∑ i ∈ S, ∫⁻ x, ∫⁻ y, F i x y ∂ν ∂μ = ∫⁻ x, ∫⁻ y, ∑ i ∈ S, F i x y ∂ν ∂μ := by
  rw [← lintegral_finsetSum _ fun i _ => (hF i).lintegral_prod_right']
  refine lintegral_congr fun x => ?_
  exact (lintegral_finsetSum _ fun i _ => (hF i).comp measurable_prodMk_left).symm
private theorem measurable_comp_swap_triple {A B C : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] {κ : B → A → ℝ}
    (hκ : Measurable fun p : B × A => κ p.1 p.2) : Measurable fun p : A × B × C => κ p.2.1 p.1 :=
  hκ.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
private theorem measurable_lintegral_lintegral {A B C : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] {ν₁ : Measure B}
    {ν₂ : Measure C} [SFinite ν₁] [SFinite ν₂] {f : A × B × C → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, ∫⁻ c, f (a, b, c) ∂ν₂ ∂ν₁ := by
  have h : Measurable fun x : (A × B) × C => f (x.1.1, x.1.2, x.2) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact h.lintegral_prod_right'.lintegral_prod_right'
private theorem lintegral_triple_eq_withDensity {A B C : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] {μ : Measure A}
    {ν₁ : Measure B} {ν₂ : Measure C} [SFinite μ] [SFinite ν₁] [SFinite ν₂] {d : B × C → ℝ≥0∞} (hd : Measurable d)
    {k : A × B × C → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, d (b, c) * k (a, b, c) ∂ν₂ ∂ν₁ ∂μ =
      ∫⁻ p : B × C, ∫⁻ a, k (a, p.1, p.2) ∂μ ∂((ν₁.prod ν₂).withDensity d) := by
  have hk1 : Measurable fun x : (B × C) × A => k (x.2, x.1.1, x.1.2) :=
    hk.comp (measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)))
  have hg : Measurable fun p : B × C => ∫⁻ a, k (a, p.1, p.2) ∂μ := hk1.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
  have hm : Measurable fun x : A × B × C => d x.2 * k x := (hd.comp measurable_snd).mul hk
  have e1 : ∀ a, ∫⁻ b, ∫⁻ c, d (b, c) * k (a, b, c) ∂ν₂ ∂ν₁ = ∫⁻ p : B × C, d p * k (a, p) ∂(ν₁.prod ν₂) := by
    intro a
    have hs : Measurable fun p : B × C => d p * k (a, p) := hd.mul (hk.comp measurable_prodMk_left)
    exact (lintegral_prod _ hs.aemeasurable).symm
  simp_rw [e1]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun p => ?_
    have hs : Measurable fun a => k (a, p) := hk.comp measurable_prodMk_right
    exact lintegral_const_mul _ hs
  · have hm2 : Measurable fun x : A × B × C => d x.2 * k x := hm
    exact hm2.aemeasurable.comp_measurable measurable_id
private theorem measurable_comp_pair_fst {A B C : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] {κ : B → A → ℝ}
    (hκ : Measurable fun p : B × A => κ p.1 p.2) : Measurable fun x : (B × C) × A => κ x.1.1 x.2 :=
  hκ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
private theorem toReal_sum_sum {Ti Bs : Type} [Fintype Ti] [Fintype Bs] (f : Ti → Bs → ℝ≥0∞) (hf : ∀ a b, f a b ≠ ⊤) :
    (∑ a, ∑ b, f a b).toReal = ∑ a, ∑ b, (f a b).toReal := by
  rw [ENNReal.toReal_sum fun a _ => ENNReal.sum_ne_top.mpr fun b _ => hf a b]
  exact Finset.sum_congr rfl fun a _ => ENNReal.toReal_sum fun b _ => hf a b
private theorem toReal_sum_sum_sum {Bd Ti Bs : Type} [Fintype Ti] [Fintype Bs] (P : Finset Bd) (f : Bd → Ti → Bs → ℝ≥0∞)
    (hf : ∑ a ∈ P, ∑ b, ∑ c, f a b c ≠ ⊤) :
    (∑ a ∈ P, ∑ b, ∑ c, f a b c).toReal = ∑ a ∈ P, ∑ b, ∑ c, (f a b c).toReal := by
  have h1 := ENNReal.sum_ne_top.mp hf
  rw [ENNReal.toReal_sum h1]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h2 := ENNReal.sum_ne_top.mp (h1 a ha)
  rw [ENNReal.toReal_sum h2]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact ENNReal.toReal_sum (ENNReal.sum_ne_top.mp (h2 b hb))
private theorem lintegral_sum_sum_sum {Bd Ti Bs X : Type} [Fintype Ti] [Fintype Bs] [MeasurableSpace X] {μ : Measure X} (P : Finset Bd)
    (f : Bd → Ti → Bs → X → ℝ≥0∞) (hf : ∀ a b c, Measurable (f a b c)) :
    ∫⁻ x, ∑ a ∈ P, ∑ b, ∑ c, f a b c x ∂μ = ∑ a ∈ P, ∑ b, ∑ c, ∫⁻ x, f a b c x ∂μ := by
  rw [lintegral_finsetSum _ fun a _ => Finset.measurable_fun_sum _ fun b _ => Finset.measurable_fun_sum _ fun c _ => hf a b c]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lintegral_finsetSum _ fun b _ => Finset.measurable_fun_sum _ fun c _ => hf a b c]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lintegral_finsetSum _ fun c _ => hf a b c]
private theorem sum_four_reorder {Yi Bd Ti Bs : Type} [Fintype Yi] [Fintype Ti] [Fintype Bs] (P : Finset Bd)
    (f : Yi → Bd → Ti → Bs → ℝ≥0∞) (g : Bd → Ti → Bs → ℝ≥0∞) (k : Ti → Bs → ℝ≥0∞)
    (h1 : ∀ bad ti bs, ∑ y, f y bad ti bs = g bad ti bs) (h2 : ∀ ti bs, ∑ bad ∈ P, g bad ti bs = k ti bs) :
    ∑ y, ∑ bad ∈ P, ∑ ti, ∑ bs, f y bad ti bs = ∑ ti, ∑ bs, k ti bs := by
  rw [Finset.sum_comm]
  have e : ∀ bad ∈ P, ∑ y, ∑ ti, ∑ bs, f y bad ti bs = ∑ ti, ∑ bs, g bad ti bs := by
    intro bad _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ti _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun bs _ => h1 bad ti bs
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ti _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun bs _ => h2 ti bs
end General
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem sum_markProduct (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R C).powerset, ENNReal.ofReal (markProduct R C V W bad) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.sum_markProduct_eq_one <;> assumption
end Marks
section Model
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def hullDensity (R : StepSetup) (m : ℕ) [NeZero m] (Y : Finset (TorusSite m)) (p : TorusField m × (Y → R.labels.Ω)) : ℝ≥0∞ :=
  open Classical in if IsHullState R.params (clusterRange R.coupling) p.1 Y then ENNReal.ofReal (R.labelWeight m p.1 Y p.2) else 0
private theorem measurable_hullDensity (hrow : R.HasExpansions) {m : ℕ} [NeZero m] (hb : IsBlockTorusSide R.params m) (Y : Finset (TorusSite m)) :
    Measurable (hullDensity R m Y) := by
  classical
  have e : hullDensity R m Y = ENNReal.ofReal ∘ fun p : TorusField m × (Y → R.labels.Ω) =>
      if IsHullState R.params (clusterRange R.coupling) p.1 Y then R.labelWeight m p.1 Y p.2 else 0 := by
    funext p
    unfold hullDensity
    simp only [Function.comp_apply]
    split_ifs <;> simp
  rw [e]
  exact ENNReal.measurable_ofReal.comp (hrow.2.borel m hb Y).1
private theorem stepTransitionDensity_eq (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n) :
    stepTransitionDensity R.params R.coupling W b V = baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by
  classical
  unfold stepTransitionDensity baseLaw
  split_ifs <;> simp
abbrev _root_.YangMills.SharedProofs.p31947 := @stepTransitionDensity_eq
private theorem kernel_prod_nonneg (hk : BondKernelProperties) (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n) :
    0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
  Finset.prod_nonneg fun c _ => (hk.2 R.params R.coupling n _ _ b c).1.le
private theorem baseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) : 0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem stepTransitionDensity_nonneg (hk : BondKernelProperties) (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n) :
    0 ≤ stepTransitionDensity R.params R.coupling W b V := by
  rw [stepTransitionDensity_eq]
  exact mul_nonneg (baseLaw_nonneg W b) (kernel_prod_nonneg hk W b V)
private theorem stepWeight_eq (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b = R.labelWeight (n * R.params.side) W Yt ωt * stepTransitionDensity R.params R.coupling W b V * markProduct R C V W bad := by
  unfold stepWeight
  rw [stepTransitionDensity_eq]
  ring
abbrev _root_.YangMills.SharedProofs.p15525 := @stepWeight_eq
private theorem stepWeight_nonneg (hR : R.IsWellPosed) (hk : BondKernelProperties) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    (hh : IsHullState R.params R.range W Yt) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by
  rw [stepWeight_eq]
  exact mul_nonneg (mul_nonneg (hR.hasExpansions.2.nonneg _ hb _ _ _ hh) (stepTransitionDensity_nonneg hk W b V)) (markProduct_nonneg hR C V W bad)
private theorem configurationWeight_factor (hR : R.IsWellPosed) (hk : BondKernelProperties) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ωt =
      hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * ENNReal.ofReal (markProduct R C V W bad) := by
  classical
  unfold configurationWeight hullDensity
  by_cases hh : IsHullState R.params R.range W Yt
  · have hh' : IsHullState R.params (clusterRange R.coupling) W Yt := hh
    simp only [if_pos hh, if_pos hh']
    rw [stepWeight_eq, ENNReal.ofReal_mul (mul_nonneg (hR.hasExpansions.2.nonneg _ hb _ _ _ hh') (stepTransitionDensity_nonneg hk W b V)),
      ENNReal.ofReal_mul (hR.hasExpansions.2.nonneg _ hb _ _ _ hh')]
  · have hh' : ¬ IsHullState R.params (clusterRange R.coupling) W Yt := hh
    simp [if_neg hh, if_neg hh']
private theorem sum_over_badBonds (hR : R.IsWellPosed) (hk : BondKernelProperties) (hw : ConfigurationWeightMeasurable)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (hn₀ : R.params.n₀ ≤ n) (C : Finset (TorusSite n)) (V : TorusField n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (h : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞)
    (hh : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => h p.1 p.2) :
    ∑ bad ∈ (markedBonds R C).powerset, ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * h W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * h W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hm : ∀ bad : Finset (TorusBond (n * R.params.side)), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2 * h p.1 p.2 := fun bad => (hw R hR n hn₀ C V bad Yt b).mul hh
  rw [sum_lintegral_lintegral _ (fun bad W ωt => configurationWeight R C V bad Yt b W ωt * h W ωt) hm]
  refine lintegral_congr fun W => lintegral_congr fun ωt => ?_
  have e : ∀ bad ∈ (markedBonds R C).powerset, configurationWeight R C V bad Yt b W ωt * h W ωt =
      hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * ENNReal.ofReal (markProduct R C V W bad) *
        h W ωt := fun bad _ => by rw [configurationWeight_factor hR hk hb]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← Finset.mul_sum, sum_markProduct hR C V W, mul_one]
private theorem sum_hull_configurationMass (hC : ConfigurationMassWithFunction) (hH : CoarseHullIsHullState)
    (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params n) (hn₀ : R.params.n₀ ≤ n) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (h : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞)
    (hh : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => h p.1 p.2) :
    ∑ Y : Finset (TorusSite n), (open Classical in if IsHullState R.params R.nextRange V Y then
        ∫⁻ ω, configurationMassWith R (hotCoreSites R V) V bad Yt b h ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt * h W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hC R hR n hn₀ (hotCoreSites R V) V bad Yt b h hh
  have hmem : IsHullState R.params R.nextRange V (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)) :=
    hH R.params hR.admissible R.range R.nextRange hR.range_le hR.nextRange_ge n hside.1 V bad Yt
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)))]
  · rw [if_pos hmem]
    exact h4
  · intro Y _ hY
    split_ifs
    · rw [lintegral_congr fun ω => h1 ⟨Y, ω⟩ hY]
      simp
    · rfl
end Model
section Sums
variable {R : StepSetup} {n : ℕ} [NeZero n]
private abbrev ConfigurationFamily (R : StepSetup) (n : ℕ) : Type :=
  (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n → TorusField n → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞
private def IsMeasurableFamily (h : ConfigurationFamily R n) : Prop :=
  ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => h Yt b p.1 p.2.1 p.2.2
open Classical in
private def configurationSum (h : ConfigurationFamily R n) (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) : ℝ≥0∞ :=
  ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩
open Classical in
private def hullConfigurationSum (h : ConfigurationFamily R n) (Y : Finset (TorusSite n)) (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) : ℝ≥0∞ :=
  if IsHullState R.params R.nextRange p.1 Y then configurationSum h p.1 Y p.2 else 0
private def configurationTotal (h : ConfigurationFamily R n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) : ℝ≥0∞ :=
  ∫⁻ V, ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * h Yt b V W ωt
    ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ∂(fieldHaar n)
private theorem measurable_family_section {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (V : TorusField n) : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => h Yt b V p.1 p.2 :=
  (hh Yt b).comp (measurable_const.prodMk measurable_id)
private theorem measurable_integrand (hD : StepTransitionDensityBounds) (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side))
    {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      hullDensity R (n * R.params.side) Yt p.2 * ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.2.1 b p.1) * h Yt b p.1 p.2.1 p.2.2 := by
  have h1 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => hullDensity R (n * R.params.side) Yt p.2 :=
    (measurable_hullDensity hrow hb Yt).comp measurable_snd
  have h2 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => stepTransitionDensity R.params R.coupling p.2.1 b p.1 :=
    measurable_comp_swap_triple (κ := fun W V => stepTransitionDensity R.params R.coupling W b V) ((hD R.params R.coupling n).1 b)
  have h3 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.2.1 b p.1) := ENNReal.measurable_ofReal.comp h2
  exact (h1.mul h3).mul (hh Yt b)
private theorem sum_hull_configurationSum (hC : ConfigurationMassWithFunction) (hH : CoarseHullIsHullState)
    (hw : ConfigurationWeightMeasurable) (hk : BondKernelProperties) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params n) (hb : IsBlockTorusSide R.params (n * R.params.side)) (hn₀ : R.params.n₀ ≤ n) {h : ConfigurationFamily R n}
    (hh : IsMeasurableFamily h) (V : TorusField n) :
    ∑ Y : Finset (TorusSite n), (open Classical in if IsHullState R.params R.nextRange V Y then
        ∫⁻ ω, configurationSum h V Y ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * h Yt b V W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hm : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (Y : Finset (TorusSite n)), Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
        configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩ := by
    intro bad Yt b Y
    obtain ⟨h1, h2, h3, h4⟩ := hC R hR n hn₀ (hotCoreSites R V) V bad Yt b (h Yt b V) (measurable_family_section hh Yt b V)
    by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)
    · subst hY
      exact h3
    · have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩) =
          fun _ => 0 := funext fun ω => h1 ⟨Y, ω⟩ hY
      rw [this]
      exact measurable_const
  have hY : ∀ Y : Finset (TorusSite n), (if IsHullState R.params R.nextRange V Y then
      ∫⁻ ω, configurationSum h V Y ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0) =
      ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        if IsHullState R.params R.nextRange V Y then ∫⁻ ω, configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0 := by
    intro Y
    by_cases hy : IsHullState R.params R.nextRange V Y
    · simp only [if_pos hy]
      exact lintegral_sum_sum_sum (markedBonds R (hotCoreSites R V)).powerset
        (fun bad Yt b ω => configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩) fun bad Yt b => hm bad Yt b Y
    · simp only [if_neg hy, Finset.sum_const_zero]
  refine (Finset.sum_congr rfl fun Y _ => hY Y).trans ?_
  refine sum_four_reorder (markedBonds R (hotCoreSites R V)).powerset
    (fun Y bad Yt b => if IsHullState R.params R.nextRange V Y then ∫⁻ ω, configurationMassWith R (hotCoreSites R V) V bad Yt b (h Yt b V) ⟨Y, ω⟩
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0)
    (fun bad Yt b => ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R (hotCoreSites R V) V bad Yt b W ωt * h Yt b V W ωt
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) _ ?_ ?_
  · intro bad Yt b
    exact sum_hull_configurationMass hC hH hR hside hn₀ V bad Yt b (h Yt b V) (measurable_family_section hh Yt b V)
  · intro Yt b
    exact sum_over_badBonds hR hk hw hb hn₀ (hotCoreSites R V) V Yt b (h Yt b V) (measurable_family_section hh Yt b V)
end Sums
section Totals
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_hullConfigurationSum (hCset : ∀ C : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = C})
    (hHull : ∀ Y : Finset (TorusSite n), MeasurableSet {V : TorusField n | IsHullState R.params R.nextRange V Y})
    (hCM : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (G : TorusField n → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞),
      (Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2.1 p.2.2) →
      ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
        configurationMassWith R (hotCoreSites R p.1) p.1 bad Yt b (G p.1) ⟨Y, p.2⟩)
    {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h) (Y : Finset (TorusSite n)) : Measurable (hullConfigurationSum h Y) := by
  classical
  have hS : ∀ bad : Finset (TorusBond (n * R.params.side)), MeasurableSet {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      bad ∈ (markedBonds R (hotCoreSites R p.1)).powerset} := by
    intro bad
    have e : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | bad ∈ (markedBonds R (hotCoreSites R p.1)).powerset} =
        ⋃ C ∈ (Finset.univ.filter fun C : Finset (TorusSite n) => bad ∈ (markedBonds R C).powerset),
          Prod.fst ⁻¹' {V : TorusField n | hotCoreSites R V = C} := by
      ext p
      simp
    rw [e]
    exact Finset.measurableSet_biUnion _ fun C _ => measurable_fst (hCset C)
  have hterm : ∀ bad : Finset (TorusBond (n * R.params.side)), Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        configurationMassWith R (hotCoreSites R p.1) p.1 bad Yt b (h Yt b p.1) ⟨Y, p.2⟩ := fun bad =>
    Finset.measurable_fun_sum _ fun Yt _ => Finset.measurable_fun_sum _ fun b _ => hCM bad Yt b (h Yt b) (hh Yt b) Y
  have e : (fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) => configurationSum h p.1 Y p.2) =
      fun p => ∑ bad : Finset (TorusBond (n * R.params.side)), if bad ∈ (markedBonds R (hotCoreSites R p.1)).powerset then
        ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
          configurationMassWith R (hotCoreSites R p.1) p.1 bad Yt b (h Yt b p.1) ⟨Y, p.2⟩ else 0 := by
    funext p
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  have hsum : Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) => configurationSum h p.1 Y p.2 := by
    rw [e]
    exact Finset.measurable_fun_sum _ fun bad _ => Measurable.ite (hS bad) (hterm bad) measurable_const
  unfold hullConfigurationSum
  exact Measurable.ite (measurable_fst (hHull Y)) hsum measurable_const
private theorem sum_lintegral_hullConfigurationSum [SigmaFinite (coarseLabelMeasure R.labels.μ R.params.side)] (hC : ConfigurationMassWithFunction)
    (hH : CoarseHullIsHullState) (hw : ConfigurationWeightMeasurable) (hk : BondKernelProperties)
    (hD : StepTransitionDensityBounds) (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params n) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (hn₀ : R.params.n₀ ≤ n) {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h)
    (hmeas : ∀ Y : Finset (TorusSite n), Measurable (hullConfigurationSum h Y)) :
    ∑ Y : Finset (TorusSite n), ∫⁻ p, hullConfigurationSum h Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, configurationTotal h Yt b := by
  classical
  have hinner : ∀ (Y : Finset (TorusSite n)) (V : TorusField n),
      ∫⁻ ω, hullConfigurationSum h Y (V, ω) ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
        if IsHullState R.params R.nextRange V Y then ∫⁻ ω, configurationSum h V Y ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) else 0 := by
    intro Y V
    unfold hullConfigurationSum
    by_cases hy : IsHullState R.params R.nextRange V Y
    · simp only [if_pos hy]
    · simp only [if_neg hy, lintegral_zero]
  have e1 : ∀ Y : Finset (TorusSite n), ∫⁻ p, hullConfigurationSum h Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ∫⁻ V, ∫⁻ ω, hullConfigurationSum h Y (V, ω) ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) :=
    fun Y => lintegral_prod _ (hmeas Y).aemeasurable
  rw [Finset.sum_congr rfl fun Y _ => e1 Y,
    ← lintegral_finsetSum _ fun Y _ => (hmeas Y).lintegral_prod_right']
  have e2 : ∀ V : TorusField n, ∑ Y : Finset (TorusSite n), ∫⁻ ω, hullConfigurationSum h Y (V, ω) ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * h Yt b V W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro V
    rw [Finset.sum_congr rfl fun Y _ => hinner Y V]
    exact sum_hull_configurationSum hC hH hw hk hR hside hb hn₀ hh V
  rw [lintegral_congr e2]
  have hmI : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n), Measurable fun V : TorusField n =>
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, hullDensity R (n * R.params.side) Yt (W, ωt) * ENNReal.ofReal (stepTransitionDensity R.params R.coupling W b V) * h Yt b V W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := fun Yt b =>
    measurable_lintegral_lintegral (measurable_integrand hD hR.hasExpansions hb hh Yt b)
  rw [lintegral_finsetSum _ fun Yt _ => Finset.measurable_fun_sum _ fun b _ => hmI Yt b]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [lintegral_finsetSum _ fun b _ => hmI Yt b]
  rfl
private theorem configurationTotal_eq (hD : StepTransitionDensityBounds) (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side))
    {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    configurationTotal h Yt b = ∫⁻ p, ∫⁻ V, ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.1 b V) * h Yt b V p.1 p.2 ∂(fieldHaar n)
      ∂(stateMeasure R (n * R.params.side) Yt) := by
  have h2 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => stepTransitionDensity R.params R.coupling p.2.1 b p.1 :=
    measurable_comp_swap_triple (κ := fun W V => stepTransitionDensity R.params R.coupling W b V) ((hD R.params R.coupling n).1 b)
  have h3 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.2.1 b p.1) := ENNReal.measurable_ofReal.comp h2
  have hk : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.2.1 b p.1) * h Yt b p.1 p.2.1 p.2.2 := h3.mul (hh Yt b)
  have := lintegral_triple_eq_withDensity (μ := fieldHaar n) (ν₁ := fieldHaar (n * R.params.side)) (ν₂ := Measure.pi fun _ : Yt => R.labels.μ)
    (measurable_hullDensity hrow hb Yt) hk
  refine Eq.trans ?_ this
  unfold configurationTotal
  refine lintegral_congr fun V => lintegral_congr fun W => lintegral_congr fun ωt => ?_
  exact mul_assoc _ _ _
end Totals
section Value
variable {R : StepSetup} {n : ℕ} [NeZero n]
private abbrev LowerStateFunction (R : StepSetup) (n : ℕ) : Type :=
  (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ
private def positivePart (gt : LowerStateFunction R n) (ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) : ConfigurationFamily R n :=
  fun Yt b V W ωt => ENNReal.ofReal (gt Yt (W, ωt) * ψ W b V)
private def negativePart (gt : LowerStateFunction R n) (ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) : ConfigurationFamily R n :=
  fun Yt b V W ωt => ENNReal.ofReal (-(gt Yt (W, ωt) * ψ W b V))
private theorem measurable_parts {gt : LowerStateFunction R n} {ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ}
    (hgt : ∀ Yt, Measurable (gt Yt)) (hψ : ∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => ψ p.1 b p.2) :
    IsMeasurableFamily (positivePart gt ψ) ∧ IsMeasurableFamily (negativePart gt ψ) := by
  have hm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => gt Yt p.2 * ψ p.2.1 b p.1 := fun Yt b =>
    ((hgt Yt).comp measurable_snd).mul (measurable_comp_swap_triple (κ := fun W V => ψ W b V) (hψ b))
  exact ⟨fun Yt b => ENNReal.measurable_ofReal.comp (hm Yt b), fun Yt b => ENNReal.measurable_ofReal.comp (hm Yt b).neg⟩
private theorem ofReal_mul_le {a c d : ℝ} (hc : |c| ≤ d) : ENNReal.ofReal (a * c) ≤ ‖a‖ₑ * ENNReal.ofReal d := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc a * c ≤ |a * c| := le_abs_self _
    _ = |a| * |c| := abs_mul _ _
    _ ≤ |a| * d := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
private theorem configurationTotal_ne_top (hD : StepTransitionDensityBounds) (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side))
    {gt : LowerStateFunction R n} {Yt : Finset (TorusSite (n * R.params.side))} (hi : Integrable (gt Yt) (stateMeasure R (n * R.params.side) Yt))
    {h : ConfigurationFamily R n} (hh : IsMeasurableFamily h) (b : BaseChoice R.params.side n) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ V W ωt, h Yt b V W ωt ≤ ‖gt Yt (W, ωt)‖ₑ * c) : configurationTotal h Yt b ≠ ⊤ := by
  obtain ⟨K, hK⟩ := (hD R.params R.coupling n).2
  rw [configurationTotal_eq hD hrow hb hh]
  have hbound : ∀ p : TorusField (n * R.params.side) × (Yt → R.labels.Ω),
      ∫⁻ V, ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.1 b V) * h Yt b V p.1 p.2 ∂(fieldHaar n) ≤
        ‖gt Yt p‖ₑ * (ENNReal.ofReal K * c) := by
    intro p
    have h1 : ∀ V, ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.1 b V) * h Yt b V p.1 p.2 ≤ ‖gt Yt p‖ₑ * (ENNReal.ofReal K * c) := by
      intro V
      calc ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.1 b V) * h Yt b V p.1 p.2
          ≤ ENNReal.ofReal K * (‖gt Yt p‖ₑ * c) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (hK p.1 b V).2) (hle V p.1 p.2)
        _ = ‖gt Yt p‖ₑ * (ENNReal.ofReal K * c) := by ring
    calc _ ≤ ∫⁻ _, ‖gt Yt p‖ₑ * (ENNReal.ofReal K * c) ∂(fieldHaar n) := lintegral_mono h1
      _ = _ := by simp
  have hfin : ENNReal.ofReal K * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
  rw [lintegral_mul_const' _ _ hfin]
  exact ENNReal.mul_ne_top hi.2.ne hfin
private theorem stateIntegralSum_eq_parts (hD : StepTransitionDensityBounds) (hk : BondKernelProperties) (hrow : R.HasExpansions)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (hfin : ∀ Yt : Finset (TorusSite (n * R.params.side)), IsFiniteMeasure (stateMeasure R (n * R.params.side) Yt))
    {gt : LowerStateFunction R n} {ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ}
    (hgt : ∀ Yt, Measurable (gt Yt)) (hi : ∀ Yt, Integrable (gt Yt) (stateMeasure R (n * R.params.side) Yt))
    (hψ : ∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => ψ p.1 b p.2) {Cψ : ℝ} (hC : ∀ W b V, |ψ W b V| ≤ Cψ) :
    (∀ Yt b, configurationTotal (positivePart gt ψ) Yt b ≠ ⊤) ∧ (∀ Yt b, configurationTotal (negativePart gt ψ) Yt b ≠ ⊤) ∧
    stateIntegralSum R (n * R.params.side) (fun W Yt ωt => gt Yt (W, ωt) *
        ∑ b : BaseChoice R.params.side n, ∫ V, ψ W b V * stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n)) =
      (∑ Yt, ∑ b, configurationTotal (positivePart gt ψ) Yt b).toReal - (∑ Yt, ∑ b, configurationTotal (negativePart gt ψ) Yt b).toReal := by
  classical
  obtain ⟨hp, hn⟩ := measurable_parts hgt hψ
  have hfp : ∀ Yt b, configurationTotal (positivePart gt ψ) Yt b ≠ ⊤ := fun Yt b =>
    configurationTotal_ne_top hD hrow hb (hi Yt) hp b (c := ENNReal.ofReal Cψ) ENNReal.ofReal_ne_top
      fun V W ωt => ofReal_mul_le (hC W b V)
  have hfn : ∀ Yt b, configurationTotal (negativePart gt ψ) Yt b ≠ ⊤ := fun Yt b =>
    configurationTotal_ne_top hD hrow hb (hi Yt) hn b (c := ENNReal.ofReal Cψ) ENNReal.ofReal_ne_top
      fun V W ωt => by
        have := ofReal_mul_le (a := gt Yt (W, ωt)) (c := -ψ W b V) (d := Cψ) (by rw [abs_neg]; exact hC W b V)
        simpa [negativePart, mul_neg] using this
  refine ⟨hfp, hfn, ?_⟩
  have hone : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Integrable (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => gt Yt p * ∫ V, ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V ∂(fieldHaar n))
        (stateMeasure R (n * R.params.side) Yt) ∧
      ∫ p : TorusField (n * R.params.side) × (Yt → R.labels.Ω), gt Yt p * ∫ V, ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V ∂(fieldHaar n)
        ∂(stateMeasure R (n * R.params.side) Yt) =
        (configurationTotal (positivePart gt ψ) Yt b).toReal - (configurationTotal (negativePart gt ψ) Yt b).toReal := by
    intro Yt b
    have := hfin Yt
    have hu : Measurable fun x : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × TorusField n =>
        gt Yt x.1 * (ψ x.1.1 b x.2 * stepTransitionDensity R.params R.coupling x.1.1 b x.2) :=
      ((hgt Yt).comp measurable_fst).mul ((measurable_comp_pair_fst (κ := fun W V => ψ W b V) (hψ b)).mul
        (measurable_comp_pair_fst (κ := fun W V => stepTransitionDensity R.params R.coupling W b V) ((hD R.params R.coupling n).1 b)))
    have ep : ∫⁻ p, ∫⁻ V, ENNReal.ofReal (gt Yt p * (ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V)) ∂(fieldHaar n)
        ∂(stateMeasure R (n * R.params.side) Yt) = configurationTotal (positivePart gt ψ) Yt b := by
      rw [configurationTotal_eq hD hrow hb hp]
      refine lintegral_congr fun p => lintegral_congr fun V => ?_
      rw [← mul_assoc, ENNReal.ofReal_mul' (stepTransitionDensity_nonneg hk p.1 b V), mul_comm]
      rfl
    have en : ∫⁻ p, ∫⁻ V, ENNReal.ofReal (-(gt Yt p * (ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V))) ∂(fieldHaar n)
        ∂(stateMeasure R (n * R.params.side) Yt) = configurationTotal (negativePart gt ψ) Yt b := by
      rw [configurationTotal_eq hD hrow hb hn]
      refine lintegral_congr fun p => lintegral_congr fun V => ?_
      rw [← mul_assoc, ← neg_mul, ENNReal.ofReal_mul' (stepTransitionDensity_nonneg hk p.1 b V), mul_comm]
      rfl
    obtain ⟨h1, h2⟩ := integral_iterated_eq_posPart_sub_negPart (μ := stateMeasure R (n * R.params.side) Yt) (ν := fieldHaar n) hu
      (by rw [ep]; exact hfp Yt b) (by rw [en]; exact hfn Yt b)
    have hin : ∀ p : TorusField (n * R.params.side) × (Yt → R.labels.Ω), ∫ V, gt Yt p * (ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V) ∂(fieldHaar n) =
        gt Yt p * ∫ V, ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V ∂(fieldHaar n) := fun p => integral_const_mul _ _
    simp only [hin] at h1 h2
    rw [ep, en] at h2
    exact ⟨h1, h2⟩
  rw [toReal_sum_sum _ hfp, toReal_sum_sum _ hfn, ← Finset.sum_sub_distrib]
  unfold stateIntegralSum
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [← Finset.sum_sub_distrib]
  have e : ∀ p : TorusField (n * R.params.side) × (Yt → R.labels.Ω), gt Yt (p.1, p.2) *
      ∑ b : BaseChoice R.params.side n, ∫ V, ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V ∂(fieldHaar n) =
      ∑ b : BaseChoice R.params.side n, gt Yt p * ∫ V, ψ p.1 b V * stepTransitionDensity R.params R.coupling p.1 b V ∂(fieldHaar n) :=
    fun p => Finset.mul_sum _ _ _
  simp_rw [e]
  rw [integral_finsetSum _ fun b _ => (hone Yt b).1]
  exact Finset.sum_congr rfl fun b _ => (hone Yt b).2
end Value
section Fibre
private theorem integral_indicator_term {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {S : Set (X × Y)} (hS : MeasurableSet S) {cw : X × Y → ℝ≥0∞} (hcw : Measurable cw)
    {sw vg Fv : X × Y → ℝ} (hvg : Measurable vg) {ind : X × Y → ℝ≥0∞} (hind : Measurable ind) {T : X → Y → ℝ}
    (hcw_eq : ∀ p ∈ S, cw p = ENNReal.ofReal (sw p)) (hsw : ∀ p ∈ S, 0 ≤ sw p)
    (hT1 : ∀ x y, (x, y) ∈ S → T x y = Fv (x, y) * sw (x, y)) (hT0 : ∀ x y, (x, y) ∉ S → T x y = 0)
    (hF : ∀ p, ind p = 0 → Fv p = vg p)
    (hz : ∫⁻ x, ∫⁻ y, S.indicator (fun p => cw p * ind p) (x, y) ∂ν ∂μ = 0)
    (hp : ∫⁻ x, ∫⁻ y, S.indicator (fun p => cw p * ENNReal.ofReal (vg p)) (x, y) ∂ν ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ∫⁻ y, S.indicator (fun p => cw p * ENNReal.ofReal (-vg p)) (x, y) ∂ν ∂μ ≠ ⊤) :
    ∫ x, ∫ y, T x y ∂ν ∂μ = (∫⁻ x, ∫⁻ y, S.indicator (fun p => cw p * ENNReal.ofReal (vg p)) (x, y) ∂ν ∂μ).toReal -
      (∫⁻ x, ∫⁻ y, S.indicator (fun p => cw p * ENNReal.ofReal (-vg p)) (x, y) ∂ν ∂μ).toReal := by
  classical
  have htr : ∀ p ∈ S, (cw p).toReal = sw p := fun p hp' => by
    rw [hcw_eq p hp', ENNReal.toReal_ofReal (hsw p hp')]
  have hum : Measurable (S.indicator fun p => vg p * (cw p).toReal) :=
    (hvg.mul (ENNReal.measurable_toReal.comp hcw)).indicator hS
  have ep : ∀ p, ENNReal.ofReal (S.indicator (fun p => vg p * (cw p).toReal) p) =
      S.indicator (fun p => cw p * ENNReal.ofReal (vg p)) p := by
    intro p
    by_cases h : p ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, htr p h, ENNReal.ofReal_mul' (hsw p h), hcw_eq p h, mul_comm]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  have en : ∀ p, ENNReal.ofReal (-S.indicator (fun p => vg p * (cw p).toReal) p) =
      S.indicator (fun p => cw p * ENNReal.ofReal (-vg p)) p := by
    intro p
    by_cases h : p ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, htr p h, ← neg_mul, ENNReal.ofReal_mul' (hsw p h), hcw_eq p h, mul_comm]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  simp_rw [← ep, ← en] at hp hn ⊢
  rw [← (integral_iterated_eq_posPart_sub_negPart hum hp hn).2]
  have hm : Measurable (S.indicator fun p => cw p * ind p) := (hcw.mul hind).indicator hS
  have hW := (lintegral_eq_zero_iff (hm.lintegral_prod_right' (ν := ν))).mp hz
  refine integral_congr_ae ?_
  filter_upwards [hW] with x hx
  have hy := (lintegral_eq_zero_iff (hm.comp measurable_prodMk_left)).mp hx
  refine integral_congr_ae ?_
  filter_upwards [hy] with y hyz
  have hmz : S.indicator (fun p => cw p * ind p) (x, y) = 0 := hyz
  by_cases h : (x, y) ∈ S
  · rw [hT1 x y h, Set.indicator_of_mem h, htr _ h]
    rw [Set.indicator_of_mem h] at hmz
    rcases mul_eq_zero.mp hmz with h0 | h0
    · have h1 : sw (x, y) = 0 := by
        have h2 := htr _ h
        rw [h0] at h2
        simpa using h2.symm
      rw [h1, mul_zero, mul_zero]
    · rw [hF _ h0]
  · rw [hT0 x y h, Set.indicator_of_notMem h]
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem configurationMassWith_eq (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) (f : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞) :
    configurationMassWith R C V bad Yt b f q = ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      Set.indicator {p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) | IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt ∧
        coarseStateOf R C (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b = q}
        (fun p => configurationWeight R C V bad Yt b (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2) *
          f (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2)) (W, ν)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  unfold configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  by_cases hp : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · rw [if_pos hp, Set.indicator_of_mem (show (W, ν) ∈ _ from hp)]
    simp only [configurationWeight, if_pos hp.1]
  · rw [if_neg hp, Set.indicator_of_notMem (show (W, ν) ∉ _ from hp)]
private theorem integral_caseTerm (hR : R.IsWellPosed) (hk : BondKernelProperties) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n)
    (hw : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => configurationWeight R C V bad Yt b p.1 p.2)
    (hS : MeasurableSet {p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) | IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b = q})
    (hfo : Measurable fun W : TorusField (n * R.params.side) => q.fieldWithStoredLinks W)
    (hlo : Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν)
    (F : CaseFunction R n) (gt : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ) (hgt : Measurable gt)
    (ψ₀ : TorusField (n * R.params.side) → ℝ) (hψ : Measurable ψ₀)
    (N : Set (TorusField (n * R.params.side) × (Yt → R.labels.Ω))) (hN : MeasurableSet N)
    (hF : ∀ (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω), (W, ωt) ∉ N → F W Yt ωt bad b = gt (W, ωt) * ψ₀ W)
    (hnull : configurationMassWith R C V bad Yt b (fun W ωt => N.indicator 1 (W, ωt)) q = 0)
    (hfp : configurationMassWith R C V bad Yt b (fun W ωt => ENNReal.ofReal (gt (W, ωt) * ψ₀ W)) q ≠ ⊤)
    (hfn : configurationMassWith R C V bad Yt b (fun W ωt => ENNReal.ofReal (-(gt (W, ωt) * ψ₀ W))) q ≠ ⊤) :
    ∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      (configurationMassWith R C V bad Yt b (fun W ωt => ENNReal.ofReal (gt (W, ωt) * ψ₀ W)) q).toReal -
        (configurationMassWith R C V bad Yt b (fun W ωt => ENNReal.ofReal (-(gt (W, ωt) * ψ₀ W))) q).toReal := by
  classical
  have hfoP : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => q.fieldWithStoredLinks p.1 := hfo.comp measurable_fst
  have hloP : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => q.fillLabels Yt p.2 := hlo.comp measurable_snd
  have hpair : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) :=
    hfoP.prodMk hloP
  have hcw0 := hw.comp hpair
  have hcw : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2) := hcw0
  have hvg : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      gt (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) * ψ₀ (q.fieldWithStoredLinks p.1) := (hgt.comp hpair).mul (hψ.comp hfoP)
  have hind : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      N.indicator (1 : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞) (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) :=
    (measurable_one.indicator hN).comp hpair
  rw [configurationMassWith_eq] at hnull hfp hfn ⊢
  rw [configurationMassWith_eq]
  exact integral_indicator_term (sw := fun p => stepWeight R C V (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b)
    (Fv := fun p => F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b) hS hcw hvg hind
    (fun p hp => if_pos hp.1) (fun p hp => stepWeight_nonneg hR hk hb C V hp.1 _ _ _)
    (fun W ν hp => if_pos (show _ ∧ _ from hp)) (fun W ν hp => if_neg (show ¬ (_ ∧ _) from hp))
    (fun p h0 => hF _ _ fun hin => by
      have h1 : N.indicator (1 : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞) (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) = 1 :=
        Set.indicator_of_mem hin _
      rw [h1] at h0
      exact one_ne_zero h0) hnull hfp hfn
end Fibre
section Above
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def unitFamily (R : StepSetup) (n : ℕ) : ConfigurationFamily R n := fun _ _ _ _ _ => 1
private theorem measurable_unitFamily : IsMeasurableFamily (unitFamily R n) := fun _ _ => measurable_const
private theorem coarseStateMass_eq (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩ = configurationSum (unitFamily R n) V Y ω := by
  classical
  unfold coarseStateMass configurationSum configurationMassWith unitFamily
  simp only [mul_one]
private theorem coarseWeightExpansion_eq (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseWeightExpansion R n V Y ω = (configurationSum (unitFamily R n) V Y ω).toReal := by
  unfold coarseWeightExpansion
  rw [dif_neg (NeZero.ne n)]
  show (coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩).toReal = _
  rw [coarseStateMass_eq]
private def upperDensity (R : StepSetup) (n : ℕ) [NeZero n] (Y : Finset (TorusSite n)) (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) : ℝ≥0∞ :=
  open Classical in if IsHullState R.params R.nextRange p.1 Y then ENNReal.ofReal (coarseWeightExpansion R n p.1 Y p.2) else 0
private theorem upperDensity_eq (Y : Finset (TorusSite n)) (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) :
    upperDensity R n Y p = ENNReal.ofReal (hullConfigurationSum (unitFamily R n) Y p).toReal := by
  classical
  unfold upperDensity hullConfigurationSum
  by_cases hy : IsHullState R.params R.nextRange p.1 Y
  · simp only [if_pos hy, coarseWeightExpansion_eq]
  · simp only [if_neg hy, ENNReal.toReal_zero, ENNReal.ofReal_zero]
private theorem stateMeasure_next (h : CoarseLabelFacts R) (lam x'' : ℝ) (Y : Finset (TorusSite n)) :
    stateMeasure (nextStepSetup R h lam x'') n Y =
      ((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)).withDensity (upperDensity R n Y) := rfl
private theorem configurationSum_eq_zero (hC : ConfigurationMassWithFunction) (hR : R.IsWellPosed) (hn₀ : R.params.n₀ ≤ n)
    {f : ConfigurationFamily R n} (hh : IsMeasurableFamily f) (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side)
    (h0 : configurationSum (unitFamily R n) V Y ω = 0) : configurationSum f V Y ω = 0 := by
  classical
  unfold configurationSum at h0 ⊢
  refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
  have h1 := Finset.sum_eq_zero_iff.mp h0 bad hbad
  have h2 := Finset.sum_eq_zero_iff.mp h1 Yt (Finset.mem_univ _)
  have h3 := Finset.sum_eq_zero_iff.mp h2 b (Finset.mem_univ _)
  have h4 : configurationMass R (hotCoreSites R V) V bad Yt b ⟨Y, ω⟩ = 0 := by
    rw [← h3]
    unfold configurationMass configurationMassWith unitFamily
    simp only [mul_one]
  exact (hC R hR n hn₀ _ V bad Yt b (f Yt b V) (measurable_family_section hh Yt b V)).2.1 _ h4
private theorem configurationMassWith_le {f : ConfigurationFamily R n} (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side)
    {bad : Finset (TorusBond (n * R.params.side))} (hbad : bad ∈ (markedBonds R (hotCoreSites R V)).powerset)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    configurationMassWith R (hotCoreSites R V) V bad Yt b (f Yt b V) ⟨Y, ω⟩ ≤ configurationSum f V Y ω := by
  classical
  unfold configurationSum
  calc configurationMassWith R (hotCoreSites R V) V bad Yt b (f Yt b V) ⟨Y, ω⟩
      ≤ ∑ b' : BaseChoice R.params.side n, configurationMassWith R (hotCoreSites R V) V bad Yt b' (f Yt b' V) ⟨Y, ω⟩ :=
        Finset.single_le_sum (f := fun b' : BaseChoice R.params.side n => configurationMassWith R (hotCoreSites R V) V bad Yt b' (f Yt b' V) ⟨Y, ω⟩)
          (fun _ _ => zero_le) (Finset.mem_univ b)
    _ ≤ ∑ Yt' : Finset (TorusSite (n * R.params.side)), ∑ b' : BaseChoice R.params.side n,
          configurationMassWith R (hotCoreSites R V) V bad Yt' b' (f Yt' b' V) ⟨Y, ω⟩ :=
        Finset.single_le_sum (f := fun Yt' : Finset (TorusSite (n * R.params.side)) => ∑ b' : BaseChoice R.params.side n,
          configurationMassWith R (hotCoreSites R V) V bad Yt' b' (f Yt' b' V) ⟨Y, ω⟩) (fun _ _ => zero_le) (Finset.mem_univ Yt)
    _ ≤ _ := Finset.single_le_sum (f := fun bad' : Finset (TorusBond (n * R.params.side)) => ∑ Yt' : Finset (TorusSite (n * R.params.side)),
          ∑ b' : BaseChoice R.params.side n, configurationMassWith R (hotCoreSites R V) V bad' Yt' b' (f Yt' b' V) ⟨Y, ω⟩)
        (fun _ _ => zero_le) hbad
private theorem hullConfigurationSum_eq_zero (hC : ConfigurationMassWithFunction) (hR : R.IsWellPosed) (hn₀ : R.params.n₀ ≤ n)
    {f : ConfigurationFamily R n} (hh : IsMeasurableFamily f) (Y : Finset (TorusSite n)) (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side))
    (h1 : hullConfigurationSum (unitFamily R n) Y p < ⊤) (hd : upperDensity R n Y p = 0) : hullConfigurationSum f Y p = 0 := by
  classical
  by_cases hy : IsHullState R.params R.nextRange p.1 Y
  · rw [upperDensity_eq, ENNReal.ofReal_eq_zero] at hd
    have h2 : hullConfigurationSum (unitFamily R n) Y p = 0 := by
      have := ENNReal.toReal_nonneg (a := hullConfigurationSum (unitFamily R n) Y p)
      have h3 : (hullConfigurationSum (unitFamily R n) Y p).toReal = 0 := le_antisymm hd this
      rcases (ENNReal.toReal_eq_zero_iff _).mp h3 with h4 | h4
      · exact h4
      · exact absurd h4 h1.ne
    have h3 : configurationSum (unitFamily R n) p.1 Y p.2 = 0 := by
      rw [← h2]
      exact (if_pos hy).symm
    show (if IsHullState R.params R.nextRange p.1 Y then configurationSum f p.1 Y p.2 else 0) = 0
    rw [if_pos hy]
    exact configurationSum_eq_zero hC hR hn₀ hh _ _ _ h3
  · exact if_neg hy
private theorem upperDensity_toReal (Y : Finset (TorusSite n)) (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) :
    (upperDensity R n Y p).toReal = (hullConfigurationSum (unitFamily R n) Y p).toReal := by
  rw [upperDensity_eq, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
private theorem conditionalCaseMean_on_set (hC : ConfigurationMassWithFunction) (hw : ConfigurationWeightMeasurable)
    (hk : BondKernelProperties) (hR : R.IsWellPosed) (hb : IsBlockTorusSide R.params (n * R.params.side)) (hn₀ : R.params.n₀ ≤ n)
    (hLo : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (q : CoarseState R n),
      Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν)
    (hTest : ∀ (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (q : CoarseState R n),
      MeasurableSet {p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) | IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt ∧
        coarseStateOf R C (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b = q})
    (Y : Finset (TorusSite n)) {lam : Measure (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side))}
    {g : StateFunction R (n * R.params.side)} {gt : LowerStateFunction R n} (hgt : ∀ Yt, Measurable (gt Yt))
    {ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ}
    (hψ : ∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => ψ p.1 b p.2)
    (N : (Yt : Finset (TorusSite (n * R.params.side))) → Set (TorusField (n * R.params.side) × (Yt → R.labels.Ω))) (hN : ∀ Yt, MeasurableSet (N Yt))
    (hgN : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω), (W, ωt) ∉ N Yt → g W Yt ωt = gt Yt (W, ωt))
    (hd : Measurable (upperDensity R n Y))
    (hp : IsMeasurableFamily (positivePart gt ψ)) (hn : IsMeasurableFamily (negativePart gt ψ))
    (hM1 : Measurable (hullConfigurationSum (unitFamily R n) Y)) (hMp : Measurable (hullConfigurationSum (positivePart gt ψ) Y))
    (hMn : Measurable (hullConfigurationSum (negativePart gt ψ) Y))
    (hf1 : ∫⁻ p, hullConfigurationSum (unitFamily R n) Y p ∂lam ≠ ⊤) (hfp : ∫⁻ p, hullConfigurationSum (positivePart gt ψ) Y p ∂lam ≠ ⊤)
    (hfn : ∫⁻ p, hullConfigurationSum (negativePart gt ψ) Y p ∂lam ≠ ⊤)
    (hnull : ∀ᵐ p ∂lam, hullConfigurationSum (fun Yt _ _ W ωt => (N Yt).indicator 1 (W, ωt) : ConfigurationFamily R n) Y p = 0) :
    Integrable (fun p => conditionalCaseMean R g ψ p.1 Y p.2) (lam.withDensity (upperDensity R n Y)) ∧
      ∫ p, conditionalCaseMean R g ψ p.1 Y p.2 ∂(lam.withDensity (upperDensity R n Y)) =
        (∫⁻ p, hullConfigurationSum (positivePart gt ψ) Y p ∂lam).toReal - (∫⁻ p, hullConfigurationSum (negativePart gt ψ) Y p ∂lam).toReal := by
  classical
  have h1 := ae_lt_top hM1 hf1
  have h2 := ae_lt_top hMp hfp
  have h3 := ae_lt_top hMn hfn
  refine withDensity_integral_of_quotient hd (fun p => by rw [upperDensity_eq]; exact ENNReal.ofReal_ne_top) hMp hMn hfp hfn ?_ ?_
  · filter_upwards [h1] with p hp1 hd0
    exact ⟨hullConfigurationSum_eq_zero hC hR hn₀ hp Y p hp1 hd0, hullConfigurationSum_eq_zero hC hR hn₀ hn Y p hp1 hd0⟩
  · filter_upwards [h2, h3, hnull] with p hpp hpn hpz hd0
    obtain ⟨V, ω⟩ := p
    have hy : IsHullState R.params R.nextRange V Y := by
      by_contra hy
      exact hd0 (if_neg hy)
    have eall : ∀ f : ConfigurationFamily R n, hullConfigurationSum f Y (V, ω) = configurationSum f V Y ω := fun f => if_pos hy
    rw [eall] at hpp hpn hpz
    rw [eall, eall, upperDensity_toReal, eall]
    have hfo0 := (measurable_fieldWithStoredLinks (R := R) Y).comp
      (measurable_const.prodMk measurable_id : Measurable fun W : TorusField (n * R.params.side) => (ω, W))
    have hterm : ∀ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω⟩ : CoarseState R n) Yt → R.labels.Ω,
          caseTerm R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ b => g W Yt ωt * ψ W b V) bad Yt b W ν
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        (configurationMassWith R (hotCoreSites R V) V bad Yt b (positivePart gt ψ Yt b V) ⟨Y, ω⟩).toReal -
          (configurationMassWith R (hotCoreSites R V) V bad Yt b (negativePart gt ψ Yt b V) ⟨Y, ω⟩).toReal := by
      intro bad hbad Yt b
      have hψs : Measurable fun W : TorusField (n * R.params.side) => ψ W b V := (hψ b).comp measurable_prodMk_right
      refine integral_caseTerm hR hk hb (hotCoreSites R V) V bad Yt b ⟨Y, ω⟩ (hw R hR n hn₀ _ V bad Yt b) (hTest _ bad Yt b _) hfo0
        (hLo Yt _) _ (gt Yt) (hgt Yt) (fun W => ψ W b V) hψs (N Yt) (hN Yt)
        (fun W ωt hno => by
          show g W Yt ωt * ψ W b V = _
          rw [hgN Yt W ωt hno]) ?_ ?_ ?_
      · exact le_antisymm ((configurationMassWith_le (f := fun Yt _ _ W ωt => (N Yt).indicator 1 (W, ωt)) V Y ω hbad Yt b).trans hpz.le) zero_le
      · exact ne_top_of_le_ne_top hpp.ne (configurationMassWith_le (f := positivePart gt ψ) V Y ω hbad Yt b)
      · exact ne_top_of_le_ne_top hpn.ne (configurationMassWith_le (f := negativePart gt ψ) V Y ω hbad Yt b)
    have hnum : caseIntegral R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ b => g W Yt ωt * ψ W b V) =
        (configurationSum (positivePart gt ψ) V Y ω).toReal - (configurationSum (negativePart gt ψ) V Y ω).toReal := by
      unfold caseIntegral
      rw [Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ =>
        hterm bad hbad Yt b]
      simp only [Finset.sum_sub_distrib]
      unfold configurationSum
      rw [toReal_sum_sum_sum _ _ hpp.ne, toReal_sum_sum_sum _ _ hpn.ne]
    show caseIntegral R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ b => g W Yt ωt * ψ W b V) /
      (coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩).toReal = _
    rw [hnum, coarseStateMass_eq]
end Above
theorem stepMeanOfStatesStatement_holds (hC : ConfigurationMassWithFunction) (hB : ConfigurationMassMeasurability)
    (hH : CoarseHullIsHullState) (hw : ConfigurationWeightMeasurable) (hk : BondKernelProperties)
    (hD : StepTransitionDensityBounds) (hS : ScoreProductStepMean) : stepMeanOfStatesStatement := by
  classical
  intro T hT
  refine ⟨0, fun y _ R hOn hR h lam x'' n _ hside hfin => ?_⟩
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hside.2
  have hb : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have : SigmaFinite (coarseLabelMeasure R.labels.μ R.params.side) := h.sigmaFinite
  obtain ⟨hCset, hHull, hLo, hCM, hTest⟩ := hB T hT y R hOn hR n hside
  have hHS : ∀ {f : ConfigurationFamily R n}, IsMeasurableFamily f → ∀ Y, Measurable (hullConfigurationSum f Y) :=
    fun hf Y => measurable_hullConfigurationSum hCset hHull hCM hf Y
  have hTot : ∀ {f : ConfigurationFamily R n}, IsMeasurableFamily f →
      ∑ Y : Finset (TorusSite n), ∫⁻ p, hullConfigurationSum f Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
        ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, configurationTotal f Yt b :=
    fun hf => sum_lintegral_hullConfigurationSum hC hH hw hk hD hR hside hb hn₀ hf (hHS hf)
  have hfinY : ∀ {f : ConfigurationFamily R n}, IsMeasurableFamily f → (∀ Yt b, configurationTotal f Yt b ≠ ⊤) → ∀ Y : Finset (TorusSite n),
      ∫⁻ p, hullConfigurationSum f Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) ≠ ⊤ := by
    intro f hf ht Y
    have h1 : ∑ Y : Finset (TorusSite n), ∫⁻ p, hullConfigurationSum f Y p
        ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) ≠ ⊤ := by
      rw [hTot hf]
      exact ENNReal.sum_ne_top.mpr fun Yt _ => ENNReal.sum_ne_top.mpr fun b _ => ht Yt b
    exact ENNReal.sum_ne_top.mp h1 Y (Finset.mem_univ Y)
  have hdm : ∀ Y : Finset (TorusSite n), Measurable (upperDensity R n Y) := by
    intro Y
    have e : upperDensity R n Y = fun p => ENNReal.ofReal (hullConfigurationSum (unitFamily R n) Y p).toReal :=
      funext fun p => upperDensity_eq Y p
    rw [e]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hHS measurable_unitFamily Y))
  have hot : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n), configurationTotal (unitFamily R n) Yt b ≠ ⊤ := by
    intro Yt b
    have := hfin Yt
    exact configurationTotal_ne_top (gt := fun _ _ => 1) hD hR.hasExpansions hb (integrable_const _) measurable_unitFamily b (c := 1) ENNReal.one_ne_top
      fun V W ωt => by simp [unitFamily]
  have hf1 := hfinY measurable_unitFamily hot
  have hfa : ∀ Y : Finset (TorusSite n), IsFiniteMeasure (stateMeasure (nextStepSetup R h lam x'') n Y) := by
    intro Y
    have hle : ∫⁻ p, upperDensity R n Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) ≤
        ∫⁻ p, hullConfigurationSum (unitFamily R n) Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) :=
      lintegral_mono fun p => by
        rw [upperDensity_eq]
        exact ENNReal.ofReal_toReal_le
    rw [stateMeasure_next]
    exact isFiniteMeasure_withDensity (ne_top_of_le_ne_top (hf1 Y) hle)
  have hψ1 : ∀ b : BaseChoice R.params.side n, Measurable fun p : TorusField (n * R.params.side) × TorusField n => (fun _ _ _ => 1 :
      TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) p.1 b p.2 := fun _ => measurable_const
  have hmass : ∀ Y : Finset (TorusSite n), ∫ p, (1 : ℝ) ∂(stateMeasure (nextStepSetup R h lam x'') n Y) =
      (∫⁻ p, hullConfigurationSum (unitFamily R n) Y p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))).toReal := by
    intro Y
    rw [stateMeasure_next]
    have hval := (withDensity_integral_of_quotient (H := fun _ => (1 : ℝ)) (An := fun _ => 0) (hdm Y)
      (fun p => by rw [upperDensity_eq]; exact ENNReal.ofReal_ne_top) (hHS measurable_unitFamily Y) measurable_const (hf1 Y) (by simp)
      (by
        filter_upwards [ae_lt_top (hHS measurable_unitFamily Y) (hf1 Y)] with p hp hd0
        exact ⟨hullConfigurationSum_eq_zero hC hR hn₀ measurable_unitFamily Y p hp hd0, rfl⟩)
      (Filter.Eventually.of_forall fun p hd0 => by
        have h1 : (upperDensity R n Y p).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hd0, by
          rw [upperDensity_eq]; exact ENNReal.ofReal_ne_top⟩
        rw [← upperDensity_toReal]
        simp only [ENNReal.toReal_zero, sub_zero]
        exact (div_self h1).symm)).2
    refine hval.trans ?_
    simp
  refine ⟨hfa, ?_, fun g ψ hg hψ hψb => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := stateIntegralSum_eq_parts (gt := fun _ _ => 1) (ψ := fun _ _ _ => 1) hD hk hR.hasExpansions hb hfin
      (fun _ => measurable_const) (fun Yt => by have := hfin Yt; exact integrable_const _) hψ1
      (Cψ := 1) (fun _ _ _ => by simp)
    have hpos : positivePart (R := R) (n := n) (fun _ _ => 1) (fun _ _ _ => 1) = unitFamily R n := by
      funext Yt b V W ωt
      simp [positivePart, unitFamily]
    have hneg : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        configurationTotal (negativePart (R := R) (n := n) (fun _ _ => 1) (fun _ _ _ => 1)) Yt b = 0 := by
      intro Yt b
      have h0 : ENNReal.ofReal (-1 : ℝ) = 0 := ENNReal.ofReal_of_nonpos (by norm_num)
      unfold configurationTotal negativePart
      simp [h0]
    have hunit : ∀ W : TorusField (n * R.params.side), ∑ b : BaseChoice R.params.side n, ∫ V, (1 : ℝ) * stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n) = 1 := by
      intro W
      have := hS R.params hR.admissible hR.admissible.depth_lt R.coupling n W 0 (fun k => k.elim0) (fun k => k.elim0) (fun c k => k.elim0)
      simpa using this
    simp only [hunit, mul_one, hpos, hneg, Finset.sum_const_zero, ENNReal.toReal_zero, sub_zero] at h3
    rw [h3, ← hTot measurable_unitFamily, ENNReal.toReal_sum fun Y _ => hf1 Y]
    unfold stateIntegralSum
    exact Finset.sum_congr rfl fun Y _ => hmass Y
  · obtain ⟨Cψ, hCψ⟩ := hψb
    set gt : LowerStateFunction R n := fun Yt => (hg Yt).1.mk _ with hgtdef
    have hgt : ∀ Yt, Measurable (gt Yt) := fun Yt => (hg Yt).1.stronglyMeasurable_mk.measurable
    have hae : ∀ Yt : Finset (TorusSite (n * R.params.side)),
        (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => g p.1 Yt p.2) =ᵐ[stateMeasure R (n * R.params.side) Yt] gt Yt :=
      fun Yt => (hg Yt).1.ae_eq_mk
    have hi : ∀ Yt, Integrable (gt Yt) (stateMeasure R (n * R.params.side) Yt) := fun Yt => (hg Yt).congr (hae Yt)
    obtain ⟨hcp, hcn, hval⟩ := stateIntegralSum_eq_parts hD hk hR.hasExpansions hb hfin hgt hi hψ hCψ
    obtain ⟨hp, hn⟩ := measurable_parts hgt hψ
    let N : (Yt : Finset (TorusSite (n * R.params.side))) → Set (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) := fun Yt =>
      toMeasurable (stateMeasure R (n * R.params.side) Yt) {p | g p.1 Yt p.2 ≠ gt Yt p}
    have hN : ∀ Yt, MeasurableSet (N Yt) := fun Yt => measurableSet_toMeasurable _ _
    have hN0 : ∀ Yt, stateMeasure R (n * R.params.side) Yt (N Yt) = 0 := fun Yt => by
      show stateMeasure R (n * R.params.side) Yt (toMeasurable _ _) = 0
      rw [measure_toMeasurable]
      exact hae Yt
    have hgN : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω), (W, ωt) ∉ N Yt →
        g W Yt ωt = gt Yt (W, ωt) := by
      intro Yt W ωt hno
      by_contra hne
      exact hno (subset_toMeasurable _ _ hne)
    have hnb : IsMeasurableFamily (fun Yt _ _ W ωt => (N Yt).indicator 1 (W, ωt) : ConfigurationFamily R n) := fun Yt b =>
      (measurable_one.indicator (hN Yt)).comp measurable_snd
    have hnt : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        configurationTotal (fun Yt _ _ W ωt => (N Yt).indicator 1 (W, ωt) : ConfigurationFamily R n) Yt b = 0 := by
      intro Yt b
      rw [configurationTotal_eq hD hR.hasExpansions hb hnb]
      have hz : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => ∫⁻ V, ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.1 b V) *
          (N Yt).indicator 1 (p.1, p.2) ∂(fieldHaar n)) =ᵐ[stateMeasure R (n * R.params.side) Yt] 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN0 Yt)] with p hp'
        have : (N Yt).indicator (1 : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞) (p.1, p.2) = 0 :=
          Set.indicator_of_notMem hp' _
        simp [this]
      rw [lintegral_congr_ae hz]
      simp
    have hnull : ∀ Y : Finset (TorusSite n), ∀ᵐ p ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)),
        hullConfigurationSum (fun Yt _ _ W ωt => (N Yt).indicator 1 (W, ωt) : ConfigurationFamily R n) Y p = 0 := by
      intro Y
      have h0 := hTot hnb
      simp only [hnt, Finset.sum_const_zero] at h0
      have h1 := Finset.sum_eq_zero_iff.mp h0 Y (Finset.mem_univ _)
      exact (lintegral_eq_zero_iff (hHS hnb Y)).mp h1
    have hset : ∀ Y : Finset (TorusSite n), _ := fun Y => conditionalCaseMean_on_set hC hw hk hR hb hn₀ hLo hTest Y hgt hψ N hN hgN (hdm Y) hp hn
      (hHS measurable_unitFamily Y) (hHS hp Y) (hHS hn Y) (hf1 Y) (hfinY hp hcp Y) (hfinY hn hcn Y) (hnull Y)
    refine ⟨fun Y => ?_, ?_⟩
    · rw [stateMeasure_next]
      exact (hset Y).1
    · have hsum : stateIntegralSum (nextStepSetup R h lam x'') n (conditionalCaseMean R g ψ) =
          ∑ Y : Finset (TorusSite n), ((∫⁻ p, hullConfigurationSum (positivePart gt ψ) Y p
              ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))).toReal -
            (∫⁻ p, hullConfigurationSum (negativePart gt ψ) Y p
              ∂((fieldHaar n).prod (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))).toReal) := by
        unfold stateIntegralSum
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [stateMeasure_next]
        exact (hset Y).2
      rw [hsum, Finset.sum_sub_distrib, ← ENNReal.toReal_sum fun Y _ => hfinY hp hcp Y,
        ← ENNReal.toReal_sum fun Y _ => hfinY hn hcn Y, hTot hp, hTot hn, ← hval]
      unfold stateIntegralSum
      refine Finset.sum_congr rfl fun Yt _ => ?_
      refine integral_congr_ae ?_
      filter_upwards [hae Yt] with p hp'
      show gt Yt (p.1, p.2) * _ = g p.1 Yt p.2 * _
      rw [hp']
end StepMeanOfStates
end YangMills.Construction.ResponseInTheExpansion
end
