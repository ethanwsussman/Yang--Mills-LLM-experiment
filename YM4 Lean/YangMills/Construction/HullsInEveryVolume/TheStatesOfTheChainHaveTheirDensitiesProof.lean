import YangMills.Construction.HullsInEveryVolume.TheStatesOfTheChainHaveTheirDensities
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
section Terms
variable {E : Type} [MeasurableSpace E] (ν : Measure E)
private theorem integral_mul_eq_toReal_lintegral {h d : E → ℝ} (hh : Measurable h) (hd : Measurable d)
    (h0 : ∀ e, 0 ≤ h e) (d0 : ∀ e, 0 ≤ d e) :
    ∫ e, h e * d e ∂ν = (∫⁻ e, ENNReal.ofReal (h e) * ENNReal.ofReal (d e) ∂ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun e => mul_nonneg (h0 e) (d0 e))
    (hh.mul hd).aestronglyMeasurable]
  congr 1
  exact lintegral_congr fun e => ENNReal.ofReal_mul (h0 e)
private theorem lintegral_ofReal_mul_le {h d : E → ℝ} {C : ℝ} (hC : ∀ e, h e ≤ C) :
    ∫⁻ e, ENNReal.ofReal (h e) * ENNReal.ofReal (d e) ∂ν ≤ ENNReal.ofReal C * ∫⁻ e, ENNReal.ofReal (d e) ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun e => ?_
  gcongr
  exact hC e
private theorem integrable_mul_of_lintegral_ne_top {h d : E → ℝ} (hh : Measurable h) (hd : Measurable d)
    (h0 : ∀ e, 0 ≤ h e) (d0 : ∀ e, 0 ≤ d e)
    (hfin : ∫⁻ e, ENNReal.ofReal (h e) * ENNReal.ofReal (d e) ∂ν ≠ ⊤) :
    Integrable (fun e => h e * d e) ν := by
  refine ⟨(hh.mul hd).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun e => mul_nonneg (h0 e) (d0 e))]
  have e : ∫⁻ e, ENNReal.ofReal (h e * d e) ∂ν = ∫⁻ e, ENNReal.ofReal (h e) * ENNReal.ofReal (d e) ∂ν :=
    lintegral_congr fun e => ENNReal.ofReal_mul (h0 e)
  rw [e]
  exact hfin.lt_top
end Terms
section Sums
variable {X I S A : Type} [MeasurableSpace X] [Fintype I] {E : I → Type} [∀ i, MeasurableSpace (E i)]
  [MeasurableSpace S] [MeasurableSpace A]
open Classical in
private theorem nonneg_part_of_density (μ : Measure A) [IsProbabilityMeasure μ] {s : A → S} (hs : Measurable s)
    (lam : Measure X)
    (ν : ∀ i, Measure (E i)) [∀ i, SFinite (ν i)] (P : X → I → Prop) (d : ∀ i, X → E i → ℝ)
    (d0 : ∀ x i e, P x i → 0 ≤ d i x e)
    (dm : ∀ i, Measurable fun p : X × E i => if P p.1 i then d i p.1 p.2 else 0)
    (dfin : ∀ x, ∑ i ∈ Finset.univ.filter (P x), ∫⁻ e, ENNReal.ofReal (d i x e) ∂(ν i) ≠ ⊤)
    (mk : ∀ i, X → E i → S) (mkm : ∀ i, Measurable fun p : X × E i => mk i p.1 p.2)
    {Z : ℝ} (hZ : 0 < Z)
    (hden : ∀ G : S → ENNReal, Measurable G →
      ENNReal.ofReal Z * ∫⁻ a, G (s a) ∂μ =
        ∫⁻ x, ∑ i ∈ Finset.univ.filter (P x), ∫⁻ e, G (mk i x e) * ENNReal.ofReal (d i x e) ∂(ν i) ∂lam)
    {H : S → ℝ} (hH : Measurable H) (H0 : ∀ q, 0 ≤ H q) {C : ℝ} (hC : ∀ q, H q ≤ C) :
    (∀ x i, P x i → Integrable (fun e => H (mk i x e) * d i x e) (ν i)) ∧
    Integrable (fun x => ∑ i ∈ Finset.univ.filter (P x), ∫ e, H (mk i x e) * d i x e ∂(ν i)) lam ∧
    ∫ x, ∑ i ∈ Finset.univ.filter (P x), ∫ e, H (mk i x e) * d i x e ∂(ν i) ∂lam = Z * ∫ a, H (s a) ∂μ := by
  have hsec : ∀ x i, P x i → Measurable fun e => d i x e := fun x i hP => by
    have e : (fun e => d i x e) = fun e => (fun p : X × E i => if P p.1 i then d i p.1 p.2 else 0) (x, e) :=
      funext fun e => by simp [hP]
    rw [e]
    exact (dm i).comp measurable_prodMk_left
  have hHs : ∀ x i, Measurable fun e => H (mk i x e) := fun x i =>
    hH.comp ((mkm i).comp measurable_prodMk_left)
  set G : S → ENNReal := fun q => ENNReal.ofReal (H q) with hGdef
  have hG : Measurable G := hH.ennreal_ofReal
  set B : X → ENNReal := fun x =>
    ∑ i ∈ Finset.univ.filter (P x), ∫⁻ e, G (mk i x e) * ENNReal.ofReal (d i x e) ∂(ν i) with hBdef
  have hterm : ∀ x, ∀ i ∈ Finset.univ.filter (P x),
      ∫⁻ e, G (mk i x e) * ENNReal.ofReal (d i x e) ∂(ν i) ≠ ⊤ := fun x i hi => by
    have h1 : ∫⁻ e, ENNReal.ofReal (d i x e) ∂(ν i) ≠ ⊤ :=
      ne_top_of_le_ne_top (dfin x)
        (Finset.single_le_sum (f := fun i => ∫⁻ e, ENNReal.ofReal (d i x e) ∂(ν i)) (fun _ _ => zero_le) hi)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1)
      (lintegral_ofReal_mul_le (ν i) (h := fun e => H (mk i x e)) (d := d i x) fun e => hC _)
  have hBfin : ∀ x, B x ≠ ⊤ := fun x => ENNReal.sum_ne_top.2 (hterm x)
  have hBm : Measurable B := by
    have e : B = fun x => ∑ i : I, ∫⁻ e, (fun p : X × E i => G (mk i p.1 p.2) *
        ENNReal.ofReal (if P p.1 i then d i p.1 p.2 else 0)) (x, e) ∂(ν i) := by
      funext x
      simp only [hBdef]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hP : P x i
      · simp [hP]
      · simp [hP]
    rw [e]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.lintegral_prod_right' ((hG.comp (mkm i)).mul (dm i).ennreal_ofReal)
  have hreal : ∀ x, ∑ i ∈ Finset.univ.filter (P x), ∫ e, H (mk i x e) * d i x e ∂(ν i) = (B x).toReal := fun x => by
    simp only [hBdef]
    rw [ENNReal.toReal_sum (hterm x)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hP : P x i := (Finset.mem_filter.mp hi).2
    exact integral_mul_eq_toReal_lintegral (ν i) (hHs x i) (hsec x i hP) (fun e => H0 _) (fun e => d0 x i e hP)
  have hsfin : ∫⁻ a, G (s a) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) ?_
    calc ∫⁻ a, G (s a) ∂μ ≤ ∫⁻ _, ENNReal.ofReal C ∂μ := lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hC _)
      _ = ENNReal.ofReal C := by simp
  have hmass : ∫⁻ x, B x ∂lam = ENNReal.ofReal Z * ∫⁻ a, G (s a) ∂μ := (hden G hG).symm
  have hmassfin : ∫⁻ x, B x ∂lam ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsfin
  refine ⟨fun x i hP => ?_, ?_, ?_⟩
  · exact integrable_mul_of_lintegral_ne_top (ν i) (hHs x i) (hsec x i hP) (fun e => H0 _) (fun e => d0 x i e hP)
      (hterm x i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩))
  · simp_rw [hreal]
    exact integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hmassfin
  · simp_rw [hreal]
    rw [integral_toReal hBm.aemeasurable (Filter.Eventually.of_forall fun x => (hBfin x).lt_top), hmass,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hZ.le,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun a => H0 _)
        (hH.comp hs).aestronglyMeasurable]
open Classical in
private theorem integral_eq_of_density (μ : Measure A) [IsProbabilityMeasure μ] {s : A → S} (hs : Measurable s)
    (lam : Measure X)
    (ν : ∀ i, Measure (E i)) [∀ i, SFinite (ν i)] (P : X → I → Prop) (d : ∀ i, X → E i → ℝ)
    (d0 : ∀ x i e, P x i → 0 ≤ d i x e)
    (dm : ∀ i, Measurable fun p : X × E i => if P p.1 i then d i p.1 p.2 else 0)
    (dfin : ∀ x, ∑ i ∈ Finset.univ.filter (P x), ∫⁻ e, ENNReal.ofReal (d i x e) ∂(ν i) ≠ ⊤)
    (mk : ∀ i, X → E i → S) (mkm : ∀ i, Measurable fun p : X × E i => mk i p.1 p.2)
    {Z : ℝ} (hZ : 0 < Z)
    (hden : ∀ G : S → ENNReal, Measurable G →
      ENNReal.ofReal Z * ∫⁻ a, G (s a) ∂μ =
        ∫⁻ x, ∑ i ∈ Finset.univ.filter (P x), ∫⁻ e, G (mk i x e) * ENNReal.ofReal (d i x e) ∂(ν i) ∂lam)
    {F : S → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ q, |F q| ≤ C) :
    ∫ a, F (s a) ∂μ =
      (∫ x, ∑ i ∈ Finset.univ.filter (P x), ∫ e, F (mk i x e) * d i x e ∂(ν i) ∂lam) / Z := by
  set Hp : S → ℝ := fun q => max (F q) 0 with hHp
  set Hm : S → ℝ := fun q => max (-F q) 0 with hHm
  have hsplit : ∀ q, F q = Hp q - Hm q := fun q => by
    simp only [hHp, hHm]
    rcases le_total 0 (F q) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  have hp0 : ∀ q, 0 ≤ Hp q := fun q => le_max_right _ _
  have hm0 : ∀ q, 0 ≤ Hm q := fun q => le_max_right _ _
  have hpC : ∀ q, Hp q ≤ max C 0 := fun q => max_le_max (((le_abs_self _).trans (hC q))) le_rfl
  have hmC : ∀ q, Hm q ≤ max C 0 := fun q => max_le_max (((neg_le_abs _).trans (hC q))) le_rfl
  have hpm : Measurable Hp := hF.max measurable_const
  have hmm : Measurable Hm := hF.neg.max measurable_const
  obtain ⟨ip, jp, ep⟩ := nonneg_part_of_density μ hs lam ν P d d0 dm dfin mk mkm hZ hden hpm hp0 hpC
  obtain ⟨im, jm, em⟩ := nonneg_part_of_density μ hs lam ν P d d0 dm dfin mk mkm hZ hden hmm hm0 hmC
  have hbd : ∀ {H : S → ℝ}, Measurable H → (∀ q, 0 ≤ H q) → (∀ q, H q ≤ max C 0) →
      Integrable (fun a => H (s a)) μ :=
    fun {H} hH h0 h1 => Integrable.of_bound (hH.comp hs).aestronglyMeasurable (max C 0)
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
        exact h1 _)
  have hin : ∀ x, ∑ i ∈ Finset.univ.filter (P x), ∫ e, F (mk i x e) * d i x e ∂(ν i) =
      ∑ i ∈ Finset.univ.filter (P x), ∫ e, Hp (mk i x e) * d i x e ∂(ν i) -
        ∑ i ∈ Finset.univ.filter (P x), ∫ e, Hm (mk i x e) * d i x e ∂(ν i) := fun x => by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hP : P x i := (Finset.mem_filter.mp hi).2
    rw [← integral_sub (ip x i hP) (im x i hP)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
    show F (mk i x e) * d i x e = Hp (mk i x e) * d i x e - Hm (mk i x e) * d i x e
    rw [hsplit (mk i x e)]
    ring
  have hout : ∫ x, ∑ i ∈ Finset.univ.filter (P x), ∫ e, F (mk i x e) * d i x e ∂(ν i) ∂lam =
      Z * ∫ a, Hp (s a) ∂μ - Z * ∫ a, Hm (s a) ∂μ := by
    rw [← ep, ← em, ← integral_sub jp jm]
    exact integral_congr_ae (Filter.Eventually.of_forall hin)
  have hmean : ∫ a, F (s a) ∂μ = ∫ a, Hp (s a) ∂μ - ∫ a, Hm (s a) ∂μ := by
    rw [← integral_sub (hbd hpm hp0 hpC) (hbd hmm hm0 hmC)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => hsplit (s a))
  rw [hout, hmean]
  field_simp
end Sums
section Flow
variable {ℓ : TorusLumps.StepParameters}
private theorem isBlockTorusSide_fineSide (ℓ : TorusLumps.StepParameters) (s : ℕ) {n : ℕ}
    (h : IsBlockTorusSide ℓ n) : IsBlockTorusSide ℓ (fineSide ℓ.side s n) := by
  have hL : 0 < ℓ.side ^ s := pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _
  rw [fineSide_eq]
  exact ⟨Dvd.dvd.mul_right h.1 _, h.2.trans (Nat.le_mul_of_pos_right _ hL)⟩
end Flow
section Table
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem isBlockTorusSide_top (hT : Tb.Admissible) {m : ℕ} (hv : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m) :
    IsBlockTorusSide (Tb.stepParameters y) (2 * Tb.side ^ m) := by
  refine ⟨?_, hv⟩
  cases m with
  | zero =>
    have h1 : 2 ^ 40 ≤ Tb.side := hT.L_ge
    have h2 : 4096 ≤ Tb.n₀ := hT.n₀_ge
    have h3 : 2 ^ 40 * 4096 ≤ Tb.side * Tb.n₀ := Nat.mul_le_mul h1 h2
    simp only [pow_zero, mul_one] at hv
    omega
  | succ k => exact ⟨2 * Tb.side ^ k, by show 2 * Tb.side ^ (k + 1) = Tb.side * (2 * Tb.side ^ k); ring⟩
end Table
private theorem measurable_sigmaMk {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  measurable_iff_le_map.2 (iInf_le _ a)
theorem stageStateDensityStatement_holds (hD : StageDensity.stageStateDensityStatement)
    (hBor : ResponseInTheExpansion.StageStatesMeasurableStatement) (hLaw : ChainIsProbabilityLaw)
    (hDraw : forgetLastStepStatement) : HullTrees.stageStateDensityStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, hA⟩ := hD a ha
  refine ⟨L₀, rt₀, 0, hrt, fun L hodd hL₀ Tb hTa hTL hT _ _ hrtT _ => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hA L hodd hL₀ Tb hTa hTL hT hrtT
  refine ⟨0, fun Kr _ _ _ _ _ => ⟨max y₀ Tb.floorMin, fun y hy hret hwil => ?_⟩⟩
  intro g β K m T u n _ hat F hF hbd
  have h1 : y₀ ≤ y := le_trans (le_max_left _ _) hy
  have h3 : Tb.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hfit : (Tb.stepParameters y).Admissible := hT.fits y h3
  have hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hT.L_gt
  have hu : u ≤ K := hat.le
  have hflow := hat.chain.reads_flow.toIsTowerAtParameters
  have htower : ResponseInTheExpansion.IsTowerAtParameters Tb y T β u :=
    ⟨hflow.startsAtWilson, fun j hj => hflow.coupling_eq j (by omega), fun j hj => hflow.onFamily j (by omega)⟩
  have hside : IsBlockTorusSide (Tb.stepParameters y) n := by
    rw [hat.side_eq]
    exact isBlockTorusSide_fineSide (Tb.stepParameters y) (K - u) (isBlockTorusSide_top hT hat.chain.volume_le)
  have hden := hy₀ y h1 hret hwil T β u n htower hat.chain.marks hside
  have hexp := (hat.chain.expansions u hu).2
  have hprob : IsProbabilityMeasure (markedSampleLaw T β u n) :=
    (hDraw (Tb.stepParameters y) hfit hLgt T hat.chain.cutoff_bottom hat.chain.marks β u n).1
  have hZ := (hLaw (Tb.stepParameters y) hfit hLgt β (fun _ => 0) u n).2.1
  obtain ⟨C, hC⟩ := hbd
  have key := integral_eq_of_density (X := TorusField n) (I := Finset (TorusSite n))
    (E := fun Y => Y → (T.stage u).labels.Ω)
    (markedSampleLaw T β u n) (hBor (Tb.stepParameters y) hfit T u n) (fieldHaar n)
    (fun Y => Measure.pi fun _ : Y => (T.stage u).labels.μ)
    (fun W Y => IsHullState (Tb.stepParameters y) (clusterRange (T.stage u).coupling) W Y)
    (fun Y W ω => (T.stage u).labelWeight n W Y ω)
    (fun W Y ω h => hexp.nonneg n hside W Y ω h) (fun Y => (hexp.borel n hside Y).1)
    (fun W => by
      have e := hexp.sum n hside W
      simp only [] at e ⊢
      exact e ▸ ENNReal.ofReal_ne_top)
    (fun Y W ω => (W, ⟨Y, ω⟩))
    (fun Y => measurable_fst.prodMk ((measurable_sigmaMk Y).comp measurable_snd)) hZ hden hF hC
  exact key
end YangMills.Construction.HullTrees
end
