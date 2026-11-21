import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGasProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ResponseInTheExpansion
noncomputable section
open MeasureTheory
open scoped ENNReal
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusLumps TorusFields WeightedResponses FreeEnergies ClusterBounds
  ClusterExpansionOfAStep
private theorem ofReal_sum_le_sum_ofReal {κ : Type} (s : Finset κ) (f : κ → ℝ) :
    ENNReal.ofReal (∑ k ∈ s, f k) ≤ ∑ k ∈ s, ENNReal.ofReal (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (by gcongr)
private def trackedWeight {ι : Type} (W : ι → ℝ) (J : Finset ι) : ℝ :=
  open Classical in if h : J.Nonempty then W h.choose else 0
private theorem add_sum_le_mul_prod_one_add {κ : Type} (s : Finset κ) (t : κ → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) {a : ℝ}
    (ha : 1 ≤ a) :
    a + ∑ i ∈ s, t i ≤ a * ∏ i ∈ s, (1 + t i) ∧ 1 ≤ ∏ i ∈ s, (1 + t i) := by apply _root_.YangMills.SharedProofs.p28055 <;> assumption
private theorem prod_one_add_sub_one_le {ι : Type} (I : Finset ι) (T W : ι → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hT0 : ∀ j ∈ I, 0 ≤ T j) (hTu : ∀ j ∈ I, T j ≤ u) (hTW : ∀ j ∈ I, T j ≤ W j * u) (hW : ∀ j ∈ I, 0 ≤ W j) :
    ∏ j ∈ I, (1 + T j) - 1 ≤
      (open Classical in ∑ J ∈ I.powerset.erase ∅, trackedWeight (fun j => (I.card.factorial : ℝ) * W j) J) *
        Real.exp u := by
  classical
  have e1 : ∏ j ∈ I, (1 + T j) = 1 + ∑ J ∈ I.powerset.erase ∅, ∏ j ∈ J, T j := by
    rw [Finset.prod_one_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset I)]
    simp
  rw [e1, add_sub_cancel_left, Finset.sum_mul]
  refine Finset.sum_le_sum fun J hJ => ?_
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hJ
  have hJI : J ⊆ I := Finset.mem_powerset.mp hsub
  have hJn : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  unfold trackedWeight
  rw [dif_pos hJn]
  set j₀ := hJn.choose with hj₀
  have hj : j₀ ∈ J := hJn.choose_spec
  have hjI := hJI hj
  rw [← Finset.mul_prod_erase J T hj]
  have h1 : ∏ j ∈ J.erase j₀, T j ≤ u ^ (J.card - 1) := by
    calc ∏ j ∈ J.erase j₀, T j ≤ ∏ _j ∈ J.erase j₀, u :=
          Finset.prod_le_prod (fun j hj' => hT0 j (hJI (Finset.mem_of_mem_erase hj')))
            fun j hj' => hTu j (hJI (Finset.mem_of_mem_erase hj'))
      _ = u ^ (J.card - 1) := by rw [Finset.prod_const, Finset.card_erase_of_mem hj]
  have hk : 1 ≤ J.card := Finset.card_pos.mpr hJn
  have h2 : u ^ J.card ≤ (I.card.factorial : ℝ) * Real.exp u := by
    have h3 := Real.pow_div_factorial_le_exp u hu J.card
    have h4 : (J.card.factorial : ℝ) ≤ I.card.factorial := by
      exact_mod_cast Nat.factorial_le (Finset.card_le_card hJI)
    have h5 : (0 : ℝ) < J.card.factorial := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_iff₀ h5] at h3
    calc u ^ J.card ≤ Real.exp u * J.card.factorial := h3
      _ ≤ Real.exp u * I.card.factorial := by gcongr
      _ = _ := mul_comm _ _
  calc T j₀ * ∏ j ∈ J.erase j₀, T j ≤ (W j₀ * u) * u ^ (J.card - 1) :=
        mul_le_mul (hTW _ hjI) h1
          (Finset.prod_nonneg fun j hj' => hT0 j (hJI (Finset.mem_of_mem_erase hj')))
          (mul_nonneg (hW _ hjI) hu)
    _ = W j₀ * u ^ J.card := by
        obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le' hk
        rw [hk']
        simp only [Nat.add_sub_cancel]
        ring
    _ ≤ W j₀ * ((I.card.factorial : ℝ) * Real.exp u) := mul_le_mul_of_nonneg_left h2 (hW _ hjI)
    _ = _ := by ring
private theorem sum_trackedWeight_le {ι κ : Type} [Fintype κ] (I : Finset ι) (W : κ → ι → ℝ) (z : κ → ℝ) {k b : ℝ}
    (hk : 0 ≤ k) (hb : 0 ≤ b) (hc : ∀ j ∈ I, ∑ i, W i j * z i ≤ b) :
    ∑ i, (open Classical in ∑ J ∈ I.powerset.erase ∅, trackedWeight (fun j => k * W i j) J) * z i ≤
      2 ^ I.card * k * b := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ J ∈ I.powerset.erase ∅, ∑ i, trackedWeight (fun j => k * W i j) J * z i ≤ k * b := by
    intro J hJ
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hJ
    have hJn : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hj : hJn.choose ∈ I := Finset.mem_powerset.mp hsub hJn.choose_spec
    unfold trackedWeight
    simp only [dif_pos hJn, mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hc _ hj) hk
  calc _ ≤ ∑ _J ∈ I.powerset.erase ∅, k * b := Finset.sum_le_sum h1
    _ = ((I.powerset.erase ∅).card : ℝ) * (k * b) := by simp
    _ ≤ (2 ^ I.card : ℝ) * (k * b) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hk hb)
        have h2 : (I.powerset.erase ∅).card ≤ 2 ^ I.card := by
          calc _ ≤ I.powerset.card := Finset.card_erase_le
            _ = _ := Finset.card_powerset I
        exact_mod_cast h2
    _ = _ := by ring
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R} {G : GasGround R n}
private theorem siteScore_configSetting_eq {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ)
    (y : TorusSite (n * R.params.side)) :
    siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y =
      recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i) := by apply _root_.YangMills.SharedProofs.p55158 <;> assumption
private theorem ofReal_integral_caseTerm_le (G : GasGround R n)
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ)
    (hh : ∀ Yt ωt, 0 ≤ h Yt ωt) (hi : CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt)
    (bad : Finset (TorusBond (n * R.params.side))) (hbad : bad ∈ (markedBonds R G.cut).powerset)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n) :
    ENNReal.ofReal (∫ W, ∫ ν : G.state.unlabelled Yt → R.labels.Ω,
        WeightedResponses.caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) ≤
      G.caseIntegral (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) bad Yt b := by
  classical
  have hf := hi bad hbad Yt b
  set f : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) → ℝ :=
    fun p => WeightedResponses.caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b p.1 p.2
    with hfd
  have e1 := integral_prod f hf
  have e2 : G.caseIntegral (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) bad Yt b =
      ∫⁻ p, ENNReal.ofReal (f p) ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    rw [lintegral_prod _ hf.aemeasurable.ennreal_ofReal]
    unfold GasGround.caseIntegral
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    simp only [hfd]
    unfold GasGround.caseIntegrand WeightedResponses.caseTerm
    split_ifs
    · rw [ENNReal.ofReal_mul (hh _ _)]
    · simp
  rw [← e1 , e2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans ENNReal.ofReal_toReal_le
private theorem caseMean_le_of_caseMass_le (G : GasGround R n)
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ)
    (hh : ∀ Yt ωt, 0 ≤ h Yt ωt) (hi : CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt) {c : ℝ}
    (hc : 0 ≤ c)
    (hb : coarseStateMass R G.cut G.coarse G.state ≠ 0 → coarseStateMass R G.cut G.coarse G.state ≠ ⊤ →
      G.caseMass ∅ (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) ≤
        coarseStateMass R G.cut G.coarse G.state * ENNReal.ofReal c) :
    caseMean R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) ≤ c := by
  classical
  have h1 : ENNReal.ofReal (caseIntegral R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt) ≤
      G.caseMass ∅ (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) := by
    unfold WeightedResponses.caseIntegral GasGround.caseMass
    refine (ofReal_sum_le_sum_ofReal _ _).trans (Finset.sum_le_sum fun bad hbad => ?_)
    refine (ofReal_sum_le_sum_ofReal _ _).trans (Finset.sum_le_sum fun Yt _ => ?_)
    have hoff : G.CaseAvoids ∅ bad Yt := ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩
    rw [if_pos hoff]
    exact (ofReal_sum_le_sum_ofReal _ _).trans
      (Finset.sum_le_sum fun b _ => ofReal_integral_caseTerm_le G h hh hi bad hbad Yt b)
  unfold WeightedResponses.caseMean coarseStateWeight
  by_cases hM0 : coarseStateMass R G.cut G.coarse G.state = 0
  · simp [hM0, hc]
  by_cases hMt : coarseStateMass R G.cut G.coarse G.state = ⊤
  · simp [hMt, hc]
  have hMpos : 0 < (coarseStateMass R G.cut G.coarse G.state).toReal := ENNReal.toReal_pos hM0 hMt
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hMt ENNReal.ofReal_ne_top)).mp
    (h1.trans (hb hM0 hMt))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
  rw [div_le_iff₀ hMpos]
  linarith
omit [NeZero n] in
private theorem measurable_siteScore (hb : Measurable A.score) (Yt : Finset (TorusSite (n * R.params.side)))
    (y : TorusSite (n * R.params.side)) : Measurable fun ω : Yt → R.labels.Ω => siteScore A.score Yt ω y := by
  classical
  unfold siteScore
  by_cases hy : y ∈ Yt
  · simp only [dif_pos hy]
    exact hb.comp (measurable_pi_apply _)
  · simp only [dif_neg hy]
    exact measurable_const
omit [NeZero n] in
private theorem measurable_prod_meanSiteScore {ι : Type} (hb : Measurable A.score) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun ω : Yt → R.labels.Ω => ∏ j ∈ I, meanSiteScore A.score (B j) Yt ω :=
  Finset.measurable_prod _ fun j _ => by
    unfold meanSiteScore
    exact ((Finset.measurable_sum _ fun y _ => measurable_siteScore hb Yt y).const_mul _).const_add _
private theorem meanSiteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} (S Y : Finset (TorusSite m))
    (ω : Y → Ω) : 0 ≤ meanSiteScore s S Y ω := by
  unfold meanSiteScore
  have : 0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, siteScore s Y ω y :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _)
  linarith
private theorem caseIntegrable_prod_meanSiteScore {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (hb : Measurable A.score)
    (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))) (hB : ∀ j ∈ I, (B j).Nonempty)
    (hI : ∀ (S : Finset (TorusSite (n * R.params.side)))
      (h' : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ),
      (∀ Yt, Measurable (h' Yt)) → (∀ Yt ωt, |h' Yt ωt| ≤ Real.exp (scoreSumOn A S Yt ωt)) →
      CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h' Yt ωt) :
    CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => ∏ j ∈ I, meanSiteScore A.score (B j) Yt ωt := by
  classical
  set c₀ : ℝ := (I.card.factorial : ℝ) * Real.exp 1 with hc₀
  have hfac : (0 : ℝ) < I.card.factorial := by exact_mod_cast Nat.factorial_pos _
  have hpos : 0 < c₀ := mul_pos hfac (Real.exp_pos _)
  have key := hI (I.biUnion B) (fun Yt ωt => c₀⁻¹ * ∏ j ∈ I, meanSiteScore A.score (B j) Yt ωt)
    (fun Yt => (measurable_prod_meanSiteScore hb I B Yt).const_mul _) (fun Yt ωt => ?_)
  · intro bad hbad Yt b
    refine ((key bad hbad Yt b).const_mul c₀).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [WeightedResponses.caseTerm]
    split_ifs
    · field_simp
    · simp
  · set u := scoreSumOn A (I.biUnion B) Yt ωt with hu
    have hu0 : 0 ≤ u := Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _
    have hN : ∀ j ∈ I, meanSiteScore A.score (B j) Yt ωt ≤ 1 + u := by
      intro j hj
      unfold meanSiteScore
      have h1 : ((B j).card : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by exact_mod_cast Finset.card_pos.mpr (hB j hj))
      have h2 : ∑ y ∈ B j, siteScore A.score Yt ωt y ≤ u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem B hj)
          fun y _ _ => siteScore_nonneg hs _ _ _
      have h3 : 0 ≤ ∑ y ∈ B j, siteScore A.score Yt ωt y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _
      have h4 : ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, siteScore A.score Yt ωt y ≤ 1 * u :=
        mul_le_mul h1 h2 h3 zero_le_one
      linarith
    have hprod : ∏ j ∈ I, meanSiteScore A.score (B j) Yt ωt ≤ (1 + u) ^ I.card := by
      calc _ ≤ ∏ _j ∈ I, (1 + u) := Finset.prod_le_prod (fun j _ => meanSiteScore_nonneg hs _ _ _) hN
        _ = _ := by rw [Finset.prod_const]
    have hp0 : 0 ≤ ∏ j ∈ I, meanSiteScore A.score (B j) Yt ωt :=
      Finset.prod_nonneg fun j _ => meanSiteScore_nonneg hs _ _ _
    have hexp := Real.pow_div_factorial_le_exp (1 + u) (by linarith) I.card
    rw [div_le_iff₀ hfac, Real.exp_add] at hexp
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le) hp0), inv_mul_le_iff₀ hpos]
    calc _ ≤ (1 + u) ^ I.card := hprod
      _ ≤ _ := hexp
      _ = _ := by rw [hc₀]; ring
private def spinFactor (A : ResponseSetup R) (G : GasGround R n) {ι : Type} (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (v : G.SpinValue i) : ℝ :=
  ∏ j ∈ I, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v)
private def recordedMean (A : ResponseSetup R) (G : GasGround R n) (S : Finset (TorusSite (n * R.params.side))) : ℝ :=
  1 + (S.card : ℝ)⁻¹ * ∑ y ∈ S, recordedSiteScore A G y
private theorem one_le_recordedMean (hs : ∀ w, 0 ≤ A.score w) (S : Finset (TorusSite (n * R.params.side))) :
    1 ≤ recordedMean A G S := by apply _root_.YangMills.DeltaSharedProofs.p502616 <;> assumption
private theorem spinMean_nonneg (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i)
    (S : Finset (TorusSite (n * R.params.side))) :
    0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, spinSiteScore A G i y v :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => spinSiteScore_nonneg hs i y v)
private theorem prod_meanSiteScore_le {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (σ : G.Config) :
    ∏ j ∈ I, meanSiteScore A.score (B j) (configSetting G σ).support (configSetting G σ).labelling ≤
      (∏ j ∈ I, recordedMean A G (B j)) * ∏ i, spinFactor A G I B i (σ i) := by
  classical
  have h1 : ∀ j ∈ I, meanSiteScore A.score (B j) (configSetting G σ).support (configSetting G σ).labelling ≤
      recordedMean A G (B j) * ∏ i, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i)) := by
    intro j _
    refine le_trans ?_ (add_sum_le_mul_prod_one_add Finset.univ _
      (fun i _ => spinMean_nonneg hs i (σ i) (B j)) (one_le_recordedMean hs (B j))).1
    unfold meanSiteScore recordedMean
    have e : ∑ i, ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i) =
        ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, ∑ i, spinSiteScore A G i y (σ i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [e, add_assoc, ← mul_add, ← Finset.sum_add_distrib]
    have : ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j,
          siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y ≤
        ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, (recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => siteScore_configSetting_le hs σ y)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  calc _ ≤ ∏ j ∈ I, (recordedMean A G (B j) *
          ∏ i, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i))) :=
        Finset.prod_le_prod (fun j _ => meanSiteScore_nonneg hs _ _ _) h1
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_comm]
        rfl
private theorem sum_spinSiteScore_le (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i)
    (S : Finset (TorusSite (n * R.params.side))) :
    ∑ y ∈ S, spinSiteScore A G i y v ≤ spinScore A i v := by apply _root_.YangMills.SharedProofs.p40586 <;> assumption
private theorem spinScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i) :
    0 ≤ spinScore A i v := by
  rcases v with u | w
  · exact le_rfl
  · exact Finset.sum_nonneg fun z _ => hs _
private def meetWeight {ι : Type} (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (j : ι) : ℝ :=
  open Classical in if (B j ∩ i.1.2).Nonempty then ((B j).card : ℝ)⁻¹ else 0
private def excessCoefficient {ι : Type} (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side)))
    (i : G.GasSpin) : ℝ :=
  open Classical in
  ∑ J ∈ I.powerset.erase ∅, trackedWeight (fun j => (I.card.factorial : ℝ) * meetWeight B i j) J
private theorem excessCoefficient_nonneg {ι : Type} (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side)))
    (i : G.GasSpin) : 0 ≤ excessCoefficient I B i := by
  classical
  unfold excessCoefficient
  refine Finset.sum_nonneg fun J _ => ?_
  unfold trackedWeight
  split_ifs
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold meetWeight
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  · exact le_rfl
private theorem spinFactor_sub_one_le {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (hB : ∀ j ∈ I, (B j).Nonempty) (i : G.GasSpin)
    (v : G.SpinValue i) :
    spinFactor A G I B i v - 1 ≤ excessCoefficient I B i * Real.exp (spinScore A i v) := by
  classical
  have hu := spinScore_nonneg (A := A) hs i v
  have hsum := fun j => sum_spinSiteScore_le (A := A) hs i v (B j)
  have hTW : ∀ j ∈ I, ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v ≤
      meetWeight B i j * spinScore A i v := by
    intro j _
    unfold meetWeight
    split_ifs with hm
    · exact mul_le_mul_of_nonneg_left (hsum j) (inv_nonneg.mpr (Nat.cast_nonneg _))
    · have : ∑ y ∈ B j, spinSiteScore A G i y v = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hyi : y ∉ i.1.2 := fun h => hm ⟨y, Finset.mem_inter.mpr ⟨hy, h⟩⟩
        rcases v with u | w
        · rfl
        · simp [spinSiteScore, hyi]
      simp [this]
  have hW0 : ∀ j ∈ I, 0 ≤ meetWeight B i j := by
    intro j _
    unfold meetWeight
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  have hW1 : ∀ j ∈ I, meetWeight B i j ≤ 1 := by
    intro j hj
    unfold meetWeight
    split_ifs
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast Finset.card_pos.mpr (hB j hj))
    · exact zero_le_one
  refine prod_one_add_sub_one_le I (fun j => ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v)
    (meetWeight B i) hu (fun j _ => spinMean_nonneg hs i v (B j)) (fun j hj => ?_) hTW hW0
  calc _ ≤ meetWeight B i j * spinScore A i v := hTW j hj
    _ ≤ 1 * spinScore A i v := mul_le_mul_of_nonneg_right (hW1 j hj) hu
    _ = _ := one_mul _
private theorem hasSmallExcess_spinFactor {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (hB : ∀ j ∈ I, (B j).Nonempty) (z : G.GasSpin → ℝ)
    (hpaid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
        ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) :
    G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight (spinFactor A G I B)
      fun i => excessCoefficient I B i * z i := by
  classical
  intro i σ hσ
  have hC := excessCoefficient_nonneg I B i
  calc ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (spinFactor A G I B i s - 1) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i)
      ≤ ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (excessCoefficient I B i) *
          (ENNReal.ofReal (Real.exp (spinScore A i s)) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i s)) ∂(G.referenceMeasure ∅ i) := by
        refine lintegral_mono fun s => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
        gcongr
        exact spinFactor_sub_one_le hs I B hB i s
    _ = ENNReal.ofReal (excessCoefficient I B i) * ∫⁻ s in {G.pairConstraint.vacant i}ᶜ,
          ENNReal.ofReal (Real.exp (spinScore A i s)) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (excessCoefficient I B i) * (ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by
        gcongr
        exact hpaid i σ hσ
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
private theorem gasIntegrand_eq_ofReal_mul (hpos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < G.weight σ)
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ) (σ : G.Config) :
    G.gasIntegrand (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) σ =
      ENNReal.ofReal (h (configSetting G σ).support (configSetting G σ).labelling) *
        G.pairConstraint.weightDensity G.weight σ := by
  classical
  unfold GasGround.gasIntegrand PairConstraint.weightDensity
  by_cases ha : G.pairConstraint.IsAdmissible σ
  · rw [if_pos ha, if_pos ha]
    have hw := hpos σ ha
    have hm : settingMass (G.settingOf (G.familyOf σ)) ≠ ⊤ := by
      intro htop
      unfold GasGround.weight at hw
      rw [if_pos ha, htop] at hw
      simp at hw
    have e : ENNReal.ofReal (G.weight σ) = settingMass (G.settingOf (G.familyOf σ)) := by
      unfold GasGround.weight
      rw [if_pos ha, ENNReal.ofReal_toReal hm]
    rw [e]
    unfold ChartSetting.settingIntegral settingMass
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [if_neg ha, if_neg ha, mul_zero]
private theorem gasMass_le_partitionFunction_mul (hP : MeanOfProductStatement) {z : G.GasSpin → ℝ}
    (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z) (g : ∀ i, G.SpinValue i → ℝ)
    (e : G.GasSpin → ℝ) (hm : ∀ i, Measurable (g i)) (h1 : ∀ i s, 1 ≤ g i s)
    (ha : ∀ i, g i (G.pairConstraint.vacant i) = 1) (he : ∀ i, 0 ≤ e i)
    (hx : G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight g e)
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hH : ∀ σ, h (configSetting G σ).support (configSetting G σ).labelling ≤ c * ∏ i, g i (σ i))
    (hP0 : G.partitionFunction ∅ ≠ 0) (hPt : G.partitionFunction ∅ ≠ ⊤) :
    G.gasMass ∅ (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) ≤
      G.partitionFunction ∅ * ENNReal.ofReal (c * ∏ i, (1 + e i)) := by
  classical
  have key := hP G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight z hW g e hm h1 ha he hx
  set f : G.Config → ℝ≥0∞ := fun σ => ∏ i, ENNReal.ofReal (g i (σ i)) with hf
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hm i).comp (measurable_pi_apply i))
  have hd := hW.measurable_weightDensity
  have hlaw : ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) =
      (G.partitionFunction ∅)⁻¹ *
        ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) := by
    unfold PairConstraint.gibbsLaw
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hd hfm]
    rfl
  have hbig : ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) =
      G.partitionFunction ∅ * ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) := by
    rw [hlaw, ← mul_assoc, ENNReal.mul_inv_cancel hP0 hPt, one_mul]
  have hpw : ∀ σ, G.gasIntegrand (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) σ ≤
      ENNReal.ofReal c * (G.pairConstraint.weightDensity G.weight σ * f σ) := by
    intro σ
    rw [gasIntegrand_eq_ofReal_mul hW.pos_of_admissible h σ]
    have e1 : ENNReal.ofReal (h (configSetting G σ).support (configSetting G σ).labelling) ≤
        ENNReal.ofReal c * f σ := by
      simp only [hf]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_trans zero_le_one (h1 i _)), ← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (hH σ)
    calc _ ≤ ENNReal.ofReal c * f σ * G.pairConstraint.weightDensity G.weight σ := by gcongr
      _ = _ := by ring
  unfold GasGround.gasMass
  calc _ ≤ ∫⁻ σ, ENNReal.ofReal c * (G.pairConstraint.weightDensity G.weight σ * f σ)
          ∂Measure.pi (G.referenceMeasure ∅) :=
        lintegral_mono hpw
    _ = ENNReal.ofReal c *
          ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal c * (G.partitionFunction ∅ *
          ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)) := by rw [hbig]
    _ ≤ ENNReal.ofReal c * (G.partitionFunction ∅ * ENNReal.ofReal (∏ i, (1 + e i))) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hc]; ring
private theorem recordedMean_le (hs : ∀ w, 0 ≤ A.score w) (h₁ : 0 ≤ A.responseParams.s₁)
    (S : Finset (TorusSite (n * R.params.side))) (hS : S.Nonempty) :
    recordedMean A G S ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (open Classical in S.image (parentBlock R.params.side)) G.state.1 G.state.2 := by apply _root_.YangMills.DeltaSharedProofs.p501903 <;> assumption
theorem productMeanScoreStepBound_holds (hS : clusterScoreIntegralBound)
    (hI : labelFunctionsIntegrableStatement) (hA : coarseStateGasStatement) (hW : GasIsActivityBounded)
    (hG : CaseMassEqGasMass) (hC : _root_.YangMills.Construction.ClusterBounds.ClusterSumBound) (hP : MeanOfProductStatement) :
    productMeanScoreStepBound := by
  classical
  obtain ⟨r₁, p₁, hS⟩ := hS
  obtain ⟨r₂, p₂, hI⟩ := hI
  obtain ⟨r₃, p₃, hA⟩ := hA
  obtain ⟨r₄, p₄, hW⟩ := hW
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (p₁ c) (p₂ c)) (lt_min (p₃ c) (p₄ c)), fun T hT hT' K => ?_⟩
  have t₁ : T.rt ≤ r₁ T.toChainParameters := hT'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have t₂ : T.rt ≤ r₂ T.toChainParameters := hT'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have t₃ : T.rt ≤ r₃ T.toChainParameters := hT'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t₄ : T.rt ≤ r₄ T.toChainParameters := hT'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨yS, hS⟩ := hS T hT t₁ K
  obtain ⟨yI, hI⟩ := hI T hT t₂ K
  obtain ⟨yA, hA⟩ := hA T hT t₃
  obtain ⟨yW, hW⟩ := hW T hT t₄
  obtain ⟨yG, hG⟩ := hG T hT
  obtain ⟨yC, hC⟩ := hC T hT
  refine ⟨max (max (max yS yI) (max yA yW)) (max (max yG yC) (max 0 (200 * T.B))),
    fun y hy R A hK hTab n _ G hG₀ ι I B hB => ?_⟩
  have f₁ := le_trans (le_max_left _ _) hy
  have f₂ := le_trans (le_max_right _ _) hy
  have fS : yS ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) f₁
  have fI : yI ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) f₁
  have fA : yA ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) f₁
  have fW : yW ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) f₁
  have fG : yG ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) f₂
  have fC : yC ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) f₂
  have f0 : 0 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) f₂
  have fB : 200 * T.B ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) f₂
  have hOn := hTab.onFamily
  have hl := hOn.params_eq
  have hxy : y ≤ R.coupling := hOn.le_coupling
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp hTab.abs_sub_le).2
    linarith
  have hprice := hTab.admissible.price
  have hs := hprice.nonneg
  have hb := hprice.borel
  have hfits := hTab.admissible.params_admissible
  have hκ₁ : 0 < T.κ₁ := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    exact lt_min (by positivity) (by positivity)
  have hch : 0 < T.gasRate := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    have h4 : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min h2 (lt_min (by positivity) (by positivity))
    unfold ParameterAssignment.gasRate
    positivity
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have h1 : 1 ≤ R.params.coupling := by
      rw [hl]
      exact hT.a_ge
    have h2 := hfits.N₀_nonneg
    have h3 := hfits.Kc_ge
    have h4 : 0 ≤ A.responseParams.C₀ := by
      rw [hfits.C₀_eq]
      linarith
    rw [hfits.s₁_eq]
    positivity
  set h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ :=
    fun Yt ωt => ∏ j ∈ I, meanSiteScore A.score (B j) Yt ωt with hh
  have hh0 : ∀ Yt ωt, 0 ≤ h Yt ωt := fun Yt ωt => Finset.prod_nonneg fun j _ => meanSiteScore_nonneg hs _ _ _
  have hint : CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt :=
    caseIntegrable_prod_meanSiteScore hs hb I B hB fun S h' hm hbd => hI y fI R A hK hTab n G hG₀ S h' hm hbd
  refine ⟨hint, ?_⟩
  have hWt : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    hW y fW R hOn hx n G hG₀ fun j => j.1.Touches ∅
  have hz0 : ∀ i, 0 ≤ G.spinActivity T.gasRate i := hWt.activity_nonneg
  have hexc := hasSmallExcess_spinFactor (A := A) (G := G) hs I B hB (G.spinActivity T.gasRate)
    fun i σ hσ => hS y fS R A hK hTab n G hG₀ i σ hσ
  set e : G.GasSpin → ℝ := fun i => excessCoefficient I B i * G.spinActivity T.gasRate i with he
  have he0 : ∀ i, 0 ≤ e i := fun i => mul_nonneg (excessCoefficient_nonneg I B i) (hz0 i)
  set b : ℝ := Real.exp (-(8 * T.gasRate * R.coupling)) with hbd
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hcount : ∀ Y : TorusSite n, ∑ θ ∈ supportsAtBlock R.params.side R.range Y,
      clusterWeight R.params.side T.gasRate R.coupling R.range θ ≤ b := by
    have gen : ∀ ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters, ℓ = T.stepParameters y → ∀ Y : TorusSite n,
        ∑ θ ∈ supportsAtBlock ℓ.side (clusterRange R.coupling) Y,
          clusterWeight ℓ.side T.gasRate R.coupling (clusterRange R.coupling) θ ≤ b := by
      rintro ℓ rfl Y
      refine le_trans (Finset.sum_le_sum fun θ hθ => ?_) (hC y fC R.coupling hxy n Y)
      have hY := (Finset.mem_filter.mp hθ).2.2
      have hcard : (1 : ℝ) ≤ (supportCore (T.stepParameters y).side (clusterRange R.coupling) θ).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨Y, hY⟩
      have hz : 0 ≤ clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ :=
        (Real.exp_pos _).le
      have h1 : (1 : ℝ) ≤ ((supportCore (T.stepParameters y).side (clusterRange R.coupling) θ).card : ℝ) ^ 4 :=
        one_le_pow₀ hcard
      have h2 : (1 : ℝ) ≤ Real.exp (2 * T.rt *
          (siteDiameter (supportCore (T.stepParameters y).side (clusterRange R.coupling) θ) : ℝ)) :=
        Real.one_le_exp (by have := hT.rt_pos; positivity)
      calc clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ
          = clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ * 1 * 1 := by
            ring
        _ ≤ _ := by gcongr
    exact gen R.params hl
  have hmeet : ∀ j ∈ I, ∑ i : G.GasSpin, meetWeight B i j * G.spinActivity T.gasRate i ≤ b := by
    intro j hj
    have hsp := sum_spin_weight_le_card_parentBlocks_mul (G := G)
      (fun θ => clusterWeight R.params.side T.gasRate R.coupling R.range θ)
      (fun θ => (Real.exp_pos _).le) hcount (B j)
    have hpos : (0 : ℝ) < (B j).card := by exact_mod_cast Finset.card_pos.mpr (hB j hj)
    have hcard : ((parentBlocks (B j)).card : ℝ) ≤ (B j).card := by exact_mod_cast Finset.card_image_le
    calc ∑ i : G.GasSpin, meetWeight B i j * G.spinActivity T.gasRate i
        = ((B j).card : ℝ)⁻¹ * ∑ i : G.GasSpin, if (B j ∩ i.1.2).Nonempty then
            clusterWeight R.params.side T.gasRate R.coupling R.range i.1 else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold meetWeight GasGround.spinActivity
          split_ifs
          · rfl
          · simp
      _ ≤ ((B j).card : ℝ)⁻¹ * (((parentBlocks (B j)).card : ℝ) * b) :=
          mul_le_mul_of_nonneg_left hsp (inv_nonneg.mpr hpos.le)
      _ ≤ ((B j).card : ℝ)⁻¹ * (((B j).card : ℝ) * b) := by gcongr
      _ = b := by field_simp
  have hfac : (0 : ℝ) ≤ I.card.factorial := Nat.cast_nonneg _
  have hsum : ∑ i, e i ≤ 2 ^ I.card * (I.card.factorial : ℝ) * b :=
    sum_trackedWeight_le I (fun i j => meetWeight B i j) (G.spinActivity T.gasRate) hfac hb0 hmeet
  set c : ℝ := ∏ j ∈ I, recordedMean A G (B j) with hc
  have hc1 : 0 ≤ c := Finset.prod_nonneg fun j _ => le_trans zero_le_one (one_le_recordedMean hs _)
  have hprod0 : 0 ≤ ∏ i, (1 + e i) := Finset.prod_nonneg fun i _ => by linarith [he0 i]
  have hg1 : ∀ i s, 1 ≤ spinFactor A G I B i s := by
    intro i s
    unfold spinFactor
    exact (add_sum_le_mul_prod_one_add (a := 1) I _ (fun j _ => spinMean_nonneg hs i s (B j)) le_rfl).2
  have hga : ∀ i, spinFactor A G I B i (G.pairConstraint.vacant i) = 1 := by
    intro i
    unfold spinFactor
    refine Finset.prod_eq_one fun j _ => ?_
    have : ∑ y ∈ B j, spinSiteScore A G i y (G.pairConstraint.vacant i) = 0 :=
      Finset.sum_eq_zero fun y _ => rfl
    rw [this]
    simp
  have hgm : ∀ i, Measurable (spinFactor A G I B i) := by
    intro i
    unfold spinFactor
    exact Finset.measurable_prod _ fun j _ =>
      ((Finset.measurable_sum _ fun y _ => measurable_spinSiteScore hb i y).const_mul _).const_add _
  have hFw : IsCaseFunctional (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt) : CaseFunctional R n) := by
    refine ⟨fun Yt _ _ =>
      ENNReal.measurable_ofReal.comp ((measurable_prod_meanSiteScore hb I B Yt).comp measurable_snd), ?_⟩
    intro W Yt ωt bad bs u _ _ _ _
    have e1 : ∀ S, meanSiteScore A.score S Yt (R.labels.act Yt u ωt) = meanSiteScore A.score S Yt ωt := by
      intro S
      unfold meanSiteScore
      congr 2
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold siteScore
      by_cases hy : y ∈ Yt
      · rw [dif_pos hy, dif_pos hy]
        exact hprice.gauge (n * R.params.side) Yt u ωt ⟨y, hy⟩
      · rw [dif_neg hy, dif_neg hy]
    simp only [hh, e1]
  have hmeas : Measurable (G.gasIntegrand (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt))) := by
    have e1 : G.gasIntegrand (fun _ Yt ωt _ _ => ENNReal.ofReal (h Yt ωt)) = fun σ =>
        ENNReal.ofReal (∏ j ∈ I, (1 + ((B j).card : ℝ)⁻¹ *
          ∑ y ∈ B j, (recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i)))) *
            G.pairConstraint.weightDensity G.weight σ := by
      funext σ
      rw [gasIntegrand_eq_ofReal_mul hWt.pos_of_admissible h σ]
      by_cases ha : G.pairConstraint.IsAdmissible σ
      · simp only [hh, meanSiteScore, siteScore_configSetting_eq ha]
      · have : G.pairConstraint.weightDensity G.weight σ = 0 := by
          unfold PairConstraint.weightDensity
          rw [if_neg ha]
        rw [this, mul_zero, mul_zero]
    rw [e1]
    refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun j _ => ?_)).mul
      hWt.measurable_weightDensity
    refine ((Finset.measurable_sum _ fun y _ => ?_).const_mul _).const_add _
    exact (Finset.measurable_sum _ fun i _ =>
      (measurable_spinSiteScore hb i y).comp (measurable_pi_apply i)).const_add _
  obtain ⟨-, -, -, hmass, -⟩ := hA y fA R hOn hx n G hG₀
  have hsumG := hG y fG R hOn hx n G hG₀ ∅ _ hFw hmeas
  have hmain : caseMean R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) ≤ c * ∏ i, (1 + e i) := by
    refine caseMean_le_of_caseMass_le G h hh0 hint (mul_nonneg hc1 hprod0) fun hM0 hMt => ?_
    have hP0 : G.partitionFunction ∅ ≠ 0 := by
      intro h0
      rw [hmass, h0, mul_zero] at hM0
      exact hM0 rfl
    have hZ0 : ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) ≠ 0 := by
      intro h0
      rw [hmass, h0, zero_mul] at hM0
      exact hM0 rfl
    have hPt : G.partitionFunction ∅ ≠ ⊤ := by
      intro h0
      rw [hmass, h0, ENNReal.mul_top hZ0] at hMt
      exact hMt rfl
    rw [hsumG, hmass, mul_assoc (ENNReal.ofReal _ * ENNReal.ofReal _) (G.partitionFunction ∅)]
    exact mul_le_mul' le_rfl (gasMass_le_partitionFunction_mul hP hWt (spinFactor A G I B) e hgm hg1 hga he0
      hexc h hc1 (fun σ => prod_meanSiteScore_le hs I B σ) hP0 hPt)
  refine hmain.trans ?_
  have h7 : b ≤ Real.exp (-(7 * T.gasRate * R.coupling)) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ T.gasRate * R.coupling := mul_nonneg hch.le (f0.trans hxy)
    linarith
  have hexp : ∏ i, (1 + e i) ≤
      Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) := by
    calc ∏ i, (1 + e i) ≤ ∏ i, Real.exp (e i) :=
          Finset.prod_le_prod (fun i _ => by linarith [he0 i])
            fun i _ => by linarith [Real.add_one_le_exp (e i)]
      _ = Real.exp (∑ i, e i) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hsum.trans (mul_le_mul_of_nonneg_left h7 (by positivity)))
  have hstored : c ≤ ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (open Classical in (B i).image (parentBlock R.params.side)) G.state.1 G.state.2 :=
    Finset.prod_le_prod (fun j _ => le_trans zero_le_one (one_le_recordedMean hs _))
      fun j hj => recordedMean_le hs hs₁ (B j) (hB j hj)
  calc c * ∏ i, (1 + e i) ≤ (∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (open Classical in (B i).image (parentBlock R.params.side)) G.state.1 G.state.2) *
        Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) :=
        mul_le_mul hstored hexp hprod0 (hc1.trans hstored)
    _ = _ := mul_comm _ _
end
end YangMills.Construction.ResponseInTheExpansion
