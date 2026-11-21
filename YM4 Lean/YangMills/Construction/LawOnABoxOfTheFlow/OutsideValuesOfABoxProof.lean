import YangMills.Construction.LawOnABoxOfTheFlow.ColdEventsOfABoxAreLikely
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsBelowATopHaveTheirLaw
import YangMills.Construction.LawOnABoxOfTheFlow.OutsideValuesOfABox
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BoxEvents
section ConditionalChance
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
private theorem exists_set_condProb_ge (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → X} (hF : Measurable F)
    (E : Set Ω) (c : ℝ) (hc : 0 ≤ c) :
    ∃ P : Set X, MeasurableSet P ∧
      (∀ B : Set X, MeasurableSet B → B ⊆ P → c * μ.real (F ⁻¹' B) ≤ μ.real (F ⁻¹' B ∩ E)) ∧
      (1 - c) * μ.real (F ⁻¹' Pᶜ) ≤ μ.real Eᶜ := by
  have hmap : ∀ B, MeasurableSet B → (μ.map F) B = μ (F ⁻¹' B) := fun B hB => Measure.map_apply hF hB
  have hmapE : ∀ B, MeasurableSet B → ((μ.restrict E).map F) B = μ (F ⁻¹' B ∩ E) := fun B hB => by
    rw [Measure.map_apply hF hB, Measure.restrict_apply (hF hB)]
  have hle : (μ.restrict E).map F ≤ μ.map F := Measure.map_mono Measure.restrict_le_self hF
  have hac : (μ.restrict E).map F ≪ μ.map F := Measure.absolutelyContinuous_of_le hle
  have hwd : (μ.map F).withDensity (((μ.restrict E).map F).rnDeriv (μ.map F)) = (μ.restrict E).map F :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  have hd : Measurable (((μ.restrict E).map F).rnDeriv (μ.map F)) := Measure.measurable_rnDeriv _ _
  have hint : ∀ B, MeasurableSet B → ((μ.restrict E).map F) B =
      ∫⁻ x in B, ((μ.restrict E).map F).rnDeriv (μ.map F) x ∂(μ.map F) := fun B hB => by
    conv_lhs => rw [← hwd]
    exact withDensity_apply _ hB
  refine ⟨{x | ENNReal.ofReal c ≤ ((μ.restrict E).map F).rnDeriv (μ.map F) x},
    measurableSet_le measurable_const hd, ?_, ?_⟩
  · intro B hB hBP
    have h1 : ENNReal.ofReal c * (μ.map F) B ≤ ((μ.restrict E).map F) B := by
      rw [hint B hB]
      calc ENNReal.ofReal c * (μ.map F) B = ∫⁻ _ in B, ENNReal.ofReal c ∂(μ.map F) := by
            rw [setLIntegral_const]
        _ ≤ _ := setLIntegral_mono' hB fun x hx => hBP hx
    rw [hmap B hB, hmapE B hB] at h1
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
  · have hQm : MeasurableSet {x | ENNReal.ofReal c ≤ ((μ.restrict E).map F).rnDeriv (μ.map F) x}ᶜ :=
      (measurableSet_le measurable_const hd).compl
    set Q := {x | ENNReal.ofReal c ≤ ((μ.restrict E).map F).rnDeriv (μ.map F) x}ᶜ with hQ
    have h1 : ((μ.restrict E).map F) Q ≤ ENNReal.ofReal c * (μ.map F) Q := by
      rw [hint Q hQm]
      calc _ ≤ ∫⁻ _ in Q, ENNReal.ofReal c ∂(μ.map F) :=
            setLIntegral_mono' hQm fun x hx => le_of_lt (not_le.mp hx)
        _ = ENNReal.ofReal c * (μ.map F) Q := by rw [setLIntegral_const]
    rw [hmap Q hQm, hmapE Q hQm] at h1
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
    have h3 : μ.real (F ⁻¹' Q) ≤ μ.real (F ⁻¹' Q ∩ E) + μ.real Eᶜ := by
      refine le_trans (measureReal_mono (s₂ := (F ⁻¹' Q ∩ E) ∪ Eᶜ) ?_) (measureReal_union_le _ _)
      intro u hu
      by_cases huE : u ∈ E
      · exact Or.inl ⟨hu, huE⟩
      · exact Or.inr huE
    have h4 : μ.real (F ⁻¹' Q ∩ E) ≤ c * μ.real (F ⁻¹' Q) := h2
    linarith
private theorem exists_set_condProb_inter_ge (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → X}
    (hF : Measurable F) (A G : Set Ω) :
    ∃ H : Set X, MeasurableSet H ∧ μ.real (F ⁻¹' Hᶜ) ≤ 16 * μ.real Aᶜ + 4 * μ.real Gᶜ ∧
      ∀ B : Set X, MeasurableSet B → B ⊆ H →
        11 / 16 * μ.real (F ⁻¹' B) ≤ μ.real (F ⁻¹' B ∩ (A ∩ G)) := by
  have kernel : ∀ C : Set Ω, ∃ C' : Set Ω, MeasurableSet C' ∧ C' ⊆ C ∧ μ.real C'ᶜ = μ.real Cᶜ := fun C =>
    ⟨(toMeasurable μ Cᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl,
      Set.compl_subset_comm.mp (subset_toMeasurable _ _), by
        simp only [compl_compl, Measure.real, measure_toMeasurable]⟩
  obtain ⟨A', -, hAsub, hAeq⟩ := kernel A
  obtain ⟨G', hGm, hGsub, hGeq⟩ := kernel G
  obtain ⟨PA, hPAm, hPAb, hPAc⟩ := exists_set_condProb_ge μ hF A' (15 / 16) (by norm_num)
  obtain ⟨PG, hPGm, hPGb, hPGc⟩ := exists_set_condProb_ge μ hF G' (3 / 4) (by norm_num)
  refine ⟨PA ∩ PG, hPAm.inter hPGm, ?_, ?_⟩
  · have h1 : μ.real (F ⁻¹' (PA ∩ PG)ᶜ) ≤ μ.real (F ⁻¹' PAᶜ) + μ.real (F ⁻¹' PGᶜ) := by
      refine le_trans (measureReal_mono (s₂ := F ⁻¹' PAᶜ ∪ F ⁻¹' PGᶜ) ?_) (measureReal_union_le _ _)
      intro u hu
      by_cases h : F u ∈ PA
      · exact Or.inr fun h' => hu ⟨h, h'⟩
      · exact Or.inl h
    rw [hAeq] at hPAc
    rw [hGeq] at hPGc
    linarith
  · intro B hB hBH
    have hBm : MeasurableSet (F ⁻¹' B) := hF hB
    have h1 := hPAb B hB fun x hx => (hBH hx).1
    have h2 := hPGb B hB fun x hx => (hBH hx).2
    have h3 := measureReal_union_add_inter (μ := μ) (s := F ⁻¹' B ∩ A') (hBm.inter hGm)
    have h4 : μ.real (F ⁻¹' B ∩ A' ∪ F ⁻¹' B ∩ G') ≤ μ.real (F ⁻¹' B) :=
      measureReal_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
    have h5 : μ.real (F ⁻¹' B ∩ A' ∩ (F ⁻¹' B ∩ G')) ≤ μ.real (F ⁻¹' B ∩ (A ∩ G)) :=
      measureReal_mono fun u hu => ⟨hu.1.1, hAsub hu.1.2, hGsub hu.2.2⟩
    linarith
end ConditionalChance
private theorem measurable_sampleBelow (ℓ : TorusLumps.StepParameters) (k : ℕ) :
    ∀ d n : ℕ, Measurable (sampleBelow ℓ k d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow ℓ k d (n * ℓ.side)).comp
      (@measurable_fst _ _ (markedSampleMeasurableSpace ℓ (k + d) (n * ℓ.side)) _)
private theorem measurable_outerData {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n] (T : StageTower ℓ)
    (k : ℕ) (o : TorusSite n) (R : ℕ) : Measurable (outerData T k o R) := by
  refine Measurable.prodMk ?_ measurable_snd
  refine measurable_pi_lambda _ fun b => ?_
  exact (measurable_pi_apply b.1.2).comp ((measurable_pi_apply b.1.1).comp measurable_fst)
private theorem measurableSet_support_disjoint {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
    (T : StageTower ℓ) (k : ℕ) (o : TorusSite n) (R : ℕ) (S : Finset (TorusSite n)) :
    MeasurableSet {q : OuterData T k o R | Disjoint q.2.1 S} := by
  have h : MeasurableSet {z : Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω) | Disjoint z.1 S} := by
    refine MeasurableSpace.measurableSet_iInf.mpr fun Y => ?_
    exact (MeasurableSet.const (Disjoint Y S) : MeasurableSet {_w : Y → (T.stage k).labels.Ω | Disjoint Y S})
  exact measurable_snd h
theorem goodOuterData_holds (h₁ : coldEventsLikelyStatement)
    (h₂ : sampleBelowLawStatement) (h₃ : StageStatesMeasurableStatement) :
    goodOuterDataStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hadm hr
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hadm (le_trans hr (min_le_left _ _))
  obtain ⟨y₂, Y₂⟩ := H₂ L hodd (le_trans (le_max_right _ _) hL) Tb hTa hTL hadm (le_trans hr (min_le_right _ _))
  refine ⟨max (max y₁ y₂) Tb.floorMin, ?_⟩
  intro y hy hexp hwil
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy₀ : Tb.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hfit := hadm.fits y hy₀
  have c1 := Y₁ y hy₁ hexp hwil
  have c2 := Y₂ y hy₂ hexp hwil
  intro κ₀ hκ₁ hκ₂
  obtain ⟨xs, xp, hcold⟩ := c1 κ₀ hκ₁ hκ₂
  refine ⟨xs, fun p => max (xp (p + 1)) 21, ?_⟩
  intro T β k s n _ o x R hdat hx hR hs
  have hst : IsTowerAtParameters Tb y T β (k + s) := by
    rw [hs, hR, hx]
    exact hdat.onFamily
  have hcoupling : ∀ j ≤ k + s, y ≤ flowCoupling (Tb.stepParameters y) β j := fun j hj => by
    have h : y ≤ (T.stage j).coupling := (hst.onFamily j hj).le_coupling
    rw [hst.coupling_eq j (by omega)] at h
    exact h
  obtain ⟨hprob, hmap⟩ := c2 T β k s n hst hdat.measurable hcoupling
  have hFd : Measurable (sampleBelow (Tb.stepParameters y) k s n) := measurable_sampleBelow _ k s n
  have hF : Measurable (outerDataOfSample T k s n o R) :=
    (measurable_outerData T k o R).comp ((h₃ _ hfit T k _).comp hFd)
  obtain ⟨H', hH'm, hH'c, hH'B⟩ := exists_set_condProb_inter_ge (markedSampleLaw T β (k + s) n) hF
    {u | IsColdOnBox o R (boxScale x) (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).1
      (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).2.1}
    {u | IsGoodSample (Tb.stepParameters y) k s (apexRadius (Tb.stepParameters y).side s R) (boxScale x)
      (Real.log x ^ 2 / x) s n u o}
  refine ⟨H' ∩ {q | Disjoint q.2.1 (supBall o (3 * R))}, hH'm.inter (measurableSet_support_disjoint T k o R _),
    fun q hq => hq.2, ?_, ?_⟩
  · intro p hp
    have hp' : max (xp (p + 1)) 21 ≤ x := hp
    have hxp : xp (p + 1) ≤ x := le_trans (le_max_left _ _) hp'
    have h21 : (21 : ℝ) ≤ x := le_trans (le_max_right _ _) hp'
    obtain ⟨hc, hg⟩ := hcold T β k s n o x R hdat hx hR hs (p + 1) hxp
    have hbelow : ∀ C : Set (MarkedSample (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side s n)),
        (markedSampleLaw T β (k + s) n).real (sampleBelow (Tb.stepParameters y) k s n ⁻¹' C) ≤
          (markedSampleLaw T β k (fineSide (Tb.stepParameters y).side s n)).real C := fun C => by
      rw [← hmap]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hFd.aemeasurable C)
    have hA : (markedSampleLaw T β (k + s) n).real
        {u | IsColdOnBox o R (boxScale x) (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).1
          (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).2.1}ᶜ ≤ x ^ (-((p + 1 : ℕ) : ℝ)) :=
      (hbelow {u | ¬ IsColdOnBox o R (boxScale x) (stageState T k _ u).1 (stageState T k _ u).2.1}).trans hc
    have hG : (markedSampleLaw T β (k + s) n).real
        {u | IsGoodSample (Tb.stepParameters y) k s (apexRadius (Tb.stepParameters y).side s R) (boxScale x)
          (Real.log x ^ 2 / x) s n u o}ᶜ ≤ x ^ (-((p + 1 : ℕ) : ℝ)) := hg
    have hleft : (markedSampleLaw T β (k + s) n).real
        (outerDataOfSample T k s n o R ⁻¹' (H' ∩ {q | Disjoint q.2.1 (supBall o (3 * R))})ᶜ) ≤
        (markedSampleLaw T β (k + s) n).real (outerDataOfSample T k s n o R ⁻¹' H'ᶜ) +
          (markedSampleLaw T β (k + s) n).real
            {u | IsColdOnBox o R (boxScale x) (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).1
              (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).2.1}ᶜ := by
      refine le_trans (measureReal_mono (s₂ := outerDataOfSample T k s n o R ⁻¹' H'ᶜ ∪
        {u | IsColdOnBox o R (boxScale x) (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).1
          (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).2.1}ᶜ) ?_) (measureReal_union_le _ _)
      intro u hu
      by_cases h : outerDataOfSample T k s n o R u ∈ H'
      · exact Or.inr fun hcu => hu ⟨h, hcu.1⟩
      · exact Or.inl h
    have hcompl := probReal_compl_eq_one_sub (μ := markedSampleLaw T β (k + s) n)
      (hF (hH'm.inter (measurableSet_support_disjoint T k o R (supBall o (3 * R)))))
    have hx0 : 0 < x := by linarith
    have hpow : x ^ (-((p + 1 : ℕ) : ℝ)) = x ^ (-(p : ℝ)) / x := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hx0, Real.rpow_neg_one, div_eq_mul_inv]
    have ht : 0 < x ^ (-(p : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hsmall : 21 * (x ^ (-(p : ℝ)) / x) ≤ x ^ (-(p : ℝ)) := by
      rw [mul_div_assoc', div_le_iff₀ hx0]
      nlinarith
    rw [hpow] at hA hG
    show 1 - x ^ (-(p : ℝ)) ≤ (markedSampleLaw T β (k + s) n).real
      (outerDataOfSample T k s n o R ⁻¹' (H' ∩ {q | Disjoint q.2.1 (supBall o (3 * R))}))
    rw [Set.preimage_compl] at hleft
    linarith
  · intro B hB hBH
    exact hH'B B hB fun q hq => (hBH hq).1
end YangMills.Construction.BoxGaussian
end
