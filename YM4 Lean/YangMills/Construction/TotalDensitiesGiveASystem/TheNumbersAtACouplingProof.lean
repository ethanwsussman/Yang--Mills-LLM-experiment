import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfALimitAlongToriProof
import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfALimitAlongTori
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.ListOfALimitOnATorus
import YangMills.Construction.TotalDensitiesGiveASystem.MoreAtTheVolumeFirstLimits
import YangMills.Construction.TotalDensitiesGiveASystem.TheBoundsAtTheData
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawsAtEveryShape
import YangMills.Construction.TotalDensitiesGiveASystem.TheNumbersAtACoupling
import YangMills.Construction.TotalDensitiesGiveASystem.TheShortDistanceLawIsNotGaussian
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopAtTheExpansion
import YangMills.Construction.TotalDensitiesGiveASystem.WeightedNormsGrowWithTheirIndex
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open SystemsWithFiveBounds TestFunctions
open ConfigSpace (FlatSequence)
private def transportPairs {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L') (hP : ∀ K β, P K β → P' K β)
    (Q : PairSequence L P) : PairSequence L' P' := by
  subst h
  exact ⟨Q.cutoff, Q.tendsto_cutoff, Q.coupling, fun j => hP _ _ (Q.pair j), Q.state, Q.isLimit⟩
private theorem transportPairs_defines {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L') (hP : ∀ K β, P K β → P' K β)
    (Q : PairSequence L P) (S : LimitTheorem.CumulantFamily) :
    (transportPairs h hP Q).Defines S ↔ Q.Defines S := by
  subst h
  exact Iff.rfl
private theorem transportPairs_conclusion {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L') (hP : ∀ K β, P K β → P' K β)
    (Q : PairSequence L P) (S : LimitTheorem.CumulantFamily) {M ϑ d₀ : ℝ} {ηBar : ℝ → ℝ} {K : LimitConstants}
    (hA : ErgodicDecompositionConclusion M ϑ d₀ ηBar K (transportPairs h hP Q) S) :
    ErgodicDecompositionConclusion M ϑ d₀ ηBar K Q S := by
  subst h
  exact { limit := { hA.limit with states := hA.limit.states, tori := hA.limit.tori }
          decomposition := hA.decomposition
          onePoint := hA.onePoint
          components := hA.components }
private theorem le_of_zpow_neg_two_le {g top : ℝ} (hg : 0 < g) (ht : 0 < top) (h : top ^ (-2 : ℤ) ≤ g ^ (-2 : ℤ)) :
    g ≤ top := by
  by_contra hlt
  have h2 : top ^ 2 < g ^ 2 := by nlinarith
  have h3 : (g ^ 2)⁻¹ < (top ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) h2
  have e : ∀ u : ℝ, u ^ (-2 : ℤ) = (u ^ 2)⁻¹ := fun u => by
    rw [zpow_neg]; norm_cast
  rw [e, e] at h
  linarith
private def maxConstants (C₀ C₁ : LimitConstants) (k : ℕ) (c₁ c₂ κ : ℝ) : LimitConstants where
  localBound n d R := max (C₀.localBound n d R) (C₁.localBound n d R)
  globalPrefactor d R := max (C₀.globalPrefactor d R) (C₁.globalPrefactor d R)
  globalBase R := max (C₀.globalBase R) (C₁.globalBase R)
  globalExp := max C₀.globalExp C₁.globalExp
  schwartzOrder := max C₀.schwartzOrder k
  schwartzPrefactor := max C₀.schwartzPrefactor c₁
  schwartzBase := max C₀.schwartzBase c₂
  schwartzExp := max C₀.schwartzExp κ
  clusterConst := C₀.clusterConst
  clusterRadius := C₀.clusterRadius
private theorem maxConstants_valid {C₀ C₁ : LimitConstants} {k : ℕ} {c₁ c₂ κ : ℝ} (h₀ : C₀.Valid)
    (h₁ : C₁.Valid) : (maxConstants C₀ C₁ k c₁ c₂ κ).Valid where
  globalExp_nonneg := le_max_of_le_left h₀.globalExp_nonneg
  localBound_antitone n hn R hR := fun _ ha _ hb hab =>
    max_le_max (h₀.localBound_antitone n hn R hR ha hb hab) (h₁.localBound_antitone n hn R hR ha hb hab)
  localBound_pos n hn d R hd hR := lt_max_of_lt_left (h₀.localBound_pos n hn d R hd hR)
  globalPrefactor_pos d R hd hR := lt_max_of_lt_left (h₀.globalPrefactor_pos d R hd hR)
  globalBase_pos R hR := lt_max_of_lt_left (h₀.globalBase_pos R hR)
  schwartzOrder_pos := lt_of_lt_of_le h₀.schwartzOrder_pos (le_max_left _ _)
  schwartzPrefactor_pos := lt_max_of_lt_left h₀.schwartzPrefactor_pos
  schwartzBase_pos := lt_max_of_lt_left h₀.schwartzBase_pos
  schwartzExp_pos := lt_max_of_lt_left h₀.schwartzExp_pos
  clusterConst_pos := h₀.clusterConst_pos
  clusterRadius_pos := h₀.clusterRadius_pos
private theorem factorial_growth_mono {A A' B B' κ κ' : ℝ} (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAA : A ≤ A') (hBB : B ≤ B')
    (hκ : κ ≤ κ') : A * B ^ n * (n.factorial : ℝ) ^ κ ≤ A' * B' ^ n * (n.factorial : ℝ) ^ κ' := by
  have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hf : (n.factorial : ℝ) ^ κ ≤ (n.factorial : ℝ) ^ κ' := Real.rpow_le_rpow_of_exponent_le h1 hκ
  have hp : 0 ≤ (n.factorial : ℝ) ^ κ := Real.rpow_nonneg (by linarith) _
  have hBn : B ^ n ≤ B' ^ n := pow_le_pow_left₀ hB hBB n
  have hA' : 0 ≤ A' := le_trans hA hAA
  have hB' : 0 ≤ B' := le_trans hB hBB
  exact mul_le_mul (mul_le_mul hAA hBn (by positivity) hA') hf hp (by positivity)
private theorem prod_sharpNormR4_nonneg {n : ℕ} (M : ℝ) (f : Fin n → InfiniteLattice.AmbientSpace → ℝ) :
    0 ≤ ∏ i, sharpNormR4 M (f i) :=
  Finset.prod_nonneg fun _ _ => le_trans (Real.iSup_nonneg fun _ => norm_nonneg _) (le_max_left _ _)
private theorem localCumulantBounds_maxConstants {M : ℝ} {C₀ C₁ : LimitConstants} {k : ℕ} {c₁ c₂ κ : ℝ}
    (h₀ : C₀.Valid) {σ : SeparatedTuples.TupleFunctional} (h : SystemsWithFiveBounds.LocalCumulantBounds M C₀ σ) :
    SystemsWithFiveBounds.LocalCumulantBounds M (maxConstants C₀ C₁ k c₁ c₂ κ) σ := fun n hn R hR d hd X hX hs => by
  have hp : 0 ≤ ∏ i, sharpNormR4 M (X.1 i) := prod_sharpNormR4_nonneg M X.1
  obtain ⟨a, b⟩ := h n hn R hR d hd X hX hs
  refine ⟨le_trans a (mul_le_mul_of_nonneg_right (le_max_left _ _) hp), le_trans b ?_⟩
  exact mul_le_mul_of_nonneg_right (factorial_growth_mono n (h₀.globalPrefactor_pos d R hd hR).le
    (h₀.globalBase_pos R hR).le (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)) hp
private theorem satisfiesGrowth_mono (hW : TotalDensitiesGiveASystem.BracketNormMonotone) {T : FlatSequence} {k k' : ℕ}
    {c c' C C' κ κ' : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hk : k ≤ k') (hcc : c ≤ c') (hCC : C ≤ C') (hκ : κ ≤ κ')
    (h : SatisfiesGrowth T k c C κ) : SatisfiesGrowth T k' c' C' κ' := by
  exact _root_.YangMills.DeltaSharedProofs.p501308 hW hc hC hk hcc hCC hκ h
private theorem satisfiesGrowth_maxConstants (hW : TotalDensitiesGiveASystem.BracketNormMonotone) {C₀ C₁ : LimitConstants}
    {k : ℕ} {c₁ c₂ κ : ℝ} (h₀ : C₀.Valid) {T : FlatSequence}
    (h : SatisfiesGrowth T C₀.schwartzOrder C₀.schwartzPrefactor C₀.schwartzBase C₀.schwartzExp) :
    SatisfiesGrowth T (maxConstants C₀ C₁ k c₁ c₂ κ).schwartzOrder (maxConstants C₀ C₁ k c₁ c₂ κ).schwartzPrefactor
      (maxConstants C₀ C₁ k c₁ c₂ κ).schwartzBase (maxConstants C₀ C₁ k c₁ c₂ κ).schwartzExp :=
  satisfiesGrowth_mono hW h₀.schwartzPrefactor_pos.le h₀.schwartzBase_pos.le (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (le_max_left _ _) h
private theorem satisfiesTwoPointLaw_mono {η₁ η : ℝ → ℝ} {d t : ℝ} {f h : InfiniteLattice.AmbientSpace → ℝ}
    (h₁ : η₁ d ∈ Icc (0 : ℝ) (1 / 3)) (h₂ : η d ∈ Icc (0 : ℝ) (1 / 3)) (hle : η₁ d ≤ η d)
    (hO : SatisfiesTwoPointLaw η₁ d t f h) : SatisfiesTwoPointLaw η d t f h := by
  obtain ⟨e, he, a, b⟩ := hO
  refine ⟨e, he, le_trans ?_ a, le_trans b ?_⟩
  · have : (1 - η d) ^ 4 ≤ (1 - η₁ d) ^ 4 := pow_le_pow_left₀ (by linarith [h₂.2]) (by linarith) 4
    linarith
  · have : (1 + η₁ d) ^ 4 ≤ (1 + η d) ^ 4 := pow_le_pow_left₀ (by linarith [h₁.1]) (by linarith) 4
    linarith
private theorem twoPointLawHolds_mono {ϑ d₁ d₀ : ℝ} {η₁ η : ℝ → ℝ} {σ : SeparatedTuples.TupleFunctional} (hd : d₀ ≤ d₁)
    (h₁ : ∀ d ∈ Ioc 0 d₁, η₁ d ∈ Icc (0 : ℝ) (1 / 3)) (h₂ : ∀ d ∈ Ioc 0 d₀, η d ∈ Icc (0 : ℝ) (1 / 3))
    (hle : ∀ d ∈ Ioc 0 d₀, η₁ d ≤ η d) (h : TwoPointLawHolds ϑ d₁ η₁ σ) : TwoPointLawHolds ϑ d₀ η σ :=
  fun d hdm f k hp a b => by
    have hd₁ : d ∈ Ioc 0 d₁ := ⟨hdm.1, le_trans hdm.2 hd⟩
    obtain ⟨X, hX, hO⟩ := h d hd₁ f k hp a b
    exact ⟨X, hX, satisfiesTwoPointLaw_mono (h₁ d hd₁) (h₂ d hdm) (hle d hdm) hO⟩
private theorem conclusion_maxConstants (hW : TotalDensitiesGiveASystem.BracketNormMonotone) {ϑ₀ ϑ d₀' d₁ d₀ : ℝ}
    {η₀ η₁ η : ℝ → ℝ} {C₀ C₁ C' : LimitConstants} {k : ℕ} {c₁ c₂ κ : ℝ} {L : ℕ} {IsPair : ℕ+ → ℝ → Prop}
    {Q : PairSequence L IsPair} {S : LimitTheorem.CumulantFamily} (h₀ : C₀.Valid) (hd : d₀ ≤ d₁)
    (h₁ : ∀ d ∈ Ioc 0 d₁, η₁ d ∈ Icc (0 : ℝ) (1 / 3)) (h₂ : ∀ d ∈ Ioc 0 d₀, η d ∈ Icc (0 : ℝ) (1 / 3))
    (hle : ∀ d ∈ Ioc 0 d₀, η₁ d ≤ η d)
    (A₀ : ErgodicDecompositionConclusion 1 ϑ₀ d₀' η₀ C₀ Q S) (A₁ : ErgodicDecompositionConclusion 1 ϑ d₁ η₁ C' Q S) :
    ErgodicDecompositionConclusion 1 ϑ d₀ η (maxConstants C₀ C₁ k c₁ c₂ κ) Q S where
  limit :=
    { A₀.limit with
      conditions :=
        { localBounds := localCumulantBounds_maxConstants h₀ A₀.limit.conditions.localBounds
          growth := by
            obtain ⟨T, hT, hB⟩ := A₀.limit.conditions.growth
            exact ⟨T, hT, satisfiesGrowth_maxConstants hW h₀ hB⟩
          reconstruction := A₀.limit.conditions.reconstruction
          twoPointLaw := twoPointLawHolds_mono hd h₁ h₂ hle A₁.limit.conditions.twoPointLaw
          cumulants_eq := A₀.limit.conditions.cumulants_eq
          twoPoint_pos := fun d hdm X hX =>
            A₁.limit.conditions.twoPoint_pos d ⟨hdm.1, le_trans hdm.2 hd⟩ X hX
          two_le_rank := A₀.limit.conditions.two_le_rank } }
  decomposition := A₀.decomposition
  onePoint := A₀.onePoint
  components := fun A hA ξ =>
    { symmetries := (A₀.components A hA ξ).symmetries
      localBounds := localCumulantBounds_maxConstants h₀ (A₀.components A hA ξ).localBounds
      growth := by
        obtain ⟨T, hT, hB⟩ := (A₀.components A hA ξ).growth
        exact ⟨T, hT, satisfiesGrowth_maxConstants hW h₀ hB⟩
      twoPointLaw := twoPointLawHolds_mono hd h₁ h₂ hle (A₁.components A hA ξ).twoPointLaw
      reconstruction := (A₀.components A hA ξ).reconstruction
      clustering := (A₀.components A hA ξ).clustering
      componentOS := fun T hT => by
        have h6 := (A₀.components A hA ξ).componentOS T hT
        exact { h6 with growth := satisfiesGrowth_maxConstants hW h₀ h6.growth }
      fieldData := (A₀.components A hA ξ).fieldData }
theorem couplingConstantsExist (hTop : topAtAdmissibleParamsStatement) (hB : CumulantBoundsExist)
    (hList : TorusLimitsHaveProperties) (hMore : VolumeFirstLimitExtras)
    (hNot : ShortDistanceNonGaussianAtEveryShape.Statement) (hLaws : LawsAtEveryShape)
    (hAlong : GrowingTorusLimitsSatisfyConditions)
    (hW : TotalDensitiesGiveASystem.BracketNormMonotone) : CouplingConstantsExist := by
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
    (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and hTop hB) hList) hMore)
    hLaws) hAlong) fun T y hDr hA => ?_
  obtain ⟨⟨⟨⟨⟨⟨-, -, -, hw⟩, yB, fB⟩, yL, fL⟩, yM, fM⟩, c, fLaws⟩, yA, fA⟩ := hA
  obtain ⟨c₅', lam', top, -, -, ht, hg₀, hY⟩ := hw (2 * T.B) le_rfl
  refine ⟨c, fun c₅ hc₅ => ?_⟩
  obtain ⟨yS, fS⟩ := fLaws c₅ hc₅
  refine ⟨max (top ^ (-2 : ℤ)) (max yB (max yL (max yM (max yS yA)))), fun g hg hy => ?_⟩
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅⟩ : top ^ (-2 : ℤ) ≤ g ^ (-2 : ℤ) ∧ yB ≤ g ^ (-2 : ℤ) ∧ yL ≤ g ^ (-2 : ℤ) ∧
      yM ≤ g ^ (-2 : ℤ) ∧ yS ≤ g ^ (-2 : ℤ) ∧ yA ≤ g ^ (-2 : ℤ) := by
    simpa only [max_le_iff] using hy
  have hgt : g ∈ Ioc 0 top := ⟨hg, le_of_zpow_neg_two_le hg ht a₀⟩
  obtain ⟨-, -, hJ, -⟩ := hg₀ g hgt
  have toPoint : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    have h' : β ∈ SequencePassage.definedPassageWindow (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := h
    rw [(hJ K).1] at h'
    exact h'
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  obtain ⟨Y₀, hY₀, -, K₀, hK₀⟩ := hY 0 1 hone
  have hg₀' : g ∈ Ioc 0 Y₀.top := by rw [hY₀.top_eq]; exact hgt
  obtain ⟨s₀, -, -, k₀⟩ := hK₀ g hg₀'
  obtain ⟨cV, Cn, C₁, s₁, tb, pb⟩ := fB g hg a₁
  obtain ⟨k, c₁, c₂, κ, fAl⟩ := fA g hg a₅
  set C := maxConstants (K₀ g) C₁ k c₁ c₂ κ with hC
  have sC : C.Valid := maxConstants_valid s₀ s₁
  have pbC : TotalDensitySystem.LocalCumulantBounds (T.stepParameters y) (2 * T.B) g C := by
    refine ⟨fun K β hp m n hn R d hR hd f h₁ h₂ h₃ => ?_, fun K β hp ν hν n hn R d hR hd f h₁ h₂ h₃ => ?_⟩
    · have hq : 0 ≤ ∏ i, sharpNormTorus 1 (f i) :=
        Finset.prod_nonneg fun i _ => le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
      obtain ⟨u, v⟩ := pb.onTori K β hp m n hn R d hR hd f h₁ h₂ h₃
      refine ⟨le_trans u (mul_le_mul_of_nonneg_right (le_max_right _ _) hq), le_trans v ?_⟩
      exact mul_le_mul_of_nonneg_right (factorial_growth_mono n (s₁.globalPrefactor_pos d R hd hR).le
        (s₁.globalBase_pos R hR).le (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)) hq
    · have hq := prod_sharpNormR4_nonneg 1 f
      obtain ⟨u, v⟩ := pb.inGibbsStates K β hp ν hν n hn R d hR hd f h₁ h₂ h₃
      refine ⟨le_trans u (mul_le_mul_of_nonneg_right (le_max_right _ _) hq), le_trans v ?_⟩
      exact mul_le_mul_of_nonneg_right (factorial_growth_mono n (s₁.globalPrefactor_pos d R hd hR).le
        (s₁.globalBase_pos R hR).le (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)) hq
  refine ⟨cV, Cn, C, sC, tb, pbC, fun s S hs hl => fL g hg a₂ cV Cn C sC tb pbC s S hs hl, fM g hg a₃,
    fun ϑ hϑ => ⟨hNot ϑ hϑ, fun room hroom => ?_⟩⟩
  obtain ⟨Y, hYs, -, Kϑ, hKϑ⟩ := hY 0 ϑ hϑ
  have hgY : g ∈ Ioc 0 Y.top := by rw [hYs.top_eq]; exact hgt
  have sideY := Y.consts_admissible g hgY
  obtain ⟨-, -, -, kϑ⟩ := hKϑ g hgY
  have hmod : IsLawModulus (Y.consts g).lawScale (Y.consts g).lawError :=
    ⟨sideY.lawError_monotoneOn, sideY.lawError_mem, sideY.lawError_tendsto⟩
  obtain ⟨d₀, ηBar, εBar, ζ, K₀', d₄, hd, hle, law, lim, hd₄, four, fourLim⟩ :=
    fS g hg a₄ ϑ hϑ room hroom (Y.consts g).lawScale (Y.consts g).lawError sideY.lawScale_mem.1 hmod
  have hη : ∀ d ∈ Ioc 0 d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3) := law.sharp_on_tori.ηBar_mem
  have hM₀ : Y₀.M = 1 := by rw [hY₀.scale_eq]; simp
  have hM : Y.M = 1 := by rw [hYs.scale_eq]; simp
  have hL₀ := hY₀.side_eq
  have hL := hYs.side_eq
  have toY₀ : ∀ K β, TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → Y₀.IsPair g K β :=
    fun K β h => (hY₀.isPair_iff g hgt K β).2 (toPoint K β h)
  have toY : ∀ K β, TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → Y.IsPair g K β :=
    fun K β h => (hYs.isPair_iff g hgt K β).2 (toPoint K β h)
  have conclusions : ∀ (Q : PairSequence (T.stepParameters y).side
      (TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g)) (S : LimitTheorem.CumulantFamily),
      Q.Defines S → ErgodicDecompositionConclusion 1 ϑ d₀ ηBar C Q S := fun Q S hQ => by
    have A₀ := k₀ (transportPairs hL₀.symm toY₀ Q) S ((transportPairs_defines _ _ _ _).2 hQ)
    have A₁ := kϑ (transportPairs hL.symm toY Q) S ((transportPairs_defines _ _ _ _).2 hQ)
    rw [hM₀] at A₀
    rw [hM] at A₁
    exact conclusion_maxConstants hW s₀ hd sideY.lawError_mem hη hle (transportPairs_conclusion _ _ _ _ A₀)
      (transportPairs_conclusion _ _ _ _ A₁)
  refine ⟨d₀, ηBar, εBar, ζ, K₀', d₄, ⟨law, lim, fun S hS => ?_, hd₄, four, fourLim, conclusions⟩⟩
  rcases hS with hS | ⟨Q, hQ⟩
  · exact fAl C sC (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) pbC ϑ d₀ ηBar εBar hϑ
      lim law.cutoff_mem hη (fun d hd' => law.sharp_on_tori.εBar_mem 0 d hd') S hS
  · have A := conclusions Q S hQ
    exact ⟨A.limit.symmetries, A.limit.axialPositive, A.limit.distributions, A.limit.conditions⟩
end YangMills.Construction.TotalDensities
end
