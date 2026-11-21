import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsUpOneStep
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupportProof
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.TransfersOffTheWalk.ProductsLevelByLevel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters WeightedResponses ResponseInTheExpansion FreeEnergies ClusterExpansionOfAStep
section Sites
variable {L : ℕ} [NeZero L]
private theorem weightSupportSites_of_depth_eq (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s)
    (m : ℕ) [NeZero m] :
    weightSupportSites L t m (fineWeight f (fineSide L t m)) = functionSites L f s m := by
  subst ht
  rfl
private theorem weightNorm_of_depth_eq (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s)
    (m : ℕ) [NeZero m] :
    weightNorm L t (fineWeight f (fineSide L t m)) = weightNorm L s (fineWeight f (fineSide L s m)) := by
  subst ht
  rfl
open Classical in
private theorem image_parentBlock_weightSupportSites {t n : ℕ} [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (weightSupportSites L t (n * L) f).image (parentBlock L) = weightSupportSites L (t + 1) n f := by apply _root_.YangMills.SharedProofs.p19152 <;> assumption
private theorem weightLipschitz_le_succ (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by apply _root_.YangMills.SharedProofs.p58015 <;> assumption
private theorem weightNorm_le_succ (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ hL t h)
private theorem exists_mem_fineBlock (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (c : TorusSite (fineSide L t n)),
    ∃ y : TorusSite n, c ∈ fineBlock L t n y := by apply _root_.YangMills.SharedProofs.p68008 <;> assumption
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)),
      blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
open Classical in
private theorem image_parentBlock_functionSites {f : FinePlaquetteFunction} {t n : ℕ} [NeZero n] :
    (functionSites L f t (n * L)).image (parentBlock L) = functionSites L f (t + 1) n :=
  image_parentBlock_weightSupportSites (fineWeight f (fineSide L (t + 1) n))
private theorem fineWeight_eq_zero_of_functionSites_empty {f : FinePlaquetteFunction} {t n : ℕ} [NeZero n]
    (h : functionSites L f t n = ∅) {p : TorusPlaquette (fineSide L t n)} (hp : p.2.1 < p.2.2) :
    fineWeight f (fineSide L t n) p = 0 := by
  classical
  by_contra hne
  obtain ⟨y, hy⟩ := exists_mem_fineBlock L t n p.1
  have hm : y ∈ functionSites L f t n := by
    simp only [functionSites, weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, ⟨hp, p.1, by simp [plaquetteVertices], hy⟩, hne⟩
  rw [h] at hm
  simp at hm
private theorem functionSites_empty_of_succ {f : FinePlaquetteFunction} {t n : ℕ} [NeZero n]
    (h : functionSites L f (t + 1) n = ∅) : functionSites L f t (n * L) = ∅ := by
  classical
  have hs := image_parentBlock_weightSupportSites (L := L) (t := t) (n := n)
    (fineWeight f (fineSide L (t + 1) n))
  have h1 : weightSupportSites L (t + 1) n (fineWeight f (fineSide L (t + 1) n)) = ∅ := h
  rw [h1] at hs
  exact Finset.image_eq_empty.1 hs
end Sites
section Empty
variable {ℓ : StepParameters} {T : StageTower ℓ}
private theorem caseMean_const_zero {R : StepSetup} {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) (V : TorusField n)
    (q : CoarseState R n) :
    caseMean R C V q (fun _ _ _ _ _ => 0) = 0 := by apply _root_.YangMills.SharedProofs.p64354 <;> assumption
private theorem cumulativeSource_eq_zero (al : ℕ → ℝ) (f : FinePlaquetteFunction) :
    ∀ (s n : ℕ) [NeZero n], functionSites ℓ.side f s n = ∅ →
      ∀ u, cumulativeSource T al s n (fineWeight f _) u = 0 := by
  intro s
  induction s with
  | zero => intro n _ _ u; rfl
  | succ s ih =>
    intro n _ h u
    have h1 := ih (n * ℓ.side) (functionSites_empty_of_succ h) u.1
    have h2 : sourceTerm T al s n (fineWeight f _) u = 0 := by
      unfold sourceTerm stepSourceTerm
      rw [Finset.sum_eq_zero, mul_zero]
      intro Y _
      have h0 : blockMean ℓ.side (s + 1) n Y (fineWeight f (fineSide ℓ.side (s + 1) n)) = 0 := by
        by_contra hne
        have hm := mem_weightSupportSites_of_blockMean_ne_zero ℓ.side (s + 1) n Y _ hne
        have h' : weightSupportSites ℓ.side (s + 1) n (fineWeight f (fineSide ℓ.side (s + 1) n)) = ∅ := h
        rw [h'] at hm
        simp at hm
      rw [h0, zero_mul]
    show cumulativeSource T al s (n * ℓ.side) (fineWeight f _) u.1 + sourceTerm T al s n (fineWeight f _) u = 0
    rw [h2, add_zero]
    exact h1
private theorem centering_eq_zero (S : ScoredStageTower T) (f : FinePlaquetteFunction)
    (hlevel : ∀ u, (T.stage u).depth = u) :
    ∀ (s n : ℕ) [NeZero n], functionSites ℓ.side f s n = ∅ → centering S f s n = 0 := by
  intro s
  induction s with
  | zero => intro n _ _; rfl
  | succ s ih =>
    intro n _ h
    have h1 := ih (n * ℓ.side) (functionSites_empty_of_succ h)
    have hs1 := weightSupportSites_of_depth_eq ℓ.side f (hlevel s) (n * ℓ.side)
    have hs2 := weightSupportSites_of_depth_eq ℓ.side f (congrArg (· + 1) (hlevel s)) n
    have h2 : supportResponseSum (S.setup s) (trivialField n) (fineWeight f _) = fun _ _ _ _ _ => 0 := by
      funext W Yt ωt bad b
      show ∑ y ∈ weightSupportSites ℓ.side (T.stage s).depth (n * ℓ.side) (fineWeight f _),
          centeredHullResponse (S.setup s).cold (S.setup s).hull (n * ℓ.side) y W Yt ωt (fineWeight f _) +
          ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y ∈ weightSupportSites ℓ.side ((T.stage s).depth + 1) n
            (fineWeight f _),
          blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) *
            blockBondScores (R := (T.stage s).toStepSetup) W (trivialField n) b Y = 0
      rw [hs1, hs2, h, functionSites_empty_of_succ h]
      simp
    show centering S f s (n * ℓ.side) + caseMean (T.stage s).toStepSetup (n := n) ∅ (trivialField n)
      (emptyCoarseState _) (supportResponseSum (S.setup s) (trivialField n) (fineWeight f _)) = 0
    rw [h2, caseMean_const_zero, h1, add_zero]
private theorem completedCentered_eq_zero (S : ScoredStageTower T) (f : FinePlaquetteFunction)
    (hlevel : ∀ u, (T.stage u).depth = u) (s n : ℕ) [NeZero n]
    (h : functionSites ℓ.side f s n = ∅) (u : MarkedSample ℓ s n) : completedCentered S f s n u = 0 := by
  have h1 : curvatureObservable (fineWeight f (fineSide ℓ.side s n)) (bottomField ℓ s n u) = 0 := by
    unfold curvatureObservable
    refine Finset.sum_eq_zero fun p hp => ?_
    have hord : p.2.1 < p.2.2 := by
      simp only [plaquettesIn, Finset.mem_filter] at hp
      exact hp.2.1
    rw [fineWeight_eq_zero_of_functionSites_empty h hord, zero_mul]
  show curvatureObservable _ _ + cumulativeSource T S.coeffs s n _ u - centering S f s n = 0
  rw [h1, cumulativeSource_eq_zero _ f s n h u, centering_eq_zero S f hlevel s n h]
  simp
end Empty
private theorem decorrelation_bound_factor {ι : Type} (I : Finset ι) {Cq Cb S₂ E k : ℝ} (a b : ι → ℝ)
    (hC : Cq ≤ Cb) (hE : 0 ≤ E) (hk : 0 ≤ k) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Cq * S₂ ^ 2 * E * ∏ i ∈ I, (4 * (k * a i) * b i) ≤
      (Cb * S₂ ^ 2 * E * ∏ i ∈ I, (4 * (k * a i))) * ∏ i ∈ I, b i := by
  rw [Finset.prod_mul_distrib]
  have hP : 0 ≤ (∏ i ∈ I, (4 * (k * a i))) * ∏ i ∈ I, b i :=
    mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (mul_nonneg hk (ha i)))
      (Finset.prod_nonneg fun i _ => hb i)
  have h1 : Cq * S₂ ^ 2 * E ≤ Cb * S₂ ^ 2 * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg _)) hE
  calc _ ≤ Cb * S₂ ^ 2 * E * ((∏ i ∈ I, (4 * (k * a i))) * ∏ i ∈ I, b i) := mul_le_mul_of_nonneg_right h1 hP
    _ = _ := by ring
private theorem one_le_meanSiteScore {n : ℕ} [NeZero n] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    (B Y : Finset (TorusSite n)) (ω : Y → Ω) :
    1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p16546 <;> assumption
theorem productInductionStatement_holds (hU : ConditionalProductStepBound) (hH : conditionalProductMeansStatement)
    (hO : severalSupportsStepDecorrelation) (hM : productMeanScoreStepBound) (hR : expansionAlongFlow) :
    productInductionStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hU a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hH a ha
  obtain ⟨r₃, hr₃, H₃⟩ := hO
  obtain ⟨r₄, hr₄, H₄⟩ := hM
  refine ⟨max L₁ L₂, fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)), max C₁ C₂,
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hOn
    (hrt.trans ((min_le_left _ _).trans (min_le_left _ _))) ((le_max_left _ _).trans hCd) K
  obtain ⟨y₂, Y₂⟩ := H₂ L hodd ((le_max_right _ _).trans hL) Tb hTa hTL hD hCS hOn
    (hrt.trans ((min_le_left _ _).trans (min_le_right _ _))) ((le_max_right _ _).trans hCd) K
  obtain ⟨y₃, Y₃⟩ := H₃ Tb hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₄, Y₄⟩ := H₄ Tb hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  refine ⟨max (max y₁ y₂) (max y₃ (max y₄ Tb.floorMin)), fun y hy hRS p => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₄ : y₄ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₀ : Tb.floorMin ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hfit := hD.fits y hy₀
  have hL1 : 1 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hD.L_ge
  choose Cq hCq using Y₃
  refine ⟨∑ q ∈ Finset.range (p + 1), |Cq q|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro T S β f hSK
  have hC₀ : ∀ {tp : ℕ}, S.FollowsFlow β tp → 0 ≤ K.C₀ := by
    intro tp hOR
    have hfitK := (hOR.isAdmissible 0 (Nat.zero_le tp)).params_admissible
    have hk : (S.setup 0).responseParams = K := (hOR.params_eq 0).trans hSK
    rw [hk] at hfitK
    have e := hfitK.C₀_eq
    have h1 := hfitK.N₀_nonneg
    have h2 := hfitK.Kc_ge
    have h3 : 1 ≤ (Tb.stepParameters y).coupling := hD.a_ge
    have h4 : ((T.stage 0).toStepSetup).params = Tb.stepParameters y := rfl
    rw [e, h4]
    linarith
  have hlevel : ∀ {tp : ℕ}, S.FollowsFlow β tp → ∀ u, (T.stage u).depth = u := by
    intro tp hOR u
    induction u with
    | zero => exact hOR.startsAtWilson.depth_eq
    | succ u ih =>
      show (T.stage u).depth + 1 = u + 1
      rw [ih]
  refine ⟨?_, ?_, ?_⟩
  · intro s n _ I hOR hRR hbs
    exact (Y₂ y hy₂ hRS β T S s hSK hOR hRR p f I n hbs).1 s
  · intro n _ I hOR hRR hbs
    exact (Y₂ y hy₂ hRS β T S 0 hSK hOR hRR p f I n hbs).2
  · intro t n _ I D Err hOR hRR hbs hsz h2 h8 hsep hErr0 hErr
    have hC0 := hC₀ hOR
    have hlev := hlevel hOR
    have hst := hOR.isFlowStep t (Nat.le_succ t)
    have hscore1 : ∀ w, 0 ≤ (S.setup (t + 1)).score w := (hOR.isAdmissible (t + 1) le_rfl).price.nonneg
    have hN : ∀ x : MarkedSample (Tb.stepParameters y) (t + 1) n,
        0 ≤ ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n x) :=
      fun x => Finset.prod_nonneg fun i _ => zero_le_one.trans (one_le_meanSiteScore hscore1 _ _ _)
    have hsum0 : 0 ≤ ∑ q ∈ Finset.range (p + 1), |Cq q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hfour : 0 ≤ ∏ i ∈ I, (4 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
        (n * (Tb.stepParameters y).side)).card : ℝ))) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (mul_nonneg hC0 (Nat.cast_nonneg _))
    have htwo : ∀ J : Finset (Fin p), 0 ≤ ∏ i ∈ I \ J, (2 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
        (n * (Tb.stepParameters y).side)).card : ℝ))) :=
      fun J => Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (mul_nonneg hC0 (Nat.cast_nonneg _))
    by_cases hne : ∀ i ∈ I, (functionSites (Tb.stepParameters y).side (f i) (t + 1) n).Nonempty
    · have hKt : (S.setup t).responseParams = K := (hOR.params_eq t).trans hSK
      have hAT : OnStepParameters Tb y (S.setup t) := by
        refine ⟨hst.onFamily, ?_, hOR.isAdmissible t (Nat.le_succ t), ?_⟩
        · rw [hst.nextCoupling_eq, hst.coupling_eq]
          exact (hR _ hRS β (t + 1) hRR).2 t (Nat.lt_succ_self t)
        · rw [hOR.params_eq t]
          exact hOR.N₀_eq
      have hsz' : ∀ i, weightNorm (Tb.stepParameters y).side t (fineWeight (f i) (fineSide (Tb.stepParameters y).side t
          (n * (Tb.stepParameters y).side))) ≤ 1 :=
        fun i => (weightNorm_le_succ hL1 t _).trans (hsz i)
      have hlt := hlev t
      have hstored : ∀ w, 0 ≤ coarseLabelScore (L := (Tb.stepParameters y).side) S.params.s₁ (S.setup t).score w := by
        have h := hscore1
        rw [hOR.score_succ t (Nat.lt_succ_self t)] at h
        exact h
      have hs1 : ∀ i, weightSupportSites (Tb.stepParameters y).side (T.stage t).depth (n * (Tb.stepParameters y).side)
          (fineWeight (f i) (fineSide (Tb.stepParameters y).side (T.stage t).depth (n * (Tb.stepParameters y).side))) =
          functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side) :=
        fun i => weightSupportSites_of_depth_eq _ (f i) hlt _
      have hs2 : ∀ i, weightSupportSites (Tb.stepParameters y).side ((T.stage t).depth + 1) n
          (fineWeight (f i) (fineSide (Tb.stepParameters y).side ((T.stage t).depth + 1) n)) =
          functionSites (Tb.stepParameters y).side (f i) (t + 1) n :=
        fun i => weightSupportSites_of_depth_eq _ (f i) (congrArg (· + 1) hlt) n
      have hx : (T.stage t).coupling = flowCoupling (Tb.stepParameters y) β t := hst.coupling_eq
      have hcard : I.card ≤ p := by simpa using Finset.card_le_univ I
      obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = (∑ q ∈ Finset.range (p + 1), |Cq q|) *
          (∑ i ∈ I, ((functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)).card : ℝ)) ^ 2 *
          Real.exp (-((Tb.stepParameters y).rt * (D : ℝ) / 2 ^ 7)) *
          ∏ i ∈ I, (4 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
            (n * (Tb.stepParameters y).side)).card : ℝ))) := ⟨_, rfl⟩
      have he : ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
          CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Yt ωt bad b =>
            ∏ i ∈ I, centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _) W Yt ωt bad b) ∧
          |caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Yt ωt bad b =>
              ∏ i ∈ I, centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _) W Yt ωt bad b) -
            ∏ i ∈ I, caseMean (T.stage t).toStepSetup G.cut G.coarse G.state
              (centeredSupportResponse (S.setup t) G.coarse (fineWeight (f i) _))| ≤
          e * ∏ i ∈ I, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
            (functionSites (Tb.stepParameters y).side (f i) (t + 1) n) G.state.1 G.state.2 := by
        intro G hG
        have hOS := hCq I.card y hy₃ (T.stage t).toStepSetup (S.setup t) hKt hAT n G hG (Fin p) I
          (fun i => fineWeight (f i) _) D rfl
          (fun i _ => (weightNorm_of_depth_eq _ (f i) (congrArg (· + 1) hlt) n).le.trans (hsz i))
          (fun i hi => by
            have h := hne i hi
            rw [← hs2 i] at h
            exact h)
          (by
            show 2 ^ 10 * clusterRange (T.stage t).coupling ≤ D
            rw [hx]
            exact_mod_cast h2)
          h8
          (fun i _ j _ hij Y hY Y' hY' => by
            have hY1 : Y ∈ thickening 2 (weightSupportSites (Tb.stepParameters y).side ((T.stage t).depth + 1) n
              (fineWeight (f i) (fineSide (Tb.stepParameters y).side ((T.stage t).depth + 1) n))) := hY
            have hY2 : Y' ∈ thickening 2 (weightSupportSites (Tb.stepParameters y).side ((T.stage t).depth + 1) n
              (fineWeight (f j) (fineSide (Tb.stepParameters y).side ((T.stage t).depth + 1) n))) := hY'
            rw [hs2 i] at hY1
            rw [hs2 j] at hY2
            obtain ⟨x₁, hx₁, hd₁⟩ := (Finset.mem_filter.1 hY1).2
            obtain ⟨x₂, hx₂, hd₂⟩ := (Finset.mem_filter.1 hY2).2
            have h1 := hsep i j hij x₁ hx₁ x₂ hx₂
            have h3 : D + 4 ≤ supDist x₁ x₂ := by exact_mod_cast h1
            have t1 := supDist_triangle x₁ Y x₂
            have t2 := supDist_triangle Y Y' x₂
            have c1 := supDist_comm x₁ Y
            omega)
        refine ⟨hOS.1, hOS.2.2.trans ?_⟩
        show Cq I.card * (∑ i ∈ I, ((weightSupportSites (Tb.stepParameters y).side (T.stage t).depth
            (n * (Tb.stepParameters y).side) (fineWeight (f i) (fineSide (Tb.stepParameters y).side (T.stage t).depth
              (n * (Tb.stepParameters y).side)))).card : ℝ)) ^ 2 *
            Real.exp (-((Tb.stepParameters y).rt * (D : ℝ) / 2 ^ 7)) *
            ∏ i ∈ I, (4 * (K.C₀ * ((weightSupportSites (Tb.stepParameters y).side (T.stage t).depth
              (n * (Tb.stepParameters y).side) (fineWeight (f i) (fineSide (Tb.stepParameters y).side
                (T.stage t).depth (n * (Tb.stepParameters y).side)))).card : ℝ)) *
              meanSiteScore (coarseLabelScore K.s₁ (S.setup t).score)
                (weightSupportSites (Tb.stepParameters y).side ((T.stage t).depth + 1) n
                  (fineWeight (f i) (fineSide (Tb.stepParameters y).side ((T.stage t).depth + 1) n)))
                G.state.1 G.state.2) ≤ _
        simp only [hs1, hs2]
        rw [he_def, hSK]
        have hstoredK : ∀ w, 0 ≤ coarseLabelScore (L := (Tb.stepParameters y).side) K.s₁ (S.setup t).score w := by
          rw [← hSK]
          exact hstored
        exact decorrelation_bound_factor I _ _
          ((le_abs_self _).trans (Finset.single_le_sum (f := fun q => |Cq q|) (fun _ _ => abs_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hcard))))
          (Real.exp_pos _).le hC0 (fun i => Nat.cast_nonneg _)
          (fun i => zero_le_one.trans (one_le_meanSiteScore hstoredK _ _ _))
      obtain ⟨m, hm_def⟩ : ∃ m : Finset (Fin p) → ℝ, m = fun J =>
          Real.exp (2 ^ J.card * (J.card.factorial : ℝ) *
            Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))) := ⟨_, rfl⟩
      have hmaj : ∀ J ⊆ I, J.Nonempty → ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
          CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Yt ωt _ _ =>
            ∏ i ∈ J, meanSiteScore (S.setup t).score
              (functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)) Yt ωt) ∧
          caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Yt ωt _ _ =>
            ∏ i ∈ J, meanSiteScore (S.setup t).score
              (functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)) Yt ωt) ≤
          m J * ∏ i ∈ J, meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
            (functionSites (Tb.stepParameters y).side (f i) (t + 1) n) G.state.1 G.state.2 := by
        intro J hJ _ G hG
        have hnonJ : ∀ i ∈ J,
            (functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)).Nonempty := by
          intro i hi
          have h := hne i (hJ hi)
          rw [← image_parentBlock_functionSites] at h
          exact Finset.image_nonempty.1 h
        have hMJ := Y₄ y hy₄ (T.stage t).toStepSetup (S.setup t) hKt hAT n G hG (Fin p) J
          (fun i => functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)) hnonJ
        refine ⟨hMJ.1, hMJ.2.trans (le_of_eq ?_)⟩
        show Real.exp (2 ^ J.card * (J.card.factorial : ℝ) * Real.exp (-(7 * Tb.gasRate * (T.stage t).coupling))) *
            ∏ i ∈ J, meanSiteScore (coarseLabelScore (S.setup t).responseParams.s₁ (S.setup t).score)
              (open Classical in (functionSites (Tb.stepParameters y).side (f i) t
                (n * (Tb.stepParameters y).side)).image (parentBlock (Tb.stepParameters y).side))
              G.state.1 G.state.2 = _
        rw [hx, hOR.params_eq t, hm_def]
        simp only [image_parentBlock_functionSites]
      have hbd : ∀ J ⊆ I, J.Nonempty → 0 ≤ Err J ∧ 0 ≤ m J ∧
          ∀ᵐ a ∂(markedSampleLaw T β t (n * (Tb.stepParameters y).side)),
            |conditionalProduct S β f J t (n * (Tb.stepParameters y).side) a -
                ∏ i ∈ J, fittedResponse S (f i) t (n * (Tb.stepParameters y).side) (stageState T t _ a)| ≤
              Err J * ∏ i ∈ J, scoreMeanOver S (f i) t (n * (Tb.stepParameters y).side) (stageState T t _ a) :=
        fun J hJ _ => ⟨hErr0 J hJ, by rw [hm_def]; exact (Real.exp_pos _).le, hErr J hJ⟩
      have hup := Y₁ y hy₁ hRS β T S t hSK hOR hRR p f n hbs hsz' hsz I e m Err he hmaj hbd
      filter_upwards [hup] with x hx'
      refine hx'.trans (mul_le_mul_of_nonneg_right ?_ (hN x))
      rw [hSK, he_def]
      refine add_le_add le_rfl ?_
      have hmJ : ∀ J ∈ I.powerset.filter Finset.Nonempty, m J ≤
          Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
            Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))) := by
        intro J hJ
        have hsub := Finset.mem_powerset.1 (Finset.mem_filter.1 hJ).1
        have hc := Finset.card_le_card hsub
        rw [hm_def]
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        have a₁ : (2 : ℝ) ^ J.card ≤ 2 ^ I.card := pow_le_pow_right₀ (by norm_num) hc
        have b₁ : (J.card.factorial : ℝ) ≤ (I.card.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hc
        exact mul_le_mul a₁ b₁ (Nat.cast_nonneg _) (by positivity)
      calc ∑ J ∈ I.powerset.filter Finset.Nonempty, Err J * m J *
            ∏ i ∈ I \ J, (2 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
              (n * (Tb.stepParameters y).side)).card : ℝ)))
          ≤ ∑ J ∈ I.powerset.filter Finset.Nonempty,
              Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
                Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))) *
              (Err J * ∏ i ∈ I \ J, (2 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
                (n * (Tb.stepParameters y).side)).card : ℝ)))) := by
            refine Finset.sum_le_sum fun J hJ => ?_
            have h0 := hErr0 J (Finset.mem_powerset.1 (Finset.mem_filter.1 hJ).1)
            have h1 := mul_le_mul_of_nonneg_right (hmJ J hJ) (mul_nonneg h0 (htwo J))
            calc _ = m J * (Err J * ∏ i ∈ I \ J, (2 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
                  (n * (Tb.stepParameters y).side)).card : ℝ)))) := by ring
              _ ≤ _ := h1
        _ = Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
              Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))) *
            ∑ J ∈ I.powerset.filter Finset.Nonempty, Err J *
              ∏ i ∈ I \ J, (2 * (K.C₀ * ((functionSites (Tb.stepParameters y).side (f i) t
                (n * (Tb.stepParameters y).side)).card : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun J hJ _ => mul_nonneg (hErr0 J (Finset.mem_powerset.1 hJ)) (htwo J)) (Real.exp_pos _).le
    · push_neg at hne
      obtain ⟨i₀, hi₀, hempty⟩ := hne
      have hz : ∀ u, ∏ i ∈ I, completedCentered S (f i) (t + 1) n u = 0 := fun u =>
        Finset.prod_eq_zero hi₀ (completedCentered_eq_zero S (f i₀) hlev (t + 1) n hempty u)
      have hG0 : conditionalProduct S β f I (t + 1) n = 0 := by
        show (markedSampleLaw T β (t + 1) n)[fun u => ∏ i ∈ I, completedCentered S (f i) (t + 1) n u |
          stageSigma T (t + 1) n] = 0
        rw [funext hz]
        exact condExp_zero
      have hF0 : ∀ q : StageState T (t + 1) n, ∏ i ∈ I, fittedResponse S (f i) (t + 1) n q = 0 := fun q =>
        Finset.prod_eq_zero hi₀ (by unfold fittedResponse; rw [hempty]; simp)
      refine Filter.Eventually.of_forall fun u => ?_
      rw [hG0, hF0]
      simp only [Pi.zero_apply, sub_zero, abs_zero]
      refine mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsum0 (sq_nonneg _)) (Real.exp_pos _).le) hfour)
        (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun J hJ =>
          mul_nonneg (hErr0 J (Finset.mem_powerset.1 hJ)) (htwo J)))) (hN u)
end YangMills.Construction.TransfersOffTheWalk
end
