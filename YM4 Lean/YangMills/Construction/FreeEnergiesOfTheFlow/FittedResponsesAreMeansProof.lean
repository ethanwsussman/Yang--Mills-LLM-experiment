import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStep
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCases
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansOverTheCases
import YangMills.Construction.FreeEnergiesOfTheFlow.StatesOfATowerStandOnGrounds
import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheState
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepGas StepCosts WeightedResponses ResponseInTheExpansion
namespace FreeEnergies
section Weights
variable {L : ℕ} [NeZero L]
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
private theorem mem_weightSupportSites_iff {t n : ℕ} [NeZero n] {h : PlaquetteWeight (fineSide L t n)} {y : TorusSite n} :
    y ∈ weightSupportSites L t n h ↔ ∃ p, IsPlaquetteAt L t y p ∧ h p ≠ 0 := by
  simp [weightSupportSites]
private theorem sum_count_eq_length {α : Type} [Fintype α] [DecidableEq α] (l : List α) :
    ∑ z, ((l.count z : ℕ) : ℝ) = l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have e : ∀ z, (((b :: l).count z : ℕ) : ℝ) = ((l.count z : ℕ) : ℝ) + if z = b then 1 else 0 := by
      intro z
      rw [List.count_cons]
      by_cases h : z = b
      · subst h
        simp
      · have h' : ¬ b = z := fun e => h e.symm
        simp [h, h']
    simp only [e, Finset.sum_add_distrib, ih, Finset.sum_ite_eq', Finset.mem_univ, if_true, List.length_cons]
    push_cast
    ring
private theorem sum_siteResponse_eq (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (h : PlaquetteWeight n) (W : TorusField n) :
    ∑ z ∈ weightSupportSites L 0 n h, siteResponse z W h = curvatureObservable h W := by
  have off : ∀ z ∈ (Finset.univ : Finset (TorusSite n)), z ∉ weightSupportSites L 0 n h → siteResponse z W h = 0 := by
    intro z _ hz
    unfold siteResponse
    refine Finset.sum_eq_zero fun p hp => ?_
    by_cases hc : vertexMultiplicity z p = 0
    · simp [hc]
    · have hmem : z ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
        by_contra hy
        apply hc
        simp [vertexMultiplicity, List.count_eq_zero_of_not_mem hy]
      have hord : p.2.1 < p.2.2 := by
        simp only [plaquettesIn, Finset.mem_filter] at hp
        exact hp.2.1
      have hh : h p = 0 := by
        by_contra hne
        exact hz (mem_weightSupportSites_iff.2 ⟨p, ⟨hord, z, hmem, Finset.mem_singleton_self _⟩, hne⟩)
      simp [hh]
  rw [Finset.sum_subset (Finset.subset_univ _) off]
  unfold siteResponse curvatureObservable
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hs : ∑ z : TorusSite n, vertexMultiplicity z p = 4 := by
    unfold vertexMultiplicity
    rw [sum_count_eq_length]
    simp [plaquetteVertices]
  rw [← Finset.sum_mul, ← Finset.sum_div, hs]
  ring
private theorem curvatureObservable_trivialField {n : ℕ} [NeZero n] (h : PlaquetteWeight n) :
    curvatureObservable h (trivialField n) = 0 := by
  unfold curvatureObservable
  refine Finset.sum_eq_zero fun p _ => ?_
  have e : plaquetteEnergyOf (trivialField n) p = 0 := by
    unfold plaquetteEnergyOf
    rw [plaquetteEnergy_eq_curvature_sq]
    simp [curvature, holonomy, trivialField]
  rw [e, mul_zero]
end Weights
section Sigma
variable {X A : Type} [MeasurableSpace X] {β : A → Type} [∀ a, MeasurableSpace (β a)]
private theorem measurableSet_image_sigmaMk [DecidableEq A] (a : A) {V : Set (β a)} (hV : MeasurableSet V) :
    MeasurableSet (Sigma.mk a '' V : Set (Sigma β)) := by
  refine MeasurableSpace.measurableSet_iInf.2 fun a' => ?_
  show MeasurableSet ((Sigma.mk a' : β a' → Sigma β) ⁻¹' (Sigma.mk a '' V))
  by_cases h : a' = a
  · subst h
    have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' (Sigma.mk a' '' V) = V := by
      ext b
      simp
    rw [e]
    exact hV
  · have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' (Sigma.mk a '' V) = ∅ := by
      ext b
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro c _ hc
      exact h (congrArg Sigma.fst hc).symm
    rw [e]
    exact MeasurableSet.empty
private theorem measurableSet_sigma_fst_eq [DecidableEq A] (a : A) : MeasurableSet {z : Sigma β | z.1 = a} := by
  refine MeasurableSpace.measurableSet_iInf.2 fun a' => ?_
  show MeasurableSet ((Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a})
  by_cases h : a' = a
  · subst h
    have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a'} = Set.univ := by
      ext y
      simp
    rw [e]
    exact MeasurableSet.univ
  · have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a} = ∅ := by
      ext y
      simpa using h
    rw [e]
    exact MeasurableSet.empty
private theorem measurableSet_image_prod_sigmaMk [DecidableEq A] (a : A) {S : Set (X × β a)} (hS : MeasurableSet S) :
    MeasurableSet ((fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) '' S) := by
  refine MeasurableSpace.induction_on_inter (C := fun S _ => MeasurableSet
    ((fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) '' S)) generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ S hS
  · simp
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    have e : (fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) '' (U ×ˢ V) = U ×ˢ (Sigma.mk a '' V) := by
      ext ⟨x, z⟩
      simp only [Set.mem_image, Set.mem_prod, Prod.mk.injEq, Prod.exists]
      constructor
      · rintro ⟨x', b, ⟨h1, h2⟩, rfl, rfl⟩
        exact ⟨h1, b, h2, rfl⟩
      · rintro ⟨h1, b, h2, rfl⟩
        exact ⟨x, b, ⟨h1, h2⟩, rfl, rfl⟩
    rw [e]
    exact hU.prod (measurableSet_image_sigmaMk a hV)
  · intro S _ ih
    have e : (fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) '' Sᶜ =
        (Prod.snd ⁻¹' {z : Sigma β | z.1 = a}) \ (fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) '' S := by
      ext ⟨x, ⟨a', b⟩⟩
      simp only [Set.mem_image, Set.mem_compl_iff, Prod.mk.injEq, Prod.exists, Set.mem_sdiff, Set.mem_preimage,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x', b', h1, rfl, h2⟩
        cases h2
        refine ⟨rfl, ?_⟩
        rintro ⟨x'', b'', h3, rfl, h4⟩
        cases h4
        exact h1 h3
      · rintro ⟨rfl, h2⟩
        exact ⟨x, b, fun h => h2 ⟨x, b, h, rfl, rfl⟩, rfl, rfl⟩
    rw [e]
    exact (measurable_snd (measurableSet_sigma_fst_eq a)).diff ih
  · intro f _ _ ih
    rw [Set.image_iUnion]
    exact MeasurableSet.iUnion ih
private theorem measurable_prod_sigma_of_slices [DecidableEq A] [Countable A] {g : X × Sigma β → ℝ}
    (h : ∀ a, Measurable fun p : X × β a => g (p.1, ⟨a, p.2⟩)) : Measurable g := by
  intro E hE
  have e : g ⁻¹' E = ⋃ a, (fun p : X × β a => (p.1, (⟨a, p.2⟩ : Sigma β))) ''
      ((fun p : X × β a => g (p.1, ⟨a, p.2⟩)) ⁻¹' E) := by
    ext ⟨x, ⟨a, b⟩⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · intro hx
      exact ⟨a, x, b, hx, rfl, rfl⟩
    · rintro ⟨a', x', b', hx, rfl, h2⟩
      cases h2
      exact hx
  rw [e]
  exact MeasurableSet.iUnion fun a => measurableSet_image_prod_sigmaMk a (h a hE)
abbrev _root_.YangMills.SharedProofs.p67771 := @measurable_prod_sigma_of_slices
end Sigma
section Levels
variable {ℓ : StepParameters}
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s n) :
    (stageState T s n a).1 = topField ℓ s n a := by
  cases s with
  | zero => rfl
  | succ s => rfl
abbrev _root_.YangMills.SharedProofs.p2480 := @stageState_fst
private theorem weightSupportSites_fineWeight (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s) (m : ℕ) [NeZero m] :
    weightSupportSites L t m (fineWeight f (fineSide L t m)) = functionSites L f s m := by
  subst ht
  rfl
private theorem blockMean_fineWeight_congr (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) {t s : ℕ} (ht : t = s) (m : ℕ) [NeZero m]
    (Y : TorusSite m) :
    blockMean L t m Y (fineWeight f (fineSide L t m)) = blockMean L s m Y (fineWeight f (fineSide L s m)) := by
  subst ht
  rfl
private theorem centeredSupportResponse_eq {T : StageTower ℓ} (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s : ℕ}
    (ht : (T.stage s).depth = s) (n : ℕ)
    [NeZero n] (V : TorusField n) (W : TorusField (n * ℓ.side)) (Yt : Finset (TorusSite (n * ℓ.side)))
    (ωt : Yt → (T.stage s).labels.Ω) (bad : Finset (TorusBond (n * ℓ.side))) (b : BaseChoice ℓ.side n) :
    centeredSupportResponse (S.setup s) V (fineWeight f _) W Yt ωt bad b =
      fittedResponse S f s (n * ℓ.side) (W, ⟨Yt, ωt⟩) +
        (stepSourceTerm ℓ (T.stage s).coupling (S.coeffs s) s (fineWeight f _) W (b, V, bad) -
        caseMean (T.stage s).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
          (supportResponseSum (S.setup s) (trivialField n) (fineWeight f _))) := by
  classical
  have hs1 := weightSupportSites_fineWeight ℓ.side f ht (n * ℓ.side)
  have hs2 := weightSupportSites_fineWeight ℓ.side f (congrArg (· + 1) ht) n
  have hh : ∀ Y : TorusSite n, blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) =
      blockMean ℓ.side (s + 1) n Y (fineWeight f _) :=
    fun Y => blockMean_fineWeight_congr ℓ.side f (congrArg (· + 1) ht) n Y
  have hsum : ∑ Y ∈ functionSites ℓ.side f (s + 1) n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
        blockBondScores (R := (T.stage s).toStepSetup) W V b Y =
      ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
        blockBondScores (R := (T.stage s).toStepSetup) W V b Y := by
    refine Finset.sum_subset (Finset.subset_univ _) fun Y _ hY => ?_
    have h0 : blockMean ℓ.side (s + 1) n Y (fineWeight f (fineSide ℓ.side (s + 1) n)) = 0 := by
      by_contra hne
      exact hY (mem_weightSupportSites_of_blockMean_ne_zero ℓ.side (s + 1) n Y _ hne)
    rw [h0, zero_mul]
  show (∑ y ∈ weightSupportSites ℓ.side (T.stage s).depth (n * ℓ.side) (fineWeight f _),
      centeredHullResponse (S.setup s).cold (S.setup s).hull (n * ℓ.side) y W Yt ωt (fineWeight f _) +
      ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y ∈ weightSupportSites ℓ.side ((T.stage s).depth + 1) n (fineWeight f _),
        blockMean ℓ.side ((T.stage s).depth + 1) n Y (fineWeight f _) *
          blockBondScores (R := (T.stage s).toStepSetup) W V b Y) - _ =
    ∑ y ∈ functionSites ℓ.side f s (n * ℓ.side),
        centeredHullResponse (S.setup s).cold (S.setup s).hull (n * ℓ.side) y W Yt ωt (fineWeight f _) +
      (ℓ.coupling / 2 * (S.setup s).coeff * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y (fineWeight f _) *
        blockBondScores (R := (T.stage s).toStepSetup) W V b Y - _)
  rw [hs1, hs2]
  simp only [hh]
  rw [hsum]
  ring
abbrev _root_.YangMills.SharedProofs.p36430 := @centeredSupportResponse_eq
end Levels
section Core
variable {ℓ : StepParameters} {T : StageTower ℓ}
private structure StageFacts (S : ScoredStageTower T) (β : ℝ) (tp : ℕ) : Prop where
  fit : ℓ.Admissible
  cut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn
  marks : T.MarksMeasurable
  start : ResponseInTheExpansion.StageTower.StartsAtWilson T β
  expansions : ∀ s ≤ tp, (T.stage s).toStepSetup.HasExpansions
  depth_eq : ∀ s ≤ tp, (T.stage s).depth = s
  borel : ∀ s ≤ tp, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (Y : Finset (TorusSite n))
    (h : PlaquetteWeight (fineSide ℓ.side (T.stage s).depth n)),
    (open Classical in Measurable fun p : TorusField n × (Y → (T.stage s).labels.Ω) =>
      if IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight p.1 Y p.2 then
        (S.setup s).hull n y p.1 Y p.2 h else 0)
  cold_zero : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (f : FinePlaquetteFunction),
    (S.setup 0).cold n z W (fineWeight f _) = siteResponse z W (fineWeight f n)
  hull_zero : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → (T.stage 0).labels.Ω) (f : FinePlaquetteFunction),
    (S.setup 0).hull n z W Y ω (fineWeight f _) = siteResponse z W (fineWeight f n)
  cold_succ : ∀ u < tp, (S.setup (u + 1)).cold = (S.setup u).coldStep
  hull_succ : ∀ u < tp, (S.setup (u + 1)).hull = (S.setup u).hullStep
  variable_mean : ∀ u < tp, ∀ (n : ℕ) [NeZero n] (f : PlaquetteWeight (fineSide ℓ.side ((T.stage u).depth + 1) n))
    (G : GasGround (T.stage u).toStepSetup n),
    G.IsAdmissibleGround → CaseIntegrable (T.stage u).toStepSetup G.cut G.coarse G.state
        (centeredSupportResponse (S.setup u) G.coarse f) ∧
      caseMean (T.stage u).toStepSetup G.cut G.coarse G.state (centeredSupportResponse (S.setup u) G.coarse f) =
        ∑ Y ∈ weightSupportSites ℓ.side ((T.stage u).depth + 1) n f,
          (caseMean (T.stage u).toStepSetup G.cut G.coarse G.state (caseResponse (S.setup u) G.coarse Y f) -
            caseMean (T.stage u).toStepSetup ∅ (trivialField n) (emptyCoarseState _)
              (caseResponse (S.setup u) (trivialField n) Y f))
  one : ∀ u < tp, ∀ (n : ℕ) [NeZero n] (G : GasGround (T.stage u).toStepSetup n), G.IsAdmissibleGround →
    CaseIntegrable (T.stage u).toStepSetup G.cut G.coarse G.state (fun _ _ _ _ _ => 1)
  read : ∀ u < tp, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ReadsCasesAt T β u n
  grounds : ∀ u < tp, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ᵐ x ∂(markedSampleLaw T β (u + 1) n),
    (hotCaseGround (T.stage u).toStepSetup x.2.2.1 (stageState T (u + 1) n x).2).IsAdmissibleGround ∧
    IsLiveState ℓ (T.stage (u + 1)).coupling (T.stage (u + 1)).labelWeight x.2.2.1 (stageState T (u + 1) n x).2.1
      (stageState T (u + 1) n x).2.2
private theorem fittedResponse_zero {S : ScoredStageTower T} {β : ℝ} {tp : ℕ} (hF : StageFacts S β tp)
    (f : FinePlaquetteFunction) (n : ℕ) [NeZero n]
    (q : StageState T 0 n) : fittedResponse S f 0 n q = curvatureObservable (fineWeight f n) q.1 := by
  have e : ∀ z : TorusSite n, centeredHullResponse (S.setup 0).cold (S.setup 0).hull n z q.1 q.2.1 q.2.2 (fineWeight f _) =
      siteResponse z q.1 (fineWeight f n) - siteResponse z (trivialField n) (fineWeight f n) := by
    intro z
    unfold centeredHullResponse
    rw [hF.hull_zero, hF.cold_zero]
  have h1 : ∑ z ∈ functionSites ℓ.side f 0 n, siteResponse z q.1 (fineWeight f n) =
      curvatureObservable (fineWeight f n) q.1 :=
    sum_siteResponse_eq ℓ.side _ _
  have h2 : ∑ z ∈ functionSites ℓ.side f 0 n, siteResponse z (trivialField n) (fineWeight f n) = 0 :=
    (sum_siteResponse_eq ℓ.side _ _).trans (curvatureObservable_trivialField _)
  unfold fittedResponse
  simp only [e]
  rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
private def FittedIsConditionalMean (S : ScoredStageTower T) (β : ℝ) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n] :
    Prop :=
  (∃ fm : StageState T s n → ℝ, Measurable fm ∧
    (∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (T.stage s).labels.Ω),
      IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight W Y ω →
        fm (W, ⟨Y, ω⟩) = fittedResponse S f s n (W, ⟨Y, ω⟩)) ∧
    ∀ᵐ a ∂(markedSampleLaw T β s n), fm (stageState T s n a) = fittedResponse S f s n (stageState T s n a)) ∧
  (∀ᵐ a ∂(markedSampleLaw T β s n), fittedResponse S f s n (stageState T s n a) =
    ((markedSampleLaw T β s n)[completedCentered S f s n | stageSigma T s n]) a)
variable (hSt : StageStatesMeasurableStatement) (hB : completedObservablesBounded)
  (hT : TwoPointByTotalCovarianceStatement) (hPast : FreeEnergiesOfTheFlow.MarkovPropertyOfStageStates)
  (hC : caseMeanProperties)
include hSt hB hT in
private theorem fittedIsConditionalMean_zero {S : ScoredStageTower T} {β : ℝ} {tp : ℕ} (hF : StageFacts S β tp)
    (f : FinePlaquetteFunction) (n : ℕ) [NeZero n] :
    FittedIsConditionalMean S β f 0 n := by
  have hf := hF.fit
  have hP : IsProbabilityMeasure (markedSampleLaw T β 0 n) :=
    (hT ℓ hf hf.depth_lt T hF.cut hF.marks β (fun _ => 0) 0 n).1
  have hG : stageSigma T 0 n ≤ markedSampleMeasurableSpace ℓ 0 n := (hSt ℓ hf T 0 n).comap_le
  obtain ⟨hm, C, hC'⟩ := ((hB ℓ hf T S.coeffs 0 n).1 (fineWeight f _))
  have hfm : Measurable (fittedResponse S f 0 n) := by
    have e : fittedResponse S f 0 n =
        fun q : StageState T 0 n => completedObservable T S.coeffs 0 n (fineWeight f _) q.1 := by
      funext q
      rw [fittedResponse_zero hF]
      show _ = curvatureObservable _ q.1 + 0
      rw [add_zero]
      rfl
    rw [e]
    exact hm.comp measurable_fst
  have hcl : ∀ a : MarkedSample ℓ 0 n, completedCentered S f 0 n a = fittedResponse S f 0 n (stageState T 0 n a) := by
    intro a
    rw [fittedResponse_zero hF]
    show curvatureObservable _ a + 0 - 0 = curvatureObservable _ a
    rw [add_zero, sub_zero]
    rfl
  refine ⟨⟨fittedResponse S f 0 n, hfm, fun _ _ _ _ => rfl, Filter.Eventually.of_forall fun _ => rfl⟩, ?_⟩
  have hsm : StronglyMeasurable[stageSigma T 0 n] (completedCentered S f 0 n) := by
    have e : completedCentered S f 0 n = fun a => fittedResponse S f 0 n (stageState T 0 n a) := funext hcl
    rw [e]
    exact (hfm.comp (comap_measurable _)).stronglyMeasurable
  have hI : Integrable (completedCentered S f 0 n) (markedSampleLaw T β 0 n) :=
    Integrable.of_bound (hsm.mono hG).aestronglyMeasurable (C + 0) (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]
      show |completedObservable T S.coeffs 0 n _ a - 0| ≤ _
      rw [sub_zero, add_zero]
      exact hC' a)
  rw [condExp_of_stronglyMeasurable hG hsm hI]
  exact Filter.Eventually.of_forall fun a => (hcl a).symm
open Classical in
private def liveFittedResponse (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n]
    (q : StageState T s n) : ℝ :=
  ∑ z ∈ functionSites ℓ.side f s n,
    ((if IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight q.1 q.2.1 q.2.2 then
      (S.setup s).hull n z q.1 q.2.1 q.2.2 (fineWeight f _) else 0) -
      (S.setup s).cold n z (trivialField n) (fineWeight f _))
private theorem liveFittedResponse_of_live (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    {q : StageState T s n}
    (hl : IsLiveState ℓ (T.stage s).coupling (T.stage s).labelWeight q.1 q.2.1 q.2.2) :
    liveFittedResponse S f s n q = fittedResponse S f s n q := by
  classical
  unfold liveFittedResponse fittedResponse centeredHullResponse
  exact Finset.sum_congr rfl fun z _ => by rw [if_pos hl]
private def stepCaseFunction (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (g : StageState T s (n * ℓ.side) → ℝ) (c : ℝ) :
    TorusField n → CaseFunction (T.stage s).toStepSetup n :=
  fun V W Yt ωt bad b => g (W, ⟨Yt, ωt⟩) +
    (stepSourceTerm ℓ (T.stage s).coupling (S.coeffs s) s (fineWeight f _) W (b, V, bad) - c)
private theorem caseLift_stepCaseFunction (S : ScoredStageTower T) (f : FinePlaquetteFunction) {s n : ℕ} [NeZero n]
    (g : StageState T s (n * ℓ.side) → ℝ) (c : ℝ) (x : MarkedSample ℓ (s + 1) n) :
    caseLift T s n (stepCaseFunction S f g c) x =
      g (stageState T s (n * ℓ.side) x.1) + (sourceTerm T S.coeffs s n (fineWeight f _) x - c) := by
  have e : ((topField ℓ s (n * ℓ.side) x.1,
      ⟨(stageState T s (n * ℓ.side) x.1).2.1, (stageState T s (n * ℓ.side) x.1).2.2⟩) :
      StageState T s (n * ℓ.side)) = stageState T s (n * ℓ.side) x.1 := by
    rw [← stageState_fst]
  show g (topField ℓ s (n * ℓ.side) x.1,
      ⟨(stageState T s (n * ℓ.side) x.1).2.1, (stageState T s (n * ℓ.side) x.1).2.2⟩) +
    (stepSourceTerm ℓ (T.stage s).coupling (S.coeffs s) s (fineWeight f _) (topField ℓ s (n * ℓ.side) x.1)
      (x.2.1, x.2.2.1, x.2.2.2) - c) = _
  rw [e]
  rfl
private theorem caseMean_eq_fittedResponse_of_ground {S : ScoredStageTower T} {β : ℝ} {tp : ℕ} (hF : StageFacts S β tp)
    (f : FinePlaquetteFunction) {s : ℕ}
    (hs : s < tp) (n : ℕ) [NeZero n] (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n)
    (hG : (hotCaseGround (T.stage s).toStepSetup V q).IsAdmissibleGround) :
    caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V) V q
        (centeredSupportResponse (S.setup s) V (fineWeight f _)) =
      fittedResponse S f (s + 1) n (V, q) := by
  have h := (hF.variable_mean s hs n (fineWeight f _) _ hG).2
  refine h.trans ?_
  have ht1 : (T.stage s).depth + 1 = s + 1 := by rw [hF.depth_eq s hs.le]
  have hs2 := weightSupportSites_fineWeight ℓ.side f ht1 n
  unfold fittedResponse
  refine (Finset.sum_congr hs2 fun Y _ => ?_)
  unfold centeredHullResponse
  rw [hF.hull_succ s hs, hF.cold_succ s hs]
  rfl
include hSt hB hT hPast hC in
private theorem fittedIsConditionalMean_succ {S : ScoredStageTower T} {β : ℝ} {tp : ℕ} (hF : StageFacts S β tp)
    (f : FinePlaquetteFunction) {s : ℕ}
    (hs : s < tp) (n : ℕ) [NeZero n] (hbs : IsBlockTorusSide ℓ n) (hbsL : IsBlockTorusSide ℓ (n * ℓ.side))
    (ih : FittedIsConditionalMean S β f s (n * ℓ.side)) :
    FittedIsConditionalMean S β f (s + 1) n ∧ ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n),
        caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1
            (stageState T (s + 1) n x).2
            (centeredSupportResponse (S.setup s) x.2.2.1 (fineWeight f _)) =
          fittedResponse S f (s + 1) n (stageState T (s + 1) n x) := by
  classical
  have hf := hF.fit
  have hP : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
    (hT ℓ hf hf.depth_lt T hF.cut hF.marks β (fun _ => 0) (s + 1) n).1
  have hμ : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)) :=
    (hT ℓ hf hf.depth_lt T hF.cut hF.marks β (fun _ => 0) s (n * ℓ.side)).1
  have hτ : Measurable (stageState T s (n * ℓ.side)) := hSt ℓ hf T s (n * ℓ.side)
  have hτ' : Measurable (stageState T (s + 1) n) := hSt ℓ hf T (s + 1) n
  obtain ⟨hπ, hbold⟩ := hPast ℓ hf hf.depth_lt T hF.cut hF.marks β s n
  obtain ⟨hw, hread⟩ := hF.read s hs n hbs
  have hgr := hF.grounds s hs n hbs
  have h1 : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n (fun _ _ _ _ _ _ => 1) x := by
    refine hgr.mono fun x hx => ?_
    have h2 := hF.one s hs n (hotCaseGround (T.stage s).toStepSetup x.2.2.1 (stageState T (s + 1) n x).2) hx.1
    exact h2
  obtain ⟨hmean, -⟩ := hread h1
  obtain ⟨⟨fm₀, hfm₀, hlive₀, hae₀⟩, hmean₀⟩ := ih
  obtain ⟨hYm, KY, hKY⟩ := (hB ℓ hf T S.coeffs s (n * ℓ.side)).1 (fineWeight f _)
  obtain ⟨hSm, KS, hKS⟩ := (hB ℓ hf T S.coeffs s n).2.1 (fineWeight f _)
  have hYm' : Measurable (completedCentered S f s (n * ℓ.side)) := hYm.sub_const _
  have hKY' : ∀ a, |completedCentered S f s (n * ℓ.side) a| ≤ KY + |centering S f s (n * ℓ.side)| := fun a =>
    (abs_sub _ _).trans (add_le_add (hKY a) le_rfl)
  have hYi : Integrable (completedCentered S f s (n * ℓ.side)) (markedSampleLaw T β s (n * ℓ.side)) :=
    Integrable.of_bound hYm'.aestronglyMeasurable _ (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]; exact hKY' a)
  have hbar := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := markedSampleLaw T β s (n * ℓ.side))
    (m := stageSigma T s (n * ℓ.side)) (Filter.Eventually.of_forall hKY')
  have hfm_le : ∀ᵐ a ∂(markedSampleLaw T β s (n * ℓ.side)),
      |fm₀ (stageState T s (n * ℓ.side) a)| ≤ KY + |centering S f s (n * ℓ.side)| := by
    filter_upwards [hbar, hae₀, hmean₀] with a h2 h3 h4
    rw [h3, h4]
    exact h2
  set vv := caseMean (T.stage s).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
    (supportResponseSum (S.setup s) (trivialField n) (fineWeight f _)) with hvv
  have hlift := caseLift_stepCaseFunction S f (s := s) (n := n) fm₀ vv
  have hBm : Measurable fun x : MarkedSample ℓ (s + 1) n => sourceTerm T S.coeffs s n (fineWeight f _) x - vv :=
    hSm.sub_const _
  have hgm : Measurable fun x : MarkedSample ℓ (s + 1) n => fm₀ (stageState T s (n * ℓ.side) x.1) :=
    (hfm₀.comp hτ).comp hπ.measurable
  have hFm : Measurable (caseLift T s n (stepCaseFunction S f fm₀ vv)) := by
    have e : caseLift T s n (stepCaseFunction S f fm₀ vv) = fun x =>
        fm₀ (stageState T s (n * ℓ.side) x.1) + (sourceTerm T S.coeffs s n (fineWeight f _) x - vv) := funext hlift
    rw [e]
    exact hgm.add hBm
  have hfmP := hπ.quasiMeasurePreserving.ae hfm_le
  have hFK : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), |caseLift T s n (stepCaseFunction S f fm₀ vv) x| ≤
      KY + |centering S f s (n * ℓ.side)| + (KS + |vv|) := by
    filter_upwards [hfmP] with x hx
    rw [hlift]
    exact (abs_add_le _ _).trans (add_le_add hx ((abs_sub _ _).trans (add_le_add (hKS x) le_rfl)))
  have hcases : ∀ (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n),
      (hotCaseGround (T.stage s).toStepSetup V q).IsAdmissibleGround →
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V) V q
        (stepCaseFunction S f fm₀ vv V) ∧
      caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V) V q (stepCaseFunction S f fm₀ vv V) =
        caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V) V q
          (centeredSupportResponse (S.setup s) V (fineWeight f _)) := by
    intro V q hG
    have hp := hC (T.stage s).toStepSetup n (hotCoreSites (T.stage s).toStepSetup V) V q
      (fun W Yt ωt bad b _ => hw _ _ W Yt ωt bad b)
    have he := hp.1 (centeredSupportResponse (S.setup s) V (fineWeight f _)) (stepCaseFunction S f fm₀ vv V)
      (fun W Yt ωt bad b hh hwp => by
      have hD : 0 ≤ (T.stage s).labelWeight (n * ℓ.side) W Yt ωt :=
        (hF.expansions s hs.le).2.nonneg _ hbsL W Yt ωt hh
      have hD' : 0 < (T.stage s).labelWeight (n * ℓ.side) W Yt ωt := lt_of_le_of_ne hD fun h0 => hwp.ne' (by
        unfold stepWeight
        show (T.stage s).labelWeight (n * ℓ.side) W Yt ωt * _ * _ * _ = 0
        rw [← h0]
        ring)
      rw [centeredSupportResponse_eq S f (hF.depth_eq s hs.le) n V W Yt ωt bad b]
      show _ = fm₀ (W, ⟨Yt, ωt⟩) + _
      rw [hlive₀ W Yt ωt ⟨hh, hD'⟩])
    exact ⟨he.1 (hF.variable_mean s hs n (fineWeight f _) _ hG).1, he.2.symm⟩
  have hI : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n (stepCaseFunction S f fm₀ vv) x := by
    refine hgr.mono fun x hx => ?_
    have h2 := (hcases x.2.2.1 (stageState T (s + 1) n x).2 hx.1).1
    exact h2
  have hcm := hmean _ hFm _ hFK hI
  have hX : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n),
      caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1 (stageState T (s + 1) n x).2
          (centeredSupportResponse (S.setup s) x.2.2.1 (fineWeight f _)) =
        fittedResponse S f (s + 1) n (stageState T (s + 1) n x) :=
    hgr.mono fun x hx => caseMean_eq_fittedResponse_of_ground hF f hs n x.2.2.1 (stageState T (s + 1) n x).2 hx.1
  have hc : ∀ x : MarkedSample ℓ (s + 1) n, completedCentered S f (s + 1) n x =
      completedCentered S f s (n * ℓ.side) x.1 + (sourceTerm T S.coeffs s n (fineWeight f _) x - vv) := by
    intro x
    show (curvatureObservable (fineWeight f (fineSide ℓ.side s (n * ℓ.side))) (bottomField ℓ s (n * ℓ.side) x.1) +
        (cumulativeSource T S.coeffs s (n * ℓ.side) (fineWeight f (fineSide ℓ.side s (n * ℓ.side))) x.1 +
          sourceTerm T S.coeffs s n (fineWeight f (fineSide ℓ.side (s + 1) n)) x)) -
      (centering S f s (n * ℓ.side) + vv) =
      (curvatureObservable (fineWeight f (fineSide ℓ.side s (n * ℓ.side))) (bottomField ℓ s (n * ℓ.side) x.1) +
        cumulativeSource T S.coeffs s (n * ℓ.side) (fineWeight f (fineSide ℓ.side s (n * ℓ.side))) x.1 -
        centering S f s (n * ℓ.side)) + (sourceTerm T S.coeffs s n (fineWeight f (fineSide ℓ.side (s + 1) n)) x - vv)
    ring
  have hBi : Integrable (fun x : MarkedSample ℓ (s + 1) n => sourceTerm T S.coeffs s n (fineWeight f _) x - vv)
      (markedSampleLaw T β (s + 1) n) :=
    Integrable.of_bound hBm.aestronglyMeasurable (KS + |vv|) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hKS x) le_rfl))
  have hYPi : Integrable (fun x : MarkedSample ℓ (s + 1) n => completedCentered S f s (n * ℓ.side) x.1)
      (markedSampleLaw T β (s + 1) n) :=
    (hπ.integrable_comp hYi.aestronglyMeasurable).2 hYi
  have hgi : Integrable (fun x : MarkedSample ℓ (s + 1) n => fm₀ (stageState T s (n * ℓ.side) x.1))
      (markedSampleLaw T β (s + 1) n) :=
    Integrable.of_bound hgm.aestronglyMeasurable _ (hfmP.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact hx)
  have hb1 := hbold (completedCentered S f s (n * ℓ.side)) (fun _ => 1)
    (max (KY + |centering S f s (n * ℓ.side)|) 1) hYm' measurable_const
    (fun a => (hKY' a).trans (le_max_left _ _)) (fun _ => (abs_one (α := ℝ)).le.trans (le_max_right _ _))
  simp only [mul_one] at hb1
  have hbarP : (fun x : MarkedSample ℓ (s + 1) n =>
      ((markedSampleLaw T β s (n * ℓ.side))[completedCentered S f s (n * ℓ.side) | stageSigma T s (n * ℓ.side)]) x.1)
        =ᵐ[markedSampleLaw T β (s + 1) n] fun x => fm₀ (stageState T s (n * ℓ.side) x.1) := by
    have h2 : ∀ᵐ a ∂(markedSampleLaw T β s (n * ℓ.side)),
        ((markedSampleLaw T β s (n * ℓ.side))[completedCentered S f s (n * ℓ.side) | stageSigma T s (n * ℓ.side)]) a =
        fm₀ (stageState T s (n * ℓ.side) a) := by
      filter_upwards [hae₀, hmean₀] with a h3 h4
      rw [h3, h4]
    exact hπ.quasiMeasurePreserving.ae h2
  have e1 : completedCentered S f (s + 1) n =
      (fun x : MarkedSample ℓ (s + 1) n => completedCentered S f s (n * ℓ.side) x.1) +
      fun x => sourceTerm T S.coeffs s n (fineWeight f _) x - vv := funext hc
  have e2 : caseLift T s n (stepCaseFunction S f fm₀ vv) =
      (fun x : MarkedSample ℓ (s + 1) n => fm₀ (stageState T s (n * ℓ.side) x.1)) +
      fun x => sourceTerm T S.coeffs s n (fineWeight f _) x - vv := funext hlift
  have hfinal : (markedSampleLaw T β (s + 1) n)[completedCentered S f (s + 1) n | stageSigma T (s + 1) n]
      =ᵐ[markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n (stepCaseFunction S f fm₀ vv) := by
    rw [e1]
    refine (condExp_add hYPi hBi _).trans ?_
    refine ((hb1.trans (condExp_congr_ae hbarP)).add Filter.EventuallyEq.rfl).trans ?_
    refine (condExp_add hgi hBi _).symm.trans ?_
    rw [← e2]
    exact hcm
  refine ⟨⟨⟨liveFittedResponse S f (s + 1) n, ?_, ?_, ?_⟩, ?_⟩, hX⟩
  · refine measurable_prod_sigma_of_slices fun Y => ?_
    exact Finset.measurable_sum _ fun z _ => (hF.borel (s + 1) hs n hbs z Y _).sub_const _
  · intro W Y ω hl
    exact liveFittedResponse_of_live S f hl
  · exact hgr.mono fun x hx => liveFittedResponse_of_live S f hx.2
  · filter_upwards [hfinal, hgr, hX] with x h2 h3 h4
    rw [h2]
    show _ = caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1
      (stageState T (s + 1) n x).2 (stepCaseFunction S f fm₀ vv x.2.2.1)
    rw [(hcases x.2.2.1 (stageState T (s + 1) n x).2 h3.1).2, h4]
end Core
theorem fittedResponseIsConditionalMean (hSt : StageStatesMeasurableStatement) (hB : completedObservablesBounded)
    (hT : TwoPointByTotalCovarianceStatement) (hPast : FreeEnergiesOfTheFlow.MarkovPropertyOfStageStates)
    (hRead : conditionalMeanReadsCasesStatement) (hC : caseMeanProperties)
    (hMV : supportResponseMeanStatement) (hFL : labelFunctionsIntegrableStatement)
    (hGr : TowerStatesAreGroundStates) (hRow : expansionAlongFlow) : fittedResponseIsConditionalMeanStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hGr a ha
  obtain ⟨L₄, r₄, hr₄, H₄⟩ := hRead a ha
  obtain ⟨r₂, hr₂, H₂⟩ := hMV
  obtain ⟨r₃, hr₃, H₃⟩ := hFL
  refine ⟨max L₁ L₄, fun c => min (min (r₁ c) (r₄ c)) (min (r₂ c) (r₃ c)), C₁,
    fun c => lt_min (lt_min (hr₁ c) (hr₄ c)) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hOn
    (hrt.trans ((min_le_left _ _).trans (min_le_left _ _))) hCd K
  obtain ⟨y₄, Y₄⟩ := H₄ L hodd ((le_max_right _ _).trans hL) Tb hTa hTL hD
    (hrt.trans ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨y₂, Y₂⟩ := H₂ Tb hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₃, Y₃⟩ := H₃ Tb hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  refine ⟨max (max y₁ y₄) (max y₂ (max y₃ Tb.floorMin)), fun y hy hRS => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₄ : y₄ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₀ : Tb.floorMin ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  intro β T S tp hSK hOR hRR f s hs n _ hbs
  have hfit := hD.fits y hy₀
  have hdepth : ∀ u, (T.stage u).depth = u := by
    intro u
    induction u with
    | zero => exact hOR.startsAtWilson.depth_eq
    | succ u ih =>
      show (T.stage u).depth + 1 = u + 1
      rw [ih]
  have hAT : ∀ u < tp, OnStepParameters Tb y (S.setup u) := by
    intro u hu
    have hst := hOR.isFlowStep u hu.le
    refine ⟨hst.onFamily, ?_, hOR.isAdmissible u hu.le, ?_⟩
    · rw [hst.nextCoupling_eq, hst.coupling_eq]
      exact (hRow _ hRS β tp hRR).2 u hu
    · rw [hOR.params_eq u]
      exact hOR.N₀_eq
  have hK : ∀ u, (S.setup u).responseParams = K := fun u => (hOR.params_eq u).trans hSK
  have hF : StageFacts S β tp :=
    { fit := hfit
      cut := hOR.isCutoff_bottom
      marks := hOR.marksMeasurable
      start := hOR.startsAtWilson
      expansions := fun u hu => (hOR.isFlowStep u hu).onFamily.isStep.1
      depth_eq := fun u _ => hdepth u
      borel := fun u hu n _ hbs y Y h => (hOR.isAdmissible u hu).bounds.hull_borel n hbs y Y h
      cold_zero := hOR.cold_zero
      hull_zero := hOR.hull_zero
      cold_succ := hOR.cold_succ
      hull_succ := hOR.hull_succ
      variable_mean := fun u hu n _ f G hG => (Y₂ y hy₂ _ _ (hK u) (hAT u hu) n f).1 G hG
      one := fun u hu n _ G hG => Y₃ y hy₃ _ _ (hK u) (hAT u hu) n G hG ∅ (fun _ _ => 1) (fun _ => measurable_const)
        (fun Yt ωt => by simp [scoreSumOn])
      read := fun u hu n _ hbs => Y₄ y hy₄ hRS.returns_at hRS.wilson_expansion T β u n
        ⟨hOR.startsAtWilson, fun j hj => (hOR.isFlowStep j (by omega)).coupling_eq,
          fun j hj => (hOR.isFlowStep j (by omega)).onFamily⟩
        hOR.isCutoff_bottom hOR.marksMeasurable (Y₁ y hy₁ hRS β T S tp hSK hOR hRR u hu).1
        ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))⟩ hbs.1
      grounds := fun u hu n _ hbs => (Y₁ y hy₁ hRS β T S tp hSK hOR hRR u hu).2 n hbs }
  have key : ∀ s : ℕ, s ≤ tp → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      FittedIsConditionalMean S β f s n := by
    intro s
    induction s with
    | zero => exact fun _ n _ _ => fittedIsConditionalMean_zero hSt hB hT hF f n
    | succ s ih =>
      intro hs n _ hbs
      have hbsL : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
        ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))⟩
      exact (fittedIsConditionalMean_succ hSt hB hT hPast hC hF f hs n hbs hbsL (ih (by omega) _ hbsL)).1
  refine ⟨(key s hs n hbs).1, (key s hs n hbs).2, fun hlt => ?_⟩
  have hbsL : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))⟩
  exact (fittedIsConditionalMean_succ hSt hB hT hPast hC hF f hlt n hbs hbsL (key s hs _ hbsL)).2
end FreeEnergies
end YangMills.Construction
end
