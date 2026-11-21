import YangMills.Construction.CellOfTheFlow.ACellIsRareProof
import YangMills.Construction.CellOfTheFlow.MomentOfTheLowerMajorant
import YangMills.Construction.CellOfTheFlow.MomentOfTheMajorant
import YangMills.Construction.CellOfTheFlow.TheLowerMajorantIsBelowTheMajorant
import YangMills.Construction.CellOfTheFlow.TheLowerSumReadsItsCell
import YangMills.Construction.CellOfTheFlow.TheLowerWindowLiesInTheHull
import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheMeansOfACell
import YangMills.Construction.CellOfTheFlow.WilsonsLawUnderTheMirrors
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevelProof
import YangMills.Construction.SixteenPointsOnASmallTorus.SizeOfACopyProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped unitInterval ENNReal
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
namespace LowerScoreMoment
private def IsMixing {X : Type} [MeasurableSpace X] (μ : Measure X) (m : X → X → X) : Prop :=
  Measurable (Function.uncurry m) ∧
    ∀ g : X → ℝ≥0∞, Measurable g → ∫⁻ a, ∫⁻ b, g (m a b) ∂μ ∂μ = ∫⁻ a, g a ∂μ
private theorem isMixing_pi {ι : Type} [Fintype ι] (A : ι → Prop) [DecidablePred A] :
    IsMixing (Measure.pi fun _ : ι => (volume : Measure I)) (fun a b i => if A i then a i else b i) := by
  classical
  set P := Measure.pi fun _ : ι => (volume : Measure I) with hP
  have hm : Measurable (Function.uncurry fun (a b : ι → I) (i : ι) => if A i then a i else b i) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : A i
    · have e : (fun c : (ι → I) × (ι → I) => Function.uncurry
          (fun (a b : ι → I) (i : ι) => if A i then a i else b i) c i) = fun c => c.1 i := by
        funext c
        simp [Function.uncurry, h]
      rw [e]
      exact (measurable_pi_apply i).comp measurable_fst
    · have e : (fun c : (ι → I) × (ι → I) => Function.uncurry
          (fun (a b : ι → I) (i : ι) => if A i then a i else b i) c i) = fun c => c.2 i := by
        funext c
        simp [Function.uncurry, h]
      rw [e]
      exact (measurable_pi_apply i).comp measurable_snd
  have hmap : P = (P.prod P).map (Function.uncurry fun (a b : ι → I) (i : ι) => if A i then a i else b i) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Function.uncurry fun (a b : ι → I) (i : ι) => if A i then a i else b i) ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ fun i => if A i then s i else Set.univ) ×ˢ
          (Set.pi Set.univ fun i => if A i then Set.univ else s i) := by
      ext ⟨a, b⟩
      simp only [Set.mem_preimage, Function.uncurry, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun i => ?_, fun i => ?_⟩
        · by_cases hi : A i
          · simpa [hi] using h i
          · simp [hi]
        · by_cases hi : A i
          · simp [hi]
          · simpa [hi] using h i
      · rintro ⟨h1, h2⟩ i
        by_cases hi : A i
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    rw [hpre, Measure.prod_prod, hP, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : A i <;> simp [h]
  refine ⟨hm, fun g hg => ?_⟩
  conv_rhs => rw [hmap]
  rw [lintegral_map hg hm]
  exact (lintegral_prod (fun z => g (Function.uncurry (fun (a b : ι → I) (i : ι) => if A i then a i else b i) z))
    (hg.comp hm).aemeasurable).symm
private theorem IsMixing.prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {mx : X → X → X} {my : Y → Y → Y} (hx : IsMixing μ mx) (hy : IsMixing ν my) :
    IsMixing (μ.prod ν) (fun p q => (mx p.1 q.1, my p.2 q.2)) := by
  have hm : Measurable (Function.uncurry fun (p q : X × Y) => (mx p.1 q.1, my p.2 q.2)) :=
    (hx.1.comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
      (hy.1.comp (measurable_fst.snd.prodMk measurable_snd.snd))
  refine ⟨hm, fun g hg => ?_⟩
  have hq : ∀ p : X × Y, ∫⁻ q, g (mx p.1 q.1, my p.2 q.2) ∂(μ.prod ν) =
      ∫⁻ a', ∫⁻ b', g (mx p.1 a', my p.2 b') ∂ν ∂μ := fun p =>
    lintegral_prod _ (hg.comp (hm.comp (measurable_const.prodMk measurable_id))).aemeasurable
  simp_rw [hq]
  have hG : Measurable fun z : (X × Y) × (X × Y) => g (mx z.1.1 z.2.1, my z.1.2 z.2.2) := hg.comp hm
  have hout : Measurable fun p : X × Y => ∫⁻ a', ∫⁻ b', g (mx p.1 a', my p.2 b') ∂ν ∂μ := by
    have h1 : Measurable fun z : (X × Y) × X => ∫⁻ b', g (mx z.1.1 z.2, my z.1.2 b') ∂ν :=
      Measurable.lintegral_prod_right' (f := fun w : ((X × Y) × X) × Y => g (mx w.1.1.1 w.1.2, my w.1.1.2 w.2))
        (hG.comp ((measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))))
    exact Measurable.lintegral_prod_right' (f := fun z : (X × Y) × X => ∫⁻ b', g (mx z.1.1 z.2, my z.1.2 b') ∂ν) h1
  rw [lintegral_prod _ hout.aemeasurable]
  have hstep : ∀ a : X, ∫⁻ b, ∫⁻ a', ∫⁻ b', g (mx a a', my b b') ∂ν ∂μ ∂ν =
      ∫⁻ a', ∫⁻ y, g (mx a a', y) ∂ν ∂μ := by
    intro a
    have h1 : Measurable fun z : Y × X => ∫⁻ b', g (mx a z.2, my z.1 b') ∂ν :=
      Measurable.lintegral_prod_right' (f := fun w : (Y × X) × Y => g (mx a w.1.2, my w.1.1 w.2))
        (hG.comp (((measurable_const.prodMk measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))))
    rw [lintegral_lintegral_swap h1.aemeasurable]
    refine lintegral_congr fun a' => ?_
    exact hy.2 (fun y => g (mx a a', y)) (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hstep]
  rw [hx.2 (fun x => ∫⁻ y, g (x, y) ∂ν) hg.lintegral_prod_right']
  exact (lintegral_prod _ hg.aemeasurable).symm
open Classical in
private def mixStepNoise (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (c : Finset (TorusSite n))
    (ξ ξ' : StepNoise ℓ n) : StepNoise ℓ n :=
  (fun y => if y ∈ c then ξ.1 y else ξ'.1 y,
    fun b => if b.1 ∈ c ∧ b.1 + TorusFields.unitStep n b.2 ∈ c then ξ.2.1 b else ξ'.2.1 b,
    fun b => if b.1 ∈ sitesInBlocks ℓ.side c ∧ b.1 + TorusFields.unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c
      then ξ.2.2 b else ξ'.2.2 b)
private def mixChainNoise (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → [NeZero n] → Finset (TorusSite n) →
    ChainNoise ℓ s n → ChainNoise ℓ s n → ChainNoise ℓ s n
  | 0, _, _, _, _, _ => ()
  | s + 1, n, _, c, ξ, ξ' =>
      (mixChainNoise ℓ s (n * ℓ.side) (sitesInBlocks ℓ.side c) ξ.1 ξ'.1, mixStepNoise ℓ c ξ.2 ξ'.2)
private instance chainNoiseMeasure_isProbability (ℓ : TorusLumps.StepParameters) :
    (s n : ℕ) → [NeZero n] → IsProbabilityMeasure (chainNoiseMeasure ℓ s n)
  | 0, _, _ => by
      unfold chainNoiseMeasure
      exact Measure.dirac.isProbabilityMeasure
  | s + 1, n, _ => by
      have h1 := chainNoiseMeasure_isProbability ℓ s (n * ℓ.side)
      have h2 : IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
        unfold stepNoiseMeasure
        infer_instance
      unfold chainNoiseMeasure
      exact @Measure.prod.instIsProbabilityMeasure _ _ (instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)) _ _ _ h1 h2
private theorem isMixing_mixStepNoise (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (c : Finset (TorusSite n)) :
    IsMixing (stepNoiseMeasure ℓ n) (mixStepNoise ℓ c) := by
  classical
  exact (isMixing_pi (fun y => y ∈ c)).prod
    ((isMixing_pi (fun b : TorusBond n => b.1 ∈ c ∧ b.1 + TorusFields.unitStep n b.2 ∈ c)).prod
    (isMixing_pi (fun b : TorusBond (n * ℓ.side) => b.1 ∈ sitesInBlocks ℓ.side c ∧
      b.1 + TorusFields.unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c)))
private theorem isMixing_mixChainNoise (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusSite n)),
    IsMixing (chainNoiseMeasure ℓ s n) (mixChainNoise ℓ s n c)
  | 0, n, _, c => by
      refine ⟨measurable_const, fun g hg => ?_⟩
      have e : ∀ a b : ChainNoise ℓ 0 n, g (mixChainNoise ℓ 0 n c a b) = g (() : ChainNoise ℓ 0 n) := fun _ _ => rfl
      have e' : ∀ a : ChainNoise ℓ 0 n, g a = g (() : ChainNoise ℓ 0 n) := fun _ => rfl
      simp_rw [e, e']
      simp
  | s + 1, n, _, c => by
      have h2 : IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
        unfold stepNoiseMeasure
        infer_instance
      exact (isMixing_mixChainNoise ℓ s (n * ℓ.side) (sitesInBlocks ℓ.side c)).prod (isMixing_mixStepNoise ℓ c)
private theorem noiseAgreesOn_mix_left (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusSite n))
    (ξ ξ' : ChainNoise ℓ s n), NoiseAgreesOn ℓ s n c (mixChainNoise ℓ s n c ξ ξ') ξ
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, c, ξ, ξ' => by
      refine ⟨noiseAgreesOn_mix_left ℓ s (n * ℓ.side) _ _ _, fun y hy => ?_, fun b h1 h2 => ?_, fun b h1 h2 => ?_⟩
      · simp [mixChainNoise, mixStepNoise, hy]
      · simp [mixChainNoise, mixStepNoise, h1, h2]
      · simp [mixChainNoise, mixStepNoise, h1, h2]
private theorem disjoint_sitesInBlocks (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)}
    (h : Disjoint c c') : Disjoint (sitesInBlocks L c) (sitesInBlocks L c') := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact h hx hx'
private theorem noiseAgreesOn_mix_right (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ) [NeZero n]
    (c c' : Finset (TorusSite n)) (_ : Disjoint c c') (ξ ξ' : ChainNoise ℓ s n),
    NoiseAgreesOn ℓ s n c' (mixChainNoise ℓ s n c ξ ξ') ξ'
  | 0, _, _, _, _, _, _, _ => trivial
  | s + 1, n, _, c, c', h, ξ, ξ' => by
      have hb := disjoint_sitesInBlocks ℓ.side h
      refine ⟨noiseAgreesOn_mix_right ℓ s (n * ℓ.side) _ _ hb _ _, fun y hy => ?_, fun b h1 h2 => ?_,
        fun b h1 h2 => ?_⟩
      · have : y ∉ c := fun h' => Finset.disjoint_left.mp h h' hy
        simp [mixChainNoise, mixStepNoise, this]
      · have : b.1 ∉ c := fun h' => Finset.disjoint_left.mp h h' h1
        simp [mixChainNoise, mixStepNoise, this]
      · have : b.1 ∉ sitesInBlocks ℓ.side c := fun h' => Finset.disjoint_left.mp hb h' h1
        simp [mixChainNoise, mixStepNoise, this]
private theorem lintegral_prod_eq_prod_lintegral_of_disjoint (ℓ : TorusLumps.StepParameters) (s n : ℕ) [NeZero n]
    {ι : Type} (A : Finset ι) (c : ι → Finset (TorusSite n)) (f : ι → ChainNoise ℓ s n → ℝ≥0∞)
    (hd : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j))
    (hm : ∀ i ∈ A, Measurable (f i))
    (hr : ∀ i ∈ A, ∀ ξ ξ', NoiseAgreesOn ℓ s n (c i) ξ ξ' → f i ξ = f i ξ') :
    ∫⁻ ξ, ∏ i ∈ A, f i ξ ∂(chainNoiseMeasure ℓ s n) = ∏ i ∈ A, ∫⁻ ξ, f i ξ ∂(chainNoiseMeasure ℓ s n) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have ih' := ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hm i (Finset.mem_insert_of_mem hi)) (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    have hg : Measurable fun ξ => ∏ i ∈ A, f i ξ :=
      Finset.measurable_prod _ fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hfa := hm a (Finset.mem_insert_self a A)
    simp_rw [Finset.prod_insert ha]
    rw [← (isMixing_mixChainNoise ℓ s n (c a)).2 (fun ξ => f a ξ * ∏ i ∈ A, f i ξ) (hfa.mul hg)]
    have hpt : ∀ ξ ξ', f a (mixChainNoise ℓ s n (c a) ξ ξ') * ∏ i ∈ A, f i (mixChainNoise ℓ s n (c a) ξ ξ') =
        f a ξ * ∏ i ∈ A, f i ξ' := by
      intro ξ ξ'
      rw [hr a (Finset.mem_insert_self a A) _ _ (noiseAgreesOn_mix_left ℓ s n _ ξ ξ')]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact hr i (Finset.mem_insert_of_mem hi) _ _
        (noiseAgreesOn_mix_right ℓ s n _ _
          (hd a (Finset.mem_insert_self a A) i (Finset.mem_insert_of_mem hi) hne) ξ ξ')
    simp_rw [hpt]
    simp_rw [lintegral_const_mul _ hg]
    rw [lintegral_mul_const _ hfa, ih']
private theorem wilsonLaw_isProbability (β : ℝ) (m : ℕ) [NeZero m] : IsProbabilityMeasure (wilsonLaw β m) := by apply _root_.YangMills.SharedProofs.p1521 <;> assumption
section Reflections
variable (G : CellGrid)
private theorem reflectionTo_of_even {κ κ' : Fin 4 → ℤ} {i : Fin 4} (h : Even (κ' i - κ i)) :
    (G.reflectionTo κ κ').axisSign i = 1 ∧ (G.reflectionTo κ κ').offset i = (G.side : ℤ) * (κ' i - κ i) := by
  simp [CellGrid.reflectionTo, h]
private theorem reflectionTo_of_odd {κ κ' : Fin 4 → ℤ} {i : Fin 4} (h : ¬ Even (κ' i - κ i)) :
    (G.reflectionTo κ κ').axisSign i = -1 ∧
      (G.reflectionTo κ κ').offset i = 2 * G.offset i + (G.side : ℤ) * (κ i + κ' i) + (G.side : ℤ) - 1 := by
  simp [CellGrid.reflectionTo, h]
private theorem pullbackBy_pullbackBy {m : ℕ} (g h g' : TorusIsometry) (hp : g.axisPerm = 1) (hp' : g'.axisPerm = 1)
    (hhp : h.axisPerm = 1) (hs : ∀ i, h.axisSign i = 1) (hsg : ∀ i, g'.axisSign i = g.axisSign i)
    (hc : ∀ x : TorusSite m, g.mapSite (h.mapSite x) = g'.mapSite x) (W : TorusField m) :
    pullbackBy h (pullbackBy g W) = pullbackBy g' W := by
  funext x k
  simp only [pullbackBy, hp, hp', hhp, Equiv.Perm.one_symm, Equiv.Perm.coe_one, id, hs, if_true, hsg, hc]
private def parity (κ κ' : Fin 4 → ℤ) : Fin 4 → Bool := fun i => decide (¬ Even (κ' i - κ i))
private def corner (κ : Fin 4 → ℤ) (τ : Fin 4 → Bool) : Fin 4 → ℤ := fun i => if τ i then κ i + 1 else κ i
private def reflectIndex (M : ℤ) (κ : Fin 4 → ℤ) (τ : Fin 4 → Bool) (κ' : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if τ i then (2 * κ i + 1 - κ' i) % M else κ' i
private theorem even_emod_sub {x y M : ℤ} (h : (2 : ℤ) ∣ M) : Even (x % M - y) ↔ Even (x - y) := by
  obtain ⟨M', rfl⟩ := h
  have e : x % (2 * M') = x - 2 * (M' * (x / (2 * M'))) := by
    rw [Int.emod_def]
    ring
  rw [e]
  generalize M' * (x / (2 * M')) = u
  rw [Int.even_iff, Int.even_iff]
  omega
private theorem parity_reflectIndex {M : ℤ} (h2 : (2 : ℤ) ∣ M) (κ κ' : Fin 4 → ℤ) (τ : Fin 4 → Bool) (i : Fin 4) :
    parity κ (reflectIndex M κ τ κ') i = xor (τ i) (parity κ κ' i) := by
  simp only [parity, reflectIndex]
  by_cases ht : τ i
  · simp only [ht, if_true]
    have : Even ((2 * κ i + 1 - κ' i) % M - κ i) ↔ ¬ Even (κ' i - κ i) := by
      rw [even_emod_sub h2, Int.even_iff, Int.even_iff]
      omega
    by_cases h : Even (κ' i - κ i) <;> simp [this, h]
  · simp [ht]
private theorem reflectIndex_mem (G : CellGrid) {m : ℕ} {M : ℤ} (hM : 0 < M) (hMm : ((m / G.side : ℕ) : ℤ) = M)
    {κ κ' : Fin 4 → ℤ} (τ : Fin 4 → Bool) (h : κ' ∈ G.indices m) : reflectIndex M κ τ κ' ∈ G.indices m := by
  simp only [CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, hMm] at h ⊢
  intro i
  simp only [reflectIndex]
  split_ifs
  · exact ⟨Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM⟩
  · exact h i
private theorem reflectIndex_reflectIndex (G : CellGrid) {m : ℕ} {M : ℤ} (hM : 0 < M)
    (hMm : ((m / G.side : ℕ) : ℤ) = M) {κ κ' : Fin 4 → ℤ} (τ : Fin 4 → Bool) (h : κ' ∈ G.indices m) :
    reflectIndex M κ τ (reflectIndex M κ τ κ') = κ' := by
  simp only [CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, hMm] at h
  funext i
  simp only [reflectIndex]
  split_ifs with ht
  · have e : (2 * κ i + 1 - κ' i) % M = 2 * κ i + 1 - κ' i - M * ((2 * κ i + 1 - κ' i) / M) := by
      rw [Int.emod_def]
    rw [e]
    have : 2 * κ i + 1 - (2 * κ i + 1 - κ' i - M * ((2 * κ i + 1 - κ' i) / M)) =
        κ' i + M * ((2 * κ i + 1 - κ' i) / M) := by ring
    rw [this, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (h i).1 (h i).2
  · rfl
private theorem pullbackBy_reflect_corner (G : CellGrid) {m : ℕ} {M : ℤ} (hMm : (G.side : ℤ) * M = m)
    (κ κ' : Fin 4 → ℤ) (τ : Fin 4 → Bool) (h2 : (2 : ℤ) ∣ M) (hp : parity κ κ' = τ) (W : TorusField m) :
    pullbackBy (G.reflectionTo κ (reflectIndex M κ τ κ')) (pullbackBy (G.reflectionTo κ (corner κ τ)) W) =
      pullbackBy (G.reflectionTo κ κ') W := by
  have hflip : ∀ i, Even (reflectIndex M κ τ κ' i - κ i) := by
    intro i
    have h := parity_reflectIndex h2 κ κ' τ i
    rw [hp] at h
    simpa [parity] using h
  have hτ : ∀ i, (τ i = true ↔ ¬ Even (κ' i - κ i)) := by
    intro i
    rw [← hp]
    simp [parity]
  have hperm : ∀ a b, (G.reflectionTo a b).axisPerm = 1 := fun _ _ => rfl
  refine pullbackBy_pullbackBy _ _ _ rfl rfl rfl (fun i => (reflectionTo_of_even G (hflip i)).1)
    (fun i => ?_) (fun x => ?_) W
  · by_cases ht : τ i = true
    · have h1 := (hτ i).1 ht
      have h2 : ¬ Even (corner κ τ i - κ i) := by simp [corner, ht]
      rw [(reflectionTo_of_odd G h1).1, (reflectionTo_of_odd G h2).1]
    · have h1 : Even (κ' i - κ i) := by_contra fun h => ht ((hτ i).2 h)
      have h2 : Even (corner κ τ i - κ i) := by simp [corner, ht]
      rw [(reflectionTo_of_even G h1).1, (reflectionTo_of_even G h2).1]
  · funext i
    simp only [TorusIsometry.mapSite, hperm, Equiv.Perm.coe_one, id]
    by_cases ht : τ i = true
    · have h1 := (hτ i).1 ht
      have ht1 : corner κ τ i = κ i + 1 := by simp [corner, ht]
      have h2 : ¬ Even (corner κ τ i - κ i) := by simp [corner, ht]
      rw [(reflectionTo_of_odd G h2).1, (reflectionTo_of_odd G h2).2, (reflectionTo_of_even G (hflip i)).1,
        (reflectionTo_of_even G (hflip i)).2, (reflectionTo_of_odd G h1).1, (reflectionTo_of_odd G h1).2, ht1]
      have hfl : reflectIndex M κ τ κ' i = 2 * κ i + 1 - κ' i - M * ((2 * κ i + 1 - κ' i) / M) := by
        simp only [reflectIndex, ht, if_true]
        rw [Int.emod_def]
      rw [hfl]
      generalize (2 * κ i + 1 - κ' i) / M = t
      have e : -((G.side : ℤ) * (2 * κ i + 1 - κ' i - M * t - κ i)) +
          (2 * G.offset i + (G.side : ℤ) * (κ i + (κ i + 1)) + (G.side : ℤ) - 1) =
          (2 * G.offset i + (G.side : ℤ) * (κ i + κ' i) + (G.side : ℤ) - 1) + (m : ℤ) * t := by
        rw [← hMm]
        ring
      have ec : ((-((G.side : ℤ) * (2 * κ i + 1 - κ' i - M * t - κ i)) +
          (2 * G.offset i + (G.side : ℤ) * (κ i + (κ i + 1)) + (G.side : ℤ) - 1) : ℤ) : ZMod m) =
          ((2 * G.offset i + (G.side : ℤ) * (κ i + κ' i) + (G.side : ℤ) - 1 : ℤ) : ZMod m) := by
        rw [e, Int.cast_add, Int.cast_mul]
        simp
      push_cast at ec ⊢
      linear_combination ec
    · have h1 : Even (κ' i - κ i) := by_contra fun h => ht ((hτ i).2 h)
      have ht1 : corner κ τ i = κ i := by simp [corner, ht]
      have ht2 : reflectIndex M κ τ κ' i = κ' i := by simp [reflectIndex, ht]
      have h2 : Even (corner κ τ i - κ i) := by simp [corner, ht]
      rw [(reflectionTo_of_even G h2).1, (reflectionTo_of_even G h2).2, (reflectionTo_of_even G (hflip i)).1,
        (reflectionTo_of_even G (hflip i)).2, (reflectionTo_of_even G h1).1, (reflectionTo_of_even G h1).2, ht1, ht2]
      push_cast
      ring
end Reflections
private theorem measurable_pullbackBy {m : ℕ} (g : TorusIsometry) :
    Measurable (pullbackBy g : TorusField m → TorusField m) := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun k => ?_
  unfold pullbackBy
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact continuous_inv.measurable.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
abbrev _root_.YangMills.SharedProofs.p130372 := @measurable_pullbackBy
section Chessboard
variable {m : ℕ} [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ) (F : TorusField m → ℝ)
open Classical in
private def cellsOfParity (τ : Fin 4 → Bool) : Finset (Fin 4 → ℤ) :=
  (G.indices m).filter fun κ' => parity κ κ' = τ
private def parityProduct (τ : Fin 4 → Bool) (W : TorusField m) : ℝ :=
  ∏ κ' ∈ cellsOfParity (m := m) G κ τ, cellCopy G κ κ' F W
private theorem parityProduct_reflect {M : ℤ} (hMm : (G.side : ℤ) * M = m) (hM : ((m / G.side : ℕ) : ℤ) = M)
    (hpos : 0 < M) (h2 : (2 : ℤ) ∣ M) (τ : Fin 4 → Bool) (W : TorusField m) :
    parityProduct G κ F τ W = parityProduct G κ F (fun _ => false) (pullbackBy (G.reflectionTo κ (corner κ τ)) W) := by
  classical
  unfold parityProduct cellsOfParity
  refine Finset.prod_nbij' (reflectIndex M κ τ) (reflectIndex M κ τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨reflectIndex_mem G hpos hM τ ha1, funext fun i => ?_⟩
    rw [parity_reflectIndex h2, ha2]
    simp
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨reflectIndex_mem G hpos hM τ ha1, funext fun i => ?_⟩
    rw [parity_reflectIndex h2, ha2]
    simp
  · intro a ha
    exact reflectIndex_reflectIndex G hpos hM τ (Finset.mem_filter.mp ha).1
  · intro a ha
    exact reflectIndex_reflectIndex G hpos hM τ (Finset.mem_filter.mp ha).1
  · intro a ha
    simp only [cellCopy]
    rw [pullbackBy_reflect_corner G hMm κ a τ h2 (Finset.mem_filter.mp ha).2 W]
variable {F}
private theorem parityProduct_nonneg (hF0 : ∀ W, 0 ≤ F W) (τ : Fin 4 → Bool) (W : TorusField m) :
    0 ≤ parityProduct G κ F τ W :=
  Finset.prod_nonneg fun _ _ => hF0 _
private theorem parityProduct_measurable (hFm : Measurable F) (τ : Fin 4 → Bool) :
    Measurable (parityProduct G κ F τ) :=
  Finset.measurable_prod _ fun _ _ => hFm.comp (measurable_pullbackBy _)
private theorem parityProduct_bound {M₀ : ℝ} (hFb : ∀ W, |F W| ≤ M₀) (τ : Fin 4 → Bool) :
    ∃ B, ∀ W, |parityProduct G κ F τ W| ≤ B := by
  refine ⟨∏ _κ' ∈ cellsOfParity (m := m) G κ τ, M₀, fun W => ?_⟩
  unfold parityProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun _ _ => hFb _
private theorem integral_le_chessboard_parity (hW : wilsonLawReflectionInvariantStatement)
    (hC : chessboardEstimateStatement)
    (β : ℝ) (hβ : 0 < β) (hfit : G.Compatible m) (hodd : Odd G.side) (hκ : κ ∈ G.indices m)
    (hFm : Measurable F) {M₀ : ℝ} (hFb : ∀ W, |F W| ≤ M₀) (hF0 : ∀ W, 0 ≤ F W)
    (hFr : DependsOnlyOn (G.cell m κ) F) :
    ∫ W, F W ∂(wilsonLaw β m) ≤
      (∫ W, parityProduct G κ F (fun _ => false) W ^ 16 ∂(wilsonLaw β m)) ^ (1 / ((G.indices m).card : ℝ)) := by
  classical
  have := wilsonLaw_isProbability β m
  obtain ⟨q, hq⟩ := hfit.two_mul_side_dvd
  have hs := hfit.side_pos
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq
      exact absurd hq (NeZero.ne m)
    · exact h
  have hdiv : m / G.side = 2 * q := by
    rw [hq, show 2 * G.side * q = G.side * (2 * q) by ring]
    exact Nat.mul_div_cancel_left _ hs
  have hMm : (G.side : ℤ) * ((2 * q : ℕ) : ℤ) = m := by
    rw [hq]
    push_cast
    ring
  have hM : ((m / G.side : ℕ) : ℤ) = ((2 * q : ℕ) : ℤ) := by rw [hdiv]
  have hpos : (0 : ℤ) < ((2 * q : ℕ) : ℤ) := by
    have : 0 < 2 * q := by omega
    exact_mod_cast this
  have h2 : (2 : ℤ) ∣ ((2 * q : ℕ) : ℤ) := ⟨q, by push_cast; ring⟩
  set P := parityProduct G κ F with hPdef
  have hP0 := parityProduct_nonneg G κ hF0
  have hPm := parityProduct_measurable G κ hFm
  have hPb := parityProduct_bound G κ hFb
  have hI : ∀ τ, Integrable (fun W => P τ W ^ 16) (wilsonLaw β m) := by
    intro τ
    obtain ⟨B, hB⟩ := hPb τ
    refine Integrable.of_bound ((hPm τ).pow_const 16).aestronglyMeasurable (B ^ 16)
      (Filter.Eventually.of_forall fun W => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB W) 16
  have hint : ∀ τ, ∫ W, P τ W ^ 16 ∂(wilsonLaw β m) = ∫ W, P (fun _ => false) W ^ 16 ∂(wilsonLaw β m) := by
    intro τ
    obtain ⟨B, hB⟩ := hPb (fun _ => false)
    have := hW β m G κ (corner κ τ) (fun W => P (fun _ => false) W ^ 16) hβ hfit ((hPm _).pow_const 16)
      ⟨B ^ 16, fun W => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB W) 16⟩
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [hPdef]
    rw [parityProduct_reflect G κ F hMm hM hpos h2 τ W]
  have hall : ∀ W, ∏ κ' ∈ G.indices m, cellCopy G κ κ' F W = ∏ τ : Fin 4 → Bool, P τ W := by
    intro W
    exact (Finset.prod_fiberwise (G.indices m) (parity κ) _).symm
  have hamgm : ∀ W, ∏ τ : Fin 4 → Bool, P τ W ≤ ∑ τ : Fin 4 → Bool, (1 / 16 : ℝ) * P τ W ^ 16 := by
    intro W
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin 4 → Bool => (1 / 16 : ℝ))
      (fun τ => P τ W ^ 16) (fun _ _ => by norm_num) (by simp) (fun τ _ => pow_nonneg (hP0 τ W) 16)
    refine le_trans (le_of_eq ?_) h
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := Real.pow_rpow_inv_natCast (hP0 τ W) (n := 16) (by norm_num)
    rw [show (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num, this]
  have hmean : copyProductMean G β κ (G.indices m) F ≤ ∫ W, P (fun _ => false) W ^ 16 ∂(wilsonLaw β m) := by
    unfold copyProductMean
    simp_rw [hall]
    calc ∫ W, ∏ τ : Fin 4 → Bool, P τ W ∂(wilsonLaw β m)
        ≤ ∫ W, ∑ τ : Fin 4 → Bool, (1 / 16 : ℝ) * P τ W ^ 16 ∂(wilsonLaw β m) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun W => Finset.prod_nonneg fun τ _ => hP0 τ W)
            (integrable_finsetSum _ fun τ _ => (hI τ).const_mul _) (Filter.Eventually.of_forall hamgm)
      _ = ∫ W, P (fun _ => false) W ^ 16 ∂(wilsonLaw β m) := by
          rw [integral_finsetSum _ fun τ _ => (hI τ).const_mul _]
          simp_rw [integral_const_mul, hint]
          simp
  have hmean0 : 0 ≤ copyProductMean G β κ (G.indices m) F := by
    refine integral_nonneg fun W => Finset.prod_nonneg fun _ _ => hF0 _
  have hone := hC β m G hβ hfit hodd
  have h1 := hone.2 {κ} (fun _ => F) (Finset.singleton_subset_iff.mpr hκ) (by
    intro κ' hκ'
    rw [Finset.mem_singleton.mp hκ']
    exact ⟨hFm, ⟨M₀, hFb⟩, hF0, hFr⟩)
  simp only [Finset.prod_singleton] at h1
  refine h1.trans ?_
  unfold chessboardNorm
  exact Real.rpow_le_rpow hmean0 hmean (by positivity)
end Chessboard
section Grid
private theorem refineBy_side (L : ℕ) : ∀ (d : ℕ) (G : CellGrid), (CellGrid.refineBy L d G).side = G.side * L ^ d
  | 0, G => by simp [CellGrid.refineBy]
  | d + 1, G => by
      rw [CellGrid.refineBy, refineBy_side L d]
      simp only [CellGrid.refine]
      ring
private theorem sitesInBlocks_mono (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : c ⊆ c') :
    sitesInBlocks L c ⊆ sitesInBlocks L c' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem cellBelow_mono (L : ℕ) [NeZero L] : ∀ (d n : ℕ) [NeZero n] {c c' : Finset (TorusSite n)}, c ⊆ c' →
    cellBelow L d n c ⊆ cellBelow L d n c'
  | 0, _, _, _, _, h => h
  | d + 1, n, _, _, _, h => cellBelow_mono L d (n * L) (sitesInBlocks_mono L h)
private theorem sitesInBlocks_cell_subset (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ) :
    sitesInBlocks L (G.cell n κ) ⊆ (G.refine L).cell (n * L) κ := by apply _root_.YangMills.SharedProofs.p122840 <;> assumption
private theorem cellBelow_subset_cell (L : ℕ) [NeZero L] : ∀ (d n : ℕ) [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ),
    cellBelow L d n (G.cell n κ) ⊆ (CellGrid.refineBy L d G).cell (fineSide L d n) κ
  | 0, _, _, _, _ => subset_rfl
  | d + 1, n, _, G, κ =>
      (cellBelow_mono L d (n * L) (sitesInBlocks_cell_subset L G κ)).trans
        (cellBelow_subset_cell L d (n * L) (G.refine L) κ)
private theorem compatible_refineBy (L : ℕ) [NeZero L] (d n : ℕ) (G : CellGrid) (h : G.Compatible n) :
    (CellGrid.refineBy L d G).Compatible (fineSide L d n) := by apply _root_.YangMills.SharedProofs.p100547 <;> assumption
private theorem indices_refineBy (L : ℕ) [NeZero L] (d n : ℕ) (G : CellGrid) :
    (CellGrid.refineBy L d G).indices (fineSide L d n) = G.indices n := by apply _root_.YangMills.SharedProofs.p32682 <;> assumption
private theorem disjoint_cell {n : ℕ} [NeZero n] (G : CellGrid) (hfit : G.Compatible n) {κ κ' : Fin 4 → ℤ}
    (h : κ ∈ G.indices n) (h' : κ' ∈ G.indices n) (hne : κ ≠ κ') : Disjoint (G.cell n κ) (G.cell n κ') := by apply _root_.YangMills.SharedProofs.p60222 <;> assumption
private theorem image_cell_add {n : ℕ} [NeZero n] (G : CellGrid) (κ κ' : Fin 4 → ℤ) :
    (G.cell n κ).image (· + siteOfInt fun i => (G.side : ℤ) * (κ' i - κ i)) = G.cell n κ' := by
  classical
  ext x
  simp only [CellGrid.cell, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨h, hh, funext fun i => ?_⟩
    simp only [siteOfInt, Pi.add_apply]
    push_cast
    ring
  · rintro ⟨h, hh, rfl⟩
    refine ⟨siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h i, ⟨h, hh, rfl⟩, funext fun i => ?_⟩
    simp only [siteOfInt, Pi.add_apply]
    push_cast
    ring
private theorem pullbackBy_of_even {m : ℕ} (G : CellGrid) {κ κ' : Fin 4 → ℤ} (h : ∀ i, Even (κ' i - κ i))
    (W : TorusField m) :
    pullbackBy (G.reflectionTo κ κ') W = TorusFields.translate (siteOfInt fun i => (G.side : ℤ) * (κ' i - κ i)) W := by
  have hs : ∀ i, (G.reflectionTo κ κ').axisSign i = 1 := fun i => by simp [CellGrid.reflectionTo, h i]
  have hsh : ∀ i, (G.reflectionTo κ κ').offset i = (G.side : ℤ) * (κ' i - κ i) := fun i => by
    simp [CellGrid.reflectionTo, h i]
  funext x k
  have hperm : (G.reflectionTo κ κ').axisPerm = 1 := rfl
  have hx : (G.reflectionTo κ κ').mapSite x = x + siteOfInt fun i => (G.side : ℤ) * (κ' i - κ i) := by
    funext i
    simp [TorusIsometry.mapSite, hperm, hs, hsh, siteOfInt]
  simp [pullbackBy, hperm, hs, hx, TorusFields.translate]
  rfl
end Grid
section Lower
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k : ℕ)
private theorem supDist_comm {n : ℕ} (x y : TorusSite n) :
    TorusFields.supDist x y = TorusFields.supDist y x := by apply _root_.YangMills.SharedProofs.p9265 <;> assumption
private theorem lowerHull_subset : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)),
    lowerHull T k s n u c ⊆ c
  | 0, n, _, u, c => by
      intro x hx
      simp only [lowerHull, Finset.mem_inter] at hx
      exact (Finset.mem_filter.mp hx.2).1
  | s + 1, n, _, u, c => by
      classical
      intro x hx
      simp only [lowerHull, thickening, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨z, hz, hd⟩ := hx
      simp only [lowerZone, windowZone, Finset.mem_inter] at hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz.2
      by_contra hxc
      have h1 := hz2 x hxc
      have h2 : TorusFields.supDist z x = TorusFields.supDist x z := supDist_comm z x
      have h3 : 1 ≤ blockDepth T k s := by
        unfold blockDepth
        omega
      have h4 : 4 * stageRange T (s + 1) ≤ blockDepth T k s := by
        unfold blockDepth
        omega
      omega
private theorem lowerScore_mul (a s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n)
    (c : Finset (TorusSite n)) (y : TorusSite n),
    lowerScore T k (a * s₀) (a * s₁) s n u c y = a * lowerScore T k s₀ s₁ s n u c y
  | 0, n, _, u, c, y => by
      simp only [lowerScore]
      split_ifs <;> simp
  | s + 1, n, _, u, c, y => by
      simp only [lowerScore]
      split_ifs
      · simp_rw [lowerScore_mul a s₀ s₁ s (n * ℓ.side)]
        rw [← Finset.mul_sum, mul_add]
      · simp
      · simp
private theorem lowerScoreSum_mul (a s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n)
    (c : Finset (TorusSite n)) :
    lowerScoreSum T k (a * s₀) (a * s₁) s n u c = a * lowerScoreSum T k s₀ s₁ s n u c := by
  unfold lowerScoreSum
  simp_rw [lowerScore_mul T k a s₀ s₁]
  rw [Finset.mul_sum]
private theorem exists_abs_lowerScore_le (s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n], ∃ B : ℝ,
    ∀ (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)) (y : TorusSite n),
    |lowerScore T k s₀ s₁ s n u c y| ≤ B
  | 0, n, _ => ⟨|s₀|, fun u c y => by
      simp only [lowerScore]
      split_ifs <;> simp⟩
  | s + 1, n, _ => by
      obtain ⟨B', hB'⟩ := exists_abs_lowerScore_le s₀ s₁ s (n * ℓ.side)
      obtain ⟨B, hB, hB0⟩ : ∃ B : ℝ, (∀ (u : MarkedSample ℓ s (n * ℓ.side)) (c : Finset (TorusSite (n * ℓ.side)))
          (y : TorusSite (n * ℓ.side)), |lowerScore T k s₀ s₁ s (n * ℓ.side) u c y| ≤ B) ∧ 0 ≤ B :=
        ⟨max B' 0, fun u c y => (hB' u c y).trans (le_max_left _ _), le_max_right _ _⟩
      refine ⟨|s₁| + (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B, fun u c y => ?_⟩
      have hsum : ∀ X : Finset (TorusSite (n * ℓ.side)),
          |∑ z ∈ X, lowerScore T k s₀ s₁ s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) z| ≤
          (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by
        intro X
        refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun z _ => hB _ _ _).trans ?_)
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ X) hB0
      have hs1 : |s₁| ≤ |s₁| + (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by
        have : 0 ≤ (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by positivity
        linarith
      simp only [lowerScore]
      split_ifs
      · exact (abs_add_le _ _).trans (by gcongr; exact hsum _)
      · simpa using hs1
      · simpa using le_trans (abs_nonneg _) hs1
private theorem exists_abs_lowerScoreSum_le (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] : ∃ B : ℝ,
    ∀ (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)), |lowerScoreSum T k s₀ s₁ s n u c| ≤ B := by
  obtain ⟨B, hB⟩ := exists_abs_lowerScore_le T k s₀ s₁ s n
  have hB0 : ∀ u c, 0 ≤ B := fun u c => le_trans (abs_nonneg _) (hB u c 0)
  refine ⟨(Fintype.card (TorusSite n) : ℝ) * B, fun u c => ?_⟩
  unfold lowerScoreSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun z _ => hB _ _ _).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (hB0 u c)
private theorem sum_lowerScoreSum_le (hB : lowerScoreLeMajorantStatement) (hH : lowerHullSubsetStageHullStatement)
    {s₀ s₁ : ℝ} (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) {ι : Type}
    (A : Finset ι) (c : ι → Finset (TorusSite n)) (hd : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j)) :
    ∑ i ∈ A, lowerScoreSum T k s₀ s₁ s n u (c i) ≤ hullMajorantSum T s₀ s₁ s n u := by
  classical
  have hmaj : ∀ z, 0 ≤ siteMajorant T s₀ s₁ s n u z := fun z =>
    (((hB ℓ T k s₀ s₁ h₀ h₁ s n u ∅).1 z).1).trans ((hB ℓ T k s₀ s₁ h₀ h₁ s n u ∅).1 z).2
  have hle : ∀ i, lowerScoreSum T k s₀ s₁ s n u (c i) ≤
      ∑ y ∈ lowerHull T k s n u (c i), siteMajorant T s₀ s₁ s n u y :=
    fun i => Finset.sum_le_sum fun y _ => ((hB ℓ T k s₀ s₁ h₀ h₁ s n u (c i)).1 y).2
  have hdis : (A : Set ι).PairwiseDisjoint fun i => lowerHull T k s n u (c i) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (lowerHull_subset T k s n u _)
      (Finset.disjoint_of_subset_right (lowerHull_subset T k s n u _) (hd i hi j hj hij))
  calc ∑ i ∈ A, lowerScoreSum T k s₀ s₁ s n u (c i)
      ≤ ∑ i ∈ A, ∑ y ∈ lowerHull T k s n u (c i), siteMajorant T s₀ s₁ s n u y :=
        Finset.sum_le_sum fun i _ => hle i
    _ = ∑ y ∈ A.biUnion fun i => lowerHull T k s n u (c i), siteMajorant T s₀ s₁ s n u y :=
        (Finset.sum_biUnion hdis).symm
    _ ≤ hullMajorantSum T s₀ s₁ s n u := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => hmaj z
        intro y hy
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
        exact ((hH ℓ T k).1 s n u (c i)) hi
end Lower
section Mean
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (S : ChainSampler T) (s₀ s₁ : ℝ) (k n : ℕ) [NeZero n]
private theorem noiseAgreesOn_refl (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) (ξ : ChainNoise ℓ s n), NoiseAgreesOn ℓ s n c ξ ξ
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, _, ξ =>
      ⟨noiseAgreesOn_refl ℓ s (n * ℓ.side) _ ξ.1, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
variable {T S s₀ s₁ k n} {c : Finset (TorusSite n)}
private theorem measurable_exp_lowerScoreSum (hl : LowerSumIsLocal T S s₀ s₁ k n c) (a : ℝ)
    (U : TorusField (fineSide ℓ.side k n)) :
    Measurable fun ξ : ChainNoise ℓ k n => Real.exp (a * lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c) :=
  Real.measurable_exp.comp (measurable_const.mul (hl.1.comp (measurable_const.prodMk measurable_id)))
private theorem integrable_exp_lowerScoreSum (hl : LowerSumIsLocal T S s₀ s₁ k n c) (a : ℝ)
    (U : TorusField (fineSide ℓ.side k n)) :
    Integrable (fun ξ : ChainNoise ℓ k n => Real.exp (a * lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c))
      (chainNoiseMeasure ℓ k n) := by
  obtain ⟨B, hB⟩ := exists_abs_lowerScoreSum_le T k s₀ s₁ k n
  refine Integrable.of_bound (measurable_exp_lowerScoreSum hl a U).aestronglyMeasurable (Real.exp (|a| * B))
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg _)
private theorem lowerSumExpMean_nonneg (U : TorusField (fineSide ℓ.side k n)) :
    0 ≤ lowerSumExpMean T S s₀ s₁ k n c U :=
  integral_nonneg fun _ => (Real.exp_pos _).le
private theorem lowerSumExpMean_measurable (hl : LowerSumIsLocal T S s₀ s₁ k n c) :
    Measurable (lowerSumExpMean T S s₀ s₁ k n c) := by
  have h : StronglyMeasurable fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
      Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n p.1 p.2) c) :=
    (Real.measurable_exp.comp hl.1).stronglyMeasurable
  exact (h.integral_prod_right' (ν := chainNoiseMeasure ℓ k n)).measurable
private theorem lowerSumExpMean_bound : ∃ M₀ : ℝ, ∀ U, |lowerSumExpMean T S s₀ s₁ k n c U| ≤ M₀ := by
  obtain ⟨B, hB⟩ := exists_abs_lowerScoreSum_le T k s₀ s₁ k n
  refine ⟨Real.exp B, fun U => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := chainNoiseMeasure ℓ k n) (C := Real.exp B)
    (f := fun ξ => Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c))
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB _ _)))
  simpa [lowerSumExpMean] using this
private theorem lowerSumExpMean_dependsOnlyOn (hl : LowerSumIsLocal T S s₀ s₁ k n c)
    {c' : Finset (TorusSite (fineSide ℓ.side k n))}
    (hc : cellBelow ℓ.side k n c ⊆ c') : DependsOnlyOn c' (lowerSumExpMean T S s₀ s₁ k n c) := by
  intro W W' h
  unfold lowerSumExpMean
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have : lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n W ξ) c =
      lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n W' ξ) c :=
    hl.2 W W' ξ ξ (fun b h1 h2 => h b (hc h1) (hc h2)) (noiseAgreesOn_refl ℓ k n c ξ)
  simp only [this]
private theorem lowerSumExpMean_pow_le (hl : LowerSumIsLocal T S s₀ s₁ k n c) (U : TorusField (fineSide ℓ.side k n)) :
    lowerSumExpMean T S s₀ s₁ k n c U ^ 16 ≤
      ∫ ξ, Real.exp (16 * lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c) ∂(chainNoiseMeasure ℓ k n) := by
  have he : ∀ x : ℝ, Real.exp x ^ 16 = Real.exp (16 * x) := fun x => by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := integrable_exp_lowerScoreSum hl 1 U
  simp only [one_mul] at h1
  have := (convexOn_pow 16).map_integral_le (μ := chainNoiseMeasure ℓ k n)
    (f := fun ξ => Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) c))
    (continuous_pow 16).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le) h1
    (by
      have h2 := integrable_exp_lowerScoreSum hl 16 U
      refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
      simp [Function.comp, he])
  simpa [lowerSumExpMean, he] using this
private theorem prod_lowerSumExpMean_pow_le (hB : lowerScoreLeMajorantStatement)
    (hH : lowerHullSubsetStageHullStatement)
    (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) {ι : Type} (A : Finset ι) (c : ι → Finset (TorusSite n))
    (hd : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j)) (hl : ∀ i ∈ A, LowerSumIsLocal T S s₀ s₁ k n (c i))
    (U : TorusField (fineSide ℓ.side k n)) :
    ENNReal.ofReal (∏ i ∈ A, lowerSumExpMean T S s₀ s₁ k n (c i) U ^ 16) ≤
      ∫⁻ ξ, ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n (sampleChain T S k n U ξ)))
        ∂(chainNoiseMeasure ℓ k n) := by
  classical
  set f : ι → ChainNoise ℓ k n → ℝ≥0∞ := fun i ξ =>
    ENNReal.ofReal (Real.exp (16 * lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) (c i))) with hf
  have hprod := lintegral_prod_eq_prod_lintegral_of_disjoint ℓ k n A c f hd
    (fun i hi => (measurable_exp_lowerScoreSum (hl i hi) 16 U).ennreal_ofReal)
    (fun i hi ξ ξ' hξ => by
      have : lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ) (c i) =
          lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n U ξ') (c i) :=
        (hl i hi).2 U U ξ ξ' (fun _ _ _ => rfl) hξ
      simp only [hf, this])
  calc ENNReal.ofReal (∏ i ∈ A, lowerSumExpMean T S s₀ s₁ k n (c i) U ^ 16)
      = ∏ i ∈ A, ENNReal.ofReal (lowerSumExpMean T S s₀ s₁ k n (c i) U ^ 16) :=
        ENNReal.ofReal_prod_of_nonneg fun i _ => pow_nonneg (lowerSumExpMean_nonneg U) 16
    _ ≤ ∏ i ∈ A, ∫⁻ ξ, f i ξ ∂(chainNoiseMeasure ℓ k n) := by
        refine Finset.prod_le_prod' fun i hi => ?_
        rw [hf]
        simp only
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_lowerScoreSum (hl i hi) 16 U)
          (Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (lowerSumExpMean_pow_le (hl i hi) U)
    _ = ∫⁻ ξ, ∏ i ∈ A, f i ξ ∂(chainNoiseMeasure ℓ k n) := hprod.symm
    _ ≤ _ := by
        refine lintegral_mono fun ξ => ?_
        simp only [hf]
        rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have := sum_lowerScoreSum_le T k hB hH (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) h₀)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) h₁) k n (sampleChain T S k n U ξ) A c hd
        simpa only [lowerScoreSum_mul] using this
end Mean
section Final
variable {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ} {S : ChainSampler T} {s₀ s₁ : ℝ} {k n : ℕ} [NeZero n]
private theorem lintegral_exp_lowerScoreSum_le (hW : wilsonLawReflectionInvariantStatement)
    (hC : chessboardEstimateStatement)
    (hB : lowerScoreLeMajorantStatement) (hH : lowerHullSubsetStageHullStatement)
    {β : ℝ} (hβ : 0 < β) (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (G : CellGrid) (κ : Fin 4 → ℤ) (hfit : G.Compatible n)
    (hodd : Odd (CellGrid.refineBy ℓ.side k G).side) (hκ : κ ∈ G.indices n)
    (hl : ∀ κ', LowerSumIsLocal T S s₀ s₁ k n (G.cell n κ'))
    (htr : ∀ κ' U, (∀ i, Even (κ' i - κ i)) →
      lowerSumExpMean T S s₀ s₁ k n (G.cell n κ)
          (TorusFields.translate (siteOfInt fun i => ((CellGrid.refineBy ℓ.side k G).side : ℤ) * (κ' i - κ i)) U) =
        lowerSumExpMean T S s₀ s₁ k n (G.cell n κ') U)
    (hdm : Measurable fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2)
    (hmap : Measure.map (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) = markedSampleLaw T β k n)
    (hMm : Measurable (hullMajorantSum T (16 * s₀) (16 * s₁) k n))
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∫⁻ u, ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n u)) ∂(markedSampleLaw T β k n) ≤
      ENNReal.ofReal D) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k n u (G.cell n κ))) ∂(markedSampleLaw T β k n) ≤
      ENNReal.ofReal (D ^ (1 / ((G.indices n).card : ℝ))) := by
  classical
  have hprob := wilsonLaw_isProbability β (fineSide ℓ.side k n)
  set Gb := CellGrid.refineBy ℓ.side k G with hGb
  have hfitb : Gb.Compatible (fineSide ℓ.side k n) := compatible_refineBy ℓ.side k n G hfit
  have hidx : Gb.indices (fineSide ℓ.side k n) = G.indices n := indices_refineBy ℓ.side k n G
  have hκb : κ ∈ Gb.indices (fineSide ℓ.side k n) := hidx ▸ hκ
  set F := lowerSumExpMean T S s₀ s₁ k n (G.cell n κ) with hF
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ U, |F U| ≤ M₀ := lowerSumExpMean_bound
  have hFm : Measurable F := lowerSumExpMean_measurable (hl κ)
  have hF0 : ∀ U, 0 ≤ F U := fun U => lowerSumExpMean_nonneg U
  have hchess := integral_le_chessboard_parity Gb κ hW hC β hβ hfitb hodd hκb hFm hM₀ hF0
    (lowerSumExpMean_dependsOnlyOn (hl κ) (cellBelow_subset_cell ℓ.side k n G κ))
  rw [hidx] at hchess
  set A := cellsOfParity (m := fineSide ℓ.side k n) Gb κ (fun _ => false) with hA
  have hAeven : ∀ κ' ∈ A, ∀ i, Even (κ' i - κ i) := by
    intro κ' hκ' i
    have := congrFun (Finset.mem_filter.mp hκ').2 i
    simpa [parity] using this
  have hAmem : ∀ κ' ∈ A, κ' ∈ G.indices n := fun κ' hκ' => hidx ▸ (Finset.mem_filter.mp hκ').1
  have hpart : ∀ W, parityProduct Gb κ F (fun _ => false) W =
      ∏ κ' ∈ A, lowerSumExpMean T S s₀ s₁ k n (G.cell n κ') W := by
    intro W
    refine Finset.prod_congr rfl fun κ' hκ' => ?_
    simp only [cellCopy]
    rw [pullbackBy_of_even Gb (hAeven κ' hκ') W]
    exact htr κ' W (hAeven κ' hκ')
  have hdis : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (G.cell n i) (G.cell n j) :=
    fun i hi j hj hij => disjoint_cell G hfit (hAmem i hi) (hAmem j hj) hij
  have hgm : Measurable fun u => ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n u)) :=
    (Real.measurable_exp.comp hMm).ennreal_ofReal
  have hI : Integrable (fun W => parityProduct Gb κ F (fun _ => false) W ^ 16) (wilsonLaw β (fineSide ℓ.side k n)) := by
    obtain ⟨B, hBd⟩ := parityProduct_bound Gb κ hM₀ (fun _ => false)
    refine Integrable.of_bound ((parityProduct_measurable Gb κ hFm _).pow_const 16).aestronglyMeasurable (B ^ 16)
      (Filter.Eventually.of_forall fun W => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hBd W) 16
  have hpow : ∫ W, parityProduct Gb κ F (fun _ => false) W ^ 16 ∂(wilsonLaw β (fineSide ℓ.side k n)) ≤ D := by
    refine (ENNReal.ofReal_le_ofReal_iff hD0).mp ?_
    rw [ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun W => pow_nonneg (parityProduct_nonneg Gb κ hF0 _ W) 16)]
    calc ∫⁻ W, ENNReal.ofReal (parityProduct Gb κ F (fun _ => false) W ^ 16) ∂(wilsonLaw β (fineSide ℓ.side k n))
        ≤ ∫⁻ W, ∫⁻ ξ, ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n (sampleChain T S k n W ξ)))
            ∂(chainNoiseMeasure ℓ k n) ∂(wilsonLaw β (fineSide ℓ.side k n)) := by
          refine lintegral_mono fun W => ?_
          rw [hpart W, ← Finset.prod_pow]
          exact prod_lowerSumExpMean_pow_le hB hH h₀ h₁ A (fun κ' => G.cell n κ') hdis (fun κ' _ => hl κ') W
      _ = ∫⁻ p, ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n (sampleChain T S k n p.1 p.2)))
            ∂((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) :=
          (lintegral_prod _ (hgm.comp hdm).aemeasurable).symm
      _ = ∫⁻ u, ENNReal.ofReal (Real.exp (hullMajorantSum T (16 * s₀) (16 * s₁) k n u)) ∂(markedSampleLaw T β k n) := by
          rw [← hmap, lintegral_map hgm hdm]
      _ ≤ ENNReal.ofReal D := hD
  have hFI : Integrable F (wilsonLaw β (fineSide ℓ.side k n)) :=
    Integrable.of_bound hFm.aestronglyMeasurable M₀
      (Filter.Eventually.of_forall fun W => by rw [Real.norm_eq_abs]; exact hM₀ W)
  have hpow0 : 0 ≤ ∫ W, parityProduct Gb κ F (fun _ => false) W ^ 16 ∂(wilsonLaw β (fineSide ℓ.side k n)) :=
    integral_nonneg fun W => pow_nonneg (parityProduct_nonneg Gb κ hF0 _ W) 16
  have hmeas : Measurable fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
      ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n p.1 p.2) (G.cell n κ))) :=
    (Real.measurable_exp.comp (hl κ).1).ennreal_ofReal
  rw [← hmap]
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k n u (G.cell n κ)))
        ∂(Measure.map (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2)
          ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)))
      ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n p.1 p.2) (G.cell n κ)))
          ∂((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) := lintegral_map_le _ _
    _ = ∫⁻ W, ∫⁻ ξ, ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k n (sampleChain T S k n W ξ) (G.cell n κ)))
          ∂(chainNoiseMeasure ℓ k n) ∂(wilsonLaw β (fineSide ℓ.side k n)) := lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ W, ENNReal.ofReal (F W) ∂(wilsonLaw β (fineSide ℓ.side k n)) := by
        refine lintegral_congr fun W => ?_
        have h1 := integrable_exp_lowerScoreSum (hl κ) 1 W
        simp only [one_mul] at h1
        rw [hF]
        unfold lowerSumExpMean
        exact (ofReal_integral_eq_lintegral_ofReal h1
          (Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (∫ W, F W ∂(wilsonLaw β (fineSide ℓ.side k n))) :=
        (ofReal_integral_eq_lintegral_ofReal hFI (Filter.Eventually.of_forall hF0)).symm
    _ ≤ ENNReal.ofReal (D ^ (1 / ((G.indices n).card : ℝ))) :=
        ENNReal.ofReal_le_ofReal (hchess.trans (Real.rpow_le_rpow hpow0 hpow (by positivity)))
private theorem lintegral_pow_le_of_lintegral_exp_le {X : Type} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ ≤ ENNReal.ofReal (Real.exp a))
    (q : ℕ) (hq : 1 ≤ q) :
    ∫⁻ x, ENNReal.ofReal (f x ^ q) ∂μ ≤ ENNReal.ofReal (((q : ℝ) + a) ^ q) := by
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp a) := by
    refine le_trans ?_ ha
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ _ := lintegral_mono fun x => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (hf x))
  have ha0 : 0 ≤ a := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos a).le] at hone
    by_contra h
    have h' : Real.exp a < Real.exp 0 := Real.exp_lt_exp.mpr (not_le.mp h)
    rw [Real.exp_zero] at h'
    linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set b : ℝ := q + a with hb
  have hb0 : 0 < b := by positivity
  set w : ℝ := q / b with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one hb0]
    linarith
  have hpt : ∀ x, f x ^ q ≤ b ^ q * (1 - w) + b ^ q * w * Real.exp (-a) * Real.exp (f x) := by
    intro x
    have h1 : f x ^ q ≤ ((q : ℝ) + f x) ^ q :=
      pow_le_pow_left₀ (hf x) (by linarith [hf x]) q
    set v : ℝ := (f x - a) / b with hv
    have h2 : (q : ℝ) + f x = b * (1 + v) := by
      rw [hv]
      field_simp
      rw [hb]
      ring
    have h3 : 0 ≤ 1 + v := by
      have : 0 ≤ b * (1 + v) := by rw [← h2]; linarith [hf x]
      exact nonneg_of_mul_nonneg_right this hb0
    have h4 : (1 + v) ^ q ≤ Real.exp (w * (f x - a)) := by
      have : (1 + v) ^ q ≤ Real.exp v ^ q := pow_le_pow_left₀ h3 (by linarith [Real.add_one_le_exp v]) q
      refine this.trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul, hv, hw]
      congr 1
      ring
    have h5 : Real.exp (w * (f x - a)) ≤ (1 - w) + w * (Real.exp (-a) * Real.exp (f x)) := by
      have := convexOn_exp.2 (Set.mem_univ (f x - a)) (Set.mem_univ (0 : ℝ)) hw0 (sub_nonneg.mpr hw1)
        (by ring)
      simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at this
      rw [← Real.exp_add]
      have e : -a + f x = f x - a := by ring
      rw [e]
      linarith
    calc f x ^ q ≤ ((q : ℝ) + f x) ^ q := h1
      _ = b ^ q * (1 + v) ^ q := by rw [h2, mul_pow]
      _ ≤ b ^ q * ((1 - w) + w * (Real.exp (-a) * Real.exp (f x))) :=
          mul_le_mul_of_nonneg_left (h4.trans h5) (by positivity)
      _ = _ := by ring
  have hc1 : 0 ≤ b ^ q * (1 - w) := mul_nonneg (by positivity) (sub_nonneg.mpr hw1)
  have hc2 : 0 ≤ b ^ q * w * Real.exp (-a) := by positivity
  calc ∫⁻ x, ENNReal.ofReal (f x ^ q) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (b ^ q * (1 - w)) +
          ENNReal.ofReal (b ^ q * w * Real.exp (-a)) * ENNReal.ofReal (Real.exp (f x))) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add hc1 (mul_nonneg hc2 (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (b ^ q * (1 - w)) +
          ENNReal.ofReal (b ^ q * w * Real.exp (-a)) * ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp
    _ ≤ ENNReal.ofReal (b ^ q * (1 - w)) +
          ENNReal.ofReal (b ^ q * w * Real.exp (-a)) * ENNReal.ofReal (Real.exp a) := by gcongr
    _ = ENNReal.ofReal (b ^ q) := by
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add hc1 (mul_nonneg hc2 (Real.exp_pos _).le)]
        congr 1
        have : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
        linear_combination (b ^ q * w) * this
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem measurable_hullMajorantSum (hA : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hfit : ℓ.Admissible) (T : StageTower ℓ)
    {a b : ℝ} (t : ℕ) (n : ℕ) [NeZero n] (hs : Measurable (labelMajorant T a b t)) :
    Measurable (hullMajorantSum T a b t n) := by
  have hsig : Measurable fun p : (Σ Y : Finset (TorusSite n), (Y → (T.stage t).labels.Ω)) =>
      ∑ y ∈ p.1, siteScore (labelMajorant T a b t) p.1 p.2 y := by
    refine measurable_sigma_of_forall fun Y => ?_
    refine Finset.measurable_sum _ fun y hy => ?_
    simp only [siteScore, hy, dif_pos]
    exact hs.comp (measurable_pi_apply (⟨y, hy⟩ : {z // z ∈ Y}))
  exact hsig.comp (measurable_snd.comp (hA ℓ hfit T t n))
end Final
private theorem le_clusterRange {c : ℕ} {x : ℝ} (h : (c : ℝ) ^ 100 ≤ x) : c ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem exists_side_eq_pow (ℓ : TorusLumps.StepParameters) (hlf : ℓ.Admissible) {r e a : ℕ}
    (hr : ℓ.side * ℓ.n₀ ≤ r) (G : CellGrid)
    (hside : G.side = baseCellSide ℓ.side r * ℓ.side ^ a) (hle : 2 * G.side ≤ 2 * ℓ.side ^ e) :
    ∃ d, 1 ≤ d ∧ d ≤ e ∧ G.side = ℓ.side ^ d ∧ ℓ.side * ℓ.n₀ ≤ 2 * ℓ.side ^ e := by
  have hL : 1 < ℓ.side := lt_of_lt_of_le (by norm_num) hlf.L_ge
  have hn₀ : 1 ≤ ℓ.n₀ := le_trans (by norm_num) hlf.n₀_ge
  have hr1 : 1 ≤ r := le_trans (Nat.mul_pos (by omega) hn₀) hr
  have hc : 1 ≤ Nat.clog ℓ.side (2 ^ 7 * r) := Nat.clog_pos hL (by omega)
  have hs : G.side = ℓ.side ^ (Nat.clog ℓ.side (2 ^ 7 * r) + a) := by
    rw [hside, baseCellSide, pow_add]
  have hde : Nat.clog ℓ.side (2 ^ 7 * r) + a ≤ e := by
    have : ℓ.side ^ (Nat.clog ℓ.side (2 ^ 7 * r) + a) ≤ ℓ.side ^ e := by
      rw [← hs]
      omega
    exact (Nat.pow_le_pow_iff_right hL).mp this
  refine ⟨_, by omega, hde, hs, ?_⟩
  have h1 : 2 ^ 7 * r ≤ ℓ.side ^ Nat.clog ℓ.side (2 ^ 7 * r) := Nat.le_pow_clog hL _
  have h2 : ℓ.side ^ Nat.clog ℓ.side (2 ^ 7 * r) ≤ ℓ.side ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  omega
private theorem card_indices (G : CellGrid) (n : ℕ) : (G.indices n).card = (n / G.side) ^ 4 := by
  unfold CellGrid.indices
  rw [Fintype.card_piFinset]
  simp only [Int.card_Ico, sub_zero, Int.toNat_natCast, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem lowerScoreMomentStatement_holds (hM : majorantExpMomentStatement) (hC : chessboardEstimateStatement)
    (hW : wilsonLawReflectionInvariantStatement) (hR : lowerSumLocalStatement)
    (hB : lowerScoreLeMajorantStatement) (hH : lowerHullSubsetStageHullStatement)
    (hN : sampleChainLawStatement) (hS : samplerExistsStatement)
    (hT : translationCarriesCellMeansStatement) (hA : ResponseInTheExpansion.StageStatesMeasurableStatement) :
    lowerScoreMomentStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₀, hrt₁, h1⟩ := hM a ha
  obtain ⟨L₂, rt₂, hrt₂, h2⟩ := hR a ha
  obtain ⟨L₃, rt₃, hrt₃, h3⟩ := hT a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (rt₁ c) (min (rt₂ c) (rt₃ c)), C₀,
    fun c => lt_min (hrt₁ c) (lt_min (hrt₂ c) (hrt₃ c)), ?_⟩
  intro L hL hLge Tb hTa hTL hDr hCS hHalf hrt hC₀ C s₁ hC0 hs₁
  have e1 : L₁ ≤ L := (le_max_left _ _).trans hLge
  have e2 : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLge
  have e3 : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLge
  obtain ⟨y₁, hy₁⟩ := h1 L hL e1 Tb hTa hTL hDr hCS hHalf (hrt.trans (min_le_left _ _)) hC₀ (16 * C) (16 * s₁)
    (by positivity) (by positivity)
  obtain ⟨y₂, hy₂⟩ := h2 L hL e2 Tb hTa hTL hDr (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, hy₃⟩ := h3 L hL e3 Tb hTa hTL hDr (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max (max y₁ y₂) (max y₃ (max Tb.floorMin (((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100))), fun y hy hrow hhas => ?_⟩
  have f1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have f2 : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have f3 : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have f4 : Tb.floorMin ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have f5 : ((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100 ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hlf : (Tb.stepParameters y).Admissible := hDr.fits y f4
  obtain ⟨C₁, C₂, hm⟩ := hy₁ y f1 hrow hhas
  have hlocal := hy₂ y f2 hrow hhas
  have hcarried := hy₃ y f3 hrow hhas
  refine ⟨C₁, C₂, fun T β s₀ k hrun h₀ hs₀ hcar e a' G κ hside hle hκ => ?_⟩
  obtain ⟨S, hSd⟩ := hS _ hlf T
  have hx0 := (hrun.onFamily.onFamily 0 (Nat.zero_le k)).le_coupling
  have hβy : y ≤ β := by
    have h := hrun.onFamily.coupling_eq 0 (Nat.zero_le _)
    have hx : (T.stage 0).toStepSetup.coupling = β := h
    rwa [hx] at hx0
  have hβ : 0 < β := lt_of_lt_of_le one_pos (hlf.y₁_ge.trans hβy)
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have hc0 := (hrun.onFamily.onFamily 0 (Nat.zero_le k)).barrierFn_eq
    have hp : T.base.barrierFn = Tb.cutoff := hc0
    rw [hp]
    exact hDr.cut
  have hxk : y ≤ (T.stage k).coupling := (hrun.onFamily.onFamily k le_rfl).le_coupling
  have hr : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ stageRange T k :=
    le_clusterRange (f5.trans hxk)
  obtain ⟨d, hd1, hde, hsd, hnL⟩ := exists_side_eq_pow (Tb.stepParameters y) hlf hr G hside hle
  have hLgt : 1 < (Tb.stepParameters y).side := lt_of_lt_of_le (by norm_num) hlf.L_ge
  have hfit : G.Compatible (2 * (Tb.stepParameters y).side ^ e) := by
    refine ⟨by rw [hsd]; exact pow_pos (by omega) d, ?_⟩
    rw [hsd]
    exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow _ hde)
  have hodd : Odd (CellGrid.refineBy (Tb.stepParameters y).side k G).side := by
    rw [refineBy_side, hsd]
    exact (hlf.L_odd.pow).mul (hlf.L_odd.pow)
  have hLn : (Tb.stepParameters y).side ∣ 2 * (Tb.stepParameters y).side ^ e :=
    Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  have h64 : 64 ≤ 2 * (Tb.stepParameters y).side ^ e := by
    have : (Tb.stepParameters y).side ≤ (Tb.stepParameters y).side ^ e := Nat.le_self_pow (by omega) _
    have := hlf.L_ge
    omega
  have hnd := hN _ hlf T S β hβ hcut hrun.measurable hSd k (2 * (Tb.stepParameters y).side ^ e) hLn h64
  have hMm := measurable_hullMajorantSum hA hlf T k (2 * (Tb.stepParameters y).side ^ e) (hcar k le_rfl).borel
  have hl := fun κ' => hlocal T S β s₀ s₁ k hrun hSd (2 * (Tb.stepParameters y).side ^ e) G κ' hfit hLn h64
  have htr : ∀ κ' U, (∀ i, Even (κ' i - κ i)) →
      lowerSumExpMean T S s₀ s₁ k (2 * (Tb.stepParameters y).side ^ e)
          (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)
          (TorusFields.translate (siteOfInt fun i => ((CellGrid.refineBy (Tb.stepParameters y).side k G).side : ℤ) *
            (κ' i - κ i)) U) =
        lowerSumExpMean T S s₀ s₁ k (2 * (Tb.stepParameters y).side ^ e)
          (G.cell (2 * (Tb.stepParameters y).side ^ e) κ') U := by
    intro κ' U _
    have hv : ∀ i, ((Tb.stepParameters y).side : ℤ) ∣ (G.side : ℤ) * (κ' i - κ i) := fun i => by
      refine Dvd.dvd.mul_right ?_ _
      rw [hsd]
      push_cast
      exact dvd_pow_self _ (by omega)
    have h := (hcarried T S β s₀ s₁ k e hrun hSd hnL _ hv (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) U).1
    rw [image_cell_add] at h
    rw [← h]
    congr 2
    funext i
    rw [refineBy_side]
    push_cast
    ring_nf
  have hD := hm T β (16 * s₀) k hrun (by positivity) (by rw [mul_assoc]; linarith) hcar e hnL
  have hfirst := lintegral_exp_lowerScoreSum_le hW hC hB hH hβ h₀ hs₁ G κ hfit hodd hκ hl htr hnd.1 hnd.2 hMm
    (Real.exp_pos _).le hD
  have hval : Real.exp ((C₁ + C₂ * Real.log (T.stage k).coupling) * (2 * ((Tb.stepParameters y).side : ℝ) ^ e) ^ 4) ^
      (1 / ((G.indices (2 * (Tb.stepParameters y).side ^ e)).card : ℝ)) =
      Real.exp ((C₁ + C₂ * Real.log (T.stage k).coupling) * (G.side : ℝ) ^ 4) := by
    rw [← Real.exp_mul, card_indices]
    congr 1
    have hdiv : 2 * (Tb.stepParameters y).side ^ e / G.side * G.side = 2 * (Tb.stepParameters y).side ^ e :=
      Nat.div_mul_cancel (dvd_trans (Dvd.intro_left 2 rfl) hfit.two_mul_side_dvd)
    have hq : ((2 * (Tb.stepParameters y).side ^ e / G.side : ℕ) : ℝ) * (G.side : ℝ) =
        2 * ((Tb.stepParameters y).side : ℝ) ^ e := by
      exact_mod_cast hdiv
    have hq0 : ((2 * (Tb.stepParameters y).side ^ e / G.side : ℕ) : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hq
      have : (0 : ℝ) < 2 * ((Tb.stepParameters y).side : ℝ) ^ e := by
        have : (0 : ℝ) < (Tb.stepParameters y).side := by
          exact_mod_cast (by omega : 0 < (Tb.stepParameters y).side)
        positivity
      linarith
    rw [← hq]
    push_cast
    field_simp
  rw [hval] at hfirst
  refine ⟨hfirst, fun q hq => ?_⟩
  have hw := wilsonLaw_isProbability β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e))
  have hprob : IsProbabilityMeasure (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) := by
    rw [← hnd.2]
    exact Measure.isProbabilityMeasure_map hnd.1.aemeasurable
  exact lintegral_pow_le_of_lintegral_exp_le _ _
    (fun u => Finset.sum_nonneg fun z _ => ((hB _ T k s₀ s₁ h₀ hs₁ k _ u _).1 z).1) _ hfirst q hq
end LowerScoreMoment
end YangMills.Construction.CellWindows
end
