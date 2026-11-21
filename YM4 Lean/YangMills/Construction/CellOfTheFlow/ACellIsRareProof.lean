import YangMills.Construction.CellOfTheFlow.ACellIsRare
import YangMills.Construction.CellOfTheFlow.ChessboardOfABareGrid
import YangMills.Construction.CellOfTheFlow.SizesOfTheWindows
import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCell
import YangMills.Construction.CellOfTheFlow.TheChainHasASampler
import YangMills.Construction.CellOfTheFlow.TheChanceOfACellHasItsValue
import YangMills.Construction.CellOfTheFlow.TheHullLiesInTheUpperWindow
import YangMills.Construction.CellOfTheFlow.TheNoiseDrawsTheChain
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal unitInterval
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
section Factorization
private def FactorsOver {X : Type} [MeasurableSpace X] (μ : Measure X) (R R' : X → X → Prop) : Prop :=
  ∀ f g : X → ℝ≥0∞, Measurable f → Measurable g → (∀ x x', R x x' → f x = f x') →
    (∀ x x', R' x x' → g x = g x') →
    ∫⁻ x, f x * g x ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ
private theorem factorsOver_dirac {X : Type} [MeasurableSpace X] (x : X) (R R' : X → X → Prop) :
    FactorsOver (Measure.dirac x) R R' := by
  intro f g hf hg _ _
  rw [lintegral_dirac' x (f := fun z => f z * g z) (hf.mul hg), lintegral_dirac' x hf, lintegral_dirac' x hg]
private theorem FactorsOver.mono {X : Type} [MeasurableSpace X] {μ : Measure X} {R R' Q Q' : X → X → Prop}
    (h : FactorsOver μ R R') (hq : ∀ x x', R x x' → Q x x') (hq' : ∀ x x', R' x x' → Q' x x') :
    FactorsOver μ Q Q' :=
  fun f g hf hg hfr hgr => h f g hf hg (fun x x' e => hfr x x' (hq x x' e)) (fun x x' e => hgr x x' (hq' x x' e))
private theorem FactorsOver.prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} [SFinite μ] [SFinite ν] {R R' : X → X → Prop} {S S' : Y → Y → Prop}
    (hR : ∀ x, R x x) (hR' : ∀ x, R' x x) (hS : ∀ y, S y y) (hS' : ∀ y, S' y y)
    (h₁ : FactorsOver μ R R') (h₂ : FactorsOver ν S S') :
    FactorsOver (μ.prod ν) (fun p q => R p.1 q.1 ∧ S p.2 q.2) (fun p q => R' p.1 q.1 ∧ S' p.2 q.2) := by
  intro f g hf hg hfr hgr
  rw [lintegral_prod (fun z => f z * g z) (hf.mul hg).aemeasurable, lintegral_prod f hf.aemeasurable,
    lintegral_prod g hg.aemeasurable]
  have inner : ∀ x, ∫⁻ y, f (x, y) * g (x, y) ∂ν = (∫⁻ y, f (x, y) ∂ν) * ∫⁻ y, g (x, y) ∂ν := fun x =>
    h₂ (fun y => f (x, y)) (fun y => g (x, y)) (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
      (fun y y' e => hfr _ _ ⟨hR x, e⟩) (fun y y' e => hgr _ _ ⟨hR' x, e⟩)
  simp_rw [inner]
  refine h₁ (fun x => ∫⁻ y, f (x, y) ∂ν) (fun x => ∫⁻ y, g (x, y) ∂ν) hf.lintegral_prod_right'
    hg.lintegral_prod_right' ?_ ?_
  · intro x x' e
    exact lintegral_congr fun y => hfr _ _ ⟨e, hS y⟩
  · intro x x' e
    exact lintegral_congr fun y => hgr _ _ ⟨e, hS' y⟩
abbrev _root_.YangMills.DeltaSharedProofs.p502163 := @FactorsOver.prod
private theorem factorsOver_pi {J : Type} [Fintype J] (D D' : Set J) (hd : Disjoint D D') :
    FactorsOver (Measure.pi fun _ : J => (volume : Measure I))
      (fun x x' => ∀ j ∈ D, x j = x' j) (fun x x' => ∀ j ∈ D', x j = x' j) := by
  classical
  intro f g hf hg hfr hgr
  let p : J → Prop := fun j => j ∈ D
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => I) p
  have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : J => (volume : Measure I)) p
  let f' : (∀ j : {j // p j}, I) → ℝ≥0∞ := fun w => f (e.symm (w, fun _ => 0))
  let g' : (∀ j : {j // ¬ p j}, I) → ℝ≥0∞ := fun v => g (e.symm (fun _ => 0, v))
  have hf' : Measurable f' := hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hg' : Measurable g' := hg.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have ef : ∀ x, f x = f' (e x).1 := by
    intro x
    refine hfr _ _ fun j hj => ?_
    have : (e.symm ((e x).1, fun _ => 0)) j = (e x).1 ⟨j, hj⟩ := by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, p, hj]
    rw [this]
    rfl
  have eg : ∀ x, g x = g' (e x).2 := by
    intro x
    refine hgr _ _ fun j hj => ?_
    have hn : ¬ p j := fun h => Set.disjoint_left.1 hd h hj
    have : (e.symm (fun _ => 0, (e x).2)) j = (e x).2 ⟨j, hn⟩ := by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hn]
    rw [this]
    rfl
  set μ₁ := Measure.pi fun _ : {j // p j} => (volume : Measure I)
  set μ₂ := Measure.pi fun _ : {j // ¬ p j} => (volume : Measure I)
  have key : ∀ (a : (∀ j : {j // p j}, I) → ℝ≥0∞) (b : (∀ j : {j // ¬ p j}, I) → ℝ≥0∞), Measurable a →
      Measurable b → ∫⁻ x, a (e x).1 * b (e x).2 ∂(Measure.pi fun _ : J => (volume : Measure I)) =
        (∫⁻ w, a w ∂μ₁) * ∫⁻ v, b v ∂μ₂ := by
    intro a b ha hb
    have h1 : Measurable fun z : (∀ j : {j // p j}, I) × (∀ j : {j // ¬ p j}, I) => a z.1 * b z.2 :=
      (ha.comp measurable_fst).mul (hb.comp measurable_snd)
    rw [← lintegral_prod_mul ha.aemeasurable hb.aemeasurable]
    exact mp.lintegral_comp h1
  have h1 : ∫⁻ x, f x ∂(Measure.pi fun _ : J => (volume : Measure I)) = ∫⁻ w, f' w ∂μ₁ := by
    have := key f' (fun _ => 1) hf' measurable_const
    simpa [← ef] using this
  have h2 : ∫⁻ x, g x ∂(Measure.pi fun _ : J => (volume : Measure I)) = ∫⁻ v, g' v ∂μ₂ := by
    have := key (fun _ => 1) g' measurable_const hg'
    simpa [← eg] using this
  rw [h1, h2, ← key f' g' hf' hg']
  exact lintegral_congr fun x => by rw [ef x, eg x]
abbrev _root_.YangMills.DeltaSharedProofs.p501219 := @factorsOver_pi
end Factorization
section Noise
variable (ℓ : StepParameters)
private theorem noiseAgreesOn_refl : ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (ξ : ChainNoise ℓ s n),
    NoiseAgreesOn ℓ s n c ξ ξ
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, c, ξ =>
    ⟨noiseAgreesOn_refl s (n * ℓ.side) _ ξ.1, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
private theorem sitesInBlocks_mono {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : c ⊆ c') :
    sitesInBlocks ℓ.side c ⊆ sitesInBlocks ℓ.side c' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem noiseAgreesOn_anti : ∀ (s n : ℕ) [NeZero n] {c c' : Finset (TorusSite n)} (_ : c ⊆ c')
    (ξ ξ' : ChainNoise ℓ s n), NoiseAgreesOn ℓ s n c' ξ ξ' → NoiseAgreesOn ℓ s n c ξ ξ'
  | 0, _, _, _, _, _, _, _, _ => trivial
  | s + 1, n, _, c, c', h, ξ, ξ', e =>
    ⟨noiseAgreesOn_anti s (n * ℓ.side) (sitesInBlocks_mono ℓ h) _ _ e.1, fun y hy => e.2.1 y (h hy),
      fun b h₁ h₂ => e.2.2.1 b (h h₁) (h h₂),
      fun b h₁ h₂ => e.2.2.2 b (sitesInBlocks_mono ℓ h h₁) (sitesInBlocks_mono ℓ h h₂)⟩
private theorem chainNoiseMeasure_isProb : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseMeasure ℓ s n)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac () : Measure Unit)
    infer_instance
  | s + 1, n, _ => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := chainNoiseMeasure_isProb s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
      unfold stepNoiseMeasure
      infer_instance
    show IsProbabilityMeasure ((chainNoiseMeasure ℓ s (n * ℓ.side)).prod (stepNoiseMeasure ℓ n))
    infer_instance
private theorem sitesInBlocks_disjoint {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : Disjoint c c') :
    Disjoint (sitesInBlocks ℓ.side c) (sitesInBlocks ℓ.side c') := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact h hx hx'
abbrev _root_.YangMills.SharedProofs.p27072 := @sitesInBlocks_disjoint
private def StepNoiseAgreesOn {n : ℕ} [NeZero n] (c : Finset (TorusSite n)) (ξ ξ' : StepNoise ℓ n) : Prop :=
  (∀ y ∈ c, ξ.1 y = ξ'.1 y) ∧
    (∀ b : TorusBond n, b.1 ∈ c → b.1 + unitStep n b.2 ∈ c → ξ.2.1 b = ξ'.2.1 b) ∧
    (∀ b : TorusBond (n * ℓ.side), b.1 ∈ sitesInBlocks ℓ.side c →
      b.1 + unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c → ξ.2.2 b = ξ'.2.2 b)
private theorem stepNoise_factors {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : Disjoint c c') :
    FactorsOver (stepNoiseMeasure ℓ n) (StepNoiseAgreesOn ℓ c) (StepNoiseAgreesOn ℓ c') := by
  have hb := sitesInBlocks_disjoint ℓ h
  have h₁ := factorsOver_pi (J := TorusSite n) (↑c) (↑c') (Finset.disjoint_coe.2 h)
  have h₂ := factorsOver_pi (J := TorusBond n) {b | b.1 ∈ c ∧ b.1 + unitStep n b.2 ∈ c}
    {b | b.1 ∈ c' ∧ b.1 + unitStep n b.2 ∈ c'}
    (Set.disjoint_left.2 fun b hb₁ hb₂ => Finset.disjoint_left.1 h hb₁.1 hb₂.1)
  have h₃ := factorsOver_pi (J := TorusBond (n * ℓ.side))
    {b | b.1 ∈ sitesInBlocks ℓ.side c ∧ b.1 + unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c}
    {b | b.1 ∈ sitesInBlocks ℓ.side c' ∧ b.1 + unitStep (n * ℓ.side) b.2 ∈ sitesInBlocks ℓ.side c'}
    (Set.disjoint_left.2 fun b hb₁ hb₂ => Finset.disjoint_left.1 hb hb₁.1 hb₂.1)
  have h₂₃ := FactorsOver.prod (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) h₂ h₃
  have h₁₂₃ := FactorsOver.prod (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩) (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩) h₁ h₂₃
  refine FactorsOver.mono h₁₂₃ ?_ ?_
  · rintro x x' ⟨a, b, d⟩
    exact ⟨a, fun b' u v => b b' ⟨u, v⟩, fun b' u v => d b' ⟨u, v⟩⟩
  · rintro x x' ⟨a, b, d⟩
    exact ⟨a, fun b' u v => b b' ⟨u, v⟩, fun b' u v => d b' ⟨u, v⟩⟩
private theorem chainNoise_factors : ∀ (s n : ℕ) [NeZero n] {c c' : Finset (TorusSite n)} (_ : Disjoint c c'),
    FactorsOver (chainNoiseMeasure ℓ s n) (NoiseAgreesOn ℓ s n c) (NoiseAgreesOn ℓ s n c')
  | 0, n, _, c, c', _ => factorsOver_dirac (X := ChainNoise ℓ 0 n) () _ _
  | s + 1, n, _, c, c', h => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := chainNoiseMeasure_isProb ℓ s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
      unfold stepNoiseMeasure
      infer_instance
    have h₁ := chainNoise_factors s (n * ℓ.side) (sitesInBlocks_disjoint ℓ h)
    have h₂ := stepNoise_factors ℓ h
    have := FactorsOver.prod (noiseAgreesOn_refl ℓ s (n * ℓ.side) _) (noiseAgreesOn_refl ℓ s (n * ℓ.side) _)
      (fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩)
      (fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩) h₁ h₂
    exact this
private theorem chainNoise_indep {ι : Type} {n s : ℕ} [NeZero n] (A : Finset ι) (c : ι → Finset (TorusSite n))
    (hc : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j)) (B : ι → Set (ChainNoise ℓ s n))
    (hB : ∀ i ∈ A, MeasurableSet (B i))
    (hr : ∀ i ∈ A, ∀ ξ ξ', NoiseAgreesOn ℓ s n (c i) ξ ξ' → (ξ ∈ B i ↔ ξ' ∈ B i)) :
    chainNoiseMeasure ℓ s n {ξ | ∀ i ∈ A, ξ ∈ B i} = ∏ i ∈ A, chainNoiseMeasure ℓ s n (B i) := by
  classical
  haveI := chainNoiseMeasure_isProb ℓ s n
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have ih' := ih (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hB i (Finset.mem_insert_of_mem hi)) (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, ← ih']
    set C : Set (ChainNoise ℓ s n) := {ξ | ∀ i ∈ A, ξ ∈ B i} with hC
    have hCm : MeasurableSet C := by
      have : C = ⋂ i ∈ A, B i := by
        ext ξ
        simp [hC]
      rw [this]
      exact Finset.measurableSet_biInter _ fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hBa := hB a (Finset.mem_insert_self _ _)
    have hdis : Disjoint (c a) (A.biUnion c) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hc a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi))
    have key := chainNoise_factors ℓ s n hdis (B a |>.indicator 1) (C.indicator 1)
      (measurable_one.indicator hBa) (measurable_one.indicator hCm) ?_ ?_
    · have e1 : ∫⁻ x, (B a).indicator (1 : ChainNoise ℓ s n → ℝ≥0∞) x ∂(chainNoiseMeasure ℓ s n) =
          chainNoiseMeasure ℓ s n (B a) :=
        lintegral_indicator_one hBa
      have e2 : ∫⁻ x, C.indicator (1 : ChainNoise ℓ s n → ℝ≥0∞) x ∂(chainNoiseMeasure ℓ s n) =
          chainNoiseMeasure ℓ s n C :=
        lintegral_indicator_one hCm
      have e3 : (fun x => (B a).indicator (1 : ChainNoise ℓ s n → ℝ≥0∞) x * C.indicator 1 x) =
          (B a ∩ C).indicator 1 := by
        funext x
        by_cases h₁ : x ∈ B a <;> by_cases h₂ : x ∈ C <;> simp [h₁, h₂]
      rw [e1, e2, e3, lintegral_indicator_one (hBa.inter hCm)] at key
      rw [← key]
      congr 1
      ext ξ
      simp only [Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp, Set.mem_inter_iff, hC]
    · intro ξ ξ' e
      have := hr a (Finset.mem_insert_self _ _) ξ ξ' e
      simp only [Set.indicator, this, Pi.one_apply]
    · intro ξ ξ' e
      have : ξ ∈ C ↔ ξ' ∈ C := by
        simp only [hC, Set.mem_setOf_eq]
        refine forall₂_congr fun i hi => ?_
        exact hr i (Finset.mem_insert_of_mem hi) ξ ξ'
          (noiseAgreesOn_anti ℓ s n (Finset.subset_biUnion_of_mem c hi) ξ ξ' e)
      simp only [Set.indicator, this, Pi.one_apply]
end Noise
section Cells
private theorem cell_disjoint {n : ℕ} [NeZero n] (G : CellGrid) (hG : G.Compatible n) {κ κ' : Fin 4 → ℤ}
    (hκ : κ ∈ G.indices n) (hκ' : κ' ∈ G.indices n) (hne : κ ≠ κ') :
    Disjoint (G.cell n κ) (G.cell n κ') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨h', hh', e⟩ := hx'
  apply hne
  funext i
  have hi := congrFun e i
  simp only [siteOfInt] at hi
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
  have hs : (0 : ℤ) < G.side := by exact_mod_cast hG.side_pos
  obtain ⟨N, hN⟩ : G.side ∣ n := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hG.two_mul_side_dvd
  have hNdiv : n / G.side = N := by
    rw [hN]
    exact Nat.mul_div_cancel_left N hG.side_pos
  have hnZ : (n : ℤ) = G.side * N := by exact_mod_cast hN
  have m₁ := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hκ i)
  have m₂ := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hκ' i)
  rw [hNdiv] at m₁ m₂
  obtain ⟨a₁, a₂⟩ := hh i
  obtain ⟨b₁, b₂⟩ := hh' i
  set t : ℤ := κ' i - κ i with ht
  have t₁ : t ≤ N - 1 := by omega
  have t₂ : -(N - 1 : ℤ) ≤ t := by omega
  have d₁ : (G.side : ℤ) * t ≤ G.side * (N - 1) := mul_le_mul_of_nonneg_left t₁ hs.le
  have d₂ : (G.side : ℤ) * (-(N - 1 : ℤ)) ≤ G.side * t := mul_le_mul_of_nonneg_left t₂ hs.le
  have hd : G.offset i + (G.side : ℤ) * κ' i + h' i - (G.offset i + (G.side : ℤ) * κ i + h i) =
      G.side * t + (h' i - h i) := by
    rw [ht]
    ring
  rw [hd] at hi
  have habs : |(G.side : ℤ) * t + (h' i - h i)| < n := by
    rw [abs_lt, hnZ]
    constructor <;> nlinarith
  have hz := Int.eq_zero_of_abs_lt_dvd hi habs
  have : t = 0 := by
    rcases lt_trichotomy t 0 with h0 | h0 | h0
    · have : (G.side : ℤ) * t ≤ G.side * (-1) := mul_le_mul_of_nonneg_left (by omega) hs.le
      nlinarith
    · exact h0
    · have : (G.side : ℤ) * 1 ≤ G.side * t := mul_le_mul_of_nonneg_left (by omega) hs.le
      nlinarith
  omega
abbrev _root_.YangMills.SharedProofs.p60222 := @cell_disjoint
variable (L : ℕ) [NeZero L]
private theorem sitesInBlocks_subset {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : c ⊆ c') :
    sitesInBlocks L c ⊆ sitesInBlocks L c' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem sitesInBlocks_cell_subset {n : ℕ} [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ) :
    sitesInBlocks L (G.cell n κ) ⊆ (G.refine L).cell (n * L) κ := by
  classical
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, CellGrid.cell] at hx ⊢
  obtain ⟨h, hh, e⟩ := hx
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨fun i => (L : ℤ) * h i + ((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ)), fun i => ?_, ?_⟩
  · have r₁ := Int.emod_nonneg (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) hL.ne'
    have r₂ := Int.emod_lt_of_pos (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) hL
    obtain ⟨a₁, a₂⟩ := hh i
    have hs : ((G.refine L).side : ℤ) = (G.side : ℤ) * L := by
      simp [CellGrid.refine]
    rw [hs]
    constructor
    · have : 0 ≤ (L : ℤ) * h i := mul_nonneg hL.le a₁
      linarith
    · have : (L : ℤ) * h i ≤ L * ((G.side : ℤ) - 1) := mul_le_mul_of_nonneg_left (by omega) hL.le
      nlinarith
  · funext i
    have hi := congrFun e i
    simp only [parentBlock, siteOfInt] at hi
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    obtain ⟨q, hq⟩ := hi
    have hdiv := Int.emod_add_mul_ediv (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) (L : ℤ)
    have hx : x i = ((((x i).cast : ℤ)) : ZMod (n * L)) := (ZMod.intCast_zmod_cast (x i)).symm
    show x i = (((G.refine L).offset i + ((G.refine L).side : ℤ) * κ i + ((L : ℤ) * h i +
      ((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ))) : ℤ) : ZMod (n * L))
    conv_lhs => rw [hx]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨q, ?_⟩
    simp only [CellGrid.refine]
    push_cast
    linear_combination (L : ℤ) * hq + hdiv
abbrev _root_.YangMills.SharedProofs.p122840 := @sitesInBlocks_cell_subset
private theorem cellBelow_subset : ∀ (d n : ℕ) [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ)
    (c : Finset (TorusSite n)),
    c ⊆ G.cell n κ → cellBelow L d n c ⊆ (CellGrid.refineBy L d G).cell (fineSide L d n) κ
  | 0, _, _, _, _, _, h => h
  | d + 1, n, _, G, κ, c, h =>
    cellBelow_subset d (n * L) (G.refine L) κ (sitesInBlocks L c)
      ((sitesInBlocks_subset L h).trans (sitesInBlocks_cell_subset L G κ))
private theorem refineBy_side : ∀ (d : ℕ) (G : CellGrid), (CellGrid.refineBy L d G).side = G.side * L ^ d
  | 0, G => by simp [CellGrid.refineBy]
  | d + 1, G => by
    rw [CellGrid.refineBy, refineBy_side d (G.refine L)]
    simp only [CellGrid.refine]
    ring
private theorem refineBy_indices (d n : ℕ) (G : CellGrid) :
    (CellGrid.refineBy L d G).indices (fineSide L d n) = G.indices n := by
  have hL : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  unfold CellGrid.indices
  rw [refineBy_side, fineSide_eq, Nat.mul_div_mul_right _ _ hL]
abbrev _root_.YangMills.SharedProofs.p32682 := @refineBy_indices
private theorem refineBy_compatible (d n : ℕ) (G : CellGrid) (h : G.Compatible n) :
    (CellGrid.refineBy L d G).Compatible (fineSide L d n) := by
  have hL : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  refine ⟨?_, ?_⟩
  · rw [refineBy_side]
    exact Nat.mul_pos h.side_pos hL
  · rw [refineBy_side, fineSide_eq, ← mul_assoc]
    exact mul_dvd_mul h.two_mul_side_dvd dvd_rfl
abbrev _root_.YangMills.SharedProofs.p100547 := @refineBy_compatible
private theorem interiorAtDepth_anti {n : ℕ} [NeZero n] {m m' : ℕ} (h : m ≤ m') (c : Finset (TorusSite n)) :
    interiorAtDepth m' c ⊆ interiorAtDepth m c := by
  classical
  intro v hv
  simp only [interiorAtDepth, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, fun w hw => h.trans (hv.2 w hw)⟩
abbrev _root_.YangMills.SharedProofs.p56231 := @interiorAtDepth_anti
private theorem dependsOnlyOn_mono {m : ℕ} [NeZero m] {c c' : Finset (TorusSite m)} {F : TorusField m → ℝ}
    (h : c ⊆ c') (hF : DependsOnlyOn c F) : DependsOnlyOn c' F :=
  fun W W' e => hF W W' fun b h₁ h₂ => e b (h h₁) (h h₂)
end Cells
section Measurability
variable {ℓ : StepParameters}
private theorem measurableSet_fibre_of_three {X A B C D : Type} [MeasurableSpace X] [Countable A] [Countable B]
    [Countable C] (a : X → A) (b : X → B) (c : X → C) (ha : ∀ v, MeasurableSet {x | a x = v})
    (hb : ∀ v, MeasurableSet {x | b x = v}) (hc : ∀ v, MeasurableSet {x | c x = v})
    (Φ : A → B → C → D) (d : D) : MeasurableSet {x | Φ (a x) (b x) (c x) = d} := by
  have e : {x | Φ (a x) (b x) (c x) = d} =
      ⋃ p : A × B × C, ⋃ _ : Φ p.1 p.2.1 p.2.2 = d,
        {x | a x = p.1} ∩ ({x | b x = p.2.1} ∩ {x | c x = p.2.2}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, Prod.exists]
    constructor
    · intro h
      exact ⟨_, _, _, h, rfl, rfl, rfl⟩
    · rintro ⟨_, _, _, h, rfl, rfl, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => (ha _).inter ((hb _).inter (hc _))
private theorem upperHull_measurableSet_fibre
    (hW : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (T : StageTower ℓ) (k : ℕ) : ∀ (s n : ℕ) [NeZero n] (c H : Finset (TorusSite n)),
      MeasurableSet {u : MarkedSample ℓ s n | upperHull T k s n u c = H}
  | 0, n, _, c, H => by
    let R₀ : StepSetup := { T.base.toStepSetup with nextCoupling := T.base.coupling }
    exact measurableSet_fibre_of_three (X := TorusField n) (fun V => hotCoreSites R₀ V) (fun _ => ()) (fun _ => ())
      (hW R₀ n) (fun _ => by simp) (fun _ => by simp)
      (fun a _ _ => a ∩ interiorAtDepth (windowDepth T k 0) c) H
  | s + 1, n, _, c, H => by
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    have ih := upperHull_measurableSet_fibre hW T k s (n * ℓ.side) (sitesInBlocks ℓ.side c)
    have hV : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hb : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    exact measurableSet_fibre_of_three (X := MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n)
      (B := Finset (TorusBond (n * ℓ.side)))
      (fun u => hotCoreSites (T.stage s).toStepSetup u.2.2.1)
      (fun u => (u.2.2.2 : Finset (TorusBond (n * ℓ.side))))
      (fun u => upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c))
      (fun a => hV (hW _ n a))
      (fun a => hb (show MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) from MeasurableSpace.measurableSet_top))
      (fun a => measurable_fst (ih a))
      (fun C bad Y => interiorAtDepth (windowDepth T k (s + 1)) c ∩ thickening (stageRange T (s + 1) / 2)
        (upperZone T k s C bad Y c)) H
private theorem cellEvent_measurableSet
    (hW : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (T : StageTower ℓ) (k n : ℕ) [NeZero n] (c : Finset (TorusSite n)) :
    MeasurableSet {u : MarkedSample ℓ k n | CellEvent T k n u c} := by
  have e : {u : MarkedSample ℓ k n | CellEvent T k n u c} =
      ⋃ H : Finset (TorusSite n), ⋃ _ : (H ∩ interiorAtDepth (8 * stageRange T k) c).Nonempty,
        {u : MarkedSample ℓ k n | upperHull T k k n u c = H} := by
    ext u
    simp only [CellEvent, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨_, h, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun H => MeasurableSet.iUnion fun _ => upperHull_measurableSet_fibre hW T k k n c H
end Measurability
section Law
variable {ℓ : StepParameters}
private theorem markedSampleLaw_cells_le (T : StageTower ℓ) (S : ChainSampler T) (β : ℝ) (k n : ℕ) [NeZero n]
    [IsFiniteMeasure (wilsonLaw β (fineSide ℓ.side k n))]
    (hlaw : Measure.map (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) = markedSampleLaw T β k n)
    (A : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → Finset (TorusSite n))
    (hc : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j))
    (hloc : ∀ i ∈ A, CellEventIsLocal T S k n (c i))
    (hset : MeasurableSet {u : MarkedSample ℓ k n | ∀ i ∈ A, CellEvent T k n u (c i)})
    (hF : ∀ i ∈ A, Measurable (cellEventProb T S k n (c i)))
    (hF₀ : ∀ i ∈ A, ∀ U, 0 ≤ cellEventProb T S k n (c i) U ∧ cellEventProb T S k n (c i) U ≤ 1) :
    markedSampleLaw T β k n {u | ∀ i ∈ A, CellEvent T k n u (c i)} ≤
      ENNReal.ofReal (∫ U, ∏ i ∈ A, cellEventProb T S k n (c i) U ∂(wilsonLaw β (fineSide ℓ.side k n))) := by
  classical
  haveI := chainNoiseMeasure_isProb ℓ k n
  rw [← hlaw]
  by_cases hm : AEMeasurable
      (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n))
  · rw [Measure.map_apply_of_aemeasurable hm hset]
    set E : Set (TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n) :=
      (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n => sampleChain T S k n p.1 p.2) ⁻¹'
        {u | ∀ i ∈ A, CellEvent T k n u (c i)} with hE
    have hEm : MeasurableSet E := by
      have : E = ⋂ i ∈ A, {p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n |
          CellEvent T k n (sampleChain T S k n p.1 p.2) (c i)} := by
        ext p
        simp [hE]
      rw [this]
      exact Finset.measurableSet_biInter _ fun i hi => (hloc i hi).1
    rw [Measure.prod_apply hEm]
    have hsec : ∀ U, chainNoiseMeasure ℓ k n (Prod.mk U ⁻¹' E) =
        ENNReal.ofReal (∏ i ∈ A, cellEventProb T S k n (c i) U) := by
      intro U
      have h₁ := chainNoise_indep ℓ A c hc
        (fun i => {ξ | CellEvent T k n (sampleChain T S k n U ξ) (c i)})
        (fun i hi => measurable_prodMk_left (hloc i hi).1)
        (fun i hi ξ ξ' e => (hloc i hi).2 U U ξ ξ' (fun _ _ _ => rfl) e)
      have h₂ : Prod.mk U ⁻¹' E =
          {ξ | ∀ i ∈ A, ξ ∈ {ξ | CellEvent T k n (sampleChain T S k n U ξ) (c i)}} := rfl
      rw [h₂, h₁, ENNReal.ofReal_prod_of_nonneg fun i hi => (hF₀ i hi U).1]
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold cellEventProb
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp_rw [hsec]
    have hmeas : Measurable fun U => ∏ i ∈ A, cellEventProb T S k n (c i) U :=
      Finset.measurable_prod _ fun i hi => hF i hi
    have hint : Integrable (fun U => ∏ i ∈ A, cellEventProb T S k n (c i) U)
        (wilsonLaw β (fineSide ℓ.side k n)) := by
      refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun U => ?_)
      rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i hi => (hF₀ i hi U).1)]
      exact Finset.prod_le_one (fun i hi => (hF₀ i hi U).1) fun i hi => (hF₀ i hi U).2
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun U => Finset.prod_nonneg fun i hi => (hF₀ i hi U).1)]
  · rw [Measure.map_of_not_aemeasurable hm]
    simp
end Law
private theorem holdsAtAdmissibleParameters_and {P Q : ParameterAssignment → ℝ → Prop}
    (h₁ : HoldsAtAdmissibleParameters P) (h₂ : HoldsAtAdmissibleParameters Q) :
    HoldsAtAdmissibleParameters fun T y => P T y ∧ Q T y := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLe T hTa hTL hD hrt
  obtain ⟨y₁, Y₁⟩ := H₁ L hL (le_of_max_le_left hLe) T hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, Y₂⟩ := H₂ L hL (le_of_max_le_right hLe) T hTa hTL hD (hrt.trans (min_le_right _ _))
  exact ⟨max y₁ y₂, fun y hy hr hw =>
    ⟨Y₁ y (le_of_max_le_left hy) hr hw, Y₂ y (le_of_max_le_right hy) hr hw⟩⟩
abbrev _root_.YangMills.SharedProofs.p114722 := @holdsAtAdmissibleParameters_and
private theorem holdsAtAdmissibleParameters_mono {P Q : ParameterAssignment → ℝ → Prop}
    (h : ∀ T y, T.Admissible → T.floorMin ≤ y → P T y → Q T y) (hP : HoldsAtAdmissibleParameters P) :
    HoldsAtAdmissibleParameters Q := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := hP a ha
  refine ⟨L₁, r₁, hr₁, ?_⟩
  intro L hL hLe T hTa hTL hD hrt
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hLe T hTa hTL hD hrt
  exact ⟨max y₁ T.floorMin, fun y hy hr hw =>
    h T y hD (le_of_max_le_right hy) (Y₁ y (le_of_max_le_left hy) hr hw)⟩
theorem cellEventsRare (hC : cellEventProbChessboardBoundStatement) (hB : chessboardEstimateStatement)
    (hR : cellEventIsLocalStatement) (hU : stageHullInterSubsetUpperHullStatement)
    (hZ : windowDepthBoundStatement) (hN : sampleChainLawStatement)
    (hS : samplerExistsStatement) (hW : ResponseInTheExpansion.chainMeasurabilityStatement) :
    cellEventsRareStatement := by
  classical
  refine holdsAtAdmissibleParameters_mono ?_
    (holdsAtAdmissibleParameters_and (holdsAtAdmissibleParameters_and (holdsAtAdmissibleParameters_and hC hR) hU) hZ)
  rintro Tb y hD hy ⟨⟨⟨hC', hR'⟩, hU'⟩, hZ'⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy
  intro T β k hrun e G A hside hle hA
  have hL2 : 2 ≤ (Tb.stepParameters y).side := T.two_le_side
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hodd : Odd (Tb.stepParameters y).side := hfit.L_odd
  have hGs : G.side = (Tb.stepParameters y).side ^
      Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) := hside
  have hfits : G.Compatible (2 * (Tb.stepParameters y).side ^ e) := by
    refine ⟨by rw [hGs]; exact pow_pos hLpos _, ?_⟩
    have h₁ : G.side ≤ (Tb.stepParameters y).side ^ e := by omega
    rw [hGs] at h₁ ⊢
    have h₂ := (Nat.pow_le_pow_iff_right (by omega)).1 h₁
    exact mul_dvd_mul_left 2 (pow_dvd_pow _ h₂)
  have hoddG : Odd G.side := by
    rw [hGs]
    exact hodd.pow
  obtain ⟨S, hSd⟩ := hS _ hfit T
  have hy1 : 1 ≤ y := by
    have h₁ : (2 : ℝ) ^ 1600 ≤ Tb.floorMin := le_max_right _ _
    have h₂ : (1 : ℝ) ≤ 2 ^ 1600 := one_le_pow₀ (by norm_num)
    exact h₂.trans (h₁.trans hy)
  have hβ : 0 < β := by
    have h₁ : (T.stage 0).coupling = β := hrun.onFamily.coupling_eq 0 (Nat.zero_le _)
    have h₂ : y ≤ (T.stage 0).coupling := (hrun.onFamily.onFamily 0 (Nat.zero_le _)).le_coupling
    linarith
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h₁ : (T.stage 0).toStepSetup.barrierFn = Tb.cutoff := (hrun.onFamily.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    have h₂ : T.base.barrierFn = Tb.cutoff := h₁
    rw [h₂]
    exact hD.cut
  have he : e ≠ 0 := by
    have hx : y ≤ (T.stage k).coupling := (hrun.onFamily.onFamily k le_rfl).le_coupling
    have hr : 1 ≤ stageRange T k := by
      have hx₀ : 0 < (T.stage k).coupling := by linarith
      exact Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx₀ _)
    have hc : 0 < Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) :=
      Nat.clog_pos (by omega) (by omega)
    have h₁ : G.side ≤ (Tb.stepParameters y).side ^ e := by omega
    rw [hGs] at h₁
    have h₂ := (Nat.pow_le_pow_iff_right (by omega)).1 h₁
    omega
  have hdvd : (Tb.stepParameters y).side ∣ 2 * (Tb.stepParameters y).side ^ e :=
    dvd_mul_of_dvd_right (dvd_pow_self _ he) 2
  have h64 : 64 ≤ 2 * (Tb.stepParameters y).side ^ e := by
    have h₁ : (Tb.stepParameters y).side ≤ (Tb.stepParameters y).side ^ e := Nat.le_self_pow he _
    have h₂ : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
    omega
  have hlaw := (hN _ hfit T S β hβ hcut hrun.measurable hSd k (2 * (Tb.stepParameters y).side ^ e) hdvd h64).2
  haveI : IsProbabilityMeasure
      (wilsonLaw β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e))) :=
    (hW.2.2 _ hfit hfit.depth_lt T hcut hrun.measurable β 0
      (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e))).1
  have hBor := hW.1
  have hupper : ∀ (u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ e))
      (κ : Fin 4 → ℤ),
      (stageHull T k _ u ∩ interiorAtDepth (8 * stageRange T k)
        (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)).Nonempty →
      CellEvent T k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) := by
    rintro u κ ⟨z, hz⟩
    have hz₁ := Finset.mem_inter.1 hz
    have hz₂ : z ∈ interiorAtDepth (windowDepth T k k) (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) :=
      interiorAtDepth_anti (hZ' T β k hrun).2 _ hz₁.2
    have hz₃ := hU' T β k hrun k le_rfl _ u G κ hfits (Finset.mem_inter.2 ⟨hz₁.1, hz₂⟩)
    exact ⟨z, Finset.mem_inter.2 ⟨hz₃, hz₁.2⟩⟩
  have hfirst : markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)
      {u | ∀ κ ∈ A, CellEvent T k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)} ≤
      ENNReal.ofReal (cellEventBound Tb (T.stage k).coupling ^ A.card) := by
    have hch := fun (κ : Fin 4 → ℤ) (hκ : κ ∈ A) => hC' T S β k hrun hSd e G κ hside hle (hA hκ)
    have hset : MeasurableSet {u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ e) |
        ∀ κ ∈ A, CellEvent T k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)} := by
      have e₁ : {u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ e) |
          ∀ κ ∈ A, CellEvent T k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)} =
          ⋂ κ ∈ A, {u | CellEvent T k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)} := by
        ext u
        simp
      rw [e₁]
      exact Finset.measurableSet_biInter _ fun κ _ => cellEvent_measurableSet hBor T k _ _
    refine (markedSampleLaw_cells_le T S β k _ hlaw A (fun κ => G.cell (2 * (Tb.stepParameters y).side ^ e) κ)
      ?_ ?_ hset ?_ ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · intro i hi j hj hij
      exact cell_disjoint G hfits (hA hi) (hA hj) hij
    · exact fun i _ => hR' T S β k hrun hSd _ G i hdvd h64 hfits
    · exact fun i hi => (hch i hi).1
    · exact fun i hi U => (hch i hi).2.1 U
    · have hG' := refineBy_compatible (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e) G hfits
      have hodd' : Odd (CellGrid.refineBy (Tb.stepParameters y).side k G).side := by
        rw [refineBy_side]
        exact hoddG.mul hodd.pow
      have hIdx := refineBy_indices (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e) G
      obtain ⟨hb₁, hb₂⟩ := hB β _ _ hβ hG' hodd'
      have hreads : ∀ κ ∈ A, DependsOnlyOn ((CellGrid.refineBy (Tb.stepParameters y).side k G).cell
          (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e)) κ)
          (cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)) := fun κ hκ =>
        dependsOnlyOn_mono (cellBelow_subset (Tb.stepParameters y).side k _ G κ _ subset_rfl) (hch κ hκ).2.2.1
      have hbnd : ∀ κ ∈ A, ∃ M, ∀ W, |cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
          (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) W| ≤ M := fun κ hκ =>
        ⟨1, fun W => by
          rw [abs_of_nonneg ((hch κ hκ).2.1 W).1]
          exact ((hch κ hκ).2.1 W).2⟩
      have h₁ := hb₂ A (fun κ => cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
          (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)) (by rw [hIdx]; exact hA)
        (fun κ hκ => ⟨(hch κ hκ).1, hbnd κ hκ, fun W => ((hch κ hκ).2.1 W).1, hreads κ hκ⟩)
      refine h₁.trans ?_
      have h₂ : ∏ κ ∈ A, chessboardNorm (CellGrid.refineBy (Tb.stepParameters y).side k G) β κ
          (cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)) ≤
          ∏ _κ ∈ A, cellEventBound Tb (T.stage k).coupling :=
        Finset.prod_le_prod
          (fun κ hκ => Real.rpow_nonneg
            (hb₁ κ _ (by rw [hIdx]; exact hA hκ) (hch κ hκ).1 (hbnd κ hκ) (hreads κ hκ)) _)
          (fun κ hκ => (hch κ hκ).2.2.2)
      simpa using h₂
  refine ⟨hfirst, hupper, ?_, fun S' hS' κ => hR' T S' β k hrun hS' _ G κ hdvd h64 hfits⟩
  refine (measure_mono ?_).trans hfirst
  intro u hu κ hκ
  exact hupper u κ (hu κ hκ)
end YangMills.Construction.CellWindows
end
