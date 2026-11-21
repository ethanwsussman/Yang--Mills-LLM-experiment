import YangMills.Construction.CellOfTheFlow.ACellIsRareProof
import YangMills.Construction.HullsInEveryVolume.CopiesByTranslationsOfTheChain
import YangMills.Construction.HullsInEveryVolume.EvenTranslatesBoundACopy
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal unitInterval
namespace YangMills.Construction.ChainNoise
open ChessboardGrids TorusFields TorusLumps WeightedResponses
section Independence
private def SplitsUnder {X : Type} [MeasurableSpace X] (μ : Measure X) (R R' : X → X → Prop) : Prop :=
  ∀ f g : X → ℝ≥0∞, Measurable f → Measurable g → (∀ x x', R x x' → f x = f x') →
    (∀ x x', R' x x' → g x = g x') →
    ∫⁻ x, f x * g x ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ
private theorem splitsUnder_dirac {X : Type} [MeasurableSpace X] (x : X) (R R' : X → X → Prop) :
    SplitsUnder (Measure.dirac x) R R' := by
  intro f g hf hg _ _
  rw [lintegral_dirac' x (f := fun z => f z * g z) (hf.mul hg), lintegral_dirac' x hf, lintegral_dirac' x hg]
private theorem SplitsUnder.mono {X : Type} [MeasurableSpace X] {μ : Measure X} {R R' Q Q' : X → X → Prop}
    (h : SplitsUnder μ R R') (hq : ∀ x x', R x x' → Q x x') (hq' : ∀ x x', R' x x' → Q' x x') : SplitsUnder μ Q Q' :=
  fun f g hf hg hfr hgr => h f g hf hg (fun x x' e => hfr x x' (hq x x' e)) (fun x x' e => hgr x x' (hq' x x' e))
private theorem SplitsUnder.prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {R R' : X → X → Prop} {S S' : Y → Y → Prop}
    (hR : ∀ x, R x x) (hR' : ∀ x, R' x x) (hS : ∀ y, S y y) (hS' : ∀ y, S' y y)
    (h₁ : SplitsUnder μ R R') (h₂ : SplitsUnder ν S S') :
    SplitsUnder (μ.prod ν) (fun p q => R p.1 q.1 ∧ S p.2 q.2) (fun p q => R' p.1 q.1 ∧ S' p.2 q.2) := by apply _root_.YangMills.DeltaSharedProofs.p502163 <;> assumption
private theorem splitsUnder_pi {J : Type} [Fintype J] (D D' : Set J) (hd : Disjoint D D') :
    SplitsUnder (Measure.pi fun _ : J => (volume : Measure I))
      (fun x x' => ∀ j ∈ D, x j = x' j) (fun x x' => ∀ j ∈ D', x j = x' j) := by apply _root_.YangMills.DeltaSharedProofs.p501219 <;> assumption
private theorem measurePreserving_pi_comp_perm {J : Type} [Fintype J] (e : J ≃ J) :
    MeasurePreserving (fun (x : J → I) j => x (e j)) (Measure.pi fun _ : J => (volume : Measure I))
      (Measure.pi fun _ : J => (volume : Measure I)) := by apply _root_.YangMills.SharedProofs.p46286 <;> assumption
end Independence
section Noise
variable (ℓ : StepParameters)
private theorem noiseAgreeAbove_refl : ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (ξ : ChainNoise ℓ s n),
    NoiseAgreeAbove ℓ s n c ξ ξ
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, c, ξ => ⟨noiseAgreeAbove_refl s (n * ℓ.side) _ ξ.1, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem sitesInBlocks_mono {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : c ⊆ c') :
    sitesInBlocks ℓ.side c ⊆ sitesInBlocks ℓ.side c' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem noiseAgreeAbove_anti : ∀ (s n : ℕ) [NeZero n] {c c' : Finset (TorusSite n)} (_ : c ⊆ c')
    (ξ ξ' : ChainNoise ℓ s n), NoiseAgreeAbove ℓ s n c' ξ ξ' → NoiseAgreeAbove ℓ s n c ξ ξ'
  | 0, _, _, _, _, _, _, _, _ => trivial
  | s + 1, n, _, c, c', h, ξ, ξ', e =>
    ⟨noiseAgreeAbove_anti s (n * ℓ.side) (sitesInBlocks_mono ℓ h) _ _ e.1, fun y hy => e.2.1 y (h hy),
      fun b h₁ => e.2.2.1 b (h h₁), fun b h₁ => e.2.2.2 b (h h₁)⟩
private theorem isProbabilityMeasure_chainNoiseLaw : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac () : Measure Unit)
    infer_instance
  | s + 1, n, _ => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := isProbabilityMeasure_chainNoiseLaw s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    show IsProbabilityMeasure ((chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n))
    infer_instance
private theorem sitesInBlocks_disjoint {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : Disjoint c c') :
    Disjoint (sitesInBlocks ℓ.side c) (sitesInBlocks ℓ.side c') := by apply _root_.YangMills.SharedProofs.p27072 <;> assumption
private def StepAgreeOn {n : ℕ} (c : Finset (TorusSite n)) (ξ ξ' : StepNoise ℓ n) : Prop :=
  (∀ y ∈ c, ξ.1 y = ξ'.1 y) ∧ (∀ b : TorusBond n, b.1 ∈ c → ξ.2.1 b = ξ'.2.1 b) ∧
    ∀ b : TorusBond (n * ℓ.side), parentBlock ℓ.side b.1 ∈ c → ξ.2.2 b = ξ'.2.2 b
private theorem stepNoiseLaw_splits {n : ℕ} [NeZero n] {c c' : Finset (TorusSite n)} (h : Disjoint c c') :
    SplitsUnder (stepNoiseLaw ℓ n) (StepAgreeOn ℓ c) (StepAgreeOn ℓ c') := by
  have h₁ := splitsUnder_pi (J := TorusSite n) (↑c) (↑c') (Finset.disjoint_coe.2 h)
  have h₂ := splitsUnder_pi (J := TorusBond n) {b | b.1 ∈ c} {b | b.1 ∈ c'}
    (Set.disjoint_left.2 fun b hb₁ hb₂ => Finset.disjoint_left.1 h hb₁ hb₂)
  have h₃ := splitsUnder_pi (J := TorusBond (n * ℓ.side)) {b | parentBlock ℓ.side b.1 ∈ c}
    {b | parentBlock ℓ.side b.1 ∈ c'}
    (Set.disjoint_left.2 fun b hb₁ hb₂ => Finset.disjoint_left.1 h hb₁ hb₂)
  have h₂₃ := SplitsUnder.prod (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) h₂ h₃
  have h₁₂₃ := SplitsUnder.prod (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩) (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩) h₁ h₂₃
  refine SplitsUnder.mono h₁₂₃ ?_ ?_
  · rintro x x' ⟨a, b, d⟩
    exact ⟨a, fun b' u => b b' u, fun b' u => d b' u⟩
  · rintro x x' ⟨a, b, d⟩
    exact ⟨a, fun b' u => b b' u, fun b' u => d b' u⟩
private theorem chainNoiseLaw_splits : ∀ (s n : ℕ) [NeZero n] {c c' : Finset (TorusSite n)} (_ : Disjoint c c'),
    SplitsUnder (chainNoiseLaw ℓ s n) (NoiseAgreeAbove ℓ s n c) (NoiseAgreeAbove ℓ s n c')
  | 0, n, _, c, c', _ => splitsUnder_dirac (X := ChainNoise ℓ 0 n) () _ _
  | s + 1, n, _, c, c', h => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := isProbabilityMeasure_chainNoiseLaw ℓ s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    have h₁ := chainNoiseLaw_splits s (n * ℓ.side) (sitesInBlocks_disjoint ℓ h)
    have h₂ := stepNoiseLaw_splits ℓ h
    have h₃ := SplitsUnder.prod (noiseAgreeAbove_refl ℓ s (n * ℓ.side) _) (noiseAgreeAbove_refl ℓ s (n * ℓ.side) _)
      (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩)
      (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩) h₁ h₂
    refine SplitsUnder.mono h₃ ?_ ?_
    · rintro x x' ⟨a, b, d, e⟩
      exact ⟨a, b, fun c' hc => d c' hc, fun b' hb => e b' (by simpa [sitesInBlocks] using hb)⟩
    · rintro x x' ⟨a, b, d, e⟩
      exact ⟨a, b, fun c' hc => d c' hc, fun b' hb => e b' (by simpa [sitesInBlocks] using hb)⟩
private theorem lintegral_prod_of_disjoint_cells {ι : Type} {n s : ℕ} [NeZero n] (A : Finset ι)
    (c : ι → Finset (TorusSite n))
    (hc : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j)) (f : ι → ChainNoise ℓ s n → ℝ≥0∞)
    (hf : ∀ i ∈ A, Measurable (f i))
    (hr : ∀ i ∈ A, ∀ ξ ξ', NoiseAgreeAbove ℓ s n (c i) ξ ξ' → f i ξ = f i ξ') :
    ∫⁻ ξ, ∏ i ∈ A, f i ξ ∂(chainNoiseLaw ℓ s n) = ∏ i ∈ A, ∫⁻ ξ, f i ξ ∂(chainNoiseLaw ℓ s n) := by
  classical
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ s n
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have ih' := ih (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    have hdis : Disjoint (c a) (A.biUnion c) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hc a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi) (fun e => ha (e ▸ hi))
    have key := chainNoiseLaw_splits ℓ s n hdis (f a) (fun ξ => ∏ i ∈ A, f i ξ)
      (hf a (Finset.mem_insert_self _ _))
      (Finset.measurable_prod _ fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hr a (Finset.mem_insert_self _ _))
      (fun ξ ξ' e => Finset.prod_congr rfl fun i hi => hr i (Finset.mem_insert_of_mem hi) ξ ξ'
        (noiseAgreeAbove_anti ℓ s n (Finset.subset_biUnion_of_mem c hi) ξ ξ' e))
    simp_rw [Finset.prod_insert ha]
    rw [key, ih']
private theorem integral_prod_of_disjoint_cells {ι : Type} {n s : ℕ} [NeZero n] (A : Finset ι)
    (c : ι → Finset (TorusSite n))
    (hc : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j)) (f : ι → ChainNoise ℓ s n → ℝ)
    (hf : ∀ i ∈ A, Measurable (f i)) (h0 : ∀ i ∈ A, ∀ ξ, 0 ≤ f i ξ)
    (hr : ∀ i ∈ A, ∀ ξ ξ', NoiseAgreeAbove ℓ s n (c i) ξ ξ' → f i ξ = f i ξ') :
    ∫ ξ, ∏ i ∈ A, f i ξ ∂(chainNoiseLaw ℓ s n) = ∏ i ∈ A, ∫ ξ, f i ξ ∂(chainNoiseLaw ℓ s n) := by
  have e : ∀ h : ChainNoise ℓ s n → ℝ, Measurable h → (∀ ξ, 0 ≤ h ξ) →
      ∫ ξ, h ξ ∂(chainNoiseLaw ℓ s n) = (∫⁻ ξ, ENNReal.ofReal (h ξ) ∂(chainNoiseLaw ℓ s n)).toReal :=
    fun h hm hp => integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp) hm.aestronglyMeasurable
  rw [e _ (Finset.measurable_prod _ hf) fun ξ => Finset.prod_nonneg fun i hi => h0 i hi ξ]
  have h1 : ∀ ξ, ENNReal.ofReal (∏ i ∈ A, f i ξ) = ∏ i ∈ A, ENNReal.ofReal (f i ξ) := fun ξ =>
    ENNReal.ofReal_prod_of_nonneg fun i hi => h0 i hi ξ
  simp_rw [h1]
  rw [lintegral_prod_of_disjoint_cells ℓ A c hc (fun i ξ => ENNReal.ofReal (f i ξ))
    (fun i hi => (hf i hi).ennreal_ofReal)
    (fun i hi ξ ξ' h => by rw [hr i hi ξ ξ' h]), ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i hi => (e _ (hf i hi) (h0 i hi)).symm
private theorem measurePreserving_noiseTranslate : ∀ (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ),
    MeasurePreserving (noiseTranslate ℓ u n h) (chainNoiseLaw ℓ u n) (chainNoiseLaw ℓ u n)
  | 0, n, _, h => MeasurePreserving.id (chainNoiseLaw ℓ 0 n)
  | u + 1, n, _, h => by
    letI := instMeasurableSpaceChainNoise ℓ u (n * ℓ.side)
    haveI := isProbabilityMeasure_chainNoiseLaw ℓ u (n * ℓ.side)
    have h0 := measurePreserving_noiseTranslate u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i)
    have h1 := measurePreserving_pi_comp_perm (J := TorusSite n) (Equiv.addRight (siteOfInt h))
    have h2 := measurePreserving_pi_comp_perm (J := TorusBond n)
      ((Equiv.addRight (siteOfInt h)).prodCongr (Equiv.refl _))
    have h3 := measurePreserving_pi_comp_perm (J := TorusBond (n * ℓ.side))
      ((Equiv.addRight (siteOfInt fun i => (ℓ.side : ℤ) * h i)).prodCongr (Equiv.refl _))
    exact h0.prod (h1.prod (h2.prod h3))
end Noise
section Cells
private def shiftPreimage {n : ℕ} [NeZero n] (h : Fin 4 → ℤ) (Q : Finset (TorusSite n)) : Finset (TorusSite n) :=
  open Classical in Finset.univ.filter fun y => y - siteOfInt h ∈ Q
private theorem parentBlock_add_siteOfInt {L n : ℕ} [NeZero L] [NeZero n] (x : TorusSite (n * L)) (h : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt fun i => (L : ℤ) * h i) = parentBlock L x + siteOfInt h := by
  have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  funext i
  simp only [parentBlock, Pi.add_apply, siteOfInt]
  set X : ℤ := ((x i).cast : ℤ) with hXd
  set X' : ℤ := ((x i + (((L : ℤ) * h i : ℤ) : ZMod (n * L))).cast : ℤ) with hX'd
  have hX : ((X : ℤ) : ZMod (n * L)) = x i := ZMod.intCast_zmod_cast _
  have hX' : ((X' : ℤ) : ZMod (n * L)) = x i + (((L : ℤ) * h i : ℤ) : ZMod (n * L)) := ZMod.intCast_zmod_cast _
  have hd : ((X' - (X + (L : ℤ) * h i) : ℤ) : ZMod (n * L)) = 0 := by
    rw [Int.cast_sub, Int.cast_add, hX, hX']
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hd
  push_cast at hk
  have e : X' + ((L : ℤ) - 1) / 2 = (X + ((L : ℤ) - 1) / 2) + (L : ℤ) * (h i + (n : ℤ) * k) := by
    linear_combination hk
  rw [e, Int.add_mul_ediv_left _ _ hL0]
  push_cast
  simp
private theorem noiseAgreeAbove_noiseTranslate (ℓ : StepParameters) : ∀ (u n : ℕ) [NeZero n]
    (Q : Finset (TorusSite n)) (h : Fin 4 → ℤ)
    (U U' : ChainNoise ℓ u n), NoiseAgreeAbove ℓ u n (shiftPreimage h Q) U U' →
      NoiseAgreeAbove ℓ u n Q (noiseTranslate ℓ u n h U) (noiseTranslate ℓ u n h U')
  | 0, _, _, _, _, _, _, _ => trivial
  | u + 1, n, _, Q, h, U, U', e => by
    have hb : ∀ b : TorusSite (n * ℓ.side), parentBlock ℓ.side b ∈ Q →
        parentBlock ℓ.side (b + siteOfInt fun i => (ℓ.side : ℤ) * h i) ∈ shiftPreimage h Q := by
      intro b hb
      simp only [shiftPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [parentBlock_add_siteOfInt]
      simpa using hb
    have hsub : shiftPreimage (fun i => (ℓ.side : ℤ) * h i) (sitesInBlocks ℓ.side Q) ⊆
        sitesInBlocks ℓ.side (shiftPreimage h Q) := by
      intro x hx
      simp only [shiftPreimage, sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have := parentBlock_add_siteOfInt (L := ℓ.side) (n := n) (x - siteOfInt fun i => (ℓ.side : ℤ) * h i) h
      rw [sub_add_cancel] at this
      rw [this]
      simpa using hx
    refine ⟨noiseAgreeAbove_noiseTranslate ℓ u (n * ℓ.side) _ _ _ _
      (noiseAgreeAbove_anti ℓ u (n * ℓ.side) hsub _ _ e.1), ?_, ?_, ?_⟩
    · intro y hy
      exact e.2.1 _ (by simpa [shiftPreimage] using hy)
    · intro c hc
      exact e.2.2.1 (c.1 + siteOfInt h, c.2) (by simpa [shiftPreimage] using hc)
    · intro b hb'
      exact e.2.2.2 (b.1 + siteOfInt (fun i => (ℓ.side : ℤ) * h i), b.2) (hb _ hb')
private theorem cellIndex_atDepth_one {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L) (g : MirrorGrid)
    (x : TorusSite (n * L)) :
    (g.atDepth L 1).cellIndex x = g.cellIndex (parentBlock L x) := by
  have hLp : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLp
  obtain ⟨a, ha⟩ := hL
  have hhalf : ((L : ℤ) - 1) / 2 = a := by
    rw [ha]; push_cast; omega
  funext i
  simp only [MirrorGrid.cellIndex, MirrorGrid.atDepth, parentBlock, pow_one]
  rw [hhalf]
  set o := g.offset i with ho
  set X : ℤ := ((x i).cast : ℤ) with hXd
  have hX : ((X : ℤ) : ZMod (n * L)) = x i := ZMod.intCast_zmod_cast _
  set q : ℤ := (X + a) / (L : ℤ) with hq
  set r : ℤ := (X + a) % (L : ℤ) with hr
  have hqr : X + a = (L : ℤ) * q + r := (Int.mul_ediv_add_emod _ _).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hLz.ne'
  have hrL : r < L := Int.emod_lt_of_pos _ hLz
  obtain ⟨rN, hrN⟩ := Int.eq_ofNat_of_zero_le hr0
  have hrN' : rN < L := by omega
  set T : ℕ := (((q : ℤ) : ZMod n) - ((o + 1 : ℤ) : ZMod n)).val with hT
  have hTn : T < n := ZMod.val_lt _
  have hTc : ((T : ℤ) : ZMod n) = ((q - (o + 1) : ℤ) : ZMod n) := by
    rw [Int.cast_natCast, hT, ZMod.natCast_zmod_val]
    push_cast
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hTc
  have hV : (x i - ((((L : ℤ) * o + a + 1 : ℤ)) : ZMod (n * L))).val = L * T + rN := by
    have hz : x i - ((((L : ℤ) * o + a + 1 : ℤ)) : ZMod (n * L)) = ((L * T + rN : ℕ) : ZMod (n * L)) := by
      have e : X - ((L : ℤ) * o + a + 1) = ((L * T + rN : ℕ) : ℤ) + ((n * L : ℕ) : ℤ) * k := by
        have ha' : (L : ℤ) = 2 * a + 1 := by rw [ha]; push_cast; ring
        push_cast
        rw [← hrN]
        linear_combination hqr + (L : ℤ) * hk + ha'
      have e2 := congrArg (fun z : ℤ => (z : ZMod (n * L))) e
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, hX, ZMod.natCast_self,
        zero_mul, add_zero] at e2
      rw [← e2]
      push_cast
      ring
    rw [hz, ZMod.val_natCast_of_lt]
    calc L * T + rN < L * T + L := by omega
      _ = L * (T + 1) := by ring
      _ ≤ L * n := Nat.mul_le_mul_left _ hTn
      _ = n * L := Nat.mul_comm _ _
  rw [hV, Nat.mul_comm g.side L, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hLp,
    Nat.div_eq_of_lt hrN', Nat.add_zero]
abbrev _root_.YangMills.SharedProofs.p15019 := @cellIndex_atDepth_one
private theorem atDepth_zero (L : ℕ) (g : MirrorGrid) : g.atDepth L 0 = g := by
  simp [MirrorGrid.atDepth]
private theorem atDepth_succ {L : ℕ} (hL : Odd L) (g : MirrorGrid) (u : ℕ) :
    g.atDepth L (u + 1) = (g.atDepth L 1).atDepth L u := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := (Odd.pow ⟨a, ha⟩ : Odd (L ^ u))
  have hbz : ((L : ℤ)) ^ u = 2 * b + 1 := by exact_mod_cast hb
  have haz : (L : ℤ) = 2 * a + 1 := by exact_mod_cast ha
  have h1 : ((L : ℤ) ^ u - 1) / 2 = b := by rw [hbz]; omega
  have h2 : ((L : ℤ) ^ 1 - 1) / 2 = a := by rw [pow_one, haz]; omega
  have h3 : ((L : ℤ) ^ (u + 1) - 1) / 2 = 2 * a * b + a + b := by
    have : (L : ℤ) ^ (u + 1) - 1 = 2 * (2 * a * b + a + b) := by
      rw [pow_succ, hbz, haz]; ring
    rw [this]; omega
  unfold MirrorGrid.atDepth
  congr 1
  · simp only [pow_succ, pow_zero, one_mul]; ring
  · funext i
    simp only []
    rw [h1, h2, h3, pow_succ, hbz, pow_one]
    rw [haz]
    ring
private theorem sitesUnder_mono (L : ℕ) [NeZero L] : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' →
    sitesUnder L u n Q ⊆ sitesUnder L u n Q'
  | 0, _, _, _, _, h => h
  | u + 1, n, _, Q, Q', h => sitesUnder_mono L u (n * L) (fun x hx => by
      simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact h hx)
private theorem sitesUnder_cellSites_subset {L : ℕ} [NeZero L] (hL : Odd L) : ∀ (u n : ℕ) [NeZero n] (g : MirrorGrid)
    (c : Fin 4 → ℕ),
    sitesUnder L u n (g.cellSites n c) ⊆ (g.atDepth L u).cellSites (fineSide L u n) c
  | 0, n, _, g, c => by
    rw [atDepth_zero]
    exact fun x hx => hx
  | u + 1, n, _, g, c => by
    have hstep : sitesInBlocks L (g.cellSites n c) ⊆ (g.atDepth L 1).cellSites (n * L) c := by
      intro x hx
      simp only [sitesInBlocks, MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [cellIndex_atDepth_one hL, hx]
    rw [atDepth_succ hL]
    exact (sitesUnder_mono L u (n * L) hstep).trans (sitesUnder_cellSites_subset hL u (n * L) (g.atDepth L 1) c)
private theorem cellSites_subset_recentre {N : ℕ} [NeZero N] (G : MirrorGrid) (hs : 0 < G.side) (c : Fin 4 → ℕ) :
    G.cellSites N c ⊆ (G.recentre c).cellSites N 0 := by
  intro x hx
  simp only [MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  funext i
  have h1 := congrFun hx i
  simp only [MirrorGrid.cellIndex] at h1 ⊢
  simp only [MirrorGrid.recentre, Pi.zero_apply]
  set v := (x i - ((G.offset i + 1 : ℤ) : ZMod N)).val with hv
  have hvN : v < N := ZMod.val_lt _
  have hlo : c i * G.side ≤ v := by rw [← h1]; exact Nat.div_mul_le_self _ _
  have hhi : v < (c i + 1) * G.side := by
    have : v / G.side < c i + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hs).1 this
  have hz : x i - ((G.offset i + (c i : ℤ) * (G.side : ℤ) + 1 : ℤ) : ZMod N) =
      ((v - c i * G.side : ℕ) : ZMod N) := by
    rw [Nat.cast_sub hlo, hv, ZMod.natCast_zmod_val]
    push_cast
    ring
  have hexp : (c i + 1) * G.side = c i * G.side + G.side := by ring
  rw [hz, ZMod.val_natCast_of_lt (by omega)]
  exact Nat.div_eq_of_lt (by omega)
private theorem shiftPreimage_disjoint {n : ℕ} [NeZero n] (g : MirrorGrid) (hs : 0 < g.side) (hn : 2 * g.side ∣ n)
    (c : Fin 4 → ℕ) {e e' : Fin 4 → ℕ} (he : e ∈ g.evenTranslations n) (he' : e' ∈ g.evenTranslations n)
    (hne : e ≠ e') :
    Disjoint (shiftPreimage (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) (g.cellSites n c))
      (shiftPreimage (fun i => 2 * (g.side : ℤ) * (e' i : ℤ)) (g.cellSites n c)) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  simp only [shiftPreimage, MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have h1 := congrFun hy i
  have h2 := congrFun hy' i
  simp only [MirrorGrid.cellIndex, Pi.sub_apply, siteOfInt] at h1 h2
  obtain ⟨E, hE⟩ := hn
  have hdiv : n / (2 * g.side) = E := by
    rw [hE]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hei : e i < E := by
    have := Fintype.mem_piFinset.1 he i
    rwa [Finset.mem_range, hdiv] at this
  have hei' : e' i < E := by
    have := Fintype.mem_piFinset.1 he' i
    rwa [Finset.mem_range, hdiv] at this
  set a := (y i - ((2 * (g.side : ℤ) * (e i : ℤ) : ℤ) : ZMod n) - ((g.offset i + 1 : ℤ) : ZMod n)).val with ha
  set a' := (y i - ((2 * (g.side : ℤ) * (e' i : ℤ) : ℤ) : ZMod n) - ((g.offset i + 1 : ℤ) : ZMod n)).val with ha'
  have hac : ((a : ℤ) : ZMod n) =
      y i - ((2 * (g.side : ℤ) * (e i : ℤ) : ℤ) : ZMod n) - ((g.offset i + 1 : ℤ) : ZMod n) := by
    rw [Int.cast_natCast, ha, ZMod.natCast_zmod_val]
  have hac' : ((a' : ℤ) : ZMod n) =
      y i - ((2 * (g.side : ℤ) * (e' i : ℤ) : ℤ) : ZMod n) - ((g.offset i + 1 : ℤ) : ZMod n) := by
    rw [Int.cast_natCast, ha', ZMod.natCast_zmod_val]
  have hz : (((a : ℤ) - a' - 2 * (g.side : ℤ) * ((e' i : ℤ) - e i) : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_sub, Int.cast_sub, hac, hac']
    push_cast
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
  have hnz : (n : ℤ) = 2 * (g.side : ℤ) * (E : ℤ) := by rw [hE]; push_cast; ring
  rw [hnz] at hk
  have hlo : c i * g.side ≤ a := by rw [← h1]; exact Nat.div_mul_le_self _ _
  have hhi : a < (c i + 1) * g.side := by
    have : a / g.side < c i + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hs).1 this
  have hlo' : c i * g.side ≤ a' := by rw [← h2]; exact Nat.div_mul_le_self _ _
  have hhi' : a' < (c i + 1) * g.side := by
    have : a' / g.side < c i + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hs).1 this
  have hexp : (c i + 1) * g.side = c i * g.side + g.side := by ring
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (e' i : ℤ) - e i := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by
    intro h0
    apply hi
    omega
  rw [← hd] at hk
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = d + (E : ℤ) * k := ⟨_, rfl⟩
  have hat : (a : ℤ) - a' = 2 * (g.side : ℤ) * t := by rw [ht]; linear_combination hk
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have : t ≤ -1 := by omega
      nlinarith
    · exact h
    · exfalso
      have : 1 ≤ t := by omega
      nlinarith
  have hEk : d = -((E : ℤ) * k) := by omega
  rcases lt_trichotomy k 0 with h | h | h
  · have : k ≤ -1 := by omega
    have hE0 : (0 : ℤ) ≤ E := by omega
    nlinarith
  · rw [h] at hEk
    apply hd0
    simpa using hEk
  · have : 1 ≤ k := by omega
    have hE0 : (0 : ℤ) ≤ E := by omega
    nlinarith
end Cells
section Main
variable (ℓ : StepParameters)
private theorem isFiniteMeasure_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : IsFiniteMeasure (wilsonLaw β m) := by
  constructor
  unfold wilsonLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  by_cases hI : Integrable (fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W)) (fieldHaar m)
  · have hZ : 0 ≤ ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar m) :=
      integral_nonneg fun W => (Real.exp_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal (hI.div_const _)
      (Filter.Eventually.of_forall fun W => div_nonneg (Real.exp_nonneg _) hZ)]
    exact ENNReal.ofReal_lt_top
  · have hZ : ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar m) = 0 := integral_undef hI
    simp only [hZ, div_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact ENNReal.zero_lt_top
private theorem measurable_translate {m : ℕ} (a : TorusSite m) : Measurable (TorusFields.translate a : TorusField m → TorusField m) :=
  measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply i).comp (measurable_pi_apply (x + a))
private theorem measurable_pairTranslate (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ) :
    Measurable (pairTranslate ℓ u n h) :=
  ((measurable_translate _).comp measurable_fst).prodMk
    ((measurePreserving_noiseTranslate ℓ u n h).measurable.comp measurable_snd)
abbrev _root_.YangMills.SharedProofs.p68462 := @measurable_pairTranslate
private theorem measurable_noiseExpectation {u n : ℕ} [NeZero n]
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ}
    (hΦ : Measurable Φ) : Measurable (noiseExpectation ℓ u n Φ) := by
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ u n
  exact (hΦ.stronglyMeasurable.integral_prod_right' (ν := chainNoiseLaw ℓ u n)).measurable
private theorem abs_noiseExpectation_le {u n : ℕ} [NeZero n]
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} {C : ℝ}
    (hC : ∀ p, |Φ p| ≤ C) (W : TorusField (fineSide ℓ.side u n)) : |noiseExpectation ℓ u n Φ W| ≤ C := by
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ u n
  have := norm_integral_le_of_norm_le_const (μ := chainNoiseLaw ℓ u n) (f := fun U => Φ (W, U)) (C := C)
    (Filter.Eventually.of_forall fun U => hC (W, U))
  simpa [noiseExpectation] using this
private theorem integral_pow_sixteen_le {u n : ℕ} [NeZero n] (f : ChainNoise ℓ u n → ℝ) (hf : Measurable f)
    (h0 : ∀ U, 0 ≤ f U) {C : ℝ} (hC : ∀ U, |f U| ≤ C) :
    (∫ U, f U ∂(chainNoiseLaw ℓ u n)) ^ 16 ≤ ∫ U, f U ^ 16 ∂(chainNoiseLaw ℓ u n) := by
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ u n
  have hi : Integrable f (chainNoiseLaw ℓ u n) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hi2 : Integrable (fun U => f U ^ 16) (chainNoiseLaw ℓ u n) :=
    Integrable.of_bound (hf.pow_const 16).aestronglyMeasurable (C ^ 16) (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC U) 16)
  exact (convexOn_pow 16).map_integral_le (g := fun x : ℝ => x ^ 16) (continuous_pow 16).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall h0) hi hi2
private theorem prod_translates_le_noiseExpectation {u n : ℕ} [NeZero n] (g : MirrorGrid) (hs : 0 < g.side)
    (hn : 2 * g.side ∣ n) {c₀ : Fin 4 → ℕ}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} (hΦ : IsCellObservable ℓ g u n c₀ Φ)
    (W : TorusField (fineSide ℓ.side u n)) :
    ∏ e ∈ g.evenTranslations n, noiseExpectation ℓ u n Φ
        (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ u * (2 * (g.side : ℤ) * (e i : ℤ))) W) ^ 16 ≤
      noiseExpectation ℓ u n (fun p => ∏ e ∈ g.evenTranslations n,
        Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p) ^ 16) W := by
  obtain ⟨C, hC⟩ := hΦ.bounded
  let w : (Fin 4 → ℕ) → Fin 4 → ℤ := fun e i => 2 * (g.side : ℤ) * (e i : ℤ)
  let f : (Fin 4 → ℕ) → ChainNoise ℓ u n → ℝ := fun e U => Φ (pairTranslate ℓ u n (w e) (W, U)) ^ 16
  have hfm : ∀ e, Measurable (f e) := fun e =>
    (hΦ.measurable.comp ((measurable_pairTranslate ℓ u n (w e)).comp measurable_prodMk_left)).pow_const 16
  have hprod : noiseExpectation ℓ u n (fun p => ∏ e ∈ g.evenTranslations n, Φ (pairTranslate ℓ u n (w e) p) ^ 16) W =
      ∏ e ∈ g.evenTranslations n, ∫ U, f e U ∂(chainNoiseLaw ℓ u n) :=
    integral_prod_of_disjoint_cells ℓ (g.evenTranslations n) (fun e => shiftPreimage (w e) (g.cellSites n c₀))
      (fun e he e' he' hne => shiftPreimage_disjoint g hs hn c₀ he he' hne) f (fun e _ => hfm e)
      (fun e _ U => pow_nonneg (hΦ.nonneg _) 16)
      (fun e _ ξ ξ' h => by
        have h1 := noiseAgreeAbove_noiseTranslate ℓ u n (g.cellSites n c₀) (w e) ξ ξ' h
        have h2 := hΦ.depends (pairTranslate ℓ u n (w e) (W, ξ)).1 (pairTranslate ℓ u n (w e) (W, ξ)).1 _ _
          (fun _ _ _ => rfl) h1
        show Φ (pairTranslate ℓ u n (w e) (W, ξ)) ^ 16 = Φ (pairTranslate ℓ u n (w e) (W, ξ')) ^ 16
        exact congrArg (· ^ 16) h2)
  refine le_of_le_of_eq ?_ hprod.symm
  refine Finset.prod_le_prod (fun e _ => pow_nonneg ?_ 16) fun e _ => ?_
  · exact integral_nonneg fun U => hΦ.nonneg _
  set V := TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ u * w e i) W with hV
  have hm : Measurable fun U => Φ (V, U) := hΦ.measurable.comp measurable_prodMk_left
  have a1 := integral_pow_sixteen_le ℓ (fun U => Φ (V, U)) hm (fun U => hΦ.nonneg _) (fun U => hC _)
  have a2 : ∫ U, Φ (V, U) ^ 16 ∂(chainNoiseLaw ℓ u n) = ∫ U, f e U ∂(chainNoiseLaw ℓ u n) := by
    have mp := measurePreserving_noiseTranslate ℓ u n (w e)
    conv_lhs => rw [← mp.map_eq]
    rw [integral_map mp.measurable.aemeasurable (hm.pow_const 16).aestronglyMeasurable]
    rfl
  exact a1.trans a2.le
private theorem noiseExpectation_isCellFunction {u n : ℕ} [NeZero n] (hodd : Odd ℓ.side) (g : MirrorGrid)
    (hs : 0 < g.side) {c₀ : Fin 4 → ℕ}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} (hΦ : IsCellObservable ℓ g u n c₀ Φ) :
    IsCellFunction ((g.atDepth ℓ.side u).recentre c₀) (fineSide ℓ.side u n) 0 (noiseExpectation ℓ u n Φ) := by
  obtain ⟨C, hC⟩ := hΦ.bounded
  have hside : 0 < (g.atDepth ℓ.side u).side :=
    Nat.mul_pos hs (pow_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)) u)
  refine ⟨measurable_noiseExpectation ℓ hΦ.measurable, ⟨C, abs_noiseExpectation_le ℓ hC⟩,
    fun W => integral_nonneg fun U => hΦ.nonneg _, ?_⟩
  intro W W' h
  have hsub := (sitesUnder_cellSites_subset hodd u n g c₀).trans
    (cellSites_subset_recentre (N := fineSide ℓ.side u n) (g.atDepth ℓ.side u) hside c₀)
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  exact hΦ.depends W W' U U (fun b h₁ h₂ => h b (hsub h₁) (hsub h₂)) (noiseAgreeAbove_refl ℓ u n _ U)
private theorem translatedCopies_of_evenBound (β : ℝ) {u n : ℕ} [NeZero n] (g : MirrorGrid) (hs : 0 < g.side)
    (hn : 2 * g.side ∣ n) {c₀ : Fin 4 → ℕ}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} (hΦ : IsCellObservable ℓ g u n c₀ Φ)
    (key : ((g.atDepth ℓ.side u).recentre c₀).chessboardNorm β (fineSide ℓ.side u n) (noiseExpectation ℓ u n Φ) ^
        (((g.atDepth ℓ.side u).recentre c₀).cellIndices (fineSide ℓ.side u n)).card ≤
      ∫ W, ∏ e ∈ ((g.atDepth ℓ.side u).recentre c₀).evenTranslations (fineSide ℓ.side u n),
        noiseExpectation ℓ u n Φ
        (TorusFields.translate (siteOfInt fun i => 2 * (((g.atDepth ℓ.side u).recentre c₀).side : ℤ) * (e i : ℤ)) W) ^ 16
        ∂(wilsonLaw β (fineSide ℓ.side u n))) :
    (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c₀ (noiseExpectation ℓ u n Φ) ^
        numCells n g.side ≤
      pairExpectation ℓ β u n fun p => ∏ e ∈ g.evenTranslations n,
        Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p) ^ 16 := by
  have hLp : 0 < ℓ.side ^ u := pow_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)) u
  have hGs : ((g.atDepth ℓ.side u).recentre c₀).side = g.side * ℓ.side ^ u := rfl
  have hdiv : fineSide ℓ.side u n / (g.side * ℓ.side ^ u) = n / g.side := by
    rw [fineSide_eq]
    exact Nat.mul_div_mul_right _ _ hLp
  have hdiv2 : fineSide ℓ.side u n / (2 * (g.side * ℓ.side ^ u)) = n / (2 * g.side) := by
    rw [fineSide_eq, ← Nat.mul_assoc]
    exact Nat.mul_div_mul_right _ _ hLp
  have hcard : (((g.atDepth ℓ.side u).recentre c₀).cellIndices (fineSide ℓ.side u n)).card = numCells n g.side := by
    simp only [MirrorGrid.cellIndices, hGs, hdiv, numCells, Fintype.card_piFinset, Finset.card_range,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hev : ((g.atDepth ℓ.side u).recentre c₀).evenTranslations (fineSide ℓ.side u n) = g.evenTranslations n := by
    simp only [MirrorGrid.evenTranslations, hGs, hdiv2]
  rw [hcard, hev] at key
  refine key.trans ?_
  haveI := isFiniteMeasure_wilsonLaw β (fineSide ℓ.side u n)
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ u n
  obtain ⟨C, hC⟩ := hΦ.bounded
  let Ψ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ := fun p => ∏ e ∈ g.evenTranslations n,
    Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p) ^ 16
  have hΨm : Measurable Ψ := Finset.measurable_prod _ fun e _ =>
    (hΦ.measurable.comp (measurable_pairTranslate ℓ u n _)).pow_const 16
  have hΨb : ∀ p, |Ψ p| ≤ ∏ _e ∈ g.evenTranslations n, C ^ 16 := fun p => by
    simp only [Ψ]
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 16
  have hint : Integrable (noiseExpectation ℓ u n Ψ) (wilsonLaw β (fineSide ℓ.side u n)) :=
    Integrable.of_bound (measurable_noiseExpectation ℓ hΨm).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun W => abs_noiseExpectation_le ℓ hΨb W)
  have hw : ∀ e : Fin 4 → ℕ, (fun i => 2 * (((g.atDepth ℓ.side u).recentre c₀).side : ℤ) * (e i : ℤ)) =
      fun i => (ℓ.side : ℤ) ^ u * (2 * (g.side : ℤ) * (e i : ℤ)) := by
    intro e
    funext i
    rw [hGs]
    push_cast
    ring
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun W => Finset.prod_nonneg fun e _ =>
    pow_nonneg (integral_nonneg fun U => hΦ.nonneg _) 16) hint (Filter.Eventually.of_forall fun W => ?_)
  have := prod_translates_le_noiseExpectation ℓ g hs hn hΦ W
  simp only [hw]
  exact this
private theorem translatedCopies_at (hE : evenTranslatesBoundStatement) (β : ℝ) (u n M : ℕ) [NeZero n]
    (g : MirrorGrid) (hodd : Odd ℓ.side) (hL : 2 ^ 16 ≤ ℓ.side) (hβ : 0 < β) (hn : n = 2 * ℓ.side ^ M)
    (hg : IsGridOfTorus g ℓ.side M) (h2 : 2 * g.side ≤ n) (c₀ : Fin 4 → ℕ)
    (Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ)
    (hΦ : IsCellObservable ℓ g u n c₀ Φ) :
    (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c₀ (noiseExpectation ℓ u n Φ) ^
        numCells n g.side ≤
      pairExpectation ℓ β u n fun p => ∏ e ∈ g.evenTranslations n,
        Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p) ^ 16 := by
  obtain ⟨p, hp1, hpM, hside⟩ := hg
  have hLp : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hs : 0 < g.side := by rw [hside]; exact pow_pos hLp p
  have hdvd : 2 * g.side ∣ n := by
    rw [hn, hside]
    exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow _ hpM)
  have hN : fineSide ℓ.side u n = 2 * ℓ.side ^ (M + u) := by
    rw [fineSide_eq, hn, pow_add]
    ring
  have hGs : ((g.atDepth ℓ.side u).recentre c₀).side = g.side * ℓ.side ^ u := rfl
  have hGg : IsGridOfTorus ((g.atDepth ℓ.side u).recentre c₀) ℓ.side (M + u) :=
    ⟨p + u, by omega, by omega, by rw [hGs, hside, pow_add]⟩
  have hG2 : 2 * ((g.atDepth ℓ.side u).recentre c₀).side ≤ fineSide ℓ.side u n := by
    rw [hGs, fineSide_eq, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ h2
  exact translatedCopies_of_evenBound ℓ β g hs hdvd hΦ
    (hE ℓ.side (M + u) (fineSide ℓ.side u n) β _ hodd hL hβ hN hGg hG2 _
      (noiseExpectation_isCellFunction ℓ hodd g hs hΦ))
end Main
theorem translatedCopiesBound_of_evenTranslatesBound (hE : evenTranslatesBoundStatement) :
    translatedCopiesBoundStatement := by
  intro ℓ β u n M _ g hodd hL hβ hn hg h2 c₀ Φ _ hΦ
  exact translatedCopies_at ℓ hE β u n M g hodd hL hβ hn hg h2 c₀ Φ hΦ
end YangMills.Construction.ChainNoise
end
