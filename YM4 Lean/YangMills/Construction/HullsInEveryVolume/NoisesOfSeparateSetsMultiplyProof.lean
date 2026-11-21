import YangMills.Construction.HullsInEveryVolume.MeansUnderATilt
import YangMills.Construction.HullsInEveryVolume.NoisesOfSeparateSetsMultiply
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChainNoise
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
private def IndependentUnder {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (R₁ R₂ : Ω → Ω → Prop) : Prop :=
  ∀ f g : Ω → ℝ, Measurable f → Measurable g → (∃ C : ℝ, ∀ ω, |f ω| ≤ C) → (∃ C : ℝ, ∀ ω, |g ω| ≤ C) →
    (∀ ω ω', R₁ ω ω' → f ω = f ω') → (∀ ω ω', R₂ ω ω' → g ω = g ω') →
    ∫ ω, f ω * g ω ∂μ = (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ
private theorem integrable_of_abs_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ ω, |f ω| ≤ C) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hC ω)
private theorem IndependentUnder.prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R₁ R₂ : X → X → Prop} {S₁ S₂ : Y → Y → Prop}
    (hμ : IndependentUnder μ R₁ R₂) (hν : IndependentUnder ν S₁ S₂) (hR₁ : ∀ x, R₁ x x) (hR₂ : ∀ x, R₂ x x)
    (hS₁ : ∀ y, S₁ y y) (hS₂ : ∀ y, S₂ y y) :
    IndependentUnder (μ.prod ν) (fun p q => R₁ p.1 q.1 ∧ S₁ p.2 q.2) (fun p q => R₂ p.1 q.1 ∧ S₂ p.2 q.2) := by
  intro f g hf hg hfb hgb hfr hgr
  obtain ⟨C₁, hC₁⟩ := hfb
  obtain ⟨C₂, hC₂⟩ := hgb
  have intf : Integrable f (μ.prod ν) := integrable_of_abs_le hf ⟨C₁, hC₁⟩
  have intg : Integrable g (μ.prod ν) := integrable_of_abs_le hg ⟨C₂, hC₂⟩
  have intfg : Integrable (fun p => f p * g p) (μ.prod ν) :=
    integrable_of_abs_le (hf.mul hg) ⟨C₁ * C₂, fun p => by
      rw [abs_mul]
      exact mul_le_mul (hC₁ p) (hC₂ p) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ p))⟩
  have measf : ∀ y, Measurable fun x => f (x, y) := fun y => hf.comp measurable_prodMk_right
  have measg : ∀ y, Measurable fun x => g (x, y) := fun y => hg.comp measurable_prodMk_right
  let F : Y → ℝ := fun y => ∫ x, f (x, y) ∂μ
  let G : Y → ℝ := fun y => ∫ x, g (x, y) ∂μ
  have measF : Measurable F := (hf.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have measG : Measurable G := (hg.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have boundF : ∀ y, |F y| ≤ |C₁| := fun y => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f (x, y)) (C := C₁) (ae_of_all _ fun x => by simpa using hC₁ _)
    simpa using h.trans (by simp [le_abs_self])
  have boundG : ∀ y, |G y| ≤ |C₂| := fun y => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => g (x, y)) (C := C₂) (ae_of_all _ fun x => by simpa using hC₂ _)
    simpa using h.trans (by simp [le_abs_self])
  have fiber : ∀ y, ∫ x, f (x, y) * g (x, y) ∂μ = F y * G y := fun y =>
    hμ _ _ (measf y) (measg y) ⟨C₁, fun x => hC₁ _⟩ ⟨C₂, fun x => hC₂ _⟩
      (fun x x' h => hfr _ _ ⟨h, hS₁ y⟩) (fun x x' h => hgr _ _ ⟨h, hS₂ y⟩)
  rw [integral_prod_symm _ intfg, integral_prod_symm _ intf, integral_prod_symm _ intg]
  simp only [fiber]
  exact hν F G measF measG ⟨_, boundF⟩ ⟨_, boundG⟩
    (fun y y' h => integral_congr_ae (ae_of_all _ fun x => hfr _ _ ⟨hR₁ x, h⟩))
    (fun y y' h => integral_congr_ae (ae_of_all _ fun x => hgr _ _ ⟨hR₂ x, h⟩))
private theorem map_piecewise_prod_eq_pi {ι : Type} [Fintype ι] [DecidableEq ι] (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (A : Set ι) [DecidablePred (· ∈ A)] :
    ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)).map
      (fun p : (ι → unitInterval) × (ι → unitInterval) => fun i => if i ∈ A then p.1 i else p.2 i) =
      Measure.pi fun _ : ι => μ := by
  have hm : Measurable fun p : (ι → unitInterval) × (ι → unitInterval) => fun i => if i ∈ A then p.1 i else p.2 i := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ A
    · simp only [if_pos h]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [if_neg h]
      exact (measurable_pi_apply i).comp measurable_snd
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have e : (fun p : (ι → unitInterval) × (ι → unitInterval) => fun i => if i ∈ A then p.1 i else p.2 i) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ fun i => if i ∈ A then s i else Set.univ) ×ˢ (Set.pi Set.univ fun i => if i ∈ A then Set.univ else s i) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ A
        · simpa [hi] using h i
        · simp [hi]
      · by_cases hi : i ∈ A
        · simp [hi]
        · simpa [hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ A
      · simpa [hi] using h1 i
      · simpa [hi] using h2 i
  rw [e, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ A
  · simp [hi]
  · simp [hi]
private theorem independentUnder_pi {ι : Type} [Fintype ι] (μ : Measure unitInterval) [IsProbabilityMeasure μ] (A B : Set ι)
    (hAB : Disjoint A B) :
    IndependentUnder (Measure.pi fun _ : ι => μ) (fun x x' => ∀ i ∈ A, x i = x' i) (fun x x' => ∀ i ∈ B, x i = x' i) := by
  classical
  intro f g hf hg hfb hgb hfr hgr
  have hmap := map_piecewise_prod_eq_pi μ A
  have hm : Measurable fun p : (ι → unitInterval) × (ι → unitInterval) => fun i => if i ∈ A then p.1 i else p.2 i := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ A
    · simp only [if_pos h]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [if_neg h]
      exact (measurable_pi_apply i).comp measurable_snd
  have h1 : ∫ ω, f ω * g ω ∂(Measure.pi fun _ : ι => μ) =
      ∫ p, f (fun i => if i ∈ A then p.1 i else p.2 i) * g (fun i => if i ∈ A then p.1 i else p.2 i)
        ∂((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)) := by
    conv_lhs => rw [← hmap]
    exact integral_map hm.aemeasurable (hf.mul hg).aestronglyMeasurable
  rw [h1]
  have h2 : ∀ p : (ι → unitInterval) × (ι → unitInterval),
      f (fun i => if i ∈ A then p.1 i else p.2 i) * g (fun i => if i ∈ A then p.1 i else p.2 i) = f p.1 * g p.2 := by
    intro p
    rw [hfr _ p.1 (fun i hi => by simp [hi]), hgr _ p.2 (fun i hi => by
      have : i ∉ A := fun h => Set.disjoint_left.1 hAB h hi
      simp [this])]
  simp only [h2]
  exact integral_prod_mul f g
variable {ℓ : StepParameters}
private theorem noiseAgreeAbove_refl (ℓ : StepParameters) :
    ∀ (u n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (U : ChainNoise ℓ u n), NoiseAgreeAbove ℓ u n Q U U
  | 0, _, _, _, _ => trivial
  | u + 1, n, _, Q, U => ⟨noiseAgreeAbove_refl ℓ u (n * ℓ.side) _ U.1, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem sitesInBlocks_mono {n L : ℕ} [NeZero n] [NeZero L] {Q Q' : Finset (TorusSite n)} (h : Q ⊆ Q') :
    sitesInBlocks L Q ⊆ sitesInBlocks L Q' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem noiseAgreeAbove_mono (ℓ : StepParameters) :
    ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)} {U U' : ChainNoise ℓ u n}, Q ⊆ Q' →
      NoiseAgreeAbove ℓ u n Q' U U' → NoiseAgreeAbove ℓ u n Q U U'
  | 0, _, _, _, _, _, _, _, _ => trivial
  | u + 1, n, _, Q, Q', U, U', h, ⟨h1, h2, h3, h4⟩ =>
    ⟨noiseAgreeAbove_mono ℓ u (n * ℓ.side) (sitesInBlocks_mono h) h1, fun y hy => h2 y (h hy), fun c hc => h3 c (h hc),
      fun b hb => h4 b (h hb)⟩
private theorem independentUnder_stepNoiseLaw (ℓ : StepParameters) (n : ℕ) [NeZero n] (Q₁ Q₂ : Finset (TorusSite n))
    (hQ : Disjoint Q₁ Q₂) :
    IndependentUnder (stepNoiseLaw ℓ n)
      (fun p q => (∀ y ∈ Q₁, p.1 y = q.1 y) ∧ (∀ c : TorusBond n, c.1 ∈ Q₁ → p.2.1 c = q.2.1 c) ∧
        ∀ b : TorusBond (n * ℓ.side), parentBlock ℓ.side b.1 ∈ Q₁ → p.2.2 b = q.2.2 b)
      (fun p q => (∀ y ∈ Q₂, p.1 y = q.1 y) ∧ (∀ c : TorusBond n, c.1 ∈ Q₂ → p.2.1 c = q.2.1 c) ∧
        ∀ b : TorusBond (n * ℓ.side), parentBlock ℓ.side b.1 ∈ Q₂ → p.2.2 b = q.2.2 b) := by
  have hsites : Disjoint (↑Q₁ : Set (TorusSite n)) ↑Q₂ := by exact_mod_cast hQ
  have hpre : ∀ {Z : Type} (f : Z → TorusSite n), Disjoint {c : Z | f c ∈ Q₁} {c : Z | f c ∈ Q₂} := fun f =>
    Set.disjoint_left.2 fun c h1 h2 => Finset.disjoint_left.1 hQ h1 h2
  have i1 := independentUnder_pi (ι := TorusSite n) volume (↑Q₁) (↑Q₂) hsites
  have i2 := independentUnder_pi (ι := TorusBond n) volume {c | c.1 ∈ Q₁} {c | c.1 ∈ Q₂} (hpre _)
  have i3 := independentUnder_pi (ι := TorusBond (n * ℓ.side)) volume {b | parentBlock ℓ.side b.1 ∈ Q₁}
    {b | parentBlock ℓ.side b.1 ∈ Q₂} (hpre _)
  have i23 := IndependentUnder.prod i2 i3 (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact IndependentUnder.prod i1 i23 (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
private theorem independentUnder_chainNoiseLaw (ℓ : StepParameters) :
    ∀ (u n : ℕ) [NeZero n] (Q₁ Q₂ : Finset (TorusSite n)), Disjoint Q₁ Q₂ →
      IndependentUnder (chainNoiseLaw ℓ u n) (NoiseAgreeAbove ℓ u n Q₁) (NoiseAgreeAbove ℓ u n Q₂)
  | 0, n, _, Q₁, Q₂, _ => by
    intro f g hf hg _ _ _ _
    have h : ∀ F : ChainNoise ℓ 0 n → ℝ, Measurable F → ∫ ω, F ω ∂(chainNoiseLaw ℓ 0 n) = F () := fun F hF => by
      unfold chainNoiseLaw
      exact integral_dirac' F () hF.stronglyMeasurable
    rw [h (fun ω => f ω * g ω) (hf.mul hg), h _ hf, h _ hg]
  | u + 1, n, _, Q₁, Q₂, hQ => by
    have hb : Disjoint (sitesInBlocks ℓ.side Q₁) (sitesInBlocks ℓ.side Q₂) := by
      refine Finset.disjoint_left.2 fun x h1 h2 => ?_
      simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact Finset.disjoint_left.1 hQ h1 h2
    have h1 := independentUnder_chainNoiseLaw ℓ u (n * ℓ.side) _ _ hb
    have h2 := independentUnder_stepNoiseLaw ℓ n Q₁ Q₂ hQ
    exact IndependentUnder.prod h1 h2 (noiseAgreeAbove_refl ℓ _ _ _) (noiseAgreeAbove_refl ℓ _ _ _)
      (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩) (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩)
theorem disjointNoisesMultiply : disjointNoisesMultiplyStatement := by
  classical
  intro ℓ u n _ ι I Q Φ hdis hΦ W
  have hread : ∀ i ∈ I, ∀ U U' : ChainNoise ℓ u n, NoiseAgreeAbove ℓ u n (Q i) U U' → Φ i (W, U) = Φ i (W, U') :=
    fun i hi U U' h => (hΦ i hi).2.2 W W U U' (fun _ _ _ => rfl) h
  have hmeas : ∀ i ∈ I, Measurable fun U : ChainNoise ℓ u n => Φ i (W, U) := fun i hi =>
    (hΦ i hi).1.comp measurable_prodMk_left
  have hbd : ∀ i ∈ I, ∃ C : ℝ, ∀ U : ChainNoise ℓ u n, |Φ i (W, U)| ≤ C := fun i hi => by
    obtain ⟨C, hC⟩ := (hΦ i hi).2.1
    exact ⟨C, fun U => hC _⟩
  have key : ∀ J : Finset ι, J ⊆ I → (Measurable fun U : ChainNoise ℓ u n => ∏ i ∈ J, Φ i (W, U)) ∧
      (∃ C : ℝ, ∀ U : ChainNoise ℓ u n, |∏ i ∈ J, Φ i (W, U)| ≤ C) ∧
      (∀ U U' : ChainNoise ℓ u n, NoiseAgreeAbove ℓ u n (J.biUnion Q) U U' → ∏ i ∈ J, Φ i (W, U) = ∏ i ∈ J, Φ i (W, U')) ∧
      ∫ U, ∏ i ∈ J, Φ i (W, U) ∂(chainNoiseLaw ℓ u n) = ∏ i ∈ J, ∫ U, Φ i (W, U) ∂(chainNoiseLaw ℓ u n) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simpa using measurable_const, ⟨1, by simp⟩, by simp, by simp⟩
    | insert a J ha ih =>
      intro hJ
      have hJ' : J ⊆ I := (Finset.subset_insert _ _).trans hJ
      have haI : a ∈ I := hJ (Finset.mem_insert_self _ _)
      obtain ⟨m1, ⟨C₁, b1⟩, r1, e1⟩ := ih hJ'
      obtain ⟨C₂, b2⟩ := hbd a haI
      have hd : Disjoint (Q a) (J.biUnion Q) := by
        refine Finset.disjoint_left.2 fun x h1 h2 => ?_
        obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.1 h2
        have hne : a ≠ i := fun e => ha (e ▸ hi)
        exact Finset.disjoint_left.1 (hdis a haI i (hJ' hi) hne) h1 hx
      simp only [Finset.prod_insert ha]
      refine ⟨(hmeas a haI).mul m1, ⟨C₂ * C₁, fun U => ?_⟩, fun U U' h => ?_, ?_⟩
      · rw [abs_mul]
        exact mul_le_mul (b2 U) (b1 U) (abs_nonneg _) ((abs_nonneg _).trans (b2 U))
      · rw [hread a haI U U' (noiseAgreeAbove_mono ℓ u n (fun x hx => by
            simp only [Finset.biUnion_insert]
            exact Finset.mem_union_left _ hx) h),
          r1 U U' (noiseAgreeAbove_mono ℓ u n (fun x hx => by
            simp only [Finset.biUnion_insert]
            exact Finset.mem_union_right _ hx) h)]
      · rw [independentUnder_chainNoiseLaw ℓ u n _ _ hd _ _ (hmeas a haI) m1 ⟨C₂, b2⟩ ⟨C₁, b1⟩ (hread a haI) r1, e1]
  exact (key I subset_rfl).2.2.2
end YangMills.Construction.ChainNoise
end
