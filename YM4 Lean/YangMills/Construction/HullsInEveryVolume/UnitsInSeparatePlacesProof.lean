import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.HullsInEveryVolume.ChessboardOnABareGrid
import YangMills.Construction.HullsInEveryVolume.NoisesCarryTheChain
import YangMills.Construction.HullsInEveryVolume.NormOfAUnit
import YangMills.Construction.HullsInEveryVolume.PlacesFarApartAreRare
import YangMills.Construction.HullsInEveryVolume.ReachOfAUnit
import YangMills.Construction.HullsInEveryVolume.SixteenOffsetsSeparatePlaces
import YangMills.Construction.HullsInEveryVolume.UnitsInSeparatePlaces
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields TorusLumps RenormalizationStepParameters StepReturn ChainNoise HullTrees ChessboardGrids WeightedResponses
private structure BoundedMeasurable {X : Type*} [MeasurableSpace X] (f : X → ℝ) : Prop where
  measurable : Measurable f
  bounded : ∃ C : ℝ, ∀ x, |f x| ≤ C
private lemma BoundedMeasurable.integrable {X : Type*} [MeasurableSpace X] {f : X → ℝ} (hf : BoundedMeasurable f)
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bounded
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by simpa using hC x)
private lemma BoundedMeasurable.mul {X : Type*} [MeasurableSpace X] {f g : X → ℝ} (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g) : BoundedMeasurable fun x => f x * g x := by
  obtain ⟨C, hC⟩ := hf.bounded
  obtain ⟨D, hD⟩ := hg.bounded
  refine ⟨hf.measurable.mul hg.measurable, C * D, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
private lemma BoundedMeasurable.slice {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {f : X × Y → ℝ}
    (hf : BoundedMeasurable f) (y : Y) : BoundedMeasurable fun x => f (x, y) := by
  obtain ⟨C, hC⟩ := hf.bounded
  exact ⟨hf.measurable.comp (measurable_id.prodMk measurable_const), C, fun x => hC _⟩
private lemma BoundedMeasurable.marginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {f : X × Y → ℝ}
    (hf : BoundedMeasurable f) (μ : Measure X) [IsProbabilityMeasure μ] :
    BoundedMeasurable fun y => ∫ x, f (x, y) ∂μ := by
  obtain ⟨C, hC⟩ := hf.bounded
  refine ⟨(hf.measurable.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable, C, fun y => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f (x, y)) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa using hC (x, y))
  simpa using this
private lemma integral_prod_mul_of_fiberwise {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f g : X × Y → ℝ} (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g)
    (h₁ : ∀ y, ∫ x, f (x, y) * g (x, y) ∂μ = (∫ x, f (x, y) ∂μ) * ∫ x, g (x, y) ∂μ)
    (h₂ : ∫ y, (∫ x, f (x, y) ∂μ) * (∫ x, g (x, y) ∂μ) ∂ν =
      (∫ y, ∫ x, f (x, y) ∂μ ∂ν) * ∫ y, ∫ x, g (x, y) ∂μ ∂ν) :
    ∫ p, f p * g p ∂(μ.prod ν) = (∫ p, f p ∂(μ.prod ν)) * ∫ p, g p ∂(μ.prod ν) := by
  rw [integral_prod_symm _ ((hf.mul hg).integrable _), integral_prod_symm _ (hf.integrable _),
    integral_prod_symm _ (hg.integrable _)]
  simp only [h₁]
  exact h₂
private lemma integral_pi_mul_of_disjoint {ι E : Type*} [Fintype ι] [MeasurableSpace E] [Nonempty E] (ν : Measure E)
    [IsProbabilityMeasure ν] (A : Set ι) {f g : (ι → E) → ℝ}
    (rf : ∀ x x' : ι → E, (∀ i ∈ A, x i = x' i) → f x = f x')
    (rg : ∀ x x' : ι → E, (∀ i, i ∉ A → x i = x' i) → g x = g x') :
    ∫ x, f x * g x ∂(Measure.pi fun _ : ι => ν) =
      (∫ x, f x ∂(Measure.pi fun _ : ι => ν)) * ∫ x, g x ∂(Measure.pi fun _ : ι => ν) := by
  classical
  have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) (· ∈ A)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) (· ∈ A) with he
  have key : ∀ h : (ι → E) → ℝ, ∫ x, h x ∂(Measure.pi fun _ : ι => ν) = ∫ p, h (e.symm p) ∂
      ((Measure.pi fun _ : {i // i ∈ A} => ν).prod (Measure.pi fun _ : {i // ¬ i ∈ A} => ν)) := fun h => by
    rw [← mp.integral_comp' (fun p => h (e.symm p))]
    simp
  have e0 : E := Classical.arbitrary E
  let a₀ : {i // i ∈ A} → E := fun _ => e0
  let b₀ : {i // ¬ i ∈ A} → E := fun _ => e0
  have hf' : ∀ p, f (e.symm p) = f (e.symm (p.1, b₀)) := fun p => rf _ _ fun i hi => by
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
  have hg' : ∀ p, g (e.symm p) = g (e.symm (a₀, p.2)) := fun p => rg _ _ fun i hi => by
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
  rw [key, key f, key g]
  simp only [hf' _, hg' _]
  have one : ∀ (h : ({i // i ∈ A} → E) → ℝ), ∫ p, h p.1 ∂((Measure.pi fun _ : {i // i ∈ A} => ν).prod
      (Measure.pi fun _ : {i // ¬ i ∈ A} => ν)) = ∫ a, h a ∂(Measure.pi fun _ : {i // i ∈ A} => ν) := fun h => by
    have := integral_prod_mul (μ := Measure.pi fun _ : {i // i ∈ A} => ν)
      (ν := Measure.pi fun _ : {i // ¬ i ∈ A} => ν) h (fun _ => (1 : ℝ))
    simpa using this
  have two : ∀ (h : ({i // ¬ i ∈ A} → E) → ℝ), ∫ p, h p.2 ∂((Measure.pi fun _ : {i // i ∈ A} => ν).prod
      (Measure.pi fun _ : {i // ¬ i ∈ A} => ν)) = ∫ a, h a ∂(Measure.pi fun _ : {i // ¬ i ∈ A} => ν) := fun h => by
    have := integral_prod_mul (μ := Measure.pi fun _ : {i // i ∈ A} => ν)
      (ν := Measure.pi fun _ : {i // ¬ i ∈ A} => ν) (fun _ => (1 : ℝ)) h
    simpa using this
  rw [one (fun a => f (e.symm (a, b₀))), two (fun b => g (e.symm (a₀, b)))]
  exact integral_prod_mul (fun a => f (e.symm (a, b₀))) (fun b => g (e.symm (a₀, b)))
variable {ℓ : StepParameters}
private lemma isProbabilityMeasure_chainNoiseLaw :
    ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  | s + 1, n, _ => by
    have := isProbabilityMeasure_chainNoiseLaw s (n * ℓ.side)
    have : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by unfold stepNoiseLaw; infer_instance
    show IsProbabilityMeasure ((chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n))
    infer_instance
private lemma integral_dirac_mul (f g : Unit → ℝ) :
    ∫ U, f U * g U ∂(Measure.dirac ()) = (∫ U, f U ∂(Measure.dirac ())) * ∫ U, g U ∂(Measure.dirac ()) := by
  simp
private instance (s n : ℕ) [NeZero n] : IsProbabilityMeasure (chainNoiseLaw ℓ s n) :=
  isProbabilityMeasure_chainNoiseLaw s n
private def StepDependsOn (ℓ : StepParameters) (n : ℕ) [NeZero n] (Q : Finset (TorusSite n))
    (F : StepNoise ℓ n → ℝ) : Prop :=
  ∀ U U' : StepNoise ℓ n, (∀ y ∈ Q, U.1 y = U'.1 y) → (∀ c : TorusBond n, c.1 ∈ Q → U.2.1 c = U'.2.1 c) →
    (∀ b : TorusBond (n * ℓ.side), parentBlock ℓ.side b.1 ∈ Q → U.2.2 b = U'.2.2 b) → F U = F U'
private lemma integral_stepNoiseLaw_mul (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)} (hd : Disjoint Q Q')
    {F G : StepNoise ℓ n → ℝ} (hF : BoundedMeasurable F) (hG : BoundedMeasurable G) (rF : StepDependsOn ℓ n Q F)
    (rG : StepDependsOn ℓ n Q' G) :
    ∫ U, F U * G U ∂(stepNoiseLaw ℓ n) = (∫ U, F U ∂(stepNoiseLaw ℓ n)) * ∫ U, G U ∂(stepNoiseLaw ℓ n) := by
  have off : ∀ {y : TorusSite n}, y ∈ Q' → y ∉ Q := fun h h' => Finset.disjoint_left.mp hd h' h
  unfold stepNoiseLaw
  refine integral_prod_mul_of_fiberwise hF hG (fun y => ?_) ?_
  · refine integral_pi_mul_of_disjoint _ {y | y ∈ Q} (fun x x' h => ?_) (fun x x' h => ?_)
    · exact rF _ _ h (fun _ _ => rfl) (fun _ _ => rfl)
    · exact rG _ _ (fun i hi => h i (off hi)) (fun _ _ => rfl) (fun _ _ => rfl)
  · refine integral_prod_mul_of_fiberwise (hF.marginal _) (hG.marginal _) (fun y => ?_) ?_
    · refine integral_pi_mul_of_disjoint _ {c : TorusBond n | c.1 ∈ Q} (fun x x' h => ?_) (fun x x' h => ?_)
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v => rF _ _ (fun _ _ => rfl) h (fun _ _ => rfl))
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
          rG _ _ (fun _ _ => rfl) (fun c hc => h c (off hc)) (fun _ _ => rfl))
    · refine integral_pi_mul_of_disjoint _ {b : TorusBond (n * ℓ.side) | parentBlock ℓ.side b.1 ∈ Q}
        (fun x x' h => ?_) (fun x x' h => ?_)
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
          integral_congr_ae (Filter.Eventually.of_forall fun w => rF _ _ (fun _ _ => rfl) (fun _ _ => rfl) h))
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
          integral_congr_ae (Filter.Eventually.of_forall fun w =>
            rG _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun b hb => h b (off hb))))
private lemma noiseAgreeAbove_refl : ∀ (u n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (U : ChainNoise.ChainNoise ℓ u n),
    NoiseAgreeAbove ℓ u n Q U U
  | 0, _, _, _, _ => trivial
  | u + 1, n, _, _, U => ⟨noiseAgreeAbove_refl u (n * ℓ.side) _ U.1, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private lemma sitesInBlocks_mono {n : ℕ} [NeZero n] (L : ℕ) [NeZero L] {Q Q' : Finset (TorusSite n)} (h : Q ⊆ Q') :
    sitesInBlocks L Q ⊆ sitesInBlocks L Q' := fun x hx => by
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private lemma sitesInBlocks_disjoint {n : ℕ} [NeZero n] (L : ℕ) [NeZero L] {Q Q' : Finset (TorusSite n)}
    (h : Disjoint Q Q') : Disjoint (sitesInBlocks L Q) (sitesInBlocks L Q') := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact h hx hx'
private lemma noiseAgreeAbove_mono : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)} (_ : Q ⊆ Q')
    {U U' : ChainNoise.ChainNoise ℓ u n}, NoiseAgreeAbove ℓ u n Q' U U' → NoiseAgreeAbove ℓ u n Q U U'
  | 0, _, _, _, _, _, _, _, _ => trivial
  | u + 1, n, _, _, _, h, _, _, ⟨a, b, c, d⟩ =>
    ⟨noiseAgreeAbove_mono u (n * ℓ.side) (sitesInBlocks_mono ℓ.side h) a, fun y hy => b y (h hy),
      fun x hx => c x (h hx), fun x hx => d x (h hx)⟩
private def NoiseDependsOn (ℓ : StepParameters) (u n : ℕ) [NeZero n] (Q : Finset (TorusSite n))
    (f : ChainNoise.ChainNoise ℓ u n → ℝ) : Prop :=
  ∀ U U', NoiseAgreeAbove ℓ u n Q U U' → f U = f U'
private lemma integral_chainNoiseLaw_mul : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Disjoint Q Q' →
    ∀ {f g : ChainNoise.ChainNoise ℓ u n → ℝ}, BoundedMeasurable f → BoundedMeasurable g →
      NoiseDependsOn ℓ u n Q f → NoiseDependsOn ℓ u n Q' g →
      ∫ U, f U * g U ∂(chainNoiseLaw ℓ u n) = (∫ U, f U ∂(chainNoiseLaw ℓ u n)) * ∫ U, g U ∂(chainNoiseLaw ℓ u n)
  | 0, _, _, _, _, _, f, g, hf, hg, _, _ => by
    exact integral_dirac_mul f g
  | u + 1, n, _, Q, Q', hd, f, g, hf, hg, rf, rg => by
    have : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by unfold stepNoiseLaw; infer_instance
    have hf' : @BoundedMeasurable (ChainNoise.ChainNoise ℓ u (n * ℓ.side) × StepNoise ℓ n) _ f := hf
    have hg' : @BoundedMeasurable (ChainNoise.ChainNoise ℓ u (n * ℓ.side) × StepNoise ℓ n) _ g := hg
    refine integral_prod_mul_of_fiberwise (μ := chainNoiseLaw ℓ u (n * ℓ.side)) (ν := stepNoiseLaw ℓ n) hf' hg'
      (fun y => ?_) ?_
    · refine integral_chainNoiseLaw_mul u (n * ℓ.side) (sitesInBlocks_disjoint ℓ.side hd) (hf'.slice y)
        (hg'.slice y)
        (fun U U' h => rf _ _ ⟨h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩)
        (fun U U' h => rg _ _ ⟨h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩)
    · refine integral_stepNoiseLaw_mul n hd (hf'.marginal _) (hg'.marginal _) (fun U U' h₁ h₂ h₃ => ?_)
        (fun U U' h₁ h₂ h₃ => ?_)
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
          rf _ _ ⟨noiseAgreeAbove_refl _ _ _ _, h₁, h₂, h₃⟩)
      · exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
          rg _ _ ⟨noiseAgreeAbove_refl _ _ _ _, h₁, h₂, h₃⟩)
private lemma BoundedMeasurable.finsetProd {X ι : Type*} [MeasurableSpace X] (I : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ I, BoundedMeasurable (f i)) : BoundedMeasurable fun x => ∏ i ∈ I, f i x := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨by simp, 1, by simp⟩
  | insert a I ha ih =>
    have h1 := hf a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.prod_insert ha] using h1.mul h2
private lemma integral_chainNoiseLaw_prod (u n : ℕ) [NeZero n] {ι : Type*} (I : Finset ι)
    (Q : ι → Finset (TorusSite n)) (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Q i) (Q j))
    {f : ι → ChainNoise.ChainNoise ℓ u n → ℝ} (hf : ∀ i ∈ I, BoundedMeasurable (f i))
    (rf : ∀ i ∈ I, NoiseDependsOn ℓ u n (Q i) (f i)) :
    ∫ U, ∏ i ∈ I, f i U ∂(chainNoiseLaw ℓ u n) = ∏ i ∈ I, ∫ U, f i U ∂(chainNoiseLaw ℓ u n) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    have hsub : ∀ i ∈ I, i ∈ insert a I := fun i hi => Finset.mem_insert_of_mem hi
    simp only [Finset.prod_insert ha]
    rw [← ih (fun i hi j hj => hd i (hsub i hi) j (hsub j hj)) (fun i hi => hf i (hsub i hi))
      (fun i hi => rf i (hsub i hi))]
    refine integral_chainNoiseLaw_mul u n (Q := Q a) (Q' := I.biUnion Q) ?_ (hf a (Finset.mem_insert_self _ _))
      (BoundedMeasurable.finsetProd I fun i hi => hf i (hsub i hi)) (rf a (Finset.mem_insert_self _ _)) ?_
    · rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hd a (Finset.mem_insert_self _ _) i (hsub i hi) fun h => ha (h ▸ hi)
    · intro U U' h
      exact Finset.prod_congr rfl fun i hi =>
        rf i (hsub i hi) _ _ (noiseAgreeAbove_mono u n (Finset.subset_biUnion_of_mem Q hi) h)
private lemma cellIndex_arith (n L l : ℕ) [NeZero n] [NeZero L] (hL : Odd L) (t o : ℤ) :
    (((((t + ((L : ℤ) - 1) / 2) / (L : ℤ)) - (o + 1) : ℤ) : ZMod n)).val / l =
      (((t - ((L : ℤ) * o + ((L : ℤ) - 1) / 2 + 1) : ℤ) : ZMod (n * L))).val / (l * L) := by
  obtain ⟨h, hh⟩ : ∃ h : ℤ, (L : ℤ) = 2 * h + 1 := by
    obtain ⟨k, hk⟩ := hL
    exact ⟨k, by exact_mod_cast hk⟩
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hhalf : ((L : ℤ) - 1) / 2 = h := by omega
  rw [hhalf]
  set a := (t + h) / (L : ℤ) with ha
  set e := (t + h) % (L : ℤ) with he
  have hdiv : (L : ℤ) * a + e = t + h := Int.mul_ediv_add_emod _ _
  have he0 : 0 ≤ e := Int.emod_nonneg _ hLpos.ne'
  have he1 : e < L := Int.emod_lt_of_pos _ hLpos
  set A := a - (o + 1) with hA
  have hX : t - ((L : ℤ) * o + h + 1) = (L : ℤ) * A + e := by
    rw [hA]
    have : t = (L : ℤ) * a + e - h := by linarith
    rw [this, hh]; ring
  rw [hX]
  set w := A % (n : ℤ) with hw
  have hw0 : 0 ≤ w := Int.emod_nonneg _ hn.ne'
  have hw1 : w < n := Int.emod_lt_of_pos _ hn
  have hAw : (n : ℤ) * (A / (n : ℤ)) + w = A := Int.mul_ediv_add_emod _ _
  have hv1 : ((((A : ℤ) : ZMod n)).val : ℤ) = w := by rw [ZMod.val_intCast]
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hv2 : (((((L : ℤ) * A + e : ℤ) : ZMod (n * L))).val : ℤ) = (L : ℤ) * w + e := by
    rw [ZMod.val_intCast]
    have : (L : ℤ) * A + e = ((L : ℤ) * w + e) + (((n * L : ℕ) : ℤ)) * (A / (n : ℤ)) := by
      push_cast
      linear_combination (-(L : ℤ)) * hAw
    rw [this, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt (by positivity)
    push_cast
    nlinarith
  obtain ⟨v, hv⟩ : ∃ v : ℕ, (v : ℤ) = w := ⟨w.toNat, Int.toNat_of_nonneg hw0⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = e := ⟨e.toNat, Int.toNat_of_nonneg he0⟩
  have e1 : (((A : ℤ) : ZMod n)).val = v := by exact_mod_cast hv1.trans hv.symm
  have e2 : ((((L : ℤ) * A + e : ℤ) : ZMod (n * L))).val = L * v + d := by
    have : ((((((L : ℤ) * A + e : ℤ) : ZMod (n * L))).val : ℕ) : ℤ) = ((L * v + d : ℕ) : ℤ) := by
      rw [hv2]; push_cast; rw [hv, hd]
    exact_mod_cast this
  have hdL : d < L := by
    have : (d : ℤ) < L := hd ▸ he1
    exact_mod_cast this
  rw [e1, e2, mul_comm l L, ← Nat.div_div_eq_div_mul, Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne L)),
    Nat.div_eq_of_lt hdL, add_zero]
private def refinedGrid (g : MirrorGrid) (L : ℕ) : MirrorGrid :=
  ⟨g.side * L, fun i => (L : ℤ) * g.offset i + ((L : ℤ) - 1) / 2⟩
private lemma atDepth_zero (g : MirrorGrid) (L : ℕ) : g.atDepth L 0 = g := by
  cases g
  simp [MirrorGrid.atDepth]
private lemma atDepth_succ (g : MirrorGrid) (L u : ℕ) (hL : Odd L) :
    g.atDepth L (u + 1) = (refinedGrid g L).atDepth L u := by
  obtain ⟨h, hh⟩ : ∃ h : ℤ, (L : ℤ) = 2 * h + 1 := by
    obtain ⟨k, hk⟩ := hL
    exact ⟨k, by exact_mod_cast hk⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (L : ℤ) ^ u = 2 * k + 1 := by
    obtain ⟨k, hk⟩ := hL.pow (n := u)
    exact ⟨k, by exact_mod_cast hk⟩
  simp only [MirrorGrid.atDepth, refinedGrid, MirrorGrid.mk.injEq]
  refine ⟨by ring, ?_⟩
  funext i
  have e1 : (L : ℤ) ^ (u + 1) - 1 = 2 * (2 * h * k + h + k) := by rw [pow_succ, hk, hh]; ring
  have e2 : (L : ℤ) - 1 = 2 * h := by rw [hh]; ring
  have e3 : (L : ℤ) ^ u - 1 = 2 * k := by rw [hk]; ring
  rw [e1, e2, e3, Int.mul_ediv_cancel_left _ two_ne_zero, Int.mul_ediv_cancel_left _ two_ne_zero,
    Int.mul_ediv_cancel_left _ two_ne_zero, pow_succ, hk, hh]
  ring
private lemma cellIndex_parentBlock {n : ℕ} [NeZero n] (L : ℕ) [NeZero L] (hL : Odd L) (g : MirrorGrid)
    (x : TorusSite (n * L)) : g.cellIndex (parentBlock L x) = (refinedGrid g L).cellIndex x := by
  funext i
  simp only [MirrorGrid.cellIndex, parentBlock, refinedGrid]
  have := cellIndex_arith n L g.side hL ((x i).cast : ℤ) (g.offset i)
  push_cast at this ⊢
  rw [this]
private lemma sitesUnder_mono (L : ℕ) [NeZero L] : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' →
    sitesUnder L u n Q ⊆ sitesUnder L u n Q'
  | 0, _, _, _, _, h => h
  | u + 1, n, _, _, _, h => sitesUnder_mono L u (n * L) (sitesInBlocks_mono L h)
private lemma sitesUnder_cellSites (L : ℕ) [NeZero L] (hL : Odd L) :
    ∀ (u n : ℕ) [NeZero n] (g : MirrorGrid) (c : Fin 4 → ℕ),
    sitesUnder L u n (g.cellSites n c) ⊆ (g.atDepth L u).cellSites (fineSide L u n) c
  | 0, n, _, g, c => by
    rw [atDepth_zero]
    exact Finset.Subset.refl _
  | u + 1, n, _, g, c => by
    have h1 : sitesInBlocks L (g.cellSites n c) ⊆ (refinedGrid g L).cellSites (n * L) c := fun x hx => by
      simp only [sitesInBlocks, MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← cellIndex_parentBlock L hL]
      exact hx
    refine (sitesUnder_mono L u (n * L) h1).trans ?_
    rw [atDepth_succ g L u hL]
    exact sitesUnder_cellSites L hL u (n * L) (refinedGrid g L) c
private lemma unitIndicator_nonneg (rule : NoiseRule ℓ) (T : StageTower ℓ) (u n : ℕ) [NeZero n] (z : TorusSite n)
    (p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n) : 0 ≤ unitIndicator rule T u n z p := by
  unfold unitIndicator
  split_ifs <;> norm_num
private lemma abs_unitIndicator_le (rule : NoiseRule ℓ) (T : StageTower ℓ) (u n : ℕ) [NeZero n] (z : TorusSite n)
    (p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n) : |unitIndicator rule T u n z p| ≤ 1 := by
  unfold unitIndicator
  split_ifs <;> norm_num
private lemma prod_unitIndicator (rule : NoiseRule ℓ) (T : StageTower ℓ) (u n : ℕ) [NeZero n]
    (I : Finset (TorusSite n)) (p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n) :
    ∏ z ∈ I, unitIndicator rule T u n z p =
      Set.indicator ((fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n =>
        rule.chain T u n p.1 p.2) ⁻¹' {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z}) 1 p := by
  classical
  by_cases h : ∀ z ∈ I, HullTrees.IsUnit T u n (rule.chain T u n p.1 p.2) z
  · rw [Set.indicator_of_mem (by exact h)]
    simp only [Pi.one_apply]
    exact Finset.prod_eq_one fun z hz => by simp [unitIndicator, h z hz]
  · rw [Set.indicator_of_notMem (by exact h)]
    push Not at h
    obtain ⟨z, hz, hn⟩ := h
    exact Finset.prod_eq_zero hz (by simp [unitIndicator, hn])
private lemma boundedMeasurable_unitIndicator (rule : NoiseRule ℓ) (T : StageTower ℓ) (u n : ℕ) [NeZero n]
    (z : TorusSite n) (hm : Measurable (unitIndicator rule T u n z)) :
    BoundedMeasurable (unitIndicator rule T u n z) :=
  ⟨hm, 1, abs_unitIndicator_le rule T u n z⟩
private lemma measureReal_units_eq_integral (T : StageTower ℓ) (β : ℝ) (u n : ℕ) [NeZero n] (rule : NoiseRule ℓ)
    [IsProbabilityMeasure (wilsonLaw β (fineSide ℓ.side u n))] [IsProbabilityMeasure (markedSampleLaw T β u n)]
    (hlaw : ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)).map
      (fun p => rule.chain T u n p.1 p.2) = markedSampleLaw T β u n)
    (I : Finset (TorusSite n)) (hm : ∀ z ∈ I, Measurable (unitIndicator rule T u n z))
    (hA : MeasurableSet {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z}) :
    (markedSampleLaw T β u n).real {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} =
      ∫ W, ∫ U, ∏ z ∈ I, unitIndicator rule T u n z (W, U) ∂(chainNoiseLaw ℓ u n)
        ∂(wilsonLaw β (fineSide ℓ.side u n)) := by
  have hae : AEMeasurable (fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n =>
      rule.chain T u n p.1 p.2) ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) := by
    by_contra h
    have h0 : markedSampleLaw T β u n = 0 := by rw [← hlaw, Measure.map_of_not_aemeasurable h]
    exact IsProbabilityMeasure.ne_zero (markedSampleLaw T β u n) h0
  have tp : BoundedMeasurable fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n =>
      ∏ z ∈ I, unitIndicator rule T u n z p :=
    BoundedMeasurable.finsetProd I fun z hz => boundedMeasurable_unitIndicator rule T u n z (hm z hz)
  have hpre : MeasurableSet ((fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n =>
      rule.chain T u n p.1 p.2) ⁻¹' {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z}) := by
    have : ((fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n => rule.chain T u n p.1 p.2) ⁻¹'
        {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z}) =
        (fun p => ∏ z ∈ I, unitIndicator rule T u n z p) ⁻¹' {1} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, prod_unitIndicator]
      by_cases h : p ∈ ((fun p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n =>
        rule.chain T u n p.1 p.2) ⁻¹' {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z})
      · rw [Set.indicator_of_mem h]
        simpa using h
      · rw [Set.indicator_of_notMem h]
        simpa using h
    rw [this]
    exact tp.measurable (measurableSet_singleton 1)
  rw [← integral_prod (fun p => ∏ z ∈ I, unitIndicator rule T u n z p) (tp.integrable _)]
  simp only [prod_unitIndicator]
  rw [integral_indicator_one hpre, ← hlaw]
  simp only [Measure.real]
  rw [Measure.map_apply_of_aemeasurable hae hA]
private lemma measureReal_units_le_of_grid (T : StageTower ℓ) (β : ℝ) (u n : ℕ) [NeZero n] (rule : NoiseRule ℓ)
    (hL : Odd ℓ.side) (g : MirrorGrid) (I : Finset (TorusSite n)) (cf : TorusSite n → Fin 4 → ℕ) (a : ℝ)
    [IsProbabilityMeasure (wilsonLaw β (fineSide ℓ.side u n))] [IsProbabilityMeasure (markedSampleLaw T β u n)]
    (hlaw : ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)).map
      (fun p => rule.chain T u n p.1 p.2) = markedSampleLaw T β u n)
    (hc : ∀ z ∈ I, cf z ∈ g.cellIndices n)
    (hinj : ∀ z ∈ I, ∀ z' ∈ I, z ≠ z' → cf z ≠ cf z')
    (hin : ∀ z ∈ I, IsCellObservable ℓ g u n (cf z) (unitIndicator rule T u n z))
    (hnorm : ∀ z ∈ I, (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) (cf z)
      (noiseExpectation ℓ u n (unitIndicator rule T u n z)) ≤ Real.exp (-a))
    (hA : MeasurableSet {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z})
    (hidx : (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n) = g.cellIndices n)
    (hch : ∀ F : (Fin 4 → ℕ) → TorusField (fineSide ℓ.side u n) → ℝ,
      (∀ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
        IsCellFunction (g.atDepth ℓ.side u) (fineSide ℓ.side u n) c (F c)) →
      ∫ W, ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n), F c W
          ∂(wilsonLaw β (fineSide ℓ.side u n)) ≤
        ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
          (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (F c))
    (hone : ∀ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
      (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (fun _ => 1) = 1) :
    (markedSampleLaw T β u n).real {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} ≤ Real.exp (-(a * (I.card : ℝ))) := by
  classical
  let G : TorusSite n → TorusField (fineSide ℓ.side u n) → ℝ :=
    fun z => noiseExpectation ℓ u n (unitIndicator rule T u n z)
  let F : (Fin 4 → ℕ) → TorusField (fineSide ℓ.side u n) → ℝ :=
    fun c W => ∏ z ∈ I.filter (fun z => cf z = c), G z W
  have G0 : ∀ z W, 0 ≤ G z W := fun z W => integral_nonneg fun U => unitIndicator_nonneg rule T u n z (W, U)
  have G1 : ∀ z W, G z W ≤ 1 := fun z W => by
    have h := norm_integral_le_of_norm_le_const (μ := chainNoiseLaw ℓ u n)
      (f := fun U => unitIndicator rule T u n z (W, U)) (C := 1)
      (Filter.Eventually.of_forall fun U => by simpa using abs_unitIndicator_le rule T u n z (W, U))
    have h' : |G z W| ≤ 1 := by simpa [G, noiseExpectation] using h
    exact (le_abs_self _).trans h'
  have Gm : ∀ z ∈ I, Measurable (G z) := fun z hz =>
    ((hin z hz).measurable.stronglyMeasurable.integral_prod_right' (ν := chainNoiseLaw ℓ u n)).measurable
  have Gr : ∀ z ∈ I, DependsOnBondsIn ((g.atDepth ℓ.side u).cellSites (fineSide ℓ.side u n) (cf z)) (G z) :=
    fun z hz W W' h => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    refine (hin z hz).depends W W' U U (fun b h₁ h₂ => ?_) (noiseAgreeAbove_refl _ _ _ _)
    exact h b (sitesUnder_cellSites ℓ.side hL u n g (cf z) h₁) (sitesUnder_cellSites ℓ.side hL u n g (cf z) h₂)
  have hcell : ∀ c, IsCellFunction (g.atDepth ℓ.side u) (fineSide ℓ.side u n) c (F c) := fun c => by
    refine ⟨Finset.measurable_prod _ fun z hz => Gm z (Finset.mem_of_mem_filter z hz), ⟨1, fun W => ?_⟩,
      fun W => Finset.prod_nonneg fun z _ => G0 z W, fun W W' h => ?_⟩
    · rw [abs_of_nonneg (Finset.prod_nonneg fun z _ => G0 z W)]
      exact Finset.prod_le_one (fun z _ => G0 z W) fun z _ => G1 z W
    · refine Finset.prod_congr rfl fun z hz => ?_
      obtain ⟨hzI, rfl⟩ := Finset.mem_filter.mp hz
      exact Gr z hzI W W' h
  have step1 : (markedSampleLaw T β u n).real {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} =
      ∫ W, ∏ z ∈ I, G z W ∂(wilsonLaw β (fineSide ℓ.side u n)) := by
    rw [measureReal_units_eq_integral T β u n rule hlaw I (fun z hz => (hin z hz).measurable) hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    refine integral_chainNoiseLaw_prod u n I (fun z => g.cellSites n (cf z)) (fun z hz z' hz' hne => ?_)
      (fun z hz => ?_) (fun z hz U U' h => ?_)
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      exact hinj z hz z' hz' hne (hx.symm.trans hx')
    · exact ⟨(hin z hz).measurable.comp (measurable_const.prodMk measurable_id), 1,
        fun U => abs_unitIndicator_le rule T u n z (W, U)⟩
    · exact (hin z hz).depends W W U U' (fun _ _ _ => rfl) h
  have step2 : ∀ W, ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n), F c W = ∏ z ∈ I, G z W :=
    fun W => by
    rw [hidx]
    exact Finset.prod_fiberwise_of_maps_to hc _
  have bound : ∀ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
      (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (F c) ≤
        Real.exp (-a * ((I.filter fun z => cf z = c).card : ℝ)) := fun c hcm => by
    rcases (I.filter fun z => cf z = c).eq_empty_or_nonempty with h | ⟨z, hz⟩
    · have hF : F c = fun _ => 1 := by
        funext W
        simp [F, h]
      rw [hF, hone c hcm, h]
      simp
    · obtain ⟨hzI, hzc⟩ := Finset.mem_filter.mp hz
      have hs : (I.filter fun z => cf z = c) = {z} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hz, fun z' hz' => ?_⟩
        obtain ⟨hz'I, hz'c⟩ := Finset.mem_filter.mp hz'
        by_contra hne
        exact hinj z' hz'I z hzI hne (hz'c.trans hzc.symm)
      have hF : F c = G z := by
        funext W
        simp [F, hs]
      rw [hF, hs, ← hzc]
      simpa using hnorm z hzI
  have nonneg : ∀ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
      0 ≤ (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (F c) := fun c _ =>
    Real.rpow_nonneg (integral_nonneg fun W => Finset.prod_nonneg fun c' _ => (hcell c).nonneg _) _
  have total : ∑ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
      -a * ((I.filter fun z => cf z = c).card : ℝ) = -(a * (I.card : ℝ)) := by
    rw [← Finset.mul_sum, hidx, ← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hc]
    ring
  calc (markedSampleLaw T β u n).real {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z}
      = ∫ W, ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n), F c W
          ∂(wilsonLaw β (fineSide ℓ.side u n)) := by
        rw [step1]
        exact integral_congr_ae (Filter.Eventually.of_forall fun W => (step2 W).symm)
    _ ≤ ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
          (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (F c) := hch F fun c _ => hcell c
    _ ≤ ∏ c ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
          Real.exp (-a * ((I.filter fun z => cf z = c).card : ℝ)) := Finset.prod_le_prod nonneg bound
    _ = Real.exp (-(a * (I.card : ℝ))) := by rw [← Real.exp_sum, total]
private lemma measurable_topField : ∀ (s n : ℕ), Measurable (topField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    show Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1
    exact measurable_fst.comp (measurable_snd.comp measurable_snd)
private lemma measurableSet_containsHotPlaquette (u n : ℕ) [NeZero n] (B : Finset (TorusSite n)) :
    MeasurableSet {w : MarkedSample ℓ u n | ContainsHotPlaquette ℓ (topField ℓ u n w) B} := by
  have : {w : MarkedSample ℓ u n | ContainsHotPlaquette ℓ (topField ℓ u n w) B} =
      ⋃ p ∈ plaquettesIn B, {w | ℓ.threshold ≤ curvature (topField ℓ u n w) p.1 p.2.1 p.2.2} := by
    ext w
    simp [ContainsHotPlaquette]
  rw [this]
  refine Finset.measurableSet_biUnion _ fun p _ => ?_
  exact measurableSet_le measurable_const
    ((continuous_curvature p.1 p.2.1 p.2.2).measurable.comp (measurable_topField u n))
private lemma measurableSet_containsBadBlock : ∀ (u n : ℕ) [NeZero n] (B : Finset (TorusSite n)),
    MeasurableSet {w : MarkedSample ℓ u n | ContainsBadBlock ℓ u n w B}
  | 0, _, _, _ => by simp [ContainsBadBlock]
  | s + 1, n, _, B => by
    have hm : Measurable fun w : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => w.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    exact hm (MeasurableSpace.measurableSet_top
      (s := {bb : BondSet (n * ℓ.side) | ∃ b : TorusBond (n * ℓ.side),
        b ∈ (show Finset (TorusBond (n * ℓ.side)) from bb) ∧ parentBlock ℓ.side b.1 ∈ B}))
private lemma measurableSet_units (T : StageTower ℓ) (u n : ℕ) [NeZero n] (I : Finset (TorusSite n)) :
    MeasurableSet {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} := by
  have : {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} = ⋂ z ∈ I, {w | HullTrees.IsUnit T u n w z} := by
    ext w
    simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun z _ =>
    (measurableSet_containsHotPlaquette u n _).union (measurableSet_containsBadBlock u n _)
private lemma natAbs_valMinAbs_sub_le {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a - b).valMinAbs.natAbs ≤ ((a.val : ℤ) - b.val).natAbs := by
  refine ZMod.natAbs_min_of_le_div_two n _ _ ?_ (ZMod.natAbs_valMinAbs_le _)
  simp
private lemma card_le_of_separated {n L r : ℕ} [NeZero n] (hr : 0 < r) (hn : n ≤ 90 * L * r)
    (S : Finset (TorusSite n)) (h : HullTrees.Separated (30 * r) S) : S.card ≤ (3 * L) ^ 4 := by
  classical
  let φ : TorusSite n → Fin 4 → ℕ := fun z i => (z i).val / (30 * r)
  have hmap : ∀ z ∈ S, φ z ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.range (3 * L)) := fun z _ => by
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    apply Nat.div_lt_of_lt_mul
    have h1 := ZMod.val_lt (z i)
    calc (z i).val < n := h1
      _ ≤ 90 * L * r := hn
      _ = 30 * r * (3 * L) := by ring
  have hinj : Set.InjOn φ S := by
    intro a ha b hb hab
    by_contra hne
    have h30 := h a ha b hb hne
    have hlt : supDist a b < 30 * r := by
      unfold supDist
      rw [Finset.sup_lt_iff (by positivity)]
      intro i _
      have hi : (a i).val / (30 * r) = (b i).val / (30 * r) := congrFun hab i
      refine lt_of_le_of_lt (natAbs_valMinAbs_sub_le _ _) ?_
      have h1 := Nat.div_add_mod (a i).val (30 * r)
      have h2 := Nat.div_add_mod (b i).val (30 * r)
      have h3 := Nat.mod_lt (a i).val (show 0 < 30 * r by positivity)
      have h4 := Nat.mod_lt (b i).val (show 0 < 30 * r by positivity)
      rw [hi] at h1
      generalize (30 * r) * ((b i).val / (30 * r)) = w at h1 h2
      omega
    omega
  calc S.card ≤ (Fintype.piFinset fun _ : Fin 4 => Finset.range (3 * L)).card :=
        Finset.card_le_card_of_injOn φ hmap hinj
    _ = (3 * L) ^ 4 := by simp
private lemma leastPowerAbove_le (L a : ℕ) (hL : 1 < L) (ha : 1 < a) : leastPowerAbove L a ≤ L * a := by
  unfold leastPowerAbove
  have h1 := Nat.pow_pred_clog_lt_self hL ha
  have h2 : 0 < Nat.clog L a := Nat.clog_pos hL ha
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h2.ne'
  rw [hk] at h1 ⊢
  simp only [Nat.pred_succ] at h1
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left L h1.le
private lemma eventually_log_bound (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (L : ℕ) : ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x →
    Real.log 4 + C * Real.log x * (80 * (L : ℝ) * (clusterRange x : ℝ)) ^ 4 ≤ c / 2 * x := by
  set D : ℝ := 2 * C * (160 * (L : ℝ)) ^ 4 with hDdef
  have t := tendsto_rpow_atTop (y := (23 / 50 : ℝ)) (by norm_num)
  have e1 := t.eventually_ge_atTop (4 * D / c)
  have e2 := Filter.eventually_ge_atTop (1 : ℝ)
  have e3 := Filter.eventually_ge_atTop (4 * Real.log 4 / c)
  obtain ⟨y₀, hy⟩ := Filter.eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨y₀, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hy x hx
  have x0 : 0 < x := by linarith
  have hp : 1 ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow h2 (by norm_num)
  have hr : (clusterRange x : ℝ) ≤ 2 * x ^ (1 / 100 : ℝ) := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ x ^ ((1 : ℝ) / 100) by positivity)).le
    unfold clusterRange
    linarith
  have hr4 : (80 * (L : ℝ) * (clusterRange x : ℝ)) ^ 4 ≤ (160 * (L : ℝ)) ^ 4 * x ^ (1 / 25 : ℝ) := by
    calc (80 * (L : ℝ) * (clusterRange x : ℝ)) ^ 4 ≤ (80 * (L : ℝ) * (2 * x ^ (1 / 100 : ℝ))) ^ 4 := by gcongr
      _ = (160 * (L : ℝ)) ^ 4 * (x ^ (1 / 100 : ℝ)) ^ (4 : ℕ) := by ring
      _ = (160 * (L : ℝ)) ^ 4 * x ^ (1 / 25 : ℝ) := by
        have hq : (x ^ (1 / 100 : ℝ)) ^ (4 : ℕ) = x ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_natCast (x ^ (1 / 100 : ℝ)) 4, ← Real.rpow_mul x0.le]
          norm_num
        rw [hq]
  have hlog : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div x0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    calc Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := this
      _ = 2 * x ^ (1 / 2 : ℝ) := by ring
  have main : C * Real.log x * (80 * (L : ℝ) * (clusterRange x : ℝ)) ^ 4 ≤ D * x ^ (27 / 50 : ℝ) := by
    calc C * Real.log x * (80 * (L : ℝ) * (clusterRange x : ℝ)) ^ 4
        ≤ C * (2 * x ^ (1 / 2 : ℝ)) * ((160 * (L : ℝ)) ^ 4 * x ^ (1 / 25 : ℝ)) := by gcongr
      _ = D * (x ^ (1 / 2 : ℝ) * x ^ (1 / 25 : ℝ)) := by rw [hDdef]; ring
      _ = D * x ^ (27 / 50 : ℝ) := by
        rw [← Real.rpow_add x0]
        norm_num
  have hsplit : x ^ (23 / 50 : ℝ) * x ^ (27 / 50 : ℝ) = x := by
    rw [← Real.rpow_add x0]
    norm_num
  have h4 : D ≤ c / 4 * x ^ (23 / 50 : ℝ) := by
    rw [div_le_iff₀ hc] at h1
    linarith
  have h5 : D * x ^ (27 / 50 : ℝ) ≤ c / 4 * x := by
    calc D * x ^ (27 / 50 : ℝ) ≤ (c / 4 * x ^ (23 / 50 : ℝ)) * x ^ (27 / 50 : ℝ) := by gcongr
      _ = c / 4 * x := by rw [mul_assoc, hsplit]
  have h6 : Real.log 4 ≤ c / 4 * x := by
    rw [div_le_iff₀ hc] at h3
    linarith
  linarith
private lemma le_stageCoupling (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y))
    (hB : 0 ≤ Tb.B) (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (h : HullChain Tb y g β K m T) (u : ℕ) (hu : u ≤ K) : y ≤ stageCoupling T u := by
  have hΞ : (g ^ 2)⁻¹ + 2 * Tb.B = windowUpper (Tb.stepParameters y) g := rfl
  have hfl : y ≤ (g ^ 2)⁻¹ := h.le_inv_sq
  have hab : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := h.upper_le
  have hyΞ : y ≤ windowUpper (Tb.stepParameters y) g := by rw [← hΞ]; linarith
  have hyβ : y ≤ β := by linarith
  have hpass : ∀ j < K, windowUpper (Tb.stepParameters y) g < (couplingFlow (Tb.stepParameters y) β j).1 :=
    h.isFirst.2
  have step : ∀ j, j < K → HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
      (couplingFlow (Tb.stepParameters y) β j).2 →
      HasExpansion (Tb.stepParameters y) (j + 1) (couplingFlow (Tb.stepParameters y) β (j + 1)).1
          (couplingFlow (Tb.stepParameters y) β (j + 1)).2 ∧
        |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 - (couplingFlow (Tb.stepParameters y) β j).1| ≤
          2 * Tb.B := by
    intro j hj hr
    obtain ⟨x', ⟨hx', hb⟩, huniq⟩ := hret j _ _ (hyΞ.trans (hpass j hj).le) hr
    have hex : ∃ x', HasExpansion (Tb.stepParameters y) (j + 1) x'
        (kernelImage (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β j).1
          (couplingFlow (Tb.stepParameters y) β j).2) := ⟨x', hx'⟩
    have hnext : (couplingFlow (Tb.stepParameters y) β (j + 1)).1 = hex.choose := by
      show expansionCoupling _ _ _ _ = _
      unfold expansionCoupling
      rw [dif_pos hex]
    obtain ⟨_, f, hc, _⟩ := hex.choose_spec
    have hx : (couplingFlow (Tb.stepParameters y) β (j + 1)).1 = x' := hnext.trans (huniq _ f hc)
    rw [hx]
    exact ⟨hx', hb⟩
  have row : ∀ j, j ≤ K → HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
      (couplingFlow (Tb.stepParameters y) β j).2 := by
    intro j
    induction j with
    | zero => exact fun _ => hW β hyβ
    | succ j ih => exact fun hj => (step j hj (ih (by omega))).1
  have hx : stageCoupling T u = (couplingFlow (Tb.stepParameters y) β u).1 := h.follows u (by omega)
  rw [hx]
  rcases Nat.lt_or_ge u K with hlt | hge
  · exact hyΞ.trans (hpass u hlt).le
  · obtain rfl : u = K := le_antisymm hu hge
    cases u with
    | zero =>
      show y ≤ β
      exact hyβ
    | succ j =>
      have hj := (step j (by omega) (row j (by omega))).2
      have hp := hpass j (by omega)
      rw [← hΞ] at hp
      have := abs_le.mp hj
      linarith [this.1]
private lemma eventuallyInParameters_and {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : EventuallyInParameters P) (hQ : EventuallyInParameters Q) :
    EventuallyInParameters fun Tb Kr y => P Tb Kr y ∧ Q Tb Kr y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, p₂, h₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (p₁ c) (p₂ c), ?_⟩
  intro L hodd hL Tb e1 e2 hD hC hH hrt hCd
  obtain ⟨M₁, m₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) Tb e1 e2 hD hC hH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd)
  obtain ⟨M₂, m₂⟩ := h₂ L hodd ((le_max_right _ _).trans hL) Tb e1 e2 hD hC hH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd)
  refine ⟨max M₁ M₂, fun Kr hM a1 a2 a3 a4 => ?_⟩
  obtain ⟨y₁, k₁⟩ := m₁ Kr ((le_max_left _ _).trans hM) a1 a2 a3 a4
  obtain ⟨y₂, k₂⟩ := m₂ Kr ((le_max_right _ _).trans hM) a1 a2 a3 a4
  exact ⟨max y₁ y₂, fun y hy hr hw =>
    ⟨k₁ y ((le_max_left _ _).trans hy) hr hw, k₂ y ((le_max_right _ _).trans hy) hr hw⟩⟩
private lemma eventuallyInParameters_mono {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : EventuallyInParameters P)
    (h : ∀ Tb : ParameterAssignment, Tb.Admissible → ∃ Y : ℝ, ∀ (Kr : ResponseParameters) (y : ℝ), Y ≤ y →
      ExpansionReturnsAt (Tb.stepParameters y) →
      (∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) → P Tb Kr y → Q Tb Kr y) :
    EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, h₁⟩ := hP a ha
  refine ⟨L₁, r₁, C₁, p₁, ?_⟩
  intro L hodd hL Tb e1 e2 hD hC hH hrt hCd
  obtain ⟨M₁, m₁⟩ := h₁ L hodd hL Tb e1 e2 hD hC hH hrt hCd
  obtain ⟨Y, hY⟩ := h Tb hD
  refine ⟨M₁, fun Kr hM a1 a2 a3 a4 => ?_⟩
  obtain ⟨y₁, k₁⟩ := m₁ Kr hM a1 a2 a3 a4
  exact ⟨max y₁ Y, fun y hy hr hw =>
    hY Kr y ((le_max_right _ _).trans hy) hr hw (k₁ y ((le_max_left _ _).trans hy) hr hw)⟩
private lemma box_mono {n : ℕ} [NeZero n] (z : TorusSite n) {a b : ℕ} (h : a ≤ b) : box z a ⊆ box z b :=
  fun x hx => by
  simp only [box, thickening, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨w, hw, hd⟩ := hx
  exact ⟨w, hw, hd.trans h⟩
private lemma cellIndices_atDepth (g : MirrorGrid) (L u n : ℕ) [NeZero L] :
    (g.atDepth L u).cellIndices (fineSide L u n) = g.cellIndices n := by
  unfold MirrorGrid.cellIndices
  rw [fineSide_eq]
  simp only [MirrorGrid.atDepth]
  rw [Nat.mul_div_mul_right _ _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) u)]
private lemma torusSideAtLevel_eq (L K m u n : ℕ) (hu : u ≤ K) (h : n = torusSideAtLevel L K m u) :
    n = 2 * L ^ (m + (K - u)) ∧ fineSide L u n = 2 * L ^ (m + K) := by
  have h1 : n = 2 * L ^ (m + (K - u)) := by
    rw [h, torusSideAtLevel, fineSide_eq, pow_add]
    ring
  refine ⟨h1, ?_⟩
  rw [fineSide_eq, h1, mul_assoc, ← pow_add]
  congr 2
  omega
theorem separatedUnitsBound (hch : ChessboardGrids.chessboardEstimateStatement) (hre : HullTrees.unitIndicatorLocal)
    (hsx : ChessboardGrids.offsetSeparationStatement) (hfa : HullTrees.separatedUnitsRareStatement)
    (hno : unitProbabilityNormBoundStatement) (hnc : ChainNoise.noiseRepresentationStatement)
    (hbo : ResponseInTheExpansion.chainMeasurabilityStatement) : HullTrees.separatedUnitsBoundStatement := by
  obtain ⟨CE, hfa⟩ := hfa
  refine eventuallyInParameters_mono (eventuallyInParameters_and (eventuallyInParameters_and
    (eventuallyInParameters_and hre hsx) (eventuallyInParameters_and hfa hno)) hnc) fun Tb hD => ?_
  have hc : 0 < unitDecayRate Tb := by
    unfold unitDecayRate
    exact mul_pos (by norm_num) (lt_min (mul_pos hD.κ_pos (pow_pos hD.σ_pos 2)) hD.cE_pos)
  obtain ⟨Y, hY⟩ := eventually_log_bound |CE Tb| (unitDecayRate Tb) (abs_nonneg _) hc Tb.side
  refine ⟨max (max Tb.floorMin Y) 1, fun Kr y hy hret hW hP => ?_⟩
  obtain ⟨⟨⟨hreach, hsix⟩, hfar, hnorm⟩, hnoise⟩ := hP
  have hy₀ : Tb.floorMin ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyY : Y ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy₀
  intro g β K m T u n _ hat S hS
  have hB : 0 ≤ Tb.B := by linarith [hD.B_ge]
  have hx : y ≤ stageCoupling T u := le_stageCoupling Tb y g β K m T hB hret hW hat.chain u hat.le
  have hx1 : 1 ≤ stageCoupling T u := hy1.trans hx
  have hx0 : 0 < stageCoupling T u := by linarith
  have hr : 0 < stageRange T u := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
  have hbo' := hbo.2.2 (Tb.stepParameters y) hfit hfit.depth_lt T hat.chain.cutoff_bottom hat.chain.marks β
  have hP1 : IsProbabilityMeasure (markedSampleLaw T β u n) := (hbo' u n).1
  have hP0 : IsProbabilityMeasure (wilsonLaw β (fineSide (Tb.stepParameters y).side u n)) :=
    (hbo' 0 (fineSide (Tb.stepParameters y).side u n)).1
  obtain ⟨⟨rule, hrule⟩, hlaw⟩ := hnoise g β K m T hat.chain
  have hlaw' := hlaw rule hrule u n hat
  have hL16 : 2 ^ 16 ≤ Tb.side := hfit.L_ge
  have hL1 : 1 < Tb.side := by omega
  have h40 : 1 < 40 * stageRange T u := by omega
  have hLR : (0 : ℝ) < Tb.side := by exact_mod_cast (show 0 < Tb.side by omega)
  have hpr : 0 ≤ separatedUnitRate Tb := by
    unfold separatedUnitRate
    exact div_nonneg hc.le (by positivity)
  by_cases hgrid : 2 * leastPowerAbove (Tb.stepParameters y).side (40 * stageRange T u) ≤ n
  · obtain ⟨G, I, hside, hIS, hcard, cf, hcf, hne⟩ := hsix g β K m T u n hat hgrid S hS
    obtain ⟨hn1, hN⟩ := torusSideAtLevel_eq (Tb.stepParameters y).side K m u n hat.le hat.side_eq
    have hcl : 0 < Nat.clog Tb.side (40 * stageRange T u) := Nat.clog_pos hL1 h40
    have hm2 : 2 ≤ m := by
      by_contra h
      have hv : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hat.chain.volume_le
      have hn₀ := hD.n₀_ge
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl
      · rw [pow_zero] at hv
        nlinarith
      · rw [pow_one] at hv
        nlinarith
    have hβ : 0 < β := by
      have hfl : y ≤ (g ^ 2)⁻¹ := hat.chain.le_inv_sq
      have hab : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := hat.chain.upper_le
      linarith
    have hIG : IsGridOfTorus (G.atDepth (Tb.stepParameters y).side u) (Tb.stepParameters y).side (m + K) := by
      refine ⟨Nat.clog Tb.side (40 * stageRange T u) + u, by omega, ?_, ?_⟩
      · have h2 : Tb.side ^ Nat.clog Tb.side (40 * stageRange T u) ≤ Tb.side ^ (m + (K - u)) := by
          have h3 : 2 * Tb.side ^ Nat.clog Tb.side (40 * stageRange T u) ≤ n := hgrid
          have h4 : n = 2 * Tb.side ^ (m + (K - u)) := hn1
          omega
        have h5 := (Nat.pow_le_pow_iff_right hL1).mp h2
        have h6 := hat.le
        omega
      · show G.side * Tb.side ^ u = Tb.side ^ (Nat.clog Tb.side (40 * stageRange T u) + u)
        rw [hside, pow_add]
        rfl
    have chess := hch (Tb.stepParameters y).side (m + K) (fineSide (Tb.stepParameters y).side u n) β
      (G.atDepth (Tb.stepParameters y).side u) hfit.L_odd hfit.L_ge (by omega) hβ hN hIG
    have hmono : {w | ∀ z ∈ S, HullTrees.IsUnit T u n w z} ⊆ {w | ∀ z ∈ I, HullTrees.IsUnit T u n w z} :=
      fun w hw z hz => hw z (hIS hz)
    have hbound := measureReal_units_le_of_grid T β u n rule hfit.L_odd G I cf
      (unitDecayRate Tb * stageCoupling T u / 32) hlaw'
      (fun z hz => (hcf z hz).1) hne
      (fun z hz => (hreach g β K m T u n hat rule hrule z).2 G (cf z)
        ((box_mono z (by omega)).trans (hcf z hz).2))
      (fun z hz => hnorm g β K m T u n hat rule hrule G hside (by rw [hside]; exact hgrid) z (cf z) (hcf z hz).1
        ((box_mono z (by omega)).trans (hcf z hz).2))
      (measurableSet_units T u n I) (cellIndices_atDepth G _ u n) chess.1 (fun c hc => (chess.2 c hc).2)
    refine (measureReal_mono hmono).trans (hbound.trans (Real.exp_le_exp.mpr ?_))
    have hcard' : (S.card : ℝ) ≤ 16 * (2 * (Tb.side : ℝ)) ^ 4 * (I.card : ℝ) := hcard
    have e : separatedUnitRate Tb * stageCoupling T u * (16 * (2 * (Tb.side : ℝ)) ^ 4 * (I.card : ℝ)) =
        unitDecayRate Tb * stageCoupling T u / 32 * (I.card : ℝ) := by
      unfold separatedUnitRate
      field_simp
      ring
    have h7 : separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ) ≤
        unitDecayRate Tb * stageCoupling T u / 32 * (I.card : ℝ) := by
      rw [← e]
      exact mul_le_mul_of_nonneg_left hcard' (mul_nonneg hpr hx0.le)
    linarith
  · have hgrid' : n < 2 * leastPowerAbove Tb.side (40 * stageRange T u) := not_le.mp hgrid
    have hlp := leastPowerAbove_le Tb.side (40 * stageRange T u) hL1 h40
    have e80 : 80 * Tb.side * stageRange T u = 2 * (Tb.side * (40 * stageRange T u)) := by ring
    have hn80 : n ≤ 80 * Tb.side * stageRange T u := by omega
    have hn90 : n ≤ 90 * Tb.side * stageRange T u := hn80.trans (by gcongr; norm_num)
    have hSc : S.card ≤ (3 * Tb.side) ^ 4 := card_le_of_separated hr hn90 S hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨z0, hz0⟩
    · have h1 : (markedSampleLaw T β u n).real
          {w | ∀ z ∈ (∅ : Finset (TorusSite n)), HullTrees.IsUnit T u n w z} ≤ 1 :=
        measureReal_le_one
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero]
      exact h1
    · have hf := hfar g β K m T u n hat {z0} (Finset.singleton_nonempty z0)
        (fun a ha b hb hab => absurd ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm) hab)
      have hmono : {w | ∀ z ∈ S, HullTrees.IsUnit T u n w z} ⊆
          {w | ∀ z ∈ ({z0} : Finset (TorusSite n)), HullTrees.IsUnit T u n w z} :=
        fun w hw z hz => hw z (by rw [Finset.mem_singleton.mp hz]; exact hz0)
      refine (measureReal_mono hmono).trans (hf.trans ?_)
      rw [Finset.card_singleton]
      have hnum : Real.log 4 + |CE Tb| * Real.log (stageCoupling T u) *
          (80 * (Tb.side : ℝ) * (stageRange T u : ℝ)) ^ 4 ≤ unitDecayRate Tb / 2 * stageCoupling T u :=
        hY _ (hyY.trans hx)
      have e4 : (2 : ℝ) ^ (1 + 1) = Real.exp (Real.log 4) := by
        rw [Real.exp_log (by norm_num)]
        norm_num
      rw [e4, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log (stageCoupling T u) := Real.log_nonneg hx1
      have hn4 : (n : ℝ) ^ 4 ≤ (80 * (Tb.side : ℝ) * (stageRange T u : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn80) 4
      have h1 : CE Tb * Real.log (stageCoupling T u) * (n : ℝ) ^ 4 ≤
          |CE Tb| * Real.log (stageCoupling T u) * (80 * (Tb.side : ℝ) * (stageRange T u : ℝ)) ^ 4 := by
        calc CE Tb * Real.log (stageCoupling T u) * (n : ℝ) ^ 4
            ≤ |CE Tb| * Real.log (stageCoupling T u) * (n : ℝ) ^ 4 := by
              have := le_abs_self (CE Tb)
              gcongr
          _ ≤ _ := by gcongr
      have hS81 : (S.card : ℝ) ≤ 81 * (Tb.side : ℝ) ^ 4 := by
        have : S.card ≤ 81 * Tb.side ^ 4 := hSc.trans (le_of_eq (by ring))
        exact_mod_cast this
      have h2 : separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ) ≤ unitDecayRate Tb / 2 * stageCoupling T u := by
        calc separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ)
            ≤ separatedUnitRate Tb * stageCoupling T u * (81 * (Tb.side : ℝ) ^ 4) :=
              mul_le_mul_of_nonneg_left hS81 (mul_nonneg hpr hx0.le)
          _ = 81 / 2 ^ 13 * (unitDecayRate Tb * stageCoupling T u) := by
              unfold separatedUnitRate
              field_simp
          _ ≤ unitDecayRate Tb / 2 * stageCoupling T u := by nlinarith [mul_pos hc hx0]
      push_cast
      linarith
end YangMills.Construction.HullsInEveryVolume
end
