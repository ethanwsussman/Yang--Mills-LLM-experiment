import YangMills.Construction.ReflectionPositiveLimits.ReconstructionFromAContractionAtADenseSetOfTimesProof
import YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction
import YangMills.Construction.SpectralCalculus.SpectralResolutionUniqueness
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus
namespace ResolutionUniqueness
section Bounded
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
theorem integrable_of_isBoundedMeasurable {f : α → ℂ} (hf : IsBoundedMeasurable f)
    (μ : ComplexMeasure α) : μ.Integrable f := by apply _root_.YangMills.Construction.SpectralCalculus.JointSpectralProof.integrable_of_isBoundedMeasurable <;> assumption
theorem isBoundedMeasurable_comp {f : β → ℂ} (hf : IsBoundedMeasurable f) {g : α → β}
    (hg : Measurable g) : IsBoundedMeasurable (f ∘ g) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨hm.comp hg, C, fun x => hC (g x)⟩
theorem complexIntegral_map (μ : ComplexMeasure α) {g : α → β} (hg : Measurable g)
    {f : β → ℂ} (hf : IsBoundedMeasurable f) : complexIntegral (μ.map g) f = complexIntegral μ (f ∘ g) :=
  VectorMeasure.integral_map hg hf.1.aestronglyMeasurable
    (integrable_of_isBoundedMeasurable (isBoundedMeasurable_comp hf hg) μ)
theorem isBoundedMeasurable_indicator {f : α → ℂ} (hf : IsBoundedMeasurable f) {S : Set α}
    (hS : MeasurableSet S) : IsBoundedMeasurable (S.indicator f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.indicator hS, max C 0, fun x => ?_⟩
  by_cases hx : x ∈ S
  · simpa [hx] using Or.inl (hC x)
  · simp [hx]
theorem isBoundedMeasurable_truncate {f : SpectralPlane → ℂ} (hf : Measurable f) (n : ℕ) :
    IsBoundedMeasurable (ProjValuedMeasure.truncate f n) := by apply _root_.YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction.isBoundedMeasurable_truncate <;> assumption
end Bounded
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem projValuedMeasure_ext {P Q : ProjValuedMeasure H} (h : ∀ S, P S = Q S) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h
def pushforward (P : ProjValuedMeasure H) (g : SpectralPlane → SpectralPlane)
    (hg : Measurable g) : ProjValuedMeasure H where
  toFun S := P ⟨g ⁻¹' S.1, hg S.2⟩
  isOrthogonalProjection _ := P.isOrthogonalProjection _
  map_univ := P.map_univ
  map_inter _ _ := P.map_inter _ _
  exists_complexMeasure u v := ⟨(P.matrixCoeff u v).map g, fun S => by
    rw [VectorMeasure.map_apply _ hg S.2]
    exact P.matrixCoeff_apply u v ⟨g ⁻¹' S.1, hg S.2⟩⟩
section Pushforward
variable {P : ProjValuedMeasure H} {g : SpectralPlane → SpectralPlane}
  (hg : Measurable g)
include hg in
theorem matrixCoeff_pushforward (u v : H) :
    (pushforward P g hg).matrixCoeff u v = (P.matrixCoeff u v).map g := by
  refine VectorMeasure.ext fun S hS => ?_
  rw [VectorMeasure.map_apply _ hg hS]
  exact ((pushforward P g hg).matrixCoeff_apply u v ⟨S, hS⟩).trans
    (P.matrixCoeff_apply u v ⟨g ⁻¹' S, hg hS⟩).symm
theorem boundedSpectralIntegral_pushforward (hI : SpectralIntegralProperties (pushforward P g hg))
    (hP : SpectralIntegralProperties P) {f : SpectralPlane → ℂ} (hf : IsBoundedMeasurable f) :
    (pushforward P g hg).boundedSpectralIntegral f = P.boundedSpectralIntegral (f ∘ g) := by
  refine (hI.eq_boundedSpectralIntegral f _ hf fun u v => ?_).symm
  rw [hP.isBoundedSpectralIntegral _ (isBoundedMeasurable_comp hf hg) u v,
    matrixCoeff_pushforward hg, complexIntegral_map _ hg hf]
theorem variation_pushforward (hI : SpectralIntegralProperties (pushforward P g hg))
    (hP : SpectralIntegralProperties P) (v : H) :
    ((pushforward P g hg).matrixCoeff v v).variation = (P.matrixCoeff v v).variation.map g := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hg hS]
  have e : (pushforward P g hg).matrixCoeff v v S = P.matrixCoeff v v (g ⁻¹' S) := by
    rw [matrixCoeff_pushforward hg, VectorMeasure.map_apply _ hg hS]
  have h₁ : ((pushforward P g hg).matrixCoeff v v).variation.real S =
      (P.matrixCoeff v v (g ⁻¹' S)).re := by
    rw [← e]
    exact hI.variation_eq v ⟨S, hS⟩
  have h₂ := hP.variation_eq v ⟨g ⁻¹' S, hg hS⟩
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (h₁.trans h₂.symm)
theorem spectralIntegral_pushforward (hI : SpectralIntegralProperties (pushforward P g hg))
    (hP : SpectralIntegralProperties P) {f : SpectralPlane → ℂ} (hf : Measurable f) :
    (pushforward P g hg).spectralIntegral f = P.spectralIntegral (f ∘ g) := by
  refine (hI.eq_spectralIntegral f _ hf ⟨?_, fun v => ?_⟩).symm
  · rw [(hP.isSpectralIntegral _ (hf.comp hg)).1]
    ext v
    simp only [ProjValuedMeasure.spectralDomain, mem_ofPred_eq]
    rw [variation_pushforward hg hI hP, lintegral_map (hf.enorm.pow_const 2) hg]
    rfl
  · refine ((hP.isSpectralIntegral _ (hf.comp hg)).2 v).congr fun n => ?_
    rw [boundedSpectralIntegral_pushforward hg hI hP (isBoundedMeasurable_truncate hf n)]
    rfl
end Pushforward
theorem partialOfCLM_eq_spectralIntegral {P : ProjValuedMeasure H}
    (hP : SpectralIntegralProperties P) {f : SpectralPlane → ℂ} {T : H →L[ℂ] H}
    (hf : IsBoundedMeasurable f) (hT : P.IsBoundedSpectralIntegral f T) :
    partialOfCLM T = P.spectralIntegral f := by
  obtain ⟨hd, hv⟩ := hP.spectralIntegral_of_isBoundedMeasurable f hf
  have e : T = P.boundedSpectralIntegral f := hP.eq_boundedSpectralIntegral f T hf hT
  refine LinearPMap.ext hd.symm fun x hx hy => ?_
  rw [hv ⟨x, hy⟩, ← e]
  rfl
theorem partialComp_partialOfCLM (A B : H →L[ℂ] H) :
    partialComp (partialOfCLM A) (partialOfCLM B) = partialOfCLM (A * B) := by
  have hd : compDomain (partialOfCLM A) (partialOfCLM B) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact ⟨⟨x, trivial⟩, trivial, rfl⟩
  refine LinearPMap.ext ?_ fun x _ _ => rfl
  show compDomain _ _ ⊓ ⊤ = ⊤
  rw [hd]
  exact inf_top_eq _
def sndCharacter (s : ℝ) (p : SpectralPlane) : ℂ := Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ))
theorem norm_sndCharacter (s : ℝ) (p : SpectralPlane) : ‖sndCharacter s p‖ = 1 := by
  rw [sndCharacter, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
theorem measurable_sndCharacter (s : ℝ) : Measurable (sndCharacter s) := by
  unfold sndCharacter
  fun_prop
theorem isBoundedMeasurable_sndCharacter (s : ℝ) : IsBoundedMeasurable (sndCharacter s) :=
  ⟨measurable_sndCharacter s, 1, fun p => (norm_sndCharacter s p).le⟩
theorem sndCharacter_add (s a : ℝ) (p : SpectralPlane) :
    sndCharacter (s + a) p = sndCharacter s p * sndCharacter a p := by
  simp only [sndCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem conj_sndCharacter (s : ℝ) (p : SpectralPlane) :
    conj (sndCharacter s p) = sndCharacter (-s) p := by
  simp only [sndCharacter, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring
theorem measurable_coordSnd : Measurable coordSnd := by apply _root_.YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction.measurable_lineMomentumCoord <;> assumption
section Character
variable {P : ProjValuedMeasure H}
theorem boundedSpectralIntegral_one (hP : SpectralIntegralProperties P) :
    P.boundedSpectralIntegral (fun _ => 1) = 1 := by
  have h := hP.boundedSpectralIntegral_indicator ⟨univ, MeasurableSet.univ⟩
  simp only [indicator_univ] at h
  rw [h]
  exact P.map_univ
theorem boundedSpectralIntegral_sndCharacter_zero (hP : SpectralIntegralProperties P) :
    P.boundedSpectralIntegral (sndCharacter 0) = 1 := by
  have : sndCharacter 0 = fun _ => 1 := by
    funext p
    simp [sndCharacter]
  rw [this]
  exact boundedSpectralIntegral_one hP
theorem boundedSpectralIntegral_sndCharacter_mul (hP : SpectralIntegralProperties P) (s a : ℝ) :
    P.boundedSpectralIntegral (sndCharacter s) * P.boundedSpectralIntegral (sndCharacter a) =
      P.boundedSpectralIntegral (sndCharacter (s + a)) := by
  rw [hP.boundedSpectralIntegral_mul _ _ (isBoundedMeasurable_sndCharacter s)
    (isBoundedMeasurable_sndCharacter a)]
  congr 1
  funext p
  exact (sndCharacter_add s a p).symm
theorem boundedSpectralIntegral_sndCharacter_neg_mul (hP : SpectralIntegralProperties P) (s : ℝ) :
    P.boundedSpectralIntegral (sndCharacter (-s)) * P.boundedSpectralIntegral (sndCharacter s) = 1 := by
  rw [boundedSpectralIntegral_sndCharacter_mul hP, neg_add_cancel,
    boundedSpectralIntegral_sndCharacter_zero hP]
theorem inner_boundedSpectralIntegral_sndCharacter (hP : SpectralIntegralProperties P) (s : ℝ)
    (u v : H) :
    inner ℂ (P.boundedSpectralIntegral (sndCharacter s) u) v =
      inner ℂ u (P.boundedSpectralIntegral (sndCharacter (-s)) v) := by
  have h := hP.inner_boundedSpectralIntegral (sndCharacter s) (isBoundedMeasurable_sndCharacter s) u v
  have e : (fun p => conj (sndCharacter s p)) = sndCharacter (-s) := funext (conj_sndCharacter s)
  rwa [e] at h
theorem sndCharacter_commute (hP : SpectralIntegralProperties P) (s : ℝ)
    (S : MeasurableSubtype SpectralPlane) :
    P.boundedSpectralIntegral (sndCharacter s) * P S = P S * P.boundedSpectralIntegral (sndCharacter s) := by
  have hS : IsBoundedMeasurable (S.1.indicator fun _ : SpectralPlane => (1 : ℂ)) :=
    isBoundedMeasurable_indicator ⟨measurable_const, 1, fun _ => by simp⟩ S.2
  rw [← hP.boundedSpectralIntegral_indicator S,
    hP.boundedSpectralIntegral_mul _ _ (isBoundedMeasurable_sndCharacter s) hS,
    hP.boundedSpectralIntegral_mul _ _ hS (isBoundedMeasurable_sndCharacter s)]
  congr 1
  funext p
  exact mul_comm _ _
theorem variation_sndCharacter (hP : SpectralIntegralProperties P) (s : ℝ) (v : H) :
    (P.matrixCoeff (P.boundedSpectralIntegral (sndCharacter s) v)
      (P.boundedSpectralIntegral (sndCharacter s) v)).variation = (P.matrixCoeff v v).variation := by
  refine Measure.ext fun S hS => ?_
  have h₁ := hP.variation_eq (P.boundedSpectralIntegral (sndCharacter s) v) ⟨S, hS⟩
  have h₂ := hP.variation_eq v ⟨S, hS⟩
  have e : P.matrixCoeff (P.boundedSpectralIntegral (sndCharacter s) v)
      (P.boundedSpectralIntegral (sndCharacter s) v) S = P.matrixCoeff v v S := by
    have a₁ := P.matrixCoeff_apply (P.boundedSpectralIntegral (sndCharacter s) v)
      (P.boundedSpectralIntegral (sndCharacter s) v) ⟨S, hS⟩
    have a₂ := P.matrixCoeff_apply v v ⟨S, hS⟩
    have c := sndCharacter_commute hP s ⟨S, hS⟩
    have c' : P ⟨S, hS⟩ (P.boundedSpectralIntegral (sndCharacter s) v) =
        P.boundedSpectralIntegral (sndCharacter s) (P ⟨S, hS⟩ v) :=
      (DFunLike.congr_fun c v).symm
    have n : P.boundedSpectralIntegral (sndCharacter (-s))
        (P.boundedSpectralIntegral (sndCharacter s) (P ⟨S, hS⟩ v)) = P ⟨S, hS⟩ v :=
      DFunLike.congr_fun (boundedSpectralIntegral_sndCharacter_neg_mul hP s) _
    simp only at a₁ a₂
    rw [a₁, a₂, c', inner_boundedSpectralIntegral_sndCharacter hP, n]
  simp only at h₁ h₂
  rw [e] at h₁
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h₁.trans h₂.symm)
theorem mem_spectralIntegral_domain_iff (hP : SpectralIntegralProperties P) {f : SpectralPlane → ℂ}
    (hf : Measurable f) (v : H) :
    v ∈ (P.spectralIntegral f).domain ↔ v ∈ P.spectralDomain f := by
  rw [← SetLike.mem_coe, (hP.isSpectralIntegral f hf).1]
theorem sndCharacter_mem_domain (hP : SpectralIntegralProperties P) (s : ℝ) {v : H}
    (hv : v ∈ (P.spectralIntegral coordSnd).domain) :
    P.boundedSpectralIntegral (sndCharacter s) v ∈ (P.spectralIntegral coordSnd).domain := by
  rw [mem_spectralIntegral_domain_iff hP measurable_coordSnd] at hv ⊢
  simp only [ProjValuedMeasure.spectralDomain, mem_ofPred_eq] at hv ⊢
  rwa [variation_sndCharacter hP]
def diffQuotient (a : ℝ) (p : SpectralPlane) : ℂ := ((a⁻¹ : ℝ) : ℂ) * (sndCharacter a p - 1)
def diffRemainder (a : ℝ) (p : SpectralPlane) : ℂ :=
  diffQuotient a p - Complex.I * coordSnd p
theorem measurable_diffQuotient (a : ℝ) : Measurable (diffQuotient a) :=
  ((measurable_sndCharacter a).sub_const 1).const_mul _
theorem measurable_diffRemainder (a : ℝ) : Measurable (diffRemainder a) :=
  (measurable_diffQuotient a).sub (measurable_coordSnd.const_mul _)
theorem isBoundedMeasurable_diffQuotient (a : ℝ) : IsBoundedMeasurable (diffQuotient a) := by
  refine ⟨measurable_diffQuotient a, ‖((a⁻¹ : ℝ) : ℂ)‖ * 2, fun p => ?_⟩
  rw [diffQuotient, norm_mul]
  gcongr
  calc ‖sndCharacter a p - 1‖ ≤ ‖sndCharacter a p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_sndCharacter, norm_one]; norm_num
theorem norm_diffQuotient_le {a : ℝ} (ha : a ≠ 0) (p : SpectralPlane) :
    ‖diffQuotient a p‖ ≤ ‖coordSnd p‖ := by
  have h : ‖sndCharacter a p - 1‖ ≤ ‖a * p.2‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
  have ha' : 0 < |a| := abs_pos.mpr ha
  rw [diffQuotient, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  rw [Real.norm_eq_abs, abs_mul] at h
  have hq : ‖coordSnd p‖ = |p.2| := by simp [coordSnd]
  rw [hq, inv_mul_le_iff₀ ha']
  exact h
theorem norm_diffRemainder_le {a : ℝ} (ha : a ≠ 0) (p : SpectralPlane) :
    ‖diffRemainder a p‖ ≤ 2 * ‖coordSnd p‖ := by
  have h₁ := norm_diffQuotient_le ha p
  have h₂ : ‖Complex.I * coordSnd p‖ = ‖coordSnd p‖ := by simp
  have h₃ := norm_sub_le (diffQuotient a p) (Complex.I * coordSnd p)
  rw [diffRemainder]
  linarith
theorem enorm_sq_diffRemainder_le {a : ℝ} (ha : a ≠ 0) (p : SpectralPlane) :
    ‖diffRemainder a p‖ₑ ^ 2 ≤ 4 * ‖coordSnd p‖ₑ ^ 2 := by
  have h : ‖diffRemainder a p‖ₑ ≤ 2 * ‖coordSnd p‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖diffRemainder a p‖
        ≤ ENNReal.ofReal (2 * ‖coordSnd p‖) :=
          ENNReal.ofReal_le_ofReal (norm_diffRemainder_le ha p)
      _ = 2 * ENNReal.ofReal ‖coordSnd p‖ := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
  calc ‖diffRemainder a p‖ₑ ^ 2 ≤ (2 * ‖coordSnd p‖ₑ) ^ 2 := by gcongr
    _ = 4 * ‖coordSnd p‖ₑ ^ 2 := by rw [mul_pow]; norm_num
theorem tendsto_diffRemainder (p : SpectralPlane) :
    Tendsto (fun a : ℝ => diffRemainder a p) (𝓝[≠] 0) (𝓝 0) := by
  have h₀ : HasDerivAt (fun a : ℝ => ((a * p.2 : ℝ) : ℂ)) (p.2 : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const p.2).ofReal_comp
  have h₁ : HasDerivAt (fun a : ℝ => sndCharacter a p) (Complex.I * coordSnd p) 0 := by
    simpa [sndCharacter, coordSnd] using (h₀.const_mul Complex.I).cexp
  have h₂ := hasDerivAt_iff_tendsto_slope_zero.mp h₁
  have h₃ : Tendsto (fun a : ℝ => diffQuotient a p - Complex.I * coordSnd p) (𝓝[≠] 0)
      (𝓝 (Complex.I * coordSnd p - Complex.I * coordSnd p)) := by
    refine (h₂.congr fun a => ?_).sub_const _
    simp [diffQuotient, sndCharacter, Complex.real_smul]
  simpa [diffRemainder] using h₃
theorem tendsto_lintegral_diffRemainder {u : H} (hu : u ∈ P.spectralDomain coordSnd) :
    Tendsto (fun a : ℝ => ∫⁻ p, ‖diffRemainder a p‖ₑ ^ 2 ∂(P.matrixCoeff u u).variation)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := (P.matrixCoeff u u).variation)
    (l := 𝓝[≠] (0 : ℝ)) (F := fun a p => ‖diffRemainder a p‖ₑ ^ 2) (f := fun _ => 0)
    (fun p => 4 * ‖coordSnd p‖ₑ ^ 2)
    (Eventually.of_forall fun a => (measurable_diffRemainder a).enorm.pow_const 2)
    (eventually_mem_nhdsWithin.mono fun a ha => Eventually.of_forall fun p =>
      enorm_sq_diffRemainder_le ha p)
    (by
      rw [lintegral_const_mul' _ _ (by norm_num)]
      exact ENNReal.mul_ne_top (by norm_num) hu.ne)
    (Eventually.of_forall fun p => by
      have h₁ : Tendsto (fun a : ℝ => ‖diffRemainder a p‖ₑ) (𝓝[≠] 0) (𝓝 0) := by
        have h₀ := (continuous_enorm.tendsto (0 : ℂ)).comp (tendsto_diffRemainder p)
        simpa [Function.comp_def] using h₀
      simpa using ENNReal.Tendsto.pow (n := 2) h₁)
  simpa using h
def sndStrip (n : ℕ) : MeasurableSubtype SpectralPlane :=
  ⟨{p | ‖coordSnd p‖ ≤ n}, measurableSet_le measurable_coordSnd.norm measurable_const⟩
theorem isBoundedExhaustion_sndStrip {f : SpectralPlane → ℂ}
    (hf : ∀ p, ‖f p‖ = ‖coordSnd p‖) : IsBoundedExhaustion f sndStrip where
  monotone := fun m n hmn p hp => by
    have h : ‖coordSnd p‖ ≤ m := hp
    exact h.trans (Nat.cast_le.mpr hmn)
  iUnion_eq := by
    refine eq_univ_of_forall fun p => mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖coordSnd p‖
    exact ⟨n, hn⟩
  isBounded := fun n => ⟨n, fun p hp => (hf p).le.trans hp⟩
theorem spectralIntegral_I_mul (hP : SpectralIntegralProperties P) {u : H}
    (hu : u ∈ (P.spectralIntegral coordSnd).domain)
    (hu' : u ∈ (P.spectralIntegral fun p => Complex.I * coordSnd p).domain) :
    (P.spectralIntegral fun p => Complex.I * coordSnd p) ⟨u, hu'⟩ =
      Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩ := by
  have hm' : Measurable fun p => Complex.I * coordSnd p := measurable_coordSnd.const_mul _
  have t₁ := hP.tendsto_boundedSpectralIntegral_indicator _ sndStrip hm'
    (isBoundedExhaustion_sndStrip fun p => by simp) ⟨u, hu'⟩
  have t₂ := hP.tendsto_boundedSpectralIntegral_indicator _ sndStrip measurable_coordSnd
    (isBoundedExhaustion_sndStrip fun _ => rfl) ⟨u, hu⟩
  refine tendsto_nhds_unique t₁ ((t₂.const_smul Complex.I).congr fun n => ?_)
  have hb : IsBoundedMeasurable ((sndStrip n).1.indicator coordSnd) := by
    refine ⟨measurable_coordSnd.indicator (sndStrip n).2, n, fun p => ?_⟩
    by_cases hp : p ∈ (sndStrip n).1
    · rw [indicator_of_mem hp]
      exact hp
    · simp [hp]
  have e : ((sndStrip n).1.indicator fun p => Complex.I * coordSnd p) =
      fun p => Complex.I * (sndStrip n).1.indicator coordSnd p := by
    funext p
    by_cases hp : p ∈ (sndStrip n).1 <;> simp [hp]
  rw [e, hP.boundedSpectralIntegral_smul _ _ hb]
  rfl
theorem spectralIntegral_apply_congr {f g : SpectralPlane → ℂ} (h : f = g) {v : H}
    (hf : v ∈ (P.spectralIntegral f).domain) (hg : v ∈ (P.spectralIntegral g).domain) :
    P.spectralIntegral f ⟨v, hf⟩ = P.spectralIntegral g ⟨v, hg⟩ := by
  subst h
  rfl
theorem boundedSpectralIntegral_diffQuotient (hP : SpectralIntegralProperties P) (a : ℝ) :
    P.boundedSpectralIntegral (diffQuotient a) =
      ((a⁻¹ : ℝ) : ℂ) • (P.boundedSpectralIntegral (sndCharacter a) - 1) := by
  have h₁ : IsBoundedMeasurable fun _ : SpectralPlane => (1 : ℂ) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have h₂ : IsBoundedMeasurable fun p : SpectralPlane => (-1 : ℂ) * 1 := by
    refine ⟨measurable_const, 1, fun _ => by simp⟩
  have h₃ : IsBoundedMeasurable fun p => sndCharacter a p + (-1 : ℂ) * 1 := by
    refine ⟨(measurable_sndCharacter a).add_const _, 2, fun p => ?_⟩
    calc ‖sndCharacter a p + (-1 : ℂ) * 1‖ ≤ ‖sndCharacter a p‖ + ‖(-1 : ℂ) * 1‖ := norm_add_le _ _
      _ = 2 := by rw [norm_sndCharacter]; norm_num
  have e : diffQuotient a = fun p => ((a⁻¹ : ℝ) : ℂ) * (sndCharacter a p + (-1 : ℂ) * 1) := by
    funext p
    simp [diffQuotient, sub_eq_add_neg]
  rw [e, hP.boundedSpectralIntegral_smul _ _ h₃,
    hP.boundedSpectralIntegral_add _ _ (isBoundedMeasurable_sndCharacter a) h₂,
    hP.boundedSpectralIntegral_smul _ _ h₁, boundedSpectralIntegral_one hP]
  simp [sub_eq_add_neg]
theorem tendsto_diffQuotient_apply (hP : SpectralIntegralProperties P) {u : H}
    (hu : u ∈ (P.spectralIntegral coordSnd).domain) :
    Tendsto (fun a : ℝ => a⁻¹ • (P.boundedSpectralIntegral (sndCharacter a) u - u)) (𝓝[≠] 0)
      (𝓝 (Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩)) := by
  have hfin := (mem_spectralIntegral_domain_iff hP measurable_coordSnd u).mp hu
  have hm' : Measurable fun p => Complex.I * coordSnd p := measurable_coordSnd.const_mul _
  have hIq : u ∈ (P.spectralIntegral fun p => Complex.I * coordSnd p).domain := by
    rw [mem_spectralIntegral_domain_iff hP hm']
    have he : ∀ p, ‖Complex.I * coordSnd p‖ₑ = ‖coordSnd p‖ₑ := fun p => by
      rw [← ofReal_norm, ← ofReal_norm, norm_mul, Complex.norm_I, one_mul]
    simpa only [ProjValuedMeasure.spectralDomain, mem_ofPred_eq, he] using hfin
  have hrem : ∀ a : ℝ, a ≠ 0 → u ∈ (P.spectralIntegral (diffRemainder a)).domain := by
    intro a ha
    rw [mem_spectralIntegral_domain_iff hP (measurable_diffRemainder a)]
    refine lt_of_le_of_lt (lintegral_mono fun p => enorm_sq_diffRemainder_le ha p) ?_
    rw [lintegral_const_mul' _ _ (by norm_num)]
    exact ENNReal.mul_lt_top (by norm_num) hfin
  have key : ∀ (a : ℝ) (ha : a ≠ 0),
      a⁻¹ • (P.boundedSpectralIntegral (sndCharacter a) u - u) -
          Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩ =
        P.spectralIntegral (diffRemainder a) ⟨u, hrem a ha⟩ := by
    intro a ha
    obtain ⟨hs, he⟩ := hP.spectralIntegral_add _ _ (measurable_diffRemainder a) hm' u
      (hrem a ha) hIq
    have hfun : (fun p => diffRemainder a p + Complex.I * coordSnd p) = diffQuotient a := by
      funext p
      simp [diffRemainder]
    obtain ⟨hd, hv⟩ :=
      hP.spectralIntegral_of_isBoundedMeasurable _ (isBoundedMeasurable_diffQuotient a)
    have hq : u ∈ (P.spectralIntegral (diffQuotient a)).domain := by
      rw [hd]
      trivial
    have h₁ := spectralIntegral_apply_congr hfun hs hq
    rw [he, spectralIntegral_I_mul hP hu hIq, hv ⟨u, hq⟩,
      boundedSpectralIntegral_diffQuotient hP] at h₁
    rw [← Complex.coe_smul]
    rw [eq_sub_of_add_eq h₁]
    simp
  have hnorm : Tendsto (fun a : ℝ => ‖a⁻¹ • (P.boundedSpectralIntegral (sndCharacter a) u - u) -
      Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    refine (tendsto_lintegral_diffRemainder hfin).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with a ha
    rw [key a ha, hP.enorm_sq_spectralIntegral _ (measurable_diffRemainder a) ⟨u, hrem a ha⟩]
  have hnorm₁ : Tendsto (fun a : ℝ => ‖a⁻¹ • (P.boundedSpectralIntegral (sndCharacter a) u - u) -
      Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩‖ₑ) (𝓝[≠] 0) (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hnorm
    have e0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := by simp
    rw [e0] at h
    refine h.congr fun a => ?_
    simp only [Function.comp]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hz := tendsto_zero_iff_enorm_tendsto_zero.mpr hnorm₁
  simpa using hz.add_const (Complex.I • P.spectralIntegral coordSnd ⟨u, hu⟩)
theorem hasDerivAt_sndCharacter (hP : SpectralIntegralProperties P) {A : PartialOperator H}
    (hA : P.spectralIntegral coordSnd = A) {v : H} (hv : v ∈ A.domain) (s : ℝ) :
    ∃ hs : P.boundedSpectralIntegral (sndCharacter s) v ∈ A.domain,
      HasDerivAt (fun s => P.boundedSpectralIntegral (sndCharacter s) v)
        (Complex.I • A ⟨P.boundedSpectralIntegral (sndCharacter s) v, hs⟩) s := by
  subst hA
  refine ⟨sndCharacter_mem_domain hP s hv, ?_⟩
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (tendsto_diffQuotient_apply hP (sndCharacter_mem_domain hP s hv)).congr fun a => ?_
  have h := DFunLike.congr_fun (boundedSpectralIntegral_sndCharacter_mul hP a s) v
  have h' : P.boundedSpectralIntegral (sndCharacter a) (P.boundedSpectralIntegral (sndCharacter s) v) =
      P.boundedSpectralIntegral (sndCharacter (a + s)) v := h
  rw [h', add_comm a s]
end Character
theorem sndCharacter_apply_eq_of_spectralIntegral_eq {P' P'' : ProjValuedMeasure H}
    (hP' : SpectralIntegralProperties P') (hP'' : SpectralIntegralProperties P'')
    (hA : P'.spectralIntegral coordSnd = P''.spectralIntegral coordSnd) {v : H}
    (hv : v ∈ (P'.spectralIntegral coordSnd).domain) (s : ℝ) :
    P'.boundedSpectralIntegral (sndCharacter s) v = P''.boundedSpectralIntegral (sndCharacter s) v := by
  set A := P'.spectralIntegral coordSnd with hAdef
  have d₁ := fun s => hasDerivAt_sndCharacter hP' rfl hv s
  have d₂ := fun s => hasDerivAt_sndCharacter hP'' hA.symm hv s
  choose m₁ e₁ using d₁
  choose m₂ e₂ using d₂
  let w : ℝ → H := fun s =>
    P'.boundedSpectralIntegral (sndCharacter s) v - P''.boundedSpectralIntegral (sndCharacter s) v
  have hw : ∀ s, w s ∈ A.domain := fun s => A.domain.sub_mem (m₁ s) (m₂ s)
  have dw : ∀ s, HasDerivAt w (Complex.I • A ⟨w s, hw s⟩) s := fun s => by
    have h := (e₁ s).sub (e₂ s)
    have e : (⟨w s, hw s⟩ : A.domain) = ⟨_, m₁ s⟩ - ⟨_, m₂ s⟩ := rfl
    rw [e, LinearPMap.map_sub, smul_sub]
    exact h
  have hsym := (hP'.isSelfAdjoint_spectralIntegral coordSnd measurable_coordSnd
    fun p => by simp [coordSnd]).symmetric
  have dg : ∀ s, HasDerivAt (fun s => (inner ℂ (w s) (w s) : ℂ)) 0 s := fun s => by
    have h := (dw s).inner ℂ (dw s)
    have e : (inner ℂ (w s) (Complex.I • A ⟨w s, hw s⟩) : ℂ) +
        inner ℂ (Complex.I • A ⟨w s, hw s⟩) (w s) = 0 := by
      rw [inner_smul_right, inner_smul_left, Complex.conj_I, hsym ⟨w s, hw s⟩ ⟨w s, hw s⟩]
      ring
    rwa [e] at h
  have hc := is_const_of_deriv_eq_zero (fun s => (dg s).differentiableAt) (fun s => (dg s).deriv) s 0
  have w0 : w 0 = 0 := by
    simp [w, boundedSpectralIntegral_sndCharacter_zero hP', boundedSpectralIntegral_sndCharacter_zero hP'']
  have hz : w s = 0 := by
    refine inner_self_eq_zero (𝕜 := ℂ).mp ?_
    have hc' : (inner ℂ (w s) (w s) : ℂ) = inner ℂ (w 0) (w 0) := hc
    rw [hc', w0, inner_zero_left]
  exact sub_eq_zero.mp hz
theorem sndCharacter_eq_of_spectralIntegral_eq {P' P'' : ProjValuedMeasure H}
    (hP' : SpectralIntegralProperties P') (hP'' : SpectralIntegralProperties P'')
    (hA : P'.spectralIntegral coordSnd = P''.spectralIntegral coordSnd) (s : ℝ) :
    P'.boundedSpectralIntegral (sndCharacter s) = P''.boundedSpectralIntegral (sndCharacter s) := by
  have hd : Dense ((P'.spectralIntegral coordSnd).domain : Set H) := by
    rw [(hP'.isSpectralIntegral _ measurable_coordSnd).1]
    exact (isSeqDense_iff_dense _).mp
      (hP'.isSeqDense_spectralDomain _ measurable_coordSnd)
  exact DFunLike.coe_injective (Continuous.ext_on hd (P'.boundedSpectralIntegral (sndCharacter s)).continuous
    (P''.boundedSpectralIntegral (sndCharacter s)).continuous
    fun v hv => sndCharacter_apply_eq_of_spectralIntegral_eq hP' hP'' hA hv s)
def zeroFst (p : SpectralPlane) : SpectralPlane := (0, p.2)
def fstToSnd (p : SpectralPlane) : SpectralPlane := (0, (p.1 : ℝ))
theorem measurable_zeroFst : Measurable zeroFst :=
  measurable_const.prodMk measurable_snd
theorem measurable_fstToSnd : Measurable fstToSnd :=
  measurable_const.prodMk (measurable_coe_nnreal_real.comp measurable_fst)
theorem isBoundedMeasurable_spectralCharacter (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (spectralCharacter t s) := by apply _root_.YangMills.Construction.SpectralCalculus.JointSpectralProof.isBoundedMeasurable_spectralCharacter <;> assumption
theorem spectralCharacter_comp_zeroFst (t : ℝ≥0) (s : ℝ) :
    spectralCharacter t s ∘ zeroFst = sndCharacter s := by
  funext p
  simp [spectralCharacter, sndCharacter, zeroFst]
theorem pushforward_zeroFst_eq
    (hU : ∀ μ ν : ComplexMeasure SpectralPlane,
      (∀ (t : ℝ≥0) (s : ℝ), laplaceFourier μ t s = laplaceFourier ν t s) → μ = ν)
    {P' P'' : ProjValuedMeasure H} (hP' : SpectralIntegralProperties P')
    (hP'' : SpectralIntegralProperties P'')
    (hA : P'.spectralIntegral coordSnd = P''.spectralIntegral coordSnd) :
    pushforward P' zeroFst measurable_zeroFst = pushforward P'' zeroFst measurable_zeroFst := by
  have hν : ∀ u v, (P'.matrixCoeff u v).map zeroFst = (P''.matrixCoeff u v).map zeroFst := by
    intro u v
    refine hU _ _ fun t s => ?_
    have hb := isBoundedMeasurable_spectralCharacter t s
    rw [laplaceFourier, laplaceFourier, complexIntegral_map _ measurable_zeroFst hb,
      complexIntegral_map _ measurable_zeroFst hb, spectralCharacter_comp_zeroFst,
      ← hP'.isBoundedSpectralIntegral _ (isBoundedMeasurable_sndCharacter s) u v,
      ← hP''.isBoundedSpectralIntegral _ (isBoundedMeasurable_sndCharacter s) u v,
      sndCharacter_eq_of_spectralIntegral_eq hP' hP'' hA]
  refine projValuedMeasure_ext fun S => ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  have h := congrArg (fun μ : ComplexMeasure SpectralPlane => μ S.1) (hν u v)
  rw [VectorMeasure.map_apply _ measurable_zeroFst S.2,
    VectorMeasure.map_apply _ measurable_zeroFst S.2] at h
  exact (P'.matrixCoeff_apply u v ⟨_, measurable_zeroFst S.2⟩).symm.trans
    (h.trans (P''.matrixCoeff_apply u v ⟨_, measurable_zeroFst S.2⟩))
theorem pushforward_zeroFst_cylinderSet (P : ProjValuedMeasure H) (S : MeasurableSubtype ℝ) :
    pushforward P zeroFst measurable_zeroFst (cylinderSet S) = P (cylinderSet S) :=
  congrArg P.toFun (Subtype.ext (by ext p; simp [cylinderSet, zeroFst]))
theorem pushforward_fstToSnd_cylinderSet (P : ProjValuedMeasure H) (S : MeasurableSubtype ℝ) :
    pushforward P fstToSnd measurable_fstToSnd (cylinderSet S) = P (fstCylinderSet S) :=
  congrArg P.toFun (Subtype.ext (by ext p; simp [cylinderSet, fstCylinderSet, fstToSnd]))
end ResolutionUniqueness
open ResolutionUniqueness in
theorem spectralResolutionUniqueness_of_spectralIntegralTheorem (hS : SpectralIntegralTheorem)
    (hU : TwoPoints.SpectralMeasureUniqueness.Statement) :
    SpectralResolutionUniqueness := by
  intro H _ _ _
  have props : ∀ P : ProjValuedMeasure H, SpectralIntegralProperties P := (hS H).1
  obtain ⟨-, hU₂⟩ := hU
  have partA : ∀ P' P'' : ProjValuedMeasure H,
      P'.spectralIntegral coordSnd = P''.spectralIntegral coordSnd →
        (∀ S : MeasurableSubtype ℝ, P' (cylinderSet S) = P'' (cylinderSet S)) ∧
        ∀ f : ℝ → ℂ, Measurable f →
          P'.spectralIntegral (fun p => f p.2) = P''.spectralIntegral fun p => f p.2 := by
    intro P' P'' hA
    have hI := pushforward_zeroFst_eq hU₂ (props P') (props P'') hA
    refine ⟨fun S => ?_, fun f hf => ?_⟩
    · rw [← pushforward_zeroFst_cylinderSet P', ← pushforward_zeroFst_cylinderSet P'', hI]
    · have hg : Measurable fun p : SpectralPlane => f p.2 := hf.comp measurable_snd
      have e₁ := spectralIntegral_pushforward measurable_zeroFst (props _) (props P') hg
      have e₂ := spectralIntegral_pushforward measurable_zeroFst (props _) (props P'') hg
      rw [hI] at e₁
      exact e₁.symm.trans e₂
  have readOff : ∀ (A : PartialOperator H) (P' : ProjValuedMeasure H),
      IsSpectralIntegralSnd P' A →
        (∀ S : MeasurableSubtype ℝ, spectralProjection A S = P' (cylinderSet S)) ∧
        ∀ f : ℝ → ℂ, Measurable f →
          functionalCalculus f A = P'.spectralIntegral fun p => f p.2 := by
    intro A P' hA
    have hs : HasSpectralResolution A := ⟨P', hA⟩
    have hc : IsSpectralIntegralSnd (Classical.choose hs) A := Classical.choose_spec hs
    have h := partA _ P' (hc.symm.trans hA)
    refine ⟨fun S => ?_, fun f hf => ?_⟩
    · rw [spectralProjection, dif_pos hs]
      exact h.1 S
    · rw [functionalCalculus, dif_pos hs]
      exact h.2 f hf
  refine ⟨partA, readOff, fun P => ?_⟩
  have hE : IsSpectralIntegralSnd (pushforward P fstToSnd measurable_fstToSnd)
      (P.spectralIntegral coordFst) :=
    (spectralIntegral_pushforward measurable_fstToSnd (props _) (props P)
      measurable_coordSnd).symm
  have hQ : IsSpectralIntegralSnd P (P.spectralIntegral coordSnd) := rfl
  have rE := readOff _ _ hE
  have rQ := readOff _ _ hQ
  have sE : ∀ S : MeasurableSubtype ℝ,
      spectralProjection (P.spectralIntegral coordFst) S = P (fstCylinderSet S) := fun S =>
    (rE.1 S).trans (pushforward_fstToSnd_cylinderSet P S)
  have fE : ∀ f : ℝ → ℂ, Measurable f →
      functionalCalculus f (P.spectralIntegral coordFst) =
        P.spectralIntegral fun p => f (p.1 : ℝ) := fun f hf =>
    (rE.2 f hf).trans (spectralIntegral_pushforward measurable_fstToSnd (props _) (props P)
      (hf.comp measurable_snd))
  refine ⟨⟨_, hE⟩, ⟨_, hQ⟩, fun S => ⟨sE S, rQ.1 S⟩, fun f hf => ⟨fE f hf, rQ.2 f hf⟩,
    ⟨⟨_, hE⟩, ⟨_, hQ⟩, fun S S' => ?_⟩, fun T U hTU hM => ?_⟩
  · rw [sE S, rQ.1 S']
    show P.toFun _ * P.toFun _ = P.toFun _ * P.toFun _
    rw [P.map_inter, P.map_inter]
    exact congrArg P.toFun (Subtype.ext (inter_comm _ _))
  · have bT : ∀ t, partialOfCLM (T t) = expNegMul t (P.spectralIntegral coordFst) := by
      intro t
      have hb := hM t 0
      rw [hTU.group.map_zero, mul_one] at hb
      rw [partialOfCLM_eq_spectralIntegral (props P) (isBoundedMeasurable_spectralCharacter t 0) hb,
        expNegMul, fE _ (by fun_prop)]
      congr 1
      funext p
      simp [spectralCharacter]
    have bU : ∀ s, partialOfCLM (U s) = expIMul s (P.spectralIntegral coordSnd) := by
      intro s
      have hb := hM 0 s
      rw [hTU.semigroup.map_zero, one_mul] at hb
      rw [partialOfCLM_eq_spectralIntegral (props P) (isBoundedMeasurable_spectralCharacter 0 s) hb,
        expIMul, rQ.2 _ (by fun_prop)]
      congr 1
      funext p
      simp [spectralCharacter]
    refine ⟨bT, bU, fun t s => ?_⟩
    rw [← bT, ← bU, partialComp_partialOfCLM]
    exact partialOfCLM_eq_spectralIntegral (props P) (isBoundedMeasurable_spectralCharacter t s) (hM t s)
end YangMills.Construction.SpectralCalculus
end
