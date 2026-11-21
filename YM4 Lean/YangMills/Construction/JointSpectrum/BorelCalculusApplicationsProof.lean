import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrierProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open JointSpectrum JointSpectrum.SpectralIntegral FamilyPolynomials MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ComplexOrder
namespace JointSpectrum.CalculusApplications
section Functions
variable {J : Type}
private lemma isBoundedFn_of_continuous {f : SpectralDomain J → ℂ} (hf : Continuous f) :
    BorelCalculus.IsBoundedFn f := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun p => hM p (mem_univ p)⟩
private lemma isBoundedFn_indicator_one (T : Set (SpectralDomain J)) :
    BorelCalculus.IsBoundedFn (T.indicator (1 : SpectralDomain J → ℂ)) := by
  refine ⟨1, fun p => ?_⟩
  by_cases hp : p ∈ T <;> simp [hp]
private lemma measurable_indicator_one {T : Set (SpectralDomain J)} (hT : MeasurableSet T) :
    Measurable (T.indicator (1 : SpectralDomain J → ℂ)) :=
  measurable_one.indicator hT
private lemma noncommProd_eq_of_eq_one_of_ne {G : Type*} [Monoid G] (g : J → G) (i : J)
    (hg : ∀ j, j ≠ i → g j = 1) (s : Finset J) (comm) (hi : i ∈ s) :
    s.noncommProd g comm = g i := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.noncommProd_eq_of_eq_one_of_ne <;> assumption
end Functions
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
private lemma mem_integralDomain_of_bounded (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f : SpectralDomain J → ℂ} (hf : Measurable f)
    (hb : BorelCalculus.IsBoundedFn f) (x : H) : x ∈ integralDomain S f := by
  obtain ⟨c1, -⟩ := h H J S
  rw [((c1 f hf).2.2.2.2 hb).1]
  exact mem_univ x
private lemma exists_clm_eq_spectralIntegral (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f : SpectralDomain J → ℂ} (hf : Measurable f)
    (hb : BorelCalculus.IsBoundedFn f) :
    ∃ C : H →L[ℂ] H, ⇑C = spectralIntegral S f := by
  obtain ⟨c1, -⟩ := h H J S
  obtain ⟨C, hC, -⟩ := ((c1 f hf).2.2.2.2 hb).2
  exact ⟨C, hC⟩
private lemma enorm_sq_spectralIntegral (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f : SpectralDomain J → ℂ} (hf : Measurable f) {x : H}
    (hx : x ∈ integralDomain S f) :
    ‖spectralIntegral S f x‖ₑ ^ 2 =
      ScalarSpectralMeasures.sqNormLIntegral (ScalarSpectralMeasures.spectralMeasure S x) f := by
  obtain ⟨c1, -⟩ := h H J S
  exact ((c1 f hf).2.2.2.1 x hx).1
private lemma inner_spectralIntegral_self (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f : SpectralDomain J → ℂ} (hf : Measurable f) {x : H}
    (hx : x ∈ integralDomain S f) :
    inner ℂ x (spectralIntegral S f x) = ∫ p, f p ∂(ScalarSpectralMeasures.spectralMeasure S x) := by
  obtain ⟨c1, -⟩ := h H J S
  exact ((c1 f hf).2.2.2.1 x hx).2
private lemma isFiniteMeasure_spectralMeasure
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (S : CommutingFamily H J) (x : H) :
    IsFiniteMeasure (ScalarSpectralMeasures.spectralMeasure S x) :=
  ((hm H J S).2.2.2.1 x).1.1
private lemma spectralIntegral_zero_apply (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) (x : H) : spectralIntegral S 0 x = 0 := by
  have hb : BorelCalculus.IsBoundedFn (0 : SpectralDomain J → ℂ) :=
    ⟨0, fun p => by simp⟩
  have h1 := enorm_sq_spectralIntegral h S measurable_zero
    (mem_integralDomain_of_bounded h S measurable_zero hb x)
  have h2 : ScalarSpectralMeasures.sqNormLIntegral (ScalarSpectralMeasures.spectralMeasure S x)
      (0 : SpectralDomain J → ℂ) = 0 := by
    simp [ScalarSpectralMeasures.sqNormLIntegral]
  rw [h2] at h1
  simpa using h1
private lemma jointSpectralMeasure_apply_eq_zero_iff (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {T : Set (SpectralDomain J)} (hT : MeasurableSet T) (x : H) :
    jointSpectralMeasure S T x = 0 ↔ ScalarSpectralMeasures.spectralMeasure S x T = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := h H J S
  have h1 := (c10 T x hT).2
  rw [← h1]
  simp
private lemma jointSpectralMeasure_univ_apply (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) (x : H) : jointSpectralMeasure S univ x = x := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨P, hP, -⟩, -⟩ := h H J S
  have h1 := hP ⟨univ, MeasurableSet.univ⟩
  have h2 := P.E_univ
  change ⇑(P.E ⟨univ, MeasurableSet.univ⟩) = jointSpectralMeasure S univ at h1
  rw [← h1, h2]
  rfl
private lemma jointSpectralMeasure_add_compl_apply (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {T : Set (SpectralDomain J)} (hT : MeasurableSet T) (x : H) :
    jointSpectralMeasure S T x + jointSpectralMeasure S Tᶜ x = x := by
  obtain ⟨-, -, -, c4, -⟩ := h H J S
  have h1 := (c4 _ _ (measurable_indicator_one hT) (measurable_indicator_one hT.compl) 1 x
    (mem_integralDomain_of_bounded h S (measurable_indicator_one hT) (isBoundedFn_indicator_one T) x)
    (mem_integralDomain_of_bounded h S (measurable_indicator_one hT.compl)
      (isBoundedFn_indicator_one Tᶜ) x)).2
  have h2 : T.indicator (1 : SpectralDomain J → ℂ) +
      (1 : ℂ) • Tᶜ.indicator (1 : SpectralDomain J → ℂ) =
      univ.indicator (1 : SpectralDomain J → ℂ) := by
    funext p
    by_cases hp : p ∈ T <;> simp [hp]
  rw [h2, one_smul] at h1
  exact h1.symm.trans (jointSpectralMeasure_univ_apply h S x)
private lemma spectralIntegral_one_apply (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) (x : H) : spectralIntegral S 1 x = x := by
  have h1 := jointSpectralMeasure_univ_apply h S x
  unfold jointSpectralMeasure at h1
  rwa [indicator_univ] at h1
private lemma spectralIntegral_sub_apply (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f g : SpectralDomain J → ℂ} (hf : Measurable f)
    (hg : Measurable g) {x : H} (hxf : x ∈ integralDomain S f) (hxg : x ∈ integralDomain S g) :
    x ∈ integralDomain S (f - g) ∧
      spectralIntegral S (f - g) x = spectralIntegral S f x - spectralIntegral S g x := by
  obtain ⟨-, -, -, c4, -⟩ := h H J S
  have h1 := c4 f g hf hg (-1) x hxf hxg
  have h2 : f + (-1 : ℂ) • g = f - g := by
    funext p
    simp [sub_eq_add_neg]
  rw [h2] at h1
  refine ⟨h1.1, ?_⟩
  rw [h1.2]
  simp [sub_eq_add_neg]
private lemma unitaryMonomial_zero (S : CommutingFamily H J) : S.unitaryMonomial 0 = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.unitaryMonomial_zero <;> assumption
private lemma unitaryMonomial_single (S : CommutingFamily H J) (i : J) [DecidableEq J] :
    S.unitaryMonomial (Pi.single i 1) = (S.B i : H →L[ℂ] H) := by
  have h1 : Finset.univ.noncommProd (fun j => S.B j ^ (Pi.single i 1 : J → ℤ) j)
      (fun j _ k _ _ => S.commute_zpow_unitary (Pi.single i 1) j k) = S.B i := by
    refine (noncommProd_eq_of_eq_one_of_ne _ i (fun j hj => by simp [Pi.single_eq_of_ne hj]) _ _
      (Finset.mem_univ i)).trans ?_
    simp
  exact congrArg Subtype.val h1
private lemma spectralIntegral_coord (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) :
    spectralIntegral S (fun p => (((p.1 : ℝ)) : ℂ)) = ⇑S.A := by
  obtain ⟨-, -, c3, -⟩ := h H J S
  have h1 := (c3 1 0).2
  have h2 : (spectralMonomial 1 0 : SpectralDomain J → ℂ) = fun p => (((p.1 : ℝ)) : ℂ) := by
    funext p
    simp [spectralMonomial, torusMonomial]
  rw [h2] at h1
  rw [h1]
  simp [familyMonomial, unitaryMonomial_zero]
private lemma spectralIntegral_circleCoord (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) (i : J) :
    spectralIntegral S (fun p => ((p.2 i : Circle) : ℂ)) = ⇑(S.B i : H →L[ℂ] H) := by
  classical
  obtain ⟨-, -, c3, -⟩ := h H J S
  have h1 := (c3 0 (Pi.single i 1)).2
  have h2 : (spectralMonomial 0 (Pi.single i 1) : SpectralDomain J → ℂ) =
      fun p => ((p.2 i : Circle) : ℂ) := by
    funext p
    simp only [spectralMonomial, torusMonomial, pow_zero, one_mul]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h2] at h1
  rw [h1]
  simp [familyMonomial, unitaryMonomial_single]
private lemma nonneg_iff_spectralIntegral (h : BorelCalculus.BorelCalculusStatement)
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement) (S : CommutingFamily H J)
    (f : SpectralDomain J → ℝ) (hf : Measurable f) (hb : ∃ M : ℝ, ∀ p, |f p| ≤ M) :
    ∃ C : H →L[ℂ] H, ⇑C = spectralIntegral S (fun p => (f p : ℂ)) ∧ IsSelfAdjoint C ∧
      (0 ≤ C ↔ jointSpectralMeasure S {p | f p < 0} = 0) := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨-, -, -, -, -, hcalc, hdensity, -⟩ := h H J S
  have hmeasC : Measurable (fun p => (f p : ℂ)) := hf.complex_ofReal
  have hbddC : BorelCalculus.IsBoundedFn (fun p => (f p : ℂ)) := by
    refine ⟨M, fun p => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM p
  obtain ⟨C, hC, hstar⟩ := (hcalc _ hmeasC).2.2 hbddC
  have hsa : IsSelfAdjoint C := by
    show star C = C
    apply DFunLike.coe_injective
    rw [hstar, hC]
    congr 1
    funext p
    exact Complex.conj_ofReal _
  refine ⟨C, hC, hsa, ?_⟩
  have hfinite := isFiniteMeasure_spectralMeasure hm S
  have hintf : ∀ x : H, Integrable f (ScalarSpectralMeasures.spectralMeasure S x) := by
    intro x
    have := hfinite x
    refine Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hM p
  have hquad : ∀ x : H,
      inner ℂ x (C x) = ((∫ p, f p ∂(ScalarSpectralMeasures.spectralMeasure S x) : ℝ) : ℂ) := by
    intro x
    have hx := mem_integralDomain_of_bounded h S hmeasC hbddC x
    rw [hC, inner_spectralIntegral_self h S hmeasC hx]
    exact integral_ofReal
  have hT : MeasurableSet {p | f p < 0} := measurableSet_lt hf measurable_const
  rw [LatticeBasics.le_iff_inner_nonneg hsa (IsSelfAdjoint.zero _)]
  simp only [sub_zero]
  set T : Set (SpectralDomain J) := {p | f p < 0} with hTdef
  refine ⟨fun hpos => ?_, fun hzero x => ?_⟩
  · funext x
    refine (jointSpectralMeasure_apply_eq_zero_iff h S hT x).mpr ?_
    have hind : (fun p => ‖T.indicator (1 : SpectralDomain J → ℂ) p‖ₑ ^ 2) =
        T.indicator (1 : SpectralDomain J → ℝ≥0∞) := by
      funext p
      by_cases hp : p ∈ T <;> simp [hp]
    have hwd := (hdensity _ (measurable_indicator_one hT) x
      (mem_integralDomain_of_bounded h S (measurable_indicator_one hT)
        (isBoundedFn_indicator_one T) x)).1
    rw [hind, withDensity_indicator_one hT] at hwd
    have hge := hpos (spectralIntegral S (T.indicator 1) x)
    rw [hquad, hwd, Complex.zero_le_real] at hge
    set μ := (ScalarSpectralMeasures.spectralMeasure S x).restrict T with hμ
    have hneg : ∀ᵐ p ∂μ, f p < 0 := ae_restrict_mem hT
    have hnegint : ∫ p, -f p ∂μ = 0 := by
      rw [integral_neg]
      have hle : ∫ p, f p ∂μ ≤ 0 := integral_nonpos_of_ae (hneg.mono fun _ hp => hp.le)
      linarith
    have hae : (fun p => -f p) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (f := fun p => -f p)
        (hneg.mono fun p hp => (neg_pos.mpr hp).le) (hintf x).restrict.neg).mp hnegint
    have hbot : ae μ = ⊥ := by
      rw [← Filter.eventually_false_iff_eq_bot]
      filter_upwards [hneg, hae] with p hp hq
      have hfp : f p = 0 := by simpa using hq
      linarith
    have hμ0 : μ = 0 := ae_eq_bot.mp hbot
    calc ScalarSpectralMeasures.spectralMeasure S x T = μ univ :=
          (Measure.restrict_apply_univ T).symm
      _ = 0 := by rw [hμ0]; rfl
  · rw [hquad, Complex.zero_le_real]
    have hnull := (jointSpectralMeasure_apply_eq_zero_iff h S hT x).mp (congrFun hzero x)
    refine integral_nonneg_of_ae ?_
    rw [Filter.EventuallyLE, ae_iff]
    simpa [hTdef] using hnull
private lemma orthProj_nullSet_spectralIntegral (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) (f : SpectralDomain J → ℂ) (hf : Measurable f)
    (hb : BorelCalculus.IsBoundedFn f) :
    ∃ P C : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | f p = 0} ∧ ⇑C = spectralIntegral S f ∧
      HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet C) := by
  obtain ⟨-, -, -, -, -, -, -, c8, ⟨Q, hQ, -⟩, -⟩ := h H J S
  have hZ : MeasurableSet {p | f p = 0} := hf (measurableSet_singleton 0)
  set Z : Set (SpectralDomain J) := {p | f p = 0} with hZdef
  obtain ⟨C, hC⟩ := exists_clm_eq_spectralIntegral h S hf hb
  have hP : ⇑(Q.E ⟨Z, hZ⟩) = jointSpectralMeasure S Z := hQ ⟨Z, hZ⟩
  refine ⟨Q.E ⟨Z, hZ⟩, C, hP, hC,
    ⟨(Q.isStarProjection _).isSelfAdjoint.star_eq.symm,
      (Q.isStarProjection _).isIdempotentElem.eq.symm⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change C (Q.E ⟨Z, hZ⟩ y) = 0
    rw [hC, hP]
    have h1 := congrFun (c8 f _ hf (measurable_indicator_one hZ) hb
      (isBoundedFn_indicator_one Z)).1 y
    have h2 : f * Z.indicator (1 : SpectralDomain J → ℂ) = 0 := by
      funext p
      by_cases hp : p ∈ Z
      · have : f p = 0 := hp
        simp [this]
      · simp [hp]
    rw [h2, spectralIntegral_zero_apply h S y] at h1
    exact h1.symm
  · intro hx
    have hx' : C x = 0 := hx
    have h1 := enorm_sq_spectralIntegral h S hf (mem_integralDomain_of_bounded h S hf hb x)
    rw [← hC, hx'] at h1
    have h2 : ScalarSpectralMeasures.sqNormLIntegral
        (ScalarSpectralMeasures.spectralMeasure S x) f = 0 := by
      rw [← h1]
      simp
    have h3 := (lintegral_eq_zero_iff ((hf.enorm).pow_const 2)).mp h2
    have h4 : ScalarSpectralMeasures.spectralMeasure S x Zᶜ = 0 := by
      have h5 : ∀ᵐ p ∂(ScalarSpectralMeasures.spectralMeasure S x), p ∈ Z :=
        h3.mono fun p hp => by simpa [hZdef] using hp
      exact mem_ae_iff.mp h5
    have h6 := jointSpectralMeasure_add_compl_apply h S hZ x
    rw [(jointSpectralMeasure_apply_eq_zero_iff h S hZ.compl x).mpr h4, add_zero] at h6
    exact ⟨x, (congrFun hP x).trans h6⟩
private lemma orthProj_nullSet_of_continuous (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {f : SpectralDomain J → ℂ} (hf : Continuous f)
    (C : H →L[ℂ] H) (hC : ⇑C = spectralIntegral S f) :
    ∃ P : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | f p = 0} ∧
      HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet C) := by
  obtain ⟨P, C', hP, hC', hO⟩ :=
    orthProj_nullSet_spectralIntegral h S f hf.measurable (isBoundedFn_of_continuous hf)
  obtain rfl : C' = C := DFunLike.coe_injective (hC'.trans hC.symm)
  exact ⟨P, hP, hO⟩
private lemma orthProj_nullSet_one_sub (h : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily H J) {g : SpectralDomain J → ℂ} (hg : Continuous g)
    (D : H →L[ℂ] H) (hD : ⇑D = spectralIntegral S g) :
    ∃ P : H →L[ℂ] H, ⇑P = jointSpectralMeasure S {p | g p = 1} ∧
      HilbertSpaceBasics.IsOrthProjOnto P (LatticeBasics.nullSet (1 - D)) := by
  have h1 : Continuous (1 - g) := continuous_const.sub hg
  have hone : Measurable (1 : SpectralDomain J → ℂ) := measurable_one
  have hboundedOne : BorelCalculus.IsBoundedFn (1 : SpectralDomain J → ℂ) :=
    isBoundedFn_of_continuous continuous_const
  have hC : ⇑(1 - D) = spectralIntegral S (1 - g) := by
    funext x
    have h2 := (spectralIntegral_sub_apply h S hone hg.measurable
      (mem_integralDomain_of_bounded h S hone hboundedOne x)
      (mem_integralDomain_of_bounded h S hg.measurable (isBoundedFn_of_continuous hg) x)).2
    rw [h2, spectralIntegral_one_apply h S x, ← hD]
    rfl
  obtain ⟨P, hP, hO⟩ := orthProj_nullSet_of_continuous h S h1 (1 - D) hC
  refine ⟨P, ?_, hO⟩
  rw [hP]
  congr 1
  ext p
  simp only [mem_ofPred_eq, Pi.sub_apply, Pi.one_apply, sub_eq_zero]
  exact eq_comm
private lemma tendstoStrongly_spectralIntegral (h : BorelCalculus.BorelCalculusStatement)
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement) (S : CommutingFamily H J)
    (F : ℕ → SpectralDomain J → ℂ) (f : SpectralDomain J → ℂ)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f) (hb : ∃ M : ℝ, ∀ n p, ‖F n p‖ ≤ M)
    (hlim : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 (f p))) :
    ∃ (C : ℕ → H →L[ℂ] H) (D : H →L[ℂ] H), (∀ n, ⇑(C n) = spectralIntegral S (F n)) ∧
      ⇑D = spectralIntegral S f ∧ HilbertSpaceBasics.TendstoStrongly C atTop D := by
  obtain ⟨M, hM⟩ := hb
  have hlimb : ∀ p, ‖f p‖ ≤ M := by
    intro p
    refine le_of_tendsto (hlim p).norm ?_
    exact Eventually.of_forall fun n => hM n p
  obtain ⟨D, hD⟩ := exists_clm_eq_spectralIntegral (H := H) h S hf ⟨M, hlimb⟩
  have hCex : ∀ n, ∃ Cn : H →L[ℂ] H, ⇑Cn = spectralIntegral S (F n) := fun n =>
    exists_clm_eq_spectralIntegral (H := H) h S (hF n) ⟨M, hM n⟩
  choose C hC using hCex
  refine ⟨C, D, hC, hD, (LatticeBasics.tendstoStrongly_iff C D).mpr fun x => ?_⟩
  have := isFiniteMeasure_spectralMeasure hm S x
  have hdiff : ∀ n, ‖C n x - D x‖ₑ ^ 2 =
      ScalarSpectralMeasures.sqNormLIntegral (ScalarSpectralMeasures.spectralMeasure S x)
        (F n - f) := by
    intro n
    have hsub := spectralIntegral_sub_apply h S (hF n) hf
      (mem_integralDomain_of_bounded h S (hF n) ⟨M, hM n⟩ x)
      (mem_integralDomain_of_bounded h S hf ⟨M, hlimb⟩ x)
    rw [hC, hD, ← hsub.2]
    exact enorm_sq_spectralIntegral h S ((hF n).sub hf) hsub.1
  have hdom : ∀ n p, ‖(F n - f) p‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * M) ^ 2 := by
    intro n p
    gcongr
    rw [Pi.sub_apply, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖F n p - f p‖ ≤ ‖F n p‖ + ‖f p‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM n p) (hlimb p)
      _ = 2 * M := by ring
  have hpt : ∀ p, Tendsto (fun n => ‖(F n - f) p‖ₑ ^ 2) atTop (𝓝 0) := by
    intro p
    have hz : Tendsto (fun n => F n p - f p) atTop (𝓝 0) := by
      simpa using (hlim p).sub_const (f p)
    have hcont : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 :=
      (ENNReal.continuous_pow 2).comp continuous_enorm
    have hcomp : Tendsto (fun n => ‖F n p - f p‖ₑ ^ 2) atTop (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
      (hcont.tendsto 0).comp hz
    rw [enorm_zero, zero_pow two_ne_zero] at hcomp
    exact hcomp
  have hfiniteBound :
      ∫⁻ _p, ENNReal.ofReal (2 * M) ^ 2 ∂(ScalarSpectralMeasures.spectralMeasure S x) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hint0 : Tendsto (fun n => ScalarSpectralMeasures.sqNormLIntegral
      (ScalarSpectralMeasures.spectralMeasure S x) (F n - f)) atTop (𝓝 0) := by
    have hlt := tendsto_lintegral_of_dominated_convergence
      (μ := ScalarSpectralMeasures.spectralMeasure S x) (fun _ => ENNReal.ofReal (2 * M) ^ 2)
      (fun n => ((hF n).sub hf).enorm.pow_const 2) (fun n => ae_of_all _ (hdom n))
      hfiniteBound (ae_of_all _ hpt)
    rw [lintegral_zero] at hlt
    exact hlt
  have hsqn : Tendsto (fun n => ‖C n x - D x‖ₑ ^ 2) atTop (𝓝 0) := by
    simpa only [hdiff] using hint0
  have hreal : Tendsto (fun n => ‖C n x - D x‖ ^ 2) atTop (𝓝 0) := by
    have hto := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsqn
    simpa [Function.comp_def, ENNReal.toReal_pow] using hto
  have hroot := hreal.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using hroot
end Calculus
section Transport
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {V : H →ₗ[ℂ] H'}
private lemma map_unitary_mul_apply {u v : unitary (H →L[ℂ] H)} {u' v' : unitary (H' →L[ℂ] H')}
    (hu : ∀ x, V ((u : H →L[ℂ] H) x) = (u' : H' →L[ℂ] H') (V x))
    (hv : ∀ x, V ((v : H →L[ℂ] H) x) = (v' : H' →L[ℂ] H') (V x)) (x : H) :
    V (((u * v : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) =
      ((u' * v' : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H') (V x) := by
  change V ((u : H →L[ℂ] H) ((v : H →L[ℂ] H) x)) =
    (u' : H' →L[ℂ] H') ((v' : H' →L[ℂ] H') (V x))
  rw [hu, hv]
private lemma map_unitary_inv_apply {u : unitary (H →L[ℂ] H)} {u' : unitary (H' →L[ℂ] H')}
    (hu : ∀ x, V ((u : H →L[ℂ] H) x) = (u' : H' →L[ℂ] H') (V x)) (x : H) :
    V (((u⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) =
      ((u'⁻¹ : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H') (V x) := by
  have h1 : (u : H →L[ℂ] H) (((u⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) = x :=
    congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H) x) (mul_inv_cancel u)
  have h2 : ∀ y : H', ((u'⁻¹ : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H')
      ((u' : H' →L[ℂ] H') y) = y := fun y =>
    congrArg (fun w : unitary (H' →L[ℂ] H') => (w : H' →L[ℂ] H') y) (inv_mul_cancel u')
  rw [← h2 (V (((u⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x)), ← hu, h1]
private lemma map_unitary_pow_apply {u : unitary (H →L[ℂ] H)} {u' : unitary (H' →L[ℂ] H')}
    (hu : ∀ x, V ((u : H →L[ℂ] H) x) = (u' : H' →L[ℂ] H') (V x)) (n : ℕ) (x : H) :
    V (((u ^ n : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) =
      ((u' ^ n : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H') (V x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact map_unitary_mul_apply ih hu x
private lemma map_unitary_zpow_apply {u : unitary (H →L[ℂ] H)} {u' : unitary (H' →L[ℂ] H')}
    (hu : ∀ x, V ((u : H →L[ℂ] H) x) = (u' : H' →L[ℂ] H') (V x)) (z : ℤ) (x : H) :
    V (((u ^ z : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) =
      ((u' ^ z : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H') (V x) := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast]
    exact map_unitary_pow_apply hu n x
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact map_unitary_inv_apply (map_unitary_pow_apply hu n) x
private lemma map_noncommProd_apply {J : Type} (g : J → unitary (H →L[ℂ] H))
    (g' : J → unitary (H' →L[ℂ] H'))
    (hg : ∀ i x, V ((g i : H →L[ℂ] H) x) = (g' i : H' →L[ℂ] H') (V x))
    (s : Finset J) (comm) (comm') (x : H) :
    V (((s.noncommProd g comm : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) =
      ((s.noncommProd g' comm' : unitary (H' →L[ℂ] H')) : H' →L[ℂ] H') (V x) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem s a g comm ha,
      Finset.noncommProd_insert_of_notMem s a g' comm' ha]
    exact map_unitary_mul_apply (hg a) (fun y => ih _ _ y) x
variable {J : Type} [Fintype J] [Nonempty J] {S : CommutingFamily H J} {S' : CommutingFamily H' J}
private lemma map_unitaryMonomial_apply
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    (y : J → ℤ) (x : H) : V (S.unitaryMonomial y x) = S'.unitaryMonomial y (V x) :=
  map_noncommProd_apply _ _ (fun i => map_unitary_zpow_apply (hB i) (y i)) Finset.univ _ _ x
private lemma map_familyMonomial_apply (hA : ∀ x, V (S.A x) = S'.A (V x))
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    (n : ℕ) (y : J → ℤ) (x : H) :
    V (familyMonomial S n y x) = familyMonomial S' n y (V x) := by
  have hpow : ∀ (n : ℕ) (z : H), V ((S.A ^ n) z) = (S'.A ^ n) (V z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ]
      change V ((S.A ^ n) (S.A z)) = (S'.A ^ n) (S'.A (V z))
      rw [ih, hA]
  change V ((S.A ^ n) (S.unitaryMonomial y x)) = (S'.A ^ n) (S'.unitaryMonomial y (V x))
  rw [hpow, map_unitaryMonomial_apply hB]
private lemma map_polynomialCalculus_apply (hA : ∀ x, V (S.A x) = S'.A (V x))
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    (q : SpectralDomain J → ℂ) (x : H) :
    V (polynomialCalculus S q x) = polynomialCalculus S' q (V x) := by
  unfold polynomialCalculus
  simp only [familySum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [map_familyMonomial_apply hA hB]
private lemma spectralMeasure_map (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (hV : LatticeBasics.IsIsometricMap V) (hA : ∀ x, V (S.A x) = S'.A (V x))
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    (x : H) :
    ScalarSpectralMeasures.spectralMeasure S' (V x) = ScalarSpectralMeasures.spectralMeasure S x := by
  have hs := ((hm H J S).2.2.2.1 x).1
  refine (((hm H' J S').2.2.2.1 (V x)).2.1 _ ⟨hs.1, fun n y => ?_⟩).symm
  rw [← map_familyMonomial_apply hA hB, hV.inner_map_map]
  exact hs.2 n y
private lemma mem_integralDomain_map_iff
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (hV : LatticeBasics.IsIsometricMap V) (hA : ∀ x, V (S.A x) = S'.A (V x))
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    (f : SpectralDomain J → ℂ) (x : H) : x ∈ integralDomain S f ↔ V x ∈ integralDomain S' f := by
  simp only [integralDomain, mem_ofPred_eq, spectralMeasure_map hm hV hA hB x]
private lemma spectralIntegral_map_apply
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (hV : LatticeBasics.IsIsometricMap V) (hA : ∀ x, V (S.A x) = S'.A (V x))
    (hB : ∀ (i : J) (x : H), V ((S.B i : H →L[ℂ] H) x) = (S'.B i : H' →L[ℂ] H') (V x))
    {f : SpectralDomain J → ℂ} (hf : Measurable f) {x : H} (hx : x ∈ integralDomain S f) :
    spectralIntegral S' f (V x) = V (spectralIntegral S f x) := by
  have hx' : V x ∈ integralDomain S' f := (mem_integralDomain_map_iff hm hV hA hB f x).mp hx
  obtain ⟨hl, -, ⟨q, hq⟩, -⟩ := (hm H J S).2.2.2.2.2.2.2 x f hf hx
  obtain ⟨hl', -⟩ := (hm H' J S').2.2.2.2.2.2.2 (V x) f hf hx'
  have hq' : ScalarSpectralMeasures.PolynomialL2Approximation S' (V x) f q :=
    ⟨hq.1, by rw [spectralMeasure_map hm hV hA hB x]; exact hq.2⟩
  have t1 := hl q hq
  have t2 := hl' q hq'
  have t3 : Tendsto (fun l => V (polynomialCalculus S (q l) x)) atTop
      (𝓝 (V (ScalarSpectralMeasures.l2Calculus S x f))) :=
    ((⟨V, hV⟩ : H →ₗᵢ[ℂ] H').continuous.tendsto _).comp t1
  unfold SpectralIntegral.spectralIntegral
  rw [if_pos hx, if_pos hx']
  exact tendsto_nhds_unique t2 (t3.congr fun l => map_polynomialCalculus_apply hA hB (q l) x)
end Transport
theorem calculusApplicationsStatement_of_borelCalculus
    (h : BorelCalculus.BorelCalculusStatement)
    (hm : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement) :
    CalculusApplicationsStatement := by
  intro H _ _ _ J _ _ S
  have hbt : Continuous (fun p : SpectralDomain J => (((p.1 : ℝ)) : ℂ)) := by fun_prop
  have hz : ∀ i : J, Continuous (fun p : SpectralDomain J => ((p.2 i : Circle) : ℂ)) := by
    intro i
    fun_prop
  refine ⟨nonneg_iff_spectralIntegral h hm S, orthProj_nullSet_spectralIntegral h S, ?_, ?_, ?_,
    tendstoStrongly_spectralIntegral h hm S, ?_⟩
  · obtain ⟨P, hP, hO⟩ := orthProj_nullSet_of_continuous h S hbt S.A (spectralIntegral_coord h S).symm
    refine ⟨P, ?_, hO⟩
    rw [hP]
    congr 1
    ext p
    simp
  · obtain ⟨P, hP, hO⟩ := orthProj_nullSet_one_sub h S hbt S.A (spectralIntegral_coord h S).symm
    refine ⟨P, ?_, hO⟩
    rw [hP]
    congr 1
    ext p
    simp only [mem_ofPred_eq]
    exact Complex.ofReal_eq_one
  · intro i
    obtain ⟨P, hP, hO⟩ :=
      orthProj_nullSet_one_sub h S (hz i) _ (spectralIntegral_circleCoord h S i).symm
    refine ⟨P, ?_, hO⟩
    rw [hP]
    congr 1
    ext p
    simp only [mem_ofPred_eq]
    exact Circle.coe_eq_one
  · intro H' _ _ _ S' V hV hA hB
    have hE : ∀ Δ : Set (SpectralDomain J), MeasurableSet Δ → ∀ x,
        jointSpectralMeasure S' Δ (V x) = V (jointSpectralMeasure S Δ x) := fun Δ hΔ x =>
      spectralIntegral_map_apply hm hV hA hB (measurable_indicator_one hΔ)
        (mem_integralDomain_of_bounded h S (measurable_indicator_one hΔ)
          (isBoundedFn_indicator_one Δ) x)
    refine ⟨spectralMeasure_map hm hV hA hB, fun f hf x =>
      ⟨mem_integralDomain_map_iff hm hV hA hB f x,
        fun hx => spectralIntegral_map_apply hm hV hA hB hf hx⟩, hE,
      fun hU Δ hΔ => ?_⟩
    set e := LinearIsometryEquiv.ofSurjective (⟨V, hU.1⟩ : H →ₗᵢ[ℂ] H') hU.2 with he
    have hVe : ∀ y : H', V (e.symm y) = y := fun y => e.apply_symm_apply y
    have h1 : jointSpectralMeasure S' Δ = V ∘ jointSpectralMeasure S Δ ∘ e.symm := by
      funext y
      change jointSpectralMeasure S' Δ y = V (jointSpectralMeasure S Δ (e.symm y))
      rw [← hE Δ hΔ, hVe]
    refine ⟨h1, ?_, ?_⟩
    · intro h0
      funext x
      have h2 : V (jointSpectralMeasure S Δ x) = 0 := by
        rw [← hE Δ hΔ, h0]
        rfl
      have h3 := hU.1 (jointSpectralMeasure S Δ x)
      rw [h2, norm_zero] at h3
      exact norm_eq_zero.mp h3.symm
    · intro h0
      rw [h1, h0]
      funext y
      simp
end JointSpectrum.CalculusApplications
end YangMills.Construction
