import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAreReflectionPositiveOnHalfSpaces
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStatesProof
import YangMills.Construction.Sequences.LogConvexSequenceBounds
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.InfiniteLattice.ReflectionPairingProof
variable {a : ℝ}
theorem isRegionMeasurable_mono {S S' : Set AmbientSpace} (hSS' : S ⊆ S')
    {F : GaugeField a → ℂ} (hF : IsRegionMeasurable S F) : IsRegionMeasurable S' F := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
theorem isBoundedObservable_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (fun W => F W * G W) := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
theorem isBoundedObservable_conj {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (fun W => conj (F W)) := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.isBoundedObservable_conj <;> assumption
theorem isBoundedObservable_actOn (g : LatticeSymmetry a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (g.actOn F) := by apply _root_.YangMills.Construction.InfiniteLattice.LiftedGibbsStates.isBoundedObservable_actOn <;> assumption
theorem isRegionMeasurable_actOn (g : LatticeSymmetry a) {S : Set AmbientSpace}
    {F : GaugeField a → ℂ} (hF : IsRegionMeasurable S F) :
    IsRegionMeasurable (g.toFun '' S) (g.actOn F) := by
  have hmeas : @Measurable _ _ (regionSigma (g.toFun '' S)) (regionSigma S) g.pullbackField := by
    refine measurable_iff_comap_le.mpr ?_
    simp only [MeasurableSpace.comap_iSup]
    refine iSup₂_le fun l hl => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le (f := fun (e : Link a) (_ : e ∈ linksWithin (g.toFun '' S)) =>
      MeasurableSpace.comap (fun W : GaugeField a => W e) inferInstance) (g.linkMap l)
      ⟨⟨_, hl.1, rfl⟩, ⟨_, hl.2, rfl⟩⟩ le_rfl
  have hF' : Measurable[regionSigma S] F := hF
  exact hF'.comp hmeas
theorem isBounded_image_shift (v : LatticePoint a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded ((shift v).toFun '' S) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS
  refine isBounded_iff_forall_norm_le.mpr ⟨R + ‖(v : AmbientSpace)‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (norm_add_le _ _).trans (add_le_add (hR x hx) le_rfl)
theorem timeReflect_timeAxis (t : halfSpacingTimes a) (x : AmbientSpace) :
    (timeReflect t).toFun x timeAxis = 2 * (t : ℝ) - x timeAxis := by
  rw [timeReflect_apply]
  simp
  ring
theorem isBounded_image_timeReflect (t : halfSpacingTimes a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded ((timeReflect t).toFun '' S) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS
  refine isBounded_iff_forall_norm_le.mpr
    ⟨R + (2 * (R + |(t : ℝ)|)) * ‖(Pi.single timeAxis 1 : AmbientSpace)‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [timeReflect_apply]
  refine (norm_sub_le _ _).trans (add_le_add (hR x hx) ?_)
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1 : |x timeAxis| ≤ ‖x‖ := norm_le_pi_norm x timeAxis
  have h2 : |x timeAxis - (t : ℝ)| ≤ |x timeAxis| + |(t : ℝ)| := abs_sub _ _
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  have := hR x hx
  linarith
theorem exists_common_region {t : halfSpacingTimes a} {F G : GaugeField a → ℂ}
    (hF : F ∈ upperAlgebra t) (hG : G ∈ upperAlgebra t) :
    ∃ S : Set AmbientSpace, S ⊆ halfSpaceAbove t ∧ Bornology.IsBounded S ∧
      Measurable[regionSigma S] F ∧ Measurable[regionSigma S] G := by
  obtain ⟨-, S, hS, hb, hm⟩ := hF
  obtain ⟨-, S', hS', hb', hm'⟩ := hG
  exact ⟨S ∪ S', Set.union_subset hS hS', hb.union hb',
    isRegionMeasurable_mono Set.subset_union_left hm,
    isRegionMeasurable_mono Set.subset_union_right hm'⟩
theorem upperAlgebra_isConjClosedSubalgebra (t : halfSpacingTimes a) :
    IsConjClosedSubalgebra t := by
  refine ⟨fun c => ?_, fun F hF G hG => ?_, fun c F hF => ?_, fun F hF G hG => ?_,
    fun F hF => ?_⟩
  · exact ⟨⟨measurable_const, ‖c‖, fun _ => le_rfl⟩, ∅, Set.empty_subset _,
      Bornology.isBounded_empty, measurable_const⟩
  · obtain ⟨S, hS, hb, h₁, h₂⟩ := exists_common_region hF hG
    obtain ⟨⟨mF, K, hK⟩, -⟩ := hF
    obtain ⟨⟨mG, K', hK'⟩, -⟩ := hG
    exact ⟨⟨mF.add mG, K + K', fun W => (norm_add_le _ _).trans (add_le_add (hK W) (hK' W))⟩,
      S, hS, hb, h₁.add h₂⟩
  · obtain ⟨⟨mF, K, hK⟩, S, hS, hb, h⟩ := hF
    refine ⟨⟨mF.const_smul c, ‖c‖ * K, fun W => ?_⟩, S, hS, hb, h.const_smul c⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hK W) (norm_nonneg _)
  · obtain ⟨S, hS, hb, h₁, h₂⟩ := exists_common_region hF hG
    exact ⟨isBoundedObservable_mul hF.1 hG.1, S, hS, hb, h₁.mul h₂⟩
  · obtain ⟨hO, S, hS, hb, h⟩ := hF
    exact ⟨isBoundedObservable_conj hO, S, hS, hb, Complex.continuous_conj.measurable.comp h⟩
section Pairing
variable {μ : Measure (GaugeField a)} [IsProbabilityMeasure μ]
theorem integrable_of_isBoundedObservable {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    Integrable F μ := by
  obtain ⟨mF, K, hK⟩ := hF
  exact Integrable.of_bound mF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
theorem isBoundedObservable_pairingIntegrand (t : halfSpacingTimes a) {G F : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hF : IsBoundedObservable F) :
    IsBoundedObservable (fun W => conj ((timeReflect t).actOn G W) * F W) :=
  isBoundedObservable_mul (isBoundedObservable_conj (isBoundedObservable_actOn _ hG)) hF
theorem reflectionPairing_linear_right (t : halfSpacingTimes a) {G F F' : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hF : IsBoundedObservable F) (hF' : IsBoundedObservable F')
    (c c' : ℂ) :
    reflectionPairing μ t G (c • F + c' • F') =
      c * reflectionPairing μ t G F + c' * reflectionPairing μ t G F' := by
  have h₁ : Integrable (fun W => conj ((timeReflect t).actOn G W) * F W) μ :=
    integrable_of_isBoundedObservable (isBoundedObservable_pairingIntegrand t hG hF)
  have h₂ : Integrable (fun W => conj ((timeReflect t).actOn G W) * F' W) μ :=
    integrable_of_isBoundedObservable (isBoundedObservable_pairingIntegrand t hG hF')
  have hfun : (fun W => conj ((timeReflect t).actOn G W) * (c • F + c' • F') W) =
      fun W => c * (conj ((timeReflect t).actOn G W) * F W) +
        c' * (conj ((timeReflect t).actOn G W) * F' W) := by
    funext W
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [reflectionPairing]
  rw [hfun, integral_add (h₁.const_mul c) (h₂.const_mul c'), integral_const_mul,
    integral_const_mul]
theorem reflectionPairing_antilinear_left (t : halfSpacingTimes a) {G G' F : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hG' : IsBoundedObservable G') (hF : IsBoundedObservable F)
    (c c' : ℂ) :
    reflectionPairing μ t (c • G + c' • G') F =
      conj c * reflectionPairing μ t G F + conj c' * reflectionPairing μ t G' F := by
  have h₁ : Integrable (fun W => conj ((timeReflect t).actOn G W) * F W) μ :=
    integrable_of_isBoundedObservable (isBoundedObservable_pairingIntegrand t hG hF)
  have h₂ : Integrable (fun W => conj ((timeReflect t).actOn G' W) * F W) μ :=
    integrable_of_isBoundedObservable (isBoundedObservable_pairingIntegrand t hG' hF)
  have hfun : (fun W => conj ((timeReflect t).actOn (c • G + c' • G') W) * F W) =
      fun W => conj c * (conj ((timeReflect t).actOn G W) * F W) +
        conj c' * (conj ((timeReflect t).actOn G' W) * F W) := by
    funext W
    simp only [LatticeSymmetry.actOn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add,
      map_mul]
    ring
  simp only [reflectionPairing]
  rw [hfun, integral_add (h₁.const_mul _) (h₂.const_mul _), integral_const_mul,
    integral_const_mul]
omit [IsProbabilityMeasure μ] in
theorem conj_reflectionPairing (t : halfSpacingTimes a)
    (hsym : IsSymmetricUnder μ (timeReflect t))
    (hinv : ∀ X : GaugeField a → ℂ, IsBoundedObservable X →
      (timeReflect t).actOn ((timeReflect t).actOn X) = X)
    {G F : GaugeField a → ℂ} (hG : IsBoundedObservable G) (hF : IsBoundedObservable F) :
    conj (reflectionPairing μ t G F) = reflectionPairing μ t F G := by
  have hX : IsBoundedObservable (fun W => (timeReflect t).actOn G W * conj (F W)) :=
    isBoundedObservable_mul (isBoundedObservable_actOn _ hG) (isBoundedObservable_conj hF)
  have h := hsym _ hX
  have hfun : (timeReflect t).actOn
      (fun W => (timeReflect t).actOn G W * conj (F W)) =
      fun W => conj ((timeReflect t).actOn F W) * G W := by
    funext W
    have hG' := congrFun (hinv G hG) W
    simp only [LatticeSymmetry.actOn] at hG' ⊢
    rw [hG', mul_comm]
  rw [hfun] at h
  simp only [reflectionPairing]
  rw [h, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp
omit [IsProbabilityMeasure μ] in
theorem norm_reflectionPairing_sq_le {t : halfSpacingTimes a}
    (hP : ReflectionPairingIsPosHermitian μ t)
    {G F : GaugeField a → ℂ} (hG : G ∈ upperAlgebra t) (hF : F ∈ upperAlgebra t) :
    ‖reflectionPairing μ t G F‖ ^ 2 ≤
      (reflectionPairing μ t G G).re * (reflectionPairing μ t F F).re := by
  obtain ⟨hlin, hanti, hherm, hpos⟩ := hP
  obtain ⟨-, hadd, hsmul, -, -⟩ := upperAlgebra_isConjClosedSubalgebra t
  set z := reflectionPairing μ t G F with hz
  set p := (reflectionPairing μ t G G).re with hp
  set q := (reflectionPairing μ t F F).re with hq
  have hpc : reflectionPairing μ t G G = (p : ℂ) :=
    Complex.ext (by simp [hp]) (by simp [(hpos G hG).1])
  have hqc : reflectionPairing μ t F F = (q : ℂ) :=
    Complex.ext (by simp [hq]) (by simp [(hpos F hF).1])
  have hzc : reflectionPairing μ t F G = conj z := (hherm G hG F hF).symm
  set N := ‖z‖ ^ 2 with hN
  have hW : conj z * z = (N : ℂ) := by
    rw [hN, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hquad : ∀ s : ℝ, 0 ≤ (N * p) * (s * s) + (-2 * N) * s + q := by
    intro s
    set c : ℂ := -(s : ℂ) * z with hc
    have hv : c • G + (1 : ℂ) • F ∈ upperAlgebra t :=
      hadd _ (hsmul c G hG) _ (hsmul 1 F hF)
    have hexp : reflectionPairing μ t (c • G + (1 : ℂ) • F) (c • G + (1 : ℂ) • F) =
        (((N * p) * (s * s) + (-2 * N) * s + q : ℝ) : ℂ) := by
      rw [hanti G hG F hF _ hv c 1, hlin G hG G hG F hF c 1, hlin F hF G hG F hF c 1, hpc, hqc,
        hzc, ← hz, hc]
      simp only [map_mul, map_neg, Complex.conj_ofReal, map_one]
      push_cast
      linear_combination ((s : ℂ) ^ 2 * (p : ℂ) - 2 * (s : ℂ)) * hW
    have := (hpos _ hv).2
    rw [hexp, Complex.ofReal_re] at this
    exact this
  have hdisc := discrim_le_zero hquad
  have hNnn : 0 ≤ N := sq_nonneg _
  have hpnn : 0 ≤ p := (hpos G hG).2
  have hqnn : 0 ≤ q := (hpos F hF).2
  rcases hNnn.eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hpnn hqnn
  · simp only [discrim] at hdisc
    have : N * (N - p * q) ≤ 0 := by nlinarith
    have h2 : N - p * q ≤ 0 := by
      by_contra hc
      have := mul_pos h0 (not_le.mp hc)
      linarith
    linarith
theorem reflectionSeminorm_le_supNorm (t : halfSpacingTimes a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : reflectionPairingRoot μ t F ≤ observableSupNorm F := by
  obtain ⟨-, K, hK⟩ := hF
  have hbdd : BddAbove (Set.range fun W => ‖F W‖) := ⟨K, by rintro _ ⟨W, rfl⟩; exact hK W⟩
  have hle : ∀ W, ‖F W‖ ≤ observableSupNorm F := fun W => le_ciSup hbdd W
  have hM : 0 ≤ observableSupNorm F := Real.iSup_nonneg fun _ => norm_nonneg _
  refine Real.sqrt_le_iff.mpr ⟨hM, ?_⟩
  refine (Complex.re_le_norm _).trans ?_
  have hb : ∀ W, ‖conj ((timeReflect t).actOn F W) * F W‖ ≤ observableSupNorm F ^ 2 := by
    intro W
    rw [norm_mul, RCLike.norm_conj, sq]
    exact mul_le_mul (hle _) (hle _) (norm_nonneg _) hM
  have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
  simpa [reflectionPairing] using this
theorem reflectionSeminorm_one (t : halfSpacingTimes a) :
    reflectionPairingRoot μ t (fun _ => 1) = 1 := by
  simp [reflectionPairingRoot, reflectionPairing, LatticeSymmetry.actOn]
end Pairing
theorem positiveMultiples_pos (ha : 0 < a) (u : positiveMultiples a) : 0 < (u : ℝ) := by
  obtain ⟨n, hn, h⟩ := u.2
  rw [h]
  exact mul_pos (by exact_mod_cast hn) ha
theorem isSlabLocalized_reflectedInsert {t : halfSpacingTimes a} {u : positiveMultiples a}
    {E : GaugeField a → ℂ} (hE : IsSlabLocalized t u E) :
    IsSlabLocalized t u (reflectedInsert t u E) := by
  obtain ⟨hO, S, hS, hb, hm⟩ := hE
  refine ⟨isBoundedObservable_conj (isBoundedObservable_actOn _ hO),
    (timeReflect (midpointTime t u)).toFun '' S, ?_, isBounded_image_timeReflect _ hb,
    Complex.continuous_conj.measurable.comp (isRegionMeasurable_actOn _ hm)⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨h₁, h₂⟩ : (t : ℝ) < x timeAxis ∧ x timeAxis < (t : ℝ) + u := hS hx
  have hmid : ((midpointTime t u : halfSpacingTimes a) : ℝ) = (t : ℝ) + (u : ℝ) / 2 := rfl
  show (t : ℝ) < _ ∧ _ < (t : ℝ) + u
  rw [timeReflect_timeAxis, hmid]
  constructor <;> linarith
theorem reflectedInsert_involutive {t : halfSpacingTimes a} {u : positiveMultiples a}
    (hinv : ∀ X : GaugeField a → ℂ, IsBoundedObservable X →
      (timeReflect (midpointTime t u)).actOn
        ((timeReflect (midpointTime t u)).actOn X) = X)
    {E : GaugeField a → ℂ} (hE : IsBoundedObservable E) :
    reflectedInsert t u (reflectedInsert t u E) = E := by
  funext W
  have h := congrFun (hinv E hE) W
  simpa [reflectedInsert, LatticeSymmetry.actOn] using h
theorem insertMul_mem_upperAlgebra (ha : 0 < a) {t : halfSpacingTimes a}
    {u : positiveMultiples a} {E F : GaugeField a → ℂ} (hE : IsSlabLocalized t u E)
    (hF : F ∈ upperAlgebra t) : insertMul u E F ∈ upperAlgebra t := by
  obtain ⟨hEo, S, hS, hb, hm⟩ := hE
  obtain ⟨hFo, SF, hSF, hbF, hmF⟩ := hF
  refine ⟨isBoundedObservable_mul hEo (isBoundedObservable_actOn _ hFo),
    S ∪ (shift (timeStep u)).toFun '' SF, ?_,
    hb.union (isBounded_image_shift _ hbF),
    Measurable.mul (isRegionMeasurable_mono Set.subset_union_left hm)
      (isRegionMeasurable_mono Set.subset_union_right (isRegionMeasurable_actOn _ hmF))⟩
  refine Set.union_subset (fun x hx => (hS hx).1) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h₁ : (t : ℝ) < x timeAxis := hSF hx
  have h₂ := positiveMultiples_pos ha u
  have h₃ : ((shift (timeStep u)).toFun x) timeAxis = x timeAxis + (u : ℝ) := by
    simp [shift, timeStep]
  show (t : ℝ) < _
  rw [h₃]
  linarith
theorem insertMul_linear (u : positiveMultiples a) (E F F' : GaugeField a → ℂ)
    (c c' : ℂ) : insertMul u E (c • F + c' • F') =
      c • insertMul u E F + c' • insertMul u E F' := by
  funext W
  simp only [insertMul, LatticeSymmetry.actOn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem integral_reflection_chain {μ : Measure (GaugeField a)} (ϑ θ τ : LatticeSymmetry a)
    (hϑ : IsSymmetricUnder μ ϑ) (hθ : IsSymmetricUnder μ θ)
    (hinv : ∀ X : GaugeField a → ℂ, IsBoundedObservable X → θ.actOn (θ.actOn X) = X)
    (h₁ : ∀ X : GaugeField a → ℂ, IsBoundedObservable X →
      ϑ.actOn (θ.actOn X) = τ.actOn X)
    (h₂ : ∀ X : GaugeField a → ℂ, IsBoundedObservable X →
      ϑ.actOn (τ.actOn X) = θ.actOn X)
    {E F G : GaugeField a → ℂ} (hE : IsBoundedObservable E) (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) :
    ∫ W, conj (θ.actOn G W) * (E W * τ.actOn F W) ∂μ =
      ∫ W, conj (θ.actOn
        (fun V => conj (ϑ.actOn E V) * τ.actOn G V) W) * F W ∂μ := by
  have hX : IsBoundedObservable (fun W => conj (θ.actOn G W) * (E W * τ.actOn F W)) :=
    isBoundedObservable_mul (isBoundedObservable_conj (isBoundedObservable_actOn _ hG))
      (isBoundedObservable_mul hE (isBoundedObservable_actOn _ hF))
  have hYfun : ϑ.actOn
      (fun W => conj (θ.actOn G W) * (E W * τ.actOn F W)) =
      fun W => conj (τ.actOn G W) * (ϑ.actOn E W * θ.actOn F W) := by
    funext W
    have e₁ := congrFun (h₁ G hG) W
    have e₂ := congrFun (h₂ F hF) W
    simp only [LatticeSymmetry.actOn] at e₁ e₂ ⊢
    rw [e₁, e₂]
  have hY : IsBoundedObservable
      (fun W => conj (τ.actOn G W) * (ϑ.actOn E W * θ.actOn F W)) := by
    rw [← hYfun]
    exact isBoundedObservable_actOn _ hX
  have hZfun : θ.actOn
      (fun W => conj (τ.actOn G W) * (ϑ.actOn E W * θ.actOn F W)) =
      fun W => conj (θ.actOn
        (fun V => conj (ϑ.actOn E V) * τ.actOn G V) W) * F W := by
    funext W
    have e₃ := congrFun (hinv F hF) W
    simp only [LatticeSymmetry.actOn, map_mul, Complex.conj_conj] at e₃ ⊢
    rw [e₃]
    ring
  rw [← hϑ _ hX, hYfun, ← hθ _ hY, hZfun]
section Moments
variable {μ : Measure (GaugeField a)} {t : halfSpacingTimes a} {u : positiveMultiples a}
  {E F : GaugeField a → ℂ}
theorem insertedTransfer_mem (hT : InsertMulAdjoint μ t u E)
    {G : GaugeField a → ℂ} (hG : G ∈ upperAlgebra t) :
    insertedTransfer t u E G ∈ upperAlgebra t :=
  hT.2.2.2.1.1 _ (hT.2.2.1.1 _ hG)
theorem iterate_insertedTransfer_mem (hT : InsertMulAdjoint μ t u E) (n : ℕ)
    {G : GaugeField a → ℂ} (hG : G ∈ upperAlgebra t) :
    (insertedTransfer t u E)^[n] G ∈ upperAlgebra t := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact insertedTransfer_mem hT ih
theorem reflectionPairing_insertedTransfer_right (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E))
    {G H : GaugeField a → ℂ} (hG : G ∈ upperAlgebra t) (hH : H ∈ upperAlgebra t) :
    reflectionPairing μ t G (insertedTransfer t u E H) =
      reflectionPairing μ t (insertMul u E G) (insertMul u E H) := by
  have h := hR.2.2.2.2 _ (hT.2.2.1.1 _ hH) G hG
  rw [hT.2.1] at h
  exact h
theorem reflectionPairing_insertedTransfer_left (hT : InsertMulAdjoint μ t u E)
    {G H : GaugeField a → ℂ} (hG : G ∈ upperAlgebra t) (hH : H ∈ upperAlgebra t) :
    reflectionPairing μ t (insertedTransfer t u E G) H =
      reflectionPairing μ t (insertMul u E G) (insertMul u E H) :=
  (hT.2.2.2.2 _ hH _ (hT.2.2.1.1 _ hG)).symm
theorem reflectionPairing_iterate_symm (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E)) (i : ℕ) :
    ∀ G ∈ upperAlgebra t, ∀ H ∈ upperAlgebra t,
      reflectionPairing μ t ((insertedTransfer t u E)^[i] G) H =
        reflectionPairing μ t G ((insertedTransfer t u E)^[i] H) := by
  induction i with
  | zero => exact fun _ _ _ _ => rfl
  | succ i ih =>
    intro G hG H hH
    have hHi := iterate_insertedTransfer_mem hT i hH
    rw [Function.iterate_succ_apply, ih _ (insertedTransfer_mem hT hG) H hH,
      Function.iterate_succ_apply', reflectionPairing_insertedTransfer_left hT hG hHi,
      reflectionPairing_insertedTransfer_right hT hR hG hHi]
theorem reflectionMoment_add (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E))
    (hF : F ∈ upperAlgebra t) (i j : ℕ) :
    reflectionMoment μ t u E F (i + j) =
      reflectionPairing μ t ((insertedTransfer t u E)^[i] F) ((insertedTransfer t u E)^[j] F) := by
  rw [reflectionMoment, Function.iterate_add_apply]
  exact (reflectionPairing_iterate_symm hT hR i F hF _ (iterate_insertedTransfer_mem hT j hF)).symm
theorem reflectionMoment_add_one (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E))
    (hF : F ∈ upperAlgebra t) (i j : ℕ) :
    reflectionMoment μ t u E F (i + j + 1) =
      reflectionPairing μ t (insertMul u E ((insertedTransfer t u E)^[i] F))
        (insertMul u E ((insertedTransfer t u E)^[j] F)) := by
  rw [add_assoc, reflectionMoment_add hT hR hF i (j + 1), Function.iterate_succ_apply']
  exact reflectionPairing_insertedTransfer_right hT hR (iterate_insertedTransfer_mem hT i hF)
    (iterate_insertedTransfer_mem hT j hF)
theorem reflectionMoment_nonneg (hP : ReflectionPairingIsPosHermitian μ t)
    (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E))
    (hF : F ∈ upperAlgebra t) (n : ℕ) :
    (reflectionMoment μ t u E F n).im = 0 ∧ 0 ≤ (reflectionMoment μ t u E F n).re := by
  rcases Nat.even_or_odd' n with ⟨i, rfl | rfl⟩
  · rw [two_mul, reflectionMoment_add hT hR hF i i]
    exact hP.2.2.2 _ (iterate_insertedTransfer_mem hT i hF)
  · rw [two_mul, reflectionMoment_add_one hT hR hF i i]
    exact hP.2.2.2 _ (hT.2.2.1.1 _ (iterate_insertedTransfer_mem hT i hF))
theorem re_sq_le_norm_sq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
theorem reflectionMoment_sq_le (hP : ReflectionPairingIsPosHermitian μ t)
    (hT : InsertMulAdjoint μ t u E)
    (hR : InsertMulAdjoint μ t u (reflectedInsert t u E))
    (hF : F ∈ upperAlgebra t) (n : ℕ) (hn : 1 ≤ n) :
    (reflectionMoment μ t u E F n).re ^ 2 ≤
      (reflectionMoment μ t u E F (n - 1)).re * (reflectionMoment μ t u E F (n + 1)).re := by
  rcases Nat.even_or_odd' n with ⟨i, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have e₁ : 2 * (j + 1) - 1 = j + j + 1 := by omega
    have e₂ : 2 * (j + 1) + 1 = j + 1 + (j + 1) + 1 := by omega
    have e₀ : 2 * (j + 1) = j + (j + 1) + 1 := by omega
    rw [e₁, e₂, e₀, reflectionMoment_add_one hT hR hF j (j + 1),
      reflectionMoment_add_one hT hR hF j j, reflectionMoment_add_one hT hR hF (j + 1) (j + 1)]
    exact (re_sq_le_norm_sq _).trans (norm_reflectionPairing_sq_le hP
      (hT.2.2.1.1 _ (iterate_insertedTransfer_mem hT j hF))
      (hT.2.2.1.1 _ (iterate_insertedTransfer_mem hT (j + 1) hF)))
  · have e₁ : 2 * i + 1 - 1 = i + i := by omega
    have e₂ : 2 * i + 1 + 1 = i + 1 + (i + 1) := by omega
    have e₀ : 2 * i + 1 = i + (i + 1) := by omega
    rw [e₁, e₂, e₀, reflectionMoment_add hT hR hF i (i + 1), reflectionMoment_add hT hR hF i i,
      reflectionMoment_add hT hR hF (i + 1) (i + 1)]
    exact (re_sq_le_norm_sq _).trans (norm_reflectionPairing_sq_le hP
      (iterate_insertedTransfer_mem hT i hF) (iterate_insertedTransfer_mem hT (i + 1) hF))
end Moments
theorem shift_actOn_shift (v w : LatticePoint a) (F : GaugeField a → ℂ) :
    (shift v).actOn ((shift w).actOn F) = (shift (v + w)).actOn F := by
  funext W
  simp only [LatticeSymmetry.actOn]
  congr 1
  apply Subtype.ext
  funext l
  have hl : (shift v).linkMap ((shift w).linkMap l) = (shift (v + w)).linkMap l := by
    apply Link.ext
    · apply Subtype.ext
      show ((l.initial : AmbientSpace) + w) + v =
        l.initial + ((v + w : LatticePoint a) : AmbientSpace)
      rw [AddSubgroup.coe_add]
      abel
    · apply Subtype.ext
      show ((l.terminal : AmbientSpace) + w) + v =
        l.terminal + ((v + w : LatticePoint a) : AmbientSpace)
      rw [AddSubgroup.coe_add]
      abel
  show W.1 ((shift v).linkMap ((shift w).linkMap l)) = W.1 ((shift (v + w)).linkMap l)
  rw [hl]
theorem shift_zero_actOn (F : GaugeField a → ℂ) :
    (shift (0 : LatticePoint a)).actOn F = F := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.actOn_shift_zero <;> assumption
theorem iterate_insertedTransfer_eq (t : halfSpacingTimes a) (u : positiveMultiples a)
    (E : GaugeField a → ℂ) (n : ℕ) (F : GaugeField a → ℂ) :
    (insertedTransfer t u E)^[n] F =
      (∏ i ∈ Finset.Icc 1 (2 * n), insertSeq t u E i) *
        (shift ((2 * (n : ℤ)) • timeStep u)).actOn F := by
  induction n generalizing F with
  | zero =>
    simp [shift_zero_actOn]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    have hprod : ∏ i ∈ Finset.Icc 1 (2 * (n + 1)), insertSeq t u E i =
        (∏ i ∈ Finset.Icc 1 (2 * n), insertSeq t u E i) *
          insertSeq t u E (2 * n + 1) * insertSeq t u E (2 * n + 1 + 1) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_Icc_succ_top (by omega),
        Finset.prod_Icc_succ_top (by omega)]
    have e₁ : insertSeq t u E (2 * n + 1) =
        (shift ((2 * (n : ℤ)) • timeStep u)).actOn (reflectedInsert t u E) := by
      have hodd : Odd (2 * n + 1) := ⟨n, rfl⟩
      have hcast : (((2 * n + 1 : ℕ) : ℤ) - 1) = 2 * (n : ℤ) := by
        push_cast
        ring
      rw [insertSeq, if_pos hodd, hcast]
    have e₂ : insertSeq t u E (2 * n + 1 + 1) =
        (shift ((2 * (n : ℤ) + 1) • timeStep u)).actOn E := by
      have heven : ¬ Odd (2 * n + 1 + 1) := by
        rw [Nat.not_odd_iff_even]
        exact ⟨n + 1, by ring⟩
      have hcast : (((2 * n + 1 + 1 : ℕ) : ℤ) - 1) = 2 * (n : ℤ) + 1 := by
        push_cast
        ring
      rw [insertSeq, if_neg heven, hcast]
    have h₁ : (shift ((2 * (n : ℤ)) • timeStep u)).actOn
        ((shift (timeStep u)).actOn E) =
        (shift ((2 * (n : ℤ) + 1) • timeStep u)).actOn E := by
      rw [shift_actOn_shift, add_zsmul, one_zsmul]
    have h₂ : (shift ((2 * (n : ℤ)) • timeStep u)).actOn
        ((shift (timeStep u)).actOn
          ((shift (timeStep u)).actOn F)) =
        (shift ((2 * ((n + 1 : ℕ) : ℤ)) • timeStep u)).actOn F := by
      have hsum : (2 * (n : ℤ)) • timeStep u + timeStep u + timeStep u =
          (2 * ((n + 1 : ℕ) : ℤ)) • timeStep u := by
        push_cast
        rw [show 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 1 + 1 by ring, add_zsmul, add_zsmul, one_zsmul]
      rw [shift_actOn_shift, shift_actOn_shift, hsum]
    have hR : (shift ((2 * (n : ℤ)) • timeStep u)).actOn
        (insertedTransfer t u E F) =
        (shift ((2 * (n : ℤ)) • timeStep u)).actOn (reflectedInsert t u E) *
          (shift ((2 * (n : ℤ) + 1) • timeStep u)).actOn E *
          (shift ((2 * ((n + 1 : ℕ) : ℤ)) • timeStep u)).actOn F := by
      funext W
      have a₁ := congrFun h₁ W
      have a₂ := congrFun h₂ W
      rw [Pi.mul_apply, Pi.mul_apply, ← a₁, ← a₂, mul_assoc]
      rfl
    rw [hprod, e₁, e₂, hR]
    simp only [mul_assoc]
theorem reflectionSeminorm_sq_eq {μ : Measure (GaugeField a)} {t : halfSpacingTimes a}
    {F : GaugeField a → ℂ}
    (h : (reflectionPairing μ t F F).im = 0 ∧ 0 ≤ (reflectionPairing μ t F F).re) :
    ((reflectionPairingRoot μ t F ^ 2 : ℝ) : ℂ) = reflectionPairing μ t F F := by
  rw [reflectionPairingRoot, Real.sq_sqrt h.2]
  exact Complex.ext (by simp) (by simp [h.1])
theorem periodicGibbsReflectionTransfer
    (hPos : MultipleReflections.HalfSpacePositivity.Statement)
    (hSym : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hLog : LogConvexSequence.RatioAndPowerBounds) :
    PeriodicGibbsReflectionTransfer := by
  intro d μ hμ t
  have : IsProbabilityMeasure μ := hμ.1.1
  have ha : 0 < d.mesh := by
    have hL : 0 < (d.L : ℝ) := by
      have h := d.isAdmissible.2
      exact_mod_cast (by omega : 0 < d.L)
    exact zpow_pos hL _
  obtain ⟨-, hRP, hInv⟩ := hPos d μ hμ
  have hsym : ∀ s : halfSpacingTimes d.mesh, IsSymmetricUnder μ (timeReflect s) :=
    fun s => hInv timeAxis s s.2
  have hinv : ∀ (s : halfSpacingTimes d.mesh) (X : GaugeField d.mesh → ℂ), IsBoundedObservable X →
      (timeReflect s).actOn ((timeReflect s).actOn X) = X :=
    fun s X hX => ((hSym d).2.2 s s ⟨0, 0, by simp⟩).1.2 X hX
  have hpos : ∀ F ∈ upperAlgebra t,
      (reflectionPairing μ t F F).im = 0 ∧ 0 ≤ (reflectionPairing μ t F F).re := by
    rintro F ⟨hO, S, hS, -, hm⟩
    have hsub : S ⊆ {x : AmbientSpace | (t : ℝ) ≤ x timeAxis} := fun x hx =>
      (show (t : ℝ) < x timeAxis from hS hx).le
    have h : 0 ≤ reflectionPairing μ t F F :=
      (hRP timeAxis t t.2).1 F hO (Or.inl (isRegionMeasurable_mono hsub hm))
    have h' := Complex.le_def.mp h
    exact ⟨by simpa using h'.2.symm, by simpa using h'.1⟩
  have hP : ReflectionPairingIsPosHermitian μ t :=
    ⟨fun G hG F hF F' hF' c c' => reflectionPairing_linear_right t hG.1 hF.1 hF'.1 c c',
      fun G hG G' hG' F hF c c' => reflectionPairing_antilinear_left t hG.1 hG'.1 hF.1 c c',
      fun G hG F hF => conj_reflectionPairing t (hsym t) (hinv t) hG.1 hF.1, hpos⟩
  have hBounds : ReflectionSeminormEstimates μ t := by
    refine ⟨fun G hG F hF => ?_, fun F hF => reflectionSeminorm_le_supNorm t hF.1,
      reflectionSeminorm_one t⟩
    have h := norm_reflectionPairing_sq_le hP hG hF
    have hp := (hpos G hG).2
    have hq := (hpos F hF).2
    have hroot : reflectionPairingRoot μ t G * reflectionPairingRoot μ t F =
        Real.sqrt ((reflectionPairing μ t G G).re * (reflectionPairing μ t F F).re) := by
      rw [reflectionPairingRoot, reflectionPairingRoot, Real.sqrt_mul hp]
    rw [hroot]
    exact Real.le_sqrt_of_sq_le h
  refine ⟨upperAlgebra_isConjClosedSubalgebra t, hP, hBounds, fun u E hE => ?_⟩
  obtain ⟨-, hQ₁, hQ₂⟩ := (hSym d).2.1 t u
  have hacts : ∀ E' : GaugeField d.mesh → ℂ, IsSlabLocalized t u E' →
      InsertMulIsLinearEndo t u E' := fun E' hE' =>
    ⟨fun F hF => insertMul_mem_upperAlgebra ha hE' hF,
      fun F _ F' _ c c' => insertMul_linear u E' F F' c c'⟩
  have hadj : ∀ E' : GaugeField d.mesh → ℂ, IsSlabLocalized t u E' →
      InsertMulAdjoint μ t u E' := fun E' hE' =>
    ⟨isSlabLocalized_reflectedInsert hE', reflectedInsert_involutive (hinv _) hE'.1,
      hacts E' hE', hacts _ (isSlabLocalized_reflectedInsert hE'), fun F hF G hG =>
        integral_reflection_chain _ _ _ (hsym (midpointTime t u)) (hsym t) (hinv t) hQ₁.2 hQ₂.2
          hE'.1 hF.1 hG.1⟩
  have hT := hadj E hE
  have hR := hadj _ (isSlabLocalized_reflectedInsert hE)
  refine ⟨hT, fun F hF => ?_⟩
  have hnn := reflectionMoment_nonneg hP hT hR hF
  have hlc := reflectionMoment_sq_le hP hT hR hF
  have hconv := hLog (fun n => (reflectionMoment μ t u E F n).re) (fun n => (hnn n).2) hlc
  refine ⟨hnn, (reflectionSeminorm_sq_eq (hpos F hF)).symm, ?_, fun n hn =>
    ⟨hlc n hn, hconv.2 n hn, iterate_insertedTransfer_eq t u E n F⟩⟩
  exact (reflectionMoment_add_one hT hR hF 0 0).trans
    (reflectionSeminorm_sq_eq (hpos _ (hT.2.2.1.1 _ hF))).symm
end YangMills.Construction.InfiniteLattice.ReflectionPairingProof
