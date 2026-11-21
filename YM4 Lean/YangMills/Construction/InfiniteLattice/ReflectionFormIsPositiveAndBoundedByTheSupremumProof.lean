import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.IsometriesAndReflectionsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.ReflectionFormIsPositiveAndBoundedByTheSupremum
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.InfiniteLattice.ReflectionFormBound
open LatticeConventions (NormalHyperplane)
open LatticeConventions.NormalHyperplane (reflectSymmetry)
open LatticeConventions.MirrorSideIndependence (reflectedPairing)
variable {a : ℝ}
theorem isRegionMeasurable_mono {R R' : Set AmbientSpace} (hsub : R ⊆ R') {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable R F) : IsRegionMeasurable R' F := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
theorem exists_common_region {t : halfSpacingTimes a} {F G : GaugeField a → ℂ}
    (hF : F ∈ localObsAbove t) (hG : G ∈ localObsAbove t) :
    ∃ R : Set AmbientSpace, R ⊆ abovePlane t ∧ Bornology.IsBounded R ∧
      Measurable[regionSigma R] F ∧ Measurable[regionSigma R] G := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.exists_common_region <;> assumption
theorem isBoundedObservable_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (F * G) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_mul <;> assumption
theorem localObsAbove_isAlgebra (t : halfSpacingTimes a) :
    LocalObsAboveIsAlgebra t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⟨measurable_const, 0, fun _ => by simp⟩, ∅, Set.empty_subset _,
      Bornology.isBounded_empty, measurable_const⟩
  · intro F hF G hG
    obtain ⟨R, hR, hb, h₁, h₂⟩ := exists_common_region hF hG
    obtain ⟨⟨m, C, hC⟩, -⟩ := hF
    obtain ⟨⟨m', C', hC'⟩, -⟩ := hG
    exact ⟨⟨m.add m', C + C', fun U => (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))⟩,
      R, hR, hb, h₁.add h₂⟩
  · intro c F hF
    obtain ⟨⟨m, C, hC⟩, R, hR, hb, hm⟩ := hF
    refine ⟨⟨m.const_smul c, ‖c‖ * C, fun U => ?_⟩, R, hR, hb,
      Measurable.const_smul (show Measurable[regionSigma R] F from hm) c⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg _)
  · intro F hF G hG
    obtain ⟨R, hR, hb, h₁, h₂⟩ := exists_common_region hF hG
    exact ⟨isBoundedObservable_mul hF.1 hG.1, R, hR, hb, h₁.mul h₂⟩
theorem isBoundedObservable_timeConj (t : halfSpacingTimes a) {G : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) : IsBoundedObservable (timeConj t G) := by apply _root_.YangMills.Construction.InfiniteLattice.CutoffSymmetries.isBoundedObservable_timeConj <;> assumption
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    {f : GaugeField a → ℂ} (hf : IsBoundedObservable f) : Integrable f ν := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.integrable_of_isBoundedObservable <;> assumption
theorem reflectionForm_linear_right (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (t : halfSpacingTimes a) {G F F' : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (hF : IsBoundedObservable F) (hF' : IsBoundedObservable F') (c c' : ℂ) :
    reflectionForm ν t G (c • F + c' • F') =
      c * reflectionForm ν t G F + c' * reflectionForm ν t G F' := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.reflectionPairing_linear_right <;> assumption
theorem reflectionForm_conjLinear_left (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (t : halfSpacingTimes a) {G G' F : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (hG' : IsBoundedObservable G') (hF : IsBoundedObservable F) (c c' : ℂ) :
    reflectionForm ν t (c • G + c' • G') F =
      conj c * reflectionForm ν t G F + conj c' * reflectionForm ν t G' F := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.reflectionPairing_antilinear_left <;> assumption
theorem reflectionForm_conj_symm (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (t : halfSpacingTimes a)
    (hreal : ∀ F ∈ localObsAbove t, (reflectionForm ν t F F).im = 0)
    {G F : GaugeField a → ℂ} (hG : G ∈ localObsAbove t)
    (hF : F ∈ localObsAbove t) :
    reflectionForm ν t G F = conj (reflectionForm ν t F G) := by
  obtain ⟨-, -, hsmul, -⟩ := localObsAbove_isAlgebra t
  have hadd := (localObsAbove_isAlgebra t).2.1
  have expand : ∀ c : ℂ, reflectionForm ν t (F + c • G) (F + c • G) =
      reflectionForm ν t F F + c * reflectionForm ν t F G +
        conj c * reflectionForm ν t G F +
          conj c * c * reflectionForm ν t G G := by
    intro c
    have hcG := hsmul c G hG
    have e₁ : F + c • G = (1 : ℂ) • F + c • G := by rw [one_smul]
    have e₂ : ∀ X : GaugeField a → ℂ, IsBoundedObservable X → reflectionForm ν t X (F + c • G) =
        reflectionForm ν t X F + c * reflectionForm ν t X G := by
      intro X hX
      rw [e₁, reflectionForm_linear_right ν t hX hF.1 hG.1, one_mul]
    have e₃ : reflectionForm ν t (F + c • G) (F + c • G) =
        reflectionForm ν t F (F + c • G) +
          conj c * reflectionForm ν t G (F + c • G) := by
      conv_lhs => rw [show reflectionForm ν t (F + c • G) (F + c • G) =
        reflectionForm ν t ((1 : ℂ) • F + c • G) (F + c • G) by rw [one_smul]]
      rw [reflectionForm_conjLinear_left ν t hF.1 hG.1 (hadd F hF _ hcG).1, map_one, one_mul]
    rw [e₃, e₂ F hF.1, e₂ G hG.1]
    ring
  have h₁ := hreal _ (hadd F hF _ (hsmul 1 G hG))
  have h₂ := hreal _ (hadd F hF _ (hsmul Complex.I G hG))
  rw [expand] at h₁ h₂
  have hFF := hreal F hF
  have hGG := hreal G hG
  simp only [map_one, one_mul, Complex.add_im, Complex.conj_I, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.neg_im, hFF, hGG, zero_mul, one_mul, zero_add, add_zero,
    neg_mul, neg_zero, zero_sub, mul_zero] at h₁ h₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
def timePlane (t : ℝ) : NormalHyperplane :=
  NormalHyperplane.axial timeAxis t
theorem timePlane_isLatticeMirror (t : halfSpacingTimes a) :
    (timePlane t).IsLatticeMirror a := by
  refine ⟨fun _ => t.2, fun h => ?_⟩
  exfalso
  obtain ⟨μ, lam, -, h | h⟩ := h <;>
  · have hs := congrArg (fun v : Fin 4 → ℝ => ∑ i, v i) h
    simp [timePlane, NormalHyperplane.axial,
      LatticeConventions.basisVector, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_pi_single'] at hs
theorem latticeSymmetry_ext {s r : LatticeSymmetry a} (h : s.toFun = r.toFun) : s = r := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem reflectSymmetry_timePlane_eq_timeReflect (t : halfSpacingTimes a) :
    reflectSymmetry (timePlane_isLatticeMirror t) = timeReflect t := by
  apply latticeSymmetry_ext
  funext x
  rw [timeReflect_apply]
  change NormalHyperplane.reflect (timePlane t) x = _
  rw [NormalHyperplane.reflect_eq_hyperplaneReflect]
  simp [timePlane, NormalHyperplane.axial, hyperplaneReflect,
    LatticeConventions.basisVector]
theorem abovePlane_subset_upperHalfSpace (t : ℝ) :
    abovePlane t ⊆ (timePlane t).upperHalfSpace := by
  intro x hx
  have hd : LatticeConventions.euclidDot (timePlane t).normal x = x timeAxis := by
    simp [timePlane, NormalHyperplane.axial, LatticeConventions.euclidDot,
      LatticeConventions.basisVector, Pi.single_apply]
  change (t : ℝ) ≤ LatticeConventions.euclidDot (timePlane t).normal x
  rw [hd]
  exact le_of_lt hx
theorem reflectionFormNonneg_of_symmetries (h : PeriodicGibbsSymmetries.Statement) (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField a)} (hν : IsPeriodicGibbs β ν)
    (t : halfSpacingTimes a) {F : GaugeField a → ℂ} (hF : F ∈ localObsAbove t) :
    ReflectionFormNonneg ν t F := by
  have hQ := timePlane_isLatticeMirror t
  obtain ⟨hobs, R, hR, -, hm⟩ := hF
  have hside : F ∈ regionObservables a (timePlane t).upperHalfSpace :=
    ⟨hobs, isRegionMeasurable_mono (hR.trans (abovePlane_subset_upperHalfSpace t)) hm⟩
  have hpos := (((h a ha β hβ).1 ν hν).2 _ hQ).2.1 F hside
  have e : reflectedPairing hQ ν F = reflectionForm ν t F F := by
    unfold reflectedPairing reflectionForm
    rw [reflectSymmetry_timePlane_eq_timeReflect]
    rfl
  rw [e] at hpos
  obtain ⟨h₁, h₂⟩ := Complex.le_def.mp hpos
  exact ⟨by simpa using h₂.symm, by simpa using h₁⟩
theorem reflectionSeminorm_le_supNorm (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (t : halfSpacingTimes a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    reflectionSeminorm ν t F ≤ observableSupNorm F := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.reflectionSeminorm_le_supNorm <;> assumption
theorem reflectionFormPosAndSupBound_holds (h : PeriodicGibbsSymmetries.Statement) :
    ReflectionFormPosAndSupBound := by
  intro s β hβ ν hν t
  have ha : 0 < refinedSpacing s.L s.K :=
    zpow_pos (by exact_mod_cast (by have := s.isAdmissible.2; omega : 0 < s.L)) _
  have hν' : IsPeriodicGibbs β ν := hν
  have : IsProbabilityMeasure ν := hν'.1.1
  have hroot : ∀ F ∈ localObsAbove t, ReflectionFormNonneg ν t F :=
    fun F hF => reflectionFormNonneg_of_symmetries h ha hβ hν' t hF
  exact ⟨localObsAbove_isAlgebra t,
    ⟨fun G hG F hF F' hF' c c' => reflectionForm_linear_right ν t hG.1 hF.1 hF'.1 c c',
      fun G hG G' hG' F hF c c' => reflectionForm_conjLinear_left ν t hG.1 hG'.1 hF.1 c c',
      fun G hG F hF => reflectionForm_conj_symm ν t (fun F hF => (hroot F hF).1) hG hF, hroot⟩,
    fun F hF => reflectionSeminorm_le_supNorm ν t hF.1⟩
end YangMills.Construction.InfiniteLattice.ReflectionFormBound
