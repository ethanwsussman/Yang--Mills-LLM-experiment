import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacingProof
import YangMills.Construction.ReflectionPositivity.DecayAndLawAtASpacing
import YangMills.Construction.ReflectionPositivity.DecayOnSiteCubeVectors
import YangMills.Construction.ReflectionPositivity.InverseSquareLawWithReflectionSizes
import YangMills.Construction.ReflectionPositivity.ReflectionSizesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexConjugate ComplexOrder Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
namespace SpacingDecayAndLaw
open InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry IsBoundedObservable
  regionObservables scaledCube pointToUnit shift pullToUnit pushToUnit plateauPairing
  plateauUnitSpacing unitRegionObservables)
open GibbsAtFixedSpacing (BorelProb linfNorm)
open MirrorHyperplanes (unitPositiveClass)
open LatticeAtSpacing (reflectionPositiveSet)
open LatticeAtSpacing.UnitScaling (TransportsMeasuresAndSymmetries)
open CoarseStepsInverseSquare (SeparatedCubeBound cocompactSites shiftedCorrelation
  transferDecayForm largeDistanceBound invariantPartPairing reflectionSize reflectionSizeRoots)
open SmearingFilter (spectralRateConst spectralRateFn)
variable {a : ℝ}
theorem latticeSymmetry_ext {b : ℝ} {g g' : LatticeSymmetry b} (h : g.toFun = g'.toFun) :
    g = g' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem isBoundedObservable_conj_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => conj (F U) * G U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.isBoundedObservable_conj_mul <;> assumption
theorem conj_mem_regionObservables {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : F ∈ regionObservables a S) : (fun U => conj (F U)) ∈ regionObservables a S := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.conj_mem_regionObservables <;> assumption
theorem pushToUnit_mem_unitPositiveClass
    (hD : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hS : HalfAndShift.HalfAndShiftStatement) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) : pushToUnit ν.1 ∈ unitPositiveClass := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.pushToUnit_mem_unitPositiveClass <;> assumption
theorem pullToUnit_shift (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (v : LatticePoint a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    _root_.YangMills.Construction.InfiniteLattice.pullToUnit ha ((shift v).actOn F) = (shift (pointToUnit ha v)).actOn (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) := by
  rw [hM.2.2.1 (shift v) F hF, latticeSymmetry_ext (hM.2.2.2.1 v)]
theorem exists_intPoint (ha : 0 < a) (r : ℕ+) (y : LatticePoint a) :
    ∃ w : Fin 4 → ℤ, pointToUnit ha y = intPoint w ∧
      cubeGap r w = CoarseStepsInverseSquare.cubeGap a r y := by
  obtain ⟨w, hw⟩ := y.2
  have hw' : ∀ i, (y : AmbientSpace) i = (w i : ℝ) * a := hw
  have hmax : ∀ i, |(y : AmbientSpace) i| ≤ linfNorm y.1 := fun i =>
    Finset.le_sup' (fun μ => |(y : AmbientSpace) μ|) (Finset.mem_univ i)
  have habs : ∀ i, |(y : AmbientSpace) i| = |(w i : ℝ)| * a := fun i => by
    rw [hw' i, abs_mul, abs_of_pos ha]
  have key : EnergyMomentum.supNormCoord (fun i => (w i : ℝ)) = linfNorm y.1 / a := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun i _ => ?_
      change |(w i : ℝ)| ≤ _
      rw [le_div_iff₀ ha, ← habs]
      exact hmax i
    · rw [div_le_iff₀ ha]
      refine Finset.sup'_le _ _ fun i _ => ?_
      change |(y : AmbientSpace) i| ≤ _
      rw [habs]
      exact mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun l => |(w l : ℝ)|) (Finset.mem_univ i)) ha.le
  refine ⟨w, Subtype.ext (funext fun i => ?_), ?_⟩
  · change a⁻¹ * (y : AmbientSpace) i = (w i : ℝ)
    rw [hw' i]
    field_simp
  · unfold cubeGap CoarseStepsInverseSquare.cubeGap
    rw [key]
theorem far_estimates {r m : ℝ} (ha : 0 < a) (hr : 1 ≤ r) (hm : 4 * r * a ≤ m) :
    m / (2 * a) ≤ m / a - 2 * r ∧ 2 * r ≤ m / (2 * a) ∧
      r / (m / a - 2 * r) ≤ 2 * r * a / m ∧ 2 * r * a / m ≤ 1 / 2 := by
  have hm₀ : 0 < m := by nlinarith
  have e₁ : m / (2 * a) = m / a / 2 := by field_simp
  have e₂ : 2 * r * a / m = 2 * r / (m / a) := by field_simp
  have ht : 4 * r ≤ m / a := by rw [le_div_iff₀ ha]; exact hm
  rw [e₁, e₂]
  generalize m / a = t at ht
  have ht₀ : 0 < t := by linarith
  have hn : 0 < t - 2 * r := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [div_le_div_iff₀ hn ht₀]
    nlinarith
  · rw [div_le_iff₀ ht₀]
    linarith
theorem rate_le_six_mul {C u v : ℝ} (hC : 0 ≤ C) (hu : 0 ≤ u) (huv : u ≤ 2 * v)
    (hv : 2 * v ≤ 1 / 2) : C * (u ^ 2 + u ^ 3) ≤ 6 * C * v ^ 2 := by
  have h₂ : u ^ 2 ≤ (2 * v) ^ 2 := pow_le_pow_left₀ hu huv 2
  have h₃ : u ^ 3 ≤ u ^ 2 * (1 / 2) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (huv.trans hv) (sq_nonneg u)
  calc C * (u ^ 2 + u ^ 3) ≤ C * (6 * v ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hC
    _ = 6 * C * v ^ 2 := by ring
theorem euclidNormVec_half_le_linfNorm (v : AmbientSpace) :
    TorusMetric.euclidNormVec v / 2 ≤ linfNorm v := by
  have hle : ∀ μ, |v μ| ≤ linfNorm v := fun μ =>
    Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
  have h₀ : 0 ≤ linfNorm v := (abs_nonneg _).trans (hle 0)
  have hsq : ∀ μ, v μ ^ 2 ≤ linfNorm v ^ 2 := fun μ => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hle μ) 2
  have h : TorusMetric.euclidNormVec v ≤ 2 * linfNorm v := by
    unfold TorusMetric.euclidNormVec
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [Fin.sum_univ_four]
    nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
  linarith
theorem tendsto_linfNorm_cocompactSites (a : ℝ) :
    Tendsto (fun y : LatticePoint a => linfNorm y.1) (cocompactSites a) atTop := by
  have h : Tendsto (fun y : LatticePoint a => TorusMetric.euclidNormVec y.1) (cocompactSites a)
      atTop :=
    tendsto_comap
  exact tendsto_atTop_mono (fun y => euclidNormVec_half_le_linfNorm y.1)
    (h.atTop_div_const (by norm_num))
end SpacingDecayAndLaw
open SpacingDecayAndLaw in
open InfiniteLattice (LatticePoint GaugeField IsBoundedObservable scaledCube shift
  plateauPairing plateauUnitSpacing unitRegionObservables) in
open GibbsAtFixedSpacing (linfNorm) in
open CoarseStepsInverseSquare (SeparatedCubeBound cocompactSites shiftedCorrelation
  transferDecayForm largeDistanceBound invariantPartPairing reflectionSizeRoots) in
open SmearingFilter (spectralRateConst spectralRateFn) in
theorem SpacingDecayAndLaw.holds
    (hDecay : CubeVectorDecay)
    (hLaw : InverseSquareClustering)
    (hD : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hFr : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hSame : ScaledClassesTheorem)
    (hS : HalfAndShift.HalfAndShiftStatement)
    (hSizes : ReflectionSizeBoundsAtMesh) :
    SpacingDecayAndLaw.Statement := by
  intro a ha ν hν r
  obtain ⟨-, hM, -, -, hI⟩ := hD a ha
  have hcoe := coe_unitRepresentative (pushToUnit_mem_unitPositiveClass hD hS ha hν)
  obtain ⟨-, hCorr, hSemi, -, -⟩ := hSizes a ha ν hν r
  have hsize : ∀ F ∈ _root_.YangMills.Construction.InfiniteLattice.regionObservables a (scaledCube a r), _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.reflectionSize ha ν r F =
      cubeReflectionNorm (unitRepresentative ν.1) r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) := by
    intro F hF
    obtain ⟨-, -, -, -, -, -, h⟩ := hCorr F hF
    exact h
  have hcube : ∀ (μ : Fin 4), ∀ F ∈ _root_.YangMills.Construction.InfiniteLattice.regionObservables a (scaledCube a r),
      ScaledPair.cubeVector ν.1 μ ha r F =
          cubeVector (unitRepresentative ν.1) μ r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) ∧
        _root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F ∈ unitRegionObservables (cubeOfRadius r) := by
    intro μ F hF
    obtain ⟨-, -, h₁, h₂, h₃, h₄, -, -⟩ := (hSame a ha ν hν μ).2.2 0
      (halfSpaceLocalAtMesh a μ).zero_mem r F hF 1
    exact ⟨h₁.trans (h₂.trans h₃), h₄⟩
  have hlaw : ∀ F ∈ _root_.YangMills.Construction.InfiniteLattice.regionObservables a (scaledCube a r),
      ∀ G ∈ _root_.YangMills.Construction.InfiniteLattice.regionObservables a (scaledCube a r), SeparatedCubeBound ha ν r F G := by
    intro F hF G hG y hy
    obtain ⟨w, hw, hsep⟩ := exists_intPoint ha r y
    have hFo : IsBoundedObservable F := hF.1
    have hGo : IsBoundedObservable G := hG.1
    have h := (hLaw (unitRepresentative ν.1) r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) (hcube 0 F hF).2
      (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha G) (hcube 0 G hG).2).1 w (hsep ▸ hy)
    have hc : shiftedCorrelation ν F G y =
        ∫ U, conj (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F U) *
            (shift (intPoint w)).actOn (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha G) U
          ∂(unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ))) := by
      have h₁ := hM.2.1 ν (fun U => conj (F U) * (shift y).actOn G U)
        (isBoundedObservable_conj_mul hFo (hGo.actOn _))
      rw [shiftedCorrelation, ← h₁, hcoe, ← hw, ← pullToUnit_shift ha hM y hGo]
      rfl
    have hp : plateauPairing ν.1 F G = plateauUnitSpacing
        (unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ)))
        (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha G) := by
      rw [hcoe]
      exact (((hI.2.2.2 ν).2.2 hν.1 F G hFo hGo).2)
    rw [hc, hp, reflectionSizeRoots, hsize F hF, hsize G hG, ← hsep, ← mul_assoc]
    exact h
  intro F hF G hG μ
  have hFo : IsBoundedObservable F := hF.1
  have hGo : IsBoundedObservable G := hG.1
  have hC : 0 < spectralRateConst := hDecay.1
  have hroots : 0 ≤ reflectionSizeRoots ha ν r F G := by
    unfold reflectionSizeRoots
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hr₁ : (1 : ℝ) ≤ ((r : ℕ) : ℝ) := by exact_mod_cast r.2
  have hfar : ∀ y : LatticePoint a, 4 * ((r : ℕ) : ℝ) * a ≤ linfNorm y.1 →
      linfNorm y.1 / (2 * a) ≤ CoarseStepsInverseSquare.cubeGap a r y ∧
      2 * ((r : ℕ) : ℝ) ≤ linfNorm y.1 / (2 * a) ∧
      ((r : ℕ) : ℝ) / CoarseStepsInverseSquare.cubeGap a r y ≤
        2 * ((r : ℕ) : ℝ) * a / linfNorm y.1 ∧
      2 * ((r : ℕ) : ℝ) * a / linfNorm y.1 ≤ 1 / 2 ∧
      spectralRateFn (((r : ℕ) : ℝ) / CoarseStepsInverseSquare.cubeGap a r y) ≤
        6 * spectralRateConst * (((r : ℕ) : ℝ) * a / linfNorm y.1) ^ 2 ∧
      ‖shiftedCorrelation ν F G y - plateauPairing ν.1 F G‖ ≤ largeDistanceBound ha ν r F G y := by
    intro y hy
    obtain ⟨h₁, h₂, h₃, h₄⟩ := far_estimates ha hr₁ hy
    have hn : 1 ≤ CoarseStepsInverseSquare.cubeGap a r y := by
      have := h₁.trans' h₂
      unfold CoarseStepsInverseSquare.cubeGap at *
      linarith
    have hn₀ : 0 < CoarseStepsInverseSquare.cubeGap a r y := by linarith
    have hv : 2 * ((r : ℕ) : ℝ) * a / linfNorm y.1 =
        2 * (((r : ℕ) : ℝ) * a / linfNorm y.1) := by
      ring
    have hq : spectralRateFn (((r : ℕ) : ℝ) / CoarseStepsInverseSquare.cubeGap a r y) ≤
        6 * spectralRateConst * (((r : ℕ) : ℝ) * a / linfNorm y.1) ^ 2 :=
      rate_le_six_mul hC.le (by positivity) (hv ▸ h₃) (hv ▸ h₄)
    refine ⟨h₁, h₂, h₃, h₄, hq, ?_⟩
    exact (hlaw F hF G hG y hn).trans (mul_le_mul_of_nonneg_right hq hroots)
  have hfarT : Tendsto (largeDistanceBound ha ν r F G) (cocompactSites a) (𝓝 0) := by
    have hT : Tendsto (fun y : LatticePoint a => ((r : ℕ) : ℝ) * a / linfNorm y.1)
        (cocompactSites a) (𝓝 0) := (tendsto_linfNorm_cocompactSites a).const_div_atTop _
    have h := ((hT.pow 2).const_mul (6 * spectralRateConst)).mul_const
      (reflectionSizeRoots ha ν r F G)
    have h₀ : 6 * spectralRateConst * (0 : ℝ) ^ 2 * reflectionSizeRoots ha ν r F G = 0 := by ring
    rw [h₀] at h
    exact h
  refine ⟨?_, hlaw F hF G hG, ?_,
    ⟨hC.le, hfar, fun y => euclidNormVec_half_le_linfNorm y.1, hfarT, ?_⟩, ?_⟩
  · intro k hk
    obtain ⟨hv, hFf⟩ := hcube μ F hF
    obtain ⟨h₀, h₁⟩ := hDecay.2 (unitRepresentative ν.1) μ r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F) hFf k hk
    have he : transferDecayForm ha ν μ r F k =
        inner ℂ (cubeVector (unitRepresentative ν.1) μ r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F))
          ((ReflectionPair.site.transferOp (unitRepresentative ν.1) μ ^ k *
              (1 - groundProjection μ ReflectionPair.site (unitRepresentative ν.1)))
            (cubeVector (unitRepresentative ν.1) μ r (_root_.YangMills.Construction.InfiniteLattice.pullToUnit ha F))) := by
      unfold transferDecayForm
      rw [hv]
      rfl
    rw [he, hsize F hF]
    exact ⟨h₀, h₁⟩
  · intro y hy
    have hform : plateauPairing ν.1 (fun U => conj (F U)) G = invariantPartPairing ν F G := by
      obtain ⟨-, -, -, -, -, h⟩ := (hFr a ha).2.2.2.1 ν hν.1 F G hFo hGo 0
      exact h
    refine ⟨hform, ?_⟩
    have h := hlaw _ (conj_mem_regionObservables hF) G hG y hy
    have hcorr : shiftedCorrelation ν (fun U => conj (F U)) G y =
        ν.integral fun U => F U * (shift y).actOn G U := by
      simp only [shiftedCorrelation, Complex.conj_conj]
    have hs : reflectionSizeRoots ha ν r (fun U => conj (F U)) G =
        reflectionSizeRoots ha ν r F G := by
      unfold reflectionSizeRoots
      rw [← (hSemi.2 F hF).2.1]
    rwa [hform, hcorr, hs] at h
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hfarT
    filter_upwards [(tendsto_linfNorm_cocompactSites a).eventually_ge_atTop
      (4 * ((r : ℕ) : ℝ) * a)] with y hy
    exact (hfar y hy).2.2.2.2.2
  · intro hE
    exact (((hFr a ha).2.2.2.2 ν hE).2 hν.1 F G hFo hGo).2.1
end YangMills.Construction.ReflectionPositivity.DirectionPictures
