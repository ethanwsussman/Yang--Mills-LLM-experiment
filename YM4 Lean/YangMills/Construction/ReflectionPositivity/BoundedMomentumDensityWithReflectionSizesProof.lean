import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.Functions.PropertiesOfTheSmearingSequenceAndTheTriangleFunction
import YangMills.Construction.Functions.SmearingSeriesConvergence
import YangMills.Construction.InfiniteLattice.UnitLatticeIsometriesAndPlaquettes
import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizes
import YangMills.Construction.ReflectionPositivity.CountingAgainstTheRate
import YangMills.Construction.ReflectionPositivity.CubeVectorsDependLinearlyOnTheObservable
import YangMills.Construction.ReflectionPositivity.MeasureWithSummableFourierCoefficients
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound
open InfiniteLattice (GaugeField IsBoundedObservable UnitLatticeSymmetry axisStep shift
  unitRegionObservables)
open MirrorHyperplanes (unitPositiveClass siteReflect sitePlane)
open SmearingFilter (absCoeffSum filterSeries spectralDensityConst)
open TriangleKernel (smearingSeq tentFourierCoeff)
open Autocorrelation (twoPointCorrelation smearedTwoPointCorrelation correlationDecayRate)
open EnergyMomentum (SpectralSpace orthLattice orthProj expNegNatMulEnergy
  expNegNatMulEnergy_zero expNegNatMulEnergy_top torusCharacter boxRep boxRep_torusProj
  torusFourierCoeff torusFourierSeries distTwoPiInt isLeast_distTwoPiInt supNormCoord
  SummableFourierCoeffTheorem)
def pairCorrelation (ν : unitPositiveClass) (A : GaugeField (1 : ℝ) → ℂ)
    (y : Fin 4 → ℤ) : ℂ :=
  ∫ U, conj (A U) * (shift (intPoint y)).actOn A U
    ∂(ν : Measure (GaugeField (1 : ℝ)))
def shiftAlong (μ : Fin 4) (s : ℤ) (w : Fin 4 → ℤ) : Fin 4 → ℤ := s • Pi.single μ 1 + w
theorem twoPointCorrelation_eq_pairCorrelation (ν : unitPositiveClass) (μ : Fin 4) (ς : ℤˣ)
    (A : GaugeField (1 : ℝ) → ℂ) (s : ℤ) (w : orthLattice μ) :
    twoPointCorrelation ν μ ς A s w = ((ς : ℤ) : ℂ) * pairCorrelation ν A (shiftAlong μ s w.1) := by
  have e : s • axisStep (1 : ℝ) μ + intPoint w.1 = intPoint (shiftAlong μ s w.1) := by
    apply Subtype.ext
    funext i
    by_cases h : i = μ
    · subst h
      simp [intPoint, axisStep, shiftAlong]
    · simp [intPoint, axisStep, shiftAlong, h]
  rw [twoPointCorrelation, pairCorrelation, e]
theorem unitLatticeSymmetry_ext {g g' : UnitLatticeSymmetry} (h : g.toFun = g'.toFun) :
    g = g' := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.latticeSymmetry_ext_toFun <;> assumption
def flipCoord (μ : Fin 4) (y : Fin 4 → ℤ) : Fin 4 → ℤ := y - (2 * y μ) • Pi.single μ 1
theorem siteReflect_comp_shift (μ : Fin 4) (y : Fin 4 → ℤ) :
    (siteReflect μ).comp (shift (intPoint (flipCoord μ y))) =
      (shift (intPoint y)).comp (siteReflect μ) := by
  apply unitLatticeSymmetry_ext
  funext x i
  change (siteReflect μ).toFun (x + fun i => (flipCoord μ y i : ℝ)) i =
    (siteReflect μ).toFun x i + (y i : ℝ)
  rw [siteReflect_coord, siteReflect_coord]
  by_cases h : i = μ
  · subst h
    simp [flipCoord]
    ring
  · simp [flipCoord, h]
theorem isBoundedObservable_actOn
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (g : UnitLatticeSymmetry) {A : GaugeField (1 : ℝ) → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable (g.actOn A) :=
  ((hAct.2.2.2.2.1 g) A hA).1
theorem isBoundedObservable_conj_mul
    {A B : GaugeField (1 : ℝ) → ℂ} (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    IsBoundedObservable (fun U => conj (A U) * B U) := by
  obtain ⟨mA, C, hC⟩ := hA
  obtain ⟨mB, D, hD⟩ := hB
  refine ⟨(Complex.continuous_conj.measurable.comp mA).mul mB, C * D, fun U => ?_⟩
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem unit_cast_mul_self (ς : ℤˣ) : ((ς : ℤ) : ℂ) * ((ς : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or ς with e | e <;> simp [e]
theorem conj_unit_cast (ς : ℤˣ) : conj (((ς : ℤ) : ℂ)) = ((ς : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or ς with e | e <;> simp [e]
theorem pairCorrelation_flipCoord
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hG : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
    (ν : unitPositiveClass) (μ : Fin 4) (ς : ℤˣ)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : IsBoundedObservable A)
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U) (y : Fin 4 → ℤ) :
    pairCorrelation ν A (flipCoord μ y) = pairCorrelation ν A y := by
  have hτ := isBoundedObservable_actOn hAct (shift (intPoint (flipCoord μ y))) hA
  have inv := hG.2.1 ν.1 ν.2 (siteReflect μ) _ (isBoundedObservable_conj_mul hA hτ)
  have hc : (siteReflect μ).actOn
        ((shift (intPoint (flipCoord μ y))).actOn A) =
      (shift (intPoint y)).actOn ((siteReflect μ).actOn A) := by
    rw [← (hAct.2.2.2.2.2.1 _ _ A A hA hA).1, siteReflect_comp_shift,
      (hAct.2.2.2.2.2.1 _ _ A A hA hA).1]
  rw [pairCorrelation, ← inv, pairCorrelation]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have h1 : A ((siteReflect μ).pullbackField U) = ((ς : ℤ) : ℂ) * A U := congrFun hθ U
  have h2 : (siteReflect μ).actOn
      ((shift (intPoint (flipCoord μ y))).actOn A) U =
      ((ς : ℤ) : ℂ) * (shift (intPoint y)).actOn A U := by
    rw [hc, hθ]
    rfl
  change conj (A ((siteReflect μ).pullbackField U)) *
    (siteReflect μ).actOn
      ((shift (intPoint (flipCoord μ y))).actOn A) U = _
  rw [h1, h2, map_mul, conj_unit_cast]
  linear_combination (conj (A U) * (shift (intPoint y)).actOn A U) *
    unit_cast_mul_self ς
theorem norm_energyMomentumMonomial_le (μ : Fin 4) (n : ℕ) (w : orthLattice μ)
    (x : SpectralSpace μ) : ‖energyMomentumMonomial μ n w x‖ ≤ 1 := by
  have h := expNegNatMulEnergy_mem_Icc n x.energy
  rw [energyMomentumMonomial, norm_mul, Complex.norm_real, Complex.norm_exp_I_mul_ofReal, mul_one,
    Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2
theorem pairCorrelation_eq_spectralIntegral
    (hS : SiteReflectionPair.Conclusion) (hE : SpectralMeasuresTheorem)
    (ν : unitPositiveClass) (l : Fin 4) (r : ℕ+) {A : GaugeField (1 : ℝ) → ℂ}
    (hA : A ∈ unitRegionObservables (cubeOfRadius r)) (y : Fin 4 → ℤ) (hy : 2 * (r : ℤ) ≤ y l) :
    pairCorrelation ν A y =
      ReflectionPair.site.spectralIntegral ν l
        (cubeVector ν l r ((siteReflect l).actOn A)) (cubeVector ν l r A)
        (energyMomentumMonomial l (y l - 2 * (r : ℤ)).toNat (orthProj l y)) :=
  ((hS ν l r).2.2.2.2.1.1 A hA A hA y hy).trans
    (((hE l).2.2 ν ReflectionPair.site).2.2.2.2.2.2.2.1 _ _ _ (orthProj l y))
theorem cubeVector_unit_mul (hL : CubeVectorLinearity.Statement)
    (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r)) :
    cubeVector ν μ r (fun U => ((ς : ℤ) : ℂ) * A U) =
      ((ς : ℤ) : ℂ) • cubeVector ν μ r A := by
  obtain ⟨L, hLin⟩ := (hL ν μ r).1.2.1
  have hm : A ∈ cubeObservableSpace r := hA
  have h1 := hLin (((ς : ℤ) : ℂ) • ⟨A, hm⟩)
  have h2 := hLin ⟨A, hm⟩
  rw [map_smul, h2] at h1
  exact h1.symm
theorem unit_mul_pairCorrelation_eq_integral
    (hS : SiteReflectionPair.Conclusion) (hE : SpectralMeasuresTheorem)
    (hL : CubeVectorLinearity.Statement)
    (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (y : Fin 4 → ℤ) (hy : 2 * (r : ℤ) ≤ y μ) :
    ((ς : ℤ) : ℂ) * pairCorrelation ν A y =
      ∫ x, energyMomentumMonomial μ (y μ - 2 * (r : ℤ)).toNat (orthProj μ y) x
        ∂siteSpectralMeasure ν μ (cubeVector ν μ r A) := by
  have h : pairCorrelation ν A y = _ := (hS ν μ r).2.2.2.2.1.1 A hA A hA y hy
  rw [hθ, cubeVector_unit_mul hL ν μ r ς hA, inner_smul_left, conj_unit_cast] at h
  have m := (((hE μ).2.2 ν ReflectionPair.site).2.1 (cubeVector ν μ r A)).2.1.2
    (y μ - 2 * (r : ℤ)).toNat (orthProj μ y)
  rw [h, ← mul_assoc, unit_cast_mul_self, one_mul]
  exact m
theorem actOn_siteReflect_involutive
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (l : Fin 4) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (siteReflect l).actOn ((siteReflect l).actOn F) = F := by
  have hid := (hAct.2.2.2.2.2.2.2.2.1 (sitePlane l)).2.1
  have hl : Function.LeftInverse (siteReflect l).toFun (siteReflect l).toFun := fun x =>
    congrFun hid x
  exact (hAct.2.2.2.2.2.1 (siteReflect l) (siteReflect l) F F hF hF).2.1 (siteReflect l)
    ⟨hl, hl⟩
def siteReflectElem (l : Fin 4) : axisReflectionGroup :=
  ⟨siteReflectPerm l, Subgroup.subset_closure ⟨l, rfl⟩⟩
theorem toUnitLatticeSymmetry_siteReflectElem (l : Fin 4) :
    axisReflectionGroup.toUnitLatticeSymmetry (siteReflectElem l) = siteReflect l :=
  unitLatticeSymmetry_ext rfl
theorem sq_norm_cubeVector_reflect_le (ν : unitPositiveClass) (l : Fin 4) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) :
    ‖cubeVector ν l r ((siteReflect l).actOn A)‖ ^ 2 ≤
      cubeReflectionNorm ν r A := by
  refine (isGreatest_cubeReflectionNorm ν r A).2 ⟨(l, siteReflectElem l), ?_⟩
  simp only [toUnitLatticeSymmetry_siteReflectElem]
theorem sq_norm_cubeVector_le
    (hS : SiteReflectionPair.Conclusion)
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (ν : unitPositiveClass) (l : Fin 4) (r : ℕ+) {A : GaugeField (1 : ℝ) → ℂ}
    (hA : A ∈ unitRegionObservables (cubeOfRadius r)) :
    ‖cubeVector ν l r A‖ ^ 2 ≤ cubeReflectionNorm ν r A := by
  have h := sq_norm_cubeVector_reflect_le ν l r ((siteReflect l).actOn A)
  rw [actOn_siteReflect_involutive hAct l hA.1] at h
  have e := (hS ν l r).2.2.2.2.2.2.1 (siteReflectElem l) A hA
  rw [toUnitLatticeSymmetry_siteReflectElem] at e
  rwa [e] at h
theorem cubeReflectionNorm_nonneg_of_mem
    (hS : SiteReflectionPair.Conclusion)
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (ν : unitPositiveClass) (l : Fin 4) (r : ℕ+) {A : GaugeField (1 : ℝ) → ℂ}
    (hA : A ∈ unitRegionObservables (cubeOfRadius r)) : 0 ≤ cubeReflectionNorm ν r A :=
  (sq_nonneg _).trans (sq_norm_cubeVector_le hS hAct ν l r hA)
theorem flipCoord_shiftAlong (μ : Fin 4) (s : ℤ) {w : Fin 4 → ℤ} (hw : w μ = 0) :
    flipCoord μ (shiftAlong μ s w) = shiftAlong μ (-s) w := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [flipCoord, shiftAlong, hw]
    ring
  · simp [flipCoord, shiftAlong, h]
theorem neg_shiftAlong (μ : Fin 4) (s : ℤ) (w : Fin 4 → ℤ) :
    -shiftAlong μ s w = shiftAlong μ (-s) (-w) := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [shiftAlong]
    ring
  · simp [shiftAlong, h]
theorem shiftAlong_apply_self (μ : Fin 4) (s : ℤ) (w : orthLattice μ) :
    shiftAlong μ s w.1 μ = s := by
  have hw : w.1 μ = 0 := w.2
  simp [shiftAlong, hw]
theorem orthProj_shiftAlong (μ : Fin 4) (s : ℤ) (w : orthLattice μ) :
    orthProj μ (shiftAlong μ s w.1) = w := by
  have hw : w.1 μ = 0 := w.2
  apply Subtype.ext
  funext i
  by_cases h : i = μ
  · subst h
    simp [orthProj, shiftAlong, hw]
  · simp [orthProj, shiftAlong, h]
section TwoPoint
variable (hS : SiteReflectionPair.Conclusion)
  (hE : SpectralMeasuresTheorem)
  (hL : CubeVectorLinearity.Statement)
  (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
  (hG : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
  (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
  {A : GaugeField (1 : ℝ) → ℂ}
include hAct hG in
theorem twoPointCorrelation_neg (hA : IsBoundedObservable A)
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (s : ℤ) (w : orthLattice μ) :
    twoPointCorrelation ν μ ς A (-s) w = twoPointCorrelation ν μ ς A s w := by
  rw [twoPointCorrelation_eq_pairCorrelation, twoPointCorrelation_eq_pairCorrelation,
    ← flipCoord_shiftAlong μ s w.2, pairCorrelation_flipCoord hAct hG ν μ ς hA hθ]
include hS hAct hG in
theorem twoPointCorrelation_neg_transverse (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (s : ℤ) (w : orthLattice μ) :
    twoPointCorrelation ν μ ς A s (-w) = conj (twoPointCorrelation ν μ ς A s w) := by
  have hw : (-w).1 μ = 0 := (-w).2
  have e : shiftAlong μ s (-w).1 = flipCoord μ (-shiftAlong μ s w.1) := by
    rw [neg_shiftAlong, show -w.1 = (-w).1 from rfl, flipCoord_shiftAlong μ _ hw, neg_neg]
  rw [twoPointCorrelation_eq_pairCorrelation, twoPointCorrelation_eq_pairCorrelation, e,
    pairCorrelation_flipCoord hAct hG ν μ ς hA.1 hθ, map_mul, conj_unit_cast]
  congr 1
  exact (hS ν μ r).2.2.2.2.1.2.1 A hA A hA _
include hS hE hL in
theorem twoPointCorrelation_eq_moment (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (n : ℕ) (w : orthLattice μ) :
    twoPointCorrelation ν μ ς A (2 * (r : ℤ) + n) w =
      ∫ x, energyMomentumMonomial μ n w x
        ∂siteSpectralMeasure ν μ (cubeVector ν μ r A) := by
  have h := unit_mul_pairCorrelation_eq_integral hS hE hL ν μ r ς hA hθ
    (shiftAlong μ (2 * (r : ℤ) + n) w.1) (by rw [shiftAlong_apply_self]; omega)
  rw [shiftAlong_apply_self, orthProj_shiftAlong] at h
  rw [twoPointCorrelation_eq_pairCorrelation, h]
  congr 3
  simp
include hS hE hL hAct in
theorem norm_twoPointCorrelation_moment_le (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (n : ℕ) (w : orthLattice μ) :
    ‖twoPointCorrelation ν μ ς A (2 * (r : ℤ) + n) w‖ ≤ cubeReflectionNorm ν r A := by
  rw [twoPointCorrelation_eq_moment hS hE hL ν μ r ς hA hθ]
  have hm := ((hE μ).2.2 ν ReflectionPair.site).2.1 (cubeVector ν μ r A)
  have hb := norm_integral_le_of_norm_le_const (μ := siteSpectralMeasure ν μ
    (cubeVector ν μ r A)) (ae_of_all _ (norm_energyMomentumMonomial_le μ n w))
  refine hb.trans ?_
  have e : (siteSpectralMeasure ν μ (cubeVector ν μ r A)).real univ =
      ‖cubeVector ν μ r A‖ ^ 2 := by
    rw [measureReal_def, hm.2.2.1, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [e, one_mul]
  exact sq_norm_cubeVector_le hS hAct ν μ r hA
include hS hE hL hAct hG in
theorem norm_twoPointCorrelation_le (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    {j : ℤ} (hj : j ≠ 0) (w : orthLattice μ) :
    ‖twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w‖ ≤ cubeReflectionNorm ν r A := by
  have key : ∀ m : ℕ, ‖twoPointCorrelation ν μ ς A (2 * (r : ℤ) * ((m : ℤ) + 1)) w‖ ≤
      cubeReflectionNorm ν r A := fun m => by
    have e : 2 * (r : ℤ) * ((m : ℤ) + 1) = 2 * (r : ℤ) + ((2 * (r : ℕ) * m : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e]
    exact norm_twoPointCorrelation_moment_le hS hE hL hAct ν μ r ς hA hθ _ w
  obtain ⟨m, rfl | rfl⟩ := j.eq_nat_or_neg
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := key k
    push_cast
    exact this
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e : 2 * (r : ℤ) * -((k + 1 : ℕ) : ℤ) = -(2 * (r : ℤ) * ((k : ℤ) + 1)) := by
      push_cast
      ring
    rw [e, twoPointCorrelation_neg hAct hG ν μ ς hA.1 hθ]
    exact key k
end TwoPoint
section Smearing
variable (hS : SiteReflectionPair.Conclusion)
  (hE : SpectralMeasuresTheorem)
  (hL : CubeVectorLinearity.Statement)
  (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
  (hG : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
  (hP : TriangleKernel.SeqAndTentProperties)
  (hC : SmearingFilter.SeriesConvergence.SeriesConverge)
  (hW : SmearingFilter.Bounds.FilterWeightBounds)
  (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
  {A : GaugeField (1 : ℝ) → ℂ}
def absTermBound (j : ℤ) : ℝ := |(smearingSeq j : ℝ)| * (tentFourierCoeff j).re
def smearCoeff (j : ℤ) : ℂ := (smearingSeq j : ℂ) * tentFourierCoeff j
include hP in
theorem absTermBound_nonneg (j : ℤ) : 0 ≤ absTermBound j :=
  mul_nonneg (abs_nonneg _) (hP.2.2.1.2.2.2.1 j).2
include hP in
theorem hasSum_absTermBound : HasSum absTermBound absCoeffSum :=
  (hP.2.2.2.2.1).hasSum
include hC in
theorem norm_smearCoeff_le (j : ℤ) : ‖smearCoeff j‖ ≤ absTermBound j := by
  have h := hC.2.1.1 j 0
  simpa [smearCoeff, absTermBound] using h
include hS hE hL hAct hG hP hC in
theorem norm_smearTerm_le (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) (j : ℤ) :
    ‖smearCoeff j * twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w‖ ≤
      absTermBound j * cubeReflectionNorm ν r A := by
  have hN := cubeReflectionNorm_nonneg_of_mem hS hAct ν μ r hA
  by_cases hj : j = 0
  · subst hj
    have e : smearCoeff 0 = 0 := hP.2.2.2.2.2.2.2
    rw [e, zero_mul, norm_zero]
    exact mul_nonneg (absTermBound_nonneg hP 0) hN
  · rw [norm_mul]
    exact mul_le_mul (norm_smearCoeff_le hC j)
      (norm_twoPointCorrelation_le hS hE hL hAct hG ν μ r ς hA hθ hj w) (norm_nonneg _)
      (absTermBound_nonneg hP j)
include hS hE hL hAct hG hP hC in
theorem summable_smearTerms (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) :
    Summable fun j : ℤ => smearCoeff j * twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w :=
  Summable.of_norm_bounded ((hasSum_absTermBound hP).mul_right _).summable
    (norm_smearTerm_le hS hE hL hAct hG hP hC ν μ r ς hA hθ w)
include hS hE hL hAct hG hP hC in
theorem norm_smearedTwoPointCorrelation_le (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) :
    ‖smearedTwoPointCorrelation ν μ r ς A w‖ ≤ absCoeffSum * cubeReflectionNorm ν r A :=
  tsum_of_norm_bounded ((hasSum_absTermBound hP).mul_right _)
    (norm_smearTerm_le hS hE hL hAct hG hP hC ν μ r ς hA hθ w)
include hS hAct hG hP in
theorem smearedTwoPointCorrelation_neg (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) :
    smearedTwoPointCorrelation ν μ r ς A (-w) = conj (smearedTwoPointCorrelation ν μ r ς A w) := by
  rw [smearedTwoPointCorrelation, smearedTwoPointCorrelation, Complex.conj_tsum]
  refine tsum_congr fun j => ?_
  have hc : conj ((smearingSeq j : ℂ) * tentFourierCoeff j) =
      (smearingSeq j : ℂ) * tentFourierCoeff j :=
    Complex.conj_eq_iff_im.mpr (hP.2.2.2.2.2.1 j)
  rw [twoPointCorrelation_neg_transverse hS hAct hG ν μ r ς hA hθ, map_mul, hc]
theorem integrable_energyMomentumMonomial (hE : SpectralMeasuresTheorem) (μ : Fin 4)
    (σ : Measure (SpectralSpace μ)) [IsFiniteMeasure σ] (n : ℕ) (w : orthLattice μ) :
    Integrable (energyMomentumMonomial μ n w) σ :=
  Integrable.of_bound ((hE μ).1.2.2.2.2.2.1 n w).measurable.aestronglyMeasurable 1
    (ae_of_all _ (norm_energyMomentumMonomial_le μ n w))
def transversePhase (μ : Fin 4) (w : orthLattice μ) (x : SpectralSpace μ) : ℂ :=
  Complex.exp (Complex.I * (angleDot μ x.momentum (w : Fin 4 → ℤ) : ℂ))
include hS hE hL hAct hG hP hC hW in
theorem smearedTwoPointCorrelation_eq_integral (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) :
    smearedTwoPointCorrelation ν μ r ς A w =
      ∫ x, (smearedEnergyDensity μ r x : ℂ) * transversePhase μ w x
        ∂siteSpectralMeasure ν μ (cubeVector ν μ r A) := by
  set σ := siteSpectralMeasure ν μ (cubeVector ν μ r A) with hσ
  set t : ℤ → ℂ := fun j => smearCoeff j * twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w
    with ht
  have hsum : Summable t := summable_smearTerms hS hE hL hAct hG hP hC ν μ r ς hA hθ w
  have hs1 : Summable fun n : ℕ => t ((n : ℤ) + 1) :=
    hsum.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
  have heven : ∀ n : ℕ, t (-((n : ℤ) + 1)) = t ((n : ℤ) + 1) := fun n => by
    have e : 2 * (r : ℤ) * -((n : ℤ) + 1) = -(2 * (r : ℤ) * ((n : ℤ) + 1)) := by ring
    have hc : smearCoeff (-((n : ℤ) + 1)) = smearCoeff ((n : ℤ) + 1) :=
      hP.2.2.2.2.2.2.1 _
    simp only [ht]
    rw [e, twoPointCorrelation_neg hAct hG ν μ ς hA.1 hθ, hc]
  have hs2 : HasSum (fun n : ℕ => t (-((n : ℤ) + 1))) (∑' n : ℕ, t ((n : ℤ) + 1)) := by
    simp only [heven]
    exact hs1.hasSum
  have hK := (HasSum.of_add_one_of_neg_add_one hs1.hasSum hs2).tsum_eq
  have h0 : t 0 = 0 := by
    have e : smearCoeff 0 = 0 := hP.2.2.2.2.2.2.2
    simp only [ht]
    rw [e, zero_mul]
  rw [h0, add_zero] at hK
  set F : ℕ → SpectralSpace μ → ℂ := fun n x =>
    (2 * smearCoeff ((n : ℤ) + 1)) * energyMomentumMonomial μ (2 * (r : ℕ) * n) w x with hF
  have hint : ∀ n, Integrable (F n) σ := fun n =>
    (integrable_energyMomentumMonomial hE μ σ _ w).const_mul _
  have hbound : ∀ n x, ‖F n x‖ ≤ 2 * absTermBound ((n : ℤ) + 1) := fun n x => by
    simp only [hF]
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 := norm_energyMomentumMonomial_le μ (2 * (r : ℕ) * n) w x
    have h2 := norm_smearCoeff_le hC ((n : ℤ) + 1)
    calc 2 * ‖smearCoeff ((n : ℤ) + 1)‖ * ‖energyMomentumMonomial μ (2 * (r : ℕ) * n) w x‖
        ≤ 2 * ‖smearCoeff ((n : ℤ) + 1)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * absTermBound ((n : ℤ) + 1) := by linarith
  have hmaj : Summable fun n : ℕ => 2 * absTermBound ((n : ℤ) + 1) * σ.real univ :=
    (((hasSum_absTermBound hP).summable.comp_injective
      (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)).mul_left 2).mul_right _
  have hnorm : Summable fun n : ℕ => ∫ x, ‖F n x‖ ∂σ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) hmaj
    have h := norm_integral_le_of_norm_le_const (μ := σ) (f := fun x => ‖F n x‖)
      (C := 2 * absTermBound ((n : ℤ) + 1))
      (ae_of_all _ fun x => by rw [norm_norm]; exact hbound n x)
    exact (le_abs_self _).trans h
  have H := hasSum_integral_of_summable_integral_norm hint hnorm
  have hFn : ∀ n : ℕ, ∫ x, F n x ∂σ = 2 * t ((n : ℤ) + 1) := fun n => by
    simp only [hF]
    rw [integral_const_mul]
    have e : 2 * (r : ℤ) * ((n : ℤ) + 1) = 2 * (r : ℤ) + ((2 * (r : ℕ) * n : ℕ) : ℤ) := by
      push_cast
      ring
    simp only [ht]
    rw [e, twoPointCorrelation_eq_moment hS hE hL ν μ r ς hA hθ]
    ring
  simp only [hFn] at H
  have hpt : ∀ x, ∑' n, F n x = (smearedEnergyDensity μ r x : ℂ) * transversePhase μ w x :=
      fun x => by
    have hmem := expNegNatMulEnergy_mem_Icc (2 * (r : ℕ)) x.energy
    have hw := (hC.2.2.2.2.1 _ hmem).mul_right (transversePhase μ w x)
    rw [← ofReal_smearedEnergyDensity hW.2 μ r x] at hw
    rw [← hw.tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hF, energyMomentumMonomial, transversePhase, smearCoeff]
    have e : expNegNatMulEnergy (2 * (r : ℕ) * n) x.energy =
        expNegNatMulEnergy (2 * (r : ℕ)) x.energy ^ n := by
      simp only [expNegNatMulEnergy, pow_mul]
    rw [e]
    push_cast
    ring
  simp only [hpt] at H
  have h2 := hs1.hasSum.mul_left 2
  have huniq := H.unique h2
  rw [huniq]
  change ∑' j : ℤ, t j = _
  rw [hK]
  ring
theorem measurable_torusCharacter (w : orthLattice μ) :
    Measurable (torusCharacter μ w) := by
  have hb : Measurable (boxRep μ) :=
    measurable_pi_lambda _ fun l =>
      measurable_subtype_coe.comp
        ((AddCircle.measurableEquivIoc (2 * π) (-π)).measurable.comp (measurable_pi_apply l))
  have hd : Measurable fun η => angleDot μ (boxRep μ η) (w : Fin 4 → ℤ) :=
    Finset.measurable_sum _ fun l _ => ((measurable_pi_apply l).comp hb).mul_const _
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hd))
include hW in
theorem torusFourierCoeff_weightedMomentumLaw (σ : Measure (SpectralSpace μ))
    (w : orthLattice μ) :
    torusFourierCoeff μ (weightedMomentumLaw μ r σ) w =
      ∫ x, (smearedEnergyDensity μ r x : ℂ) * transversePhase μ w x ∂σ := by
  have hm : Measurable fun x => ENNReal.ofReal (smearedEnergyDensity μ r x) :=
    (measurable_smearedEnergyDensity hW.2 μ r).ennreal_ofReal
  rw [torusFourierCoeff, weightedMomentumLaw,
    integral_map (measurable_momentumProj μ).aemeasurable
      (measurable_torusCharacter μ w).aestronglyMeasurable, withDensityReal,
    integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hbox : boxRep μ (momentumProj μ x) = x.momentum :=
    boxRep_torusProj x.2
  simp only [torusCharacter, hbox, transversePhase]
  rw [ENNReal.toReal_ofReal (smearedEnergyDensity_nonneg hW.2 μ r x), Complex.real_smul]
include hW in
theorem isFiniteMeasure_weightedMomentumLaw (σ : Measure (SpectralSpace μ))
    [IsFiniteMeasure σ] : IsFiniteMeasure (weightedMomentumLaw μ r σ) := by
  have hi : Integrable (smearedEnergyDensity μ r) σ :=
    Integrable.of_bound (measurable_smearedEnergyDensity hW.2 μ r).aestronglyMeasurable
      (2 * absCoeffSum) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (smearedEnergyDensity_nonneg hW.2 μ r x)]
        exact smearedEnergyDensity_le hW.2 μ r x)
  have : IsFiniteMeasure (withDensityReal σ (smearedEnergyDensity μ r)) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  rw [weightedMomentumLaw]
  infer_instance
end Smearing
theorem norm_energyMomentumMonomial (μ : Fin 4) (n : ℕ) (w : orthLattice μ)
    (x : SpectralSpace μ) : ‖energyMomentumMonomial μ n w x‖ = expNegNatMulEnergy n x.energy := by
  have h := expNegNatMulEnergy_mem_Icc n x.energy
  rw [energyMomentumMonomial, norm_mul, Complex.norm_real, Complex.norm_exp_I_mul_ofReal, mul_one,
    Real.norm_eq_abs, abs_of_nonneg h.1]
theorem slopeConstant_pos : 0 < slopeConstant := by
  have h : 0 < Real.log (1 + √2) := Real.log_pos (by
    have : 0 < √2 := by positivity
    linarith)
  rw [slopeConstant]
  positivity
theorem norm_filterSeries_le (hW : SmearingFilter.Bounds.FilterWeightBounds) (u : ℝ) :
    ‖filterSeries u‖ ≤ 8 := by
  have h := hW.1.2.2.2.1 u
  rwa [hW.1.2.2.2.2.1] at h
theorem cone_decay_bound (hS : SiteReflectionPair.Conclusion)
    (hW : SmearingFilter.Bounds.FilterWeightBounds)
    (ν : unitPositiveClass) (l : Fin 4) (r : ℕ+) (m : TransverseAxis l) (n : ℕ)
    {x : SpectralSpace l} (hx : x ∈ coneInSpectral l) :
    expNegNatMulEnergy n x.energy * ‖filterSeries (2 * (r : ℝ) * x.momentum m)‖ ≤
      8 * Real.exp (-(correlationDecayRate r * n)) := by
  have hmem := expNegNatMulEnergy_mem_Icc n x.energy
  have hpos : 0 < 8 * Real.exp (-(correlationDecayRate r * n)) := by positivity
  set u := 2 * (r : ℝ) * x.momentum m with hu
  by_cases hz : filterSeries u = 0
  · rw [hz, norm_zero, mul_zero]
    exact hpos.le
  have hd : π / 4 < distTwoPiInt u := not_le.mp fun h => hz (hW.1.2.2.2.2.2 u h)
  have hdu : distTwoPiInt u ≤ |u| :=
    (isLeast_distTwoPiInt u).2 ⟨0, by simp⟩
  have habs : |u| = 2 * (r : ℝ) * |x.momentum m| := by
    rw [hu, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * r)]
  have hη : π / (8 * (r : ℝ)) ≤ |x.momentum m| := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hf := norm_filterSeries_le hW u
  suffices h : expNegNatMulEnergy n x.energy ≤ Real.exp (-(correlationDecayRate r * n)) by
    calc expNegNatMulEnergy n x.energy * ‖filterSeries u‖
        ≤ Real.exp (-(correlationDecayRate r * n)) * 8 :=
          mul_le_mul h hf (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  by_cases htop : x.energy = ⊤
  · rw [htop]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [expNegNatMulEnergy_zero]
    · rw [expNegNatMulEnergy_top hn]
      exact (Real.exp_pos _).le
  · have hc := ((hS ν l r).2.1.2.1 x.1 hx).2 htop
    have hsup : |x.momentum m| ≤ angleSupNorm l x.1.2 :=
      Finset.le_sup' (fun l' => |x.1.2 l'|) (Finset.mem_univ m)
    have hk := slopeConstant_pos
    have hα : correlationDecayRate r ≤ x.energy.toReal := by
      have e : correlationDecayRate r = slopeConstant * (π / (8 * (r : ℝ))) := by
        rw [correlationDecayRate]
        ring
      rw [e]
      calc slopeConstant * (π / (8 * (r : ℝ))) ≤ slopeConstant * angleSupNorm l x.1.2 :=
            mul_le_mul_of_nonneg_left (hη.trans hsup) hk.le
        _ ≤ x.energy.toReal := hc.2
    have e : expNegNatMulEnergy n x.energy = Real.exp (-(x.energy.toReal * n)) := by
      have h1 : ((expNegEnergy x.energy : unitInterval) : ℝ) = Real.exp (-x.energy.toReal) := by
        simp [expNegEnergy, htop]
      rw [expNegNatMulEnergy, h1, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [e]
    apply Real.exp_le_exp.mpr
    have : correlationDecayRate r * n ≤ x.energy.toReal * n :=
      mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg n)
    linarith
theorem spectralIntegral_finset_sum {ι : Type*} [DecidableEq ι] (p : ReflectionPair)
    (ν : unitPositiveClass) (l : Fin 4)
    (hlin : SpectralMeasures.IntegralLinear p ν l) (ψ ψ' : p.Hilb ν l)
    (s : Finset ι) (c : ι → ℂ) (f : ι → SpectralSpace l → ℂ)
    (hf : ∀ j, IsBoundedBorelFn (f j)) :
    IsBoundedBorelFn (∑ j ∈ s, c j • f j) ∧
      p.spectralIntegral ν l ψ ψ' (∑ j ∈ s, c j • f j) =
        ∑ j ∈ s, c j * p.spectralIntegral ν l ψ ψ' (f j) := by
  have hsm : ∀ j, IsBoundedBorelFn (c j • f j) := fun j => by
    obtain ⟨hmeas, C, hC⟩ := hf j
    refine ⟨hmeas.const_smul (c j), ‖c j‖ * C, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
  induction s using Finset.induction_on with
  | empty =>
    have h0 : IsBoundedBorelFn (0 : SpectralSpace l → ℂ) :=
      ⟨measurable_const, 0, fun _ => by simp⟩
    refine ⟨by simpa using h0, ?_⟩
    have h := hlin.2.1 ψ ψ' 0 0 h0
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨⟨m₁, C₁, h₁⟩, h₂⟩ := ih
    have hb : IsBoundedBorelFn (∑ j ∈ s, c j • f j) := ⟨m₁, C₁, h₁⟩
    obtain ⟨m₀, C₀, h₀⟩ := hsm a
    refine ⟨⟨m₀.add m₁, C₀ + C₁, fun x => ?_⟩, ?_⟩
    · rw [Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (h₀ x) (h₁ x))
    · rw [hlin.1 ψ ψ' _ _ (hsm a) hb, hlin.2.1 ψ ψ' _ _ (hf a), h₂]
theorem tendsto_Icc_neg_self :
    Tendsto (fun k : ℕ => Finset.Icc (-(k : ℤ)) k) atTop atTop :=
  tendsto_atTop_finset_of_monotone
    (fun a b h => Finset.Icc_subset_Icc (by simpa using h) (by simpa using h))
    (fun j => ⟨j.natAbs, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
theorem angleDot_orthProj_shiftAlong {μ l : Fin 4} (m : TransverseAxis l) (hm : m.1 = μ)
    (r : ℕ+) (j : ℤ) (w : Fin 4 → ℤ) (hμ : w μ = 0) (η : TransverseAxis l → ℝ) :
    angleDot l η (orthProj l (shiftAlong μ (2 * (r : ℤ) * j) w)).1 =
      angleDot l η (orthProj l w).1 + (j : ℝ) * (2 * (r : ℝ) * η m) := by
  have hne : μ ≠ l := hm ▸ m.2
  have hcoord : ∀ l' : TransverseAxis l,
      (((orthProj l (shiftAlong μ (2 * (r : ℤ) * j) w)).1 l'.1 : ℤ) : ℝ) =
        (((orthProj l w).1 l'.1 : ℤ) : ℝ) +
          (if l' = m then 2 * (r : ℝ) * j else 0) := by
    intro l'
    have h1 : l'.1 ≠ l := l'.2
    by_cases h : l' = m
    · subst h
      subst hm
      simp [orthProj, shiftAlong, h1]
      ring
    · have h2 : l'.1 ≠ μ := fun e => h (Subtype.ext (e.trans hm.symm))
      simp [orthProj, shiftAlong, h1, h, h2]
  simp only [angleDot, hcoord, mul_add, Finset.sum_add_distrib]
  simp
  ring
section Transverse
variable (hS : SiteReflectionPair.Conclusion)
  (hE : SpectralMeasuresTheorem)
  (hL : CubeVectorLinearity.Statement)
  (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
  (hG : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
  (hP : TriangleKernel.SeqAndTentProperties)
  (hC : SmearingFilter.SeriesConvergence.SeriesConverge)
  (hW : SmearingFilter.Bounds.FilterWeightBounds)
  (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
  {A : GaugeField (1 : ℝ) → ℂ}
include hS hE hL hAct hG hP hC hW in
theorem norm_smearedTwoPointCorrelation_le_of_coord
    (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) {l : Fin 4} (hl : l ≠ μ) (hw : 2 * (r : ℤ) ≤ w.1 l) :
    ‖smearedTwoPointCorrelation ν μ r ς A w‖ ≤
      8 * Real.exp (-(correlationDecayRate r * ((w.1 l : ℝ) - 2 * (r : ℝ)))) *
        cubeReflectionNorm ν r A := by
  set n := (w.1 l - 2 * (r : ℤ)).toNat with hn
  have hnr : (n : ℝ) = (w.1 l : ℝ) - 2 * (r : ℝ) := by
    have h : (n : ℤ) = w.1 l - 2 * (r : ℤ) := Int.toNat_of_nonneg (by omega)
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    exact h'
  rw [← hnr]
  let m : TransverseAxis l := ⟨μ, hl.symm⟩
  set ψ := cubeVector ν l r ((siteReflect l).actOn A) with hψ
  set ψ' := cubeVector ν l r A with hψ'
  obtain ⟨-, -, hlin, -, hbd, hcont, hcar, -, -⟩ := (hE l).2.2 ν ReflectionPair.site
  let mono : ℤ → SpectralSpace l → ℂ := fun j =>
    energyMomentumMonomial l n (orthProj l (shiftAlong μ (2 * (r : ℤ) * j) w.1))
  have hy : ∀ j : ℤ, shiftAlong μ (2 * (r : ℤ) * j) w.1 l = w.1 l := fun j => by
    simp [shiftAlong, hl]
  have hg : ∀ j : ℤ, twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w =
      ((ς : ℤ) : ℂ) * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j) := fun j => by
    rw [twoPointCorrelation_eq_pairCorrelation,
      pairCorrelation_eq_spectralIntegral hS hE ν l r hA _ (by rw [hy j]; exact hw), hy j]
  have hb : ∀ j, IsBoundedBorelFn (mono j) := fun j =>
    ⟨((hE l).1.2.2.2.2.2.1 _ _).measurable, 1, norm_energyMomentumMonomial_le l _ _⟩
  let B := energyMomentumMonomial l n (orthProj l w.1)
  let u : SpectralSpace l → ℝ := fun x => 2 * (r : ℝ) * x.momentum m
  have hmono : ∀ (j : ℤ) (x : SpectralSpace l),
      mono j x = B x * Complex.exp (Complex.I * j * (u x : ℝ)) := fun j x => by
    simp only [mono, B, u, energyMomentumMonomial]
    rw [angleDot_orthProj_shiftAlong m rfl r j w.1 w.2 x.momentum]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring_nf
  have hum : Measurable u :=
    ((hE l).1.2.2.2.2.2.2.2.2.2.2.2.1 m).const_mul _
  let φ : SpectralSpace l → ℂ := fun x => B x * filterSeries (u x)
  have hφ : IsBoundedBorelFn φ := by
    refine ⟨((hE l).1.2.2.2.2.2.1 _ _).measurable.mul (hW.1.2.1.measurable.comp hum), 8,
      fun x => ?_⟩
    simp only [φ]
    rw [norm_mul]
    calc ‖B x‖ * ‖filterSeries (u x)‖ ≤ 1 * 8 :=
          mul_le_mul (norm_energyMomentumMonomial_le l _ _ x) (norm_filterSeries_le hW _)
            (norm_nonneg _) zero_le_one
      _ = 8 := one_mul _
  let fs : Finset ℤ → SpectralSpace l → ℂ := fun s => ∑ j ∈ s, smearCoeff j • mono j
  have hfs : ∀ (s : Finset ℤ) (x : SpectralSpace l), fs s x = B x * ∑ j ∈ s,
      (smearingSeq j : ℂ) * tentFourierCoeff j *
        Complex.exp (Complex.I * j * (u x : ℝ)) := fun s x => by
    simp only [fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hmono, smearCoeff,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hunif : TendstoUniformly (fun k : ℕ => fs (Finset.Icc (-(k : ℤ)) k)) φ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h1 := Metric.tendstoUniformly_iff.mp hC.2.1.2.2.2 ε hε
    filter_upwards [tendsto_Icc_neg_self.eventually h1] with k hk x
    have h2 := hk (u x)
    rw [dist_eq_norm] at h2
    rw [hfs, dist_eq_norm, ← mul_sub, norm_mul]
    calc ‖B x‖ * _ ≤ 1 * _ :=
          mul_le_mul_of_nonneg_right (norm_energyMomentumMonomial_le l _ _ x) (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact h2
  have hsums := fun s : Finset ℤ =>
    spectralIntegral_finset_sum ReflectionPair.site ν l hlin ψ ψ' s smearCoeff mono hb
  have hlim := hcont ψ ψ' φ (fun k => fs (Finset.Icc (-(k : ℤ)) k)) hφ
    (fun k => (hsums _).1) hunif
  have hsum := summable_smearTerms hS hE hL hAct hG hP hC ν μ r ς hA hθ w
  have hS2 : HasSum
      (fun j => smearCoeff j * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j))
      (((ς : ℤ) : ℂ) * smearedTwoPointCorrelation ν μ r ς A w) := by
    have h := hsum.hasSum.mul_left ((ς : ℤ) : ℂ)
    have e : (fun j : ℤ => ((ς : ℤ) : ℂ) *
          (smearCoeff j * twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w)) =
        fun j => smearCoeff j * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j) := by
      funext j
      rw [hg j]
      linear_combination
        (smearCoeff j * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j)) *
          unit_cast_mul_self ς
    rw [e] at h
    exact h
  have hlim2 : Tendsto (fun k : ℕ => ∑ j ∈ Finset.Icc (-(k : ℤ)) k,
      smearCoeff j * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j)) atTop
      (𝓝 (((ς : ℤ) : ℂ) * smearedTwoPointCorrelation ν μ r ς A w)) :=
    (show Tendsto (fun s : Finset ℤ => ∑ j ∈ s,
        smearCoeff j * ReflectionPair.site.spectralIntegral ν l ψ ψ' (mono j)) atTop _ from
      hS2).comp tendsto_Icc_neg_self
  have hIφ : ReflectionPair.site.spectralIntegral ν l ψ ψ' φ =
      ((ς : ℤ) : ℂ) * smearedTwoPointCorrelation ν μ r ς A w := by
    refine tendsto_nhds_unique hlim ?_
    refine hlim2.congr fun k => ?_
    exact ((hsums _).2).symm
  have hcm : MeasurableSet (coneInSpectral l) :=
    ((hE l).1.2.2.2.2.2.2.1).measurableSet
  have hbound := hbd ψ ψ' φ hφ (coneInSpectral l) hcm hcar
  have hexp : 0 ≤ 8 * Real.exp (-(correlationDecayRate r * n)) := by positivity
  have hsup : sSup ((fun x => ‖φ x‖) '' coneInSpectral l) ≤
      8 * Real.exp (-(correlationDecayRate r * n)) := by
    refine Real.sSup_le ?_ hexp
    rintro _ ⟨x, hx, rfl⟩
    simp only [φ, B]
    rw [norm_mul, norm_energyMomentumMonomial]
    exact cone_decay_bound hS hW ν l r m n hx
  have hab : ‖ψ‖ * ‖ψ'‖ ≤ cubeReflectionNorm ν r A := by
    have h1 := sq_norm_cubeVector_reflect_le ν l r A
    have h2 := sq_norm_cubeVector_le hS hAct ν l r hA
    nlinarith [sq_nonneg (‖ψ‖ - ‖ψ'‖)]
  have hnorm : ‖smearedTwoPointCorrelation ν μ r ς A w‖ =
      ‖ReflectionPair.site.spectralIntegral ν l ψ ψ' φ‖ := by
    rw [hIφ, norm_mul]
    rcases Int.units_eq_one_or ς with e | e <;> simp [e]
  rw [hnorm]
  calc ‖ReflectionPair.site.spectralIntegral ν l ψ ψ' φ‖
      ≤ sSup ((fun x => ‖φ x‖) '' coneInSpectral l) * ‖ψ‖ * ‖ψ'‖ := hbound
    _ = sSup ((fun x => ‖φ x‖) '' coneInSpectral l) * (‖ψ‖ * ‖ψ'‖) := mul_assoc _ _ _
    _ ≤ 8 * Real.exp (-(correlationDecayRate r * n)) * (‖ψ‖ * ‖ψ'‖) :=
        mul_le_mul_of_nonneg_right hsup (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hab hexp
include hS hE hL hAct hG hP hC hW in
theorem norm_smearedTwoPointCorrelation_decay (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hθ : (siteReflect μ).actOn A = fun U => ((ς : ℤ) : ℂ) * A U)
    (w : orthLattice μ) (hw : 2 * (r : ℝ) ≤ supNormCoord (fun l => (w.1 l : ℝ))) :
    ‖smearedTwoPointCorrelation ν μ r ς A w‖ ≤
      8 * Real.exp (-(correlationDecayRate r *
        (supNormCoord (fun l => (w.1 l : ℝ)) - 2 * (r : ℝ)))) *
        cubeReflectionNorm ν r A := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun l => |(w.1 l : ℝ)|)
  have hmax : supNormCoord (fun l => (w.1 l : ℝ)) = |(w.1 l : ℝ)| := hl
  have hr : (0 : ℝ) < r := by exact_mod_cast r.pos
  rw [hmax] at hw ⊢
  have hne : l ≠ μ := by
    rintro rfl
    have h0 : w.1 l = 0 := w.2
    simp [h0] at hw
    linarith
  rcases le_or_gt 0 (w.1 l) with h0 | h0
  · have hc : (0 : ℝ) ≤ (w.1 l : ℝ) := by exact_mod_cast h0
    rw [abs_of_nonneg hc] at hw ⊢
    have hz : 2 * (r : ℤ) ≤ w.1 l := by
      have : ((2 * (r : ℤ) : ℤ) : ℝ) ≤ (w.1 l : ℝ) := by push_cast; exact hw
      exact_mod_cast this
    exact norm_smearedTwoPointCorrelation_le_of_coord hS hE hL hAct hG hP hC hW ν μ r ς hA hθ w
      hne hz
  · have hc : (w.1 l : ℝ) < 0 := by exact_mod_cast h0
    rw [abs_of_neg hc] at hw ⊢
    have hz : 2 * (r : ℤ) ≤ (-w).1 l := by
      have : ((2 * (r : ℤ) : ℤ) : ℝ) ≤ ((-w.1 l : ℤ) : ℝ) := by push_cast; exact hw
      exact_mod_cast this
    have h := norm_smearedTwoPointCorrelation_le_of_coord hS hE hL hAct hG hP hC hW ν μ r ς hA
      hθ (-w) hne hz
    rw [smearedTwoPointCorrelation_neg hS hAct hG hP ν μ r ς hA hθ, RCLike.norm_conj] at h
    have e : (((-w).1 l : ℤ) : ℝ) = -(w.1 l : ℝ) := by
      change ((-(w.1 l) : ℤ) : ℝ) = _
      push_cast
      rfl
    rwa [e] at h
end Transverse
theorem statement_holds
    (hS : SiteReflectionPair.Conclusion)
    (hE : SpectralMeasuresTheorem)
    (hF : SummableFourierCoeffTheorem)
    (hN : TransverseCounting.TransverseSumBound)
    (hL : CubeVectorLinearity.Statement)
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hG : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
    (hP : TriangleKernel.SeqAndTentProperties)
    (hC : SmearingFilter.SeriesConvergence.SeriesConverge)
    (hW : SmearingFilter.Bounds.FilterWeightBounds) :
    Statement := by
  refine ⟨?_, ?_⟩
  · have hz : 0 ≤ absCoeffSum := tsum_nonneg (absTermBound_nonneg hP)
    have hk := slopeConstant_pos
    have hpi := Real.pi_pos
    have h1 : 0 < 26624 / (slopeConstant * π) := by positivity
    have h2 : 0 < 3407872 / (slopeConstant * π) ^ 3 := by positivity
    rw [spectralDensityConst]
    exact mul_pos (zpow_pos (by positivity) _) (by linarith)
  · intro ν μ r ς A hA hθ
    have hN₀ := cubeReflectionNorm_nonneg_of_mem hS hAct ν μ r hA
    set M := siteMomentumLaw ν μ r A with hM
    have hfin : IsFiniteMeasure M := isFiniteMeasure_weightedMomentumLaw hW μ r _
    have hκ : ∀ w, torusFourierCoeff μ M w = smearedTwoPointCorrelation ν μ r ς A w :=
      fun w => (torusFourierCoeff_weightedMomentumLaw hW μ r _ w).trans
        (smearedTwoPointCorrelation_eq_integral hS hE hL hAct hG hP hC hW ν μ r ς hA hθ w).symm
    obtain ⟨hsum, hle⟩ := (hN μ r _ hN₀).2 (smearedTwoPointCorrelation ν μ r ς A)
      (fun w _ => norm_smearedTwoPointCorrelation_le hS hE hL hAct hG hP hC ν μ r ς hA hθ w)
      (fun w hw =>
        norm_smearedTwoPointCorrelation_decay hS hE hL hAct hG hP hC hW ν μ r ς hA hθ w hw)
    have hfun : (fun w => ‖torusFourierCoeff μ M w‖) =
        fun w => ‖smearedTwoPointCorrelation ν μ r ς A w‖ := funext fun w => by rw [hκ]
    obtain ⟨-, -, hc, hdens, hb⟩ := hF μ M (by rw [hfun]; exact hsum)
    refine ⟨hfin, fun η => (torusFourierSeries μ M η).re, Complex.continuous_re.comp hc, hdens,
      fun η => ⟨(hb η).2.1, ?_⟩⟩
    refine (hb η).2.2.trans ?_
    rw [tsum_congr fun w => by rw [hκ w]]
    have hpi : (0 : ℝ) < (2 * π) ^ 3 := by positivity
    calc ((2 * π) ^ 3)⁻¹ * ∑' w, ‖smearedTwoPointCorrelation ν μ r ς A w‖
        ≤ ((2 * π) ^ 3)⁻¹ *
            ((2 * π) ^ 3 * spectralDensityConst * (r : ℝ) ^ 3 * cubeReflectionNorm ν r A) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by
          field_simp
end YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound
