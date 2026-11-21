import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacingProof
import YangMills.Construction.ReflectionPositivity.HomogeneityOfDegreeZeroOfTheLaw
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry Link
  IsBoundedObservable regionObservables scaledCube axisStep shift plateauPairing pullToUnit pushToUnit
  gaugeFieldRescale gaugeFieldUnrescale gaugeFieldEquivUnit linkOfUnit linkToUnit pointOfUnit
  pointToUnit pointToUnit_axisStep pointToUnit_pointOfUnit continuous_gaugeFieldRescale
  continuous_gaugeFieldUnrescale)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb linfNorm)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet cubeHalfWidth)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
  (TransportsMeasuresAndSymmetries)
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
namespace SpacingInvariance
variable {a b : ℝ}
theorem symmetry_ext {t : ℝ} {f g : LatticeSymmetry t} (h : f.toFun = g.toFun) : f = g := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem rescale_unrescale (hb : 0 < b) (U : GaugeField 1) :
    gaugeFieldRescale b (gaugeFieldUnrescale hb U) = U :=
  (gaugeFieldEquivUnit hb).apply_symm_apply U
theorem unrescale_rescale (hb : 0 < b) (U : GaugeField b) :
    gaugeFieldUnrescale hb (gaugeFieldRescale b U) = U :=
  (gaugeFieldEquivUnit hb).symm_apply_apply U
theorem isBoundedObservable_conj_mul {t : ℝ} {F G : GaugeField t → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => conj (F U) * G U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.isBoundedObservable_conj_mul <;> assumption
theorem linfNorm_smul {t : ℝ} (ht : 0 ≤ t) (x : AmbientSpace) : linfNorm (t • x) = t * linfNorm x := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    have h : |(t • x) μ| = t * |x μ| := by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
    rw [h]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)) ht
  · obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun μ => |x μ|)
    have h : t * linfNorm x = |(t • x) μ| := by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
      exact congrArg (t * ·) hμ
    rw [h]
    exact Finset.le_sup' (fun μ => |(t • x) μ|) (Finset.mem_univ μ)
theorem pullToUnit_comp_respace (ha : 0 < a) (hb : 0 < b) (F : GaugeField a → ℂ) :
    pullToUnit hb (F ∘ respace b ha) = pullToUnit ha F := by
  funext U
  change F (gaugeFieldUnrescale ha
    (gaugeFieldRescale b (gaugeFieldUnrescale hb U))) = _
  rw [rescale_unrescale]
  rfl
theorem pullToUnit_injective (hb : 0 < b) {X Y : GaugeField b → ℂ}
    (h : pullToUnit hb X = pullToUnit hb Y) : X = Y := by
  funext U
  have := congrFun h (gaugeFieldRescale b U)
  change X (gaugeFieldUnrescale hb _) = Y (gaugeFieldUnrescale hb _) at this
  rwa [unrescale_rescale] at this
theorem pushToUnit_respaceState (hb : 0 < b) (ν : BorelProb a) :
    pushToUnit (respaceState hb ν).1 = pushToUnit ν.1 := by
  change (ν.1.map (respace a hb)).map (gaugeFieldRescale b) =
    ν.1.map (gaugeFieldRescale a)
  have hm : Measurable (respace a hb) :=
    ((continuous_gaugeFieldUnrescale hb).comp
      (continuous_gaugeFieldRescale a)).measurable
  refine (Measure.map_map (continuous_gaugeFieldRescale b).measurable hm).trans ?_
  congr 1
  funext U
  exact rescale_unrescale hb _
theorem toUnit_respaceState (hb : 0 < b) (ν : BorelProb a) :
    BorelProb.toUnit (respaceState hb ν) = BorelProb.toUnit ν :=
  Subtype.ext (pushToUnit_respaceState hb ν)
theorem unitRepresentative_congr {ν : Measure (GaugeField a)} {ν' : Measure (GaugeField b)}
    (h : pushToUnit ν' = pushToUnit ν) :
    unitRepresentative ν' = unitRepresentative ν := by
  by_cases hm : pushToUnit ν ∈ unitPositiveClass
  · have hm' : pushToUnit ν' ∈ unitPositiveClass := h ▸ hm
    exact Subtype.ext ((coe_unitRepresentative hm').trans
      (h.trans (coe_unitRepresentative hm).symm))
  · have hm' : pushToUnit ν' ∉ unitPositiveClass := h ▸ hm
    rw [unitRepresentative, dif_neg hm', unitRepresentative, dif_neg hm]
theorem pullToUnit_shift (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (v : LatticePoint a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((shift v).actOn F) =
      (shift (pointToUnit ha v)).actOn (pullToUnit ha F) := by
  rw [hM.2.2.1 (shift v) F hF, symmetry_ext (hM.2.2.2.1 v)]
theorem pullToUnit_coordinateReflect (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (μ : Fin 4)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((LatticeAtSpacing.coordinateReflect a μ).actOn F) =
      (MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.pullToUnit_coordinateReflect <;> assumption
theorem pullToUnit_axisReflection (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (γ : axisReflectionGroup) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((axisReflectionGroup.toLatticeSymmetry a γ).actOn F) =
      (axisReflectionGroup.toUnitLatticeSymmetry γ).actOn (pullToUnit ha F) := by
  have e₀ : axisReflectionGroup.toLatticeSymmetry a γ =
      LatticeAtSpacing.axisReflectionSymmetry a γ := symmetry_ext rfl
  rw [hM.2.2.1 _ F hF, e₀,
    symmetry_ext (g := axisReflectionGroup.toUnitLatticeSymmetry γ) (hM.2.2.2.2.2.2.1 γ)]
theorem pointToUnit_nsmul_axisStep (ha : 0 < a) (k : ℕ) (μ : Fin 4) :
    pointToUnit ha (k • axisStep a μ) = k • axisStep 1 μ := by
  rw [map_nsmul, pointToUnit_axisStep]
theorem scaledCubeVector_eq (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (ν : Measure (GaugeField a)) (μ : Fin 4) (r : ℕ+) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) :
    ScaledPair.cubeVector ν μ ha r F =
      cubeVector (unitRepresentative ν) μ r (pullToUnit ha F) := by
  rw [ScaledPair.cubeVector, ScaledPair.obsClass,
    pullToUnit_shift ha hM _ hF, pointToUnit_nsmul_axisStep, cubeVector]
theorem reflectionSize_eq (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (ν : BorelProb a)
    (r : ℕ+) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    reflectionSize ha ν r F = cubeReflectionNorm (unitRepresentative ν.1) r (pullToUnit ha F) := by
  rw [reflectionSize, scaledCubeReflectionSize, cubeReflectionNorm, scaledCubeVectorNormsSq,
    cubeVectorSqNorms]
  congr 2
  funext p
  rw [scaledCubeVector_eq ha hM ν.1 p.1 r (hF.actOn _), pullToUnit_axisReflection ha hM p.2 hF]
def unitDecayForm (ρ : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
    (X : GaugeField (1 : ℝ) → ℂ) (m : ℕ) : ℂ :=
  inner ℂ (cubeVector ρ μ r X)
    ((ReflectionPair.site.transferOp ρ μ ^ m * (1 - groundProjection μ ReflectionPair.site ρ))
      (cubeVector ρ μ r X))
theorem transferDecayForm_eq (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (ν : BorelProb a)
    (μ : Fin 4) (r : ℕ+) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (m : ℕ) :
    transferDecayForm ha ν μ r F m =
      unitDecayForm (unitRepresentative ν.1) μ r (pullToUnit ha F) m := by
  rw [transferDecayForm, scaledCubeVector_eq ha hM ν.1 μ r hF]
  rfl
theorem cubeReflectedCorrelation_eq (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (ν : BorelProb a) (μ : Fin 4) (r : ℕ+) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    cubeReflectedCorrelation ν μ r F =
      (BorelProb.toUnit ν).integral fun U =>
        conj ((MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F) U) *
          (shift ((2 * (r : ℕ)) • axisStep (1 : ℝ) μ)).actOn (pullToUnit ha F) U := by
  have h := hM.2.1 ν _ (isBoundedObservable_conj_mul
    (hF.actOn (LatticeAtSpacing.coordinateReflect a μ))
    (hF.actOn (shift ((2 * (r : ℕ)) • axisStep a μ))))
  rw [cubeReflectedCorrelation, CoarseStepsInverseSquare.reflectedCorrelation]
  refine h.symm.trans ?_
  congr 1
  funext U
  change conj (pullToUnit ha ((LatticeAtSpacing.coordinateReflect a μ).actOn F) U) *
    pullToUnit ha ((shift ((2 * (r : ℕ)) • axisStep a μ)).actOn F) U = _
  rw [pullToUnit_coordinateReflect ha hM μ hF, pullToUnit_shift ha hM _ hF, pointToUnit_nsmul_axisStep]
theorem shiftedCorrelation_eq (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (ν : BorelProb a)
    {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hG : IsBoundedObservable G)
    (y : LatticePoint a) :
    shiftedCorrelation ν F G y =
      (BorelProb.toUnit ν).integral fun U =>
        conj (pullToUnit ha F U) *
          (shift (pointToUnit ha y)).actOn (pullToUnit ha G) U := by
  have h := hM.2.1 ν _ (isBoundedObservable_conj_mul hF (hG.actOn (shift y)))
  rw [shiftedCorrelation]
  refine h.symm.trans ?_
  congr 1
  funext U
  change conj (pullToUnit ha F U) * pullToUnit ha ((shift y).actOn G) U = _
  rw [pullToUnit_shift ha hM _ hG]
theorem pointToUnit_respacePoint (ha : 0 < a) (hb : 0 < b) (y : LatticePoint a) :
    pointToUnit hb (respacePoint ha b y) = pointToUnit ha y :=
  pointToUnit_pointOfUnit hb _
theorem respacePoint_coe (ha : 0 < a) (b : ℝ) (y : LatticePoint a) :
    (respacePoint ha b y).1 = (b / a) • y.1 := by
  change b • (a⁻¹ • y.1) = _
  rw [smul_smul, div_eq_mul_inv]
theorem cubeGap_respacePoint (ha : 0 < a) (hb : 0 < b) (r : ℕ+) (y : LatticePoint a) :
    cubeGap b r (respacePoint ha b y) = cubeGap a r y := by
  rw [cubeGap, cubeGap, respacePoint_coe, linfNorm_smul (div_pos hb ha).le]
  congr 1
  field_simp
theorem respaceInvertible (ha : 0 < a) (hb : 0 < b) : RespaceInvertible ha hb := by
  refine ⟨fun U e e' ht hh => ?_, fun U => ?_, fun U => ?_⟩
  · change U (linkOfUnit a (linkToUnit hb e)) = U e'
    have key : ∀ x : LatticePoint b, ∀ x' : LatticePoint a,
        (x'.1 : AmbientSpace) = (a / b) • (x.1 : AmbientSpace) →
        pointOfUnit a (pointToUnit hb x) = x' := fun x x' h => by
      refine Subtype.ext ?_
      change a • (b⁻¹ • x.1) = x'.1
      rw [h, smul_smul, div_eq_mul_inv]
    have : linkOfUnit a (linkToUnit hb e) = e' :=
      Link.ext (key _ _ ht) (key _ _ hh)
    rw [this]
  · change gaugeFieldUnrescale ha (gaugeFieldRescale b
      (gaugeFieldUnrescale hb (gaugeFieldRescale a U))) = U
    rw [rescale_unrescale, unrescale_rescale]
  · change gaugeFieldUnrescale hb (gaugeFieldRescale a
      (gaugeFieldUnrescale ha (gaugeFieldRescale b U))) = U
    rw [rescale_unrescale, unrescale_rescale]
theorem cubeGap_eq (ha : 0 < a) (r : ℕ+) (y : LatticePoint a) :
    cubeGap a r y = (linfNorm y.1 - 2 * cubeHalfWidth a r) / a := by
  rw [cubeGap, cubeHalfWidth]
  field_simp
end SpacingInvariance
open SpacingInvariance in
theorem SpacingInvariance.holds_of_unitScaling
    (hD : LatticeAtSpacing.UnitScaling.UnitScalingDictionary) :
    SpacingInvariance.Holds := by
  intro a ha ν hν r A hA B hB μ b hb y
  have hMa := (hD a ha).2.1
  have hMb := (hD b hb).2.1
  have hAo : IsBoundedObservable A := hA.1
  have hBo : IsBoundedObservable B := hB.1
  have hflat := toUnit_respaceState hb ν
  have hc := unitRepresentative_congr (pushToUnit_respaceState hb ν)
  have hν' : respaceState hb ν ∈ reflectionPositiveSet b := by
    have h1 := (((hD a ha).2.2.2.1 ν).2.2.2.2).1 hν
    refine (((hD b hb).2.2.2.1 (respaceState hb ν)).2.2.2.2).2 ?_
    rw [hflat]
    exact h1
  have hcube : ∀ X ∈ regionObservables a (scaledCube a r),
      X ∘ respace b ha ∈ regionObservables b (scaledCube b r) := by
    intro X hX
    have hSa := (hD a ha).1.2.2.2.2.2.2.2.2 r
    have hSb := (hD b hb).1.2.2.2.2.2.2.2.2 r
    have h1 : pullToUnit ha X ∈ pullToUnit hb '' regionObservables b (scaledCube b r) := by
      rw [hSb, ← hSa]
      exact Set.mem_image_of_mem _ hX
    obtain ⟨X', hX', he⟩ := h1
    have : X' = X ∘ respace b ha :=
      pullToUnit_injective hb (he.trans (pullToUnit_comp_respace ha hb X).symm)
    exact this ▸ hX'
  have hA' := hcube A hA
  have hB' := hcube B hB
  have hAo' : IsBoundedObservable (A ∘ respace b ha) := hA'.1
  have hBo' : IsBoundedObservable (B ∘ respace b ha) := hB'.1
  have hfA := pullToUnit_comp_respace ha hb A
  have hfB := pullToUnit_comp_respace ha hb B
  have hsteps := cubeGap_respacePoint ha hb r y
  have hsizeA : reflectionSize hb (respaceState hb ν) r (A ∘ respace b ha) = reflectionSize ha ν r A := by
    rw [reflectionSize_eq hb hMb _ r hAo', reflectionSize_eq ha hMa _ r hAo, hfA, hc]
  have hsizeB : reflectionSize hb (respaceState hb ν) r (B ∘ respace b ha) = reflectionSize ha ν r B := by
    rw [reflectionSize_eq hb hMb _ r hBo', reflectionSize_eq ha hMa _ r hBo, hfB, hc]
  have hTI := hν.1
  have hTI' := hν'.1
  have hpl : plateauPairing (respaceState hb ν).1 (A ∘ respace b ha) (B ∘ respace b ha) =
      plateauPairing ν.1 A B := by
    have h1 := (((hD a ha).2.2.2.2.2.2.2 ν).2.2 hTI A B hAo hBo).2
    have h2 := (((hD b hb).2.2.2.2.2.2.2 (respaceState hb ν)).2.2 hTI' _ _ hAo' hBo').2
    rw [h1, h2, hflat, hfA, hfB]
  have hcorr : shiftedCorrelation (respaceState hb ν) (A ∘ respace b ha)
      (B ∘ respace b ha) (respacePoint ha b y) = shiftedCorrelation ν A B y := by
    rw [shiftedCorrelation_eq hb hMb _ hAo' hBo', shiftedCorrelation_eq ha hMa _ hAo hBo, hflat, hfA, hfB,
      pointToUnit_respacePoint]
  refine ⟨respaceInvertible ha hb, hν', hA', hB', respacePoint_coe ha b y, hsteps,
    ⟨?_, ?_, hsizeA, fun m _ => ⟨?_, by rw [hsizeA]⟩, fun _ => ⟨by rw [hcorr, hpl], ?_⟩⟩, ?_, ?_⟩
  · rw [cubeVecNorm, cubeVecNorm, scaledCubeVector_eq hb hMb _ μ r hAo',
      scaledCubeVector_eq ha hMa _ μ r hAo, hfA]
    exact congrArg (fun ρ : unitPositiveClass =>
      ‖cubeVector ρ μ r (pullToUnit ha A)‖ ^ 2) hc
  · rw [cubeReflectedCorrelation_eq hb hMb _ μ r hAo', cubeReflectedCorrelation_eq ha hMa _ μ r hAo, hflat, hfA]
  · rw [transferDecayForm_eq hb hMb _ μ r hAo', transferDecayForm_eq ha hMa _ μ r hAo, hfA, hc]
  · rw [hsteps, reflectionSizeRoots, reflectionSizeRoots, hsizeA, hsizeB]
  · rw [cubeGap_eq ha r y, ne_eq, div_eq_zero_iff, not_or, sub_eq_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, ha.ne'⟩⟩
  · intro h
    have hne : linfNorm y.1 - 2 * cubeHalfWidth a r ≠ 0 := by
      intro h0
      apply h
      rw [cubeGap_eq ha r y, h0, zero_div]
    rw [cubeGap_eq ha r y, cubeHalfWidth] at *
    field_simp
end YangMills.Construction.ReflectionPositivity.DirectionPictures
