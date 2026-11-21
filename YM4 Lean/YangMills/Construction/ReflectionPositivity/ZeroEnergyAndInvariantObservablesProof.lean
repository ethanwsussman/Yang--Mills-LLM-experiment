import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirectionProof
import YangMills.Construction.InfiniteLattice.ConditionalExpectationsOnTheUnitLattice
import YangMills.Construction.InfiniteLattice.InvariantFunctionsOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LocalObservablesDetermineMeasuresAndIsometriesOnIntegrableFunctions
import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import YangMills.Construction.ReflectionPositivity.MatrixElementsAreCorrelations
import YangMills.Construction.ReflectionPositivity.ReflectionsCarrierAndZeroEnergyOfTheLinkPicture
import YangMills.Construction.ReflectionPositivity.ZeroEnergyAndInvariantObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint IsBoundedObservable IsLocalObservable
  LatticeSymmetry UnitLatticeSymmetry IsSymmetricUnder axisStep shift halfSpaceLocalObservables
  shiftInvariantSigma axisShiftInvariantSigma condExpGiven axisMultiples ShiftPair)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect linkPlane)
open YangMills.Construction.FormHilbert (IsOrthProjOnto subFieldL2)
namespace GroundStateProof
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem eq_zero_of_mem_closure_of_inner_eq_zero {A : Set E} {D : E} (hD : D ∈ closure A)
    (h : ∀ x ∈ A, inner ℂ x D = 0) : D = 0 := by
  have hc : IsClosed {x : E | inner ℂ x D = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have h₀ : inner ℂ D D = 0 := closure_minimal (s := A) h hc hD
  exact inner_self_eq_zero.mp h₀
theorem inner_eq_of_tendsto_birkhoffAverage (f : E → E) (c x y : E) (L : ℂ)
    (hu : Tendsto (fun k : ℕ => inner ℂ c (f^[k] x)) atTop (𝓝 L))
    (hy : Tendsto (fun n : ℕ => birkhoffAverage ℂ f _root_.id n x) atTop (𝓝 y)) :
    inner ℂ c y = L := by
  have h₁ : Tendsto (fun n : ℕ => inner ℂ c (birkhoffAverage ℂ f _root_.id n x)) atTop
      (𝓝 (inner ℂ c y)) :=
    ((continuous_const.inner continuous_id).tendsto y).comp hy
  have h₂ := hu.cesaro_smul
  refine tendsto_nhds_unique h₁ (h₂.congr fun n => ?_)
  simp only [birkhoffAverage, birkhoffSum, inner_smul_right, inner_sum, _root_.id]
  rw [Complex.real_smul]
  push_cast
  rfl
theorem inner_map_left_of_involutive (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ a, V (V a) = a) (a b : E) :
    inner ℂ (V a) b = inner ℂ a (V b) := by
  calc inner ℂ (V a) b = inner ℂ (V a) (V (V b)) := by rw [hV]
    _ = inner ℂ a (V b) := V.inner_map_map _ _
theorem eq_self_of_involutive_of_nonneg (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ a, V (V a) = a) {M : Set E}
    (hsub : ∀ a ∈ M, ∀ b ∈ M, a - b ∈ M) (hst : ∀ a ∈ M, V a ∈ M)
    (hpos : ∀ a ∈ M, 0 ≤ (inner ℂ (V a) a).re) {J : E} (hJ : J ∈ M) : V J = J := by
  have hKM : J - V J ∈ M := hsub _ hJ _ (hst _ hJ)
  have hVK : V (J - V J) = -(J - V J) := by
    rw [map_sub, hV, neg_sub]
  have h := hpos _ hKM
  rw [hVK, inner_neg_left, Complex.neg_re] at h
  have h₂ : (inner ℂ (J - V J) (J - V J)).re = ‖J - V J‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [h₂] at h
  have h₃ : ‖J - V J‖ = 0 := by nlinarith [norm_nonneg (J - V J)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h₃)).symm
variable [CompleteSpace E]
theorem inner_starProjection_left {P : E →L[ℂ] E} (hP : IsStarProjection P) (a b : E) :
    inner ℂ (P a) b = inner ℂ a (P b) :=
  ((YangMills.Construction.FormHilbert.isSelfAdjoint_iff_inner_eq P).mp hP.isSelfAdjoint a b).symm
theorem starProjection_apply_of_mem_range {P : E →L[ℂ] E} (hP : IsStarProjection P) {a : E}
    (ha : a ∈ Set.range P) : P a = a := by
  obtain ⟨b, rfl⟩ := ha
  exact congrArg (fun T : E →L[ℂ] E => T b) hP.isIdempotentElem.eq
theorem starProjection_eq_of_inner_eq {P : E →L[ℂ] E} (hP : IsStarProjection P) {x y : E}
    (h : ∀ w ∈ Set.range P, inner ℂ w x = inner ℂ w y) : P x = P y := by
  have hD : P (x - y) ∈ Set.range P := ⟨_, rfl⟩
  have h₀ : inner ℂ (P (x - y)) (P (x - y)) = 0 := by
    rw [← inner_starProjection_left hP, starProjection_apply_of_mem_range hP hD, inner_sub_right,
      h _ hD, sub_self]
  have := inner_self_eq_zero.mp h₀
  rw [map_sub] at this
  exact sub_eq_zero.mp this
theorem tendsto_birkhoffAverage_starProjection (V : E ≃ₗᵢ[ℂ] E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hfix : ∀ J, J ∈ Set.range P ↔ V J = J) (x : E) :
    Tendsto (fun n : ℕ => birkhoffAverage ℂ V _root_.id n x) atTop (𝓝 (P x)) := by
  let f : E →L[ℂ] E := V.toLinearIsometry.toContinuousLinearMap
  have hf : ‖f‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by simp [f]
  have h := f.tendsto_birkhoffAverage_orthogonalProjection hf x
  have hK : ∀ w, w ∈ f.eqLocus (1 : E →L[ℂ] E) ↔ w ∈ Set.range P := fun w => by
    rw [hfix w]
    exact Iff.rfl
  have e : (((f.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto x :
      f.eqLocus (1 : E →L[ℂ] E)) : E) = P x := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      ((hK _).mpr ⟨x, rfl⟩) fun w hw => ?_
    have hw' := (hK w).mp hw
    rw [inner_sub_left, inner_starProjection_left hP, starProjection_apply_of_mem_range hP hw',
      sub_self]
  rw [e] at h
  exact h
end Hilbert
theorem shift_comp_shift (v w : LatticePoint (1 : ℝ)) :
    (shift v).comp (shift w) = shift (v + w) := by
  apply YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext
  funext x
  change x + (w : InfiniteLattice.AmbientSpace) + (v : InfiniteLattice.AmbientSpace) =
    x + ((v + w : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace)
  rw [AddSubgroup.coe_add, add_assoc, add_comm (w : InfiniteLattice.AmbientSpace)]
theorem shift_neg_isInverse (v : LatticePoint (1 : ℝ)) : (shift (-v)).IsInverse (shift v) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change x + (v : InfiniteLattice.AmbientSpace) +
      ((-v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) = x
    simp
  · change x + ((-v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) +
      (v : InfiniteLattice.AmbientSpace) = x
    simp
theorem shift_zero_actOn (F : GaugeField (1 : ℝ) → ℂ) :
    (shift (0 : LatticePoint (1 : ℝ))).actOn F = F := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ReflectionPairProof.translateObs_zero <;> assumption
theorem mem_of_axisStep_mem (S : AddSubgroup (LatticePoint (1 : ℝ))) (h : ∀ i, axisStep 1 i ∈ S)
    (v : LatticePoint (1 : ℝ)) : v ∈ S := by
  obtain ⟨n, hn⟩ := v.2
  have hv : v = ∑ i, n i • axisStep 1 i := by
    apply Subtype.ext
    funext μ
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, hn μ, Finset.sum_eq_single μ]
    · simp [axisStep]
    · intro i _ hi
      simp [axisStep, Pi.single_eq_of_ne (Ne.symm hi)]
    · simp
  rw [hv]
  exact sum_mem fun i _ => zsmul_mem (h i) _
section Action
variable (m : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure m]
def l2Class {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) : Lp ℂ 2 m :=
  (MemLp.of_bound hF.1.aestronglyMeasurable hF.2.choose
    (Eventually.of_forall hF.2.choose_spec)).toLp F
theorem l2Class_ae_eq {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    ⇑(l2Class m hF) =ᵐ[m] F :=
  MemLp.coeFn_toLp _
variable {m}
omit [IsProbabilityMeasure m] in
theorem inner_eq_integral_of_ae_eq {x y : Lp ℂ 2 m} {A B : GaugeField (1 : ℝ) → ℂ}
    (hx : ⇑x =ᵐ[m] A) (hy : ⇑y =ᵐ[m] B) : inner ℂ x y = ∫ U, conj (A U) * B U ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hx, hy] with U h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply, mul_comm]
variable (hAct : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
  (hMeas : InfiniteLattice.LocalDeterminationAndIntegrableAction)
  (hInv : InfiniteLattice.ShiftInvariantFunctions.InvariantFunctionsTheorem)
  (hm : ∀ r : UnitLatticeSymmetry, IsSymmetricUnder m r)
include hAct in
theorem measurable_actOn (r : UnitLatticeSymmetry) {J : GaugeField (1 : ℝ) → ℂ}
    (hJ : Measurable J) : Measurable (r.actOn J) :=
  hAct.2.2.2.2.2.2.2.1 r J hJ
include hAct in
theorem isBoundedObservable_actOn (r : UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (r.actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_actOn <;> assumption
include hAct in
theorem comp_actOn (r r' : UnitLatticeSymmetry) {J : GaugeField (1 : ℝ) → ℂ}
    (hJ : Measurable J) :
    (r.comp r').actOn J = r.actOn (r'.actOn J) :=
  (hAct.2.2.2.2.2.2.1 r r' J J hJ hJ).1
include hAct in
theorem actOn_of_isInverse {r t : UnitLatticeSymmetry} (ht : t.IsInverse r)
    {J : GaugeField (1 : ℝ) → ℂ} (hJ : Measurable J) :
    t.actOn (r.actOn J) = J :=
  (hAct.2.2.2.2.2.2.1 r r J J hJ hJ).2.1 t ht
include hMeas in
theorem actOn_ae_congr {r : UnitLatticeSymmetry} (hr : IsSymmetricUnder m r)
    {J J' : GaugeField (1 : ℝ) → ℂ} (hJ : Measurable J) (hJ' : Measurable J')
    (h : J =ᵐ[m] J') : r.actOn J =ᵐ[m] r.actOn J' :=
  ((hMeas m r).2.2.2 hr).2.2.1 J J' hJ hJ' h
include hMeas in
theorem exists_linearIsometryEquiv {r t : UnitLatticeSymmetry} (ht : t.IsInverse r)
    (hr : IsSymmetricUnder m r) :
    ∃ V : Lp ℂ 2 m ≃ₗᵢ[ℂ] Lp ℂ 2 m, (∀ J, ⇑(V J) =ᵐ[m] r.actOn ⇑J) ∧
      ∀ J, ⇑(V.symm J) =ᵐ[m] t.actOn ⇑J := by
  obtain ⟨V, hV, h₁, h₂⟩ := ((hMeas m r).2.2.2 hr).2.2.2
  exact ⟨V.isometryOfInner hV.2, h₁, fun J => h₂ t ht J⟩
omit [IsProbabilityMeasure m] in
theorem measurable_coeFn (J : Lp ℂ 2 m) : Measurable (⇑J) :=
  (Lp.stronglyMeasurable J).measurable
include hAct hMeas in
theorem linearIsometryEquiv_l2Class {r : UnitLatticeSymmetry} (hr : IsSymmetricUnder m r)
    {V : Lp ℂ 2 m ≃ₗᵢ[ℂ] Lp ℂ 2 m} (hV : ∀ J, ⇑(V J) =ᵐ[m] r.actOn ⇑J)
    {G : GaugeField (1 : ℝ) → ℂ} (hG : IsBoundedObservable G) :
    V (l2Class m hG) = l2Class m (isBoundedObservable_actOn hAct r hG) := by
  apply Lp.ext
  refine (hV _).trans ?_
  exact (actOn_ae_congr hMeas hr (measurable_coeFn _) hG.1 (l2Class_ae_eq m hG)).trans
    (l2Class_ae_eq m _).symm
include hAct hMeas hm in
def shiftStabilizer {J : GaugeField (1 : ℝ) → ℂ} (hJ : Measurable J) :
    AddSubgroup (LatticePoint (1 : ℝ)) where
  carrier := {v | (shift v).actOn J =ᵐ[m] J}
  add_mem' := by
    intro v w hv hw
    have hv' : (shift v).actOn J =ᵐ[m] J := hv
    have hw' : (shift w).actOn J =ᵐ[m] J := hw
    change (shift (v + w)).actOn J =ᵐ[m] J
    rw [← shift_comp_shift, comp_actOn hAct _ _ hJ]
    exact (actOn_ae_congr hMeas (hm _)
      (measurable_actOn hAct _ hJ) hJ hw').trans hv'
  zero_mem' := by
    change (shift 0).actOn J =ᵐ[m] J
    rw [shift_zero_actOn]
  neg_mem' := by
    intro v hv
    have hv' : (shift v).actOn J =ᵐ[m] J := hv
    change (shift (-v)).actOn J =ᵐ[m] J
    have h := actOn_ae_congr hMeas (hm (shift (-v)))
      (measurable_actOn hAct _ hJ) hJ hv'
    rw [actOn_of_isInverse hAct (shift_neg_isInverse v) hJ] at h
    exact h.symm
def axisFixedClasses (m : Measure (GaugeField (1 : ℝ))) (μ : Fin 4) : Set (Lp ℂ 2 m) :=
  subFieldL2 m (axisShiftInvariantSigma μ)
    (InfiniteLattice.axisShiftInvariantSigma_le_borel μ)
include hMeas hInv hm in
theorem mem_axisFixedClasses_iff (μ : Fin 4) (J : Lp ℂ 2 m) :
    J ∈ axisFixedClasses m μ ↔
      ∀ v ∈ axisMultiples μ, (shift v).actOn ⇑J =ᵐ[m] ⇑J := by
  constructor
  · rintro ⟨g, hg, hae⟩ v hv
    have bg : Measurable g :=
      hg.mono (InfiniteLattice.axisShiftInvariantSigma_le_borel μ) le_rfl
    have hτ : (shift v).actOn g = g :=
      (hInv.1 (.axis μ) g bg).mp hg v hv
    have h := actOn_ae_congr hMeas (hm (shift v)) (measurable_coeFn J) bg hae
    rw [hτ] at h
    exact h.trans hae.symm
  · intro h
    obtain ⟨J', h₁, h₂⟩ := (hInv.2 m).1 (.axis μ) ⇑J (measurable_coeFn J) h
    exact ⟨J', h₁, h₂.symm⟩
include hAct hMeas hInv hm in
theorem linearIsometryEquiv_mem_axisFixedClasses (μ : Fin 4) {r : UnitLatticeSymmetry}
    {V : Lp ℂ 2 m ≃ₗᵢ[ℂ] Lp ℂ 2 m} (hV : ∀ J, ⇑(V J) =ᵐ[m] r.actOn ⇑J)
    (σ : LatticePoint (1 : ℝ) → LatticePoint (1 : ℝ))
    (hσ : ∀ v ∈ axisMultiples μ, σ v ∈ axisMultiples μ ∧
      (shift v).comp r = r.comp (shift (σ v)))
    {J : Lp ℂ 2 m} (hJ : J ∈ axisFixedClasses m μ) : V J ∈ axisFixedClasses m μ := by
  rw [mem_axisFixedClasses_iff hMeas hInv hm] at hJ ⊢
  intro v hv
  obtain ⟨hs, hc⟩ := hσ v hv
  have mJ := measurable_coeFn J
  have h₁ : (shift v).actOn ⇑(V J) =ᵐ[m] (shift v).actOn (r.actOn ⇑J) :=
    actOn_ae_congr hMeas (hm _) (measurable_coeFn _)
      (measurable_actOn hAct _ mJ) (hV J)
  have h₂ : (shift v).actOn (r.actOn ⇑J) = r.actOn ((shift (σ v)).actOn ⇑J) := by
    rw [← comp_actOn hAct _ _ mJ, hc, comp_actOn hAct _ _ mJ]
  have h₃ : r.actOn ((shift (σ v)).actOn ⇑J) =ᵐ[m] r.actOn ⇑J :=
    actOn_ae_congr hMeas (hm _) (measurable_actOn hAct _ mJ) mJ (hJ _ hs)
  rw [h₂] at h₁
  exact h₁.trans (h₃.trans (hV J).symm)
include hAct hMeas hInv hm in
theorem mem_axisFixedClasses_iff_apply_eq (μ : Fin 4) {V : Lp ℂ 2 m ≃ₗᵢ[ℂ] Lp ℂ 2 m}
    (hV : ∀ J, ⇑(V J) =ᵐ[m] (shift (axisStep 1 μ)).actOn ⇑J) (J : Lp ℂ 2 m) :
    J ∈ axisFixedClasses m μ ↔ V J = J := by
  rw [mem_axisFixedClasses_iff hMeas hInv hm]
  constructor
  · intro h
    exact Lp.ext ((hV J).trans (h _ ⟨1, by simp⟩))
  · intro h
    have hs : axisStep 1 μ ∈ shiftStabilizer hAct hMeas hm (measurable_coeFn J) := by
      have := hV J
      rw [h] at this
      exact this.symm
    rintro v ⟨k, rfl⟩
    exact zsmul_mem hs k
def halfSpaceL2Classes (m : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure m] (μ : Fin 4) :
    Set (Lp ℂ 2 m) :=
  {x | ∃ H ∈ halfSpaceLocalObservables μ, ∃ hH : IsBoundedObservable H, x = l2Class m hH}
theorem isBoundedObservable_of_mem_halfSpace {μ : Fin 4} {H : GaugeField (1 : ℝ) → ℂ}
    (hH : H ∈ halfSpaceLocalObservables μ) : IsBoundedObservable H :=
  ((InfiniteLattice.mem_halfSpaceLocalObservables_iff μ H).mp hH).1.1
include hInv hm in
theorem axisFixedClasses_subset_closure (μ : Fin 4) :
    axisFixedClasses m μ ⊆ closure (halfSpaceL2Classes m μ) := by
  intro J hJ
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨H, -, hH, hL, hn⟩ := (hInv.2 m).2 μ (hm _) J hJ (ε / 2) (half_pos hε)
  refine ⟨l2Class m (isBoundedObservable_of_mem_halfSpace hH), ⟨H, hH, _, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hn (half_lt_self hε)
include hAct in
theorem shift_actOn_mem_halfSpace {μ l : Fin 4} (hl : l ≠ μ) {H : GaugeField (1 : ℝ) → ℂ}
    (hH : H ∈ halfSpaceLocalObservables μ) :
    (shift (axisStep 1 l)).actOn H ∈ halfSpaceLocalObservables μ := by
  obtain ⟨h₁, h₂⟩ := (InfiniteLattice.mem_halfSpaceLocalObservables_iff μ H).mp hH
  have hset : (shift (axisStep 1 l)).setImage (InfiniteLattice.closedHalfSpace μ) =
      InfiniteLattice.closedHalfSpace μ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : 0 ≤ y μ := hy
      change 0 ≤ (y + (axisStep 1 l : InfiniteLattice.AmbientSpace)) μ
      simpa [InfiniteLattice.axisStep, Pi.single_eq_of_ne (Ne.symm hl)] using hy'
    · intro hx
      have hx' : 0 ≤ x μ := hx
      refine ⟨x - (axisStep 1 l : InfiniteLattice.AmbientSpace), ?_, ?_⟩
      · change 0 ≤ (x - (axisStep 1 l : InfiniteLattice.AmbientSpace)) μ
        simpa [InfiniteLattice.axisStep, Pi.single_eq_of_ne (Ne.symm hl)] using hx'
      · change x - (axisStep 1 l : InfiniteLattice.AmbientSpace) +
          (axisStep 1 l : InfiniteLattice.AmbientSpace) = x
        simp
  have himg := hAct.2.1 (shift (axisStep 1 l)) (InfiniteLattice.closedHalfSpace μ)
  rw [hset] at himg
  refine (InfiniteLattice.mem_halfSpaceLocalObservables_iff μ _).mpr ⟨?_, ?_⟩
  · rw [← himg]
    exact ⟨H, h₁, rfl⟩
  · exact (hAct.2.2.2.2.1 _ H h₁.1).2.2 h₂
end Action
section Core
theorem measurable_indicator_one_of_measurableSet (𝓕 : MeasurableSpace (GaugeField (1 : ℝ)))
    {I : Set (GaugeField (1 : ℝ))} (h : MeasurableSet[𝓕] I) :
    Measurable[𝓕] (I.indicator (1 : GaugeField (1 : ℝ) → ℂ)) := by
  let _ := 𝓕
  exact Measurable.indicator measurable_one h
variable {m : Measure (GaugeField (1 : ℝ))} [IsProbabilityMeasure m]
theorem groundState_of_limitForm
    (hAct : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hMeas : InfiniteLattice.LocalDeterminationAndIntegrableAction)
    (hInv : InfiniteLattice.ShiftInvariantFunctions.InvariantFunctionsTheorem)
    (hCond : InfiniteLattice.UnitLatticeCondExp.UnitLatticeCondExpProperties)
    (hm : ∀ r : UnitLatticeSymmetry, IsSymmetricUnder m r) (μ : Fin 4)
    (Z : (GaugeField (1 : ℝ) → ℂ) → (GaugeField (1 : ℝ) → ℂ) → ℂ)
    (Z₁ : ∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ,
      Tendsto (fun k : ℕ => ∫ U, conj ((linkReflect μ).actOn F U) *
        (shift (k • axisStep 1 μ)).actOn H U ∂m) atTop (𝓝 (Z F H)))
    (Z₂ : ∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ, ∀ l : Fin 4,
      l ≠ μ → Z F ((shift (axisStep 1 l)).actOn H) = Z F H)
    (Z₃ : ∀ F ∈ halfSpaceLocalObservables μ,
      0 ≤ (∫ U, conj ((linkReflect μ).actOn F U) * F U ∂m).re) :
    (∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F → ∀ v : LatticePoint (1 : ℝ),
      condExpGiven m (shiftInvariantSigma 1) ((linkReflect μ).actOn F) =ᵐ[m]
        condExpGiven m (shiftInvariantSigma 1) F ∧
      condExpGiven m (shiftInvariantSigma 1) F =ᵐ[m]
        condExpGiven m (shiftInvariantSigma 1) ((shift v).actOn F)) ∧
    (∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ,
      Z F H = ∫ U, conj (condExpGiven m (shiftInvariantSigma 1) F U) *
        condExpGiven m (shiftInvariantSigma 1) H U ∂m) ∧
    (∀ J : GaugeField (1 : ℝ) → ℂ, Measurable[axisShiftInvariantSigma μ] J → MemLp J 2 m →
      ∃ J' : GaugeField (1 : ℝ) → ℂ, Measurable[shiftInvariantSigma 1] J' ∧ J =ᵐ[m] J') ∧
    (∀ I' : Set (GaugeField (1 : ℝ)), MeasurableSet[axisShiftInvariantSigma μ] I' →
      ∃ I : Set (GaugeField (1 : ℝ)), MeasurableSet[shiftInvariantSigma 1] I ∧
        m (symmDiff I I') = 0) ∧
    (∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
      condExpGiven m (axisShiftInvariantSigma μ) F =ᵐ[m]
        condExpGiven m (shiftInvariantSigma 1) F) := by
  have hle : axisShiftInvariantSigma μ ≤ borel (GaugeField (1 : ℝ)) :=
    InfiniteLattice.axisShiftInvariantSigma_le_borel μ
  have hleI : shiftInvariantSigma 1 ≤ borel (GaugeField (1 : ℝ)) := fun _ h => h.1
  have hIle : shiftInvariantSigma 1 ≤ axisShiftInvariantSigma μ := hAct.2.2.1 μ
  have hce : ∀ {𝓕 : MeasurableSpace (GaugeField (1 : ℝ))} {B B' : GaugeField (1 : ℝ) → ℂ},
      B =ᵐ[m] B' → condExpGiven m 𝓕 B =ᵐ[m] condExpGiven m 𝓕 B' :=
    fun h => condExp_congr_ae h
  have hθinv : (linkReflect μ).IsInverse (linkReflect μ) := by
    have h := (hAct.2.2.2.2.2.2.2.2.1 (linkPlane μ)).2.1
    exact ⟨fun x => congrFun h x, fun x => congrFun h x⟩
  obtain ⟨Vμ, hVμ, -⟩ := exists_linearIsometryEquiv hMeas (shift_neg_isInverse (axisStep 1 μ)) (hm _)
  obtain ⟨Vθ, hVθ, hVθ'⟩ := exists_linearIsometryEquiv hMeas hθinv (hm (linkReflect μ))
  obtain ⟨-, -, ⟨-, ⟨P, hP, hPc⟩, -, -, -⟩, -⟩ := hCond m (axisShiftInvariantSigma μ) hle
  have hrange : Set.range P = axisFixedClasses m μ := hP.2
  have hmem : ∀ a, P a ∈ axisFixedClasses m μ := fun a => hrange ▸ ⟨a, rfl⟩
  have hfixP : ∀ J ∈ axisFixedClasses m μ, P J = J := fun J hJ =>
    starProjection_apply_of_mem_range hP.1 (hrange.symm ▸ hJ)
  have hcl := axisFixedClasses_subset_closure (m := m) hInv hm μ
  have hsub : ∀ a ∈ axisFixedClasses m μ, ∀ b ∈ axisFixedClasses m μ,
      a - b ∈ axisFixedClasses m μ := by
    intro a ha b hb
    rw [← hrange]
    exact ⟨a - b, by rw [map_sub, hfixP a ha, hfixP b hb]⟩
  have hmeans := tendsto_birkhoffAverage_starProjection Vμ hP.1 (fun J => by
    rw [hrange]
    exact mem_axisFixedClasses_iff_apply_eq hAct hMeas hInv hm μ hVμ J)
  have hpow : ∀ {H : GaugeField (1 : ℝ) → ℂ} (hH : IsBoundedObservable H) (k : ℕ),
      ⇑((⇑Vμ)^[k] (l2Class m hH)) =ᵐ[m] (shift (k • axisStep 1 μ)).actOn H := by
    intro H hH k
    induction k with
    | zero => simpa [shift_zero_actOn] using l2Class_ae_eq m hH
    | succ k ih =>
      rw [Function.iterate_succ_apply', succ_nsmul', ← shift_comp_shift,
        comp_actOn hAct _ _ hH.1]
      exact (hVμ _).trans (actOn_ae_congr hMeas (hm _) (measurable_coeFn _)
        (measurable_actOn hAct _ hH.1) ih)
  have hstep2 : ∀ F (hF : F ∈ halfSpaceLocalObservables μ) H (hH : H ∈ halfSpaceLocalObservables μ),
      inner ℂ (Vθ (l2Class m (isBoundedObservable_of_mem_halfSpace hF)))
        (P (l2Class m (isBoundedObservable_of_mem_halfSpace hH))) = Z F H := by
    intro F hF H hH
    refine inner_eq_of_tendsto_birkhoffAverage (⇑Vμ) _ _ _ _ ?_ (hmeans _)
    refine (Z₁ F hF H hH).congr fun k => ?_
    rw [linearIsometryEquiv_l2Class hAct hMeas (hm _) hVθ]
    exact (inner_eq_integral_of_ae_eq (l2Class_ae_eq m _) (hpow _ k)).symm
  have hVV : ∀ a, Vθ (Vθ a) = a := fun a => by
    have h : Vθ.symm a = Vθ a := Lp.ext ((hVθ' a).trans (hVθ a).symm)
    rw [← h]
    exact Vθ.apply_symm_apply a
  have hθcomm : ∀ v ∈ axisMultiples μ, -v ∈ axisMultiples μ ∧
      (shift v).comp (linkReflect μ) = (linkReflect μ).comp (shift (-v)) := by
    rintro v ⟨k, rfl⟩
    refine ⟨⟨-k, by simp⟩, ?_⟩
    refine ((hAct.2.2.2.2.2.2.2.2.1 (linkPlane μ)).2.2.2.2.2.2.2 k _ ?_).symm
    funext i
    simp [InfiniteLattice.axisStep, linkPlane,
      YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.basisVec]
  have hθst : ∀ a ∈ axisFixedClasses m μ, Vθ a ∈ axisFixedClasses m μ := fun a ha =>
    linearIsometryEquiv_mem_axisFixedClasses hAct hMeas hInv hm μ hVθ (fun v => -v) hθcomm ha
  have hpos : ∀ a ∈ axisFixedClasses m μ, 0 ≤ (inner ℂ (Vθ a) a).re := by
    intro a ha
    have hc : IsClosed {x : Lp ℂ 2 m | 0 ≤ (inner ℂ (Vθ x) x).re} :=
      isClosed_le continuous_const
        (Complex.continuous_re.comp (Vθ.continuous.inner continuous_id))
    refine closure_minimal ?_ hc (hcl ha)
    rintro _ ⟨H, hH, hO, rfl⟩
    change 0 ≤ (inner ℂ (Vθ (l2Class m hO)) (l2Class m hO)).re
    rw [linearIsometryEquiv_l2Class hAct hMeas (hm _) hVθ hO,
      inner_eq_integral_of_ae_eq (l2Class_ae_eq m _) (l2Class_ae_eq m _)]
    exact Z₃ H hH
  have hθfix : ∀ J ∈ axisFixedClasses m μ, Vθ J = J := fun J hJ =>
    eq_self_of_involutive_of_nonneg Vθ hVV hsub hθst hpos hJ
  have hstep4 : ∀ F (hF : F ∈ halfSpaceLocalObservables μ) H (hH : H ∈ halfSpaceLocalObservables μ),
      Z F H = inner ℂ (l2Class m (isBoundedObservable_of_mem_halfSpace hF))
        (P (l2Class m (isBoundedObservable_of_mem_halfSpace hH))) := by
    intro F hF H hH
    rw [← hstep2 F hF H hH, inner_map_left_of_involutive Vθ hVV, hθfix _ (hmem _)]
  have hPV : ∀ a, P (Vθ a) = P a := fun a => starProjection_eq_of_inner_eq hP.1 fun w hw => by
    rw [← inner_map_left_of_involutive Vθ hVV, hθfix w (hrange ▸ hw)]
  have hstep5 : ∀ H (hH : H ∈ halfSpaceLocalObservables μ) (l : Fin 4) (hl : l ≠ μ),
      P (l2Class m (isBoundedObservable_of_mem_halfSpace (shift_actOn_mem_halfSpace hAct hl hH))) =
        P (l2Class m (isBoundedObservable_of_mem_halfSpace hH)) := by
    intro H hH l hl
    have hτ := shift_actOn_mem_halfSpace hAct hl hH
    refine sub_eq_zero.mp
      (eq_zero_of_mem_closure_of_inner_eq_zero (hcl (hsub _ (hmem _) _ (hmem _))) ?_)
    rintro _ ⟨F, hF, hO, rfl⟩
    rw [inner_sub_right, ← hstep4 F hF _ hτ, ← hstep4 F hF H hH, Z₂ F hF H hH l hl, sub_self]
  have hstab : ∀ J ∈ axisFixedClasses m μ, ∀ l : Fin 4, l ≠ μ →
      axisStep 1 l ∈ shiftStabilizer hAct hMeas hm (measurable_coeFn J) := by
    intro J hJ l hl
    obtain ⟨Vl, hVl, hVl'⟩ :=
      exists_linearIsometryEquiv hMeas (shift_neg_isInverse (axisStep 1 l)) (hm _)
    have hst : Vl.symm J ∈ axisFixedClasses m μ :=
      linearIsometryEquiv_mem_axisFixedClasses hAct hMeas hInv hm μ hVl' id
        (fun v hv => ⟨hv, by rw [shift_comp_shift, shift_comp_shift, add_comm, id]⟩) hJ
    have hD : Vl.symm J - J = 0 := by
      refine eq_zero_of_mem_closure_of_inner_eq_zero (hcl (hsub _ hst _ hJ)) ?_
      rintro _ ⟨H, hH, hO, rfl⟩
      have hτ := shift_actOn_mem_halfSpace hAct hl hH
      have e₁ : inner ℂ (l2Class m (isBoundedObservable_of_mem_halfSpace hτ)) J =
          inner ℂ (P (l2Class m (isBoundedObservable_of_mem_halfSpace hτ))) J := by
        rw [inner_starProjection_left hP.1, hfixP J hJ]
      have e₂ : inner ℂ (l2Class m hO) J = inner ℂ (P (l2Class m hO)) J := by
        rw [inner_starProjection_left hP.1, hfixP J hJ]
      rw [inner_sub_right, ← LinearIsometryEquiv.inner_map_eq_flip,
        linearIsometryEquiv_l2Class hAct hMeas (hm _) hVl hO]
      change inner ℂ (l2Class m (isBoundedObservable_of_mem_halfSpace hτ)) J - _ = 0
      rw [e₁, e₂, hstep5 H hH l hl, sub_self]
    have hJ' : Vl.symm J = J := sub_eq_zero.mp hD
    have hn : -axisStep 1 l ∈ shiftStabilizer hAct hMeas hm (measurable_coeFn J) := by
      have h := hVl' J
      rw [hJ'] at h
      exact h.symm
    simpa using neg_mem hn
  have hI : ∀ J ∈ axisFixedClasses m μ,
      ∃ g : GaugeField (1 : ℝ) → ℂ, Measurable[shiftInvariantSigma 1] g ∧ ⇑J =ᵐ[m] g := by
    intro J hJ
    have hall : ∀ v, v ∈ shiftStabilizer hAct hMeas hm (measurable_coeFn J) :=
      mem_of_axisStep_mem _ fun i => by
        by_cases hi : i = μ
        · subst hi
          exact (mem_axisFixedClasses_iff hMeas hInv hm i J).mp hJ _ ⟨1, by simp⟩
        · exact hstab J hJ i hi
    obtain ⟨J', h₁, h₂⟩ := (hInv.2 m).1 .allShifts ⇑J (measurable_coeFn J)
      (fun v _ => hall v)
    exact ⟨J', h₁, h₂.symm⟩
  have hc3 : ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
      condExpGiven m (axisShiftInvariantSigma μ) F =ᵐ[m]
        condExpGiven m (shiftInvariantSigma 1) F := by
    intro F hF
    have h₁ : ⇑(P (l2Class m hF)) =ᵐ[m] condExpGiven m (axisShiftInvariantSigma μ) F :=
      (hPc _).trans (hce (l2Class_ae_eq m hF))
    obtain ⟨g, hg, hae⟩ := hI _ (hmem (l2Class m hF))
    have hgi : Integrable g m := ((Lp.memLp (P (l2Class m hF))).integrable one_le_two).congr hae
    have h₂ : condExp (shiftInvariantSigma 1) m g = g :=
      condExp_of_stronglyMeasurable hleI hg.stronglyMeasurable hgi
    have h₃ : condExp (shiftInvariantSigma 1) m (condExp (axisShiftInvariantSigma μ) m F) =ᵐ[m]
        condExp (shiftInvariantSigma 1) m F := condExp_condExp_of_le hIle hle
    have h₄ : condExp (shiftInvariantSigma 1) m (condExp (axisShiftInvariantSigma μ) m F) =ᵐ[m]
        condExp (shiftInvariantSigma 1) m g := condExp_congr_ae (h₁.symm.trans hae)
    rw [h₂] at h₄
    exact h₁.symm.trans (hae.trans (h₄.symm.trans h₃))
  have hint : ∀ {F : GaugeField (1 : ℝ) → ℂ}, IsBoundedObservable F → Integrable F m := fun hF =>
    ((Lp.memLp (l2Class m hF)).integrable one_le_two).congr (l2Class_ae_eq m hF)
  refine ⟨fun F hF v => ⟨?_, ?_⟩, fun F hF H hH => ?_, fun J hJ hL => ?_, fun I' hI' => ?_, hc3⟩
  · have hθF := isBoundedObservable_actOn hAct (linkReflect μ) hF
    have h₁ : ⇑(P (l2Class m hθF)) =ᵐ[m] condExpGiven m (axisShiftInvariantSigma μ)
        ((linkReflect μ).actOn F) := (hPc _).trans (hce (l2Class_ae_eq m hθF))
    have h₂ : ⇑(P (l2Class m hF)) =ᵐ[m] condExpGiven m (axisShiftInvariantSigma μ) F :=
      (hPc _).trans (hce (l2Class_ae_eq m hF))
    have e : P (l2Class m hθF) = P (l2Class m hF) := by
      rw [← linearIsometryEquiv_l2Class hAct hMeas (hm _) hVθ hF, hPV]
    rw [e] at h₁
    exact (hc3 _ hθF).symm.trans (h₁.symm.trans (h₂.trans (hc3 F hF)))
  · have hEm : Measurable[shiftInvariantSigma 1] (condExpGiven m (shiftInvariantSigma 1) F) :=
      stronglyMeasurable_condExp.measurable
    have hτ := (hInv.1 .allShifts _ (hEm.mono hleI le_rfl)).mp hEm v trivial
    have hcomm := (hCond m (shiftInvariantSigma 1) hleI).2.2.2 (shift v) (shift (-v))
      (shift_neg_isInverse v) (hm _) (fun I hIm => ?_) F (hint hF)
    · rw [hτ] at hcomm
      exact hcomm.symm
    · have hi : Measurable[shiftInvariantSigma 1] (I.indicator (1 : GaugeField (1 : ℝ) → ℂ)) :=
        measurable_indicator_one_of_measurableSet _ hIm
      refine ⟨?_, ?_⟩
      · rw [hIm.2 v]
        exact hi
      · rw [hIm.2 (-v)]
        exact hi
  · have hFo := isBoundedObservable_of_mem_halfSpace hF
    have hHo := isBoundedObservable_of_mem_halfSpace hH
    have h₁ : ⇑(P (l2Class m hHo)) =ᵐ[m] condExpGiven m (shiftInvariantSigma 1) H :=
      ((hPc _).trans (hce (l2Class_ae_eq m hHo))).trans (hc3 H hHo)
    rw [hstep4 F hF H hH, inner_eq_integral_of_ae_eq (l2Class_ae_eq m hFo) h₁]
    have hmF : MemLp F 2 m := (Lp.memLp (l2Class m hFo)).ae_eq (l2Class_ae_eq m hFo)
    have hmH : MemLp H 2 m := (Lp.memLp (l2Class m hHo)).ae_eq (l2Class_ae_eq m hHo)
    exact ((hCond m (shiftInvariantSigma 1) hleI).2.2.1.2.2.2.2 F H hmF hmH).2.2.2.1.symm
  · have hx : ⇑(hL.toLp J) =ᵐ[m] J := MemLp.coeFn_toLp hL
    obtain ⟨g, hg, hae⟩ := hI (hL.toLp J) ⟨J, hJ, hx⟩
    exact ⟨g, hg, hx.symm.trans hae⟩
  · have hind : Measurable[axisShiftInvariantSigma μ]
        (I'.indicator (1 : GaugeField (1 : ℝ) → ℂ)) :=
      measurable_indicator_one_of_measurableSet _ hI'
    have hobs : IsBoundedObservable (I'.indicator (1 : GaugeField (1 : ℝ) → ℂ)) := by
      refine ⟨hind.mono hle le_rfl, 1, fun U => ?_⟩
      by_cases h : U ∈ I' <;> simp [h]
    obtain ⟨g, hg, hae⟩ := hI (l2Class m hobs) ⟨_, hind, l2Class_ae_eq m hobs⟩
    have hae' : I'.indicator (1 : GaugeField (1 : ℝ) → ℂ) =ᵐ[m] g :=
      (l2Class_ae_eq m hobs).symm.trans hae
    refine ⟨g ⁻¹' {1}, hg (measurableSet_singleton 1), ?_⟩
    have h : ∀ᵐ U ∂m, U ∉ symmDiff (g ⁻¹' {1}) I' := by
      filter_upwards [hae'] with U hU
      by_cases hU' : U ∈ I'
      · simp [Set.mem_symmDiff, hU', ← hU]
      · simp [Set.mem_symmDiff, hU', ← hU]
    simpa using ae_iff.mp h
end Core
theorem unitaryMonomial_zero {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    [CompleteSpace 𝒦] {J : Type*} [Fintype J] [Nonempty J]
    (S : JointSpectrum.CommutingFamily 𝒦 J) :
    S.unitaryMonomial (fun _ => 0) = 1 := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.unitaryMonomial_zero <;> assumption
theorem intPoint_zero : intPoint 0 = 0 := by
  apply Subtype.ext
  funext i
  simp [intPoint]
end GroundStateProof
open GroundStateProof in
theorem groundStateAndInvariance_holds
    (hAct : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hCond : InfiniteLattice.UnitLatticeCondExp.UnitLatticeCondExpProperties)
    (hGroup : InfiniteLattice.UnitSymmetriesAndFaces.Summary)
    (hInv : InfiniteLattice.ShiftInvariantFunctions.InvariantFunctionsTheorem)
    (hCarrier : LinkPictureReflectionsConeGround)
    (hMatrix : MatrixElementsEqCorrelations)
    (hMeas : InfiniteLattice.LocalDeterminationAndIntegrableAction)
    (hPict : ReflectionPairTheorem) :
    GroundStateAndInvariance := by
  intro ν μ
  have : IsProbabilityMeasure (ν : Measure (GaugeField (1 : ℝ))) := ν.2.1
  have hm : ∀ r : UnitLatticeSymmetry, IsSymmetricUnder (ν : Measure (GaugeField (1 : ℝ))) r :=
    fun r => hGroup.2.1 ν.1 ν.2 r
  have hcar := hCarrier ν μ
  have hpic := hPict ν μ ReflectionPair.link
  refine groundState_of_limitForm hAct hMeas hInv hCond hm μ
    (fun F H => inner ℂ (ReflectionPair.link.obsClass ν μ F)
      (groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ H))) ?_ ?_ ?_
  · intro F hF H hH
    have h₁ := hcar.2.2.2.1 (ReflectionPair.link.obsClass ν μ H)
    have h₂ : Tendsto (fun n : ℕ => (ReflectionPair.link.transferOp ν μ ^ n)
        (ReflectionPair.link.obsClass ν μ H)) atTop
        (𝓝 (groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ H))) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr h₁
    have hcont : Continuous fun x : ReflectionPair.link.Hilb ν μ =>
        inner ℂ (ReflectionPair.link.obsClass ν μ F) x := continuous_const.inner continuous_id
    have h₃ := (hcont.tendsto _).comp h₂
    refine h₃.congr fun k => ?_
    have h₄ := (hMatrix ν μ F hF H hH k 0 rfl).1
    have h₅ : ReflectionPair.link.shiftMonomial ν μ 0 = 1 := unitaryMonomial_zero _
    rw [h₅, mul_one, intPoint_zero, add_zero] at h₄
    exact h₄
  · intro F hF H hH l hl
    have h₁ := hpic.2.1.2.2.2 ⟨l, hl⟩ H hH
    have h₂ := (hcar.2.2.2.2 ⟨l, hl⟩).2
    have h₃ : groundProjection μ ReflectionPair.link ν
        (ReflectionPair.link.shiftOp ν μ ⟨l, hl⟩ (ReflectionPair.link.obsClass ν μ H)) =
        groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ H) :=
      congrArg (fun T : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.link.Hilb ν μ =>
        T (ReflectionPair.link.obsClass ν μ H)) h₂
    change inner ℂ (ReflectionPair.link.obsClass ν μ F) (groundProjection μ ReflectionPair.link ν
      (ReflectionPair.link.obsClass ν μ ((shift (axisStep 1 l)).actOn H))) =
      inner ℂ (ReflectionPair.link.obsClass ν μ F)
        (groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ H))
    rw [← h₁]
    exact congrArg (inner ℂ (ReflectionPair.link.obsClass ν μ F)) h₃
  · intro F hF
    have h := (hpic.1.1.nonneg ⟨F, hF⟩).2
    rw [ReflectionPair.pairForm_apply] at h
    exact h
end YangMills.Construction.ReflectionPositivity.DirectionPictures
