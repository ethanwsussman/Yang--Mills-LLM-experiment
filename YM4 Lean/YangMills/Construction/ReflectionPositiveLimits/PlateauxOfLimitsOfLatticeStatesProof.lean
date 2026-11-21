import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import YangMills.Construction.ReflectionPositiveLimits.PlateauxOfLimitsOfLatticeStates
import YangMills.Construction.ReflectionPositivity.DecayOnSiteCubeVectors
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitPlateaux
open YangMills.Construction.ReflectionPositivity
open YangMills.Construction.ReflectionPositivity.TimeClustering
open YangMills.Construction.InfiniteLattice (scaledCube mem_centeredCube regionObservables regionSigma_mono)
open YangMills.Construction.SmearingFilter (spectralRateConst spectralRateFn)
open YangMills.Construction.ReflectionPositivity.EuclidIsometry (translate)
open YangMills.Construction.TorusMetric (euclidNormVec)
theorem tendsto_of_eventually_isGreatest_range {ι : Type*} [Finite ι] {c : ι → ℕ+ → ℝ}
    {l : ι → ℝ} {N : ℕ+ → ℝ}
    {M : ℝ} (hc : ∀ i, Tendsto (c i) atTop (𝓝 (l i)))
    (hN : ∀ᶠ j in atTop, IsGreatest (range fun i => c i j) (N j))
    (hM : IsGreatest (range l) M) : Tendsto N atTop (𝓝 M) := by
  obtain ⟨⟨i₀, rfl⟩, hM⟩ := hM
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [(hc i₀).eventually (lt_mem_nhds hb), hN] with j h1 h2
    exact h1.trans_le (h2.2 ⟨i₀, rfl⟩)
  · have h : ∀ᶠ j in atTop, ∀ i, c i j < b :=
      eventually_all.2 fun i => (hc i).eventually (gt_mem_nhds ((hM ⟨i, rfl⟩).trans_lt hb))
    filter_upwards [h, hN] with j h1 h2
    obtain ⟨i, hi⟩ := h2.1
    rw [← hi]
    exact h1 i
theorem continuous_maxNorm : Continuous maxNorm := by
  have h : maxNorm = fun x => ‖x‖ := funext maxNorm_eq_norm
  rw [h]
  exact continuous_norm
theorem abs_apply_le_maxNorm (x : Space) (μ : Fin 4) : |x μ| ≤ maxNorm x :=
  Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
theorem exists_maxNorm_eq_abs (x : Space) : ∃ μ, maxNorm x = |x μ| := by
  obtain ⟨μ, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun μ => |x μ|
  exact ⟨μ, h⟩
theorem maxNorm_le_add_maxNorm_sub (x y : Space) : maxNorm x ≤ maxNorm y + maxNorm (x - y) := by
  simp only [maxNorm_eq_norm]
  simpa using norm_add_le y (x - y)
section Spacing
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
include hL in
theorem mesh_pos (j : ℕ+) : 0 < A.mesh j :=
  meshSize_pos hL _
include hL in
theorem tendsto_mesh_zero : Tendsto (fun j => A.mesh j) atTop (𝓝 0) := by
  have hL1 : (1 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have hK : Tendsto (fun j : ℕ+ => ((A.level j : ℕ+) : ℕ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b.succPNat] with j hj
    have h1 : j ≤ A.level j := A.level_strictMono.le_apply
    have h2 : ((b.succPNat : ℕ+) : ℕ) ≤ ((A.level j : ℕ+) : ℕ) := hj.trans h1
    simp only [Nat.succPNat_coe] at h2
    omega
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (L : ℝ)⁻¹)
    (inv_nonneg.2 (by positivity)) (inv_lt_one_of_one_lt₀ hL1)).comp hK
  refine h.congr fun j => ?_
  simp only [Function.comp_apply, PeriodicLattice.meshSize, zpow_neg, zpow_natCast, inv_pow]
end Spacing
theorem isCompact_iUnion_tsupport (X : Tuple) : IsCompact (⋃ f ∈ X.1, tsupport f) :=
  (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2.1
theorem exists_pos_margin {ϖ : ℝ} {X : Tuple} (hX : X ∈ tuplesSupportedIn (centredCube ϖ))
    (hne : (⋃ f ∈ X.1, tsupport f).Nonempty) :
    ∃ δ > 0, ∀ x ∈ ⋃ f ∈ X.1, tsupport f, maxNorm x ≤ ϖ - δ := by
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_iUnion_tsupport X).exists_isMaxOn hne
    continuous_maxNorm.continuousOn
  have hlt : maxNorm x₀ < ϖ := by
    obtain ⟨f, hf, hx⟩ := mem_iUnion₂.1 hx₀
    exact hX f hf hx
  refine ⟨ϖ - maxNorm x₀, by linarith, fun x hx => ?_⟩
  have h : maxNorm x ≤ maxNorm x₀ := hmax hx
  linarith
section Cube
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
  (hr : TupleRepresentatives.Statement)
  (hl : FineLatticeAdicData.AdicDataLatticeData)
include hl in
theorem eventually_cubeIndex_mul_mesh {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L)
    (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∀ᶠ j in atTop, ((A.cubeIndex ϖ j : ℕ) : ℝ) * A.mesh j = ϖ := by
  obtain ⟨j₀, h⟩ := (hl L hL A.level A.level_strictMono).2.2.2.1 ϖ hϖ
  filter_upwards [eventually_ge_atTop j₀] with j hj
  obtain ⟨n, hn, he⟩ := h j hj
  have hpos := mesh_pos hL A j
  have hc : ((A.cubeIndex ϖ j : ℕ+) : ℕ) = n := by
    simp only [LatticeSequence.cubeIndex]
    rw [he, Nat.floor_natCast, Nat.toPNat'_coe]
    simp [hn]
  rw [hc, ← he]
  exact div_mul_cancel₀ _ hpos.ne'
include hL hr hl in
theorem eventually_inCubeAt {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) : ∀ᶠ j in atTop, A.InCubeAt ϖ j X := by
  have hcube := eventually_cubeIndex_mul_mesh A hl hϖ hL
  by_cases hne : (⋃ f ∈ X.1, tsupport f).Nonempty
  · obtain ⟨δ, hδ, hm⟩ := exists_pos_margin hX hne
    have hsmall : ∀ᶠ j in atTop, A.mesh j < δ :=
      (tendsto_mesh_zero hL A).eventually (gt_mem_nhds hδ)
    filter_upwards [hcube, hsmall] with j h1 h2
    refine ⟨h1, ?_⟩
    have hloc := ((hr L hL.1 hL.2 A j).2.2.1 X).1 hne
    refine ⟨hloc.1, ?_⟩
    refine Measurable.mono hloc.2 (regionSigma_mono fun x hx => ?_) le_rfl
    have hpos := mesh_pos hL A j
    have hx' : maxNormInfDist x (⋃ f ∈ X.1, tsupport f) < A.mesh j :=
      lt_of_le_of_lt hx (by linarith)
    obtain ⟨_, ⟨x', hx'S, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image _) hx'
    have hb : maxNorm x ≤ ϖ := by
      have := maxNorm_le_add_maxNorm_sub x x'
      have := hm x' hx'S
      linarith
    rw [mem_centeredCube hpos]
    intro μ
    rw [h1]
    exact abs_le.1 ((abs_apply_le_maxNorm x μ).trans hb)
  · have hempty : (⋃ f ∈ X.1, tsupport f) = ∅ := not_nonempty_iff_eq_empty.1 hne
    filter_upwards [hcube] with j h1
    refine ⟨h1, ?_⟩
    obtain ⟨c, hc⟩ := ((hr L hL.1 hL.2 A j).2.2.1 X).2 hempty
    refine ⟨((hr L hL.1 hL.2 A j).2.1 X).2.1, ?_⟩
    have : A.complexRep j X = fun _ => ((c : ℝ) : ℂ) := by
      funext U
      simp [LatticeSequence.complexRep, hc]
    rw [this]
    exact measurable_const
end Cube
theorem euclidIsometry_ext {r r' : EuclidIsometry} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.euclidIsometry_ext <;> assumption
theorem axisReflectionGroup_eq_reflectionGroup :
    DirectionPictures.axisReflectionGroup = reflectionGroup := by
  have h : DirectionPictures.siteReflectPerm = axisReflection := by
    funext l
    ext1 x
    change (MirrorHyperplanes.siteReflect l).toFun x = _
    rw [MirrorHyperplanes.siteReflect_apply]
    rfl
  rw [DirectionPictures.axisReflectionGroup, reflectionGroup, h]
def toReflectionGroup (γ : DirectionPictures.axisReflectionGroup) : reflectionGroup :=
  ⟨γ.1, axisReflectionGroup_eq_reflectionGroup ▸ γ.2⟩
theorem toReflectionGroup_surjective : Function.Surjective toReflectionGroup := fun γ =>
  ⟨⟨γ.1, axisReflectionGroup_eq_reflectionGroup.symm ▸ γ.2⟩, rfl⟩
theorem latticeSymmetryToEuclid_toLatticeSymmetry (a : ℝ)
    (γ : DirectionPictures.axisReflectionGroup) :
    latticeSymmetryToEuclid
        (DirectionPictures.axisReflectionGroup.toLatticeSymmetry a γ) =
      reflectionGroupIsometry (toReflectionGroup γ) :=
  euclidIsometry_ext rfl
theorem latticeSymmetryToEuclid_coordinateReflect (a : ℝ) (μ : Fin 4) :
    latticeSymmetryToEuclid (LatticeAtSpacing.coordinateReflect a μ) =
      reflectionGroupIsometry (axisReflectionElem μ) :=
  euclidIsometry_ext (funext fun x => LatticeAtSpacing.coordinateReflect_apply a μ x)
theorem latticeSymmetryToEuclid_shift {a : ℝ} (v : InfiniteLattice.LatticePoint a) :
    latticeSymmetryToEuclid (InfiniteLattice.shift v) = EuclidIsometry.translate (v : Space) :=
  euclidIsometry_ext rfl
theorem coe_nsmul_axisStep {a ϖ : ℝ} {r : ℕ} (h : (r : ℝ) * a = ϖ) (μ : Fin 4) :
    (((2 * r) • InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : Space) =
      (2 * ϖ) • PeriodicLattice.coordVec μ := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [InfiniteLattice.axisStep, PeriodicLattice.coordVec, ← h]
    ring
  · simp [InfiniteLattice.axisStep, PeriodicLattice.coordVec, Pi.single_eq_of_ne hν]
theorem maxNorm_reflectionGroup_apply (γ : reflectionGroup) (x : Space) :
    maxNorm (γ.1 x) = maxNorm x := by
  obtain ⟨s, hs⟩ := (mem_reflectionGroup_iff γ.1).1 γ.2
  refine Finset.sup'_congr _ rfl fun μ _ => ?_
  have h : |((s μ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
  rw [hs, flipSigns_apply, abs_mul, h, one_mul]
theorem push_reflectionGroup_mem {ϖ : ℝ} {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ))
    (γ : reflectionGroup) : push (reflectionGroupIsometry γ) X ∈ tuplesSupportedIn (centredCube ϖ) := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn]
  intro y hy
  have h : maxNorm ((reflectionGroupIsometry γ).symm.toFun y) < ϖ := hX f hf hy
  have e := maxNorm_reflectionGroup_apply γ ((reflectionGroupIsometry γ).symm.toFun y)
  have e' : γ.1 ((reflectionGroupIsometry γ).symm.toFun y) = y :=
    (reflectionGroupIsometry γ).toFun_symm y
  rw [e'] at e
  change maxNorm y < ϖ
  rw [e]
  exact h
theorem concatenable_mirror_translated {ϖ : ℝ} {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (μ : Fin 4) (γ : reflectionGroup) :
    Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X) := by
  have h₁ : mirrorTuple μ γ X ∈ tuplesSupportedIn (centredCube ϖ) :=
    push_reflectionGroup_mem (push_reflectionGroup_mem hX γ) _
  have h₂ : translatedTuple ϖ μ γ X ∈ tuplesSupportedIn {x | ϖ < x μ} := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rw [tsupport_pushFn]
    intro y hy
    have h : maxNorm (y - (2 * ϖ) • PeriodicLattice.coordVec μ) < ϖ := by
      have := push_reflectionGroup_mem hX γ f hf hy
      rwa [EuclidIsometry.symm_translate] at this
    have h' := (abs_apply_le_maxNorm _ μ).trans_lt h
    have h'' := (abs_lt.1 h').1
    simp [PeriodicLattice.coordVec] at h''
    change ϖ < y μ
    linarith
  refine concatenable_of_disjoint ?_ h₁ h₂
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h := (abs_apply_le_maxNorm x μ).trans_lt hx
  have h' := (abs_lt.1 h).2
  have h'' : ϖ < x μ := hx'
  linarith
theorem concatenable_push_of_far {ϖ : ℝ} {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ))
    {v : Space} (hv : 2 * ϖ < maxNorm v) : Concatenable X (push (translate v) Y) := by
  have h₂ : push (translate v) Y ∈ tuplesSupportedIn {x | maxNorm (x - v) < ϖ} := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rw [tsupport_pushFn]
    intro y hy
    have := hY f hf hy
    rwa [EuclidIsometry.symm_translate] at this
  refine concatenable_of_disjoint ?_ hX h₂
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h₁ : maxNorm x < ϖ := hx
  have h₃ : maxNorm (x - v) < ϖ := hx'
  have h₄ : maxNorm v ≤ maxNorm x + maxNorm (x - v) := by
    simp only [maxNorm_eq_norm]
    simpa using norm_sub_le x (x - v)
  linarith
section Representatives
variable {L : ℕ} (A : LatticeSequence L)
theorem pushComb_basisOf (r : EuclidIsometry) (X : Tuple) :
    pushComb r (basisOf X) = basisOf (push r X) := by
  simp [pushComb, basisOf, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
theorem complexRep_eq_repComb (j : ℕ+) (X : Tuple) :
    A.complexRep j X = A.repComb j (basisOf X) :=
  funext fun U => (A.repComb_basisOf j X U).symm
variable {A}
theorem actOn_complexRep {j : ℕ+}
    (h : A.RepCommutesWithSymmetries j)
    (r : InfiniteLattice.LatticeSymmetry (A.mesh j)) (X : Tuple) :
    r.actOn (A.complexRep j X) =
      A.complexRep j (push (latticeSymmetryToEuclid r) X) := by
  rw [complexRep_eq_repComb, complexRep_eq_repComb, h, pushComb_basisOf]
theorem expect_conj_mul_complexRep {j : ℕ+} (h : A.RepConcatEqMul j)
    (X Y : Tuple) (hXY : Concatenable X Y) :
    (A.measure j).integral
        (fun U => conj (A.complexRep j X U) * A.complexRep j Y U) =
      ((A.mean j (concat X Y hXY) : ℝ) : ℂ) := by
  rw [← A.integral_rep]
  congr 1
  funext U
  simp [LatticeSequence.complexRep, h X Y hXY]
theorem reflCorr_complexRep_eq {j : ℕ+} (hc : A.RepCommutesWithSymmetries j)
    (hp : A.RepConcatEqMul j) {ϖ : ℝ} {r : ℕ}
    (hr : (r : ℝ) * A.mesh j = ϖ) {X : Tuple} (μ : Fin 4)
    (γ : DirectionPictures.axisReflectionGroup)
    (h : Concatenable (mirrorTuple μ (toReflectionGroup γ) X)
      (translatedTuple ϖ μ (toReflectionGroup γ) X)) :
    DirectionPictures.reflCorr (A.measure j) μ
        ((DirectionPictures.axisReflectionGroup.toLatticeSymmetry _ γ).actOn
          (A.complexRep j X))
        ((InfiniteLattice.shift ((2 * r) • InfiniteLattice.axisStep _ μ)).actOn
          ((DirectionPictures.axisReflectionGroup.toLatticeSymmetry _ γ).actOn
            (A.complexRep j X))) =
      ((A.mean j (concat _ _ h) : ℝ) : ℂ) := by
  rw [← expect_conj_mul_complexRep hp _ _ h, DirectionPictures.reflCorr]
  rw [actOn_complexRep hc, actOn_complexRep hc,
    actOn_complexRep hc, latticeSymmetryToEuclid_coordinateReflect,
    latticeSymmetryToEuclid_toLatticeSymmetry,
    latticeSymmetryToEuclid_shift, coe_nsmul_axisStep hr]
  rfl
end Representatives
theorem conj_condExpShiftInvariant_ofReal {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a))
    {F : InfiniteLattice.GaugeField a → ℝ}
    (hF : Integrable (fun U => ((F U : ℝ) : ℂ)) ν) :
    (fun U => conj (InfiniteLattice.condExpShiftInvariant ν (fun V => ((F V : ℝ) : ℂ)) U)) =ᵐ[ν]
      InfiniteLattice.condExpShiftInvariant ν (fun V => ((F V : ℝ) : ℂ)) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm
    (m := InfiniteLattice.shiftInvariantSigma a) hF
  have e : ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun U => ((F U : ℝ) : ℂ)) =
      fun U => ((F U : ℝ) : ℂ) := by
    funext U
    simp
  rw [e] at h
  exact h
section Plateau
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
  (hr : TupleRepresentatives.Statement)
include hL hr in
theorem integrable_complexRep (j : ℕ+) (X : Tuple) :
    Integrable (A.complexRep j X) (A.measure j).1 := by
  have : IsProbabilityMeasure (A.measure j).1 := (A.measure j).2
  obtain ⟨hm, C, hC⟩ := ((hr L hL.1 hL.2 A j).2.1 X).2.1
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
include hL hr in
theorem condExpProductAt_eq_plateauAt (j : ℕ+) (X Y : Tuple) :
    A.condExpProductAt j X Y = A.plateauAt j X Y := by
  refine integral_congr_ae ?_
  filter_upwards [conj_condExpShiftInvariant_ofReal (A.measure j).1
    (integrable_complexRep hL A hr j X)] with U hU
  have h : conj (InfiniteLattice.condExpShiftInvariant (A.measure j).1
      (A.complexRep j X) U) =
      InfiniteLattice.condExpShiftInvariant (A.measure j).1 (A.complexRep j X) U := hU
  rw [h]
end Plateau
theorem continuous_spectralRateFn : Continuous spectralRateFn := by
  have h : spectralRateFn = fun u => spectralRateConst * (u ^ 2 + u ^ 3) := rfl
  rw [h]
  fun_prop
theorem spectralRateFn_nonneg (hc : 0 ≤ spectralRateConst) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ spectralRateFn u :=
  mul_nonneg hc (by positivity)
theorem tendsto_spectralRateFn_div_atTop (ϖ : ℝ) :
    Tendsto (fun t : ℝ => spectralRateFn (ϖ / (t - 2 * ϖ))) atTop (𝓝 0) := by
  have h0 : spectralRateFn 0 = 0 := by simp [spectralRateFn]
  have h1 : Tendsto (fun t : ℝ => ϖ / (t - 2 * ϖ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  rw [← h0]
  exact (continuous_spectralRateFn.tendsto 0).comp h1
theorem spectralRateFn_le_of_far (hc : 0 ≤ spectralRateConst) {ϖ e m : ℝ} (hϖ : 0 < ϖ)
    (he : 8 * ϖ ≤ e) (hm : e ≤ 2 * m) :
    spectralRateFn (ϖ / (m - 2 * ϖ)) ≤ 32 * spectralRateConst * (ϖ / e) ^ 2 := by
  have hepos : 0 < e := by linarith
  have ht : e / 4 ≤ m - 2 * ϖ := by linarith
  have htpos : 0 < m - 2 * ϖ := by linarith
  set u := ϖ / (m - 2 * ϖ) with hu
  set w := ϖ / e with hw
  have hupos : 0 ≤ u := by positivity
  have hwpos : 0 ≤ w := by positivity
  have huw : u ≤ 4 * w := by
    rw [hu, hw, div_le_iff₀ htpos]
    have : 4 * (ϖ / e) * (m - 2 * ϖ) = ϖ * ((m - 2 * ϖ) / (e / 4)) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (m - 2 * ϖ) / (e / 4) := (one_le_div (by positivity)).2 ht
    nlinarith
  have hw8 : w ≤ 1 / 8 := by
    rw [hw, div_le_iff₀ hepos]
    linarith
  have hu1 : u ≤ 1 := by linarith
  have hu3 : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one hupos hu1 (by norm_num)
  have hu2 : u ^ 2 ≤ 16 * w ^ 2 := by nlinarith
  have : u ^ 2 + u ^ 3 ≤ 32 * w ^ 2 := by linarith
  have h := mul_le_mul_of_nonneg_left this hc
  calc spectralRateFn u = spectralRateConst * (u ^ 2 + u ^ 3) := rfl
    _ ≤ spectralRateConst * (32 * w ^ 2) := h
    _ = 32 * spectralRateConst * w ^ 2 := by ring
theorem euclidNormVec_le_two_mul_maxNorm (v : Space) : euclidNormVec v ≤ 2 * maxNorm v := by
  have hm : 0 ≤ maxNorm v := (abs_nonneg _).trans (abs_apply_le_maxNorm v 0)
  have hs : ∀ μ, v μ ^ 2 ≤ maxNorm v ^ 2 := fun μ => by
    have := abs_apply_le_maxNorm v μ
    rw [← sq_abs]
    gcongr
  rw [TorusMetric.euclidNormVec]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_four]
  nlinarith [hs 0, hs 1, hs 2, hs 3]
theorem maxNorm_smul_coordVec (c : ℝ) (μ : Fin 4) :
    maxNorm (c • PeriodicLattice.coordVec μ) = |c| := by
  rw [maxNorm_eq_norm, norm_smul, PeriodicLattice.coordVec, Pi.norm_single]
  simp
theorem natCast_mem_adicGridPoints (L n : ℕ) : (n : ℝ) ∈ PeriodicLattice.adicGridPoints L := by
  rw [PeriodicLattice.mem_adicGridPoints_iff]
  exact ⟨0, n, by simp [PeriodicLattice.meshSize]⟩
section Limits
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
  (hr : TupleRepresentatives.Statement)
  (hl : FineLatticeAdicData.AdicDataLatticeData)
  (ho : DirectionPictures.singleLatticeInputs)
  (hRP : A.IsRP)
  {σ : Tuple → ℝ} (hlim : A.HasLimit σ)
include hL hr hl ho hRP
theorem eventually_isGreatest_sizeAt {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L)
    {X : Tuple} (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) :
    ∀ᶠ j in atTop, IsGreatest
      (range fun p : Fin 4 × DirectionPictures.axisReflectionGroup =>
        A.mean j (concat _ _ (concatenable_mirror_translated hX p.1 (toReflectionGroup p.2))))
      (A.sizeAt hL ϖ j X) := by
  filter_upwards [eventually_inCubeAt hL A hr hl hϖ hX] with j hj
  have hd := (ho _ (mesh_pos hL A j) (A.measure j) (hRP j)).2.2.2.1.2 (A.cubeIndex ϖ j) _ hj.2
  have hg := hd.2.2.1
  have hcom := (hr L hL.1 hL.2 A j).2.2.2.1
  have hcat := (hr L hL.1 hL.2 A j).2.2.2.2.1
  have key := fun p : Fin 4 × DirectionPictures.axisReflectionGroup =>
    reflCorr_complexRep_eq hcom hcat hj.1 p.1 p.2
      (concatenable_mirror_translated hX p.1 (toReflectionGroup p.2))
  constructor
  · obtain ⟨p, hp⟩ := hg.1
    refine ⟨p, ?_⟩
    have h2 := (key p).symm.trans hp
    exact_mod_cast h2
  · rintro _ ⟨p, rfl⟩
    have h2 := le_of_eq_of_le (key p).symm (hg.2 ⟨p, rfl⟩)
    exact Complex.real_le_real.1 h2
omit hL hr hl ho hRP in
theorem sizeAt_nonneg (hL : Conventions.IsAdmissibleBlockingFactor L) (ϖ : ℝ) (j : ℕ+)
    (X : Tuple) : 0 ≤ A.sizeAt hL ϖ j X := by
  obtain ⟨p, hp⟩ := (DirectionPictures.isGreatest_scaledCubeReflectionSize
    (meshSize_pos hL _) (A.measure j).1 (A.cubeIndex ϖ j)
    (A.complexRep j X)).1
  rw [LatticeSequence.sizeAt, ← hp]
  positivity
include hlim
theorem tendsto_sizeAt {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) :
    Tendsto (fun j => A.sizeAt hL ϖ j X) atTop (𝓝 (functionalSize σ ϖ X)) := by
  refine tendsto_of_eventually_isGreatest_range
    (l := fun p : Fin 4 × DirectionPictures.axisReflectionGroup =>
      mirrorCorrelation σ ϖ X (p.1, toReflectionGroup p.2)) (fun p => ?_)
    (eventually_isGreatest_sizeAt hL A hr hl ho hRP hϖ hX) ?_
  · have h := concatenable_mirror_translated hX p.1 (toReflectionGroup p.2)
    have e : mirrorCorrelation σ ϖ X (p.1, toReflectionGroup p.2) = σ (concat _ _ h) := by
      unfold mirrorCorrelation
      exact dif_pos h
    rw [e]
    exact hlim.2 _
  · have e : (range fun p : Fin 4 × DirectionPictures.axisReflectionGroup =>
        mirrorCorrelation σ ϖ X (p.1, toReflectionGroup p.2)) =
        range (mirrorCorrelation σ ϖ X) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨⟨μ, γ⟩, rfl⟩
        obtain ⟨γ', rfl⟩ := toReflectionGroup_surjective γ
        exact ⟨(μ, γ'), rfl⟩
    rw [e]
    exact isGreatest_functionalSize σ ϖ X
theorem functionalSize_nonneg {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) : 0 ≤ functionalSize σ ϖ X :=
  ge_of_tendsto' (tendsto_sizeAt hL A hr hl ho hRP hlim hϖ hX) fun j =>
    sizeAt_nonneg A hL ϖ j X
theorem tendsto_sizeAt_rpow_half {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) :
    Tendsto (fun j => A.sizeAt hL ϖ j X ^ (1 / 2 : ℝ)) atTop
      (𝓝 (√(functionalSize σ ϖ X))) := by
  rw [Real.sqrt_eq_rpow]
  exact (tendsto_sizeAt hL A hr hl ho hRP hlim hϖ hX).rpow_const (Or.inr (by norm_num))
omit hlim
theorem eventually_plateauAt_bound {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ))
    {v : Space}
    (hv : ∀ μ, v μ ∈ PeriodicLattice.adicGridPoints L) (hbig : 2 * ϖ < maxNorm v)
    (hd : Concatenable X (push (translate v) Y)) :
    ∀ᶠ j in atTop, ‖((A.mean j (concat X _ hd) : ℝ) : ℂ) - A.plateauAt j X Y‖ ≤
      spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * A.sizeAt hL ϖ j X ^ (1 / 2 : ℝ) *
        A.sizeAt hL ϖ j Y ^ (1 / 2 : ℝ) := by
  obtain ⟨⟨⟨G, hG⟩, -, -⟩, -, hAdic, hMult, -, -⟩ := hl L hL A.level A.level_strictMono
  have memG : ∀ x, x ∈ G ↔ x ∈ PeriodicLattice.adicGridPoints L := fun x => by
    rw [← hG]
    rfl
  have ht : maxNorm v - 2 * ϖ ∈ posAdicGridPoints L := by
    refine ⟨?_, sub_pos.2 hbig⟩
    obtain ⟨μ, hμ⟩ := exists_maxNorm_eq_abs v
    have h1 : maxNorm v ∈ G := by
      rw [hμ]
      rcases abs_cases (v μ) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        exact (memG _).2 (hv μ)
      · rw [h]
        exact G.neg_mem ((memG _).2 (hv μ))
    have h2 : ϖ ∈ G := (memG _).2 hϖ.1
    have e : maxNorm v - 2 * ϖ = maxNorm v - (ϖ + ϖ) := by ring
    rw [e]
    exact (memG _).1 (G.sub_mem h1 (G.add_mem h2 h2))
  obtain ⟨j₁, hj₁⟩ := hAdic v hv
  obtain ⟨j₂, hj₂⟩ := hMult _ ht
  filter_upwards [eventually_inCubeAt hL A hr hl hϖ hX, eventually_inCubeAt hL A hr hl hϖ hY,
    eventually_ge_atTop j₁, eventually_ge_atTop j₂] with j hXj hYj h1 h2
  have ha := mesh_pos hL A j
  obtain ⟨k, hk, he⟩ := hj₂ j h2
  have hd' := (ho _ ha (A.measure j) (hRP j)).2.2.2.1.2 (A.cubeIndex ϖ j) _ hXj.2
  have hcom := (hr L hL.1 hL.2 A j).2.2.2.1
  have hcat := (hr L hL.1 hL.2 A j).2.2.2.2.1
  let y : InfiniteLattice.LatticePoint (A.mesh j) := ⟨v, hj₁ j h1⟩
  have hr' : (((A.cubeIndex ϖ j : ℕ+) : ℕ) : ℝ) = ϖ / A.mesh j :=
    eq_div_of_mul_eq ha.ne' hXj.1
  have hsep : DirectionPictures.scaledCubeSeparation (A.cubeIndex ϖ j) y =
      (maxNorm v - 2 * ϖ) / A.mesh j := by
    have e : GibbsAtFixedSpacing.linfNorm (y : InfiniteLattice.AmbientSpace) = maxNorm v := rfl
    rw [DirectionPictures.scaledCubeSeparation, e, hr']
    field_simp
  have hlaw := hd'.1 _ hYj.2 y (by
    rw [hsep, he]
    exact_mod_cast hk)
  rw [hsep, hr', div_div_div_cancel_right₀ ha.ne'] at hlaw
  have e : ((A.measure j).integral fun U => conj (A.complexRep j X U) *
      (InfiniteLattice.shift y).actOn (A.complexRep j Y) U) =
      ((A.mean j (concat X _ hd) : ℝ) : ℂ) := by
    rw [actOn_complexRep hcom, latticeSymmetryToEuclid_shift]
    exact expect_conj_mul_complexRep hcat X _ hd
  rw [e] at hlaw
  exact hlaw
include hlim
variable (hc : 0 ≤ spectralRateConst)
include hc
theorem exists_real_near_plateauAt {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, ∀ᶠ j in atTop, ‖A.plateauAt j X Y - (s : ℂ)‖ < ε := by
  have hϖpos : 0 < ϖ := hϖ.2
  set R := √(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y) with hR
  have hRnn : 0 ≤ R := by positivity
  have hRj : Tendsto (fun j => A.sizeAt hL ϖ j X ^ (1 / 2 : ℝ) *
      A.sizeAt hL ϖ j Y ^ (1 / 2 : ℝ)) atTop (𝓝 R) :=
    (tendsto_sizeAt_rpow_half hL A hr hl ho hRP hlim hϖ hX).mul
      (tendsto_sizeAt_rpow_half hL A hr hl ho hRP hlim hϖ hY)
  have hb : 0 < R + 1 := by linarith
  have hq : Tendsto (fun n : ℕ => spectralRateFn (ϖ / ((n : ℝ) - 2 * ϖ))) atTop (𝓝 0) :=
    (tendsto_spectralRateFn_div_atTop ϖ).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn1, hn2⟩ := ((hq.eventually (gt_mem_nhds (div_pos (half_pos hε) hb))).and
    (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * ϖ)))).exists
  set v : Space := (n : ℝ) • PeriodicLattice.coordVec 0 with hvdef
  have hsup : maxNorm v = n := by
    rw [hvdef, maxNorm_smul_coordVec, abs_of_nonneg (Nat.cast_nonneg n)]
  have hbig : 2 * ϖ < maxNorm v := by rwa [hsup]
  have hv : ∀ μ, v μ ∈ PeriodicLattice.adicGridPoints L := fun μ => by
    by_cases h : μ = 0
    · subst h
      have : v 0 = ((n : ℕ) : ℝ) := by simp [hvdef, PeriodicLattice.coordVec]
      rw [this]
      exact natCast_mem_adicGridPoints L n
    · have : v μ = ((0 : ℕ) : ℝ) := by
        simp [hvdef, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
      rw [this]
      exact natCast_mem_adicGridPoints L 0
  have hd := concatenable_push_of_far hX hY hbig
  refine ⟨σ (concat X _ hd), ?_⟩
  have hqnn : 0 ≤ spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) :=
    spectralRateFn_nonneg hc (div_nonneg hϖpos.le (by linarith))
  have hE := hlim.2 (concat X _ hd)
  filter_upwards [eventually_plateauAt_bound hL A hr hl ho hRP hϖ hX hY hv hbig hd,
    hRj.eventually (gt_mem_nhds (lt_add_one R)),
    hE.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with j h1 h2 h3
  have h3' : ‖((A.mean j (concat X _ hd) : ℝ) : ℂ) -
      ((σ (concat X _ hd) : ℝ) : ℂ)‖ < ε / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact h3
  have h4 : spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * (R + 1) < ε / 2 := by
    rw [hsup]
    exact (lt_div_iff₀ hb).1 hn1
  have h5 : ‖((A.mean j (concat X _ hd) : ℝ) : ℂ) - A.plateauAt j X Y‖ < ε / 2 := by
    refine h1.trans_lt (lt_of_le_of_lt ?_ h4)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2.le hqnn
  calc ‖A.plateauAt j X Y - ((σ (concat X _ hd) : ℝ) : ℂ)‖
      ≤ ‖A.plateauAt j X Y - ((A.mean j (concat X _ hd) : ℝ) : ℂ)‖ +
        ‖((A.mean j (concat X _ hd) : ℝ) : ℂ) -
          ((σ (concat X _ hd) : ℝ) : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
      rw [norm_sub_rev]
      exact add_lt_add h5 h3'
    _ = ε := add_halves ε
theorem exists_real_plateau_limit {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ)) :
    ∃ l : ℝ, A.IsPlateauLimit X Y l := by
  have happ := fun {ε : ℝ} (hε : 0 < ε) =>
    exists_real_near_plateauAt hL A hr hl ho hRP hlim hc hϖ hX hY hε
  have hcauchy : CauchySeq fun j => A.plateauAt j X Y := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨s, hs⟩ := happ (half_pos hε)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hs
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [← dist_eq_norm] at h1 h2
    calc dist (A.plateauAt m X Y) (A.plateauAt n X Y)
        ≤ dist (A.plateauAt m X Y) (s : ℂ) + dist (A.plateauAt n X Y) (s : ℂ) :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.2 hne
    obtain ⟨s, hs⟩ := happ (half_pos hpos)
    have hlim' : Tendsto (fun j => ‖A.plateauAt j X Y - (s : ℂ)‖) atTop (𝓝 ‖z - (s : ℂ)‖) :=
      (hz.sub_const _).norm
    have h1 := le_of_tendsto hlim' (hs.mono fun j h => h.le)
    have h2 : |z.im| ≤ ‖z - (s : ℂ)‖ := by
      have := Complex.abs_im_le_norm (z - (s : ℂ))
      simpa using this
    linarith
  refine ⟨z.re, ?_⟩
  have e : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  change Tendsto _ _ _
  rw [e]
  exact hz
theorem isPlateauLimit_limitPlateau {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ)) :
    A.IsPlateauLimit X Y (A.limitPlateau X Y) :=
  Classical.epsilon_spec (exists_real_plateau_limit hL A hr hl ho hRP hlim hc hϖ hX hY)
theorem limitPlateau_bound_of_adic {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ))
    {v : Space}
    (hv : ∀ μ, v μ ∈ PeriodicLattice.adicGridPoints L) (hbig : 2 * ϖ < maxNorm v)
    (hd : Concatenable X (push (translate v) Y)) :
    |σ (concat X _ hd) - A.limitPlateau X Y| ≤
      spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * √(functionalSize σ ϖ X) *
        √(functionalSize σ ϖ Y) := by
  have hE : Tendsto (fun j => ((A.mean j (concat X _ hd) : ℝ) : ℂ)) atTop
      (𝓝 ((σ (concat X _ hd) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hlim.2 _)
  have hP := isPlateauLimit_limitPlateau hL A hr hl ho hRP hlim hc hϖ hX hY
  have h1 := (hE.sub hP).norm
  have h2 := ((tendsto_sizeAt_rpow_half hL A hr hl ho hRP hlim hϖ hX).const_mul
    (spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)))).mul
    (tendsto_sizeAt_rpow_half hL A hr hl ho hRP hlim hϖ hY)
  have h3 := le_of_tendsto_of_tendsto h1 h2
    (eventually_plateauAt_bound hL A hr hl ho hRP hϖ hX hY hv hbig hd)
  rwa [← Complex.ofReal_sub, Complex.norm_real] at h3
end Limits
section Limits
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
  (hr : TupleRepresentatives.Statement)
  (hl : FineLatticeAdicData.AdicDataLatticeData)
  (ho : DirectionPictures.singleLatticeInputs)
  (hm : MovingTestFunctions.statement)
  (hRP : A.IsRP)
  {σ : Tuple → ℝ} (hcont : IsAdmissiblyContinuous σ) (hlim : A.HasLimit σ)
  (hc : 0 ≤ spectralRateConst)
include hL hr hl ho hm hRP hcont hlim hc
theorem limitPlateau_bound {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ))
    {v : Space}
    (hbig : 2 * ϖ < maxNorm v) (hd : Concatenable X (push (translate v) Y)) :
    |σ (concat X _ hd) - A.limitPlateau X Y| ≤
      spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * √(functionalSize σ ϖ X) *
        √(functionalSize σ ϖ Y) := by
  obtain ⟨⟨-, hdense, -⟩, -⟩ := hl L hL A.level A.level_strictMono
  have hseq : ∀ μ, ∃ x : ℕ → ℝ, (∀ n, x n ∈ PeriodicLattice.adicGridPoints L) ∧
      Tendsto x atTop (𝓝 (v μ)) := fun μ => mem_closure_iff_seq_limit.1 (hdense (v μ))
  choose x hx1 hx2 using hseq
  let w : ℕ → Space := fun n μ => x μ n
  have hw : Tendsto w atTop (𝓝 v) := tendsto_pi_nhds.2 hx2
  have hsup : Tendsto (fun n => maxNorm (w n)) atTop (𝓝 (maxNorm v)) :=
    (continuous_maxNorm.tendsto v).comp hw
  obtain ⟨n₀, -, -, hconv, -⟩ := hm.2.1 Y X w v hw hd
  have hσ := (hcont n₀ _ _ hconv).comp tendsto_natCast_atTop_atTop
  have hbigw : ∀ᶠ n in atTop, 2 * ϖ < maxNorm (w n) := hsup.eventually (lt_mem_nhds hbig)
  have hrate : Tendsto (fun n => spectralRateFn (ϖ / (maxNorm (w n) - 2 * ϖ)) *
      √(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y)) atTop
      (𝓝 (spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * √(functionalSize σ ϖ X) *
        √(functionalSize σ ϖ Y))) := by
    have h1 : Tendsto (fun n => ϖ / (maxNorm (w n) - 2 * ϖ)) atTop
        (𝓝 (ϖ / (maxNorm v - 2 * ϖ))) :=
      tendsto_const_nhds.div (hsup.sub_const _) (sub_pos.2 hbig).ne'
    exact (((continuous_spectralRateFn.tendsto _).comp h1).mul_const _).mul_const _
  refine le_of_tendsto_of_tendsto ((hσ.sub_const _).abs) hrate ?_
  filter_upwards [hbigw] with n hn
  have hdn := concatenable_push_of_far hX hY hn
  have e : concatOrNil X (push (translate (w ((n : ℤ).toNat))) Y) =
      concat X _ hdn := by
    simp only [Int.toNat_natCast]
    exact dif_pos hdn
  simp only [Function.comp_apply]
  rw [e]
  exact limitPlateau_bound_of_adic hL A hr hl ho hRP hlim hc hϖ hX hY (fun μ => hx1 μ n) hn hdn
theorem inverseSquareDecay_of_limit {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ)) :
    InverseSquareDecay A σ ϖ X Y := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hd := concatenable_push_of_far hX hY hv
    exact ⟨hd, limitPlateau_bound hL A hr hl ho hm hRP hcont hlim hc hϖ hX hY hv hd⟩
  · have hϖpos : 0 < ϖ := hϖ.2
    have hle := euclidNormVec_le_two_mul_maxNorm v
    have hv' : 2 * ϖ < maxNorm v := by linarith
    have hd := concatenable_push_of_far hX hY hv'
    refine ⟨hd, (limitPlateau_bound hL A hr hl ho hm hRP hcont hlim hc hϖ hX hY hv' hd).trans ?_⟩
    have h := spectralRateFn_le_of_far hc hϖpos hv hle
    have hs : 0 ≤ √(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y) := by positivity
    calc spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) * √(functionalSize σ ϖ X) *
          √(functionalSize σ ϖ Y)
        = spectralRateFn (ϖ / (maxNorm v - 2 * ϖ)) *
          (√(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y)) := by ring
      _ ≤ 32 * spectralRateConst * (ϖ / euclidNormVec v) ^ 2 *
          (√(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y)) :=
        mul_le_mul_of_nonneg_right h hs
      _ = _ := by ring
omit hm hcont in
theorem sizeAndPlateauLimits_of_limit {ϖ : ℝ} (hϖ : ϖ ∈ posAdicGridPoints L) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube ϖ)) (hY : Y ∈ tuplesSupportedIn (centredCube ϖ)) :
    SizeAndPlateauLimits hL A σ ϖ X Y := by
  have hP := isPlateauLimit_limitPlateau hL A hr hl ho hRP hlim hc hϖ hX hY
  refine ⟨fun μ γ => concatenable_mirror_translated hX μ γ,
    functionalSize_nonneg hL A hr hl ho hRP hlim hϖ hX, hP, ?_,
    eventually_inCubeAt hL A hr hl hϖ hX, tendsto_sizeAt hL A hr hl ho hRP hlim hϖ hX⟩
  refine Tendsto.congr (fun j => ?_) hP
  exact (condExpProductAt_eq_plateauAt hL A hr j X Y).symm
omit hm hcont hlim hc hRP hl hL ho hr in
theorem exists_mem_tuplesSupportedIn_centredCube (X : Tuple) :
    ∃ n : ℕ, 0 < n ∧ X ∈ tuplesSupportedIn (centredCube (n : ℝ)) := by
  obtain ⟨C, hC⟩ := (isCompact_iUnion_tsupport X).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  refine ⟨n + 1, by omega, fun f hf x hx => ?_⟩
  have h1 : ‖x‖ ≤ C := hC x (mem_iUnion₂.2 ⟨f, hf, hx⟩)
  have h2 : C < n := (le_max_left _ _).trans_lt hn
  change maxNorm x < ((n + 1 : ℕ) : ℝ)
  rw [maxNorm_eq_norm]
  push_cast
  linarith
omit hm hcont hlim hc hRP hl hL ho hr in
theorem tuplesSupportedIn_centredCube_mono {a b : ℝ} (h : a ≤ b) {X : Tuple}
    (hX : X ∈ tuplesSupportedIn (centredCube a)) : X ∈ tuplesSupportedIn (centredCube b) :=
  fun f hf _ hx => (hX f hf hx).trans_le h
omit hm hcont hlim hc hRP hl hL ho hr in
theorem natCast_mem_posAdicGridPoints (L : ℕ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ∈ posAdicGridPoints L :=
  ⟨natCast_mem_adicGridPoints L n, show (0 : ℝ) < n from Nat.cast_pos.2 hn⟩
omit hm hcont in
theorem limitPlateau_eq_mul_of_ergodic (hE : A.IsErgodicSeq) {ϖ : ℝ}
    (hϖ : ϖ ∈ posAdicGridPoints L)
    {X Y : Tuple} (hX : X ∈ tuplesSupportedIn (centredCube ϖ))
    (hY : Y ∈ tuplesSupportedIn (centredCube ϖ)) :
    A.limitPlateau X Y = σ X * σ Y := by
  have hP : Tendsto (fun j => A.plateauAt j X Y) atTop (𝓝 (A.limitPlateau X Y : ℂ)) :=
    isPlateauLimit_limitPlateau hL A hr hl ho hRP hlim hc hϖ hX hY
  have hQ : Tendsto (fun j => A.plateauAt j X Y) atTop (𝓝 ((σ X * σ Y : ℝ) : ℂ)) := by
    have h : Tendsto (fun j => ((A.mean j X * A.mean j Y : ℝ) : ℂ)) atTop
        (𝓝 ((σ X * σ Y : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp ((hlim.2 X).mul (hlim.2 Y))
    refine h.congr fun j => ?_
    have hs := (hr L hL.1 hL.2 A j).2.1
    have he := (ho _ (mesh_pos hL A j) (A.measure j) (hRP j)).2.2.2.2.1 (hE.2 j)
    have hform := he.2 _ _ (hs X).2.1 (hs Y).2.1
    rw [LatticeSequence.plateauAt, hform]
    have e : ∀ Z, (A.measure j).integral (A.complexRep j Z) =
        ((A.mean j Z : ℝ) : ℂ) := fun Z => A.integral_rep j Z
    rw [e, e, Complex.conj_ofReal, Complex.ofReal_mul]
  exact_mod_cast tendsto_nhds_unique hP hQ
theorem clustersInTime_of_ergodic (hE : A.IsErgodicSeq)
    (hθ : ∀ X, σ (push timeZeroMirror.reflectIso X) = σ X) : ClustersInTime σ := by
  intro X Y hX hY
  obtain ⟨n₁, hn₁, h₁⟩ := exists_mem_tuplesSupportedIn_centredCube (push timeZeroMirror.reflectIso X)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_mem_tuplesSupportedIn_centredCube Y
  set n := max n₁ n₂ with hn
  have hnpos : 0 < n := lt_max_of_lt_left hn₁
  have hϖ := natCast_mem_posAdicGridPoints L hnpos
  have hXc := tuplesSupportedIn_centredCube_mono (b := (n : ℝ))
    (by exact_mod_cast le_max_left n₁ n₂) h₁
  have hYc := tuplesSupportedIn_centredCube_mono (b := (n : ℝ))
    (by exact_mod_cast le_max_right n₁ n₂) h₂
  have hpl := limitPlateau_eq_mul_of_ergodic hL A hr hl ho hRP hlim hc hE hϖ hXc hYc
  rw [hθ] at hpl
  have hco : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 tendsto_id
  have hq := (((tendsto_spectralRateFn_div_atTop (n : ℝ)).comp hco).mul_const
    (√(functionalSize σ n (push timeZeroMirror.reflectIso X)))).mul_const
    (√(functionalSize σ n Y))
  simp only [zero_mul] at hq
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hq)
  have hbig : ∀ᶠ t : ℝ≥0 in atTop, 2 * (n : ℝ) < t := hco.eventually (eventually_gt_atTop _)
  filter_upwards [hbig] with t ht
  have hsup : maxNorm (timeShiftVec t) = t := by
    rw [timeShiftVec, maxNorm_smul_coordVec, abs_of_nonneg (NNReal.coe_nonneg t)]
  have hv : 2 * (n : ℝ) < maxNorm (timeShiftVec t) := by rwa [hsup]
  obtain ⟨hd, hlaw⟩ :=
    (inverseSquareDecay_of_limit hL A hr hl ho hm hRP hcont hlim hc hϖ hXc hYc).maxNorm_bound _ hv
  rw [hsup, hpl] at hlaw
  rw [Real.dist_eq]
  exact hlaw
end Limits
theorem limitPlateauxTheorem_holds (h₁ : DirectionPictures.singleLatticeInputs)
    (h₂ : TupleRepresentatives.Statement)
    (h₃ : FineLatticeAdicData.AdicDataLatticeData)
    (h₄ : MovingTestFunctions.statement)
    (h₅ : LatticeLimits.LatticeLimitProperties)
    (h₆ : TimeClustering.VacuumClusteringHolds)
    (h₇ : DirectionPictures.CubeVectorDecay) : LimitPlateauxTheorem := by
  intro L hL A σ hcont hRP hlim
  have hc : 0 ≤ spectralRateConst := h₇.1.le
  refine ⟨fun ϖ hϖ X hX Y hY =>
    ⟨sizeAndPlateauLimits_of_limit hL A h₂ h₃ h₁ hRP hlim hc hϖ hX hY,
      inverseSquareDecay_of_limit hL A h₂ h₃ h₁ h₄ hRP hcont hlim hc hϖ hX hY⟩, fun hE => ?_⟩
  obtain ⟨ha, hb⟩ := h₅ L hL.1 hL.2 A σ hRP hlim hcont
  obtain ⟨hσ, hdom⟩ := hb.vacuumHypotheses
  have hclust := clustersInTime_of_ergodic hL A h₂ h₃ h₁ h₄ hRP hcont hlim hc hE
    (fun X => ha.invariant_reflect timeZeroMirror X)
  obtain ⟨-, -, hk, hav, -, hall⟩ := h₆ σ hσ
  have hT := (hall hdom).2
  refine ⟨fun ϖ hϖ X hX Y hY =>
    limitPlateau_eq_mul_of_ergodic hL A h₂ h₃ h₁ hRP hlim hc hE hϖ hX hY, hσ,
    hk.2 hclust, ?_, hclust, hav.1 hclust⟩
  exact (hT.out 2 1).1 hclust
end YangMills.Construction.ReflectionPositivity.LimitPlateaux
