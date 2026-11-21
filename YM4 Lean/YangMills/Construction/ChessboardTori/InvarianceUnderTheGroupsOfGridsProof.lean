import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import YangMills.Construction.ChessboardTori.InvarianceUnderTheGroupsOfGrids
import YangMills.Construction.ChessboardTori.PeriodicGibbsStatesAreInvariantAndReflectionPositive
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace GridGroupInvariance
open InfiniteLattice (Link GaugeField IsSymmetricUnder IsLocalObservable IsRegionMeasurable
  IsBoundedObservable IsReflectionPositiveAt IsShiftInvariant LatticeSymmetry LatticeMirror
  ReflectionClass LatticePoint AmbientSpace linksWithin hyperplaneReflect regionSigma linkSigma
  axisStep)
variable {a : ℝ}
theorem regionSigma_mono {S T : Set AmbientSpace} (h : S ⊆ T) :
    (regionSigma S : MeasurableSpace (GaugeField a)) ≤ regionSigma T := by apply _root_.YangMills.Construction.InfiniteLattice.regionSigma_mono <;> assumption
theorem latticeSymmetry_ext {s t : LatticeSymmetry a} (h : s.toFun = t.toFun) : s = t := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem actOn_eq_self_of_toFun_eq (s : LatticeSymmetry a) (h : ∀ x, s.toFun x = x)
    (A : GaugeField a → ℂ) : s.actOn A = A := by
  funext U
  have hU : s.pullbackField U = U := by
    refine Subtype.ext (funext fun b => ?_)
    have hb : s.linkMap b = b :=
      Link.ext (Subtype.ext (h b.initial)) (Subtype.ext (h b.terminal))
    change U (s.linkMap b) = U b
    rw [hb]
  simp [LatticeSymmetry.actOn, hU]
theorem isBoundedObservable_actOn (s : LatticeSymmetry a) (hc : Continuous s.pullbackField)
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable (s.actOn A) := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨hm.comp hc.measurable, C, fun U => hC _⟩
theorem isBoundedObservable_add_const {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (c : ℂ) : IsBoundedObservable fun U => A U + c := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨hm.add_const c, C + ‖c‖, fun U => (norm_add_le _ _).trans (by linarith [hC U])⟩
theorem isBoundedObservable_conjReflect (P : LatticeMirror a)
    (hc : Continuous P.symmetry.pullbackField) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) : IsBoundedObservable (P.conjReflect A) := by
  obtain ⟨hm, C, hC⟩ := isBoundedObservable_actOn P.symmetry hc hA
  refine ⟨Complex.continuous_conj.measurable.comp hm, C, fun U => ?_⟩
  simpa [LatticeMirror.conjReflect] using hC U
theorem isBoundedObservable_mul {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => A U * B U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) : Integrable A ν := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem integral_add_const_mul_conjReflect (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (P : LatticeMirror a) (hc : Continuous P.symmetry.pullbackField) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) (c : ℂ) :
    ∫ U, (A U + c) * P.conjReflect (fun U => A U + c) U ∂ν =
      (∫ U, A U * P.conjReflect A U ∂ν) + conj c * (∫ U, A U ∂ν) +
        c * conj (∫ U, P.symmetry.actOn A U ∂ν) + c * conj c := by
  have hθ := isBoundedObservable_conjReflect P hc hA
  have i0 : Integrable (fun U => A U * P.conjReflect A U) ν :=
    integrable_of_isBoundedObservable ν (isBoundedObservable_mul hA hθ)
  have i1 : Integrable (fun U => conj c * A U) ν :=
    (integrable_of_isBoundedObservable ν hA).const_mul _
  have i2 : Integrable (fun U => c * P.conjReflect A U) ν :=
    (integrable_of_isBoundedObservable ν hθ).const_mul _
  have i01 : Integrable (fun U => A U * P.conjReflect A U + conj c * A U) ν := i0.add i1
  have i012 : Integrable
      (fun U => A U * P.conjReflect A U + conj c * A U + c * P.conjReflect A U) ν :=
    i01.add i2
  have hpt : ∀ U, (A U + c) * P.conjReflect (fun U => A U + c) U =
      A U * P.conjReflect A U + conj c * A U + c * P.conjReflect A U + c * conj c := by
    intro U
    simp only [LatticeMirror.conjReflect, LatticeSymmetry.actOn, map_add]
    ring
  have hconj : ∫ U, P.conjReflect A U ∂ν = conj (∫ U, P.symmetry.actOn A U ∂ν) :=
    integral_conj
  simp_rw [hpt]
  rw [integral_add i012 (integrable_const _), integral_add i01 i2, integral_add i0 i1,
    integral_const_mul, integral_const_mul, hconj, integral_const]
  simp
theorem integral_actOn_symmetry_of_halfSpace (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (P : LatticeMirror a) (hc : Continuous P.symmetry.pullbackField)
    (hRP : IsReflectionPositiveAt ν P) {H : Set AmbientSpace} (hH : P.IsHalfSpace H)
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) (hl : IsLocalObservable A)
    (hm : IsRegionMeasurable H A) :
    ∫ U, P.symmetry.actOn A U ∂ν = ∫ U, A U ∂ν := by
  have pos : ∀ c : ℂ, 0 ≤ ∫ U, (A U + c) * P.conjReflect (fun U => A U + c) U ∂ν := by
    intro c
    obtain ⟨S, hS, hAS⟩ := hl
    have hl' : IsLocalObservable fun U => A U + c :=
      ⟨S, hS, Measurable.add_const (m := regionSigma S) hAS c⟩
    have hm' : IsRegionMeasurable H fun U => A U + c :=
      Measurable.add_const (m := regionSigma H) hm c
    exact hRP.2 H hH _ (isBoundedObservable_add_const hA c) hl' hm'
  have h0 := hRP.2 H hH A hA hl hm
  have h1 := pos 1
  have h2 := pos Complex.I
  rw [integral_add_const_mul_conjReflect ν P hc hA] at h1 h2
  have i0 := (Complex.le_def.mp h0).2
  have i1 := (Complex.le_def.mp h1).2
  have i2 := (Complex.le_def.mp h2).2
  simp at i0 i1 i2
  apply Complex.ext <;> linarith
theorem realNormal_axial (μ : Fin 4) :
    (ReflectionClass.axial μ).realNormal = Pi.single μ 1 := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_axial <;> assumption
theorem realNormal_axial_dotProduct (μ : Fin 4) (x : AmbientSpace) :
    (ReflectionClass.axial μ).realNormal ⬝ᵥ x = x μ := by
  rw [realNormal_axial]
  simp
theorem hyperplaneReflect_axial (μ : Fin 4) (c : ℝ) (x : AmbientSpace) :
    hyperplaneReflect (ReflectionClass.axial μ).realNormal c x =
      x - (2 * (x μ - c)) • (Pi.single μ 1 : AmbientSpace) := by
  unfold hyperplaneReflect
  rw [InfiniteLattice.ReflectionClass.realNormal_dot_axial, realNormal_axial_dotProduct,
    realNormal_axial, div_one]
theorem coe_zsmul_axisStep (n : ℤ) (μ : Fin 4) :
    ((n • axisStep a μ : LatticePoint a) : AmbientSpace) =
      (n : ℝ) • (Pi.single μ a : AmbientSpace) := by
  funext κ
  simp [axisStep]
theorem symmetry_comp_shift (P : LatticeMirror a) (μ : Fin 4)
    (hP : P.cls = ReflectionClass.axial μ) (n : ℤ) :
    P.symmetry.comp (InfiniteLattice.shift (n • axisStep a μ)) =
      (InfiniteLattice.shift (-(n • axisStep a μ))).comp P.symmetry := by
  apply latticeSymmetry_ext
  funext x
  obtain ⟨F, c, hc⟩ := P
  cases hP
  change hyperplaneReflect (ReflectionClass.axial μ).realNormal c
      (x + ((n • axisStep a μ : LatticePoint a) : AmbientSpace)) =
    hyperplaneReflect (ReflectionClass.axial μ).realNormal c x +
      ((-(n • axisStep a μ) : LatticePoint a) : AmbientSpace)
  rw [hyperplaneReflect_axial, hyperplaneReflect_axial]
  simp only [AddSubgroup.coe_neg, coe_zsmul_axisStep]
  funext κ
  by_cases h : κ = μ
  · subst h
    simp
    ring
  · simp [Pi.single_eq_of_ne h]
theorem integral_actOn_symmetry_of_bounded (ha : 0 < a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν]
    (hact : InfiniteLattice.SmearedEnergyAndSymmetryAction.SymmetryActionProperties a)
    (hcomp : InfiniteLattice.SmearedEnergyAndSymmetryAction.ActOn_comp a)
    (P : LatticeMirror a) (μ : Fin 4) (hP : P.cls = ReflectionClass.axial μ)
    (hτ : IsShiftInvariant ν) (hRP : IsReflectionPositiveAt ν P) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hm : IsRegionMeasurable S A) :
    ∫ U, P.symmetry.actOn A U ∂ν = ∫ U, A U ∂ν := by
  have hcr : Continuous P.symmetry.pullbackField := (hact P.symmetry).2.2.1
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS
  obtain ⟨n, hn⟩ := exists_int_gt ((R + P.level) / a)
  have hn' : R + P.level < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
  set v : LatticePoint a := n • axisStep a μ with hv
  obtain ⟨hvo, hvm, -⟩ := (hact (InfiniteLattice.shift v)).2.2.2 S A hA hm
  have hvalue : ∀ x : AmbientSpace, (x + (v : AmbientSpace)) μ = x μ + (n : ℝ) * a := by
    intro x
    have h := congrFun (coe_zsmul_axisStep (a := a) n μ) μ
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at h
    rw [Pi.add_apply, hv, h]
  have hsub : (InfiniteLattice.shift v).setImage S ⊆
      {x | P.level ≤ P.cls.realNormal ⬝ᵥ x} := by
    rintro _ ⟨x, hx, rfl⟩
    change P.level ≤ P.cls.realNormal ⬝ᵥ (x + (v : AmbientSpace))
    rw [hP, realNormal_axial_dotProduct, hvalue]
    have h1 : |x μ| ≤ R := by
      have := (norm_le_pi_norm x μ).trans (hR x hx)
      simpa using this
    linarith [(abs_le.mp h1).1]
  have hbounded : Bornology.IsBounded ((InfiniteLattice.shift v).setImage S) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨R + ‖(v : AmbientSpace)‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (norm_add_le _ _).trans (by linarith [hR x hx])
  have hhalf : IsRegionMeasurable {x | P.level ≤ P.cls.realNormal ⬝ᵥ x}
      ((InfiniteLattice.shift v).actOn A) :=
    hvm.mono (regionSigma_mono hsub) le_rfl
  have hstep := integral_actOn_symmetry_of_halfSpace ν P hcr hRP (Or.inl rfl) hvo
    ⟨_, hbounded, hvm⟩ hhalf
  have hrA := isBoundedObservable_actOn P.symmetry hcr hA
  have hswap : P.symmetry.actOn ((InfiniteLattice.shift v).actOn A) =
      (InfiniteLattice.shift (-v)).actOn (P.symmetry.actOn A) := by
    rw [← hcomp _ _ A hA, ← hcomp _ _ A hA, hv, symmetry_comp_shift P μ hP n]
  rw [hswap, hτ (-v) _ hrA, hτ v A hA] at hstep
  exact hstep
theorem isSymmetricUnder_of_bounded
    (hlinks : InfiniteLattice.ConfigurationSpace.BorelEqLinkSigma a)
    (s : LatticeSymmetry a) (hc : Continuous s.pullbackField) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν]
    (hloc : ∀ S : Set AmbientSpace, Bornology.IsBounded S → ∀ A : GaugeField a → ℂ,
      IsBoundedObservable A → IsRegionMeasurable S A →
        ∫ U, s.actOn A U ∂ν = ∫ U, A U ∂ν) :
    IsSymmetricUnder ν s := by
  have hmeas : Measurable s.pullbackField := hc.measurable
  have hborel : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a)) := hlinks.1
  have hle : ∀ S : Set AmbientSpace,
      (regionSigma S : MeasurableSpace (GaugeField a)) ≤
        (inferInstance : MeasurableSpace (GaugeField a)) := fun S =>
    (show (regionSigma S : MeasurableSpace (GaugeField a)) ≤ linkSigma (univ : Set (Link a)) from
      iSup₂_le fun b _ => le_iSup₂_of_le b (mem_univ b) le_rfl).trans_eq hborel.symm
  have hmap : ν.map s.pullbackField = ν := by
    refine ext_of_generate_finite
      {E | ∃ S : Set AmbientSpace, Bornology.IsBounded S ∧ MeasurableSet[regionSigma S] E}
      ?_ ?_ ?_ ?_
    · refine le_antisymm ?_ ?_
      · refine hborel.le.trans (iSup₂_le fun b _ => ?_)
        intro E hE
        refine MeasurableSpace.measurableSet_generateFrom
          ⟨{(b.initial : AmbientSpace), (b.terminal : AmbientSpace)},
            (Set.toFinite _).isBounded, ?_⟩
        have hb : b ∈ (linksWithin {(b.initial : AmbientSpace), (b.terminal : AmbientSpace)} :
            Set (Link a)) :=
          ⟨by simp, by simp⟩
        exact (le_iSup₂_of_le b hb le_rfl :
          MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance ≤
            regionSigma {(b.initial : AmbientSpace), (b.terminal : AmbientSpace)}) E hE
      · refine MeasurableSpace.generateFrom_le ?_
        rintro E ⟨S, -, hE⟩
        exact hle S E hE
    · rintro E ⟨S, hS, hE⟩ F ⟨T, hT, hF⟩ -
      exact ⟨S ∪ T, hS.union hT,
        MeasurableSet.inter (regionSigma_mono subset_union_left E hE)
          (regionSigma_mono subset_union_right F hF)⟩
    · rintro E ⟨S, hS, hE⟩
      have hES : MeasurableSet E := hle S E hE
      have hAo : IsBoundedObservable (E.indicator fun _ => (1 : ℂ)) := by
        refine ⟨measurable_const.indicator hES, 1, fun U => ?_⟩
        by_cases h : U ∈ E <;> simp [h]
      have hAm : IsRegionMeasurable S (E.indicator fun _ => (1 : ℂ)) :=
        Measurable.indicator (m := regionSigma S) measurable_const hE
      have h := hloc S hS _ hAo hAm
      have h1 : s.actOn (E.indicator fun _ => (1 : ℂ)) =
          (s.pullbackField ⁻¹' E).indicator fun _ => (1 : ℂ) := by
        funext U
        by_cases h : s.pullbackField U ∈ E <;>
          simp [LatticeSymmetry.actOn, Set.indicator, h]
      rw [h1, integral_indicator_const _ (hmeas hES), integral_indicator_const _ hES] at h
      have h2 : ν.real (s.pullbackField ⁻¹' E) = ν.real E := by
        simpa using h
      rw [Measure.map_apply hmeas hES]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h2
    · rw [Measure.map_apply hmeas MeasurableSet.univ]
      simp
  intro A hA
  have h : ∫ U, A U ∂(ν.map s.pullbackField) = ∫ U, A (s.pullbackField U) ∂ν :=
    integral_map hmeas.aemeasurable hA.1.aestronglyMeasurable
  change ∫ U, A (s.pullbackField U) ∂ν = _
  rw [← h, hmap]
def wallMirror {D : ChessboardSetup} (g : ReflectionGrid D) (μ : Fin 4) (k : ℤ) :
    LatticeMirror D.mesh where
  cls := ReflectionClass.axial μ
  level := g.origin μ + k * g.cellSide
  level_mem := by
    obtain ⟨i, hi⟩ := g.origin_mem μ
    refine ⟨2 * i + 1 + 2 * k * g.cellRatio, ?_⟩
    rw [hi, g.cellSide_eq]
    push_cast
    ring
theorem wallMirror_bisectsLinks {D : ChessboardSetup} (g : ReflectionGrid D) (μ : Fin 4)
    (k : ℤ) : (wallMirror g μ k).BisectsLinks := by
  obtain ⟨i, hi⟩ := g.origin_mem μ
  refine ⟨i + k * g.cellRatio, ?_⟩
  change g.origin μ + k * g.cellSide = _
  rw [hi, g.cellSide_eq]
  push_cast
  ring
theorem wallMirror_symmetry_toFun {D : ChessboardSetup} (g : ReflectionGrid D) (μ : Fin 4)
    (k : ℤ) : (wallMirror g μ k).symmetry.toFun = g.reflect μ k := by
  funext x
  change hyperplaneReflect (ReflectionClass.axial μ).realNormal (g.origin μ + k * g.cellSide) x = _
  rw [hyperplaneReflect_axial]
  simp only [ReflectionGrid.reflect, coordVec, sub_sub]
theorem isSymmetricUnder_reflectionGroup {D : ChessboardSetup} (g : ReflectionGrid D)
    (ν : Measure D.GaugeField)
    (hact : InfiniteLattice.SmearedEnergyAndSymmetryAction.SymmetryActionProperties D.mesh)
    (hcomp : InfiniteLattice.SmearedEnergyAndSymmetryAction.ActOn_comp D.mesh)
    (hrefl : ∀ (μ : Fin 4) (k : ℤ), IsSymmetricUnder ν (wallMirror g μ k).symmetry)
    (r : g.reflectionGroup) : IsSymmetricUnder ν (g.toLatticeSym r) := by
  have hobs : ∀ (s : LatticeSymmetry D.mesh) {A : D.GaugeField → ℂ}, IsBoundedObservable A →
      IsBoundedObservable (s.actOn A) := fun s _ hA =>
    isBoundedObservable_actOn s (hact s).2.2.1 hA
  have key : ∀ (x : Equiv.Perm AmbientSpace) (_ : x ∈ g.reflectionGroup)
      (s : LatticeSymmetry D.mesh), s.toFun = x → IsSymmetricUnder ν s := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun (x : Equiv.Perm AmbientSpace) _ =>
        ∀ s : LatticeSymmetry D.mesh, s.toFun = x → IsSymmetricUnder ν s)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨μ, k⟩, rfl⟩ s hs
      have : s = (wallMirror g μ k).symmetry :=
        latticeSymmetry_ext (hs.trans (wallMirror_symmetry_toFun g μ k).symm)
      rw [this]
      exact hrefl μ k
    · intro s hs A _
      rw [actOn_eq_self_of_toFun_eq s fun x => congrFun hs x]
    · intro x y hx hy ihx ihy s hs A hA
      have hsc : s = (g.toLatticeSym ⟨x, hx⟩).comp (g.toLatticeSym ⟨y, hy⟩) :=
        latticeSymmetry_ext hs
      rw [hsc, hcomp _ _ A hA, ihx (g.toLatticeSym ⟨x, hx⟩) rfl _ (hobs _ hA),
        ihy (g.toLatticeSym ⟨y, hy⟩) rfl A hA]
    · intro x hx ihx s hs A hA
      have hid : ∀ z, ((g.toLatticeSym ⟨x, hx⟩).comp s).toFun z = z := by
        intro z
        change x (s.toFun z) = z
        rw [hs]
        simp
      have hback := hcomp (g.toLatticeSym ⟨x, hx⟩) s A hA
      rw [actOn_eq_self_of_toFun_eq _ hid] at hback
      rw [← ihx (g.toLatticeSym ⟨x, hx⟩) rfl _ (hobs s hA), ← hback]
  exact key r.1 r.2 _ rfl
end GridGroupInvariance
open GridGroupInvariance in
theorem GridGroupInvariance.holds
    (hobs : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    (hspace : InfiniteLattice.ConfigurationSpace.Main)
    (hstrong : PeriodicStateSymmetries.Statement) :
    GridGroupInvariance.Statement := by
  intro D
  have ha := D.mesh_pos
  obtain ⟨-, hact, hcomp, -⟩ := hobs D.mesh ha
  obtain ⟨-, hlinks, -⟩ := hspace D.mesh ha
  have one : ∀ (ν : Measure D.GaugeField) [IsProbabilityMeasure ν] (μ : Fin 4)
      (P : InfiniteLattice.LatticeMirror D.mesh), P.cls = InfiniteLattice.ReflectionClass.axial μ →
      InfiniteLattice.IsShiftInvariant ν → InfiniteLattice.IsReflectionPositiveAt ν P →
      InfiniteLattice.IsSymmetricUnder ν P.symmetry := by
    intro ν _ μ P hP hτ hRP
    exact isSymmetricUnder_of_bounded hlinks P.symmetry (hact P.symmetry).2.2.1 ν
      fun S hS A hA hm =>
        integral_actOn_symmetry_of_bounded ha ν hact hcomp P μ hP hτ hRP hS hA hm
  have two : ∀ (ν : Measure D.GaugeField) [IsProbabilityMeasure ν],
      InfiniteLattice.IsShiftInvariant ν →
      (∀ (μ : Fin 4) (P : InfiniteLattice.LatticeMirror D.mesh),
        P.cls = InfiniteLattice.ReflectionClass.axial μ → P.BisectsLinks →
        InfiniteLattice.IsReflectionPositiveAt ν P) →
      D.IsGridSymmetric ν := by
    intro ν _ hτ hRP
    have hgroup : ∀ (g : ReflectionGrid D) (r : g.reflectionGroup),
        InfiniteLattice.IsSymmetricUnder ν (g.toLatticeSym r) := fun g r =>
      isSymmetricUnder_reflectionGroup g ν hact hcomp
        (fun μ k => one ν μ _ rfl hτ (hRP μ _ rfl (wallMirror_bisectsLinks g μ k))) r
    exact ⟨fun g _ r => hgroup g r, fun r => hgroup D.unitReflectionGrid r⟩
  refine ⟨fun ν _ μ P hP _ hτ hRP => one ν μ P hP hτ hRP, two, ?_⟩
  intro ν hν
  have hgibbs : InfiniteLattice.IsPeriodicGibbs D.β ν := hν
  have : IsProbabilityMeasure ν := hgibbs.1.1
  obtain ⟨hτ, hcoord, -, -⟩ := hstrong D ν hν
  refine two ν hτ fun μ P hP _ => ?_
  obtain ⟨F, c, hc⟩ := P
  cases hP
  exact (hcoord μ c hc).2
end YangMills.Construction.ChessboardTori
end
