import YangMills.Construction.InfiniteLattice.InvariantFunctionsOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LocalObservablesDetermineMeasuresAndIsometriesOnIntegrableFunctions
import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ShiftInvariantFunctions
theorem countable_latticePoint_one : Countable (LatticePoint 1) := by
  have hs : Function.Surjective
      (fun m : Fin 4 → ℤ => (⟨fun μ => (m μ : ℝ) * 1, m, fun _ => rfl⟩ : LatticePoint 1)) := by
    rintro ⟨x, m, hm⟩
    exact ⟨m, Subtype.ext (funext fun μ => (hm μ).symm)⟩
  exact hs.countable
theorem linkMap_shift_shift (u v : LatticePoint 1) (b : Link 1) :
    (shift u).linkMap ((shift v).linkMap b) = (shift (u + v)).linkMap b := by
  apply Link.ext
  · apply Subtype.ext
    change (b.initial : AmbientSpace) + (v : AmbientSpace) + (u : AmbientSpace) =
      (b.initial : AmbientSpace) + ((u + v : LatticePoint 1) : AmbientSpace)
    rw [AddSubgroup.coe_add]
    abel
  · apply Subtype.ext
    change (b.terminal : AmbientSpace) + (v : AmbientSpace) + (u : AmbientSpace) =
      (b.terminal : AmbientSpace) + ((u + v : LatticePoint 1) : AmbientSpace)
    rw [AddSubgroup.coe_add]
    abel
theorem pullbackField_shift_shift (u v : LatticePoint 1) (U : GaugeField 1) :
    (shift v).pullbackField ((shift u).pullbackField U) =
      (shift (u + v)).pullbackField U := by
  apply Subtype.ext
  funext b
  exact congrArg U.1 (linkMap_shift_shift u v b)
theorem pullbackField_shift_zero (U : GaugeField 1) :
    (shift (0 : LatticePoint 1)).pullbackField U = U := by
  apply Subtype.ext
  funext b
  have hb : (shift (0 : LatticePoint 1)).linkMap b = b := by
    apply Link.ext
    · apply Subtype.ext
      change (b.initial : AmbientSpace) + ((0 : LatticePoint 1) : AmbientSpace) = (b.initial : AmbientSpace)
      simp
    · apply Subtype.ext
      change (b.terminal : AmbientSpace) + ((0 : LatticePoint 1) : AmbientSpace) = (b.terminal : AmbientSpace)
      simp
  exact congrArg U.1 hb
def setStabilizer (I : Set (GaugeField 1)) : AddSubgroup (LatticePoint 1) where
  carrier := {v | (shift v).pullbackField ⁻¹' I = I}
  add_mem' := by
    intro u v hu hv
    ext U
    change (shift (u + v)).pullbackField U ∈ I ↔ U ∈ I
    rw [← pullbackField_shift_shift]
    exact (Set.ext_iff.mp hv _).trans (Set.ext_iff.mp hu U)
  zero_mem' := by
    ext U
    change (shift (0 : LatticePoint 1)).pullbackField U ∈ I ↔ U ∈ I
    rw [pullbackField_shift_zero]
  neg_mem' := by
    intro v hv
    ext U
    change (shift (-v)).pullbackField U ∈ I ↔ U ∈ I
    have h := Set.ext_iff.mp hv ((shift (-v)).pullbackField U)
    have h' : (shift v).pullbackField ((shift (-v)).pullbackField U) = U := by
      rw [pullbackField_shift_shift, neg_add_cancel,
        pullbackField_shift_zero]
    have h'' : (shift v).pullbackField ((shift (-v)).pullbackField U) ∈ I ↔
        (shift (-v)).pullbackField U ∈ I := h
    rw [h'] at h''
    exact h''.symm
def shiftSubgroup : ShiftPair → AddSubgroup (LatticePoint 1)
  | .allShifts => ⊤
  | .axis μ => AddSubgroup.zmultiples (axisStep 1 μ)
theorem mem_shiftSubgroup (p : ShiftPair) (v : LatticePoint 1) :
    v ∈ shiftSubgroup p ↔ v ∈ p.shifts := by
  cases p with
  | allShifts => exact ⟨fun _ => Set.mem_univ v, fun _ => AddSubgroup.mem_top v⟩
  | axis μ =>
    constructor
    · intro h
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, hk.symm⟩
theorem measurableSet_sigma_iff (p : ShiftPair) (I : Set (GaugeField 1)) :
    MeasurableSet[p.sigma] I ↔
      MeasurableSet I ∧ ∀ v ∈ p.shifts, (shift v).pullbackField ⁻¹' I = I := by
  cases p with
  | allShifts =>
    change IsShiftInvariantSet I ↔ _
    constructor
    · intro h
      exact ⟨h.1, fun v _ => ((shift v).actOn_indicator_eq_iff I).mp (h.2 v)⟩
    · intro h
      exact ⟨h.1, fun v =>
        ((shift v).actOn_indicator_eq_iff I).mpr (h.2 v (Set.mem_univ v))⟩
  | axis μ =>
    change IsAxisShiftInvariantSet μ I ↔ _
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      rintro v ⟨k, rfl⟩
      have hs : axisStep 1 μ ∈ setStabilizer I :=
        ((shift (axisStep 1 μ)).actOn_indicator_eq_iff I).mp h.2
      exact (setStabilizer I).zsmul_mem hs k
    · intro h
      refine ⟨h.1, ((shift (axisStep 1 μ)).actOn_indicator_eq_iff I).mpr ?_⟩
      exact h.2 _ ⟨1, (one_zsmul _).symm⟩
theorem measurable_sigma_iff (p : ShiftPair) (F : GaugeField 1 → ℂ) (hF : Measurable F) :
    Measurable[p.sigma] F ↔ ∀ v ∈ p.shifts, (shift v).actOn F = F := by
  constructor
  · intro h v hv
    funext U
    have hI : MeasurableSet[p.sigma] (F ⁻¹' {F U}) := h (measurableSet_singleton _)
    have hfix := ((measurableSet_sigma_iff p _).mp hI).2 v hv
    have hU : U ∈ F ⁻¹' {F U} := rfl
    exact (Set.ext_iff.mp hfix U).mpr hU
  · intro h C hC
    refine (measurableSet_sigma_iff p _).mpr ⟨hF hC, fun v hv => ?_⟩
    change ((shift v).actOn F) ⁻¹' C = F ⁻¹' C
    rw [h v hv]
theorem exists_sigma_measurable_ae_eq (hτ : ∀ v : LatticePoint 1, Measurable (shift v).pullbackField)
    (p : ShiftPair) (ν : Measure (GaugeField 1)) (F : GaugeField 1 → ℂ)
    (hF : Measurable F)
    (h : ∀ v ∈ p.shifts, (shift v).actOn F =ᵐ[ν] F) :
    ∃ F' : GaugeField 1 → ℂ, Measurable[p.sigma] F' ∧ F' =ᵐ[ν] F := by
  classical
  have := countable_latticePoint_one
  let A : Set (GaugeField 1) :=
    {U | ∀ v ∈ p.shifts, F ((shift v).pullbackField U) = F U}
  have hAeq : A = ⋂ v ∈ p.shifts, {U | F ((shift v).pullbackField U) = F U} := by
    ext U
    simp [A]
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact MeasurableSet.biInter (Set.to_countable _) fun v _ =>
      measurableSet_eq_fun (hF.comp (hτ v)) hF
  have hae : ∀ᵐ U ∂ν, U ∈ A := by
    exact show ∀ᵐ U ∂ν, ∀ v : LatticePoint 1, v ∈ p.shifts →
        F ((shift v).pullbackField U) = F U from by
      rw [ae_all_iff]
      intro v
      by_cases hv : v ∈ p.shifts
      · filter_upwards [h v hv] with U hU _
        exact hU
      · exact Filter.Eventually.of_forall fun U h' => absurd h' hv
  have hfwd : ∀ u ∈ p.shifts, ∀ U ∈ A, (shift u).pullbackField U ∈ A := by
    intro u hu U hU v hv
    have huv : u + v ∈ p.shifts := (mem_shiftSubgroup p _).mp
      (add_mem ((mem_shiftSubgroup p _).mpr hu) ((mem_shiftSubgroup p _).mpr hv))
    rw [pullbackField_shift_shift, hU (u + v) huv, hU u hu]
  have hback : ∀ u ∈ p.shifts, ∀ U, (shift u).pullbackField U ∈ A → U ∈ A := by
    intro u hu U hU
    have hnu : -u ∈ p.shifts := (mem_shiftSubgroup p _).mp
      (neg_mem ((mem_shiftSubgroup p _).mpr hu))
    have h1 := hfwd (-u) hnu _ hU
    rwa [pullbackField_shift_shift, add_neg_cancel,
      pullbackField_shift_zero] at h1
  refine ⟨A.indicator F, (measurable_sigma_iff p _ (hF.indicator hA)).mpr fun v hv => ?_, ?_⟩
  · funext U
    change A.indicator F ((shift v).pullbackField U) = A.indicator F U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem (hfwd v hv U hU), Set.indicator_of_mem hU]
      exact hU v hv
    · have hU' : (shift v).pullbackField U ∉ A := fun h' => hU (hback v hv U h')
      rw [Set.indicator_of_notMem hU', Set.indicator_of_notMem hU]
  · filter_upwards [hae] with U hU
    exact Set.indicator_of_mem hU F
theorem measurePreserving_of_isSymmetricUnder (v : LatticePoint 1)
    (hτ : Measurable (shift v).pullbackField)
    (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (hν : IsSymmetricUnder ν (shift v)) :
    MeasurePreserving (shift v).pullbackField ν ν := by
  refine ⟨hτ, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hτ hA]
  have hobs : IsBoundedObservable (A.indicator (fun _ => (1 : ℂ))) :=
    ⟨measurable_const.indicator hA, 1, fun U => by
      by_cases h : U ∈ A <;> simp [h]⟩
  have h1 := hν _ hobs
  have h2 : (shift v).actOn (A.indicator (fun _ => (1 : ℂ))) =
      ((shift v).pullbackField ⁻¹' A).indicator (fun _ => (1 : ℂ)) := by
    funext U
    by_cases h : (shift v).pullbackField U ∈ A
    · have h' : U ∈ (shift v).pullbackField ⁻¹' A := h
      rw [Set.indicator_of_mem h']
      exact Set.indicator_of_mem h _
    · have h' : U ∉ (shift v).pullbackField ⁻¹' A := h
      rw [Set.indicator_of_notMem h']
      exact Set.indicator_of_notMem h _
  rw [h2, integral_indicator_const _ (hτ hA), integral_indicator_const _ hA] at h1
  have h3 : ν.real ((shift v).pullbackField ⁻¹' A) = ν.real A := by
    simpa using h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h3
theorem measurePreserving_shift_nsmul (v : LatticePoint 1) (ν : Measure (GaugeField 1))
    (hv : MeasurePreserving (shift v).pullbackField ν ν) (m : ℕ) :
    MeasurePreserving (shift (m • v)).pullbackField ν ν := by
  induction m with
  | zero =>
    have h0 : (shift ((0 : ℕ) • v)).pullbackField = id := by
      funext U
      rw [zero_nsmul, pullbackField_shift_zero]
      rfl
    rw [h0]
    exact MeasurePreserving.id ν
  | succ m ih =>
    have h1 : (shift ((m + 1) • v)).pullbackField =
        (shift v).pullbackField ∘ (shift (m • v)).pullbackField := by
      funext U
      rw [succ_nsmul, Function.comp_apply, pullbackField_shift_shift]
    rw [h1]
    exact hv.comp ih
theorem invariantL2ApproxByHalfSpace_holds
    (hAct : YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hMeas : LocalDeterminationAndIntegrableAction)
    (hτ : ∀ v : LatticePoint 1, Measurable (shift v).pullbackField)
    (μ : Fin 4) (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν] :
    InvariantL2ApproxByHalfSpace μ ν := by
  intro hinv F hF ε hε
  obtain ⟨-, himg, -, hlinks, hnorm, -, -, -, -, -⟩ := hAct
  obtain ⟨g, hg, hFg⟩ := hF
  have hgB : Measurable g := hg.mono (axisShiftInvariantSigma_le_borel μ) le_rfl
  obtain ⟨H₀, cH, oH, lH, hle⟩ :=
    (hMeas ν (shift (axisStep 1 μ))).2.1 2 (Or.inr rfl) F ε hε
  obtain ⟨S, bS, mS⟩ := lH
  obtain ⟨R, hR⟩ := bS.exists_norm_le
  let m : ℕ := ⌈R⌉₊
  let v : LatticePoint 1 := m • axisStep 1 μ
  have hvμ : (v : AmbientSpace) μ = (m : ℝ) := by
    simp [v, axisStep]
  have hsub : (shift v).setImage S ⊆ closedHalfSpace μ := by
    rintro _ ⟨x, hx, rfl⟩
    change 0 ≤ (x + (v : AmbientSpace)) μ
    rw [Pi.add_apply, hvμ]
    have h1 : |x μ| ≤ R := (norm_le_pi_norm x μ).trans (hR x hx)
    have h2 : R ≤ (m : ℝ) := Nat.le_ceil R
    have h3 := (abs_le.mp h1).1
    linarith
  let H : GaugeField 1 → ℂ := (shift v).actOn H₀
  have hcont : Continuous (shift v).pullbackField :=
    (hlinks (shift v)).2.1.continuous
  have cH' : Continuous H := cH.comp hcont
  obtain ⟨oH', -, lH'⟩ := hnorm (shift v) H₀ oH
  have hHS : H ∈ unitRegionObservables ((shift v).setImage S) := by
    rw [← himg]
    exact ⟨H₀, ⟨oH, mS⟩, rfl⟩
  have hHhalf : H ∈ halfSpaceLocalObservables μ :=
    ⟨⟨oH', hHS.2.mono (regionSigma_mono hsub) le_rfl⟩, lH' ⟨S, bS, mS⟩⟩
  obtain ⟨-, C, hC⟩ := id oH'
  have hHm : MemLp H 2 ν := MemLp.of_bound oH'.1.aestronglyMeasurable C (ae_of_all _ hC)
  refine ⟨H, cH', hHhalf, hHm, ?_⟩
  have hgτ : (shift v).actOn g = g :=
    (measurable_sigma_iff (.axis μ) g hgB).mp hg v ⟨m, by simp [v]⟩
  have hmp : MeasurePreserving (shift v).pullbackField ν ν :=
    measurePreserving_shift_nsmul (axisStep 1 μ) ν
      (measurePreserving_of_isSymmetricUnder _ (hτ _) ν hinv) m
  have hcong : ⇑(F - hHm.toLp H) =ᵐ[ν] (g - H₀) ∘ (shift v).pullbackField := by
    filter_upwards [Lp.coeFn_sub F (hHm.toLp H), hHm.coeFn_toLp, hFg] with U h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    change g U - H U = g ((shift v).pullbackField U) - H U
    exact congrArg (· - H U) (congrFun hgτ U).symm
  have hcong2 : (⇑F - H₀) =ᵐ[ν] (g - H₀) := by
    filter_upwards [hFg] with U h3
    rw [Pi.sub_apply, Pi.sub_apply, h3]
  have hnormeq : eLpNorm (⇑(F - hHm.toLp H)) 2 ν = eLpNorm (⇑F - H₀) 2 ν := by
    rw [eLpNorm_congr_ae hcong,
      eLpNorm_comp_measurePreserving (hgB.sub oH.1).aestronglyMeasurable hmp,
      eLpNorm_congr_ae hcong2]
  rw [Lp.norm_def, hnormeq]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle
theorem invariantFunctionsTheorem_holds
    (hAct : YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hMeas : LocalDeterminationAndIntegrableAction) :
    InvariantFunctionsTheorem := by
  have hτ : ∀ v : LatticePoint 1, Measurable (shift v).pullbackField := fun v =>
    (hAct.2.2.2.1 (shift v)).2.1.continuous.measurable
  refine ⟨fun p F hF => measurable_sigma_iff p F hF, fun ν _ => ⟨fun p F hF h => ?_, fun μ => ?_⟩⟩
  · exact exists_sigma_measurable_ae_eq hτ p ν F hF h
  · exact invariantL2ApproxByHalfSpace_holds hAct hMeas hτ μ ν
end YangMills.Construction.InfiniteLattice.ShiftInvariantFunctions
