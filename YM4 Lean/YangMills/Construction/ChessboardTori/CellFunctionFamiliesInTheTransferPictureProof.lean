import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureOfAGrid
import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPicture
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorus
import YangMills.Construction.ChessboardTori.ReflectionsOfSlabs
import YangMills.Construction.ChessboardTori.ThreeConsequencesOfTheTraceFormula
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace TransferSetupCellFamilies
section Factorization
variable {D : ChessboardSetup}
local instance instSecondCountableGaugeGroup :
    SecondCountableTopology Conventions.StandingParameters.gaugeGroup := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _
theorem lt_coord_lt_of_mem_interior_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) {x : AmbientSpace}
    (hx : x ∈ interior (g.cell k)) (μ : Fin 4) :
    g.origin μ + g.cellSide * k μ < x μ ∧ x μ < g.origin μ + g.cellSide * k μ + g.cellSide := by
  have hS : g.cell k = Set.pi univ fun ν : Fin 4 =>
      Icc (g.origin ν + g.cellSide * k ν) (g.origin ν + g.cellSide * k ν + g.cellSide) := by
    ext z
    simp only [ReflectionGrid.cell, Set.mem_ofPred_eq, Set.mem_pi, mem_univ, true_imp_iff, mem_Icc]
    refine forall_congr' fun ν => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hS, interior_pi_set finite_univ] at hx
  have h : x μ ∈ interior
      (Icc (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide)) :=
    hx μ (mem_univ μ)
  rwa [interior_Icc] at h
variable (T : TransferSetup D)
theorem slabSliceIndex_intCast (m : SlabCount) (k j : ℤ) :
    T.slabSliceIndex m (k : ZMod (m : ℕ)) j =
      ((k * (T.ratioNat : ℤ) + j : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) := by
  unfold TransferSetup.slabSliceIndex
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
  obtain ⟨w, hw⟩ : (((m : ℕ) : ℕ) : ℤ) ∣ k - (((k : ZMod (m : ℕ)).cast : ℤ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (ZMod.intCast_zmod_cast _)
  refine ⟨w, ?_⟩
  push_cast
  linear_combination (T.ratioNat : ℤ) * hw
theorem exists_sliceTime_of_mem_interior (k : Fin 4 → ℤ) {x : InfiniteLattice.LatticePoint D.mesh}
    (hx : (x : AmbientSpace) ∈ interior (T.grid.cell k)) :
    ∃ J : ℤ, 1 ≤ J ∧ J ≤ (T.ratioNat : ℤ) ∧
      (x : AmbientSpace) T.axis = T.sliceTime (k T.axis * (T.ratioNat : ℤ) + J) := by
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨i₀, hi₀⟩ := T.grid.origin_mem T.axis
  have ha : 0 < D.mesh := D.mesh_pos
  have hside : T.grid.cellSide = (T.ratioNat : ℝ) * D.mesh := by
    rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
    push_cast
    rfl
  obtain ⟨h1, h2⟩ := lt_coord_lt_of_mem_interior_cell T.grid k hx T.axis
  rw [hn T.axis, hi₀, hside] at h1 h2
  have hb1 : 2 * ((i₀ : ℝ) + (T.ratioNat : ℝ) * k T.axis) + 1 < 2 * n T.axis := by
    refine lt_of_mul_lt_mul_right ?_ ha.le
    nlinarith
  have hb2 : 2 * (n T.axis : ℝ) < 2 * ((i₀ : ℝ) + (T.ratioNat : ℝ) * k T.axis + T.ratioNat) + 1 := by
    refine lt_of_mul_lt_mul_right ?_ ha.le
    nlinarith
  have hb1' : 2 * (i₀ + (T.ratioNat : ℤ) * k T.axis) + 1 < 2 * n T.axis := by exact_mod_cast hb1
  have hb2' : 2 * n T.axis < 2 * (i₀ + (T.ratioNat : ℤ) * k T.axis + (T.ratioNat : ℤ)) + 1 := by
    exact_mod_cast hb2
  refine ⟨n T.axis - i₀ - (T.ratioNat : ℤ) * k T.axis, by omega, by omega, ?_⟩
  rw [hn T.axis, TransferSetup.sliceTime, hi₀]
  push_cast
  ring
def transverseClass (x : InfiniteLattice.LatticePoint D.mesh) : T.TransverseSite :=
  ⟨fun ν => (((x : AmbientSpace) ν.1 : ℝ) : AddCircle (T.transverseSide ν)),
    (AddSubgroup.mem_pi _).mpr fun ν _ => by
      obtain ⟨n, hn⟩ := x.2
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n ν.1, ?_⟩
      rw [hn ν.1, ← zsmul_eq_mul]
      rfl⟩
theorem projPoint_eq_gridSite (m : SlabCount) (c : ℤ) {x : InfiniteLattice.LatticePoint D.mesh}
    (h : (x : AmbientSpace) T.axis = T.sliceTime c) :
    (T.torusPeriods m).projPoint x = T.gridSite m (c : T.SliceLabel m) (transverseClass T x) := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases hν : ν = T.axis
  · subst hν
    change (((x : AmbientSpace) T.axis : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      T.torusPoint m (T.sliceTime ((c : T.SliceLabel m).cast : ℤ)) _ T.axis
    rw [T.torusPoint_axis, h]
    refine T.coe_sliceTime_eq m ?_
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (ZMod.intCast_zmod_cast _)
  · change (((x : AmbientSpace) ν : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) =
      T.torusPoint m (T.sliceTime ((c : T.SliceLabel m).cast : ℤ)) _
        (⟨ν, hν⟩ : TransverseAxis T.axis).1
    rw [T.torusPoint_transverse]
    exact (addCircleCast_coe _ _).symm
theorem transverseClass_add_axisStep (x : InfiniteLattice.LatticePoint D.mesh)
    (ν : TransverseAxis T.axis) :
    transverseClass T (x + InfiniteLattice.axisStep D.mesh ν.1) =
      transverseClass T x + T.transverseStep ν := by
  refine Subtype.ext (funext fun ρ => ?_)
  change ((((x : AmbientSpace) ρ.1 + (Pi.single ν.1 D.mesh : AmbientSpace) ρ.1 : ℝ)) :
      AddCircle (T.transverseSide ρ)) =
    (((x : AmbientSpace) ρ.1 : ℝ) : AddCircle (T.transverseSide ρ)) + T.transverseVector ν D.mesh ρ
  by_cases h : ρ = ν
  · subst h
    rw [TransferSetup.transverseVector, Pi.single_eq_same, Pi.single_eq_same]
    rfl
  · have h' : ρ.1 ≠ ν.1 := fun e => h (Subtype.ext e)
    rw [TransferSetup.transverseVector, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', add_zero,
      add_zero]
theorem transverseClass_add_axisStep_axis (x : InfiniteLattice.LatticePoint D.mesh) :
    transverseClass T (x + InfiniteLattice.axisStep D.mesh T.axis) = transverseClass T x := by
  refine Subtype.ext (funext fun ρ => ?_)
  change ((((x : AmbientSpace) ρ.1 + (Pi.single T.axis D.mesh : AmbientSpace) ρ.1 : ℝ)) :
    AddCircle (T.transverseSide ρ)) = (((x : AmbientSpace) ρ.1 : ℝ) : AddCircle (T.transverseSide ρ))
  rw [Pi.single_eq_of_ne ρ.2, add_zero]
theorem forward_link_factors (k : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint D.mesh) (κ : Fin 4)
    (hx : (x : AmbientSpace) ∈ interior (T.grid.cell k))
    (hx' : ((x + InfiniteLattice.axisStep D.mesh κ : InfiniteLattice.LatticePoint D.mesh) :
      AmbientSpace) ∈ interior (T.grid.cell k)) :
    ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
      ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
        (T.torusPeriods m).liftField U (InfiniteLattice.Link.forwardFrom x κ) =
          c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) := by
  obtain ⟨J, h1, h2, hJ⟩ := exists_sliceTime_of_mem_interior T k hx
  have hlast : (((J - 1).toNat : ℕ) : ℤ) + 1 = J := by omega
  by_cases hκ : κ = T.axis
  · subst hκ
    obtain ⟨J', h1', h2', hJ'⟩ := exists_sliceTime_of_mem_interior T k hx'
    have ha : 0 < D.mesh := D.mesh_pos
    have hstep : ((x + InfiniteLattice.axisStep D.mesh T.axis :
        InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) T.axis =
        (x : AmbientSpace) T.axis + D.mesh := by
      change (x : AmbientSpace) T.axis + (Pi.single T.axis D.mesh : AmbientSpace) T.axis = _
      rw [Pi.single_eq_same]
    have hsucc : T.sliceTime (k T.axis * (T.ratioNat : ℤ) + J + 1) =
        ((x + InfiniteLattice.axisStep D.mesh T.axis : InfiniteLattice.LatticePoint D.mesh) :
          AmbientSpace) T.axis := by
      rw [hstep, hJ, TransferSetup.sliceTime, TransferSetup.sliceTime]
      push_cast
      ring
    have hJJ : J' = J + 1 := by
      rw [hJ'] at hsucc
      have h := mul_right_cancel₀ ha.ne' (by
        have := hsucc
        simp only [TransferSetup.sliceTime] at this
        linarith : (((k T.axis * (T.ratioNat : ℤ) + J + 1 : ℤ) : ℝ)) * D.mesh =
          (((k T.axis * (T.ratioNat : ℤ) + J' : ℤ) : ℝ)) * D.mesh)
      have h' : k T.axis * (T.ratioNat : ℤ) + J + 1 = k T.axis * (T.ratioNat : ℤ) + J' := by
        exact_mod_cast h
      omega
    have hj : (J - 1).toNat < T.ratioNat - 1 := by omega
    refine ⟨fun η => η.2 ⟨(J - 1).toNat, hj⟩ (transverseClass T x),
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd), fun m U => ?_⟩
    have hlink : (T.torusPeriods m).projEdge (InfiniteLattice.Link.forwardFrom x T.axis) =
        T.axialEdge m ((k T.axis * (T.ratioNat : ℤ) + J : ℤ) : T.SliceLabel m)
          (transverseClass T x) := by
      refine BoxTorus.DirectedEdge.ext (projPoint_eq_gridSite T m _ hJ) ?_
      have h := projPoint_eq_gridSite T m (k T.axis * (T.ratioNat : ℤ) + J + 1) hsucc.symm
      rw [transverseClass_add_axisStep_axis, Int.cast_add, Int.cast_one] at h
      exact h
    change BoxTorus.edgeVariable U ((T.torusPeriods m).projEdge _) =
      T.axialField m U (T.slabSliceIndex m _ ((((J - 1).toNat : ℕ) : ℤ) + 1)) _
    rw [hlink, hlast, slabSliceIndex_intCast]
    rfl
  · have hj : (J - 1).toNat < T.ratioNat := by omega
    refine ⟨fun η => η.1 ⟨(J - 1).toNat, hj⟩
        (T.forwardEdge (transverseClass T x) ⟨κ, hκ⟩),
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst), fun m U => ?_⟩
    have hstep : ((x + InfiniteLattice.axisStep D.mesh κ : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) T.axis = (x : AmbientSpace) T.axis := by
      change (x : AmbientSpace) T.axis + (Pi.single κ D.mesh : AmbientSpace) T.axis = _
      rw [Pi.single_eq_of_ne (Ne.symm hκ), add_zero]
    have hlink : (T.torusPeriods m).projEdge (InfiniteLattice.Link.forwardFrom x κ) =
        T.sliceEdge m ((k T.axis * (T.ratioNat : ℤ) + J : ℤ) : T.SliceLabel m)
          (T.forwardEdge (transverseClass T x) ⟨κ, hκ⟩) := by
      refine BoxTorus.DirectedEdge.ext (projPoint_eq_gridSite T m _ hJ) ?_
      have h := projPoint_eq_gridSite T m (k T.axis * (T.ratioNat : ℤ) + J) (hstep.trans hJ)
      rw [transverseClass_add_axisStep T x ⟨κ, hκ⟩] at h
      exact h
    change BoxTorus.edgeVariable U ((T.torusPeriods m).projEdge _) =
      T.sliceField m U (T.slabSliceIndex m _ ((((J - 1).toNat : ℕ) : ℤ) + 1)) _
    rw [hlink, hlast, slabSliceIndex_intCast]
    rfl
theorem link_factors
    (hext : ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
      (T.torusPeriods m).LiftIsGaugeField U)
    (k : Fin 4 → ℤ) (b : D.Link) (ht : (b.initial : AmbientSpace) ∈ interior (T.grid.cell k))
    (hh : (b.terminal : AmbientSpace) ∈ interior (T.grid.cell k)) :
    ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
      ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
        (T.torusPeriods m).liftField U b =
          c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) := by
  rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem b with ⟨x, κ, h⟩ | ⟨x, κ, h⟩
  · subst h
    exact forward_link_factors T k x κ ht hh
  · have h1 : b.terminal = x := congrArg InfiniteLattice.Link.initial h
    have h2 : b.initial = x + InfiniteLattice.axisStep D.mesh κ :=
      congrArg InfiniteLattice.Link.terminal h
    obtain ⟨c, hc, hU⟩ := forward_link_factors T k x κ (h1 ▸ hh) (h2 ▸ ht)
    refine ⟨fun η => (c η)⁻¹, continuous_inv.measurable.comp hc, fun m U => ?_⟩
    have hr := hext m U b
    rw [h, hU m U] at hr
    change _ = (c _)⁻¹
    rw [hr, inv_inv]
theorem cell_observable_factors
    (hext : ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
      (T.torusPeriods m).LiftIsGaugeField U)
    (k : Fin 4 → ℤ) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) (T.grid.cell k)) :
    ∃ Ψ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Ψ ∧
      ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
        F ((T.torusPeriods m).liftGaugeField U) =
          Ψ (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  have hb : ∀ b : ReflectionGrid.interiorLinks (D := D) (T.grid.cell k),
      ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
        ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
          (T.torusPeriods m).liftField U b.1 =
            c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) :=
    fun b => link_factors T hext k b.1 b.2.1 b.2.2
  choose c hcm hc using hb
  refine ⟨fun η => f fun b => c b η, ⟨hf.comp (measurable_pi_lambda _ hcm), C, fun η => hC _⟩,
    fun m U => ?_⟩
  change f (ReflectionGrid.restrictField (T.grid.cell k) ((T.torusPeriods m).liftGaugeField U)) = _
  refine congrArg f (funext fun b => ?_)
  rw [← hc b m U]
  have he : (T.torusPeriods m).liftGaugeField U =
      ⟨(T.torusPeriods m).liftField U, hext m U⟩ := dif_pos (hext m U)
  change ((T.torusPeriods m).liftGaugeField U) b.1 = _
  rw [he]
theorem exists_slab_factorization
    (hB : T.SlabBoltzmannBounds)
    (hext : ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
      (T.torusPeriods m).LiftIsGaugeField U)
    (A : Finset (Fin 4 → ℤ)) (k : ℤ) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ)
    (hA : ∀ k' ∈ A, k' T.axis = k ∧
      F k' ∈ ReflectionGrid.cellObservables (D := D) (T.grid.cell k')) :
    ∃ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ ∧
      ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
        Φ (T.slabRestriction m (k : ZMod (m : ℕ)) U) =
          T.wilsonSlabBoltzmann (T.slabRestriction m (k : ZMod (m : ℕ)) U) *
            ∏ k' ∈ A, F k' ((T.torusPeriods m).liftGaugeField U) := by
  have h : ∀ k' ∈ A, ∃ Ψ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Ψ ∧
      ∀ (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig),
        F k' ((T.torusPeriods m).liftGaugeField U) =
          Ψ (T.slabRestriction m (k : ZMod (m : ℕ)) U) := by
    intro k' hk'
    obtain ⟨h1, h2⟩ := hA k' hk'
    have := cell_observable_factors T hext k' h2
    rwa [h1] at this
  choose! Ψ hΨ using h
  have hbd : ∀ k' ∈ A, ∃ C : ℝ, ∀ η, ‖Ψ k' η‖ ≤ C := fun k' hk' => (hΨ k' hk').1.2
  choose! C hC using hbd
  refine ⟨fun η => T.wilsonSlabBoltzmann η * ∏ k' ∈ A, Ψ k' η, ⟨?_, ∏ k' ∈ A, C k', fun η => ?_⟩,
    fun m U => ?_⟩
  · exact hB.1.measurable.mul (Finset.measurable_prod _ fun k' hk' => (hΨ k' hk').1.1)
  · have hB1 : ‖T.wilsonSlabBoltzmann η‖ ≤ 1 := by
      obtain ⟨him, hpos, hle⟩ := hB.2 η
      have : T.wilsonSlabBoltzmann η = ((T.wilsonSlabBoltzmann η).re : ℂ) :=
        Complex.ext (by simp) (by simpa using him)
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      exact hle
    rw [norm_mul, norm_prod]
    have hp : ∏ k' ∈ A, ‖Ψ k' η‖ ≤ ∏ k' ∈ A, C k' :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k' hk' => hC k' hk' η
    calc _ ≤ 1 * ∏ k' ∈ A, C k' :=
          mul_le_mul hB1 hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · refine congrArg _ (Finset.prod_congr rfl fun k' hk' => ?_)
    exact ((hΨ k' hk').2 m U).symm
end Factorization
section LayerFunctions
theorem mem_slabLayer_iff {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount) (k : ℤ)
    (k' : Fin 4 → ℤ) :
    k' ∈ T.slabLayer m k ↔ (∀ κ, 0 ≤ k' κ ∧ k' κ < T.cellCounts m κ) ∧ k' T.axis = k := by
  simp [TransferSetup.slabLayer, Fintype.mem_piFinset]
theorem cellCounts_axis {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount) :
    T.cellCounts m T.axis = ((m : ℕ) : ℤ) := by
  simp [TransferSetup.cellCounts]
theorem add_single_mem_slabLayer {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
    {k : ℤ} {k' : Fin 4 → ℤ} (hk' : k' ∈ T.slabLayer m k) (hk : k + 1 < ((m : ℕ) : ℤ)) :
    k' + Pi.single T.axis 1 ∈ T.slabLayer m (k + 1) := by
  obtain ⟨h1, h2⟩ := (mem_slabLayer_iff _ _ _ _).mp hk'
  refine (mem_slabLayer_iff _ _ _ _).mpr ⟨fun κ => ?_, by simp [h2]⟩
  by_cases h : κ = T.axis
  · subst h
    have := (h1 T.axis).1
    simp only [Pi.add_apply, Pi.single_eq_same, cellCounts_axis, h2]
    omega
  · simpa [Pi.single_eq_of_ne h] using h1 κ
theorem sub_single_mem_slabLayer {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
    {k : ℤ} {k' : Fin 4 → ℤ} (hk' : k' ∈ T.slabLayer m (k + 1)) (hk : 0 ≤ k) :
    k' - Pi.single T.axis 1 ∈ T.slabLayer m k := by
  obtain ⟨h1, h2⟩ := (mem_slabLayer_iff _ _ _ _).mp hk'
  refine (mem_slabLayer_iff _ _ _ _).mpr ⟨fun κ => ?_, by simp [h2]⟩
  by_cases h : κ = T.axis
  · subst h
    have := (h1 T.axis).2
    rw [cellCounts_axis] at this ⊢
    simp only [Pi.sub_apply, Pi.single_eq_same, h2]
    omega
  · simpa [Pi.single_eq_of_ne h] using h1 κ
theorem prod_eq_prod_slabLayer {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
    (g : (Fin 4 → ℤ) → ℂ) :
    ∏ k' ∈ Fintype.piFinset (fun κ => Finset.Ico 0 (T.cellCounts m κ)), g k' =
      ∏ c : ZMod (m : ℕ), ∏ k' ∈ T.slabLayer m ((c.val : ℕ) : ℤ), g k' := by
  rw [← Finset.prod_fiberwise_of_maps_to (t := Finset.univ)
    (g := fun k' : Fin 4 → ℤ => ((k' T.axis : ℤ) : ZMod (m : ℕ)))
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr ?_ fun _ _ => rfl
  ext k'
  simp only [Finset.mem_filter, TransferSetup.slabLayer]
  refine and_congr_right fun hk => ?_
  have h := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hk T.axis)
  rw [cellCounts_axis] at h
  constructor
  · intro h1
    rw [← h1, ZMod.val_intCast, Int.emod_eq_of_lt h.1 h.2]
  · intro h1
    rw [h1]
    simp
theorem prod_zmod_val_eq_prod_Ico (m : SlabCount) (f : ℤ → ℝ) :
    ∏ c : ZMod (m : ℕ), f ((c.val : ℕ) : ℤ) = ∏ k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ), f k := by
  refine Finset.prod_nbij' (fun c => ((c.val : ℕ) : ℤ)) (fun k => ((k : ℤ) : ZMod (m : ℕ)))
    ?_ ?_ ?_ ?_ ?_
  · intro c _
    have := ZMod.val_lt c
    simp only [Finset.mem_Ico]
    omega
  · intro _ _
    exact Finset.mem_univ _
  · intro c _
    simp
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
    rw [ZMod.val_intCast, Int.emod_eq_of_lt h1 h2]
  · intro _ _
    rfl
theorem reflect_image_cell {D : ChessboardSetup} (g : ReflectionGrid D) (μ : Fin 4)
    (k' : Fin 4 → ℤ) :
    g.reflect μ (k' μ + 1) '' g.cell k' = g.cell (k' + Pi.single μ 1) := by
  have coord : ∀ (x : AmbientSpace) (ν : Fin 4), ν ≠ μ → g.reflect μ (k' μ + 1) x ν = x ν := by
    intro x ν h
    simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h]
  have coord' : ∀ x : AmbientSpace, g.reflect μ (k' μ + 1) x μ =
      2 * (g.origin μ + ((k' μ : ℝ) + 1) * g.cellSide) - x μ := by
    intro x
    simp [ReflectionGrid.reflect, coordVec]
    ring
  have hk : ∀ ν, ν ≠ μ → (k' + Pi.single μ 1 : Fin 4 → ℤ) ν = k' ν := by
    intro ν h
    simp [Pi.single_eq_of_ne h]
  have hk' : (((k' + Pi.single μ 1 : Fin 4 → ℤ) μ : ℤ) : ℝ) = (k' μ : ℝ) + 1 := by
    simp
  have fwd : ∀ x, x ∈ g.cell k' → g.reflect μ (k' μ + 1) x ∈ g.cell (k' + Pi.single μ 1) := by
    intro x hx ν
    have h : x ν - (g.origin ν + g.cellSide * k' ν) ∈ Icc 0 g.cellSide := hx ν
    by_cases hν : ν = μ
    · subst hν
      rw [coord', hk']
      obtain ⟨h1, h2⟩ := h
      constructor <;> nlinarith
    · rw [coord x ν hν, hk ν hν]
      exact h
  have bwd : ∀ x, x ∈ g.cell (k' + Pi.single μ 1) → g.reflect μ (k' μ + 1) x ∈ g.cell k' := by
    intro x hx ν
    have h : x ν - (g.origin ν + g.cellSide * (k' + Pi.single μ 1 : Fin 4 → ℤ) ν) ∈
        Icc 0 g.cellSide := hx ν
    by_cases hν : ν = μ
    · subst hν
      rw [hk'] at h
      rw [coord']
      obtain ⟨h1, h2⟩ := h
      constructor <;> nlinarith
    · rw [coord x ν hν]
      rw [hk ν hν] at h
      exact h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact fwd y hy
  · intro hx
    exact ⟨_, bwd x hx, g.reflect_involutive _ _ x⟩
variable (O : CoupledGrid) (P : O.EvenTransverseSection)
theorem liftIsGaugeField (hR : BoxTorusQuotient.Statement) (m : SlabCount)
    (U : (P.transferSetup.torusPeriods m).GaugeConfig) :
    (P.transferSetup.torusPeriods m).LiftIsGaugeField U :=
  ((hR O).1 (P.transferSetup.cellCounts m) (P.transferSetup.two_le_cellCounts m)).2.2.2.2.2.1.1 U
variable {O} {P}
theorem exists_layerFunction (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (k : ℤ)
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : ∀ k' ∈ P.transferSetup.slabLayer m k,
      F k' ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k')) :
    ∃ Φ, P.transferSetup.IsBoundedMeasurable Φ ∧ P.transferSetup.IsLayerFunction m k F Φ := by
  obtain ⟨Φ, h1, h2⟩ := exists_slab_factorization P.transferSetup
    (hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.2.2
    (liftIsGaugeField O P hR) (P.transferSetup.slabLayer m k) k F
    (fun k' hk' => ⟨((mem_slabLayer_iff _ _ _ _).mp hk').2, hF k' hk'⟩)
  exact ⟨Φ, h1, fun U => h2 m U⟩
theorem isLayerFunction_unique (hA : GridTransferAssertions.Statement)
    (m : SlabCount) (k : ℤ) {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    {Φ Φ' : P.transferSetup.SlabConfig → ℂ} (h : P.transferSetup.IsLayerFunction m k F Φ)
    (h' : P.transferSetup.IsLayerFunction m k F Φ') : Φ = Φ' := by
  funext η
  obtain ⟨U, rfl⟩ :=
    (hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.1.2.2.2.2 (k : ZMod (m : ℕ)) η
  rw [h U, h' U]
theorem layerFunction_spec (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (k : ℤ)
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : ∀ k' ∈ P.transferSetup.slabLayer m k,
      F k' ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k')) :
    P.transferSetup.IsLayerFunction m k F (P.transferSetup.layerFunction m k F) := by
  obtain ⟨Φ, -, h⟩ := exists_layerFunction (P := P) hR hA m k hF
  exact Classical.epsilon_spec (p := P.transferSetup.IsLayerFunction m k F) ⟨Φ, h⟩
theorem layerFunction_eq (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (k : ℤ)
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : ∀ k' ∈ P.transferSetup.slabLayer m k,
      F k' ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k'))
    {Φ : P.transferSetup.SlabConfig → ℂ} (h : P.transferSetup.IsLayerFunction m k F Φ) :
    P.transferSetup.layerFunction m k F = Φ :=
  isLayerFunction_unique hA m k (layerFunction_spec hR hA m k hF) h
theorem layerFunction_isBoundedMeasurable (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (k : ℤ)
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : ∀ k' ∈ P.transferSetup.slabLayer m k,
      F k' ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k')) :
    P.transferSetup.IsBoundedMeasurable (P.transferSetup.layerFunction m k F) := by
  obtain ⟨Φ, h1, h2⟩ := exists_layerFunction (P := P) hR hA m k hF
  rw [layerFunction_eq hR hA m k hF h2]
  exact h1
theorem layerFunction_congr (m : SlabCount) (k : ℤ)
    {F F' : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (h : ∀ k' ∈ P.transferSetup.slabLayer m k, F' k' = F k') :
    P.transferSetup.layerFunction m k F' = P.transferSetup.layerFunction m k F := by
  have e : P.transferSetup.IsLayerFunction m k F' = P.transferSetup.IsLayerFunction m k F := by
    funext Φ
    refine propext (forall_congr' fun U => ?_)
    rw [Finset.prod_congr rfl fun k' hk' => congrFun (h k' hk') _]
  unfold TransferSetup.layerFunction
  rw [e]
theorem mem_cellObservables_of_isCellFamily {m : SlabCount} {hm : Even (m : ℕ)}
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) (k : ℤ) :
    ∀ k' ∈ P.transferSetup.slabLayer m k,
      F k' ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k') :=
  fun k' hk' => hF k' (Finset.mem_filter.mp hk').1
theorem cellFamilyIntegral_eq_slabProductIntegral (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) :
    O.cellFamilyIntegral (P.cellCounts m hm) F =
      P.transferSetup.slabProductIntegral m fun c =>
        P.transferSetup.layerFunction m ((c.val : ℕ) : ℤ) F := by
  unfold CoupledGrid.cellFamilyIntegral TransferSetup.slabProductIntegral
  change ∫ U, (∏ k ∈ Fintype.piFinset (fun κ => Finset.Ico 0 (P.transferSetup.cellCounts m κ)),
      F k ((P.transferSetup.torusPeriods m).liftGaugeField U)) *
      Complex.exp (-(O.β : ℂ) * ((P.transferSetup.torusPeriods m).wilsonAction U : ℂ))
      ∂(P.transferSetup.torusPeriods m).haarMeasure = _
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have hW := ((hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.2.1 U).2.2
  have hΦ : ∀ c : ZMod (m : ℕ),
      P.transferSetup.layerFunction m ((c.val : ℕ) : ℤ) F
          (P.transferSetup.slabRestriction m c U) =
        P.transferSetup.wilsonSlabBoltzmann (P.transferSetup.slabRestriction m c U) *
          ∏ k' ∈ P.transferSetup.slabLayer m ((c.val : ℕ) : ℤ),
            F k' ((P.transferSetup.torusPeriods m).liftGaugeField U) := by
    intro c
    have h := layerFunction_spec (P := P) hR hA m ((c.val : ℕ) : ℤ)
      (mem_cellObservables_of_isCellFamily hF _) U
    simpa using h
  simp only [hΦ]
  rw [prod_eq_prod_slabLayer, hW, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  ring
theorem layerFunctionsOfFamily (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) :
    O.LayerFunctionsOfFamily P m hm F := by
  refine ⟨fun k _ => ⟨?_,
    layerFunction_spec hR hA m k (mem_cellObservables_of_isCellFamily hF k),
    layerFunction_isBoundedMeasurable hR hA m k (mem_cellObservables_of_isCellFamily hF k),
    fun F' _ h => layerFunction_congr m k h⟩,
    cellFamilyIntegral_eq_slabProductIntegral hR hA m hm hF⟩
  exact ⟨_, layerFunction_spec hR hA m k (mem_cellObservables_of_isCellFamily hF k),
    fun Φ h => isLayerFunction_unique hA m k h
      (layerFunction_spec hR hA m k (mem_cellObservables_of_isCellFamily hF k))⟩
theorem nextLayerReflects (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) :
    O.NextLayerReflects P m F := by
  intro k hk0 hk2 hcopy
  have hread := (hR O).1 (P.transferSetup.cellCounts m) (P.transferSetup.two_le_cellCounts m)
  have hθ : (P.transferSetup.torusPeriods m).InducesMap
      (P.transferSetup.planeReflection (k + 1))
      ((P.transferSetup.torusPeriods m).quotientMap (P.transferSetup.planeReflection (k + 1))) :=
    Classical.epsilon_spec
      (p := (P.transferSetup.torusPeriods m).InducesMap (P.transferSetup.planeReflection (k + 1)))
      (hread.2.2.2.2.2.2.1 (O.grid.reflectElem P.axis (k + 1))).1.exists
  obtain ⟨hs1, -, hs3⟩ := hS O.toChessboardSetup P.transferSetup O.isCoarse m hm k _ hθ
  refine layerFunction_eq hR hA m (k + 1) (mem_cellObservables_of_isCellFamily hF _) fun U => ?_
  have hk := layerFunction_spec (P := P) hR hA m k (mem_cellObservables_of_isCellFamily hF k)
    ((P.transferSetup.torusPeriods m).pullback
      ((P.transferSetup.torusPeriods m).quotientMap (P.transferSetup.planeReflection (k + 1))) U)
  have hB : starRingEnd ℂ (P.transferSetup.wilsonSlabBoltzmann
      (P.transferSetup.slabReverse
        (P.transferSetup.slabRestriction m ((k + 1 : ℤ) : ZMod (m : ℕ)) U))) =
      P.transferSetup.wilsonSlabBoltzmann
        (P.transferSetup.slabRestriction m ((k + 1 : ℤ) : ZMod (m : ℕ)) U) :=
    congrFun hs3 _
  rw [hs1 U] at hk
  change starRingEnd ℂ (P.transferSetup.layerFunction m k F
    (P.transferSetup.slabReverse
      (P.transferSetup.slabRestriction m ((k + 1 : ℤ) : ZMod (m : ℕ)) U))) = _
  rw [hk, map_mul, hB, map_prod]
  refine congrArg _ ?_
  have hcopy' : ∀ k' ∈ P.transferSetup.slabLayer m k,
      F (k' + Pi.single P.transferSetup.axis 1) =
        O.grid.transportTo (O.grid.cell k')
          (O.grid.cell (k' + Pi.single P.transferSetup.axis 1)) (F k') :=
    hcopy
  refine Finset.prod_nbij' (fun k' => k' + Pi.single P.transferSetup.axis 1)
    (fun k' => k' - Pi.single P.transferSetup.axis 1) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    exact add_single_mem_slabLayer _ _ hk' (by omega)
  · intro k' hk'
    exact sub_single_mem_slabLayer _ _ hk' hk0
  · intro k' _
    simp
  · intro k' _
    simp
  · intro k' hk'
    obtain ⟨-, h2⟩ := (mem_slabLayer_iff _ _ _ _).mp hk'
    have himg : O.grid.reflect P.transferSetup.axis (k + 1) '' O.grid.cell k' =
        O.grid.cell (k' + Pi.single P.transferSetup.axis 1) := by
      have h := reflect_image_cell O.grid P.transferSetup.axis k'
      rwa [h2] at h
    have hc := ((hread.2.2.2.2.2.2.2.2 (O.grid.cell k') ⟨k', rfl⟩ (F k')
      (mem_cellObservables_of_isCellFamily hF k k' hk') P.transferSetup.axis (k + 1)).2 U)
    rw [himg] at hc
    rw [hcopy' k' hk']
    exact hc.symm
end LayerFunctions
section Reflections
variable {O : CoupledGrid} {P : O.EvenTransverseSection}
theorem firstLayerFunctionIndependent (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) :
    O.FirstLayerFunctionIndependent P m F := by
  intro m' hm' F' hF' hag
  have hl : P.transferSetup.slabLayer m' 0 = P.transferSetup.slabLayer m 0 := by
    ext k'
    rw [mem_slabLayer_iff, mem_slabLayer_iff]
    refine and_congr_left fun h0 => forall_congr' fun κ => ?_
    by_cases h : κ = P.transferSetup.axis
    · subst h
      rw [cellCounts_axis, cellCounts_axis, h0]
      omega
    · simp [TransferSetup.cellCounts, h]
  obtain ⟨Φ, -, hΦ⟩ := exists_slab_factorization P.transferSetup
    (hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.2.2
    (liftIsGaugeField O P hR) (P.transferSetup.slabLayer m 0) 0 F
    (fun k' hk' => ⟨((mem_slabLayer_iff _ _ _ _).mp hk').2,
      mem_cellObservables_of_isCellFamily hF 0 k' hk'⟩)
  have e1 : P.transferSetup.layerFunction m 0 F = Φ :=
    layerFunction_eq hR hA m 0 (mem_cellObservables_of_isCellFamily hF 0) fun U => hΦ m U
  have e2 : P.transferSetup.layerFunction m' 0 F' = Φ := by
    refine layerFunction_eq hR hA m' 0 (mem_cellObservables_of_isCellFamily hF' 0)
      fun U => (hΦ m' U).trans ?_
    rw [hl]
    exact congrArg _ (Finset.prod_congr rfl fun k' hk' => (congrFun (hag k' hk') _).symm)
  rw [e1, e2]
theorem transportTo_mem (hL : GridBasicProperties.Statement) {S S' : Set AmbientSpace}
    (hS : S ∈ O.grid.cellSet) (hS' : S' ∈ O.grid.cellSet)
    {G : O.toChessboardSetup.GaugeField → ℂ}
    (hG : G ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.grid.transportTo S S' G ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S' := by
  obtain ⟨r, hr, -⟩ :=
    (hL O.toChessboardSetup O.grid).2.2.2.1.2.2.2.2.2.2.1 S hS S' hS'
  exact ((hL O.toChessboardSetup O.grid).2.2.2.2.1 S hS S' hS' S' hS' r hr G hG G hG 0).1
theorem transportTo_self (hL : GridBasicProperties.Statement) {S : Set AmbientSpace}
    (hS : S ∈ O.grid.cellSet) {G : O.toChessboardSetup.GaugeField → ℂ}
    (hG : G ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.grid.transportTo S S G = G := by
  obtain ⟨r, hr, -⟩ := (hL O.toChessboardSetup O.grid).2.2.2.1.2.2.2.2.2.2.1 S hS S hS
  exact ((hL O.toChessboardSetup O.grid).2.2.2.2.1 S hS S hS S hS r hr G hG G hG 0).2.1
theorem transportTo_transportTo (hL : GridBasicProperties.Statement)
    {S S' S'' : Set AmbientSpace}
    (hS : S ∈ O.grid.cellSet) (hS' : S' ∈ O.grid.cellSet) (hS'' : S'' ∈ O.grid.cellSet)
    {G : O.toChessboardSetup.GaugeField → ℂ}
    (hG : G ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.grid.transportTo S' S'' (O.grid.transportTo S S' G) = O.grid.transportTo S S'' G := by
  obtain ⟨r, hr, -⟩ := (hL O.toChessboardSetup O.grid).2.2.2.1.2.2.2.2.2.2.1 S hS S' hS'
  exact ((hL O.toChessboardSetup O.grid).2.2.2.2.1 S hS S' hS' S'' hS'' r hr G hG G hG 0).2.2.1
theorem isCellFamily_reflectFamily (hL : GridBasicProperties.Statement) {n : EvenIndexVector}
    {μ : Fin 4} {k : ℤ} {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily n F) (hk : k ∈ Finset.Ico 0 (n.coord μ)) :
    O.IsCellFamily n (O.grid.reflectFamily μ k F) :=
  fun _ hk' => transportTo_mem hL ⟨_, rfl⟩ ⟨_, rfl⟩ (hF _ (n.update_mem_indexBox hk' μ hk))
theorem reflectConj_reflectConj {D : ChessboardSetup} {T : TransferSetup D}
    (h : Function.Involutive T.slabReverse) (Φ : T.SlabConfig → ℂ) :
    T.reflectConj (T.reflectConj Φ) = Φ := by
  funext η
  simp [TransferSetup.reflectConj, h η]
theorem layerFunction_reflectFamily (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (hL : GridBasicProperties.Statement) (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) {k : ℤ}
    (hk : k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ)) {j : ℤ}
    (hj : j ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ)) :
    P.transferSetup.layerFunction m j (O.grid.reflectFamily P.axis k F) =
      if Even (j - k) then P.transferSetup.layerFunction m k F
      else P.transferSetup.reflectConj (P.transferSetup.layerFunction m k F) := by
  have hq : (P.cellCounts m hm).coord P.axis = ((m : ℕ) : ℤ) :=
    cellCounts_axis P.transferSetup m
  have hk' : k ∈ Finset.Ico 0 ((P.cellCounts m hm).coord P.axis) := by rwa [hq]
  have hG := isCellFamily_reflectFamily hL hF hk'
  have hinv : Function.Involutive P.transferSetup.slabReverse :=
    (hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.1.2.1
  have hrr := reflectConj_reflectConj hinv
  set Φ := P.transferSetup.layerFunction m k F with hΦ
  set Ψ : ℤ → P.transferSetup.SlabConfig → ℂ := fun j =>
    P.transferSetup.layerFunction m j (O.grid.reflectFamily P.axis k F) with hΨ
  set A : ℤ → P.transferSetup.SlabConfig → ℂ := fun j =>
    if Even (j - k) then Φ else P.transferSetup.reflectConj Φ with hAdef
  have hAs : ∀ j, A (j + 1) = P.transferSetup.reflectConj (A j) := by
    intro j
    simp only [hAdef]
    by_cases h : Even (j - k)
    · have h' : ¬ Even (j + 1 - k) := by
        rw [show j + 1 - k = (j - k) + 1 by ring, Int.even_add_one]
        simpa using h
      rw [if_pos h, if_neg h']
    · have h' : Even (j + 1 - k) := by
        rw [show j + 1 - k = (j - k) + 1 by ring, Int.even_add_one]
        exact h
      rw [if_neg h, if_pos h', hrr]
  have h0 : Ψ k = Φ := by
    refine layerFunction_congr m k fun k' hk'' => ?_
    obtain ⟨h1, h2⟩ := (mem_slabLayer_iff _ _ _ _).mp hk''
    have hu : Function.update k' P.axis k = k' := by
      rw [← show k' P.axis = k from h2]
      exact Function.update_eq_self _ _
    change O.grid.transportTo (O.grid.cell (Function.update k' P.axis k)) (O.grid.cell k')
      (F (Function.update k' P.axis k)) = F k'
    rw [hu]
    exact transportTo_self hL ⟨_, rfl⟩ (mem_cellObservables_of_isCellFamily hF k k' hk'')
  have hrev : ∀ i : ℤ, 0 ≤ i → i ≤ ((m : ℕ) : ℤ) - 2 →
      Ψ (i + 1) = P.transferSetup.reflectConj (Ψ i) := by
    intro i hi0 hi2
    refine nextLayerReflects hR hA hS m hm hG i hi0 hi2 fun k' hk'' => ?_
    have hki : k' ∈ (P.cellCounts m hm).indexBox := (Finset.mem_filter.mp hk'').1
    have hu : Function.update (k' + Pi.single P.axis 1) P.axis k =
        Function.update k' P.axis k := by
      funext ν
      by_cases h : ν = P.axis
      · subst h
        simp
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    have hmem := (P.cellCounts m hm).update_mem_indexBox hki P.axis hk'
    change O.grid.transportTo (O.grid.cell (Function.update (k' + Pi.single P.axis 1) P.axis k))
        (O.grid.cell (k' + Pi.single P.axis 1))
        (F (Function.update (k' + Pi.single P.axis 1) P.axis k)) =
      O.grid.transportTo (O.grid.cell k') (O.grid.cell (k' + Pi.single P.axis 1))
        (O.grid.transportTo (O.grid.cell (Function.update k' P.axis k)) (O.grid.cell k')
          (F (Function.update k' P.axis k)))
    rw [hu]
    exact (transportTo_transportTo hL ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ (hF _ hmem)).symm
  obtain ⟨hk0, hk1⟩ := Finset.mem_Ico.mp hk
  obtain ⟨hj0, hj1⟩ := Finset.mem_Ico.mp hj
  have hbase : Ψ k = A k := by
    simp only [hAdef, sub_self, Even.zero, if_true]
    exact h0
  have hup : ∀ i : ℤ, k ≤ i → i < ((m : ℕ) : ℤ) → Ψ i = A i := by
    intro i hi
    induction i, hi using Int.le_induction with
    | base => exact fun _ => hbase
    | succ i hi ih =>
      intro hlt
      rw [hrev i (by omega) (by omega), ih (by omega), hAs]
  have hdown : ∀ i : ℤ, i ≤ k → 0 ≤ i → Ψ i = A i := by
    intro i hi
    induction i, hi using Int.le_induction_down with
    | base => exact fun _ => hbase
    | pred i hi ih =>
      intro h0i
      have h1 := hrev (i - 1) h0i (by omega)
      rw [sub_add_cancel] at h1
      have h2 := ih (by omega)
      have h3 := hAs (i - 1)
      rw [sub_add_cancel] at h3
      rw [h1, h3] at h2
      have h4 := congrArg P.transferSetup.reflectConj h2
      rwa [hrr, hrr] at h4
  change Ψ j = A j
  rcases le_total k j with h | h
  · exact hup j h hj1
  · exact hdown j h hj0
theorem reflectionBoundForFamily (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (hT : TraceFormulaConsequences.Statement)
    (hL : GridBasicProperties.Statement) (m : SlabCount) (hm : Even (m : ℕ))
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (hF : O.IsCellFamily (P.cellCounts m hm) F) :
    O.ReflectionBoundForFamily P m hm F := by
  have hq : (P.cellCounts m hm).coord P.axis = ((m : ℕ) : ℤ) :=
    cellCounts_axis P.transferSetup m
  have hinv : Function.Involutive P.transferSetup.slabReverse :=
    (hA O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.1.2.1
  have hrr := reflectConj_reflectConj hinv
  have hbb : ∀ k : ℤ, P.transferSetup.IsBoundedMeasurable (P.transferSetup.layerFunction m k F) :=
    fun k => layerFunction_isBoundedMeasurable hR hA m k (mem_cellObservables_of_isCellFamily hF k)
  have heq : ∀ k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ),
      O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F) =
        P.transferSetup.alternatingSlabIntegral m hm (P.transferSetup.layerFunction m k F) := by
    intro k hk
    have hk' : k ∈ Finset.Ico 0 ((P.cellCounts m hm).coord P.axis) := by rwa [hq]
    have hG := isCellFamily_reflectFamily hL hF hk'
    rw [cellFamilyIntegral_eq_slabProductIntegral hR hA m hm hG]
    have hc : ∀ c : ZMod (m : ℕ), ((c.val : ℕ) : ℤ) ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ) := by
      intro c
      have := ZMod.val_lt c
      simp only [Finset.mem_Ico]
      omega
    have hfun : (fun c : ZMod (m : ℕ) => P.transferSetup.layerFunction m ((c.val : ℕ) : ℤ)
        (O.grid.reflectFamily P.axis k F)) = fun c =>
        if Even (((c.val : ℕ) : ℤ) - k) then P.transferSetup.layerFunction m k F
        else P.transferSetup.reflectConj (P.transferSetup.layerFunction m k F) :=
      funext fun c => layerFunction_reflectFamily hR hA hS hL m hm hF hk (hc c)
    rw [hfun]
    by_cases hke : Even k
    · unfold TransferSetup.alternatingSlabIntegral
      refine congrArg _ (funext fun c => ?_)
      have : Even (((c.val : ℕ) : ℤ) - k) ↔ Even c.val := by
        rw [Int.even_sub, Int.even_coe_nat]
        simp [hke]
      simp only [this]
    · have h3 := ((hT O.toChessboardSetup P.transferSetup m hm).1 _ (hbb k)).2.2.2
      rw [← h3]
      unfold TransferSetup.alternatingSlabIntegral
      refine congrArg _ (funext fun c => ?_)
      have : Even (((c.val : ℕ) : ℤ) - k) ↔ ¬ Even c.val := by
        rw [Int.even_sub, Int.even_coe_nat]
        simp [hke]
      by_cases hc' : Even c.val
      · rw [if_pos hc', if_neg (by rwa [this, not_not])]
      · rw [if_neg hc', if_pos (this.mpr hc'), hrr]
  refine ⟨fun k hk => ?_, ?_⟩
  · have h0 := ((hT O.toChessboardSetup P.transferSetup m hm).1 _ (hbb k)).2.2.1
    obtain ⟨h1, h2⟩ := Complex.le_def.mp h0
    rw [heq k hk]
    exact ⟨rfl, h2.symm, h1⟩
  · obtain ⟨h1, h2⟩ := (hT O.toChessboardSetup P.transferSetup m hm).2.1
      (fun c => P.transferSetup.layerFunction m ((c.val : ℕ) : ℤ) F) fun c => hbb _
    rw [cellFamilyIntegral_eq_slabProductIntegral hR hA m hm hF]
    refine h1.trans (h2.le.trans (le_of_eq ?_))
    rw [← prod_zmod_val_eq_prod_Ico m fun k =>
      (O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F)).re ^
        (1 / ((m : ℕ) : ℝ))]
    refine Finset.prod_congr rfl fun c _ => ?_
    have hc : ((c.val : ℕ) : ℤ) ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ) := by
      have := ZMod.val_lt c
      simp only [Finset.mem_Ico]
      omega
    rw [heq _ hc]
end Reflections
section FourAxes
variable {O : CoupledGrid}
theorem cellFamilyIntegral_congr (n : EvenIndexVector)
    {F F' : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ}
    (h : ∀ k ∈ n.indexBox, F k = F' k) :
    O.cellFamilyIntegral n F = O.cellFamilyIntegral n F' := by
  unfold CoupledGrid.cellFamilyIntegral
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  refine congrArg (· * _) (Finset.prod_congr rfl fun k hk => ?_)
  rw [h k hk]
theorem axis_reflection_bound (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (hT : TraceFormulaConsequences.Statement)
    (hL : GridBasicProperties.Statement) (n : EvenIndexVector) (μ : Fin 4)
    {G : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ} (hG : O.IsCellFamily n G) :
    (∀ k ∈ Finset.Ico (0 : ℤ) (n.coord μ),
      (O.cellFamilyIntegral n (O.grid.reflectFamily μ k G)).im = 0 ∧
      0 ≤ (O.cellFamilyIntegral n (O.grid.reflectFamily μ k G)).re) ∧
    ‖O.cellFamilyIntegral n G‖ ≤ ∏ k ∈ Finset.Ico (0 : ℤ) (n.coord μ),
      (O.cellFamilyIntegral n (O.grid.reflectFamily μ k G)).re ^ (1 / ((n.coord μ : ℤ) : ℝ)) := by
  obtain ⟨P, m, hm, hd, he, rfl⟩ := O.exists_cellCounts_eq n μ
  subst hd
  have h := reflectionBoundForFamily (P := P) hR hA hS hT hL m hm hG
  rw [← he]
  refine ⟨fun k hk => (h.1 k hk).2, ?_⟩
  have h2 := h.2
  rwa [Int.cast_natCast]
theorem norm_eq_re_of_im_eq_zero {z : ℂ} (h1 : z.im = 0) (h2 : 0 ≤ z.re) : ‖z‖ = z.re := by
  have h : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h1)
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using h2)]
  simp
theorem chessboardPartitionsNonneg (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (hT : TraceFormulaConsequences.Statement)
    (hL : GridBasicProperties.Statement) (n : EvenIndexVector) :
    O.ChessboardPartitionsNonneg n := by
  intro S hS' F hF
  have hfam : O.IsCellFamily n fun k => O.grid.transportTo S (O.grid.cell k) F :=
    fun k _ => transportTo_mem hL hS' ⟨k, rfl⟩ hF
  have h0 : (0 : ℤ) ∈ Finset.Ico (0 : ℤ) (n.coord 0) := by
    have := n.two_le 0
    simp only [Finset.mem_Ico]
    omega
  have hfix : O.cellFamilyIntegral n
      (O.grid.reflectFamily 0 0 fun k => O.grid.transportTo S (O.grid.cell k) F) =
      O.chessboardPartitionOn n S F := by
    rw [O.chessboardPartitionOn_eq_cellFamilyIntegral]
    refine cellFamilyIntegral_congr n fun k _ => ?_
    exact transportTo_transportTo hL hS' ⟨_, rfl⟩ ⟨_, rfl⟩ hF
  have h := (axis_reflection_bound hR hA hS hT hL n 0 hfam).1 0 h0
  rwa [hfix] at h
theorem rpow_le_prod_rpow_mul {x q r : ℝ} {C : Finset ℤ} {z : ℤ → ℝ} (hz : ∀ c, 0 ≤ z c)
    (hx : 0 ≤ x) (h : x ≤ ∏ c ∈ C, z c ^ q) (hr : 0 ≤ r) : x ^ r ≤ ∏ c ∈ C, z c ^ (q * r) := by
  calc x ^ r ≤ (∏ c ∈ C, z c ^ q) ^ r := Real.rpow_le_rpow hx h hr
    _ = ∏ c ∈ C, z c ^ (q * r) := by
      rw [← Real.finsetProd_rpow _ _ fun c _ => Real.rpow_nonneg (hz c) q]
      exact Finset.prod_congr rfl fun c _ => (Real.rpow_mul (hz c) q r).symm
theorem prod_indexBox (n : EvenIndexVector) (g : (Fin 4 → ℤ) → ℝ) :
    ∏ k ∈ n.indexBox, g k =
      ∏ a ∈ Finset.Ico (0 : ℤ) (n.coord 0), ∏ b ∈ Finset.Ico (0 : ℤ) (n.coord 1),
        ∏ c ∈ Finset.Ico (0 : ℤ) (n.coord 2), ∏ d ∈ Finset.Ico (0 : ℤ) (n.coord 3),
          g ![a, b, c, d] := by
  have h : (∏ a ∈ Finset.Ico (0 : ℤ) (n.coord 0), ∏ b ∈ Finset.Ico (0 : ℤ) (n.coord 1),
        ∏ c ∈ Finset.Ico (0 : ℤ) (n.coord 2), ∏ d ∈ Finset.Ico (0 : ℤ) (n.coord 3),
          g ![a, b, c, d]) =
      ∏ t ∈ Finset.Ico (0 : ℤ) (n.coord 0) ×ˢ (Finset.Ico (0 : ℤ) (n.coord 1) ×ˢ
        (Finset.Ico (0 : ℤ) (n.coord 2) ×ˢ Finset.Ico (0 : ℤ) (n.coord 3))),
        g ![t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simp only [Finset.prod_product]
  rw [h]
  refine Finset.prod_nbij' (fun k => (k 0, k 1, k 2, k 3))
    (fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Fintype.mem_piFinset.mp hk
    simp only [Finset.mem_product]
    exact ⟨hk' 0, hk' 1, hk' 2, hk' 3⟩
  · intro t ht
    simp only [Finset.mem_product] at ht
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2
  · intro k _
    funext i
    fin_cases i <;> rfl
  · intro t _
    rfl
  · intro k _
    refine congrArg g (funext fun i => ?_)
    fin_cases i <;> rfl
theorem chessboardBoundForFamily (hR : BoxTorusQuotient.Statement)
    (hA : GridTransferAssertions.Statement) (hS : SlabReflections.Statement)
    (hT : TraceFormulaConsequences.Statement)
    (hL : GridBasicProperties.Statement) (n : EvenIndexVector)
    {F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ} (hF : O.IsCellFamily n F) :
    O.ChessboardBoundForFamily n F := by
  have hpos : ∀ i, (0 : ℝ) < ((n.coord i : ℤ) : ℝ) := fun i => by
    have := n.two_le i
    exact_mod_cast (by omega : 0 < n.coord i)
  have hq : ∀ i, (0 : ℝ) ≤ 1 / ((n.coord i : ℤ) : ℝ) := fun i => (one_div_pos.mpr (hpos i)).le
  have st : ∀ (G : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ),
      O.IsCellFamily n G → ∀ i : Fin 4, ‖O.cellFamilyIntegral n G‖ ≤
        ∏ k ∈ Finset.Ico (0 : ℤ) (n.coord i),
          ‖O.cellFamilyIntegral n (O.grid.reflectFamily i k G)‖ ^ (1 / ((n.coord i : ℤ) : ℝ)) := by
    intro G hG i
    obtain ⟨h1, h2⟩ := axis_reflection_bound hR hA hS hT hL n i hG
    refine h2.trans (le_of_eq (Finset.prod_congr rfl fun k hk => ?_))
    rw [norm_eq_re_of_im_eq_zero (h1 k hk).1 (h1 k hk).2]
  unfold CoupledGrid.ChessboardBoundForFamily
  rw [prod_indexBox]
  refine (st F hF 0).trans ?_
  have f1 : ∀ a ∈ Finset.Ico (0 : ℤ) (n.coord 0),
      O.IsCellFamily n (O.grid.reflectFamily 0 a F) :=
    fun a ha => isCellFamily_reflectFamily hL hF ha
  have f2 : ∀ a ∈ Finset.Ico (0 : ℤ) (n.coord 0), ∀ b ∈ Finset.Ico (0 : ℤ) (n.coord 1),
      O.IsCellFamily n (O.grid.reflectFamily 1 b (O.grid.reflectFamily 0 a F)) :=
    fun a ha b hb => isCellFamily_reflectFamily hL (f1 a ha) hb
  have f3 : ∀ a ∈ Finset.Ico (0 : ℤ) (n.coord 0), ∀ b ∈ Finset.Ico (0 : ℤ) (n.coord 1),
      ∀ c ∈ Finset.Ico (0 : ℤ) (n.coord 2), O.IsCellFamily n
        (O.grid.reflectFamily 2 c (O.grid.reflectFamily 1 b (O.grid.reflectFamily 0 a F))) :=
    fun a ha b hb c hc => isCellFamily_reflectFamily hL (f2 a ha b hb) hc
  have hnn : ∀ (G : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) (r : ℝ),
      0 ≤ ‖O.cellFamilyIntegral n G‖ ^ r := fun G r => Real.rpow_nonneg (norm_nonneg _) r
  refine (Finset.prod_le_prod (fun a _ => hnn _ _) fun a ha =>
    rpow_le_prod_rpow_mul (z := fun b => ‖O.cellFamilyIntegral n (O.grid.reflectFamily 1 b
      (O.grid.reflectFamily 0 a F))‖) (fun _ => norm_nonneg _) (norm_nonneg _)
      (st _ (f1 a ha) 1) (hq 0)).trans ?_
  refine (Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun b _ => hnn _ _) fun a ha =>
    Finset.prod_le_prod (fun b _ => hnn _ _) fun b hb =>
    rpow_le_prod_rpow_mul (z := fun c => ‖O.cellFamilyIntegral n (O.grid.reflectFamily 2 c
      (O.grid.reflectFamily 1 b (O.grid.reflectFamily 0 a F)))‖) (fun _ => norm_nonneg _)
      (norm_nonneg _) (st _ (f2 a ha b hb) 2) (mul_nonneg (hq 1) (hq 0))).trans ?_
  refine (Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun b _ =>
      Finset.prod_nonneg fun c _ => hnn _ _) fun a ha =>
    Finset.prod_le_prod (fun b _ => Finset.prod_nonneg fun c _ => hnn _ _) fun b hb =>
    Finset.prod_le_prod (fun c _ => hnn _ _) fun c hc =>
    rpow_le_prod_rpow_mul (z := fun d => ‖O.cellFamilyIntegral n (O.grid.reflectFamily 3 d
      (O.grid.reflectFamily 2 c (O.grid.reflectFamily 1 b (O.grid.reflectFamily 0 a F))))‖)
      (fun _ => norm_nonneg _) (norm_nonneg _) (st _ (f3 a ha b hb c hc) 3)
      (mul_nonneg (hq 2) (mul_nonneg (hq 1) (hq 0)))).trans (le_of_eq ?_)
  refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb =>
    Finset.prod_congr rfl fun c hc => Finset.prod_congr rfl fun d hd => ?_
  have hmem : ![a, b, c, d] ∈ n.indexBox := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hFk := hF _ hmem
  have hcopies : O.cellFamilyIntegral n (O.grid.reflectFamily 3 d (O.grid.reflectFamily 2 c
      (O.grid.reflectFamily 1 b (O.grid.reflectFamily 0 a F)))) =
      O.chessboardPartitionOn n (O.grid.cell ![a, b, c, d]) (F ![a, b, c, d]) := by
    rw [O.chessboardPartitionOn_eq_cellFamilyIntegral]
    refine cellFamilyIntegral_congr n fun k' _ => ?_
    have hu : Function.update (Function.update (Function.update (Function.update k' 3 d) 2 c) 1 b)
        0 a = ![a, b, c, d] := by
      funext i
      fin_cases i <;> simp [Function.update]
    change O.grid.transportTo _ (O.grid.cell k') (O.grid.transportTo _ _ (O.grid.transportTo _ _
      (O.grid.transportTo (O.grid.cell (Function.update (Function.update (Function.update
        (Function.update k' 3 d) 2 c) 1 b) 0 a)) _ (F (Function.update (Function.update
        (Function.update (Function.update k' 3 d) 2 c) 1 b) 0 a))))) = _
    rw [hu, transportTo_transportTo hL ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ hFk,
      transportTo_transportTo hL ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ hFk,
      transportTo_transportTo hL ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ hFk]
  have hnonneg := chessboardPartitionsNonneg hR hA hS hT hL n (O.grid.cell ![a, b, c, d])
    ⟨_, rfl⟩ _ hFk
  rw [hcopies, norm_eq_re_of_im_eq_zero hnonneg.1 hnonneg.2]
  refine congrArg _ ?_
  have e0 := (hpos 0).ne'
  have e1 := (hpos 1).ne'
  have e2 := (hpos 2).ne'
  have e3 := (hpos 3).ne'
  rw [Fin.prod_univ_four]
  push_cast
  field_simp
end FourAxes
end TransferSetupCellFamilies
theorem CellFamiliesInTransferSetup.proof
    (hA : GridTransferAssertions.Statement)
    (hR : BoxTorusQuotient.Statement) (hS : SlabReflections.Statement)
    (hT : TraceFormulaConsequences.Statement)
    (hL : GridBasicProperties.Statement) :
    CellFamiliesInTransferSetup.Statement := by
  open TransferSetupCellFamilies in
  exact fun O => ⟨fun P m hm F hF => ⟨layerFunctionsOfFamily hR hA m hm hF,
      nextLayerReflects hR hA hS m hm hF, firstLayerFunctionIndependent hR hA m hm hF,
      reflectionBoundForFamily hR hA hS hT hL m hm hF⟩,
    fun n => ⟨chessboardPartitionsNonneg hR hA hS hT hL n,
      fun F hF => chessboardBoundForFamily hR hA hS hT hL n hF⟩⟩
end YangMills.Construction.ChessboardTori
end
