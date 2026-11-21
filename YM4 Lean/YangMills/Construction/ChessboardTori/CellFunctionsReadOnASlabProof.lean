import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPictureProof
import YangMills.Construction.ChessboardTori.CellFunctionsReadOnASlab
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace SlabRestrictionOfCellFunctions
variable {D : ChessboardSetup}
theorem coord_bounds_of_mem_interior_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) {p : AmbientSpace}
    (hp : p ∈ interior (g.cell k)) (μ : Fin 4) :
    g.origin μ + g.cellSide * k μ < p μ ∧ p μ < g.origin μ + g.cellSide * k μ + g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetupCellFamilies.lt_coord_lt_of_mem_interior_cell <;> assumption
variable (T : TransferSetup D) (m : SlabCount)
theorem slabSliceIndex_intCast (k j : ℤ) :
    T.slabSliceIndex m (k : ZMod (m : ℕ)) j =
      ((k * (T.ratioNat : ℤ) + j : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetupCellFamilies.slabSliceIndex_intCast <;> assumption
theorem exists_sliceLabel_of_mem_interior (k : Fin 4 → ℤ) {p : InfiniteLattice.LatticePoint D.mesh}
    (hp : (p : AmbientSpace) ∈ interior (T.grid.cell k)) {i : T.SliceLabel m}
    {y : T.TransverseSite}
    (hproj : (T.torusPeriods m).projPoint p = T.gridSite m i y) :
    ∃ J : ℤ, 1 ≤ J ∧ J ≤ (T.ratioNat : ℤ) ∧
      ((k T.axis * (T.ratioNat : ℤ) + J : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) = i := by
  obtain ⟨n, hn⟩ := p.2
  obtain ⟨i₀, hi₀⟩ := T.grid.origin_mem T.axis
  have hmesh : 0 < D.mesh := D.mesh_pos
  have hcell : T.grid.cellSide = (T.ratioNat : ℝ) * D.mesh := by
    rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
    push_cast
    rfl
  obtain ⟨hlo, hhi⟩ := coord_bounds_of_mem_interior_cell T.grid k hp T.axis
  have hcirc : (((p : AmbientSpace) T.axis : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((T.sliceTime (i.cast : ℤ) : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
    have hc' := congrArg
      (fun s : (T.torusPeriods m).GridPoint => (s : (T.torusPeriods m).TorusSpace) T.axis) hproj
    exact hc'.trans (T.torusPoint_axis m _ _)
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp hcirc)
  rw [T.sideLengths_axis, zsmul_eq_mul, TransferSetup.sliceTime, hi₀, hn T.axis] at hz
  rw [hn T.axis, hi₀, hcell] at hlo hhi
  set c : ℤ := (i.cast : ℤ) with hcdef
  set N : ℤ := (((m : ℕ) * T.ratioNat : ℕ) : ℤ) with hN
  have hNr : (((m : ℕ) * T.ratioNat : ℕ) : ℝ) = (N : ℝ) := by
    rw [hN]
    push_cast
    rfl
  rw [hNr] at hz
  have hreal : (n T.axis : ℝ) = (i₀ : ℝ) + c + z * N := by
    refine mul_right_cancel₀ hmesh.ne' ?_
    linear_combination -hz
  have hint : n T.axis = i₀ + c + z * N := by exact_mod_cast hreal
  have hb₁ : 2 * ((i₀ : ℝ) + (T.ratioNat : ℝ) * k T.axis) + 1 < 2 * n T.axis := by
    refine lt_of_mul_lt_mul_right ?_ hmesh.le
    nlinarith
  have hb₂ : 2 * (n T.axis : ℝ) <
      2 * ((i₀ : ℝ) + (T.ratioNat : ℝ) * k T.axis + T.ratioNat) + 1 := by
    refine lt_of_mul_lt_mul_right ?_ hmesh.le
    nlinarith
  have hb₁' : 2 * (i₀ + (T.ratioNat : ℤ) * k T.axis) + 1 < 2 * n T.axis := by
    exact_mod_cast hb₁
  have hb₂' : 2 * n T.axis < 2 * (i₀ + (T.ratioNat : ℤ) * k T.axis + (T.ratioNat : ℤ)) + 1 := by
    exact_mod_cast hb₂
  refine ⟨n T.axis - i₀ - (T.ratioNat : ℤ) * k T.axis, by omega, by omega, ?_⟩
  have hd : (((k T.axis * (T.ratioNat : ℤ) + (n T.axis - i₀ - (T.ratioNat : ℤ) * k T.axis) : ℤ)) :
      ZMod ((m : ℕ) * T.ratioNat)) = ((c : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨-z, ?_⟩
    rw [← hN, hint]
    ring
  rw [hd, hcdef]
  exact ZMod.intCast_zmod_cast i
theorem forwardEdge_factors_through_slab (hEF : T.EdgesAndFields m) (k : Fin 4 → ℤ)
    {e : (T.torusPeriods m).DirectedEdge} (he : e.IsForward) {p p' : InfiniteLattice.LatticePoint D.mesh}
    (hp : (p : AmbientSpace) ∈ interior (T.grid.cell k))
    (hp' : (p' : AmbientSpace) ∈ interior (T.grid.cell k))
    (hsrc : e.source = (T.torusPeriods m).projPoint p)
    (htgt : e.target = (T.torusPeriods m).projPoint p') :
    ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
      ∀ U : (T.torusPeriods m).GaugeConfig, BoxTorus.edgeVariable U e =
        c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) := by
  have hmem : e ∈ range (T.edgeOfSlices m) := by
    rw [hEF.2.1]
    exact he
  obtain ⟨s, rfl⟩ := hmem
  rcases s with ⟨i, b⟩ | ⟨i, y⟩
  · obtain ⟨J, hJ₁, hJ₂, hJ⟩ :=
      exists_sliceLabel_of_mem_interior T m k hp (i := i) (y := b.1.source) hsrc.symm
    have hj : (J - 1).toNat < T.ratioNat := by omega
    refine ⟨fun η => η.1 ⟨(J - 1).toNat, hj⟩ b,
      (measurable_pi_apply b).comp ((measurable_pi_apply _).comp measurable_fst), fun U => ?_⟩
    have hi : T.slabSliceIndex m ((k T.axis : ℤ) : ZMod (m : ℕ))
        ((((J - 1).toNat : ℕ) : ℤ) + 1) = i := by
      rw [slabSliceIndex_intCast, ← hJ]
      congr 2
      omega
    change BoxTorus.edgeVariable U (T.sliceEdge m i b) =
      T.sliceField m U (T.slabSliceIndex m _ ((((J - 1).toNat : ℕ) : ℤ) + 1)) b
    rw [hi]
    rfl
  · obtain ⟨J, hJ₁, hJ₂, hJ⟩ :=
      exists_sliceLabel_of_mem_interior T m k hp (i := i) (y := y) hsrc.symm
    obtain ⟨J', hJ₁', hJ₂', hJ'⟩ :=
      exists_sliceLabel_of_mem_interior T m k hp' (i := i + 1) (y := y) htgt.symm
    have hsucc : ((k T.axis * (T.ratioNat : ℤ) + J' : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) =
        ((k T.axis * (T.ratioNat : ℤ) + J + 1 : ℤ) : ZMod ((m : ℕ) * T.ratioNat)) := by
      rw [hJ', Int.cast_add, hJ, Int.cast_one]
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hsucc
    have hN : 2 * (T.ratioNat : ℤ) ≤ (((m : ℕ) * T.ratioNat : ℕ) : ℤ) := by
      have h2m : (2 : ℤ) ≤ ((m : ℕ) : ℤ) := by exact_mod_cast m.2
      push_cast
      nlinarith
    have hr2 : (2 : ℤ) ≤ (T.ratioNat : ℤ) := by exact_mod_cast T.two_le_ratioNat
    have hz := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
    have hj : (J - 1).toNat < T.ratioNat - 1 := by omega
    refine ⟨fun η => η.2 ⟨(J - 1).toNat, hj⟩ y,
      (measurable_pi_apply y).comp ((measurable_pi_apply _).comp measurable_snd), fun U => ?_⟩
    have hi : T.slabSliceIndex m ((k T.axis : ℤ) : ZMod (m : ℕ))
        ((((J - 1).toNat : ℕ) : ℤ) + 1) = i := by
      rw [slabSliceIndex_intCast, ← hJ]
      congr 2
      omega
    change BoxTorus.edgeVariable U (T.axialEdge m i y) =
      T.axialField m U (T.slabSliceIndex m _ ((((J - 1).toNat : ℕ) : ℤ) + 1)) y
    rw [hi]
    rfl
theorem link_factors_through_slab (hEF : T.EdgesAndFields m) (k : Fin 4 → ℤ) (b : D.Link)
    (hsrc : (b.initial : AmbientSpace) ∈ interior (T.grid.cell k))
    (htgt : (b.terminal : AmbientSpace) ∈ interior (T.grid.cell k)) :
    ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
      ∀ U : (T.torusPeriods m).GaugeConfig, (T.torusPeriods m).liftField U b =
        c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) := by
  by_cases hfwd : ((T.torusPeriods m).projEdge b).IsForward
  · exact forwardEdge_factors_through_slab T m hEF k hfwd hsrc htgt rfl rfl
  · have hflip := BoxTorus.DirectedEdge.flip_isForward hfwd
    obtain ⟨c, hc, hU⟩ := forwardEdge_factors_through_slab T m hEF k hflip htgt hsrc rfl rfl
    refine ⟨fun η => (c η)⁻¹, continuous_inv.measurable.comp hc, fun U => ?_⟩
    have hUU := hU U
    change BoxTorus.edgeVariable U ((T.torusPeriods m).projEdge b) = _
    rw [BoxTorus.edgeVariable, dif_neg hfwd]
    rw [BoxTorus.edgeVariable, dif_pos hflip] at hUU
    exact congrArg (·⁻¹) hUU
theorem statement_holds (hProj : ProjOnEdgesAndFaces.Statement)
    (hTr : TransferAssertions.Statement) : SlabRestrictionOfCellFunctions.Statement := by
  intro D T m _ _ _ k F hF
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  have hEF : T.EdgesAndFields m := (hTr D T m).2.1
  have hlift := (hProj D (T.torusPeriods m)).2.2.1
  have hb : ∀ b : ReflectionGrid.interiorLinks (D := D) (T.grid.cell k),
      ∃ c : T.SlabConfig → Conventions.StandingParameters.gaugeGroup, Measurable c ∧
        ∀ U : (T.torusPeriods m).GaugeConfig, (T.torusPeriods m).liftField U b.1 =
          c (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U) :=
    fun b => link_factors_through_slab T m hEF k b.1 b.2.1 b.2.2
  choose c hcm hc using hb
  refine ⟨fun η => f fun b => c b η, ⟨hf.comp (measurable_pi_lambda _ hcm), C, fun η => hC _⟩,
    fun U => ?_⟩
  change f (ReflectionGrid.restrictField (T.grid.cell k) ((T.torusPeriods m).liftGaugeField U)) = _
  refine congrArg f (funext fun b => ?_)
  rw [← hc b U]
  have hgf : (T.torusPeriods m).liftGaugeField U =
      ⟨(T.torusPeriods m).liftField U, hlift U⟩ := dif_pos (hlift U)
  change ((T.torusPeriods m).liftGaugeField U) b.1 = _
  rw [hgf]
end SlabRestrictionOfCellFunctions
end YangMills.Construction.ChessboardTori
end
