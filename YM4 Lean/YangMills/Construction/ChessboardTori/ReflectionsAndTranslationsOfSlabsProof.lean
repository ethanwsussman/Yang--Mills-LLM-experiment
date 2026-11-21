import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopiesProof
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.ChessboardTori.ReflectionsAndTranslationsOfSlabs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace SlabSymmetryLemmas
variable {D : ChessboardSetup}
theorem linearComponent_eq_of_has {f : AmbientSpace → AmbientSpace}
    {L : AmbientSpace →ₗ[ℝ] AmbientSpace} (hf : HasLinearComponent f L) :
    linearComponent f = L := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.linearComponent_eq <;> assumption
def mirrorLinear (μ : Fin 4) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  LinearMap.id - (LinearMap.proj μ : AmbientSpace →ₗ[ℝ] ℝ).smulRight ((2 : ℝ) • coordVec μ)
theorem mirrorLinear_apply (μ : Fin 4) (x : AmbientSpace) :
    mirrorLinear μ x = x - (x μ) • ((2 : ℝ) • coordVec μ) := rfl
theorem isCoordDiagonal_mirrorLinear (μ : Fin 4) : IsCoordDiagonal (mirrorLinear μ) := by
  intro ν
  by_cases hνμ : ν = μ
  · subst hνμ
    refine ⟨-1, ?_⟩
    funext ρ
    by_cases hρ : ρ = ν
    · subst hρ
      simp [mirrorLinear_apply, coordVec]
      norm_num
    · simp [mirrorLinear_apply, coordVec, Pi.single_eq_of_ne hρ]
  · refine ⟨1, ?_⟩
    have hz : coordVec ν μ = 0 := by simp [coordVec, Pi.single_eq_of_ne (Ne.symm hνμ)]
    rw [mirrorLinear_apply, hz]
    simp
theorem isCoordDiagonal_id : IsCoordDiagonal (LinearMap.id : AmbientSpace →ₗ[ℝ] AmbientSpace) :=
  fun ν => ⟨1, by simp⟩
theorem reflect_apply_axis {g : ReflectionGrid D} (μ : Fin 4) (κ : ℤ) (x : AmbientSpace) :
    g.reflect μ κ x μ = 2 * (g.origin μ + κ * g.cellSide) - x μ := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.reflect_apply_self <;> assumption
theorem reflect_apply_of_ne {g : ReflectionGrid D} (μ : Fin 4) (κ : ℤ) (x : AmbientSpace)
    {ν : Fin 4} (hν : ν ≠ μ) : g.reflect μ κ x ν = x ν := by
  simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne hν]
theorem hasLinearComponent_reflect (g : ReflectionGrid D) (μ : Fin 4) (κ : ℤ) :
    HasLinearComponent (g.reflect μ κ) (mirrorLinear μ) := by
  refine ⟨(2 * (g.origin μ + κ * g.cellSide)) • coordVec μ, fun x => ?_⟩
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [reflect_apply_axis]
    simp [mirrorLinear_apply, coordVec]
    ring
  · rw [reflect_apply_of_ne _ _ _ hν]
    simp [mirrorLinear_apply, coordVec, Pi.single_eq_of_ne hν]
theorem inducesMap_apply {P : PeriodSubgroup D} {f : D.LatticeSym}
    {σ : P.TorusSpace → P.TorusSpace} (hf : P.InducesMap f σ) (w : AmbientSpace) :
    σ (P.proj w) = P.proj (f.toFun w) :=
  (congrFun hf w).symm
theorem proj_exists_preimage (P : PeriodSubgroup D) (u : P.TorusSpace) :
    ∃ w : AmbientSpace, P.proj w = u :=
  BoxTorus.projection_surjective P.sideLengths u
theorem inducesMap_of_proj_eq {P : PeriodSubgroup D} {f f' : D.LatticeSym}
    {σ : P.TorusSpace → P.TorusSpace} (hf : P.InducesMap f σ)
    (hproj : ∀ x, P.proj (f'.toFun x) = P.proj (f.toFun x)) : P.InducesMap f' σ :=
  funext fun x => (hproj x).trans (congrFun hf x)
theorem edgeVariable_flip (hQ : ProjOnEdgesAndFaces.Statement) (P : PeriodSubgroup D)
    (U : P.GaugeConfig) (l : P.DirectedEdge) :
    BoxTorus.edgeVariable U l.flip = (BoxTorus.edgeVariable U l)⁻¹ := by
  obtain ⟨b, rfl⟩ := (hQ D P).1.2.1 l
  have hinv := (hQ D P).2.2.1 U b
  have hrev := (hQ D P).1.2.2.2.2.1 b
  rw [← hrev]
  exact hinv
variable (T : TransferSetup D) (m : SlabCount)
theorem cellSide_eq_ratio_mul_mesh : T.grid.cellSide = (T.ratioNat : ℝ) * D.mesh := by
  rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
  norm_cast
theorem sliceTime_reflect (κ c : ℤ) :
    2 * (T.grid.origin T.axis + κ * T.grid.cellSide) - T.sliceTime c =
      T.sliceTime (2 * κ * (T.ratioNat : ℤ) + 1 - c) := by
  simp only [TransferSetup.sliceTime]
  rw [cellSide_eq_ratio_mul_mesh]
  push_cast
  ring
theorem sliceTime_shift (c : ℤ) :
    T.sliceTime c + 2 * T.grid.cellSide = T.sliceTime (c + 2 * (T.ratioNat : ℤ)) := by
  simp only [TransferSetup.sliceTime]
  rw [cellSide_eq_ratio_mul_mesh]
  push_cast
  ring
theorem cast_sub_dvd (c : ℤ) :
    (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣ (((c : T.SliceLabel m)).cast : ℤ) - c := by
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
  simp
theorem slabSliceIndex_add_intCast (k : ZMod (m : ℕ)) (n j : ℤ) :
    T.slabSliceIndex m (k + (n : ZMod (m : ℕ))) j =
      T.slabSliceIndex m k (n * (T.ratioNat : ℤ) + j) := by
  have hdvd : ((m : ℕ) : ℤ) ∣ ((k + (n : ZMod (m : ℕ))).cast : ℤ) - ((k.cast : ℤ) + n) := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
    simp
  obtain ⟨z, hz⟩ := hdvd
  have hcast : ((k + (n : ZMod (m : ℕ))).cast : ℤ) = (k.cast : ℤ) + n + ((m : ℕ) : ℤ) * z := by
    linarith
  unfold TransferSetup.slabSliceIndex
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨-z, ?_⟩
  rw [hcast]
  push_cast
  ring
theorem slabSliceIndex_add_one (k : ZMod (m : ℕ)) (j : ℤ) :
    T.slabSliceIndex m (k + 1) j = T.slabSliceIndex m k ((T.ratioNat : ℤ) + j) := by
  have key := slabSliceIndex_add_intCast T m k 1 j
  rwa [Int.cast_one, one_mul] at key
theorem slabSliceIndex_add_two (k : ZMod (m : ℕ)) (j : ℤ) :
    T.slabSliceIndex m (k + 2) j = T.slabSliceIndex m k (2 * (T.ratioNat : ℤ) + j) := by
  have key := slabSliceIndex_add_intCast T m k 2 j
  rwa [Int.cast_ofNat] at key
theorem sliceLabel_intCast_add_one (c : ℤ) :
    ((c + 1 : ℤ) : T.SliceLabel m) = (c : T.SliceLabel m) + 1 := by
  push_cast
  rfl
variable {T m}
theorem induced_reflect_axis {κ : ℤ}
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection κ) σ)
    (u : (T.torusPeriods m).TorusSpace) :
    σ u T.axis =
      ((2 * (T.grid.origin T.axis + κ * T.grid.cellSide) : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths T.axis)) - u T.axis := by
  obtain ⟨w, rfl⟩ := proj_exists_preimage _ u
  rw [inducesMap_apply hf]
  change ((T.grid.reflect T.axis κ w T.axis : ℝ) :
    AddCircle ((T.torusPeriods m).sideLengths T.axis)) = _ -
      ((w T.axis : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis))
  rw [reflect_apply_axis]
  rfl
theorem induced_reflect_of_ne {κ : ℤ}
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection κ) σ)
    (u : (T.torusPeriods m).TorusSpace) {ν : Fin 4} (hν : ν ≠ T.axis) : σ u ν = u ν := by
  obtain ⟨w, rfl⟩ := proj_exists_preimage _ u
  rw [inducesMap_apply hf]
  change ((T.grid.reflect T.axis κ w ν : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) =
    ((w ν : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν))
  rw [reflect_apply_of_ne _ _ _ hν]
theorem induced_shift_axis
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap T.twoCellShift σ) (u : (T.torusPeriods m).TorusSpace) :
    σ u T.axis = u T.axis +
      ((2 * T.grid.cellSide : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
  obtain ⟨w, rfl⟩ := proj_exists_preimage _ u
  rw [inducesMap_apply hf]
  change (((w + T.twoCellVector) T.axis : ℝ) :
    AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((w T.axis : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) + _
  have hcoord : (w + T.twoCellVector) T.axis = w T.axis + 2 * T.grid.cellSide := by
    simp [TransferSetup.twoCellVector, coordVec]
  rw [hcoord]
  rfl
theorem induced_shift_of_ne
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap T.twoCellShift σ) (u : (T.torusPeriods m).TorusSpace)
    {ν : Fin 4} (hν : ν ≠ T.axis) : σ u ν = u ν := by
  obtain ⟨w, rfl⟩ := proj_exists_preimage _ u
  rw [inducesMap_apply hf]
  change (((w + T.twoCellVector) ν : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) =
    ((w ν : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν))
  have hcoord : (w + T.twoCellVector) ν = w ν := by
    simp [TransferSetup.twoCellVector, coordVec, Pi.single_eq_of_ne hν]
  rw [hcoord]
theorem eq_torusPoint {u : (T.torusPeriods m).TorusSpace} {t : ℝ} {y : T.TransverseTorus}
    (hax : u T.axis = (t : AddCircle ((T.torusPeriods m).sideLengths T.axis)))
    (hrest : ∀ ν, ν ≠ T.axis → u ν = T.torusPoint m 0 y ν) : u = T.torusPoint m t y := by
  funext ν
  by_cases hν : ν = T.axis
  · subst hν
    rw [T.torusPoint_axis, hax]
  · rw [hrest ν hν]
    exact (T.torusPoint_transverse m 0 y ⟨ν, hν⟩).trans
      (T.torusPoint_transverse m t y ⟨ν, hν⟩).symm
theorem torusPoint_apply_of_ne (t t' : ℝ) (y : T.TransverseTorus) {ν : Fin 4}
    (hν : ν ≠ T.axis) : T.torusPoint m t y ν = T.torusPoint m t' y ν :=
  (T.torusPoint_transverse m t y ⟨ν, hν⟩).trans (T.torusPoint_transverse m t' y ⟨ν, hν⟩).symm
theorem coe_gridSite_intCast (c : ℤ) (y : T.TransverseSite) :
    ((T.gridSite m (c : T.SliceLabel m) y : (T.torusPeriods m).GridPoint) :
      (T.torusPeriods m).TorusSpace) = T.torusPoint m (T.sliceTime c) (y : T.TransverseTorus) :=
  T.torusPoint_congr m (T.coe_sliceTime_eq m (cast_sub_dvd T m c)) _
theorem induced_reflect_gridSite {κ : ℤ}
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection κ) σ) (c : ℤ) (y : T.TransverseSite) :
    σ (T.gridSite m (c : T.SliceLabel m) y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m ((2 * κ * (T.ratioNat : ℤ) + 1 - c : ℤ) : T.SliceLabel m) y :
        (T.torusPeriods m).GridPoint) := by
  rw [coe_gridSite_intCast, coe_gridSite_intCast]
  refine eq_torusPoint ?_ fun ν hν => ?_
  · rw [induced_reflect_axis hf, T.torusPoint_axis, ← sliceTime_reflect]
    rfl
  · rw [induced_reflect_of_ne hf _ hν]
    exact torusPoint_apply_of_ne _ _ _ hν
theorem induced_shift_gridSite
    {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hf : (T.torusPeriods m).InducesMap T.twoCellShift σ) (c : ℤ) (y : T.TransverseSite) :
    σ (T.gridSite m (c : T.SliceLabel m) y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m ((c + 2 * (T.ratioNat : ℤ) : ℤ) : T.SliceLabel m) y :
        (T.torusPeriods m).GridPoint) := by
  rw [coe_gridSite_intCast, coe_gridSite_intCast]
  refine eq_torusPoint ?_ fun ν hν => ?_
  · rw [induced_shift_axis hf, T.torusPoint_axis, ← sliceTime_shift]
    rfl
  · rw [induced_shift_of_ne hf _ hν]
    exact torusPoint_apply_of_ne _ _ _ hν
section Edges
variable {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
theorem mapEdge_sliceEdge (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    {i i' : T.SliceLabel m}
    (hsite : ∀ y : T.TransverseSite, σ (T.gridSite m i y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m i' y : (T.torusPeriods m).GridPoint)) (b : T.PositiveTransverseEdge) :
    (T.torusPeriods m).mapEdge σ (T.sliceEdge m i b) = T.sliceEdge m i' b := by
  obtain ⟨hs, ht⟩ := hσ.2.2.1 (T.sliceEdge m i b)
  exact BoxTorus.DirectedEdge.ext (Subtype.ext (hs.trans (hsite _)))
    (Subtype.ext (ht.trans (hsite _)))
theorem mapEdge_axialEdge (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    {i i' : T.SliceLabel m}
    (hsite : ∀ y : T.TransverseSite, σ (T.gridSite m i y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m i' y : (T.torusPeriods m).GridPoint))
    (hsite' : ∀ y : T.TransverseSite, σ (T.gridSite m (i + 1) y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m (i' + 1) y : (T.torusPeriods m).GridPoint)) (y : T.TransverseSite) :
    (T.torusPeriods m).mapEdge σ (T.axialEdge m i y) = T.axialEdge m i' y := by
  obtain ⟨hs, ht⟩ := hσ.2.2.1 (T.axialEdge m i y)
  exact BoxTorus.DirectedEdge.ext (Subtype.ext (hs.trans (hsite _)))
    (Subtype.ext (ht.trans (hsite' _)))
theorem mapEdge_axialEdge_flip (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    {i i' : T.SliceLabel m}
    (hsite : ∀ y : T.TransverseSite, σ (T.gridSite m i y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m (i' + 1) y : (T.torusPeriods m).GridPoint))
    (hsite' : ∀ y : T.TransverseSite, σ (T.gridSite m (i + 1) y : (T.torusPeriods m).GridPoint) =
      (T.gridSite m i' y : (T.torusPeriods m).GridPoint)) (y : T.TransverseSite) :
    (T.torusPeriods m).mapEdge σ (T.axialEdge m i y) = (T.axialEdge m i' y).flip := by
  obtain ⟨hs, ht⟩ := hσ.2.2.1 (T.axialEdge m i y)
  exact BoxTorus.DirectedEdge.ext (Subtype.ext (hs.trans (hsite _)))
    (Subtype.ext (ht.trans (hsite' _)))
def PullsBackEdges (σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace) : Prop :=
  ∀ (U : (T.torusPeriods m).GaugeConfig) (b : (T.torusPeriods m).DirectedEdge),
    BoxTorus.edgeVariable ((T.torusPeriods m).pullback σ U) b =
      BoxTorus.edgeVariable U ((T.torusPeriods m).mapEdge σ b)
theorem slabRestriction_pullback_reflect (hQ : ProjOnEdgesAndFaces.Statement)
    (k : ZMod (m : ℕ))
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection ((k.cast : ℤ) + 1)) σ)
    (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    (hpull : PullsBackEdges (T := T) (m := m) σ)
    (U : (T.torusPeriods m).GaugeConfig) :
    T.slabRestriction m k ((T.torusPeriods m).pullback σ U) =
      T.slabReverse (T.slabRestriction m (k + 1) U) := by
  have hr := T.two_le_ratioNat
  refine Prod.ext (funext fun j => funext fun b => ?_) (funext fun j => funext fun y => ?_)
  · change BoxTorus.edgeVariable ((T.torusPeriods m).pullback σ U)
        (T.sliceEdge m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) b) =
      BoxTorus.edgeVariable U
        (T.sliceEdge m (T.slabSliceIndex m (k + 1) (((j.rev : ℕ) : ℤ) + 1)) b)
    rw [hpull]
    have hidx : T.slabSliceIndex m (k + 1) (((j.rev : ℕ) : ℤ) + 1) =
        ((2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1)) : ℤ) : T.SliceLabel m) := by
      rw [slabSliceIndex_add_one]
      have hj : ((j.rev : ℕ) : ℤ) = (T.ratioNat : ℤ) - 1 - ((j : ℕ) : ℤ) := by
        have := j.2
        rw [Fin.val_rev]
        omega
      unfold TransferSetup.slabSliceIndex
      rw [hj]
      congr 1
      ring
    rw [hidx]
    exact congrArg _ (mapEdge_sliceEdge hσ (fun y => induced_reflect_gridSite hf _ y) b)
  · change BoxTorus.edgeVariable ((T.torusPeriods m).pullback σ U)
        (T.axialEdge m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) y) =
      (BoxTorus.edgeVariable U
        (T.axialEdge m (T.slabSliceIndex m (k + 1) (((j.rev : ℕ) : ℤ) + 1)) y))⁻¹
    rw [hpull, ← edgeVariable_flip hQ]
    have hidx : T.slabSliceIndex m (k + 1) (((j.rev : ℕ) : ℤ) + 1) =
        ((2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1)) - 1 : ℤ) :
            T.SliceLabel m) := by
      rw [slabSliceIndex_add_one]
      have hj : ((j.rev : ℕ) : ℤ) = (T.ratioNat : ℤ) - 2 - ((j : ℕ) : ℤ) := by
        have := j.2
        rw [Fin.val_rev]
        omega
      unfold TransferSetup.slabSliceIndex
      rw [hj]
      congr 1
      ring
    rw [hidx]
    refine congrArg _ (mapEdge_axialEdge_flip hσ (fun y => ?_) (fun y => ?_) y)
    · have key := induced_reflect_gridSite hf
        ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1)) y
      rw [← sliceLabel_intCast_add_one, sub_add_cancel]
      exact key
    · have key := induced_reflect_gridSite hf
        ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1) + 1) y
      rw [sliceLabel_intCast_add_one] at key
      rw [show (2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1)) - 1 : ℤ) =
        2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1) + 1) by ring]
      exact key
theorem slabRestriction_pullback_shift (k : ZMod (m : ℕ))
    (hf : (T.torusPeriods m).InducesMap T.twoCellShift σ)
    (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    (hpull : PullsBackEdges (T := T) (m := m) σ)
    (U : (T.torusPeriods m).GaugeConfig) :
    T.slabRestriction m k ((T.torusPeriods m).pullback σ U) = T.slabRestriction m (k + 2) U := by
  have hidx : ∀ j : ℤ, T.slabSliceIndex m (k + 2) j =
      (((k.cast : ℤ) * (T.ratioNat : ℤ) + j + 2 * (T.ratioNat : ℤ) : ℤ) : T.SliceLabel m) := by
    intro j
    rw [slabSliceIndex_add_two]
    unfold TransferSetup.slabSliceIndex
    congr 1
    ring
  refine Prod.ext (funext fun j => funext fun b => ?_) (funext fun j => funext fun y => ?_)
  · change BoxTorus.edgeVariable ((T.torusPeriods m).pullback σ U)
        (T.sliceEdge m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) b) =
      BoxTorus.edgeVariable U
        (T.sliceEdge m (T.slabSliceIndex m (k + 2) (((j : ℕ) : ℤ) + 1)) b)
    rw [hpull, hidx]
    exact congrArg _ (mapEdge_sliceEdge hσ (fun y => induced_shift_gridSite hf _ y) b)
  · change BoxTorus.edgeVariable ((T.torusPeriods m).pullback σ U)
        (T.axialEdge m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) y) =
      BoxTorus.edgeVariable U
        (T.axialEdge m (T.slabSliceIndex m (k + 2) (((j : ℕ) : ℤ) + 1)) y)
    rw [hpull, hidx]
    refine congrArg _
      (mapEdge_axialEdge hσ (fun y => induced_shift_gridSite hf _ y) (fun y => ?_) y)
    have key := induced_shift_gridSite hf
      ((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1) + 1) y
    rw [sliceLabel_intCast_add_one] at key
    rw [show (((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1) + 2 * (T.ratioNat : ℤ) : ℤ) :
        T.SliceLabel m) + 1 = (((k.cast : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1) + 1 +
          2 * (T.ratioNat : ℤ) : ℤ) : T.SliceLabel m) by
      rw [← sliceLabel_intCast_add_one]
      congr 1
      ring]
    exact key
end Edges
section Faces
variable {σ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
theorem mem_sliceSet_intCast_iff (c : ℤ) (x : (T.torusPeriods m).GridPoint) :
    x ∈ T.sliceSet m (c : T.SliceLabel m) ↔
      (x : (T.torusPeriods m).TorusSpace) T.axis =
        ((T.sliceTime c : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
  change (x : (T.torusPeriods m).TorusSpace) T.axis =
      ((T.sliceTime (((c : T.SliceLabel m)).cast : ℤ) : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths T.axis)) ↔ _
  rw [T.coe_sliceTime_eq m (cast_sub_dvd T m c)]
theorem mem_sliceSet_of_image {κ : ℤ}
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection κ) σ)
    {x x' : (T.torusPeriods m).GridPoint}
    (hx' : σ (x : (T.torusPeriods m).TorusSpace) = x') {c : ℤ}
    (hx : x ∈ T.sliceSet m (c : T.SliceLabel m)) :
    x' ∈ T.sliceSet m ((2 * κ * (T.ratioNat : ℤ) + 1 - c : ℤ) : T.SliceLabel m) := by
  rw [mem_sliceSet_intCast_iff] at hx ⊢
  rw [← hx', induced_reflect_axis hf, hx, ← sliceTime_reflect]
  rfl
theorem mem_sliceSet_of_preimage {κ : ℤ}
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection κ) σ)
    {x x' : (T.torusPeriods m).GridPoint}
    (hx' : σ (x : (T.torusPeriods m).TorusSpace) = x') {c : ℤ}
    (hx : x' ∈ T.sliceSet m (c : T.SliceLabel m)) :
    x ∈ T.sliceSet m ((2 * κ * (T.ratioNat : ℤ) + 1 - c : ℤ) : T.SliceLabel m) := by
  rw [mem_sliceSet_intCast_iff] at hx ⊢
  rw [← hx', induced_reflect_axis hf] at hx
  rw [← sliceTime_reflect]
  have hsub : ((2 * (T.grid.origin T.axis + κ * T.grid.cellSide) - T.sliceTime c : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((2 * (T.grid.origin T.axis + κ * T.grid.cellSide) : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths T.axis)) - (T.sliceTime c : ℝ) := rfl
  rw [hsub, ← hx]
  abel
theorem bijOn_mapFace_slab (k : ZMod (m : ℕ))
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection ((k.cast : ℤ) + 1)) σ)
    (hσ : (T.torusPeriods m).RespectsLatticeStructure σ) :
    BijOn ((T.torusPeriods m).mapFace σ) {p | T.IsInSlab m k p}
      {p | T.IsInSlab m (k + 1) p} := by
  have hverts := hσ.2.2.2.2.2.1
  have hbij := hσ.2.2.2.2.2.2.1
  refine ⟨fun p hp x' hx' => ?_, hbij.1.injOn, fun p' hp' => ?_⟩
  · have hmem : (x' : (T.torusPeriods m).TorusSpace) ∈ σ ''
        ((fun x : (T.torusPeriods m).GridPoint => (x : (T.torusPeriods m).TorusSpace)) ''
          p.vertexSet) := by
      rw [← hverts p]
      exact ⟨x', hx', rfl⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hxx⟩ := hmem
    obtain ⟨i, ⟨j, hj₁, hj₂, rfl⟩, hxi⟩ := hp x hx
    refine ⟨T.slabSliceIndex m (k + 1) ((T.ratioNat : ℤ) + 1 - j),
      ⟨(T.ratioNat : ℤ) + 1 - j, by omega, by omega, rfl⟩, ?_⟩
    have hnew := mem_sliceSet_of_image hf hxx hxi
    have hidx : T.slabSliceIndex m (k + 1) ((T.ratioNat : ℤ) + 1 - j) =
        ((2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + j) : ℤ) : T.SliceLabel m) := by
      rw [slabSliceIndex_add_one]
      unfold TransferSetup.slabSliceIndex
      congr 1
      ring
    rw [hidx]
    exact hnew
  · obtain ⟨p, rfl⟩ := hbij.2 p'
    refine ⟨p, fun x hx => ?_, rfl⟩
    have hmem : σ (x : (T.torusPeriods m).TorusSpace) ∈
        (fun x : (T.torusPeriods m).GridPoint => (x : (T.torusPeriods m).TorusSpace)) ''
          ((T.torusPeriods m).mapFace σ p).vertexSet := by
      rw [hverts p]
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hmem
    obtain ⟨i, ⟨j, hj₁, hj₂, rfl⟩, hxi⟩ := hp' x' hx'
    rw [slabSliceIndex_add_one] at hxi
    refine ⟨T.slabSliceIndex m k ((T.ratioNat : ℤ) + 1 - j),
      ⟨(T.ratioNat : ℤ) + 1 - j, by omega, by omega, rfl⟩, ?_⟩
    have hnew := mem_sliceSet_of_preimage hf hxx.symm hxi
    have hidx : T.slabSliceIndex m k ((T.ratioNat : ℤ) + 1 - j) =
        ((2 * ((k.cast : ℤ) + 1) * (T.ratioNat : ℤ) + 1 -
          ((k.cast : ℤ) * (T.ratioNat : ℤ) + ((T.ratioNat : ℤ) + j)) : ℤ) : T.SliceLabel m) := by
      unfold TransferSetup.slabSliceIndex
      congr 1
      ring
    rw [hidx]
    exact hnew
theorem conj_finprod_mem {α : Type*} (Q : α → Prop) (f : α → ℂ) :
    starRingEnd ℂ (∏ᶠ (p : α) (_ : Q p), f p) =
      ∏ᶠ (p : α) (_ : Q p), starRingEnd ℂ (f p) := by
  have hinj : Function.Injective (starRingEnd ℂ : ℂ →+* ℂ).toMonoidHom :=
    (starRingEnd ℂ : ℂ →+* ℂ).injective
  have key := (starRingEnd ℂ : ℂ →+* ℂ).toMonoidHom.map_finprod_of_injective hinj
    (fun p => ∏ᶠ (_ : Q p), f p)
  refine key.trans (finprod_congr fun p => ?_)
  exact (starRingEnd ℂ : ℂ →+* ℂ).toMonoidHom.map_finprod_of_injective hinj _
theorem slabBoltzmann_succ_eq_reflectConj (k : ZMod (m : ℕ))
    (hf : (T.torusPeriods m).InducesMap (T.planeReflection ((k.cast : ℤ) + 1)) σ)
    (hσ : (T.torusPeriods m).RespectsLatticeStructure σ)
    (hrestr : ∀ U, T.slabRestriction m k ((T.torusPeriods m).pullback σ U) =
      T.slabReverse (T.slabRestriction m (k + 1) U))
    (henergy : ∀ (U : (T.torusPeriods m).GaugeConfig) (p : (T.torusPeriods m).Face),
      (T.torusPeriods m).faceEnergy ((T.torusPeriods m).pullback σ U) p =
        (T.torusPeriods m).faceEnergy U ((T.torusPeriods m).mapFace σ p))
    (hsurj : Function.Surjective (T.slabRestriction m (k + 1)))
    (w : (T.torusPeriods m).Face → ℂ)
    (hB : ∀ (k' : ZMod (m : ℕ)) (U : (T.torusPeriods m).GaugeConfig),
      T.slabBoltzmann m w k' (T.slabRestriction m k' U) =
        ∏ᶠ (p : (T.torusPeriods m).Face) (_ : T.IsInSlab m k' p),
          Complex.exp ((w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ)))
    (hw : ∀ p, T.IsInSlab m k p →
      w ((T.torusPeriods m).mapFace σ p) = starRingEnd ℂ (w p)) :
    T.slabBoltzmann m w (k + 1) = T.reflectConj (T.slabBoltzmann m w k) := by
  funext η
  obtain ⟨U, rfl⟩ := hsurj η
  rw [TransferSetup.reflectConj, ← hrestr, hB, hB, conj_finprod_mem]
  refine (finprod_mem_eq_of_bijOn _ (bijOn_mapFace_slab k hf hσ) fun p hp => ?_).symm
  rw [← Complex.exp_conj, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_ofReal, henergy,
    hw p hp]
end Faces
end SlabSymmetryLemmas
open SlabSymmetryLemmas in
theorem SlabSymmetries.proof (hI : QuotientMapsStatement)
    (hP : TransferAssertions.Statement)
    (hQ : ProjOnEdgesAndFaces.Statement) :
    SlabSymmetries.Statement := by
  intro D T m _ k
  have hdiagR : ∀ κ : ℤ, IsCoordDiagonal (linearComponent (T.planeReflection κ).toFun) :=
    fun κ => by
      have hlin : linearComponent (T.planeReflection κ).toFun = mirrorLinear T.axis :=
        linearComponent_eq_of_has (hasLinearComponent_reflect T.grid T.axis κ)
      rw [hlin]
      exact isCoordDiagonal_mirrorLinear _
  have hdiagS : IsCoordDiagonal (linearComponent T.twoCellShift.toFun) := by
    have hlin : linearComponent T.twoCellShift.toFun = LinearMap.id :=
      linearComponent_eq_of_has ⟨T.twoCellVector, fun x => rfl⟩
    rw [hlin]
    exact isCoordDiagonal_id
  have hR := ((hI D).1 (T.torusPeriods m) (T.planeReflection ((k.cast : ℤ) + 1))
    ((hI D).2.2.1 _ _ (hdiagR _)))
  have hS := ((hI D).1 (T.torusPeriods m) T.twoCellShift
    ((hI D).2.2.1 _ _ hdiagS))
  have hfR : (T.torusPeriods m).InducesMap (T.planeReflection ((k.cast : ℤ) + 1))
      (T.slabFlip m k) := hR.1.1
  have hfS : (T.torusPeriods m).InducesMap T.twoCellShift (T.slabShift m) := hS.1.1
  have hσR : (T.torusPeriods m).RespectsLatticeStructure (T.slabFlip m k) := hR.2.1
  have hσS : (T.torusPeriods m).RespectsLatticeStructure (T.slabShift m) := hS.2.1
  have hpR : PullsBackEdges (T := T) (m := m) (T.slabFlip m k) := fun U b => (hR.2.2.2.1 U).1 b
  have hpS : PullsBackEdges (T := T) (m := m) (T.slabShift m) := fun U b => (hS.2.2.2.1 U).1 b
  have hηR := slabRestriction_pullback_reflect hQ k hfR hσR hpR
  have hηS := slabRestriction_pullback_shift k hfS hσS hpS
  obtain ⟨-, -, -, -, -, -, hV, -, hB⟩ := hP D T m
  refine ⟨fun κ hκ => ?_, hfS, hσR.1, hσS.1, hσR.2.1, hσS.2.1, hηR, hηS, fun Φ _ => ⟨?_, ?_⟩,
    fun w hw => ⟨fun U => ((hB w hw).1 k).2.2 U, fun hc => ?_⟩⟩
  · refine inducesMap_of_proj_eq hfR fun x => ?_
    have hd : ((m : ℕ) : ℤ) ∣ κ - (k.cast : ℤ) := by
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
      rw [hκ]
      simp
    obtain ⟨z, hz⟩ := hd
    funext ν
    by_cases hν : ν = T.axis
    · subst hν
      change ((T.grid.reflect T.axis (κ + 1) x T.axis : ℝ) :
          AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
        ((T.grid.reflect T.axis ((k.cast : ℤ) + 1) x T.axis : ℝ) :
          AddCircle ((T.torusPeriods m).sideLengths T.axis))
      rw [reflect_apply_axis, reflect_apply_axis]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨2 * z, ?_⟩)
      have hκ' : (κ : ℝ) = (k.cast : ℤ) + ((m : ℕ) : ℝ) * z := by
        have : κ = (k.cast : ℤ) + ((m : ℕ) : ℤ) * z := by omega
        exact_mod_cast this
      rw [T.sideLengths_axis, zsmul_eq_mul, cellSide_eq_ratio_mul_mesh]
      push_cast
      rw [hκ']
      ring
    · change ((T.grid.reflect T.axis (κ + 1) x ν : ℝ) :
          AddCircle ((T.torusPeriods m).sideLengths ν)) =
        ((T.grid.reflect T.axis ((k.cast : ℤ) + 1) x ν : ℝ) :
          AddCircle ((T.torusPeriods m).sideLengths ν))
      rw [reflect_apply_of_ne _ _ _ hν, reflect_apply_of_ne _ _ _ hν]
  · funext U
    change starRingEnd ℂ (Φ (T.slabRestriction m k ((T.torusPeriods m).pullback _ U))) =
      starRingEnd ℂ (Φ (T.slabReverse (T.slabRestriction m (k + 1) U)))
    rw [hηR]
  · funext U
    change Φ (T.slabRestriction m k ((T.torusPeriods m).pullback _ U)) =
      Φ (T.slabRestriction m (k + 2) U)
    rw [hηS]
  · refine slabBoltzmann_succ_eq_reflectConj k hfR hσR hηR (fun U p => (hR.2.2.2.1 U).2.2 p) ?_ w
      (fun k' U => ((hB w hw).1 k').2.2 U) hc
    intro η
    obtain ⟨U, hU⟩ := hV.1.bijective.2 (fun _ => η, fun _ _ => 1)
    exact ⟨U, congrFun (congrArg Prod.fst hU) (k + 1)⟩
end YangMills.Construction.ChessboardTori
end
