import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
abbrev TransverseAxis (μ : Fin 4) : Type := {ν : Fin 4 // ν ≠ μ}
abbrev SlabCount : Type := {m : ℕ // 2 ≤ m}
instance (m : SlabCount) : NeZero (m : ℕ) := ⟨by have := m.2; omega⟩
def addCircleCast {p q : ℝ} (h : p = q) (x : AddCircle p) : AddCircle q := h ▸ x
theorem addCircleCast_coe {p q : ℝ} (h : p = q) (z : ℝ) :
    addCircleCast h (z : AddCircle p) = (z : AddCircle q) := by
  subst h
  rfl
theorem addCircleCast_add {p q : ℝ} (h : p = q) (x x' : AddCircle p) :
    addCircleCast h (x + x') = addCircleCast h x + addCircleCast h x' := by
  subst h
  rfl
structure TransferSetup (D : ChessboardSetup) where
  grid : ReflectionGrid D
  axis : Fin 4
  transverseCells : TransverseAxis axis → ℤ
  two_le_transverseCells : ∀ ν, 2 ≤ transverseCells ν
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def ratioNat : ℕ := T.grid.cellRatio.toNat
theorem natCast_ratioNat : (T.ratioNat : ℤ) = T.grid.cellRatio :=
  Int.toNat_of_nonneg (by have := T.grid.two_le_cellRatio; omega)
theorem two_le_ratioNat : 2 ≤ T.ratioNat := by
  have h := T.natCast_ratioNat
  have := T.grid.two_le_cellRatio
  omega
def cellCounts (m : SlabCount) (ν : Fin 4) : ℤ :=
  if h : ν = T.axis then ((m : ℕ) : ℤ) else T.transverseCells ⟨ν, h⟩
theorem two_le_cellCounts (m : SlabCount) (ν : Fin 4) : 2 ≤ T.cellCounts m ν := by
  unfold cellCounts
  split_ifs with h
  · exact_mod_cast m.2
  · exact T.two_le_transverseCells _
def torusPeriods (m : SlabCount) : PeriodSubgroup D :=
  T.grid.boxPeriods (T.cellCounts m) (T.two_le_cellCounts m)
def sliceTime (i : ℤ) : ℝ := T.grid.origin T.axis - D.mesh / 2 + i * D.mesh
abbrev SliceLabel (m : SlabCount) : Type := ZMod ((m : ℕ) * T.ratioNat)
instance (m : SlabCount) : NeZero ((m : ℕ) * T.ratioNat) :=
  ⟨Nat.mul_ne_zero (NeZero.ne _) (by have := T.two_le_ratioNat; omega)⟩
def sliceSet (m : SlabCount) (i : T.SliceLabel m) : Set (T.torusPeriods m).GridPoint :=
  {x | (x : (T.torusPeriods m).TorusSpace) T.axis =
    ((T.sliceTime (i.cast : ℤ) : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis))}
def slabSliceIndex (m : SlabCount) (k : ZMod (m : ℕ)) (j : ℤ) : T.SliceLabel m :=
  (((k.cast : ℤ) * (T.ratioNat : ℤ) + j : ℤ) : ZMod ((m : ℕ) * T.ratioNat))
def slabSet (m : SlabCount) (k : ZMod (m : ℕ)) : Set (T.SliceLabel m) :=
  {i | ∃ j : ℤ, 1 ≤ j ∧ j ≤ T.ratioNat ∧ i = T.slabSliceIndex m k j}
def transverseSide (ν : TransverseAxis T.axis) : ℝ :=
  (T.transverseCells ν : ℝ) * T.grid.cellSide
abbrev TransverseTorus : Type := (ν : TransverseAxis T.axis) → AddCircle (T.transverseSide ν)
def transverseLattice : AddSubgroup T.TransverseTorus :=
  AddSubgroup.pi univ fun ν => AddSubgroup.zmultiples ((D.mesh : ℝ) : AddCircle (T.transverseSide ν))
abbrev TransverseSite : Type := ↥T.transverseLattice
def transverseVector (ν : TransverseAxis T.axis) (s : ℝ) : T.TransverseTorus :=
  Pi.single ν (s : AddCircle (T.transverseSide ν))
def transverseStep (ν : TransverseAxis T.axis) : T.TransverseSite :=
  ⟨T.transverseVector ν D.mesh, (AddSubgroup.mem_pi _).mpr fun ν' _ => by
    by_cases h : ν' = ν
    · subst h
      simp [transverseVector]
    · simp [transverseVector, Pi.single_eq_of_ne h, zero_mem]⟩
@[ext]
structure TransverseEdge where
  source : T.TransverseSite
  target : T.TransverseSite
  isAdjacent : ∃ ν, target - source = T.transverseStep ν ∨ target - source = -T.transverseStep ν
abbrev PositiveTransverseEdge : Type :=
  {b : T.TransverseEdge // ∃ ν, b.target - b.source = T.transverseStep ν}
def edgeAxis (b : T.PositiveTransverseEdge) : TransverseAxis T.axis := b.2.choose
theorem target_sub_source (b : T.PositiveTransverseEdge) :
    b.1.target - b.1.source = T.transverseStep (T.edgeAxis b) :=
  b.2.choose_spec
def forwardEdge (y : T.TransverseSite) (ν : TransverseAxis T.axis) :
    T.PositiveTransverseEdge :=
  ⟨⟨y, y + T.transverseStep ν, ν, Or.inl (by simp)⟩, ν, by simp⟩
@[ext]
structure TransverseFace where
  corner : T.TransverseSite
  axis₁ : TransverseAxis T.axis
  axis₂ : TransverseAxis T.axis
  axis₁_lt_axis₂ : axis₁.1 < axis₂.1
instance : Finite T.TransverseSite := by
  have hfin : ∀ ν, Finite ↥(AddSubgroup.zmultiples ((D.mesh : ℝ) : AddCircle (T.transverseSide ν))) := by
    intro ν
    have hc : (T.transverseSide ν) = ((T.transverseCells ν * T.grid.cellRatio : ℤ) : ℝ) * D.mesh := by
      rw [transverseSide, T.grid.cellSide_eq]
      push_cast
      ring
    have hN : 0 < (T.transverseCells ν * T.grid.cellRatio).natAbs := by
      have h1 := T.two_le_transverseCells ν
      have h2 := T.grid.two_le_cellRatio
      have : 0 < T.transverseCells ν * T.grid.cellRatio := by positivity
      omega
    have hord : IsOfFinAddOrder ((D.mesh : ℝ) : AddCircle (T.transverseSide ν)) := by
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr
        ⟨(T.transverseCells ν * T.grid.cellRatio).natAbs, hN, ?_⟩
      have hnn : 0 ≤ T.transverseCells ν * T.grid.cellRatio := by
        have h1 := T.two_le_transverseCells ν
        have h2 := T.grid.two_le_cellRatio
        positivity
      have hcast : (((T.transverseCells ν * T.grid.cellRatio).natAbs : ℕ) : ℝ) =
          ((T.transverseCells ν * T.grid.cellRatio : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hnn]
      rw [← AddCircle.coe_nsmul, nsmul_eq_mul, hcast, ← hc]
      exact AddCircle.coe_period _
    exact (hord.finite_zmultiples).to_subtype
  refine Finite.of_injective (β := (ν : TransverseAxis T.axis) →
    ↥(AddSubgroup.zmultiples ((D.mesh : ℝ) : AddCircle (T.transverseSide ν))))
    (fun y ν => ⟨(y : T.TransverseTorus) ν, (AddSubgroup.mem_pi _).mp y.2 ν (mem_univ ν)⟩) ?_
  intro y y' h
  refine Subtype.ext (funext fun ν => ?_)
  exact congrArg Subtype.val (congrFun h ν)
instance : Finite T.TransverseEdge :=
  Finite.of_injective (fun b : T.TransverseEdge => (b.source, b.target)) fun _ _ h =>
    TransverseEdge.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
instance : Finite T.TransverseFace :=
  Finite.of_injective (fun q : T.TransverseFace => (q.corner, q.axis₁, q.axis₂)) fun q q' h => by
    simp only [Prod.mk.injEq] at h
    exact TransverseFace.ext h.1 h.2.1 h.2.2
instance : Fintype T.PositiveTransverseEdge := Fintype.ofFinite _
instance : Fintype T.TransverseFace := Fintype.ofFinite _
def faceCentre (q : T.TransverseFace) : T.TransverseTorus :=
  (q.corner : T.TransverseTorus) +
    (T.transverseVector q.axis₁ (D.mesh / 2) + T.transverseVector q.axis₂ (D.mesh / 2))
def edgeMidpoint (b : T.PositiveTransverseEdge) : T.TransverseTorus :=
  (b.1.source : T.TransverseTorus) + T.transverseVector (T.edgeAxis b) (D.mesh / 2)
abbrev EdgeField : Type := T.PositiveTransverseEdge → Conventions.StandingParameters.gaugeGroup
abbrev SiteField : Type := T.TransverseSite → Conventions.StandingParameters.gaugeGroup
def edgeHaar : Measure T.EdgeField := Matrices.ComplexMatrix2.haarPi T.PositiveTransverseEdge
def siteHaar : Measure T.SiteField := Matrices.ComplexMatrix2.haarPi T.TransverseSite
instance : IsProbabilityMeasure T.edgeHaar :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ => Matrices.ComplexMatrix2.haarProb))
instance : IsProbabilityMeasure T.siteHaar :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ => Matrices.ComplexMatrix2.haarProb))
def faceHolonomy (ξ : T.EdgeField) (q : T.TransverseFace) :
    Conventions.StandingParameters.gaugeGroup :=
  ξ (T.forwardEdge q.corner q.axis₁) *
    ξ (T.forwardEdge (q.corner + T.transverseStep q.axis₁) q.axis₂) *
    (ξ (T.forwardEdge (q.corner + T.transverseStep q.axis₂) q.axis₁))⁻¹ *
    (ξ (T.forwardEdge q.corner q.axis₂))⁻¹
def faceAction (q : T.TransverseFace) (ξ : T.EdgeField) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
    (T.faceHolonomy ξ q : Matrices.ComplexMatrix2)).re
theorem sideLengths_axis (m : SlabCount) :
    (T.torusPeriods m).sideLengths T.axis = (((m : ℕ) * T.ratioNat : ℕ) : ℝ) * D.mesh := by
  change (((T.cellCounts m T.axis * T.grid.cellRatio : ℤ) : ℝ)) * D.mesh = _
  rw [cellCounts, dif_pos rfl, ← T.natCast_ratioNat]
  push_cast
  ring
theorem transverseSide_eq_sideLengths (m : SlabCount) (ν : TransverseAxis T.axis) :
    T.transverseSide ν = (T.torusPeriods m).sideLengths ν.1 := by
  change _ = (((T.cellCounts m ν.1 * T.grid.cellRatio : ℤ) : ℝ)) * D.mesh
  rw [cellCounts, dif_neg ν.2, transverseSide, T.grid.cellSide_eq]
  push_cast
  ring
def ambientPoint (t : ℝ) (y : TransverseAxis T.axis → ℝ) : AmbientSpace :=
  fun ν => if h : ν = T.axis then t else y ⟨ν, h⟩
def torusPoint (m : SlabCount) (t : ℝ) (y : T.TransverseTorus) : (T.torusPeriods m).TorusSpace :=
  fun ν => if h : ν = T.axis then (t : AddCircle ((T.torusPeriods m).sideLengths ν))
    else addCircleCast (T.transverseSide_eq_sideLengths m ⟨ν, h⟩) (y ⟨ν, h⟩)
theorem torusPoint_axis (m : SlabCount) (t : ℝ) (y : T.TransverseTorus) :
    T.torusPoint m t y T.axis = (t : AddCircle ((T.torusPeriods m).sideLengths T.axis)) :=
  dif_pos rfl
theorem torusPoint_transverse (m : SlabCount) (t : ℝ) (y : T.TransverseTorus)
    (ν : TransverseAxis T.axis) :
    T.torusPoint m t y ν.1 = addCircleCast (T.transverseSide_eq_sideLengths m ν) (y ν) :=
  dif_neg ν.2
theorem torusPoint_congr (m : SlabCount) {t t' : ℝ}
    (h : (t : AddCircle ((T.torusPeriods m).sideLengths T.axis)) = t') (y : T.TransverseTorus) :
    T.torusPoint m t y = T.torusPoint m t' y := by
  funext ν
  by_cases hν : ν = T.axis
  · subst hν
    rw [torusPoint_axis, torusPoint_axis, h]
  · exact (T.torusPoint_transverse m t y ⟨ν, hν⟩).trans
      (T.torusPoint_transverse m t' y ⟨ν, hν⟩).symm
theorem torusPoint_add (m : SlabCount) (t s : ℝ) (y z : T.TransverseTorus) :
    T.torusPoint m (t + s) (y + z) = T.torusPoint m t y + T.torusPoint m s z := by
  funext ν
  by_cases hν : ν = T.axis
  · subst hν
    change T.torusPoint m (t + s) (y + z) T.axis =
      T.torusPoint m t y T.axis + T.torusPoint m s z T.axis
    rw [torusPoint_axis, torusPoint_axis, torusPoint_axis]
    rfl
  · change T.torusPoint m (t + s) (y + z) (⟨ν, hν⟩ : TransverseAxis T.axis).1 =
      T.torusPoint m t y (⟨ν, hν⟩ : TransverseAxis T.axis).1 +
        T.torusPoint m s z (⟨ν, hν⟩ : TransverseAxis T.axis).1
    rw [torusPoint_transverse, torusPoint_transverse, torusPoint_transverse]
    exact addCircleCast_add _ _ _
abbrev gridStepAt (m : SlabCount) (ν : Fin 4) : (T.torusPeriods m).GridPoint :=
  BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) (T.torusPeriods m).sideLengths ν
theorem gridStepAt_apply (m : SlabCount) (ν ν' : Fin 4) :
    ((T.gridStepAt m ν : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) ν' =
      ((D.mesh * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) ν' : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths ν')) :=
  rfl
theorem torusPoint_transverseVector (m : SlabCount) (ν : TransverseAxis T.axis) :
    T.torusPoint m 0 (T.transverseVector ν D.mesh) =
      (T.gridStepAt m ν.1 : (T.torusPeriods m).GridPoint) := by
  funext ν'
  rw [gridStepAt_apply]
  by_cases hν : ν' = T.axis
  · subst hν
    rw [torusPoint_axis, Pi.single_eq_of_ne ν.2.symm, mul_zero]
  · change T.torusPoint m 0 (T.transverseVector ν D.mesh) (⟨ν', hν⟩ : TransverseAxis T.axis).1 = _
    rw [torusPoint_transverse]
    by_cases h : (⟨ν', hν⟩ : TransverseAxis T.axis) = ν
    · subst h
      rw [transverseVector, Pi.single_eq_same, addCircleCast_coe, Pi.single_eq_same, mul_one]
    · have h' : ν' ≠ ν.1 := fun e => h (Subtype.ext e)
      rw [transverseVector, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', mul_zero]
      exact addCircleCast_coe _ 0
theorem torusPoint_mesh (m : SlabCount) :
    T.torusPoint m D.mesh 0 = (T.gridStepAt m T.axis : (T.torusPeriods m).GridPoint) := by
  funext ν'
  rw [gridStepAt_apply]
  by_cases hν : ν' = T.axis
  · subst hν
    rw [torusPoint_axis, Pi.single_eq_same, mul_one]
  · change T.torusPoint m D.mesh 0 (⟨ν', hν⟩ : TransverseAxis T.axis).1 = _
    rw [torusPoint_transverse, Pi.single_eq_of_ne hν, mul_zero]
    exact addCircleCast_coe _ 0
theorem coe_sliceTime_eq (m : SlabCount) {c c' : ℤ}
    (h : (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣ c' - c) :
    ((T.sliceTime c' : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((T.sliceTime c : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
  obtain ⟨z, hz⟩ := h
  refine QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨z, ?_⟩)
  have hc : (c' : ℝ) = c + (((m : ℕ) * T.ratioNat : ℕ) : ℝ) * z := by
    have : c' = c + (((m : ℕ) * T.ratioNat : ℕ) : ℤ) * z := by omega
    exact_mod_cast this
  rw [sideLengths_axis, zsmul_eq_mul, sliceTime, sliceTime, hc]
  ring
theorem torusPoint_mem (m : SlabCount) (i : ℤ) (y : T.TransverseSite) :
    T.torusPoint m (T.sliceTime i) (y : T.TransverseTorus) ∈ (T.torusPeriods m).gridSubgroup := by
  obtain ⟨i₀, hi₀⟩ := T.grid.origin_mem T.axis
  have hy : ∀ ν, ∃ z : ℤ, (y : T.TransverseTorus) ν =
      (((z : ℝ) * D.mesh : ℝ) : AddCircle (T.transverseSide ν)) := by
    intro ν
    obtain ⟨z, hz⟩ :=
      AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp y.2 ν (mem_univ ν))
    refine ⟨z, ?_⟩
    rw [← hz, ← zsmul_eq_mul]
    rfl
  choose z hz using hy
  refine ⟨fun ν => if h : ν = T.axis then i₀ + i else z ⟨ν, h⟩, ?_⟩
  funext ν
  by_cases hν : ν = T.axis
  · subst hν
    rw [torusPoint_axis]
    change _ = ((((if h : T.axis = T.axis then i₀ + i else z ⟨T.axis, h⟩ : ℤ) : ℝ) *
      D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis))
    rw [dif_pos rfl, sliceTime, hi₀]
    congr 1
    push_cast
    ring
  · change T.torusPoint m _ _ (⟨ν, hν⟩ : TransverseAxis T.axis).1 = _
    rw [torusPoint_transverse, hz, addCircleCast_coe]
    change _ = ((((if h : ν = T.axis then i₀ + i else z ⟨ν, h⟩ : ℤ) : ℝ) * D.mesh : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths ν))
    rw [dif_neg hν]
def gridSite (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    (T.torusPeriods m).GridPoint :=
  ⟨T.torusPoint m (T.sliceTime (i.cast : ℤ)) (y : T.TransverseTorus), T.torusPoint_mem m _ y⟩
theorem gridSite_add_transverseStep (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite)
    (ν : TransverseAxis T.axis) :
    T.gridSite m i (y + T.transverseStep ν) = T.gridSite m i y + T.gridStepAt m ν.1 := by
  refine Subtype.ext ?_
  change T.torusPoint m (T.sliceTime (i.cast : ℤ))
      ((y : T.TransverseTorus) + T.transverseVector ν D.mesh) =
    T.torusPoint m (T.sliceTime (i.cast : ℤ)) (y : T.TransverseTorus) + _
  have h := T.torusPoint_add m (T.sliceTime (i.cast : ℤ)) 0 (y : T.TransverseTorus)
    (T.transverseVector ν D.mesh)
  rw [add_zero, T.torusPoint_transverseVector] at h
  exact h
theorem gridSite_add_one (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    T.gridSite m (i + 1) y = T.gridSite m i y + T.gridStepAt m T.axis := by
  refine Subtype.ext ?_
  change T.torusPoint m (T.sliceTime ((i + 1).cast : ℤ)) (y : T.TransverseTorus) =
    T.torusPoint m (T.sliceTime (i.cast : ℤ)) (y : T.TransverseTorus) + _
  have h := T.torusPoint_add m (T.sliceTime (i.cast : ℤ)) D.mesh (y : T.TransverseTorus) 0
  rw [add_zero, T.torusPoint_mesh] at h
  refine Eq.trans (T.torusPoint_congr m ?_ _) h
  have hd : (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣ (i.cast + 1 : ℤ) - ((i + 1).cast : ℤ) := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
    simp
  have ht : T.sliceTime (i.cast : ℤ) + D.mesh = T.sliceTime ((i.cast : ℤ) + 1) := by
    simp only [sliceTime]
    push_cast
    ring
  rw [ht]
  exact (T.coe_sliceTime_eq m hd).symm
theorem isNeighbourStep_of_eq_add (m : SlabCount) {x x' : (T.torusPeriods m).GridPoint}
    {ν : Fin 4} (h : x' = x + T.gridStepAt m ν) : BoxTorus.IsNeighbourStep x x' ν 1 := by
  subst h
  exact ⟨Or.inl rfl, by simp [BoxTorus.translate, BoxTorus.gridStep]⟩
def sliceEdge (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (T.torusPeriods m).DirectedEdge where
  source := T.gridSite m i b.1.source
  target := T.gridSite m i b.1.target
  isNeighbour := ⟨(T.edgeAxis b).1, 1, T.isNeighbourStep_of_eq_add m (by
    rw [← gridSite_add_transverseStep, ← target_sub_source, add_sub_cancel])⟩
def axialEdge (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    (T.torusPeriods m).DirectedEdge where
  source := T.gridSite m i y
  target := T.gridSite m (i + 1) y
  isNeighbour := ⟨T.axis, 1, T.isNeighbourStep_of_eq_add m (T.gridSite_add_one m i y)⟩
def sliceFace (m : SlabCount) (i : T.SliceLabel m) (q : T.TransverseFace) :
    (T.torusPeriods m).Face :=
  ⟨T.gridSite m i q.corner, q.axis₁.1, q.axis₂.1, q.axis₁_lt_axis₂⟩
def axialFace (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (T.torusPeriods m).Face :=
  ⟨T.gridSite m i b.1.source, min T.axis (T.edgeAxis b).1, max T.axis (T.edgeAxis b).1,
    min_lt_max.mpr (T.edgeAxis b).2.symm⟩
def sliceField (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig) (i : T.SliceLabel m) :
    T.EdgeField :=
  fun b => BoxTorus.edgeVariable U (T.sliceEdge m i b)
def axialField (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig) (i : T.SliceLabel m) :
    T.SiteField :=
  fun y => BoxTorus.edgeVariable U (T.axialEdge m i y)
def IsInSlab (m : SlabCount) (k : ZMod (m : ℕ)) (p : (T.torusPeriods m).Face) : Prop :=
  ∀ x ∈ p.vertexSet, ∃ i ∈ T.slabSet m k, x ∈ T.sliceSet m i
def IsCrossingFace (m : SlabCount) (p : (T.torusPeriods m).Face) : Prop :=
  ∀ k, ¬ T.IsInSlab m k p
abbrev SlabConfig : Type :=
  (Fin T.ratioNat → T.EdgeField) × (Fin (T.ratioNat - 1) → T.SiteField)
def slabHaar : Measure T.SlabConfig :=
  (Measure.pi fun _ : Fin T.ratioNat => T.edgeHaar).prod
    (Measure.pi fun _ : Fin (T.ratioNat - 1) => T.siteHaar)
def slabRestriction (m : SlabCount) (k : ZMod (m : ℕ)) (U : (T.torusPeriods m).GaugeConfig) :
    T.SlabConfig :=
  (fun j => T.sliceField m U (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)),
    fun j => T.axialField m U (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)))
def slabReverse (η : T.SlabConfig) : T.SlabConfig :=
  (fun j => η.1 j.rev, fun j y => (η.2 j.rev y)⁻¹)
def reflectConj (Φ : T.SlabConfig → ℂ) (η : T.SlabConfig) : ℂ :=
  starRingEnd ℂ (Φ (T.slabReverse η))
def IsBoundedMeasurable (Φ : T.SlabConfig → ℂ) : Prop :=
  Measurable Φ ∧ ∃ C : ℝ, ∀ η, ‖Φ η‖ ≤ C
def axialHolonomy (ξ ξ' : T.EdgeField) (V : T.SiteField) (b : T.PositiveTransverseEdge) :
    Conventions.StandingParameters.gaugeGroup :=
  V b.1.source * ξ' b * (V b.1.target)⁻¹ * (ξ b)⁻¹
def slabFaceAction (j : Fin T.ratioNat) (q : T.TransverseFace) (η : T.SlabConfig) : ℝ :=
  T.faceAction q (η.1 j)
def slabAxialAction (j : Fin (T.ratioNat - 1)) (b : T.PositiveTransverseEdge)
    (η : T.SlabConfig) : ℂ :=
  1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (T.axialHolonomy (η.1 ⟨j, by have := j.2; omega⟩)
    (η.1 ⟨j + 1, by have := j.2; omega⟩) (η.2 j) b : Matrices.ComplexMatrix2)
def boltzmannFactor (D : ChessboardSetup) (u : Conventions.StandingParameters.gaugeGroup) : ℂ :=
  Complex.exp (-(D.β : ℂ) * (1 - (1 / 2) *
    Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)))
def slabProductIntegral (m : SlabCount) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ) : ℂ :=
  ∫ U, ∏ k : ZMod (m : ℕ), (Φ k (T.slabRestriction m k U) * ∏ b : T.PositiveTransverseEdge,
    boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
      (T.sliceField m U (T.slabSliceIndex m k 1)) (T.axialField m U (T.slabSliceIndex m k 0)) b))
    ∂(T.torusPeriods m).haarMeasure
def alternatingSlabIntegral (m : SlabCount) (_hm : Even (m : ℕ)) (Φ : T.SlabConfig → ℂ) : ℂ :=
  T.slabProductIntegral m fun k => if Even k.val then Φ else T.reflectConj Φ
def slabBoltzmann (m : SlabCount) (w : (T.torusPeriods m).Face → ℂ) (k : ZMod (m : ℕ))
    (η : T.SlabConfig) : ℂ :=
  (∏ j : Fin T.ratioNat, ∏ q : T.TransverseFace,
    Complex.exp ((w (T.sliceFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) q) - (D.β : ℂ)) *
      (T.slabFaceAction j q η : ℂ))) *
  ∏ j : Fin (T.ratioNat - 1), ∏ b : T.PositiveTransverseEdge,
    Complex.exp ((w (T.axialFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) b) - (D.β : ℂ)) *
      T.slabAxialAction j b η)
end TransferSetup
end ChessboardTori
end YangMills.Construction
end
