import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureOfAGridProof
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open Matrices Conventions
namespace ChessboardTori
namespace TransferSetup
open InfiniteLattice (AmbientSpace)
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem intCast_mul_coe_eq_iff {a : ℝ} (ha : a ≠ 0) (s n n' : ℤ) :
    (((n : ℝ) * a : ℝ) : AddCircle ((s : ℝ) * a)) = (((n' : ℝ) * a : ℝ) : AddCircle ((s : ℝ) * a)) ↔
      s ∣ n' - n := by
  rw [show ((((n : ℝ) * a : ℝ) : AddCircle ((s : ℝ) * a)) =
      (((n' : ℝ) * a : ℝ) : AddCircle ((s : ℝ) * a))) ↔
      ((n : ℝ) * a - (n' : ℝ) * a ∈ AddSubgroup.zmultiples ((s : ℝ) * a)) from
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    have h : ((z * s : ℤ) : ℝ) = ((n - n' : ℤ) : ℝ) := by
      apply mul_right_cancel₀ ha
      push_cast
      rw [zsmul_eq_mul] at hz
      linarith
    have h' : z * s = n - n' := by exact_mod_cast h
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    have h : (n' : ℝ) - n = s * z := by exact_mod_cast hz
    rw [zsmul_eq_mul]
    push_cast
    linear_combination a * h
theorem coe_mesh_mul_eq_iff (P : PeriodSubgroup D) (ν : Fin 4) (n n' : ℤ) :
    (((n : ℝ) * D.mesh : ℝ) : AddCircle (P.sideLengths ν)) =
        (((n' : ℝ) * D.mesh : ℝ) : AddCircle (P.sideLengths ν)) ↔
      P.mult ν ∣ n' - n :=
  intCast_mul_coe_eq_iff D.mesh_pos.ne' (P.mult ν) n n'
theorem mult_axis (m : SlabCount) :
    (T.torusPeriods m).mult T.axis = (((m : ℕ) * T.ratioNat : ℕ) : ℤ) := by
  change T.cellCounts m T.axis * T.grid.cellRatio = _
  rw [cellCounts, dif_pos rfl, ← T.natCast_ratioNat]
  push_cast
  ring
theorem exists_sliceTime_eq : ∃ i₀ : ℤ, ∀ i : ℤ, T.sliceTime i = ((i₀ + i : ℤ) : ℝ) * D.mesh := by
  obtain ⟨i₀, h⟩ := T.grid.origin_mem T.axis
  refine ⟨i₀, fun i => ?_⟩
  rw [sliceTime, h]
  push_cast
  ring
theorem coe_sliceTime_eq_iff (m : SlabCount) (c c' : ℤ) :
    ((T.sliceTime c : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) = (T.sliceTime c' : ℝ) ↔
      (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣ c' - c := by
  obtain ⟨i₀, h⟩ := T.exists_sliceTime_eq
  rw [h, h, coe_mesh_mul_eq_iff, mult_axis]
  have : i₀ + c' - (i₀ + c) = c' - c := by ring
  rw [this]
theorem dvd_cast_sub_iff_eq (m : SlabCount) (i i' : T.SliceLabel m) :
    (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣ (i'.cast : ℤ) - (i.cast : ℤ) ↔ i = i' := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp
theorem addCircleCast_injective {p q : ℝ} (h : p = q) : Function.Injective (addCircleCast h) := by
  subst h
  exact fun _ _ e => e
def transverseSiteOfInt (z : TransverseAxis T.axis → ℤ) : T.TransverseSite :=
  ⟨fun ν => (((z ν : ℝ) * D.mesh : ℝ) : AddCircle (T.transverseSide ν)),
    (AddSubgroup.mem_pi _).mpr fun ν _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨z ν, by
      rw [← zsmul_eq_mul]
      rfl⟩⟩
theorem gridSite_axis (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    ((T.gridSite m i y : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) T.axis =
      ((T.sliceTime (i.cast : ℤ) : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) :=
  T.torusPoint_axis m _ _
theorem gridSite_transverse (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite)
    (ν : TransverseAxis T.axis) :
    ((T.gridSite m i y : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) ν.1 =
      addCircleCast (T.transverseSide_eq_sideLengths m ν) ((y : T.TransverseTorus) ν) :=
  T.torusPoint_transverse m _ _ ν
theorem gridSite_inj (m : SlabCount) {i i' : T.SliceLabel m} {y y' : T.TransverseSite}
    (h : T.gridSite m i y = T.gridSite m i' y') : i = i' ∧ y = y' := by
  have hv := congrArg (fun x : (T.torusPeriods m).GridPoint => (x : (T.torusPeriods m).TorusSpace)) h
  constructor
  · have := congrFun hv T.axis
    simp only [gridSite_axis] at this
    exact (T.dvd_cast_sub_iff_eq m i i').mp ((T.coe_sliceTime_eq_iff m _ _).mp this)
  · refine Subtype.ext (funext fun ν => ?_)
    have := congrFun hv ν.1
    simp only [gridSite_transverse] at this
    exact addCircleCast_injective _ this
theorem gridSite_surjective (m : SlabCount) (x : (T.torusPeriods m).GridPoint) :
    ∃ i y, T.gridSite m i y = x := by
  obtain ⟨i₀, h₀⟩ := T.exists_sliceTime_eq
  obtain ⟨n, hn⟩ := x.2
  refine ⟨((n T.axis - i₀ : ℤ) : T.SliceLabel m), T.transverseSiteOfInt fun ν => n ν.1, ?_⟩
  refine Subtype.ext (funext fun ν => ?_)
  rw [hn]
  by_cases hν : ν = T.axis
  · subst hν
    rw [gridSite_axis, h₀]
    change _ = (((n T.axis : ℝ) * D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis))
    rw [coe_mesh_mul_eq_iff, mult_axis]
    obtain ⟨z, hz⟩ : (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣
        (n T.axis - i₀) - (((n T.axis - i₀ : ℤ) : T.SliceLabel m).cast : ℤ) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp
    exact ⟨z, by linarith⟩
  · have := T.gridSite_transverse m ((n T.axis - i₀ : ℤ) : T.SliceLabel m)
      (T.transverseSiteOfInt fun ν => n ν.1) ⟨ν, hν⟩
    refine this.trans ?_
    exact addCircleCast_coe _ _
theorem coe_mesh_ne_zero (m : SlabCount) (ν : Fin 4) :
    ((D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) ≠ 0 := by
  intro h
  have h1 : ((((1 : ℤ) : ℝ) * D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) =
      ((((0 : ℤ) : ℝ) * D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) := by
    simpa using h
  have h2 := (coe_mesh_mul_eq_iff (T.torusPeriods m) ν 1 0).mp h1
  have h3 := (T.torusPeriods m).four_le_mult ν
  have := Int.le_of_dvd (by norm_num) ((dvd_neg).mpr h2)
  simp at this
  omega
theorem gridStepAt_apply_self (m : SlabCount) (ν : Fin 4) :
    ((T.gridStepAt m ν : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) ν =
      ((D.mesh : ℝ) : AddCircle ((T.torusPeriods m).sideLengths ν)) := by
  rw [gridStepAt_apply]
  simp only [Pi.single_eq_same, mul_one]
theorem gridStepAt_apply_of_ne (m : SlabCount) {ν ν' : Fin 4} (h : ν' ≠ ν) :
    ((T.gridStepAt m ν : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) ν' = 0 := by
  rw [gridStepAt_apply, Pi.single_eq_of_ne h, mul_zero]
  rfl
theorem gridStepAt_injective (m : SlabCount) : Function.Injective (T.gridStepAt m) := by
  intro ν ν' h
  by_contra hne
  have := congrFun (congrArg Subtype.val h) ν
  rw [gridStepAt_apply_self, gridStepAt_apply_of_ne T m (Ne.symm (Ne.symm hne))] at this
  exact T.coe_mesh_ne_zero m ν this
theorem eq_add_gridStepAt_of_isNeighbourStep (m : SlabCount) {x x' : (T.torusPeriods m).GridPoint}
    {ν : Fin 4} (h : BoxTorus.IsNeighbourStep x x' ν 1) : x' = x + T.gridStepAt m ν := by
  refine Subtype.ext ?_
  have := h.2
  rw [one_mul] at this
  exact this
theorem transverseStep_injective : Function.Injective T.transverseStep := by
  intro ν ν' h
  let m : SlabCount := ⟨2, le_rfl⟩
  have h₁ := T.gridSite_add_transverseStep m 0 0 ν
  have h₂ := T.gridSite_add_transverseStep m 0 0 ν'
  rw [h, h₂] at h₁
  exact Subtype.ext (T.gridStepAt_injective m (add_left_cancel h₁).symm)
theorem forwardEdge_source_edgeAxis (b : T.PositiveTransverseEdge) :
    T.forwardEdge b.1.source (T.edgeAxis b) = b := by
  refine Subtype.ext (TransverseEdge.ext rfl ?_)
  have := T.target_sub_source b
  change b.1.source + T.transverseStep (T.edgeAxis b) = b.1.target
  rw [← this]
  abel
theorem edgeAxis_forwardEdge (y : T.TransverseSite) (ν : TransverseAxis T.axis) :
    T.edgeAxis (T.forwardEdge y ν) = ν := by
  have := T.target_sub_source (T.forwardEdge y ν)
  apply T.transverseStep_injective
  rw [← this]
  change y + T.transverseStep ν - y = _
  abel
theorem sliceEdge_isForward (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (T.sliceEdge m i b).IsForward :=
  ⟨(T.edgeAxis b).1, T.isNeighbourStep_of_eq_add m (by
    change T.gridSite m i b.1.target = T.gridSite m i b.1.source + _
    rw [← gridSite_add_transverseStep, ← target_sub_source, add_sub_cancel])⟩
theorem axialEdge_isForward (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    (T.axialEdge m i y).IsForward :=
  ⟨T.axis, T.isNeighbourStep_of_eq_add m (T.gridSite_add_one m i y)⟩
theorem sliceLabel_one_ne_zero (m : SlabCount) : (1 : T.SliceLabel m) ≠ 0 := by
  have hr := T.two_le_ratioNat
  have hm := m.2
  have : Fact (1 < (m : ℕ) * T.ratioNat) := ⟨by nlinarith⟩
  exact one_ne_zero
theorem edgeOfSlices_injective (m : SlabCount) : Function.Injective (T.edgeOfSlices m) := by
  have hstep : ∀ (i : T.SliceLabel m), i + 1 ≠ i := fun i h =>
    T.sliceLabel_one_ne_zero m (by simpa using h)
  rintro (⟨i, b⟩ | ⟨i, y⟩) (⟨i', b'⟩ | ⟨i', y'⟩) h
  · have ht := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.source h)
    have hh := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.target h)
    obtain rfl := ht.1
    have : b = b' := Subtype.ext (TransverseEdge.ext ht.2 hh.2)
    rw [this]
  · exfalso
    have ht := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.source h)
    have hh := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.target h)
    exact hstep i' (hh.1.symm.trans ht.1)
  · exfalso
    have ht := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.source h)
    have hh := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.target h)
    exact hstep i (hh.1.trans ht.1.symm)
  · have ht := T.gridSite_inj m (congrArg BoxTorus.DirectedEdge.source h)
    obtain rfl := ht.1
    rw [ht.2]
theorem edgeFrom_transverse (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite)
    (ν : TransverseAxis T.axis) :
    BoxTorus.edgeFrom (T.gridSite m i y) ν.1 = T.sliceEdge m i (T.forwardEdge y ν) :=
  BoxTorus.DirectedEdge.ext rfl (T.gridSite_add_transverseStep m i y ν).symm
theorem edgeFrom_axis (m : SlabCount) (i : T.SliceLabel m) (y : T.TransverseSite) :
    BoxTorus.edgeFrom (T.gridSite m i y) T.axis = T.axialEdge m i y :=
  BoxTorus.DirectedEdge.ext rfl (T.gridSite_add_one m i y).symm
theorem range_edgeOfSlices (m : SlabCount) : range (T.edgeOfSlices m) = {l | l.IsForward} := by
  ext l
  constructor
  · rintro ⟨⟨i, b⟩ | ⟨i, y⟩, rfl⟩
    · exact T.sliceEdge_isForward m i b
    · exact T.axialEdge_isForward m i y
  · rintro ⟨ν, hν⟩
    have hh := T.eq_add_gridStepAt_of_isNeighbourStep m hν
    obtain ⟨i, y, hy⟩ := T.gridSite_surjective m l.source
    have hl : l = BoxTorus.edgeFrom (T.gridSite m i y) ν :=
      BoxTorus.DirectedEdge.ext hy.symm (by rw [hh, hy]; rfl)
    by_cases h : ν = T.axis
    · subst h
      exact ⟨.inr (i, y), by rw [hl, edgeFrom_axis]; rfl⟩
    · refine ⟨.inl (i, T.forwardEdge y ⟨ν, h⟩), ?_⟩
      rw [hl]
      exact (T.edgeFrom_transverse m i y ⟨ν, h⟩).symm
def forwardEdgeEquiv (m : SlabCount) :
    (T.SliceLabel m × T.PositiveTransverseEdge) ⊕ (T.SliceLabel m × T.TransverseSite) ≃
      (T.torusPeriods m).ForwardEdge :=
  Equiv.ofBijective
    (fun c => ⟨T.edgeOfSlices m c, by
      have : T.edgeOfSlices m c ∈ {l | l.IsForward} := by
        rw [← range_edgeOfSlices]
        exact mem_range_self c
      exact this⟩)
    ⟨fun _ _ h => T.edgeOfSlices_injective m (congrArg Subtype.val h), fun l => by
      have : l.1 ∈ range (T.edgeOfSlices m) := by
        rw [range_edgeOfSlices]
        exact l.2
      obtain ⟨c, hc⟩ := this
      exact ⟨c, Subtype.ext hc⟩⟩
theorem sliceField_apply (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    T.sliceField m U i b = U (T.forwardEdgeEquiv m (.inl (i, b))) :=
  dif_pos (T.sliceEdge_isForward m i b)
theorem axialField_apply (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (y : T.TransverseSite) :
    T.axialField m U i y = U (T.forwardEdgeEquiv m (.inr (i, y))) :=
  dif_pos (T.axialEdge_isForward m i y)
theorem faceOfSlices_bijective (m : SlabCount) :
    Function.Bijective (T.faceOfSlices m) := by
  constructor
  · rintro (⟨i, q⟩ | ⟨i, b⟩) (⟨i', q'⟩ | ⟨i', b'⟩) h
    · have hb := T.gridSite_inj m (congrArg BoxTorus.Face.corner h)
      have h₁ : q.axis₁.1 = q'.axis₁.1 := congrArg BoxTorus.Face.dir₁ h
      have h₂ : q.axis₂.1 = q'.axis₂.1 := congrArg BoxTorus.Face.dir₂ h
      obtain rfl := hb.1
      have : q = q' := TransverseFace.ext hb.2 (Subtype.ext h₁) (Subtype.ext h₂)
      rw [this]
    · exfalso
      have h₁ : q.axis₁.1 = min T.axis (T.edgeAxis b').1 :=
        congrArg BoxTorus.Face.dir₁ h
      have h₂ : q.axis₂.1 = max T.axis (T.edgeAxis b').1 :=
        congrArg BoxTorus.Face.dir₂ h
      rcases le_total T.axis (T.edgeAxis b').1 with hle | hle
      · exact q.axis₁.2 (by rw [h₁, min_eq_left hle])
      · exact q.axis₂.2 (by rw [h₂, max_eq_left hle])
    · exfalso
      have h₁ : min T.axis (T.edgeAxis b).1 = q'.axis₁.1 :=
        congrArg BoxTorus.Face.dir₁ h
      have h₂ : max T.axis (T.edgeAxis b).1 = q'.axis₂.1 :=
        congrArg BoxTorus.Face.dir₂ h
      rcases le_total T.axis (T.edgeAxis b).1 with hle | hle
      · exact q'.axis₁.2 (by rw [← h₁, min_eq_left hle])
      · exact q'.axis₂.2 (by rw [← h₂, max_eq_left hle])
    · have hb := T.gridSite_inj m (congrArg BoxTorus.Face.corner h)
      have h₁ : min T.axis (T.edgeAxis b).1 = min T.axis (T.edgeAxis b').1 :=
        congrArg BoxTorus.Face.dir₁ h
      have h₂ : max T.axis (T.edgeAxis b).1 = max T.axis (T.edgeAxis b').1 :=
        congrArg BoxTorus.Face.dir₂ h
      obtain rfl := hb.1
      have hd : T.edgeAxis b = T.edgeAxis b' := by
        apply Subtype.ext
        have hne := (T.edgeAxis b).2
        have hne' := (T.edgeAxis b').2
        rcases le_total T.axis (T.edgeAxis b).1 with hle | hle <;>
          rcases le_total T.axis (T.edgeAxis b').1 with hle' | hle'
        · rw [max_eq_right hle, max_eq_right hle'] at h₂
          exact h₂
        · rw [min_eq_left hle, min_eq_right hle'] at h₁
          exact absurd h₁.symm hne'
        · rw [min_eq_right hle, min_eq_left hle'] at h₁
          exact absurd h₁ hne
        · rw [min_eq_right hle, min_eq_right hle'] at h₁
          exact h₁
      have : b = b' := by
        rw [← T.forwardEdge_source_edgeAxis b, ← T.forwardEdge_source_edgeAxis b', hd, hb.2]
      rw [this]
  · rintro ⟨x, ν, ρ, hνρ⟩
    obtain ⟨i, y, rfl⟩ := T.gridSite_surjective m x
    by_cases h₁ : ν = T.axis
    · subst h₁
      have hρ : ρ ≠ T.axis := hνρ.ne'
      refine ⟨.inr (i, T.forwardEdge y ⟨ρ, hρ⟩), ?_⟩
      have hd : T.edgeAxis (T.forwardEdge y ⟨ρ, hρ⟩) = ⟨ρ, hρ⟩ :=
        T.edgeAxis_forwardEdge _ _
      refine BoxTorus.Face.ext rfl ?_ ?_
      · change min T.axis (T.edgeAxis _).1 = _
        rw [hd, min_eq_left hνρ.le]
      · change max T.axis (T.edgeAxis _).1 = _
        rw [hd, max_eq_right hνρ.le]
    · by_cases h₂ : ρ = T.axis
      · subst h₂
        refine ⟨.inr (i, T.forwardEdge y ⟨ν, h₁⟩), ?_⟩
        have hd : T.edgeAxis (T.forwardEdge y ⟨ν, h₁⟩) = ⟨ν, h₁⟩ :=
          T.edgeAxis_forwardEdge _ _
        refine BoxTorus.Face.ext rfl ?_ ?_
        · change min T.axis (T.edgeAxis _).1 = _
          rw [hd, min_eq_right hνρ.le]
        · change max T.axis (T.edgeAxis _).1 = _
          rw [hd, max_eq_left hνρ.le]
      · exact ⟨.inl (i, ⟨y, ⟨ν, h₁⟩, ⟨ρ, h₂⟩, hνρ⟩), rfl⟩
theorem faceHolonomy_sliceFace (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (q : T.TransverseFace) :
    BoxTorus.faceHolonomy U (T.sliceFace m i q) =
      T.faceHolonomy (T.sliceField m U i) q := by
  simp only [BoxTorus.faceHolonomy, sliceFace, faceHolonomy]
  have h₁ := T.gridSite_add_transverseStep m i q.corner q.axis₁
  have h₂ := T.gridSite_add_transverseStep m i q.corner q.axis₂
  change _ = _
  erw [← h₁, ← h₂]
  rw [edgeFrom_transverse T m i _ q.axis₁, edgeFrom_transverse T m i _ q.axis₂,
    edgeFrom_transverse T m i _ q.axis₂, edgeFrom_transverse T m i _ q.axis₁]
  rfl
theorem fullTrace_inv (u : StandingParameters.gaugeGroup) :
    ComplexMatrix2.fullTrace ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (u : ComplexMatrix2) := by
  have hdet : (u : ComplexMatrix2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp u.2).2
  have hmul : (u : ComplexMatrix2) * ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    rfl
  have hinv : ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) = (u : ComplexMatrix2)⁻¹ :=
    (Matrix.inv_eq_right_inv hmul).symm
  rw [hinv, Matrix.inv_def, hdet]
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ring
theorem fullTrace_inv_eq_conj (u : StandingParameters.gaugeGroup) :
    ComplexMatrix2.fullTrace ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) =
      starRingEnd ℂ (ComplexMatrix2.fullTrace (u : ComplexMatrix2)) := by
  have : ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) = star (u : ComplexMatrix2) := rfl
  rw [this]
  simp [Matrix.trace_fin_two, Matrix.star_eq_conjTranspose]
theorem gaugeGroupTraceFacts : GaugeGroupTraceFacts := by
  intro u
  have h := (fullTrace_inv u).symm.trans (fullTrace_inv_eq_conj u)
  refine ⟨?_, ?_, fullTrace_inv u⟩
  · exact Complex.conj_eq_iff_im.mp h.symm
  · have hb : ∀ i j, ‖(u : ComplexMatrix2) i j‖ ≤ 1 := fun i j => by
      simpa using entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup u.2) i j
    calc ‖ComplexMatrix2.fullTrace (u : ComplexMatrix2)‖
          = ‖(u : ComplexMatrix2) 0 0 + (u : ComplexMatrix2) 1 1‖ := by
          rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
      _ ≤ ‖(u : ComplexMatrix2) 0 0‖ + ‖(u : ComplexMatrix2) 1 1‖ := norm_add_le _ _
      _ ≤ 2 := by linarith [hb 0 0, hb 1 1]
theorem faceHolonomy_axialFace (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    BoxTorus.faceHolonomy U (T.axialFace m i b) =
        T.axialHolonomy (T.sliceField m U i) (T.sliceField m U (i + 1))
          (T.axialField m U i) b ∨
      BoxTorus.faceHolonomy U (T.axialFace m i b) =
        (T.axialHolonomy (T.sliceField m U i) (T.sliceField m U (i + 1))
          (T.axialField m U i) b)⁻¹ := by
  have hhead : b.1.source + T.transverseStep (T.edgeAxis b) = b.1.target := by
    rw [← T.target_sub_source b]
    abel
  have h₁ := T.gridSite_add_transverseStep m i b.1.source (T.edgeAxis b)
  have h₂ := T.gridSite_add_one m i b.1.source
  rw [hhead] at h₁
  have e₁ : ∀ j, BoxTorus.edgeFrom (T.gridSite m j b.1.source) (T.edgeAxis b).1 =
      T.sliceEdge m j b := fun j => by
    rw [edgeFrom_transverse, forwardEdge_source_edgeAxis]
  rcases lt_or_gt_of_ne (T.edgeAxis b).2 with h | h
  · right
    simp only [BoxTorus.faceHolonomy, axialFace, axialHolonomy]
    rw [min_eq_right h.le, max_eq_left h.le, ← h₁, ← h₂, edgeFrom_axis, edgeFrom_axis, e₁, e₁]
    change T.sliceField m U i b * T.axialField m U i b.1.target *
      (T.sliceField m U (i + 1) b)⁻¹ * (T.axialField m U i b.1.source)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  · left
    simp only [BoxTorus.faceHolonomy, axialFace, axialHolonomy]
    rw [min_eq_left h.le, max_eq_right h.le, ← h₁, ← h₂, edgeFrom_axis, edgeFrom_axis, e₁, e₁]
    rfl
theorem faceEnergy_axialFace (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (((T.torusPeriods m).faceEnergy U (T.axialFace m i b) : ℝ) : ℂ) =
      1 - (1 / 2) * ComplexMatrix2.fullTrace (T.axialHolonomy (T.sliceField m U i)
        (T.sliceField m U (i + 1)) (T.axialField m U i) b : ComplexMatrix2) := by
  have hre : ∀ u : StandingParameters.gaugeGroup,
      (((ComplexMatrix2.fullTrace (u : ComplexMatrix2)).re : ℝ) : ℂ) =
        ComplexMatrix2.fullTrace (u : ComplexMatrix2) :=
    fun u => Complex.ext rfl (by simpa using ((gaugeGroupTraceFacts u).1).symm)
  change ((1 - (1 / 2) * (ComplexMatrix2.fullTrace (BoxTorus.faceHolonomy U
    (T.axialFace m i b) : ComplexMatrix2)).re : ℝ) : ℂ) = _
  push_cast
  rw [hre]
  rcases T.faceHolonomy_axialFace m U i b with h | h
  · rw [h]
  · rw [h, fullTrace_inv]
theorem faceEnergy_sliceFace (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (i : T.SliceLabel m) (q : T.TransverseFace) :
    (T.torusPeriods m).faceEnergy U (T.sliceFace m i q) =
      T.faceAction q (T.sliceField m U i) := by
  change 1 - (1 / 2) * (ComplexMatrix2.fullTrace (BoxTorus.faceHolonomy U
    (T.sliceFace m i q) : ComplexMatrix2)).re = _
  rw [faceHolonomy_sliceFace]
  rfl
theorem torusPoint_zero_transverseVector (m : SlabCount) (ν : TransverseAxis T.axis) (s : ℝ) :
    T.torusPoint m 0 (T.transverseVector ν s) =
      (T.torusPeriods m).proj (s • BoxTorus.basisVector ν.1) := by
  funext ν'
  by_cases hν : ν' = T.axis
  · subst hν
    rw [torusPoint_axis]
    change _ = ((s * (Pi.single ν.1 (1 : ℝ) : Fin 4 → ℝ) T.axis : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths T.axis))
    rw [Pi.single_eq_of_ne ν.2.symm, mul_zero]
  · change T.torusPoint m 0 (T.transverseVector ν s) (⟨ν', hν⟩ : TransverseAxis T.axis).1 = _
    rw [torusPoint_transverse]
    change _ = ((s * (Pi.single ν.1 (1 : ℝ) : Fin 4 → ℝ) ν' : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths ν'))
    by_cases h : (⟨ν', hν⟩ : TransverseAxis T.axis) = ν
    · subst h
      rw [transverseVector, Pi.single_eq_same, addCircleCast_coe, Pi.single_eq_same, mul_one]
    · have h' : ν' ≠ ν.1 := fun e => h (Subtype.ext e)
      rw [transverseVector, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', mul_zero]
      exact addCircleCast_coe _ 0
theorem torusPoint_zero_right (m : SlabCount) (s : ℝ) :
    T.torusPoint m s 0 = (T.torusPeriods m).proj (s • BoxTorus.basisVector T.axis) := by
  funext ν'
  by_cases hν : ν' = T.axis
  · subst hν
    rw [torusPoint_axis]
    change _ = ((s * (Pi.single T.axis (1 : ℝ) : Fin 4 → ℝ) T.axis : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths T.axis))
    rw [Pi.single_eq_same, mul_one]
  · change T.torusPoint m s 0 (⟨ν', hν⟩ : TransverseAxis T.axis).1 = _
    rw [torusPoint_transverse]
    change _ = ((s * (Pi.single T.axis (1 : ℝ) : Fin 4 → ℝ) ν' : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths ν'))
    rw [Pi.single_eq_of_ne hν, mul_zero]
    exact addCircleCast_coe _ 0
theorem faceCenter_sliceFace (m : SlabCount) (i : T.SliceLabel m) (q : T.TransverseFace) :
    (T.torusPeriods m).faceCenter (T.sliceFace m i q) =
      T.torusPoint m (T.sliceTime (i.cast : ℤ)) (T.faceCentre q) := by
  have h := T.torusPoint_add m (T.sliceTime (i.cast : ℤ)) 0 (q.corner : T.TransverseTorus)
    (T.transverseVector q.axis₁ (D.mesh / 2) + T.transverseVector q.axis₂ (D.mesh / 2))
  have h' := T.torusPoint_add m 0 0 (T.transverseVector q.axis₁ (D.mesh / 2))
    (T.transverseVector q.axis₂ (D.mesh / 2))
  rw [add_zero] at h h'
  rw [faceCentre, h, h', torusPoint_zero_transverseVector, torusPoint_zero_transverseVector,
    ← map_add, ← smul_add]
  rfl
theorem faceCenter_axialFace (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (T.torusPeriods m).faceCenter (T.axialFace m i b) =
      T.torusPoint m (T.sliceTime (i.cast : ℤ) + D.mesh / 2) (T.edgeMidpoint b) := by
  have h := T.torusPoint_add m (T.sliceTime (i.cast : ℤ)) (D.mesh / 2) (b.1.source : T.TransverseTorus)
    (T.transverseVector (T.edgeAxis b) (D.mesh / 2))
  have h' := T.torusPoint_add m (D.mesh / 2) 0 0 (T.transverseVector (T.edgeAxis b) (D.mesh / 2))
  rw [add_zero, zero_add] at h'
  have hsum : BoxTorus.basisVector (min T.axis (T.edgeAxis b).1) +
      BoxTorus.basisVector (max T.axis (T.edgeAxis b).1) =
      BoxTorus.basisVector T.axis + BoxTorus.basisVector (T.edgeAxis b).1 := by
    rcases le_total T.axis (T.edgeAxis b).1 with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle, add_comm]
  rw [edgeMidpoint, h, h', torusPoint_zero_right, torusPoint_zero_transverseVector, ← map_add,
    ← smul_add, ← hsum]
  rfl
theorem slabSliceIndex_eq_of_intCast (m : SlabCount) {c : ℤ} {k : ZMod (m : ℕ)}
    (hc : (c : ZMod (m : ℕ)) = k) (j : ℤ) :
    T.slabSliceIndex m k j = ((c * (T.ratioNat : ℤ) + j : ℤ) : T.SliceLabel m) := by
  have h : ((m : ℕ) : ℤ) ∣ c - (k.cast : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp [hc]
  obtain ⟨z, hz⟩ := h
  rw [slabSliceIndex, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨z, ?_⟩
  push_cast
  linear_combination (T.ratioNat : ℤ) * hz
theorem slabSliceIndex_add_one (m : SlabCount) (k : ZMod (m : ℕ)) (j : ℤ) :
    T.slabSliceIndex m k (j + 1) = T.slabSliceIndex m k j + 1 := by
  simp only [slabSliceIndex]
  push_cast
  ring
theorem slabSliceIndex_succ_zero (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.slabSliceIndex m (k + 1) 0 = T.slabSliceIndex m k (T.ratioNat : ℤ) := by
  rw [T.slabSliceIndex_eq_of_intCast m (c := (k.cast : ℤ) + 1) (by simp) 0, slabSliceIndex]
  push_cast
  ring
def sliceInSlab (m : SlabCount) (p : ZMod (m : ℕ) × Fin T.ratioNat) : T.SliceLabel m :=
  T.slabSliceIndex m p.1 (((p.2 : ℕ) : ℤ) + 1)
theorem sliceInSlab_injective (m : SlabCount) : Function.Injective (T.sliceInSlab m) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  have hkv : (k.cast : ℤ) = (k.val : ℤ) := (ZMod.natCast_val k).symm
  have hkv' : (k'.cast : ℤ) = (k'.val : ℤ) := (ZMod.natCast_val k').symm
  have hlt := ZMod.val_lt k
  have hlt' := ZMod.val_lt k'
  have hj := j.2
  have hj' := j'.2
  simp only [sliceInSlab, slabSliceIndex, hkv, hkv'] at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hA : k.val * T.ratioNat + j < (m : ℕ) * T.ratioNat := by nlinarith
  have hA' : k'.val * T.ratioNat + j' < (m : ℕ) * T.ratioNat := by nlinarith
  have h0 : ((k'.val : ℤ) * (T.ratioNat : ℤ) + (((j' : ℕ) : ℤ) + 1)) -
      ((k.val : ℤ) * (T.ratioNat : ℤ) + (((j : ℕ) : ℤ) + 1)) = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    rw [abs_lt]
    push_cast
    have h1 : ((k.val * T.ratioNat + j : ℕ) : ℤ) < (((m : ℕ) * T.ratioNat : ℕ) : ℤ) := by
      exact_mod_cast hA
    have h2 : ((k'.val * T.ratioNat + j' : ℕ) : ℤ) < (((m : ℕ) * T.ratioNat : ℕ) : ℤ) := by
      exact_mod_cast hA'
    push_cast at h1 h2
    constructor
    · nlinarith [Nat.zero_le (k'.val * T.ratioNat + j'),
        (by positivity : (0 : ℤ) ≤ (k'.val : ℤ) * (T.ratioNat : ℤ) + ((j' : ℕ) : ℤ))]
    · nlinarith [(by positivity : (0 : ℤ) ≤ (k.val : ℤ) * (T.ratioNat : ℤ) + ((j : ℕ) : ℤ))]
  have hE : k.val * T.ratioNat + j = k'.val * T.ratioNat + j' := by
    have : (k.val : ℤ) * (T.ratioNat : ℤ) + ((j : ℕ) : ℤ) =
        (k'.val : ℤ) * (T.ratioNat : ℤ) + ((j' : ℕ) : ℤ) := by
      linarith
    exact_mod_cast this
  have hv : k.val = k'.val := by
    rcases lt_trichotomy k.val k'.val with hl | hl | hl
    · exfalso
      nlinarith
    · exact hl
    · exfalso
      nlinarith
  have hk : k = k' := ZMod.val_injective _ hv
  subst hk
  have : (j : ℕ) = j' := by
    have := Nat.add_left_cancel hE
    exact this
  exact Prod.ext rfl (Fin.ext this)
theorem sliceInSlab_bijective (m : SlabCount) : Function.Bijective (T.sliceInSlab m) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨T.sliceInSlab_injective m, ?_⟩
  simp [ZMod.card]
theorem mem_slabSet_iff (m : SlabCount) (k : ZMod (m : ℕ)) (i : T.SliceLabel m) :
    i ∈ T.slabSet m k ↔ ∃ j : Fin T.ratioNat, i = T.sliceInSlab m (k, j) := by
  constructor
  · rintro ⟨j, h₁, h₂, rfl⟩
    refine ⟨⟨(j - 1).toNat, by omega⟩, ?_⟩
    simp only [sliceInSlab]
    congr 1
    omega
  · rintro ⟨j, rfl⟩
    exact ⟨((j : ℕ) : ℤ) + 1, by omega, by have := j.2; omega, rfl⟩
theorem sliceInSlab_mem_slabSet_iff (m : SlabCount) (k k' : ZMod (m : ℕ)) (j : Fin T.ratioNat) :
    T.sliceInSlab m (k', j) ∈ T.slabSet m k ↔ k = k' := by
  rw [mem_slabSet_iff]
  constructor
  · rintro ⟨j', h⟩
    exact (congrArg Prod.fst (T.sliceInSlab_injective m h)).symm
  · rintro rfl
    exact ⟨j, rfl⟩
theorem slabSet_unique (m : SlabCount) {k k' : ZMod (m : ℕ)} {i : T.SliceLabel m}
    (h : i ∈ T.slabSet m k) (h' : i ∈ T.slabSet m k') : k = k' := by
  obtain ⟨j, rfl⟩ := (T.mem_slabSet_iff m k i).mp h
  exact (T.sliceInSlab_mem_slabSet_iff m k' k j).mp h' |>.symm
theorem exists_mem_slabSet (m : SlabCount) (i : T.SliceLabel m) : ∃ k, i ∈ T.slabSet m k := by
  obtain ⟨⟨k, j⟩, rfl⟩ := (T.sliceInSlab_bijective m).2 i
  exact ⟨k, (T.sliceInSlab_mem_slabSet_iff m k k j).mpr rfl⟩
theorem coe_mul_eq_iff_of_eq_period {p : ℝ} {a : ℝ} (ha : a ≠ 0) {s : ℤ} (hp : p = (s : ℝ) * a)
    (n n' : ℤ) :
    (((n : ℝ) * a : ℝ) : AddCircle p) = (((n' : ℝ) * a : ℝ) : AddCircle p) ↔ s ∣ n' - n := by
  subst hp
  exact intCast_mul_coe_eq_iff ha s n n'
theorem period_eq_mult_mul_mesh (m : SlabCount) :
    ((m : ℕ) : ℝ) * T.grid.cellSide = (((((m : ℕ) * T.ratioNat : ℕ) : ℤ)) : ℝ) * D.mesh := by
  rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
  push_cast
  ring
theorem sliceTimesAndSlabs (m : SlabCount) : T.SliceTimesAndSlabs m := by
  obtain ⟨i₀, h₀⟩ := T.exists_sliceTime_eq
  have hr : ((T.ratioNat : ℝ)) * D.mesh = T.grid.cellSide := by
    rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
    push_cast
    ring
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨i₀ + i, by rw [h₀, zsmul_eq_mul]⟩
    · intro hx
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      refine ⟨z - i₀, ?_⟩
      rw [h₀, zsmul_eq_mul]
      congr 1
      push_cast
      ring
  · intro i
    simp only [sliceTime]
    rw [← hr]
    push_cast
    ring
  · intro i _
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨i₀ + (i.cast : ℤ), ?_⟩
    rw [sliceTimeClass, h₀, ← zsmul_eq_mul]
    rfl
  · intro i _ i' _ h
    rw [sliceTimeClass, sliceTimeClass, h₀, h₀,
      coe_mul_eq_iff_of_eq_period D.mesh_pos.ne' (T.period_eq_mult_mul_mesh m)] at h
    refine (T.dvd_cast_sub_iff_eq m i i').mp ?_
    have : i₀ + (i'.cast : ℤ) - (i₀ + (i.cast : ℤ)) = (i'.cast : ℤ) - (i.cast : ℤ) := by ring
    rwa [this] at h
  · intro x hx
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    refine ⟨((z - i₀ : ℤ) : T.SliceLabel m), mem_univ _, ?_⟩
    have hz : z • (((D.mesh : ℝ)) : AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide)) =
        (((z : ℝ) * D.mesh : ℝ) : AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide)) := by
      rw [← zsmul_eq_mul]
      rfl
    rw [hz, sliceTimeClass, h₀,
      coe_mul_eq_iff_of_eq_period D.mesh_pos.ne' (T.period_eq_mult_mul_mesh m)]
    obtain ⟨w, hw⟩ : (((m : ℕ) * T.ratioNat : ℕ) : ℤ) ∣
        (z - i₀) - (((z - i₀ : ℤ) : T.SliceLabel m).cast : ℤ) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp
    exact ⟨w, by linarith⟩
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · ext x
      simp only [ReflectionGrid.wall, sliceTime, mem_ofPred_eq]
      rw [← hr]
      push_cast
      constructor <;> intro h <;> rw [h] <;> ring
    · linarith [D.mesh_pos]
    · simp only [sliceTime]
      push_cast
      linarith [D.mesh_pos]
  · intro i
    obtain ⟨k, hk⟩ := T.exists_mem_slabSet m i
    exact ⟨k, hk, fun k' hk' => T.slabSet_unique m hk' hk⟩
theorem facesOfSlices (m : SlabCount) : T.FacesOfSlices m :=
  ⟨T.faceOfSlices_bijective m, fun i q => ⟨fun U => T.faceEnergy_sliceFace m U i q,
    T.faceCenter_sliceFace m i q⟩, fun i b => ⟨T.faceCenter_axialFace m i b,
      fun U => T.faceEnergy_axialFace m U i b⟩⟩
theorem gridSite_mem_sliceSet_iff (m : SlabCount) (i i' : T.SliceLabel m) (y : T.TransverseSite) :
    T.gridSite m i y ∈ T.sliceSet m i' ↔ i = i' := by
  change ((T.gridSite m i y : (T.torusPeriods m).GridPoint) : (T.torusPeriods m).TorusSpace) T.axis = _ ↔ _
  rw [gridSite_axis, coe_sliceTime_eq_iff, dvd_cast_sub_iff_eq]
theorem exists_slice_gridSite_iff (m : SlabCount) (k : ZMod (m : ℕ)) (i : T.SliceLabel m)
    (y : T.TransverseSite) :
    (∃ i' ∈ T.slabSet m k, T.gridSite m i y ∈ T.sliceSet m i') ↔ i ∈ T.slabSet m k := by
  constructor
  · rintro ⟨i', h, hs⟩
    rw [gridSite_mem_sliceSet_iff] at hs
    rwa [hs]
  · intro h
    exact ⟨i, h, (T.gridSite_mem_sliceSet_iff m i i y).mpr rfl⟩
theorem isInSlab_sliceFace (m : SlabCount) (k : ZMod (m : ℕ)) (i : T.SliceLabel m)
    (q : T.TransverseFace) : T.IsInSlab m k (T.sliceFace m i q) ↔ i ∈ T.slabSet m k := by
  constructor
  · intro h
    exact (T.exists_slice_gridSite_iff m k i q.corner).mp (h _ (Or.inl rfl))
  · intro h x hx
    have hy : ∃ y, x = T.gridSite m i y := by
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, (T.gridSite_add_transverseStep m i q.corner q.axis₁).symm⟩
      · refine ⟨q.corner + T.transverseStep q.axis₁ + T.transverseStep q.axis₂, ?_⟩
        rw [gridSite_add_transverseStep, gridSite_add_transverseStep]
        rfl
      · exact ⟨_, (T.gridSite_add_transverseStep m i q.corner q.axis₂).symm⟩
    obtain ⟨y, rfl⟩ := hy
    exact (T.exists_slice_gridSite_iff m k i y).mpr h
theorem axialFace_vertexSet (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (∀ x ∈ (T.axialFace m i b).vertexSet, ∃ y, x = T.gridSite m i y ∨ x = T.gridSite m (i + 1) y) ∧
      T.gridSite m i b.1.source ∈ (T.axialFace m i b).vertexSet ∧
      T.gridSite m (i + 1) b.1.source ∈ (T.axialFace m i b).vertexSet := by
  have hhead : b.1.source + T.transverseStep (T.edgeAxis b) = b.1.target := by
    rw [← T.target_sub_source b]
    abel
  have h₁ := T.gridSite_add_transverseStep m i b.1.source (T.edgeAxis b)
  have h₁' := T.gridSite_add_transverseStep m (i + 1) b.1.source (T.edgeAxis b)
  have h₂ := T.gridSite_add_one m i b.1.source
  have h₂' := T.gridSite_add_one m i b.1.target
  rw [hhead] at h₁ h₁'
  rcases le_total T.axis (T.edgeAxis b).1 with hle | hle
  · have e : (T.axialFace m i b).vertexSet =
        {T.gridSite m i b.1.source, T.gridSite m (i + 1) b.1.source, T.gridSite m (i + 1) b.1.target,
          T.gridSite m i b.1.target} := by
      simp only [BoxTorus.Face.vertexSet, axialFace]
      rw [min_eq_left hle, max_eq_right hle, ← h₂, ← h₁', ← h₁]
    rw [e]
    refine ⟨?_, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    rintro x (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl⟩
    · exact ⟨_, Or.inr rfl⟩
    · exact ⟨_, Or.inr rfl⟩
    · exact ⟨_, Or.inl rfl⟩
  · have e : (T.axialFace m i b).vertexSet =
        {T.gridSite m i b.1.source, T.gridSite m i b.1.target, T.gridSite m (i + 1) b.1.target,
          T.gridSite m (i + 1) b.1.source} := by
      simp only [BoxTorus.Face.vertexSet, axialFace]
      rw [min_eq_right hle, max_eq_left hle, ← h₂, ← h₁, ← h₂']
    rw [e]
    refine ⟨?_, Or.inl rfl, Or.inr (Or.inr (Or.inr rfl))⟩
    rintro x (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl⟩
    · exact ⟨_, Or.inl rfl⟩
    · exact ⟨_, Or.inr rfl⟩
    · exact ⟨_, Or.inr rfl⟩
theorem isInSlab_axialFace (m : SlabCount) (k : ZMod (m : ℕ)) (i : T.SliceLabel m)
    (b : T.PositiveTransverseEdge) :
    T.IsInSlab m k (T.axialFace m i b) ↔ i ∈ T.slabSet m k ∧ i + 1 ∈ T.slabSet m k := by
  obtain ⟨h₁, h₂, h₃⟩ := T.axialFace_vertexSet m i b
  constructor
  · intro h
    exact ⟨(T.exists_slice_gridSite_iff m k _ _).mp (h _ h₂),
      (T.exists_slice_gridSite_iff m k _ _).mp (h _ h₃)⟩
  · rintro ⟨ha, hb⟩ x hx
    obtain ⟨y, rfl | rfl⟩ := h₁ x hx
    · exact (T.exists_slice_gridSite_iff m k _ _).mpr ha
    · exact (T.exists_slice_gridSite_iff m k _ _).mpr hb
theorem sliceInSlab_add_one (m : SlabCount) (k : ZMod (m : ℕ)) (j : Fin T.ratioNat)
    (hj : (j : ℕ) + 1 < T.ratioNat) :
    T.sliceInSlab m (k, j) + 1 = T.sliceInSlab m (k, ⟨j + 1, hj⟩) := by
  simp only [sliceInSlab]
  rw [← slabSliceIndex_add_one]
  push_cast
  rfl
theorem sliceInSlab_last (m : SlabCount) (k : ZMod (m : ℕ)) (j : Fin T.ratioNat)
    (hj : (j : ℕ) + 1 = T.ratioNat) :
    T.sliceInSlab m (k, j) = T.slabSliceIndex m (k + 1) 0 := by
  have h : ((T.ratioNat : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 := by exact_mod_cast hj.symm
  rw [slabSliceIndex_succ_zero, h]
  rfl
theorem slabSliceIndex_zero_eq (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.slabSliceIndex m k 0 =
      T.sliceInSlab m (k - 1, ⟨T.ratioNat - 1, by have := T.two_le_ratioNat; omega⟩) := by
  have := T.sliceInSlab_last m (k - 1) ⟨T.ratioNat - 1, by have := T.two_le_ratioNat; omega⟩
    (by have := T.two_le_ratioNat; simp only []; omega)
  rw [this, sub_add_cancel]
theorem slabSliceIndex_zero_add_one (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.slabSliceIndex m k 0 + 1 =
      T.sliceInSlab m (k, ⟨0, by have := T.two_le_ratioNat; omega⟩) := by
  simp only [sliceInSlab]
  rw [← slabSliceIndex_add_one]
  simp
theorem zmod_sub_one_ne_self (m : SlabCount) (k : ZMod (m : ℕ)) : k - 1 ≠ k := by
  have : Fact (1 < (m : ℕ)) := ⟨by omega⟩
  intro h
  have : (1 : ZMod (m : ℕ)) = 0 := by
    have h' : k - 1 - k = 0 := by rw [h, sub_self]
    have : k - 1 - k = -1 := by ring
    rw [this] at h'
    exact neg_eq_zero.mp h'
  exact one_ne_zero this
theorem isCrossingFace_iff (m : SlabCount) (p : (T.torusPeriods m).Face) :
    T.IsCrossingFace m p ↔ ∃ (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge),
      p = T.axialFace m (T.slabSliceIndex m k 0) b := by
  constructor
  · intro hc
    obtain ⟨⟨i, q⟩ | ⟨i, b⟩, rfl⟩ := (T.faceOfSlices_bijective m).2 p
    · exfalso
      obtain ⟨k, hk⟩ := T.exists_mem_slabSet m i
      exact hc k ((T.isInSlab_sliceFace m k i q).mpr hk)
    · obtain ⟨⟨k, j⟩, rfl⟩ := (T.sliceInSlab_bijective m).2 i
      by_cases hj : (j : ℕ) + 1 < T.ratioNat
      · exfalso
        refine hc k ((T.isInSlab_axialFace m k _ b).mpr
          ⟨(T.sliceInSlab_mem_slabSet_iff m k k j).mpr rfl, ?_⟩)
        rw [sliceInSlab_add_one T m k j hj]
        exact (T.sliceInSlab_mem_slabSet_iff m k k _).mpr rfl
      · refine ⟨k + 1, b, ?_⟩
        rw [← T.sliceInSlab_last m k j (by have := j.2; omega)]
        rfl
  · rintro ⟨k, b, rfl⟩ k' hin
    obtain ⟨h₁, h₂⟩ := (T.isInSlab_axialFace m k' _ b).mp hin
    rw [slabSliceIndex_zero_add_one] at h₂
    rw [slabSliceIndex_zero_eq] at h₁
    have e₁ := (T.sliceInSlab_mem_slabSet_iff m k' _ _).mp h₁
    have e₂ := (T.sliceInSlab_mem_slabSet_iff m k' _ _).mp h₂
    exact zmod_sub_one_ne_self m k (e₁.symm.trans e₂)
theorem axialFace_dir_eq_axis (m : SlabCount) (i : T.SliceLabel m) (b : T.PositiveTransverseEdge) :
    (T.axialFace m i b).dir₁ = T.axis ∨ (T.axialFace m i b).dir₂ = T.axis := by
  rcases le_total T.axis (T.edgeAxis b).1 with hle | hle
  · exact Or.inl (min_eq_left hle)
  · exact Or.inr (max_eq_left hle)
theorem exists_axialFace_of_dir (m : SlabCount) (p : (T.torusPeriods m).Face)
    (i : T.SliceLabel m) (y : T.TransverseSite) (hb : p.corner = T.gridSite m i y)
    (h : p.dir₁ = T.axis ∨ p.dir₂ = T.axis) :
    ∃ b, p = T.axialFace m i b := by
  obtain ⟨⟨i', q⟩ | ⟨i', b⟩, rfl⟩ := (T.faceOfSlices_bijective m).2 p
  · exfalso
    rcases h with h | h
    · exact q.axis₁.2 h
    · exact q.axis₂.2 h
  · have := (T.gridSite_inj m hb).1
    subst this
    exact ⟨b, rfl⟩
theorem exists_sliceTime_of_latticePoint (x : InfiniteLattice.LatticePoint D.mesh) :
    ∃ c : ℤ, (x : AmbientSpace) T.axis = T.sliceTime c := by
  obtain ⟨i₀, h₀⟩ := T.exists_sliceTime_eq
  obtain ⟨n, hn⟩ := x.2
  refine ⟨n T.axis - i₀, ?_⟩
  rw [hn, h₀]
  congr 1
  push_cast
  ring
theorem projPoint_eq_gridSite (m : SlabCount) (x : InfiniteLattice.LatticePoint D.mesh) {c : ℤ}
    (hc : (x : AmbientSpace) T.axis = T.sliceTime c) :
    ∃ y, (T.torusPeriods m).projPoint x = T.gridSite m (c : T.SliceLabel m) y := by
  obtain ⟨i, y, h⟩ := T.gridSite_surjective m ((T.torusPeriods m).projPoint x)
  have h₁ := congrFun (congrArg Subtype.val h) T.axis
  rw [gridSite_axis] at h₁
  change _ = (((x : AmbientSpace) T.axis : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) at h₁
  rw [hc, coe_sliceTime_eq_iff] at h₁
  have hi : ((i.cast : ℤ) : T.SliceLabel m) = (c : T.SliceLabel m) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr h₁
  rw [ZMod.intCast_cast, ZMod.cast_id'] at hi
  exact ⟨y, by rw [← h, ← hi]; rfl⟩
theorem axisStep_apply_self (ν : Fin 4) :
    (InfiniteLattice.axisStep D.mesh ν : AmbientSpace) ν = D.mesh := by
  simp [InfiniteLattice.axisStep]
theorem axisStep_apply_of_ne {ν ρ : Fin 4} (h : ρ ≠ ν) :
    (InfiniteLattice.axisStep D.mesh ν : AmbientSpace) ρ = 0 := by
  simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem faceCorners_coord (p : D.Plaquette) (ρ : Fin 4) (x : InfiniteLattice.LatticePoint D.mesh)
    (hx : x ∈ D.faceCorners p) :
    (x : AmbientSpace) ρ = (p.corner : AmbientSpace) ρ ∨
      ((x : AmbientSpace) ρ = (p.corner : AmbientSpace) ρ + D.mesh ∧
        (p.lowAxis = ρ ∨ p.highAxis = ρ)) := by
  have hne := p.lowAxis_lt_highAxis.ne
  have hs : ∀ ν, (InfiniteLattice.axisStep D.mesh ν : AmbientSpace) ρ = D.mesh ∧ ν = ρ ∨
      (InfiniteLattice.axisStep D.mesh ν : AmbientSpace) ρ = 0 ∧ ν ≠ ρ := by
    intro ν
    by_cases h : ν = ρ
    · subst h
      exact Or.inl ⟨axisStep_apply_self ν, rfl⟩
    · exact Or.inr ⟨axisStep_apply_of_ne (Ne.symm h), h⟩
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rcases hs p.lowAxis with ⟨h, e⟩ | ⟨h, e⟩
    · exact Or.inr ⟨by simp [h], Or.inl e⟩
    · exact Or.inl (by simp [h])
  · rcases hs p.lowAxis with ⟨h, e⟩ | ⟨h, e⟩
    · rcases hs p.highAxis with ⟨h', e'⟩ | ⟨h', e'⟩
      · exact absurd (e.trans e'.symm) hne
      · exact Or.inr ⟨by simp [h, h'], Or.inl e⟩
    · rcases hs p.highAxis with ⟨h', e'⟩ | ⟨h', e'⟩
      · exact Or.inr ⟨by simp [h, h'], Or.inr e'⟩
      · exact Or.inl (by simp [h, h'])
  · rcases hs p.highAxis with ⟨h, e⟩ | ⟨h, e⟩
    · exact Or.inr ⟨by simp [h], Or.inr e⟩
    · exact Or.inl (by simp [h])
theorem wall_level_eq (k : ℤ) :
    T.grid.origin T.axis + k * T.grid.cellSide = T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2 := by
  simp only [sliceTime]
  rw [T.grid.cellSide_eq, ← T.natCast_ratioNat]
  push_cast
  ring
theorem eq_of_sliceTime_between {c c' : ℤ} (h₁ : T.sliceTime c < T.sliceTime c' + D.mesh / 2)
    (h₂ : T.sliceTime c' + D.mesh / 2 < T.sliceTime c + D.mesh) : c = c' := by
  have ha := D.mesh_pos
  simp only [sliceTime] at h₁ h₂
  have e₁ : (c : ℝ) * D.mesh < ((c' : ℝ) + 1 / 2) * D.mesh := by linarith
  have e₂ : ((c' : ℝ) + 1 / 2) * D.mesh < ((c : ℝ) + 1) * D.mesh := by linarith
  have f₁ := lt_of_mul_lt_mul_right e₁ ha.le
  have f₂ := lt_of_mul_lt_mul_right e₂ ha.le
  have g₁ : (2 * c : ℝ) < 2 * c' + 1 := by linarith
  have g₂ : (2 * c' : ℝ) + 1 < 2 * c + 2 := by linarith
  have g₁' : 2 * c < 2 * c' + 1 := by exact_mod_cast g₁
  have g₂' : 2 * c' + 1 < 2 * c + 2 := by exact_mod_cast g₂
  omega
theorem straddles_face {p : D.Plaquette} {b : D.Link} (hb : D.IsEdgeOf b p) {k : ℤ}
    (hc : T.grid.Straddles b T.axis k) :
    (p.lowAxis = T.axis ∨ p.highAxis = T.axis) ∧
      (p.corner : AmbientSpace) T.axis = T.sliceTime (k * (T.ratioNat : ℤ)) := by
  obtain ⟨c, hcb⟩ := T.exists_sliceTime_of_latticePoint p.corner
  have ht := faceCorners_coord p T.axis b.initial hb.1
  have hh := faceCorners_coord p T.axis b.terminal hb.2
  have ha := D.mesh_pos
  have key : (T.sliceTime c < T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2 ∧
      T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2 < T.sliceTime c + D.mesh) ∧
      (p.lowAxis = T.axis ∨ p.highAxis = T.axis) := by
    unfold ReflectionGrid.Straddles at hc
    rw [T.wall_level_eq k] at hc
    rw [hcb] at ht hh
    rcases hc with ⟨c₁, c₂⟩ | ⟨c₁, c₂⟩ <;> rcases ht with e | ⟨e, d⟩ <;> rcases hh with e' | ⟨e', d'⟩
    · rw [e] at c₁; rw [e'] at c₂; linarith
    · rw [e] at c₁; rw [e'] at c₂; exact ⟨⟨c₁, c₂⟩, d'⟩
    · rw [e] at c₁; rw [e'] at c₂; linarith
    · rw [e] at c₁; rw [e'] at c₂; linarith
    · rw [e] at c₂; rw [e'] at c₁; linarith
    · rw [e] at c₂; rw [e'] at c₁; linarith
    · rw [e] at c₂; rw [e'] at c₁; exact ⟨⟨c₁, c₂⟩, d⟩
    · rw [e] at c₂; rw [e'] at c₁; linarith
  refine ⟨key.2, ?_⟩
  rw [hcb, T.eq_of_sliceTime_between key.1.1 key.1.2]
theorem crossingFaces (m : SlabCount) : T.CrossingFaces m := by
  refine ⟨?_, T.isCrossingFace_iff m, ?_⟩
  · intro p
    by_cases h : T.IsCrossingFace m p
    · exact Or.inr h
    · left
      simp only [IsCrossingFace, not_forall, not_not] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, hk, fun k' hk' => ?_⟩
      obtain ⟨i, y, hy⟩ := T.gridSite_surjective m p.corner
      have hmem : T.gridSite m i y ∈ p.vertexSet := by
        rw [hy]
        exact Or.inl rfl
      exact T.slabSet_unique m ((T.exists_slice_gridSite_iff m k' i y).mp (hk' _ hmem))
        ((T.exists_slice_gridSite_iff m k i y).mp (hk _ hmem))
  · intro p
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨b, hb, k, hc⟩
      obtain ⟨hdir, hbase⟩ := T.straddles_face hb hc
      obtain ⟨y, hy⟩ := T.projPoint_eq_gridSite m p.corner hbase
      obtain ⟨b', hb'⟩ :=
        T.exists_axialFace_of_dir m ((T.torusPeriods m).projFace p) _ y hy hdir
      rw [isCrossingFace_iff]
      refine ⟨(k : ZMod (m : ℕ)), b', ?_⟩
      rw [hb', T.slabSliceIndex_eq_of_intCast m (c := k) rfl 0, add_zero]
    · intro h
      obtain ⟨k, b, e⟩ := (T.isCrossingFace_iff m _).mp h
      have hdir : p.lowAxis = T.axis ∨ p.highAxis = T.axis := by
        have := T.axialFace_dir_eq_axis m (T.slabSliceIndex m k 0) b
        rw [← e] at this
        exact this
      obtain ⟨c, hc⟩ := T.exists_sliceTime_of_latticePoint p.corner
      obtain ⟨y, hy⟩ := T.projPoint_eq_gridSite m p.corner hc
      have hbase : T.gridSite m (c : T.SliceLabel m) y =
          T.gridSite m (T.slabSliceIndex m k 0) b.1.source := by
        rw [← hy]
        exact congrArg BoxTorus.Face.corner e
      have hi := (T.gridSite_inj m hbase).1
      rw [slabSliceIndex, ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
      obtain ⟨z, hz⟩ := hi
      have hcr : c = ((k.cast : ℤ) - ((m : ℕ) : ℤ) * z) * (T.ratioNat : ℤ) := by
        push_cast at hz
        linear_combination -hz
      set k' : ℤ := (k.cast : ℤ) - ((m : ℕ) : ℤ) * z with hk'
      rw [hcr] at hc
      refine ⟨InfiniteLattice.Link.forwardFrom p.corner T.axis, ⟨Or.inl rfl, ?_⟩, k', ?_⟩
      · rcases hdir with d | d
        · rw [← d]
          exact Or.inr (Or.inl rfl)
        · rw [← d]
          exact Or.inr (Or.inr (Or.inr rfl))
      · refine Or.inl ⟨?_, ?_⟩
        · change (p.corner : AmbientSpace) T.axis < _
          rw [hc, T.wall_level_eq k']
          linarith [D.mesh_pos]
        · change _ < ((p.corner + InfiniteLattice.axisStep D.mesh T.axis :
            InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) T.axis
          have : ((p.corner + InfiniteLattice.axisStep D.mesh T.axis :
              InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) T.axis =
              (p.corner : AmbientSpace) T.axis + D.mesh := by simp [axisStep_apply_self]
          rw [this, hc, T.wall_level_eq k']
          linarith [D.mesh_pos]
    · intro b hb k hc
      obtain ⟨hdir, hbase⟩ := T.straddles_face hb hc
      change p.center T.axis = _
      rw [T.wall_level_eq k, ← hbase]
      simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply]
      have hne := p.lowAxis_lt_highAxis.ne
      rcases hdir with d | d
      · have d' : T.axis ≠ p.highAxis := fun e => hne (d.trans e)
        rw [← d, Pi.single_eq_same, d, Pi.single_eq_of_ne d', add_zero]
      · have d' : T.axis ≠ p.lowAxis := fun e => hne (e.symm.trans d.symm)
        rw [Pi.single_eq_of_ne d', ← d, Pi.single_eq_same, add_zero]
section Generic
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
theorem infinitePi_map_comp_equiv {A B : Type} (e : A ≃ B) :
    (Measure.infinitePi fun _ : B => μ).map (fun U a => U (e a)) =
      Measure.infinitePi fun _ : A => μ := by
  have hm : Measurable (fun (U : B → X) a => U (e a)) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  classical
  rw [Measure.map_apply hm (.pi s.countable_toSet fun _ _ => ht _)]
  have : (fun (U : B → X) a => U (e a)) ⁻¹' ((s : Set A).pi t) =
      ((s.map e.toEmbedding : Finset B) : Set B).pi (fun b => t (e.symm b)) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Finset.mem_coe, Set.mem_image,
      Equiv.coe_toEmbedding]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      simpa using h a ha
    · intro h a ha
      simpa using h (e a) ⟨a, ha, rfl⟩
  rw [this, Measure.infinitePi_pi _ (fun b _ => ht _), Finset.prod_map]
  simp
theorem infinitePi_map_sumSplit {A B : Type} :
    (Measure.infinitePi fun _ : A ⊕ B => μ).map (fun f => (f ∘ Sum.inl, f ∘ Sum.inr)) =
      (Measure.infinitePi fun _ : A => μ).prod (Measure.infinitePi fun _ : B => μ) := by
  have hel : Measurable (fun p : (A → X) × (B → X) => (Sum.elim p.1 p.2 : A ⊕ B → X)) := by
    refine measurable_pi_lambda _ ?_
    rintro (a | b)
    · exact (measurable_pi_apply a).comp measurable_fst
    · exact (measurable_pi_apply b).comp measurable_snd
  have hsp : Measurable (fun f : A ⊕ B → X => (f ∘ Sum.inl, f ∘ Sum.inr)) :=
    (measurable_pi_lambda _ fun a => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun a => measurable_pi_apply _)
  have key : ((Measure.infinitePi fun _ : A => μ).prod (Measure.infinitePi fun _ : B => μ)).map
      (fun p : (A → X) × (B → X) => (Sum.elim p.1 p.2 : A ⊕ B → X)) =
      Measure.infinitePi fun _ : A ⊕ B => μ := by
    refine Measure.eq_infinitePi _ fun s t ht => ?_
    classical
    rw [Measure.map_apply hel (.pi s.countable_toSet fun _ _ => ht _)]
    have : (fun p : (A → X) × (B → X) => (Sum.elim p.1 p.2 : A ⊕ B → X)) ⁻¹'
        ((s : Set (A ⊕ B)).pi t) =
        ((s.toLeft : Set A).pi (t ∘ Sum.inl)) ×ˢ ((s.toRight : Set B).pi (t ∘ Sum.inr)) := by
      ext ⟨f, g⟩
      simp [Set.mem_pi, Sum.forall]
    rw [this, Measure.prod_prod, Measure.infinitePi_pi _ (t := t ∘ Sum.inl) (fun _ _ => ht _),
      Measure.infinitePi_pi _ (t := t ∘ Sum.inr) (fun _ _ => ht _)]
    conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
    rw [Finset.prod_disjSum]
    rfl
  rw [← key, Measure.map_map hsp hel]
  have : (fun f : A ⊕ B → X => (f ∘ Sum.inl, f ∘ Sum.inr)) ∘
      (fun p : (A → X) × (B → X) => (Sum.elim p.1 p.2 : A ⊕ B → X)) = id := by
    funext p
    rfl
  rw [this, Measure.map_id]
theorem infinitePi_map_curry_pi {I κ : Type} [Fintype I] :
    (Measure.infinitePi fun _ : I × κ => μ).map (fun f i b => f (i, b)) =
      Measure.pi fun _ : I => Measure.infinitePi fun _ : κ => μ := by
  have := Measure.infinitePi_map_curry (fun (_ : I) (_ : κ) => μ)
  rw [Measure.infinitePi_eq_pi (ι := I)] at this
  exact this
end Generic
instance haarPi_isProbabilityMeasure (ι : Type) [Countable ι] :
    IsProbabilityMeasure (ComplexMatrix2.haarPi ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ => ComplexMatrix2.haarProb))
theorem measurePreserving_comp_equiv {A B : Type} [Countable A] [Countable B] (e : A ≃ B) :
    MeasurePreserving (fun (U : B → StandingParameters.gaugeGroup) a => U (e a))
      (ComplexMatrix2.haarPi B) (ComplexMatrix2.haarPi A) :=
  ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    infinitePi_map_comp_equiv ComplexMatrix2.haarProb e⟩
theorem measurePreserving_sumSplit {A B : Type} [Countable A] [Countable B] :
    MeasurePreserving (fun f : A ⊕ B → StandingParameters.gaugeGroup => (f ∘ Sum.inl, f ∘ Sum.inr))
      (ComplexMatrix2.haarPi (A ⊕ B))
      ((ComplexMatrix2.haarPi A).prod (ComplexMatrix2.haarPi B)) :=
  ⟨(measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _),
    infinitePi_map_sumSplit ComplexMatrix2.haarProb⟩
theorem measurePreserving_curry {I κ : Type} [Fintype I] [Countable κ] :
    MeasurePreserving (fun (f : I × κ → StandingParameters.gaugeGroup) i b => f (i, b))
      (ComplexMatrix2.haarPi (I × κ)) (Measure.pi fun _ : I => ComplexMatrix2.haarPi κ) :=
  ⟨measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    infinitePi_map_curry_pi ComplexMatrix2.haarProb⟩
theorem sliceField_eq (m : SlabCount) (i : T.SliceLabel m) :
    (fun U => T.sliceField m U i) = fun U b => U (T.forwardEdgeEquiv m (.inl (i, b))) :=
  funext fun U => funext fun b => T.sliceField_apply m U i b
theorem axialField_eq (m : SlabCount) (i : T.SliceLabel m) :
    (fun U => T.axialField m U i) = fun U y => U (T.forwardEdgeEquiv m (.inr (i, y))) :=
  funext fun U => funext fun y => T.axialField_apply m U i y
theorem continuous_sliceField (m : SlabCount) (i : T.SliceLabel m) :
    Continuous fun U => T.sliceField m U i := by
  rw [sliceField_eq]
  exact continuous_pi fun b => continuous_apply _
theorem continuous_axialField (m : SlabCount) (i : T.SliceLabel m) :
    Continuous fun U => T.axialField m U i := by
  rw [axialField_eq]
  exact continuous_pi fun y => continuous_apply _
theorem isHomeomorph_sliceAndAxialFields (m : SlabCount) :
    IsHomeomorph (T.sliceAndAxialFields m) := by
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨continuous_pi fun i => (T.continuous_sliceField m i).prodMk
    (T.continuous_axialField m i), ?_, ?_⟩
  · intro U U' h
    funext l
    obtain ⟨⟨i, b⟩ | ⟨i, y⟩, rfl⟩ := (T.forwardEdgeEquiv m).surjective l
    · have := congrFun (congrArg Prod.fst (congrFun h i)) b
      simpa [sliceAndAxialFields, sliceField_apply] using this
    · have := congrFun (congrArg Prod.snd (congrFun h i)) y
      simpa [sliceAndAxialFields, axialField_apply] using this
  · intro w
    refine ⟨fun l => Sum.elim (fun c => (w c.1).1 c.2) (fun c => (w c.1).2 c.2)
      ((T.forwardEdgeEquiv m).symm l), ?_⟩
    funext i
    refine Prod.ext (funext fun b => ?_) (funext fun y => ?_)
    · simp [sliceAndAxialFields, sliceField_apply]
    · simp [sliceAndAxialFields, axialField_apply]
theorem map_sliceAndAxialFields (m : SlabCount) :
    Measure.map (T.sliceAndAxialFields m) (T.torusPeriods m).haarMeasure =
      Measure.pi fun _ : T.SliceLabel m => T.edgeHaar.prod T.siteHaar := by
  let e : T.SliceLabel m × (T.PositiveTransverseEdge ⊕ T.TransverseSite) ≃
      (T.torusPeriods m).ForwardEdge :=
    (Equiv.prodSumDistrib _ _ _).trans (T.forwardEdgeEquiv m)
  have h₁ : MeasurePreserving (fun (U : (T.torusPeriods m).GaugeConfig) c => U (e c))
      (T.torusPeriods m).haarMeasure (ComplexMatrix2.haarPi _) := measurePreserving_comp_equiv e
  have h₂ := measurePreserving_curry (I := T.SliceLabel m)
    (κ := T.PositiveTransverseEdge ⊕ T.TransverseSite)
  have h₃ := measurePreserving_pi (fun _ : T.SliceLabel m =>
    ComplexMatrix2.haarPi (T.PositiveTransverseEdge ⊕ T.TransverseSite))
    (fun _ => T.edgeHaar.prod T.siteHaar) (fun _ => measurePreserving_sumSplit)
  have h := (h₃.comp (h₂.comp h₁)).map_eq
  rw [← h]
  congr 1
  funext U i
  refine Prod.ext (funext fun b => ?_) (funext fun y => ?_)
  · exact T.sliceField_apply m U i b
  · exact T.axialField_apply m U i y
theorem edgesAndFields (m : SlabCount) : T.EdgesAndFields m :=
  ⟨T.edgeOfSlices_injective m, T.range_edgeOfSlices m, T.isHomeomorph_sliceAndAxialFields m,
    T.map_sliceAndAxialFields m⟩
theorem slabReverse_involutive : Function.Involutive T.slabReverse := by
  intro η
  refine Prod.ext (funext fun j => ?_) (funext fun j => funext fun y => ?_)
  · simp [slabReverse]
  · simp [slabReverse]
theorem continuous_slabReverse : Continuous T.slabReverse := by
  refine Continuous.prodMk (continuous_pi fun j => ?_)
    (continuous_pi fun j => continuous_pi fun y => ?_)
  · exact (continuous_apply j.rev).comp continuous_fst
  · have h : Continuous fun η : T.SlabConfig => η.2 j.rev :=
      (continuous_apply j.rev).comp continuous_snd
    exact ((continuous_apply y).comp h).inv
theorem measurePreserving_pi_perm {X : Type} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {I : Type} [Fintype I] (e : Equiv.Perm I) :
    MeasurePreserving (fun (f : I → X) i => f (e i)) (Measure.pi fun _ : I => μ)
      (Measure.pi fun _ : I => μ) := by
  refine ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _, ?_⟩
  have := infinitePi_map_comp_equiv μ e
  rwa [Measure.infinitePi_eq_pi] at this
theorem measurePreserving_siteField_inv
    (hinv : Measure.map (fun U : ComplexMatrix2.specialUnitary => U⁻¹) ComplexMatrix2.haarProb =
      ComplexMatrix2.haarProb) :
    MeasurePreserving (fun (V : T.SiteField) y => (V y)⁻¹) T.siteHaar T.siteHaar := by
  refine ⟨measurable_pi_lambda _ fun y => (measurable_pi_apply y).inv, ?_⟩
  have := Measure.infinitePi_map_pi (fun _ : T.TransverseSite => ComplexMatrix2.haarProb)
    (f := fun _ (U : ComplexMatrix2.specialUnitary) => U⁻¹) (fun _ => measurable_inv)
  simp only [hinv] at this
  exact this
theorem measurePreserving_slabReverse
    (hinv : Measure.map (fun U : ComplexMatrix2.specialUnitary => U⁻¹) ComplexMatrix2.haarProb =
      ComplexMatrix2.haarProb) :
    MeasurePreserving T.slabReverse T.slabHaar T.slabHaar := by
  have h₁ := measurePreserving_pi_perm T.edgeHaar (I := Fin T.ratioNat) Fin.revPerm
  have h₂ := measurePreserving_pi_perm T.siteHaar (I := Fin (T.ratioNat - 1)) Fin.revPerm
  have h₃ := measurePreserving_pi (fun _ : Fin (T.ratioNat - 1) => T.siteHaar)
    (fun _ => T.siteHaar) (fun _ => T.measurePreserving_siteField_inv hinv)
  exact h₁.prod (h₃.comp h₂)
theorem slabReversalProperties
    (hinv : Measure.map (fun U : ComplexMatrix2.specialUnitary => U⁻¹) ComplexMatrix2.haarProb =
      ComplexMatrix2.haarProb) :
    T.SlabReversalProperties := by
  have hbij := T.slabReverse_involutive.bijective
  refine ⟨isHomeomorph_iff_continuous_bijective.mpr ⟨T.continuous_slabReverse, hbij⟩,
    T.slabReverse_involutive, T.measurePreserving_slabReverse hinv,
    fun Φ Φ' hΦ hΦ' => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨hm, C, hC⟩ := hΦ
    exact ⟨(Complex.continuous_conj.measurable).comp
      (hm.comp (T.measurePreserving_slabReverse hinv).measurable), C, fun η => by
      simpa [reflectConj] using hC (T.slabReverse η)⟩
  · funext η
    simp [reflectConj, T.slabReverse_involutive η]
  · funext η
    simp [reflectConj]
  · have : (fun η => ‖T.reflectConj Φ η‖) = (fun η => ‖Φ η‖) ∘ T.slabReverse := by
      funext η
      simp [reflectConj]
    rw [this]
    exact hbij.2.iSup_comp (fun η => ‖Φ η‖)
abbrev SlabCoord : Type :=
  (Fin T.ratioNat × T.PositiveTransverseEdge) ⊕ (Fin (T.ratioNat - 1) × T.TransverseSite)
def slabCoordIndex (m : SlabCount) :
    (ZMod (m : ℕ) × T.SlabCoord) ⊕ (ZMod (m : ℕ) × T.TransverseSite) →
      (T.SliceLabel m × T.PositiveTransverseEdge) ⊕ (T.SliceLabel m × T.TransverseSite)
  | .inl (k, .inl (j, b)) => .inl (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), b)
  | .inl (k, .inr (j, y)) => .inr (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), y)
  | .inr (k, y) => .inr (T.slabSliceIndex m k 0, y)
theorem slabSliceIndex_inj (m : SlabCount) {k k' : ZMod (m : ℕ)} {j j' : ℕ}
    (hj : j < T.ratioNat) (hj' : j' < T.ratioNat)
    (h : T.slabSliceIndex m k ((j : ℤ) + 1) = T.slabSliceIndex m k' ((j' : ℤ) + 1)) :
    k = k' ∧ j = j' := by
  have := T.sliceInSlab_injective m (a₁ := (k, ⟨j, hj⟩)) (a₂ := (k', ⟨j', hj'⟩)) h
  exact ⟨congrArg Prod.fst this,
    congrArg (fun p : ZMod (m : ℕ) × Fin T.ratioNat => (p.2 : ℕ)) this⟩
theorem slabSliceIndex_zero_inj (m : SlabCount) {k k' : ZMod (m : ℕ)}
    (h : T.slabSliceIndex m k 0 = T.slabSliceIndex m k' 0) : k = k' := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetup.slabSliceIndex_zero_injective <;> assumption
theorem slabSliceIndex_ne_zero_index (m : SlabCount) {k k' : ZMod (m : ℕ)} {j : ℕ}
    (hj : j < T.ratioNat - 1) :
    T.slabSliceIndex m k ((j : ℤ) + 1) ≠ T.slabSliceIndex m k' 0 := by
  intro h
  rw [slabSliceIndex_zero_eq] at h
  have := T.sliceInSlab_injective m (a₁ := (k, ⟨j, by omega⟩)) (a₂ := (_, _)) h
  have h' := congrArg (fun p : ZMod (m : ℕ) × Fin T.ratioNat => (p.2 : ℕ)) this
  simp only [] at h'
  omega
theorem slabCoordIndex_bijective (m : SlabCount) : Function.Bijective (T.slabCoordIndex m) := by
  constructor
  · rintro (⟨k, ⟨j, b⟩ | ⟨j, y⟩⟩ | ⟨k, y⟩) (⟨k', ⟨j', b'⟩ | ⟨j', y'⟩⟩ | ⟨k', y'⟩) h <;>
      simp only [slabCoordIndex, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at h
    · obtain ⟨h₁, rfl⟩ := h
      obtain ⟨rfl, e⟩ := T.slabSliceIndex_inj m j.2 j'.2 h₁
      rw [Fin.ext e]
    · obtain ⟨h₁, rfl⟩ := h
      obtain ⟨rfl, e⟩ :=
        T.slabSliceIndex_inj m (by have := j.2; omega) (by have := j'.2; omega) h₁
      rw [Fin.ext e]
    · exact absurd h.1 (T.slabSliceIndex_ne_zero_index m j.2)
    · exact absurd h.1.symm (T.slabSliceIndex_ne_zero_index m j'.2)
    · obtain ⟨h₁, rfl⟩ := h
      rw [T.slabSliceIndex_zero_inj m h₁]
  · rintro (⟨i, b⟩ | ⟨i, y⟩)
    · obtain ⟨⟨k, j⟩, rfl⟩ := (T.sliceInSlab_bijective m).2 i
      exact ⟨.inl (k, .inl (j, b)), rfl⟩
    · obtain ⟨⟨k, j⟩, rfl⟩ := (T.sliceInSlab_bijective m).2 i
      by_cases hj : (j : ℕ) + 1 < T.ratioNat
      · exact ⟨.inl (k, .inr (⟨j, by omega⟩, y)), rfl⟩
      · refine ⟨.inr (k + 1, y), ?_⟩
        rw [T.sliceInSlab_last m k j (by have := j.2; omega)]
        rfl
def slabCoordEquiv (m : SlabCount) :
    (ZMod (m : ℕ) × T.SlabCoord) ⊕ (ZMod (m : ℕ) × T.TransverseSite) ≃
      (T.torusPeriods m).ForwardEdge :=
  (Equiv.ofBijective _ (T.slabCoordIndex_bijective m)).trans (T.forwardEdgeEquiv m)
theorem slabCoordEquiv_inl_inl (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (k : ZMod (m : ℕ)) (j : Fin T.ratioNat) (b : T.PositiveTransverseEdge) :
    U (T.slabCoordEquiv m (.inl (k, .inl (j, b)))) =
      (T.slabRestriction m k U).1 j b :=
  (T.sliceField_apply m U _ b).symm
theorem slabCoordEquiv_inl_inr (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (k : ZMod (m : ℕ)) (j : Fin (T.ratioNat - 1)) (y : T.TransverseSite) :
    U (T.slabCoordEquiv m (.inl (k, .inr (j, y)))) =
      (T.slabRestriction m k U).2 j y :=
  (T.axialField_apply m U _ y).symm
theorem slabCoordEquiv_inr (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (k : ZMod (m : ℕ)) (y : T.TransverseSite) :
    U (T.slabCoordEquiv m (.inr (k, y))) = T.axialField m U (T.slabSliceIndex m k 0) y :=
  (T.axialField_apply m U _ y).symm
def slabCoordValue (m : SlabCount)
    (w : (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField)) :
    (ZMod (m : ℕ) × T.SlabCoord) ⊕ (ZMod (m : ℕ) × T.TransverseSite) →
      StandingParameters.gaugeGroup
  | .inl (k, .inl (j, b)) => (w.1 k).1 j b
  | .inl (k, .inr (j, y)) => (w.1 k).2 j y
  | .inr (k, y) => w.2 k y
theorem isHomeomorph_slabDecomposition (m : SlabCount) : IsHomeomorph (T.slabDecomposition m) := by
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨?_, ?_, ?_⟩
  · refine Continuous.prodMk (continuous_pi fun k => Continuous.prodMk
      (continuous_pi fun j => T.continuous_sliceField m _)
      (continuous_pi fun j => T.continuous_axialField m _))
      (continuous_pi fun k => T.continuous_axialField m _)
  · intro U U' h
    funext l
    obtain ⟨⟨k, ⟨j, b⟩ | ⟨j, y⟩⟩ | ⟨k, y⟩, rfl⟩ := (T.slabCoordEquiv m).surjective l
    · rw [T.slabCoordEquiv_inl_inl m U k j b, T.slabCoordEquiv_inl_inl m U' k j b]
      exact congrFun (congrFun (congrArg Prod.fst (congrFun (congrArg Prod.fst h) k)) j) b
    · rw [T.slabCoordEquiv_inl_inr m U k j y, T.slabCoordEquiv_inl_inr m U' k j y]
      exact congrFun (congrFun (congrArg Prod.snd (congrFun (congrArg Prod.fst h) k)) j) y
    · rw [T.slabCoordEquiv_inr m U k y, T.slabCoordEquiv_inr m U' k y]
      exact congrFun (congrFun (congrArg Prod.snd h) k) y
  · intro w
    refine ⟨fun l => T.slabCoordValue m w ((T.slabCoordEquiv m).symm l), ?_⟩
    refine Prod.ext (funext fun k => Prod.ext (funext fun j => funext fun b => ?_)
      (funext fun j => funext fun y => ?_)) (funext fun k => funext fun y => ?_)
    · have := T.slabCoordEquiv_inl_inl m
        (fun l => T.slabCoordValue m w ((T.slabCoordEquiv m).symm l)) k j b
      simp only [Equiv.symm_apply_apply, slabCoordValue] at this
      exact this.symm
    · have := T.slabCoordEquiv_inl_inr m
        (fun l => T.slabCoordValue m w ((T.slabCoordEquiv m).symm l)) k j y
      simp only [Equiv.symm_apply_apply, slabCoordValue] at this
      exact this.symm
    · have := T.slabCoordEquiv_inr m
        (fun l => T.slabCoordValue m w ((T.slabCoordEquiv m).symm l)) k y
      simp only [Equiv.symm_apply_apply, slabCoordValue] at this
      exact this.symm
theorem haarPi_sFinite (ι : Type) [Countable ι] : SFinite (ComplexMatrix2.haarPi ι) := by
  have := haarPi_isProbabilityMeasure ι
  infer_instance
theorem map_slabDecomposition (m : SlabCount) :
    Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure =
      (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
        (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar) := by
  have h₁ : MeasurePreserving
      (fun (U : (T.torusPeriods m).GaugeConfig) c => U (T.slabCoordEquiv m c))
      (T.torusPeriods m).haarMeasure (ComplexMatrix2.haarPi _) :=
    measurePreserving_comp_equiv (T.slabCoordEquiv m)
  have h₂ := measurePreserving_sumSplit (A := ZMod (m : ℕ) × T.SlabCoord)
    (B := ZMod (m : ℕ) × T.TransverseSite)
  have h₃ := measurePreserving_curry (I := ZMod (m : ℕ)) (κ := T.SlabCoord)
  have h₃' := measurePreserving_curry (I := ZMod (m : ℕ)) (κ := T.TransverseSite)
  have : SFinite (ComplexMatrix2.haarPi (Fin T.ratioNat × T.PositiveTransverseEdge)) :=
    haarPi_sFinite _
  have : SFinite (ComplexMatrix2.haarPi (Fin (T.ratioNat - 1) × T.TransverseSite)) :=
    haarPi_sFinite _
  have : SFinite (ComplexMatrix2.haarPi (ZMod (m : ℕ) × T.SlabCoord)) := haarPi_sFinite _
  have : SFinite (ComplexMatrix2.haarPi (ZMod (m : ℕ) × T.TransverseSite)) := haarPi_sFinite _
  have hC : MeasurePreserving
      (Prod.map
        (fun (f : Fin T.ratioNat × T.PositiveTransverseEdge → StandingParameters.gaugeGroup) i b =>
          f (i, b))
        (fun (f : Fin (T.ratioNat - 1) × T.TransverseSite → StandingParameters.gaugeGroup) i b =>
          f (i, b)) ∘
        (fun f : T.SlabCoord → StandingParameters.gaugeGroup => (f ∘ Sum.inl, f ∘ Sum.inr)))
      (ComplexMatrix2.haarPi T.SlabCoord) T.slabHaar :=
    ((measurePreserving_curry (I := Fin T.ratioNat) (κ := T.PositiveTransverseEdge)).prod
      (measurePreserving_curry (I := Fin (T.ratioNat - 1)) (κ := T.TransverseSite))).comp
      measurePreserving_sumSplit
  have h₄ := measurePreserving_pi (fun _ : ZMod (m : ℕ) => ComplexMatrix2.haarPi T.SlabCoord)
    (fun _ => T.slabHaar) (fun _ => hC)
  have h₅ := (h₄.comp h₃).prod h₃'
  have h := (h₅.comp (h₂.comp h₁)).map_eq
  refine Eq.trans ?_ h
  congr 1
  funext U
  refine Prod.ext (funext fun k => Prod.ext (funext fun j => funext fun b => ?_)
    (funext fun j => funext fun y => ?_)) (funext fun k => funext fun y => ?_)
  · exact (T.slabCoordEquiv_inl_inl m U k j b).symm
  · exact (T.slabCoordEquiv_inl_inr m U k j y).symm
  · exact (T.slabCoordEquiv_inr m U k y).symm
theorem slabSliceIndex_one (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.slabSliceIndex m k 1 = T.slabSliceIndex m k 0 + 1 := by
  have := T.slabSliceIndex_add_one m k 0
  rwa [zero_add] at this
theorem boltzmannFactor_axialHolonomy (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig)
    (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge) :
    boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
        (T.sliceField m U (T.slabSliceIndex m k 1)) (T.axialField m U (T.slabSliceIndex m k 0)) b) =
      Complex.exp (-(D.β : ℂ) *
        ((T.torusPeriods m).faceEnergy U (T.axialFace m (T.slabSliceIndex m k 0) b) : ℂ)) := by
  rw [slabSliceIndex_one, boltzmannFactor, faceEnergy_axialFace]
theorem slabDecompositionProperties (m : SlabCount) : T.SlabDecompositionProperties m :=
  ⟨T.isHomeomorph_slabDecomposition m, T.map_slabDecomposition m,
    fun U k b => T.boltzmannFactor_axialHolonomy m U k b⟩
abbrev SlabFaceLabel : Type :=
  (Fin T.ratioNat × T.TransverseFace) ⊕ (Fin (T.ratioNat - 1) × T.PositiveTransverseEdge)
def slabFace (m : SlabCount) (k : ZMod (m : ℕ)) :
    T.SlabFaceLabel → (T.torusPeriods m).Face
  | .inl (j, q) => T.sliceFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) q
  | .inr (j, b) => T.axialFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) b
theorem isInSlab_slabFace (m : SlabCount) (k : ZMod (m : ℕ)) (c : T.SlabFaceLabel) :
    T.IsInSlab m k (T.slabFace m k c) := by
  rcases c with ⟨j, q⟩ | ⟨j, b⟩
  · exact (T.isInSlab_sliceFace m k _ q).mpr ((T.sliceInSlab_mem_slabSet_iff m k k j).mpr rfl)
  · have hj := j.2
    refine (T.isInSlab_axialFace m k _ b).mpr
      ⟨(T.sliceInSlab_mem_slabSet_iff m k k ⟨j, by omega⟩).mpr rfl, ?_⟩
    have := T.sliceInSlab_add_one m k ⟨j, by omega⟩ (by simp only []; omega)
    change T.sliceInSlab m (k, ⟨j, by omega⟩) + 1 ∈ _
    rw [this]
    exact (T.sliceInSlab_mem_slabSet_iff m k k _).mpr rfl
theorem exists_slabFace_eq (m : SlabCount) (k : ZMod (m : ℕ)) (p : (T.torusPeriods m).Face)
    (h : T.IsInSlab m k p) : ∃ c, p = T.slabFace m k c := by
  obtain ⟨⟨i, q⟩ | ⟨i, b⟩, rfl⟩ := (T.faceOfSlices_bijective m).2 p
  · obtain ⟨j, rfl⟩ := (T.mem_slabSet_iff m k i).mp ((T.isInSlab_sliceFace m k i q).mp h)
    exact ⟨.inl (j, q), rfl⟩
  · obtain ⟨h₁, h₂⟩ := (T.isInSlab_axialFace m k i b).mp h
    obtain ⟨j, rfl⟩ := (T.mem_slabSet_iff m k i).mp h₁
    by_cases hj : (j : ℕ) + 1 < T.ratioNat
    · exact ⟨.inr (⟨j, by omega⟩, b), rfl⟩
    · exfalso
      rw [T.sliceInSlab_last m k j (by have := j.2; omega), slabSliceIndex_zero_add_one] at h₂
      have e := (T.sliceInSlab_mem_slabSet_iff m k _ _).mp h₂
      have := zmod_sub_one_ne_self m (k + 1)
      rw [add_sub_cancel_right] at this
      exact this e
theorem slabFace_injective (m : SlabCount) (k : ZMod (m : ℕ)) :
    Function.Injective (T.slabFace m k) := by
  rintro (⟨j, q⟩ | ⟨j, b⟩) (⟨j', q'⟩ | ⟨j', b'⟩) h
  · have := (T.faceOfSlices_bijective m).1
      (a₁ := .inl (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), q))
      (a₂ := .inl (T.slabSliceIndex m k (((j' : ℕ) : ℤ) + 1), q')) h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at this
    obtain ⟨h₁, rfl⟩ := this
    rw [Fin.ext (T.slabSliceIndex_inj m j.2 j'.2 h₁).2]
  · have := (T.faceOfSlices_bijective m).1
      (a₁ := .inl (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), q))
      (a₂ := .inr (T.slabSliceIndex m k (((j' : ℕ) : ℤ) + 1), b')) h
    exact absurd this (by simp)
  · have := (T.faceOfSlices_bijective m).1
      (a₁ := .inr (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), b))
      (a₂ := .inl (T.slabSliceIndex m k (((j' : ℕ) : ℤ) + 1), q')) h
    exact absurd this (by simp)
  · have := (T.faceOfSlices_bijective m).1
      (a₁ := .inr (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1), b))
      (a₂ := .inr (T.slabSliceIndex m k (((j' : ℕ) : ℤ) + 1), b')) h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at this
    obtain ⟨h₁, rfl⟩ := this
    rw [Fin.ext (T.slabSliceIndex_inj m (by have := j.2; omega) (by have := j'.2; omega) h₁).2]
theorem facesInSlab (m : SlabCount) : T.FacesInSlab m := by
  intro k
  refine ⟨fun p => ⟨fun h => ?_, ?_⟩, fun U => ⟨fun j q => ?_, fun j b => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := T.exists_slabFace_eq m k p h
    rcases c with ⟨j, q⟩ | ⟨j, b⟩
    · exact Or.inl ⟨((j : ℕ) : ℤ) + 1, by omega, by have := j.2; omega, q, rfl⟩
    · exact Or.inr ⟨((j : ℕ) : ℤ) + 1, by omega, by have := j.2; omega, b, rfl⟩
  · rintro (⟨j, h₁, h₂, q, rfl⟩ | ⟨j, h₁, h₂, b, rfl⟩)
    · exact (T.isInSlab_sliceFace m k _ q).mpr ⟨j, h₁, h₂, rfl⟩
    · exact (T.isInSlab_axialFace m k _ b).mpr ⟨⟨j, h₁, by omega, rfl⟩,
        ⟨j + 1, by omega, by omega, (T.slabSliceIndex_add_one m k j).symm⟩⟩
  · rw [faceEnergy_sliceFace]
    rfl
  · rw [faceEnergy_axialFace]
    have e : T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1) + 1 =
        T.slabSliceIndex m k (((((j : ℕ) + 1 : ℕ)) : ℤ) + 1) := by
      rw [← slabSliceIndex_add_one]
      push_cast
      rfl
    rw [e]
    rfl
def exponentTerm (m : SlabCount) (w : (T.torusPeriods m).Face → ℂ)
    (U : (T.torusPeriods m).GaugeConfig) (p : (T.torusPeriods m).Face) : ℂ :=
  (w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ)
theorem slabBoltzmann_slabRestriction (m : SlabCount) (w : (T.torusPeriods m).Face → ℂ)
    (k : ZMod (m : ℕ)) (U : (T.torusPeriods m).GaugeConfig) :
    T.slabBoltzmann m w k (T.slabRestriction m k U) =
      ∏ c, Complex.exp (T.exponentTerm m w U (T.slabFace m k c)) := by
  obtain ⟨-, hA⟩ := T.facesInSlab m k
  obtain ⟨h₁, h₂⟩ := hA U
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, slabBoltzmann]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun q _ => ?_
    simp only [slabFace, exponentTerm]
    rw [h₁ j q]
  · refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun b _ => ?_
    simp only [slabFace, exponentTerm]
    rw [h₂ j b]
theorem continuous_fullTrace :
    Continuous fun u : StandingParameters.gaugeGroup => ComplexMatrix2.fullTrace (u : ComplexMatrix2) :=
  Continuous.matrix_trace continuous_subtype_val
theorem continuous_mul_mul_inv_mul_inv {X : Type} [TopologicalSpace X]
    {a b c d : X → StandingParameters.gaugeGroup}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous fun x => a x * b x * (c x)⁻¹ * (d x)⁻¹ :=
  ((ha.mul hb).mul hc.inv).mul hd.inv
theorem continuous_faceAction (q : T.TransverseFace) :
    Continuous (T.faceAction q) := by
  have h : Continuous fun ξ : T.EdgeField => T.faceHolonomy ξ q := by
    unfold faceHolonomy
    exact continuous_mul_mul_inv_mul_inv (continuous_apply _) (continuous_apply _)
      (continuous_apply _) (continuous_apply _)
  exact continuous_const.sub (continuous_const.mul
    (Complex.continuous_re.comp (continuous_fullTrace.comp h)))
theorem continuous_slabFaceAction (j : Fin T.ratioNat) (q : T.TransverseFace) :
    Continuous (T.slabFaceAction j q) :=
  (T.continuous_faceAction q).comp ((continuous_apply j).comp continuous_fst)
theorem continuous_slabAxialAction (j : Fin (T.ratioNat - 1)) (b : T.PositiveTransverseEdge) :
    Continuous (T.slabAxialAction j b) := by
  have c₁ : ∀ l : Fin T.ratioNat, Continuous fun η : T.SlabConfig => η.1 l := fun l =>
    (continuous_apply l).comp continuous_fst
  have c₂ : Continuous fun η : T.SlabConfig => η.2 j := (continuous_apply j).comp continuous_snd
  have h : Continuous fun η : T.SlabConfig => T.axialHolonomy (η.1 ⟨j, by have := j.2; omega⟩)
      (η.1 ⟨j + 1, by have := j.2; omega⟩) (η.2 j) b := by
    unfold axialHolonomy
    exact continuous_mul_mul_inv_mul_inv ((continuous_apply _).comp c₂)
      ((continuous_apply _).comp (c₁ _))
      ((continuous_apply _).comp c₂) ((continuous_apply _).comp (c₁ _))
  exact continuous_const.sub (continuous_const.mul (continuous_fullTrace.comp h))
theorem continuous_slabBoltzmann (m : SlabCount) (w : (T.torusPeriods m).Face → ℂ)
    (k : ZMod (m : ℕ)) : Continuous (T.slabBoltzmann m w k) := by
  refine Continuous.mul (continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun q _ => ?_)
    (continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun b _ => ?_)
  · exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (T.continuous_slabFaceAction j q)))
  · exact Complex.continuous_exp.comp (continuous_const.mul (T.continuous_slabAxialAction j b))
theorem isInSlab_unique (m : SlabCount) {k k' : ZMod (m : ℕ)}
    {p : (T.torusPeriods m).Face} (h : T.IsInSlab m k p) (h' : T.IsInSlab m k' p) :
    k = k' := by
  obtain ⟨i, y, hy⟩ := T.gridSite_surjective m p.corner
  have hmem : T.gridSite m i y ∈ p.vertexSet := by
    rw [hy]
    exact Or.inl rfl
  exact T.slabSet_unique m ((T.exists_slice_gridSite_iff m k i y).mp (h _ hmem))
    ((T.exists_slice_gridSite_iff m k' i y).mp (h' _ hmem))
def faceBySlabs (m : SlabCount) :
    (ZMod (m : ℕ) × T.SlabFaceLabel) ⊕ (ZMod (m : ℕ) × T.PositiveTransverseEdge) →
      (T.torusPeriods m).Face
  | .inl (k, c) => T.slabFace m k c
  | .inr (k, b) => T.axialFace m (T.slabSliceIndex m k 0) b
theorem faceBySlabs_bijective (m : SlabCount) :
    Function.Bijective (T.faceBySlabs m) := by
  constructor
  · rintro (⟨k, c⟩ | ⟨k, b⟩) (⟨k', c'⟩ | ⟨k', b'⟩) h
    · change T.slabFace m k c = T.slabFace m k' c' at h
      have hi := T.isInSlab_slabFace m k c
      rw [h] at hi
      obtain rfl := T.isInSlab_unique m hi (T.isInSlab_slabFace m k' c')
      rw [T.slabFace_injective m k h]
    · exfalso
      change T.slabFace m k c = T.axialFace m (T.slabSliceIndex m k' 0) b' at h
      have hi := T.isInSlab_slabFace m k c
      rw [h] at hi
      exact (T.isCrossingFace_iff m _).mpr ⟨k', b', rfl⟩ k hi
    · exfalso
      change T.axialFace m (T.slabSliceIndex m k 0) b = T.slabFace m k' c' at h
      have hi := T.isInSlab_slabFace m k' c'
      rw [← h] at hi
      exact (T.isCrossingFace_iff m _).mpr ⟨k, b, rfl⟩ k' hi
    · have := (T.faceOfSlices_bijective m).1
        (a₁ := .inr (T.slabSliceIndex m k 0, b)) (a₂ := .inr (T.slabSliceIndex m k' 0, b')) h
      simp only [Sum.inr.injEq, Prod.mk.injEq] at this
      obtain ⟨h₁, rfl⟩ := this
      rw [T.slabSliceIndex_zero_inj m h₁]
  · intro p
    by_cases h : T.IsCrossingFace m p
    · obtain ⟨k, b, rfl⟩ := (T.isCrossingFace_iff m p).mp h
      exact ⟨.inr (k, b), rfl⟩
    · simp only [IsCrossingFace, not_forall, not_not] at h
      obtain ⟨k, hk⟩ := h
      obtain ⟨c, rfl⟩ := T.exists_slabFace_eq m k p hk
      exact ⟨.inl (k, c), rfl⟩
theorem slabBoltzmannWeights (m : SlabCount) : T.SlabBoltzmannWeights m := by
  intro w _
  refine ⟨fun k => ⟨T.continuous_slabBoltzmann m w k, ?_, fun U => ?_⟩, fun hw => ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (T.continuous_slabBoltzmann m w k).continuousOn
    exact ⟨C, fun η => hC η (mem_univ η)⟩
  · have hs : ∀ p, T.IsInSlab m k p ↔ p ∈ range (T.slabFace m k) := fun p =>
      ⟨fun h => by
        obtain ⟨c, rfl⟩ := T.exists_slabFace_eq m k p h
        exact mem_range_self c, by
        rintro ⟨c, rfl⟩
        exact T.isInSlab_slabFace m k c⟩
    rw [T.slabBoltzmann_slabRestriction m w k U]
    have e : (∏ᶠ (p : (T.torusPeriods m).Face) (_ : T.IsInSlab m k p),
        Complex.exp ((w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ))) =
        ∏ᶠ (p : (T.torusPeriods m).Face) (_ : p ∈ range (T.slabFace m k)),
          Complex.exp (T.exponentTerm m w U p) :=
      finprod_congr fun p => finprod_congr_Prop (propext (hs p)) fun _ => rfl
    rw [e, finprod_mem_range (T.slabFace_injective m k), finprod_eq_prod_of_fintype]
  · rw [slabProductIntegral]
    refine congrArg
      (fun f : (T.torusPeriods m).GaugeConfig → ℂ => ∫ U, f U ∂(T.torusPeriods m).haarMeasure)
      (funext fun U => ?_)
    let e := Equiv.ofBijective _ (T.faceBySlabs_bijective m)
    have hsum : (∑ᶠ p : (T.torusPeriods m).Face,
        (w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ)) =
        ∑ x, T.exponentTerm m w U (T.faceBySlabs m x) :=
      (finsum_comp_equiv e).symm.trans (finsum_eq_sum_of_fintype _)
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, Complex.exp_add,
      Complex.exp_sum, Complex.exp_sum, Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [T.slabBoltzmann_slabRestriction m w k U, Complex.exp_sum]
      rfl
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [boltzmannFactor_axialHolonomy]
      have hz : w (T.axialFace m (T.slabSliceIndex m k 0) b) = 0 :=
        hw _ ((T.isCrossingFace_iff m _).mpr ⟨k, b, rfl⟩)
      simp only [faceBySlabs, exponentTerm, hz, zero_sub]
end TransferSetup
theorem TransferAssertions.holds (hHaar : ComplexMatrix2.HaarExpChartProperties) :
    TransferAssertions.Statement := fun _ T m =>
  ⟨T.sliceTimesAndSlabs m, T.edgesAndFields m, TransferSetup.gaugeGroupTraceFacts,
    T.facesOfSlices m, T.crossingFaces m, T.slabReversalProperties hHaar.2.2.2,
    T.slabDecompositionProperties m, T.facesInSlab m, T.slabBoltzmannWeights m⟩
end ChessboardTori
end YangMills.Construction
end
