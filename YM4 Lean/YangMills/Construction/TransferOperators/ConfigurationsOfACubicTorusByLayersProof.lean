import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.TorusMeasureSatisfiesThePerturbedEquationOfAWindowProof
import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
namespace TransferOperators.SliceDecomposition
variable {Γ : CubicPeriodSublattice} {μ : Fin 4}
theorem level_add (μ : Fin 4) (x y : LatticePoint 1) :
    level μ (x + y) = level μ x + level μ y := by
  have h : ((level μ (x + y) : ℤ) : ℝ) = ((level μ x + level μ y : ℤ) : ℝ) := by
    push_cast
    rw [level_cast, level_cast, level_cast]
    rfl
  exact_mod_cast h
theorem level_pointAtLevel (j : ℤ) (y : SliceSite μ) :
    level μ (pointAtLevel μ j y) = j := by
  have h : ((level μ (pointAtLevel μ j y) : ℤ) : ℝ) = (j : ℝ) := by
    rw [level_cast]
    change ((j • axisStep 1 μ : LatticePoint 1) : AmbientSpace) μ + ((y : LatticePoint 1) : AmbientSpace) μ = j
    rw [coe_zsmul_axisStep_apply_self, mem_sliceLattice.mp y.2, add_zero]
  exact_mod_cast h
theorem pointAtLevel_level_slicePart (x : LatticePoint 1) :
    pointAtLevel μ (level μ x) (slicePart μ x) = x := by
  change level μ x • axisStep 1 μ + (x - level μ x • axisStep 1 μ) = x
  abel
theorem level_period_eq_zero {γ : LatticePoint 1} (hγ : γ ∈ Γ.lattice.periods) :
    ((level μ γ : ℤ) : ZMod Γ.side) = 0 := by
  rw [Γ.periods_eq] at hγ
  obtain ⟨k, hk⟩ := AddSubgroup.mem_addSubgroupOf.mp hγ
  have e : ((level μ γ : ℤ) : ℝ) = ((k μ * (Γ.side : ℤ) : ℤ) : ℝ) := by
    rw [level_cast, hk μ]
    push_cast
    rfl
  have e' : level μ γ = k μ * (Γ.side : ℤ) := by exact_mod_cast e
  rw [e']
  simp
theorem zsmul_axisStep_mem_periods {j j' : ℤ} (h : (j : ZMod Γ.side) = j') :
    (j' - j) • axisStep 1 μ ∈ Γ.lattice.periods := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [Γ.periods_eq]
  refine AddSubgroup.mem_addSubgroupOf.mpr ⟨Pi.single μ q, fun ν => ?_⟩
  change (j' - j) • (Pi.single μ (1 : ℝ) : AmbientSpace) ν = _
  by_cases hν : ν = μ
  · subst hν
    have e : ((j' - j : ℤ) : ℝ) = ((Γ.side : ℤ) * q : ℤ) := congrArg _ hq
    push_cast at e
    simp only [Pi.single_eq_same, zsmul_eq_mul, mul_one]
    push_cast
    rw [e]
    ring
  · simp [Pi.single_eq_of_ne hν]
theorem linkClass_translate (P : PeriodSublattice 1) (b : PositiveLink 1) {γ : LatticePoint 1}
    (hγ : γ ∈ P.periods) : P.linkClass (b.translate γ) = P.linkClass b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.linkClass_translate <;> assumption
theorem exists_period_of_linkClass_eq (P : PeriodSublattice 1) {b b' : PositiveLink 1}
    (h : P.linkClass b = P.linkClass b') : ∃ γ ∈ P.periods, b' = b.translate γ := by apply _root_.YangMills.Construction.InfiniteLattice.TiltedTorusMeasureWindowEquation.exists_period_of_linkClass_eq <;> assumption
theorem vertexClass_vertexRep (v : Γ.VertexOrbits μ) :
    Γ.vertexClass (CubicPeriodSublattice.vertexRep v) = v :=
  Subtype.ext v.2.choose_spec
theorem cast_levelRep (c : ZMod Γ.side) :
    ((Γ.levelRep c : ℤ) : ZMod Γ.side) = c := by
  simp [CubicPeriodSublattice.levelRep]
theorem spatialLink_class_eq {j j' : ℤ} (hj : (j : ZMod Γ.side) = j') {b b' : SliceLink μ}
    (hb : Γ.linkClass b = Γ.linkClass b') :
    Γ.lattice.linkClass (spatialLink μ j b) = Γ.lattice.linkClass (spatialLink μ j' b') := by
  have hm : b' ∈ Γ.linkOrbit μ b := by
    have e : Γ.linkOrbit μ b = Γ.linkOrbit μ b' := congrArg Subtype.val hb
    rw [e]
    exact Γ.self_mem_linkOrbit b'
  obtain ⟨γ, hγ, e⟩ := hm
  have ht : b'.1.initial = b.1.initial + γ := congrArg InfiniteLattice.Link.initial e
  have hh : b'.1.terminal = b.1.terminal + γ := congrArg InfiniteLattice.Link.terminal e
  have hv : γ + (j' - j) • axisStep 1 μ ∈ Γ.lattice.periods :=
    add_mem (AddSubgroup.mem_inf.mp hγ).1 (zsmul_axisStep_mem_periods hj)
  have e' : spatialLink μ j' b' = (spatialLink μ j b).translate (γ + (j' - j) • axisStep 1 μ) := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change j' • axisStep 1 μ + b'.1.initial = j • axisStep 1 μ + b.1.initial + (γ + (j' - j) • axisStep 1 μ)
      rw [ht, sub_smul]
      abel
    · change j' • axisStep 1 μ + b'.1.terminal = j • axisStep 1 μ + b.1.terminal + (γ + (j' - j) • axisStep 1 μ)
      rw [hh, sub_smul]
      abel
  rw [e', linkClass_translate _ _ hv]
theorem temporalLink_class_eq {j j' : ℤ} (hj : (j : ZMod Γ.side) = j') {y y' : SliceSite μ}
    (hy : Γ.vertexClass y = Γ.vertexClass y') :
    Γ.lattice.linkClass (temporalLink μ j y) = Γ.lattice.linkClass (temporalLink μ j' y') := by
  have hm : y' ∈ Γ.vertexOrbit μ y := by
    have e : Γ.vertexOrbit μ y = Γ.vertexOrbit μ y' := congrArg Subtype.val hy
    rw [e]
    exact ⟨0, zero_mem _, (add_zero _).symm⟩
  obtain ⟨γ, hγ, e⟩ := hm
  have hv : γ + (j' - j) • axisStep 1 μ ∈ Γ.lattice.periods :=
    add_mem (AddSubgroup.mem_inf.mp hγ).1 (zsmul_axisStep_mem_periods hj)
  have e' : temporalLink μ j' y' = (temporalLink μ j y).translate (γ + (j' - j) • axisStep 1 μ) := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change j' • axisStep 1 μ + (y' : LatticePoint 1) = j • axisStep 1 μ + y + (γ + (j' - j) • axisStep 1 μ)
      rw [e, sub_smul]
      abel
    · change (j' + 1) • axisStep 1 μ + (y' : LatticePoint 1) =
        (j + 1) • axisStep 1 μ + y + (γ + (j' - j) • axisStep 1 μ)
      rw [e, sub_smul, add_smul, add_smul]
      abel
  rw [e', linkClass_translate _ _ hv]
theorem eq_of_spatialLink_class_eq {j j' : ℤ} {b b' : SliceLink μ}
    (h : Γ.lattice.linkClass (spatialLink μ j b) = Γ.lattice.linkClass (spatialLink μ j' b')) :
    (j : ZMod Γ.side) = j' ∧ Γ.linkClass b = Γ.linkClass b' := by
  obtain ⟨γ, hγ, e⟩ := exists_period_of_linkClass_eq _ h
  have ht : pointAtLevel μ j' b'.source = pointAtLevel μ j b.source + γ :=
    congrArg (fun c : PositiveLink 1 => c.1.initial) e
  have hh : pointAtLevel μ j' b'.target = pointAtLevel μ j b.target + γ :=
    congrArg (fun c : PositiveLink 1 => c.1.terminal) e
  have hl : j' = j + level μ γ := by
    have := congrArg (level μ) ht
    rwa [level_add, level_pointAtLevel, level_pointAtLevel] at this
  have hj : (j : ZMod Γ.side) = j' := by
    rw [hl]
    push_cast
    rw [level_period_eq_zero hγ, add_zero]
  refine ⟨hj, ?_⟩
  have hv : γ - (j' - j) • axisStep 1 μ ∈ Γ.lattice.periods := sub_mem hγ (zsmul_axisStep_mem_periods hj)
  have et : b'.1.initial = b.1.initial + (γ - (j' - j) • axisStep 1 μ) := by
    have e₁ : j' • axisStep 1 μ + b'.1.initial = j • axisStep 1 μ + b.1.initial + γ := ht
    have e₂ : b'.1.initial = (j' • axisStep 1 μ + b'.1.initial) - j' • axisStep 1 μ := by abel
    rw [e₂, e₁, sub_smul]
    abel
  have eh : b'.1.terminal = b.1.terminal + (γ - (j' - j) • axisStep 1 μ) := by
    have e₁ : j' • axisStep 1 μ + b'.1.terminal = j • axisStep 1 μ + b.1.terminal + γ := hh
    have e₂ : b'.1.terminal = (j' • axisStep 1 μ + b'.1.terminal) - j' • axisStep 1 μ := by abel
    rw [e₂, e₁, sub_smul]
    abel
  have hy : γ - (j' - j) • axisStep 1 μ ∈ sliceLattice μ := by
    have e₃ : γ - (j' - j) • axisStep 1 μ = (b'.source : LatticePoint 1) - b.source := by
      change _ = b'.1.initial - b.1.initial
      rw [et]
      abel
    rw [e₃]
    exact (sliceLattice μ).sub_mem b'.source.2 b.source.2
  have hm : b' ∈ Γ.linkOrbit μ b :=
    ⟨_, AddSubgroup.mem_inf.mpr ⟨hv, hy⟩, InfiniteLattice.Link.ext et eh⟩
  exact Subtype.ext (Γ.linkOrbit_eq_of_mem hm).symm
theorem eq_of_temporalLink_class_eq {j j' : ℤ} {y y' : SliceSite μ}
    (h : Γ.lattice.linkClass (temporalLink μ j y) = Γ.lattice.linkClass (temporalLink μ j' y')) :
    (j : ZMod Γ.side) = j' ∧ Γ.vertexClass y = Γ.vertexClass y' := by
  obtain ⟨γ, hγ, e⟩ := exists_period_of_linkClass_eq _ h
  have ht : pointAtLevel μ j' y' = pointAtLevel μ j y + γ :=
    congrArg (fun c : PositiveLink 1 => c.1.initial) e
  have hl : j' = j + level μ γ := by
    have := congrArg (level μ) ht
    rwa [level_add, level_pointAtLevel, level_pointAtLevel] at this
  have hj : (j : ZMod Γ.side) = j' := by
    rw [hl]
    push_cast
    rw [level_period_eq_zero hγ, add_zero]
  refine ⟨hj, ?_⟩
  have hv : γ - (j' - j) • axisStep 1 μ ∈ Γ.lattice.periods := sub_mem hγ (zsmul_axisStep_mem_periods hj)
  have et : (y' : LatticePoint 1) = y + (γ - (j' - j) • axisStep 1 μ) := by
    have e₁ : j' • axisStep 1 μ + (y' : LatticePoint 1) = j • axisStep 1 μ + y + γ := ht
    have e₂ : (y' : LatticePoint 1) = (j' • axisStep 1 μ + (y' : LatticePoint 1)) - j' • axisStep 1 μ := by abel
    rw [e₂, e₁, sub_smul]
    abel
  have hy : (y' : LatticePoint 1) - y ∈ Γ.slicePeriods μ := by
    refine AddSubgroup.mem_inf.mpr ⟨?_, (sliceLattice μ).sub_mem y'.2 y.2⟩
    rw [et]
    simpa using hv
  exact Subtype.ext (Γ.vertexOrbit_eq_of_sub_mem hy)
theorem spatialLink_class_ne_temporalLink (j j' : ℤ) (b : SliceLink μ) (y : SliceSite μ) :
    Γ.lattice.linkClass (spatialLink μ j b) ≠ Γ.lattice.linkClass (temporalLink μ j' y) := by
  intro h
  obtain ⟨γ, -, e⟩ := exists_period_of_linkClass_eq _ h
  have ht : pointAtLevel μ j' y = pointAtLevel μ j b.source + γ :=
    congrArg (fun c : PositiveLink 1 => c.1.initial) e
  have hh : pointAtLevel μ (j' + 1) y = pointAtLevel μ j b.target + γ :=
    congrArg (fun c : PositiveLink 1 => c.1.terminal) e
  have h₁ := congrArg (level μ) ht
  have h₂ := congrArg (level μ) hh
  rw [level_add, level_pointAtLevel, level_pointAtLevel] at h₁ h₂
  omega
theorem labelQuotientLink_injective : Function.Injective (Γ.labelQuotientLink μ) := by
  rintro (⟨c, e⟩ | ⟨c, v⟩) (⟨c', e'⟩ | ⟨c', v'⟩) h
  · obtain ⟨h₁, h₂⟩ := eq_of_spatialLink_class_eq h
    rw [cast_levelRep, cast_levelRep] at h₁
    rw [CubicPeriodSublattice.linkClass_linkRep,
      CubicPeriodSublattice.linkClass_linkRep] at h₂
    change c = c' at h₁
    change e = e' at h₂
    rw [h₁, h₂]
  · exact absurd h (spatialLink_class_ne_temporalLink _ _ _ _)
  · exact absurd h.symm (spatialLink_class_ne_temporalLink _ _ _ _)
  · obtain ⟨h₁, h₂⟩ := eq_of_temporalLink_class_eq h
    rw [cast_levelRep, cast_levelRep] at h₁
    rw [vertexClass_vertexRep, vertexClass_vertexRep] at h₂
    change c = c' at h₁
    change v = v' at h₂
    rw [h₁, h₂]
theorem labelQuotientLink_surjective : Function.Surjective (Γ.labelQuotientLink μ) := by
  rintro ⟨_, b, rfl⟩
  obtain ⟨ν, hν⟩ := b.2
  have hx := pointAtLevel_level_slicePart (μ := μ) b.1.initial
  have hh : b.1.terminal = b.1.initial + axisStep 1 ν := by
    rw [← hν]
    abel
  by_cases hμ : ν = μ
  · subst hμ
    have hb : b = temporalLink ν (level ν b.1.initial) (slicePart ν b.1.initial) := by
      refine Subtype.ext (InfiniteLattice.Link.ext hx.symm ?_)
      change b.1.terminal = pointAtLevel ν _ _
      rw [pointAtLevel_succ, hx, hh]
    refine ⟨Sum.inr ((level ν b.1.initial : ℤ), Γ.vertexClass (slicePart ν b.1.initial)), ?_⟩
    exact (temporalLink_class_eq (cast_levelRep _)
      (vertexClass_vertexRep _)).trans (congrArg Γ.lattice.linkClass hb.symm)
  · have hb : b = spatialLink μ (level μ b.1.initial)
        (SliceLink.ofAxis (slicePart μ b.1.initial) ν hμ) := by
      refine Subtype.ext (InfiniteLattice.Link.ext hx.symm ?_)
      change b.1.terminal = level μ b.1.initial • axisStep 1 μ +
        ((slicePart μ b.1.initial : LatticePoint 1) + axisStep 1 ν)
      rw [← add_assoc]
      change _ = pointAtLevel μ _ _ + _
      rw [hx, hh]
    refine ⟨Sum.inl ((level μ b.1.initial : ℤ),
      Γ.linkClass (SliceLink.ofAxis (slicePart μ b.1.initial) ν hμ)), ?_⟩
    exact (spatialLink_class_eq (cast_levelRep _)
      (CubicPeriodSublattice.linkClass_linkRep _)).trans
        (congrArg Γ.lattice.linkClass hb.symm)
theorem measurePreserving_readByPairs {G Z V E T : Type} [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] [Fintype Z] [Finite V] [Finite E] (N : (Z × E) ⊕ (Z × V) ≃ T)
    (σ : Z ≃ Z) :
    MeasurePreserving
      (fun (U : T → G) (c : Z) =>
        ((fun v => U (N (Sum.inr (c, v))) : V → G), (fun e => U (N (Sum.inl (σ c, e))) : E → G)))
      (Measure.infinitePi fun _ : T => ν)
      (Measure.pi fun _ : Z =>
        (Measure.infinitePi fun _ : V => ν).prod (Measure.infinitePi fun _ : E => ν)) := by
  classical
  cases nonempty_fintype V
  cases nonempty_fintype E
  have m₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : T => G) N).symm
      (Measure.infinitePi fun _ : T => ν) (Measure.pi fun _ : (Z × E) ⊕ (Z × V) => ν) := by
    rw [← Measure.infinitePi_eq_pi]
    exact MeasurePreserving.symm _
      ⟨(MeasurableEquiv.piCongrLeft (fun _ : T => G) N).measurable,
        Measure.infinitePi_map_piCongrLeft (fun _ : T => ν) N⟩
  have m₂ := measurePreserving_sumPiEquivProdPi (X := fun _ : (Z × E) ⊕ (Z × V) => G)
    (fun _ => ν)
  have curried : ∀ W : Type, ∀ [Fintype W],
      MeasurePreserving (MeasurableEquiv.curry Z W G) (Measure.pi fun _ : Z × W => ν)
        (Measure.pi fun _ : Z => Measure.infinitePi fun _ : W => ν) := by
    intro W _
    refine ⟨(MeasurableEquiv.curry Z W G).measurable, ?_⟩
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_curry fun _ _ => ν
  have shift := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (α := fun _ : Z => E → G)
      (fun _ : Z => Measure.infinitePi fun _ : E => ν) σ)
  have m₃ := ((shift.comp (curried E)).prod (curried V))
  have m₄ := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow (V → G) (E → G) Z
      (fun _ => Measure.infinitePi fun _ : V => ν) (fun _ => Measure.infinitePi fun _ : E => ν))
  have m₅ := (m₄.comp Measure.measurePreserving_swap).comp (m₃.comp (m₂.comp m₁))
  exact m₅
theorem statement_holds : Statement := by
  intro Γ μ
  have hb : Function.Bijective (Γ.labelQuotientLink μ) :=
    ⟨labelQuotientLink_injective, labelQuotientLink_surjective⟩
  exact ⟨hb, measurePreserving_readByPairs Matrices.ComplexMatrix2.haarProb (Equiv.ofBijective _ hb) (Equiv.addRight 1)⟩
end TransferOperators.SliceDecomposition
end YangMills.Construction
end
