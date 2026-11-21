import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCutProof
import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayersProof
import YangMills.Construction.TransferOperators.IntegrandOfAnInsertionIsAProductOfKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice CutoffLattice Matrices
namespace TransferOperators.SliceProduct
variable {Γ : CubicPeriodSublattice} {μ : Fin 4}
theorem plaquetteMap_shift (p : ElementaryPlaquette 1) (γ : LatticePoint 1) :
    (shift γ).plaquetteMap p = translateFace p γ := by
  have hs : ∀ x : LatticePoint 1, (shift γ).pointMap x = x + γ := fun x => rfl
  have hc : (translateFace p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by
    simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, hs]
    change ({p.corner + γ, p.corner + γ + axisStep 1 p.lowAxis,
      p.corner + γ + axisStep 1 p.lowAxis + axisStep 1 p.highAxis,
        p.corner + γ + axisStep 1 p.highAxis} : Set (LatticePoint 1)) = _
    rw [add_right_comm p.corner γ (axisStep 1 p.lowAxis),
      add_right_comm p.corner γ (axisStep 1 p.highAxis),
      add_right_comm (p.corner + axisStep 1 p.lowAxis) γ (axisStep 1 p.highAxis)]
  have h : ∃ q : ElementaryPlaquette 1, q.cornerSet = (shift γ).pointMap '' p.cornerSet :=
    ⟨_, hc⟩
  unfold LatticeSymmetry.plaquetteMap
  rw [dif_pos h]
  exact ElementaryPlaquette.cornerSet_injective one_pos (h.choose_spec.trans hc.symm)
theorem translateFace_add (p : ElementaryPlaquette 1) (γ δ : LatticePoint 1) :
    translateFace (translateFace p γ) δ = translateFace p (γ + δ) := by apply _root_.YangMills.Construction.TransferOperators.CubicPeriodSublattice.translateFace_translateFace <;> assumption
theorem translateFace_zero (p : ElementaryPlaquette 1) : translateFace p 0 = p :=
  ElementaryPlaquette.ext (add_zero _) rfl rfl
theorem faceClass_translateFace (P : PeriodSublattice 1) (p : ElementaryPlaquette 1)
    {γ : LatticePoint 1} (hγ : γ ∈ P.periods) :
    P.faceClass (translateFace p γ) = P.faceClass p := by
  refine Subtype.ext ?_
  ext q
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨γ + δ, add_mem hγ hδ, ?_⟩
    simp only [plaquetteMap_shift, translateFace_add]
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ - γ, sub_mem hδ hγ, ?_⟩
    simp only [plaquetteMap_shift, translateFace_add]
    congr 1
    abel
theorem exists_period_of_faceClass_eq (P : PeriodSublattice 1) {p q : ElementaryPlaquette 1}
    (h : P.faceClass p = P.faceClass q) :
    ∃ γ ∈ P.periods, q = translateFace p γ := by
  have hq : q ∈ P.plaquetteOrbit q :=
    ⟨0, zero_mem _, by rw [plaquetteMap_shift, translateFace_zero]⟩
  have hq' : q ∈ P.plaquetteOrbit p := by
    have e : P.plaquetteOrbit p = P.plaquetteOrbit q := congrArg Subtype.val h
    rwa [e]
  obtain ⟨γ, hγ, e⟩ := hq'
  exact ⟨γ, hγ, by rw [e, plaquetteMap_shift]⟩
theorem linkClass_translate (P : PeriodSublattice 1) (b : PositiveLink 1) {γ : LatticePoint 1}
    (hγ : γ ∈ P.periods) : P.linkClass (b.translate γ) = P.linkClass b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.linkClass_translate <;> assumption
theorem lift_positiveLink (P : PeriodSublattice 1) (U : P.QuotientField)
    (b : PositiveLink 1) : P.lift U b.1 = U (P.linkClass b) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.lift_apply_positive <;> assumption
theorem lift_forwardFrom_add_period (P : PeriodSublattice 1) (U : P.QuotientField)
    (x : LatticePoint 1) (ν : Fin 4) {γ : LatticePoint 1} (hγ : γ ∈ P.periods) :
    P.lift U (Link.forwardFrom (x + γ) ν) = P.lift U (Link.forwardFrom x ν) := by
  have e : Link.forwardFrom (x + γ) ν = ((PositiveLink.forwardAt x ν).translate γ).1 :=
    InfiniteLattice.Link.ext rfl (add_right_comm _ _ _)
  rw [e, lift_positiveLink, linkClass_translate P _ hγ]
  exact (lift_positiveLink P U _).symm
theorem faceHolonomy_translateFace (P : PeriodSublattice 1) (U : P.QuotientField)
    (p : ElementaryPlaquette 1) {γ : LatticePoint 1} (hγ : γ ∈ P.periods) :
    faceHolonomy (P.lift U) (translateFace p γ) = faceHolonomy (P.lift U) p := by
  have h₁ : (translateFace p γ).corner = p.corner + γ := rfl
  have h₂ : (translateFace p γ).lowAxis = p.lowAxis := rfl
  have h₃ : (translateFace p γ).highAxis = p.highAxis := rfl
  unfold faceHolonomy
  rw [h₁, h₂, h₃, add_right_comm p.corner γ (axisStep 1 p.lowAxis),
    add_right_comm p.corner γ (axisStep 1 p.highAxis), lift_forwardFrom_add_period P U _ _ hγ,
    lift_forwardFrom_add_period P U _ _ hγ, lift_forwardFrom_add_period P U _ _ hγ,
    lift_forwardFrom_add_period P U _ _ hγ]
theorem quotientFaceEnergy_faceClass (P : PeriodSublattice 1) (U : P.QuotientField)
    (p : ElementaryPlaquette 1) :
    P.quotientFaceEnergy U (P.faceClass p) = faceEnergy (P.lift U) p := by
  obtain ⟨γ, hγ, e⟩ := (P.quotientPlaquette_nonempty (P.faceClass p)).some_mem
  unfold PeriodSublattice.quotientFaceEnergy
  rw [e, plaquetteMap_shift]
  unfold faceEnergy
  rw [faceHolonomy_translateFace P U p hγ]
theorem level_add (ν : Fin 4) (x y : LatticePoint 1) :
    level ν (x + y) = level ν x + level ν y := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.level_add <;> assumption
theorem level_zsmul_axisStep (ν : Fin 4) (j : ℤ) :
    level ν (j • axisStep 1 μ) = if ν = μ then j else 0 := by apply _root_.YangMills.Construction.TransferOperators.ExpShiftIntegrand.level_zsmul_axisStep <;> assumption
theorem level_pointAtLevel (j : ℤ) (y : SliceSite μ) :
    level μ (pointAtLevel μ j y) = j := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.level_pointAtLevel <;> assumption
theorem pointAtLevel_level_slicePart (x : LatticePoint 1) :
    pointAtLevel μ (level μ x) (slicePart μ x) = x := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.pointAtLevel_level_slicePart <;> assumption
theorem mem_periods_of_cast_level (Γ : CubicPeriodSublattice) {x : LatticePoint 1}
    (h : ∀ ν, ((level ν x : ℤ) : ZMod Γ.side) = 0) : x ∈ Γ.lattice.periods := by
  have h₀ : ∀ ν, level ν (0 : LatticePoint 1) = 0 := fun ν => by
    apply Int.cast_injective (α := ℝ)
    rw [level_cast]
    simp
  have := Γ.sub_mem_periods (x := 0) (x' := x) fun ν => by
    rw [h ν, h₀ ν]
    simp
  simpa using this
theorem cast_level_of_mem_periods (Γ : CubicPeriodSublattice) {γ : LatticePoint 1}
    (h : γ ∈ Γ.lattice.periods) (ν : Fin 4) : ((level ν γ : ℤ) : ZMod Γ.side) = 0 := by
  rw [Γ.periods_eq] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.mp h
  have e : level ν γ = (Γ.side : ℤ) * n ν := by
    apply Int.cast_injective (α := ℝ)
    rw [level_cast, hn ν]
    push_cast
    ring
  rw [e]
  simp
theorem zsmul_axisStep_mem_periods {j j' : ℤ} (h : Γ.levelClass j = Γ.levelClass j') :
    (j - j') • axisStep 1 μ ∈ Γ.lattice.periods := by
  refine mem_periods_of_cast_level Γ fun ν => ?_
  rw [level_zsmul_axisStep]
  split_ifs
  · have h' : ((j : ℤ) : ZMod Γ.side) = j' := h
    push_cast
    rw [h', sub_self]
  · simp
theorem levelClass_levelRep (c : ZMod Γ.side) :
    Γ.levelClass (Γ.levelRep c) = c := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.cast_levelRep <;> assumption
theorem levelClass_add_one (j : ℤ) : Γ.levelClass (j + 1) = Γ.levelClass j + 1 := by
  change ((j + 1 : ℤ) : ZMod Γ.side) = (j : ZMod Γ.side) + 1
  push_cast
  rfl
theorem levelClass_eq_of_add_period {j j' : ℤ} {y y' : SliceSite μ} {γ : LatticePoint 1}
    (hγ : γ ∈ Γ.lattice.periods) (h : pointAtLevel μ j' y' = pointAtLevel μ j y + γ) :
    Γ.levelClass j = Γ.levelClass j' := by
  have e := congrArg (level μ) h
  rw [level_add, level_pointAtLevel, level_pointAtLevel] at e
  change ((j : ℤ) : ZMod Γ.side) = (j' : ℤ)
  rw [e, Int.cast_add, cast_level_of_mem_periods Γ hγ, add_zero]
theorem axisStep_injective {ρ ρ' : Fin 4} (h : axisStep 1 ρ = axisStep 1 ρ') : ρ = ρ' := by apply _root_.YangMills.Construction.InfiniteLattice.TwoLevels.axisStep_injective <;> assumption
theorem spatialQuotientLink_levelClass_linkClass (j : ℤ) (b : SliceLink μ) :
    Γ.spatialQuotientLink (Γ.levelClass j) (Γ.linkClass b) =
      Γ.lattice.linkClass (spatialLink μ j b) := by
  obtain ⟨γ, hγ, hb⟩ := Γ.mem_linkOrbit_linkRep b
  set b' := CubicPeriodSublattice.linkRep (Γ.linkClass b)
  set j' := Γ.levelRep (Γ.levelClass j) with hj'
  have hjj : Γ.levelClass j = Γ.levelClass j' := (levelClass_levelRep _).symm
  have hv : (j - j') • axisStep 1 μ + γ ∈ Γ.lattice.periods :=
    add_mem (zsmul_axisStep_mem_periods hjj) (AddSubgroup.mem_inf.mp hγ).1
  have e : spatialLink μ j b =
      (spatialLink μ j' b').translate ((j - j') • axisStep 1 μ + γ) := by
    have ht : b.1.initial = b'.1.initial + γ := congrArg Link.initial hb
    have hh : b.1.terminal = b'.1.terminal + γ := congrArg Link.terminal hb
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change j • axisStep 1 μ + b.1.initial =
        j' • axisStep 1 μ + b'.1.initial + ((j - j') • axisStep 1 μ + γ)
      rw [ht, sub_smul]
      abel
    · change j • axisStep 1 μ + b.1.terminal =
        j' • axisStep 1 μ + b'.1.terminal + ((j - j') • axisStep 1 μ + γ)
      rw [hh, sub_smul]
      abel
  change Γ.lattice.linkClass (spatialLink μ j' b') = _
  rw [e, linkClass_translate _ _ hv]
theorem temporalQuotientLink_levelClass_vertexClass (j : ℤ) (y : SliceSite μ) :
    Γ.temporalQuotientLink (Γ.levelClass j) (Γ.vertexClass y) =
      Γ.lattice.linkClass (temporalLink μ j y) := by
  have hy : y ∈ Γ.vertexOrbit μ (CubicPeriodSublattice.vertexRep (Γ.vertexClass y)) := by
    have e : Γ.vertexOrbit μ (CubicPeriodSublattice.vertexRep (Γ.vertexClass y)) =
        Γ.vertexOrbit μ y := (Γ.vertexClass y).2.choose_spec
    rw [e]
    exact ⟨0, zero_mem _, (add_zero _).symm⟩
  obtain ⟨γ, hγ, hy⟩ := hy
  set y' := CubicPeriodSublattice.vertexRep (Γ.vertexClass y)
  set j' := Γ.levelRep (Γ.levelClass j) with hj'
  have hjj : Γ.levelClass j = Γ.levelClass j' := (levelClass_levelRep _).symm
  have hv : (j - j') • axisStep 1 μ + γ ∈ Γ.lattice.periods :=
    add_mem (zsmul_axisStep_mem_periods hjj) (AddSubgroup.mem_inf.mp hγ).1
  have e : temporalLink μ j y =
      (temporalLink μ j' y').translate ((j - j') • axisStep 1 μ + γ) := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change j • axisStep 1 μ + (y : LatticePoint 1) =
        j' • axisStep 1 μ + (y' : LatticePoint 1) + ((j - j') • axisStep 1 μ + γ)
      rw [hy, sub_smul]
      abel
    · change (j + 1) • axisStep 1 μ + (y : LatticePoint 1) =
        (j' + 1) • axisStep 1 μ + (y' : LatticePoint 1) + ((j - j') • axisStep 1 μ + γ)
      rw [hy, sub_smul, add_smul, add_smul, one_smul]
      abel
  change Γ.lattice.linkClass (temporalLink μ j' y') = _
  rw [e, linkClass_translate _ _ hv]
theorem sliceField_apply (U : Γ.lattice.QuotientField) (j : ℤ) (b : SliceLink μ) :
    Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass b) =
      Γ.lattice.lift U (spatialLink μ j b).1 := by
  rw [lift_positiveLink]
  exact congrArg U (spatialQuotientLink_levelClass_linkClass j b)
theorem temporalSliceField_apply (U : Γ.lattice.QuotientField) (j : ℤ) (y : SliceSite μ) :
    Γ.temporalSliceField (μ := μ) U (Γ.levelClass j) (Γ.vertexClass y) =
      Γ.lattice.lift U (temporalLink μ j y).1 := by
  rw [lift_positiveLink]
  exact congrArg U (temporalQuotientLink_levelClass_vertexClass j y)
theorem spatialLink_ofAxis (j : ℤ) (y : SliceSite μ) (ρ : Fin 4) (h : ρ ≠ μ) :
    (spatialLink μ j (SliceLink.ofAxis y ρ h)).1 = Link.forwardFrom (pointAtLevel μ j y) ρ :=
  InfiniteLattice.Link.ext rfl (add_assoc _ _ _).symm
theorem holonomyOfFamily_sliceField (U : Γ.lattice.QuotientField) (j : ℤ)
    (p : SlicePlaquette μ) :
    Γ.holonomyOfFamily p (Γ.sliceField (μ := μ) U (Γ.levelClass j)) =
      faceHolonomy (Γ.lattice.lift U) (shiftedPlaquette μ j p) := by
  have hm : (shiftedPlaquette μ j p).corner = pointAtLevel μ j p.origin := add_comm _ _
  have h₁ : (shiftedPlaquette μ j p).lowAxis = p.1.lowAxis := rfl
  have h₂ : (shiftedPlaquette μ j p).highAxis = p.1.highAxis := rfl
  change Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass p.bottomLink) *
      Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass p.rightLink) *
      (Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass p.topLink))⁻¹ *
      (Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass p.leftLink))⁻¹ = _
  rw [sliceField_apply, sliceField_apply, sliceField_apply, sliceField_apply]
  unfold faceHolonomy
  rw [hm, h₁, h₂]
  have e₁ : (spatialLink μ j p.bottomLink).1 =
      Link.forwardFrom (pointAtLevel μ j p.origin) p.1.lowAxis :=
    spatialLink_ofAxis j p.origin _ _
  have e₂ : (spatialLink μ j p.rightLink).1 =
      Link.forwardFrom (pointAtLevel μ j p.origin + axisStep 1 p.1.lowAxis) p.1.highAxis :=
    (spatialLink_ofAxis j _ _ _).trans
      (congrArg (fun x => Link.forwardFrom x p.1.highAxis) (add_assoc _ _ _).symm)
  have e₃ : (spatialLink μ j p.topLink).1 =
      Link.forwardFrom (pointAtLevel μ j p.origin + axisStep 1 p.1.highAxis) p.1.lowAxis :=
    (spatialLink_ofAxis j _ _ _).trans
      (congrArg (fun x => Link.forwardFrom x p.1.lowAxis) (add_assoc _ _ _).symm)
  have e₄ : (spatialLink μ j p.leftLink).1 =
      Link.forwardFrom (pointAtLevel μ j p.origin) p.1.highAxis :=
    spatialLink_ofAxis j p.origin _ _
  rw [e₁, e₂, e₃, e₄]
def temporalLoop (V : Link 1 → ComplexMatrix2.specialUnitary) (j : ℤ) (b : SliceLink μ) :
    ComplexMatrix2.specialUnitary :=
  V (spatialLink μ j b).1 * V (temporalLink μ j b.target).1 *
    (V (spatialLink μ (j + 1) b).1)⁻¹ * (V (temporalLink μ j b.source).1)⁻¹
theorem faceHolonomy_temporalPlaquette (V : Link 1 → ComplexMatrix2.specialUnitary) (j : ℤ)
    (b : SliceLink μ) :
    faceHolonomy V (temporalPlaquette μ j b) = temporalLoop V j b ∨
      faceHolonomy V (temporalPlaquette μ j b) = (temporalLoop V j b)⁻¹ := by
  have s₁ : (spatialLink μ j b).1 = Link.forwardFrom (pointAtLevel μ j b.source) b.axis :=
    InfiniteLattice.Link.ext rfl (pointAtLevel_target μ j b)
  have s₂ : (spatialLink μ (j + 1) b).1 =
      Link.forwardFrom (pointAtLevel μ j b.source + axisStep 1 μ) b.axis :=
    InfiniteLattice.Link.ext (pointAtLevel_succ μ j b.source) (by
      change pointAtLevel μ (j + 1) b.target =
        pointAtLevel μ j b.source + axisStep 1 μ + axisStep 1 b.axis
      rw [pointAtLevel_succ, pointAtLevel_target]
      exact add_right_comm _ _ _)
  have t₁ : (temporalLink μ j b.source).1 = Link.forwardFrom (pointAtLevel μ j b.source) μ :=
    InfiniteLattice.Link.ext rfl (pointAtLevel_succ μ j b.source)
  have t₂ : (temporalLink μ j b.target).1 =
      Link.forwardFrom (pointAtLevel μ j b.source + axisStep 1 b.axis) μ :=
    InfiniteLattice.Link.ext (pointAtLevel_target μ j b) (by
      change pointAtLevel μ (j + 1) b.target =
        pointAtLevel μ j b.source + axisStep 1 b.axis + axisStep 1 μ
      rw [pointAtLevel_succ, pointAtLevel_target])
  unfold temporalLoop temporalPlaquette faceOfPair
  rw [s₁, s₂, t₁, t₂]
  split_ifs with h
  · exact Or.inl rfl
  · refine Or.inr (Eq.trans (b := V (Link.forwardFrom (pointAtLevel μ j b.source) μ) *
      V (Link.forwardFrom (pointAtLevel μ j b.source + axisStep 1 μ) b.axis) *
      (V (Link.forwardFrom (pointAtLevel μ j b.source + axisStep 1 b.axis) μ))⁻¹ *
      (V (Link.forwardFrom (pointAtLevel μ j b.source) b.axis))⁻¹) rfl ?_)
    simp only [mul_inv_rev, inv_inv, mul_assoc]
theorem sliceField_mul_inv_orbitGaugeAct (U : Γ.lattice.QuotientField) (j : ℤ)
    (b : SliceLink μ) :
    Γ.sliceField (μ := μ) U (Γ.levelClass j) (Γ.linkClass b) *
        (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U (Γ.levelClass j))
          (Γ.sliceField (μ := μ) U (Γ.levelClass j + 1)) (Γ.linkClass b))⁻¹ =
      temporalLoop (Γ.lattice.lift U) j b := by
  rw [Γ.orbitGaugeAct_linkClass, ← levelClass_add_one, sliceField_apply,
    sliceField_apply, temporalSliceField_apply, temporalSliceField_apply]
  unfold temporalLoop
  simp only [mul_inv_rev, inv_inv, mul_assoc]
variable (Γ μ) in
def faceLabel : (ZMod Γ.side × Γ.FaceOrbits μ) ⊕ (ZMod Γ.side × Γ.LinkOrbits μ) →
    Γ.lattice.QuotientPlaquette
  | .inl t => Γ.lattice.faceClass (shiftedPlaquette μ (Γ.levelRep t.1)
      (CubicPeriodSublattice.faceRep t.2))
  | .inr t => Γ.lattice.faceClass (temporalPlaquette μ (Γ.levelRep t.1)
      (CubicPeriodSublattice.linkRep t.2))
theorem faceOfPair_corner (x : LatticePoint 1) (ρ ν : Fin 4) (h : ρ ≠ ν) :
    (faceOfPair x ρ ν h).corner = x := by
  unfold faceOfPair
  split_ifs <;> rfl
theorem faceOfPair_add (x γ : LatticePoint 1) (ρ ν : Fin 4) (h : ρ ≠ ν) :
    faceOfPair (x + γ) ρ ν h = translateFace (faceOfPair x ρ ν h) γ := by
  unfold faceOfPair
  split_ifs <;> rfl
theorem faceOfPair_congr {x x' : LatticePoint 1} {ρ ρ' ν : Fin 4} (hx : x = x') (hρ : ρ = ρ')
    (h : ρ ≠ ν) (h' : ρ' ≠ ν) : faceOfPair x ρ ν h = faceOfPair x' ρ' ν h' := by
  subst hx
  subst hρ
  rfl
theorem eq_of_faceOfPair_axes {x x' : LatticePoint 1} {ρ ρ' ν : Fin 4} (h : ρ ≠ ν)
    (h' : ρ' ≠ ν)
    (h₁ : (faceOfPair x ρ ν h).lowAxis = (faceOfPair x' ρ' ν h').lowAxis)
    (h₂ : (faceOfPair x ρ ν h).highAxis = (faceOfPair x' ρ' ν h').highAxis) : ρ = ρ' := by
  unfold faceOfPair at h₁ h₂
  split_ifs at h₁ h₂ <;> simp only [face] at h₁ h₂
  · exact h₁
  · exact absurd h₁ h
  · exact absurd h₁.symm h'
  · exact h₂
theorem temporalPlaquette_has_axis (j : ℤ) (b : SliceLink μ) :
    (temporalPlaquette μ j b).lowAxis = μ ∨ (temporalPlaquette μ j b).highAxis = μ := by
  unfold temporalPlaquette faceOfPair
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem axis_eq_of_translateLink {b b' : SliceLink μ} {γ : LatticePoint 1}
    (h : b'.1 = translateLink b.1 γ) : b'.axis = b.axis := by
  apply axisStep_injective
  rw [← b'.terminal_sub_initial, ← b.terminal_sub_initial, h]
  exact add_sub_add_right_eq_sub _ _ _
theorem faceOrbit_faceRep (q : Γ.FaceOrbits μ) :
    Γ.faceOrbit μ (CubicPeriodSublattice.faceRep q) = q.1 :=
  q.2.choose_spec
theorem linkOrbit_linkRep (e : Γ.LinkOrbits μ) :
    Γ.linkOrbit μ (CubicPeriodSublattice.linkRep e) = e.1 :=
  e.2.choose_spec
theorem self_mem_faceOrbit (p : SlicePlaquette μ) : p ∈ Γ.faceOrbit μ p :=
  ⟨0, zero_mem _, (translateFace_zero p.1).symm⟩
theorem faceClass_shiftedPlaquette (j : ℤ) (p : SlicePlaquette μ) :
    Γ.lattice.faceClass (shiftedPlaquette μ (Γ.levelRep (Γ.levelClass j))
        (CubicPeriodSublattice.faceRep (Γ.faceClass p))) =
      Γ.lattice.faceClass (shiftedPlaquette μ j p) := by
  have hp : p ∈ Γ.faceOrbit μ (CubicPeriodSublattice.faceRep (Γ.faceClass p)) := by
    rw [faceOrbit_faceRep]
    exact self_mem_faceOrbit p
  obtain ⟨γ, hγ, hb⟩ := hp
  set p' := CubicPeriodSublattice.faceRep (Γ.faceClass p)
  set j' := Γ.levelRep (Γ.levelClass j) with hj'
  have hjj : Γ.levelClass j = Γ.levelClass j' := (levelClass_levelRep _).symm
  have hv : (j - j') • axisStep 1 μ + γ ∈ Γ.lattice.periods :=
    add_mem (zsmul_axisStep_mem_periods hjj) (AddSubgroup.mem_inf.mp hγ).1
  have e : shiftedPlaquette μ j p =
      translateFace (shiftedPlaquette μ j' p') ((j - j') • axisStep 1 μ + γ) := by
    have ht : p.1.corner = p'.1.corner + γ := congrArg ElementaryPlaquette.corner hb
    have hf : p.1.lowAxis = p'.1.lowAxis := by
      have t := congrArg ElementaryPlaquette.lowAxis hb
      exact t
    have hs : p.1.highAxis = p'.1.highAxis := by
      have t := congrArg ElementaryPlaquette.highAxis hb
      exact t
    refine ElementaryPlaquette.ext ?_ hf hs
    change p.1.corner + j • axisStep 1 μ =
      p'.1.corner + j' • axisStep 1 μ + ((j - j') • axisStep 1 μ + γ)
    rw [ht, sub_smul]
    abel
  rw [e, faceClass_translateFace _ _ hv]
theorem faceClass_temporalPlaquette (j : ℤ) (b : SliceLink μ) :
    Γ.lattice.faceClass (temporalPlaquette μ (Γ.levelRep (Γ.levelClass j))
        (CubicPeriodSublattice.linkRep (Γ.linkClass b))) =
      Γ.lattice.faceClass (temporalPlaquette μ j b) := by
  obtain ⟨γ, hγ, hb⟩ := Γ.mem_linkOrbit_linkRep b
  set b' := CubicPeriodSublattice.linkRep (Γ.linkClass b)
  set j' := Γ.levelRep (Γ.levelClass j) with hj'
  have hjj : Γ.levelClass j = Γ.levelClass j' := (levelClass_levelRep _).symm
  have hv : (j - j') • axisStep 1 μ + γ ∈ Γ.lattice.periods :=
    add_mem (zsmul_axisStep_mem_periods hjj) (AddSubgroup.mem_inf.mp hγ).1
  have e : temporalPlaquette μ j b =
      translateFace (temporalPlaquette μ j' b') ((j - j') • axisStep 1 μ + γ) := by
    have ht : b.1.initial = b'.1.initial + γ := congrArg Link.initial hb
    unfold temporalPlaquette
    rw [← faceOfPair_add]
    refine faceOfPair_congr ?_ (axis_eq_of_translateLink hb) _ _
    change j • axisStep 1 μ + b.1.initial =
      j' • axisStep 1 μ + b'.1.initial + ((j - j') • axisStep 1 μ + γ)
    rw [ht, sub_smul]
    abel
  rw [e, faceClass_translateFace _ _ hv]
theorem faceLabel_surjective : Function.Surjective (faceLabel Γ μ) := by
  rintro ⟨_, p, rfl⟩
  change ∃ t, faceLabel Γ μ t = Γ.lattice.faceClass p
  have hx := pointAtLevel_level_slicePart (μ := μ) p.corner
  set j := level μ p.corner
  set y := slicePart μ p.corner
  by_cases hμ : p.lowAxis = μ ∨ p.highAxis = μ
  · obtain ⟨ρ, hρ, hp⟩ : ∃ (ρ : Fin 4) (hρ : ρ ≠ μ), faceOfPair p.corner ρ μ hρ = p := by
      have hlt := p.lowAxis_lt_highAxis
      rcases hμ with h | h
      · have hne : p.highAxis ≠ μ := fun e => by
          rw [h, e] at hlt
          exact lt_irrefl _ hlt
        refine ⟨p.highAxis, hne, ?_⟩
        unfold faceOfPair
        rw [dif_neg (by rw [← h]; exact not_lt.mpr hlt.le)]
        exact ElementaryPlaquette.ext rfl h.symm rfl
      · have hne : p.lowAxis ≠ μ := fun e => by
          rw [h, e] at hlt
          exact lt_irrefl _ hlt
        refine ⟨p.lowAxis, hne, ?_⟩
        unfold faceOfPair
        rw [dif_pos (by rw [← h]; exact hlt)]
        exact ElementaryPlaquette.ext rfl rfl h.symm
    have hd : (SliceLink.ofAxis y ρ hρ).axis = ρ := by
      apply axisStep_injective
      rw [← (SliceLink.ofAxis y ρ hρ).terminal_sub_initial]
      exact add_sub_cancel_left _ _
    have e : temporalPlaquette μ j (SliceLink.ofAxis y ρ hρ) = p := by
      unfold temporalPlaquette
      rw [← hp]
      exact faceOfPair_congr hx hd _ _
    refine ⟨.inr (Γ.levelClass j, Γ.linkClass (SliceLink.ofAxis y ρ hρ)), ?_⟩
    change Γ.lattice.faceClass _ = _
    rw [faceClass_temporalPlaquette, e]
  · have h₁ : p.lowAxis ≠ μ := fun e => hμ (Or.inl e)
    have h₂ : p.highAxis ≠ μ := fun e => hμ (Or.inr e)
    let q : SlicePlaquette μ :=
      ⟨face (y : LatticePoint 1) p.lowAxis p.highAxis p.lowAxis_lt_highAxis, by
        intro c hc
        simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact y.2
        · exact add_axisStep_mem_sliceLattice y.2 h₁
        · exact add_axisStep_mem_sliceLattice (add_axisStep_mem_sliceLattice y.2 h₁) h₂
        · exact add_axisStep_mem_sliceLattice y.2 h₂⟩
    have e : shiftedPlaquette μ j q = p :=
      ElementaryPlaquette.ext ((add_comm _ _).trans hx) rfl rfl
    refine ⟨.inl (Γ.levelClass j, Γ.faceClass q), ?_⟩
    change Γ.lattice.faceClass _ = _
    rw [faceClass_shiftedPlaquette, e]
theorem eq_of_levelClass_levelRep_eq {c c' : ZMod Γ.side}
    (h : Γ.levelClass (Γ.levelRep c) = Γ.levelClass (Γ.levelRep c')) : c = c' := by
  rwa [levelClass_levelRep, levelClass_levelRep] at h
theorem faceLabel_injective : Function.Injective (faceLabel Γ μ) := by
  rintro (⟨c, q⟩ | ⟨c, e⟩) (⟨c', q'⟩ | ⟨c', e'⟩) h
  · obtain ⟨γ, hγ, hp⟩ := exists_period_of_faceClass_eq _ h
    set p := CubicPeriodSublattice.faceRep q
    set p' := CubicPeriodSublattice.faceRep q'
    have hb : pointAtLevel μ (Γ.levelRep c') p'.origin =
        pointAtLevel μ (Γ.levelRep c) p.origin + γ := by
      have e₀ : p'.1.corner + Γ.levelRep c' • axisStep 1 μ =
          p.1.corner + Γ.levelRep c • axisStep 1 μ + γ :=
        congrArg ElementaryPlaquette.corner hp
      change Γ.levelRep c' • axisStep 1 μ + p'.1.corner =
        Γ.levelRep c • axisStep 1 μ + p.1.corner + γ
      rw [add_comm, e₀, add_comm p.1.corner]
    have hc : c = c' := eq_of_levelClass_levelRep_eq (levelClass_eq_of_add_period hγ hb)
    subst hc
    have hy : (p'.origin : LatticePoint 1) = p.origin + γ :=
      add_left_cancel (hb.trans (add_assoc _ _ _))
    have hγ' : γ ∈ Γ.slicePeriods μ := by
      have e₀ : γ = (p'.origin : LatticePoint 1) - p.origin := by
        rw [hy]
        abel
      exact AddSubgroup.mem_inf.mpr ⟨hγ, e₀ ▸ (sliceLattice μ).sub_mem p'.origin.2 p.origin.2⟩
    have hf : p'.1.lowAxis = p.1.lowAxis := by
      have t := congrArg ElementaryPlaquette.lowAxis hp
      exact t
    have hs : p'.1.highAxis = p.1.highAxis := by
      have t := congrArg ElementaryPlaquette.highAxis hp
      exact t
    have hm : p' ∈ Γ.faceOrbit μ p := ⟨γ, hγ', ElementaryPlaquette.ext hy hf hs⟩
    have ho := Γ.faceOrbit_eq_of_mem hm
    have hq : q' = q := Subtype.ext (by
      rw [← faceOrbit_faceRep q', ← faceOrbit_faceRep q]
      exact ho)
    rw [hq]
  · exfalso
    obtain ⟨γ, -, hp⟩ := exists_period_of_faceClass_eq _ h
    have h₁ := congrArg ElementaryPlaquette.lowAxis hp
    have h₂ := congrArg ElementaryPlaquette.highAxis hp
    rcases temporalPlaquette_has_axis (μ := μ) (Γ.levelRep c')
      (CubicPeriodSublattice.linkRep e') with d | d
    · exact SlicePlaquette.lowAxis_ne (CubicPeriodSublattice.faceRep q) (h₁.symm.trans d)
    · exact SlicePlaquette.highAxis_ne (CubicPeriodSublattice.faceRep q) (h₂.symm.trans d)
  · exfalso
    obtain ⟨γ, -, hp⟩ := exists_period_of_faceClass_eq _ h.symm
    have h₁ := congrArg ElementaryPlaquette.lowAxis hp
    have h₂ := congrArg ElementaryPlaquette.highAxis hp
    rcases temporalPlaquette_has_axis (μ := μ) (Γ.levelRep c)
      (CubicPeriodSublattice.linkRep e) with d | d
    · exact SlicePlaquette.lowAxis_ne (CubicPeriodSublattice.faceRep q') (h₁.symm.trans d)
    · exact SlicePlaquette.highAxis_ne (CubicPeriodSublattice.faceRep q') (h₂.symm.trans d)
  · obtain ⟨γ, hγ, hp⟩ := exists_period_of_faceClass_eq _ h
    set b := CubicPeriodSublattice.linkRep e
    set b' := CubicPeriodSublattice.linkRep e'
    have hd : b.axis = b'.axis :=
      eq_of_faceOfPair_axes _ _ (congrArg ElementaryPlaquette.lowAxis hp).symm
        (congrArg ElementaryPlaquette.highAxis hp).symm
    have hb : pointAtLevel μ (Γ.levelRep c') b'.source =
        pointAtLevel μ (Γ.levelRep c) b.source + γ := by
      have e₀ := congrArg ElementaryPlaquette.corner hp
      unfold temporalPlaquette at e₀
      rw [faceOfPair_corner] at e₀
      rw [e₀]
      change (faceOfPair _ _ _ _).corner + γ = _
      rw [faceOfPair_corner]
    have hc : c = c' := eq_of_levelClass_levelRep_eq (levelClass_eq_of_add_period hγ hb)
    subst hc
    have hy : (b'.source : LatticePoint 1) = b.source + γ :=
      add_left_cancel (hb.trans (add_assoc _ _ _))
    have hγ' : γ ∈ Γ.slicePeriods μ := by
      have e₀ : γ = (b'.source : LatticePoint 1) - b.source := by
        rw [hy]
        abel
      exact AddSubgroup.mem_inf.mpr ⟨hγ, e₀ ▸ (sliceLattice μ).sub_mem b'.source.2 b.source.2⟩
    have hm : b' ∈ Γ.linkOrbit μ b := by
      refine ⟨γ, hγ', InfiniteLattice.Link.ext hy ?_⟩
      have e₁ : b.1.terminal = b.1.initial + axisStep 1 b.axis := by
        rw [← b.terminal_sub_initial]
        abel
      have e₂ : b'.1.terminal = b'.1.initial + axisStep 1 b'.axis := by
        rw [← b'.terminal_sub_initial]
        abel
      change b'.1.terminal = b.1.terminal + γ
      rw [e₁, e₂, ← hd]
      change (b'.source : LatticePoint 1) + _ = _
      rw [hy]
      exact add_right_comm _ _ _
    have ho := Γ.linkOrbit_eq_of_mem hm
    have hq : e' = e := Subtype.ext (by
      rw [← linkOrbit_linkRep e', ← linkOrbit_linkRep e]
      exact ho)
    rw [hq]
theorem ofReal_faceEnergy (hw : TraceAndSingleBondWeight)
    (V : Link 1 → ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette 1) :
    ((faceEnergy V p : ℝ) : ℂ) =
      1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace
        ((faceHolonomy V p : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
  have him := (hw.1.2 (faceHolonomy V p)).2.2.2.2.2.1
  unfold faceEnergy
  apply Complex.ext <;> simp [him]
theorem boltzmannWeight_eq_prod (hw : TraceAndSingleBondWeight) (β : ℝ)
    (Γ : CubicPeriodSublattice) (μ : Fin 4) (U : Γ.lattice.QuotientField) :
    ((Γ.lattice.boltzmannWeight β U : ℝ) : ℂ) =
      ∏ j : ZMod Γ.side,
        Complex.exp (-Γ.sliceEnergy β (Γ.sliceField (μ := μ) U j)) *
          linkProductKernel β (Γ.sliceField (μ := μ) U j)
            (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U j)
              (Γ.sliceField (μ := μ) U (j + 1))) := by
  classical
  let _ : Fintype (Γ.FaceOrbits μ) := Fintype.ofFinite _
  let _ : Fintype (Γ.LinkOrbits μ) := Fintype.ofFinite _
  let A : ZMod Γ.side → Γ.FaceOrbits μ → ℂ := fun c q =>
    1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((Γ.orbitHolonomy q
      (Γ.sliceField (μ := μ) U c) : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
  let B : ZMod Γ.side → Γ.LinkOrbits μ → ℂ := fun c e =>
    1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((Γ.sliceField (μ := μ) U c e *
      (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U c)
        (Γ.sliceField (μ := μ) U (c + 1)) e)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
  have hA : ∀ c q,
      ((Γ.lattice.quotientFaceEnergy U (faceLabel Γ μ (.inl (c, q))) : ℝ) : ℂ) = A c q := by
    intro c q
    change ((Γ.lattice.quotientFaceEnergy U (Γ.lattice.faceClass _) : ℝ) : ℂ) = _
    rw [quotientFaceEnergy_faceClass, ofReal_faceEnergy hw]
    have k := holonomyOfFamily_sliceField (Γ := Γ) U (Γ.levelRep c)
      (CubicPeriodSublattice.faceRep q)
    rw [levelClass_levelRep] at k
    change _ = 1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((Γ.holonomyOfFamily
      (CubicPeriodSublattice.faceRep q)
        (Γ.sliceField (μ := μ) U c) : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
    rw [k]
  have hB : ∀ c e,
      ((Γ.lattice.quotientFaceEnergy U (faceLabel Γ μ (.inr (c, e))) : ℝ) : ℂ) = B c e := by
    intro c e
    change ((Γ.lattice.quotientFaceEnergy U (Γ.lattice.faceClass _) : ℝ) : ℂ) = _
    rw [quotientFaceEnergy_faceClass, ofReal_faceEnergy hw]
    have k := sliceField_mul_inv_orbitGaugeAct (Γ := Γ) U (Γ.levelRep c)
      (CubicPeriodSublattice.linkRep e)
    rw [levelClass_levelRep, Γ.linkClass_linkRep] at k
    change _ = 1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((Γ.sliceField (μ := μ) U c e *
      (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U c)
        (Γ.sliceField (μ := μ) U (c + 1)) e)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
    rw [k]
    rcases faceHolonomy_temporalPlaquette (Γ.lattice.lift U)
      (Γ.levelRep c) (CubicPeriodSublattice.linkRep e) with h | h
    · rw [h]
    · rw [h, (hw.1.2 _).2.2.2.2.2.2.1]
  have hbij : Function.Bijective (faceLabel Γ μ) :=
    ⟨faceLabel_injective, faceLabel_surjective⟩
  have hsum : ((∑ᶠ p : Γ.lattice.QuotientPlaquette, Γ.lattice.quotientFaceEnergy U p : ℝ) : ℂ) =
      ∑ c, ∑ q, A c q + ∑ c, ∑ e, B c e := by
    have h₁ : ∑ᶠ p : Γ.lattice.QuotientPlaquette, Γ.lattice.quotientFaceEnergy U p =
        ∑ t, Γ.lattice.quotientFaceEnergy U (faceLabel Γ μ t) := by
      rw [← finsum_eq_sum_of_fintype]
      exact (finsum_eq_of_bijective (faceLabel Γ μ) hbij fun _ => rfl).symm
    rw [h₁, Complex.ofReal_sum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    simp only [hA, hB]
  have hV : ∀ c, Γ.sliceEnergy β (Γ.sliceField (μ := μ) U c) = (β : ℂ) * ∑ q, A c q := by
    intro c
    unfold CubicPeriodSublattice.sliceEnergy
    rw [finsum_eq_sum_of_fintype]
  have hK : ∀ c, linkProductKernel β (Γ.sliceField (μ := μ) U c)
      (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U c)
        (Γ.sliceField (μ := μ) U (c + 1))) =
      Complex.exp (∑ e, -(β : ℂ) * B c e) := by
    intro c
    unfold linkProductKernel singleBondWeight
    rw [finprod_eq_prod_of_fintype, Complex.exp_sum]
  simp only [hK, hV, ← Complex.exp_add]
  rw [← Complex.exp_sum]
  unfold PeriodSublattice.boltzmannWeight
  rw [Complex.ofReal_exp]
  congr 1
  rw [Complex.ofReal_mul, hsum, Complex.ofReal_neg, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => by ring)
    (Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _)
theorem boltzmannWeight_prod_slices (hw : TraceAndSingleBondWeight) :
    BoltzmannWeight.ProdSlicesStatement :=
  fun β _ μ Γ U => boltzmannWeight_eq_prod hw β Γ μ U
end TransferOperators.SliceProduct
end YangMills.Construction
end
