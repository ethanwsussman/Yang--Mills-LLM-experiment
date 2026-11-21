import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.TransferOperators
variable (μ : Fin 4)
def sliceLattice : AddSubgroup (LatticePoint 1) where
  carrier := {y | (y : AmbientSpace) μ = 0}
  add_mem' := by
    intro x y hx hy
    have hx' : (x : AmbientSpace) μ = 0 := hx
    have hy' : (y : AmbientSpace) μ = 0 := hy
    change (x : AmbientSpace) μ + (y : AmbientSpace) μ = 0
    rw [hx', hy', add_zero]
  zero_mem' := rfl
  neg_mem' := by
    intro x hx
    have hx' : (x : AmbientSpace) μ = 0 := hx
    change -(x : AmbientSpace) μ = 0
    rw [hx', neg_zero]
abbrev SliceSite : Type := ↥(sliceLattice μ)
variable {μ}
theorem mem_sliceLattice {y : LatticePoint 1} : y ∈ sliceLattice μ ↔ (y : AmbientSpace) μ = 0 :=
  Iff.rfl
theorem add_axisStep_mem_sliceLattice {y : LatticePoint 1} (hy : y ∈ sliceLattice μ) {ρ : Fin 4}
    (h : ρ ≠ μ) : y + axisStep 1 ρ ∈ sliceLattice μ := by
  have hy' : (y : AmbientSpace) μ = 0 := hy
  change (y : AmbientSpace) μ + (Pi.single ρ (1 : ℝ) : AmbientSpace) μ = 0
  rw [hy', Pi.single_eq_of_ne h.symm, add_zero]
def SliceSite.shift (y : SliceSite μ) (ρ : Fin 4) (h : ρ ≠ μ) : SliceSite μ :=
  ⟨y + axisStep 1 ρ, add_axisStep_mem_sliceLattice y.2 h⟩
variable (μ)
def pointAtLevel (j : ℤ) (y : SliceSite μ) : LatticePoint 1 := j • axisStep 1 μ + y
def level (x : LatticePoint 1) : ℤ := ⌊(x : AmbientSpace) μ⌋
theorem level_cast (x : LatticePoint 1) : ((level μ x : ℤ) : ℝ) = (x : AmbientSpace) μ := by
  obtain ⟨n, hn⟩ := x.2
  rw [level, hn μ, mul_one, Int.floor_intCast]
theorem coe_zsmul_axisStep_apply_self (j : ℤ) :
    ((j • axisStep 1 μ : LatticePoint 1) : AmbientSpace) μ = j := by
  change j • (Pi.single μ (1 : ℝ) : AmbientSpace) μ = j
  simp
def slicePart (x : LatticePoint 1) : SliceSite μ :=
  ⟨x - level μ x • axisStep 1 μ, by
    change (x : AmbientSpace) μ - ((level μ x • axisStep 1 μ : LatticePoint 1) : AmbientSpace) μ = 0
    rw [coe_zsmul_axisStep_apply_self, level_cast, sub_self]⟩
def IsSliceLink (b : Link 1) : Prop :=
  b.IsPositivelyOriented ∧ b.initial ∈ sliceLattice μ ∧ b.terminal ∈ sliceLattice μ
abbrev SliceLink : Type := {b : Link 1 // IsSliceLink μ b}
abbrev SlicePlaquette : Type :=
  {p : ElementaryPlaquette 1 // ∀ c ∈ p.cornerSet, c ∈ sliceLattice μ}
variable {μ}
def SliceLink.source (b : SliceLink μ) : SliceSite μ := ⟨b.1.initial, b.2.2.1⟩
def SliceLink.target (b : SliceLink μ) : SliceSite μ := ⟨b.1.terminal, b.2.2.2⟩
def SliceLink.toPositiveLink (b : SliceLink μ) : PositiveLink 1 := ⟨b.1, b.2.1⟩
def SliceLink.ofAxis (y : SliceSite μ) (ρ : Fin 4) (h : ρ ≠ μ) : SliceLink μ :=
  ⟨Link.forwardFrom (y : LatticePoint 1) ρ, ⟨ρ, add_sub_cancel_left _ _⟩, y.2,
    add_axisStep_mem_sliceLattice y.2 h⟩
def SliceLink.axis (b : SliceLink μ) : Fin 4 := b.2.1.choose
theorem SliceLink.terminal_sub_initial (b : SliceLink μ) :
    b.1.terminal - b.1.initial = axisStep 1 b.axis :=
  b.2.1.choose_spec
theorem SliceLink.axis_ne (b : SliceLink μ) : b.axis ≠ μ := by
  intro h
  have h₁ := congrFun (congrArg Subtype.val b.terminal_sub_initial) μ
  have ht : (b.1.initial : AmbientSpace) μ = 0 := b.2.2.1
  have hh : (b.1.terminal : AmbientSpace) μ = 0 := b.2.2.2
  change (b.1.terminal : AmbientSpace) μ - (b.1.initial : AmbientSpace) μ =
    (Pi.single b.axis (1 : ℝ) : AmbientSpace) μ at h₁
  rw [ht, hh, h, Pi.single_eq_same] at h₁
  norm_num at h₁
namespace SlicePlaquette
variable (p : SlicePlaquette μ)
def origin : SliceSite μ := ⟨p.1.corner, p.2 _ (by simp [ElementaryPlaquette.cornerSet])⟩
theorem lowAxis_ne : p.1.lowAxis ≠ μ := by
  intro h
  have h₁ : ((p.1.corner + axisStep 1 p.1.lowAxis : LatticePoint 1) : AmbientSpace) μ = 0 :=
    p.2 _ (by simp [ElementaryPlaquette.cornerSet])
  have h₂ : (p.1.corner : AmbientSpace) μ = 0 := p.origin.2
  change (p.1.corner : AmbientSpace) μ + (Pi.single p.1.lowAxis (1 : ℝ) : AmbientSpace) μ = 0 at h₁
  rw [h₂, h, Pi.single_eq_same] at h₁
  norm_num at h₁
theorem highAxis_ne : p.1.highAxis ≠ μ := by
  intro h
  have h₁ : ((p.1.corner + axisStep 1 p.1.highAxis : LatticePoint 1) : AmbientSpace) μ = 0 :=
    p.2 _ (by simp [ElementaryPlaquette.cornerSet])
  have h₂ : (p.1.corner : AmbientSpace) μ = 0 := p.origin.2
  change (p.1.corner : AmbientSpace) μ + (Pi.single p.1.highAxis (1 : ℝ) : AmbientSpace) μ = 0 at h₁
  rw [h₂, h, Pi.single_eq_same] at h₁
  norm_num at h₁
def bottomLink : SliceLink μ := SliceLink.ofAxis p.origin p.1.lowAxis p.lowAxis_ne
def rightLink : SliceLink μ :=
  SliceLink.ofAxis (p.origin.shift p.1.lowAxis p.lowAxis_ne) p.1.highAxis p.highAxis_ne
def topLink : SliceLink μ :=
  SliceLink.ofAxis (p.origin.shift p.1.highAxis p.highAxis_ne) p.1.lowAxis p.lowAxis_ne
def leftLink : SliceLink μ := SliceLink.ofAxis p.origin p.1.highAxis p.highAxis_ne
def links : Set (SliceLink μ) := {p.bottomLink, p.rightLink, p.topLink, p.leftLink}
end SlicePlaquette
variable (μ)
theorem pointAtLevel_sub_pointAtLevel (j : ℤ) (y y' : SliceSite μ) :
    pointAtLevel μ j y' - pointAtLevel μ j y = (y' : LatticePoint 1) - y := by
  simp only [pointAtLevel]
  abel
def spatialLink (j : ℤ) (b : SliceLink μ) : PositiveLink 1 :=
  ⟨⟨pointAtLevel μ j b.source, pointAtLevel μ j b.target, b.axis, Or.inl (by
      rw [pointAtLevel_sub_pointAtLevel]
      exact b.terminal_sub_initial)⟩,
    b.axis, by
      change pointAtLevel μ j b.target - pointAtLevel μ j b.source = _
      rw [pointAtLevel_sub_pointAtLevel]
      exact b.terminal_sub_initial⟩
theorem pointAtLevel_succ (j : ℤ) (y : SliceSite μ) :
    pointAtLevel μ (j + 1) y = pointAtLevel μ j y + axisStep 1 μ := by
  simp only [pointAtLevel, add_smul, one_smul]
  abel
def temporalLink (j : ℤ) (y : SliceSite μ) : PositiveLink 1 :=
  ⟨⟨pointAtLevel μ j y, pointAtLevel μ (j + 1) y, μ, Or.inl (by
      rw [pointAtLevel_succ]
      abel)⟩,
    μ, by
      change pointAtLevel μ (j + 1) y - pointAtLevel μ j y = _
      rw [pointAtLevel_succ]
      abel⟩
def spatialLinkVariable (U : GaugeField 1) (j : ℤ) (b : SliceLink μ) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (spatialLink μ j b).1
def temporalLinkVariable (U : GaugeField 1) (j : ℤ) (y : SliceSite μ) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (temporalLink μ j y).1
def temporalPlaquette (j : ℤ) (b : SliceLink μ) : ElementaryPlaquette 1 :=
  CutoffLattice.faceOfPair (pointAtLevel μ j b.source) b.axis μ b.axis_ne
theorem pointAtLevel_target (j : ℤ) (b : SliceLink μ) :
    pointAtLevel μ j b.target = pointAtLevel μ j b.source + axisStep 1 b.axis := by
  have h := pointAtLevel_sub_pointAtLevel μ j b.source b.target
  have h' : ((b.target : SliceSite μ) : LatticePoint 1) - b.source = axisStep 1 b.axis :=
    b.terminal_sub_initial
  rw [h'] at h
  rw [← h]
  abel
theorem cornerSet_temporalPlaquette (j : ℤ) (b : SliceLink μ) :
    (temporalPlaquette μ j b).cornerSet =
      {pointAtLevel μ j b.source, pointAtLevel μ j b.target, pointAtLevel μ (j + 1) b.target,
        pointAtLevel μ (j + 1) b.source} := by
  rw [pointAtLevel_succ, pointAtLevel_succ, pointAtLevel_target]
  unfold temporalPlaquette CutoffLattice.faceOfPair CutoffLattice.face
  split_ifs with h
  · rfl
  · ext x
    simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff]
    rw [add_right_comm (pointAtLevel μ j b.source) (axisStep 1 μ) (axisStep 1 b.axis)]
    tauto
def shiftedPlaquette (j : ℤ) (p : SlicePlaquette μ) : ElementaryPlaquette 1 :=
  CutoffLattice.translateFace p.1 (j • axisStep 1 μ)
variable {μ}
def shiftedLinks (L : Set (Link 1)) (v : LatticePoint 1) : Set (Link 1) :=
  (fun b => CutoffLattice.translateLink b v) '' L
structure Stack where
  lower : ℤ
  upper : ℤ
  lower_lt_upper : lower < upper
namespace Stack
variable (S : Stack)
def levels : Set ℤ := Icc S.lower S.upper
variable (μ)
def parallelTransport (U : GaugeField 1) (j : ℤ) (y : SliceSite μ) :
    Matrices.ComplexMatrix2.specialUnitary :=
  ((List.range (j - S.lower).toNat).map fun k : ℕ =>
    temporalLinkVariable μ U (S.lower + (k : ℤ)) y).prod
def transportedLinkVariable (U : GaugeField 1) (j : ℤ) (b : SliceLink μ) :
    Matrices.ComplexMatrix2.specialUnitary :=
  S.parallelTransport μ U j b.source * spatialLinkVariable μ U j b *
    (S.parallelTransport μ U j b.target)⁻¹
def transportedRestriction (U : GaugeField 1) (j : ℤ) (B : Set (SliceLink μ)) :
    B → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => S.transportedLinkVariable μ U j b
end Stack
def linksWithin (v : Set (SliceSite μ)) : Set (SliceLink μ) :=
  {b | b.source ∈ v ∧ b.target ∈ v}
def Stack.linksOver (S : Stack) (v : Set (SliceSite μ)) : Set (PositiveLink 1) :=
  {c | (∃ j b, S.lower ≤ j ∧ j ≤ S.upper ∧ b ∈ linksWithin v ∧ c = spatialLink μ j b) ∨
    ∃ j y, S.lower ≤ j ∧ j < S.upper ∧ y ∈ v ∧ c = temporalLink μ j y}
variable (μ) in
structure Block where
  links : Finset (SliceLink μ)
  links_nonempty : links.Nonempty
namespace Block
variable (B : Block μ)
def vertices : Set (SliceSite μ) := {y | ∃ b ∈ B.links, y = b.source ∨ y = b.target}
def atLevel (j : ℤ) : Set (PositiveLink 1) := spatialLink μ j '' (B.links : Set (SliceLink μ))
def thickened : Set (SliceLink μ) :=
  (B.links : Set (SliceLink μ)) ∪
    {b | ∃ p : SlicePlaquette μ, b ∈ p.links ∧ ∃ b' ∈ B.links, b' ∈ p.links}
end Block
section GaugeAction
variable {v : Set (SliceSite μ)}
def gaugeAct {B : Set (SliceLink μ)} (hB : B ⊆ linksWithin v)
    (g : v → Matrices.ComplexMatrix2.specialUnitary) (u : B → Matrices.ComplexMatrix2.specialUnitary) :
    B → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => g ⟨b.1.source, (hB b.2).1⟩ * u b * (g ⟨b.1.target, (hB b.2).2⟩)⁻¹
def diagonalGaugeAct {I : Set (ℤ × SliceLink μ)} (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (g : v → Matrices.ComplexMatrix2.specialUnitary) (u : I → Matrices.ComplexMatrix2.specialUnitary) :
    I → Matrices.ComplexMatrix2.specialUnitary :=
  fun i => g ⟨i.1.2.source, (hI i.1 i.2).1⟩ * u i * (g ⟨i.1.2.target, (hI i.1 i.2).2⟩)⁻¹
def IsDiagonalGaugeInvariant {E : Type*} {I : Set (ℤ × SliceLink μ)}
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (Φ : (I → Matrices.ComplexMatrix2.specialUnitary) → E) :
    Prop :=
  ∀ (g : v → Matrices.ComplexMatrix2.specialUnitary) (u : I → Matrices.ComplexMatrix2.specialUnitary),
    Φ (diagonalGaugeAct hI g u) = Φ u
end GaugeAction
end YangMills.Construction.TransferOperators
end
