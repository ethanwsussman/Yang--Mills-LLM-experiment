import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import YangMills.Construction.TransferOperators.SquareRootOfTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators
theorem finite_range_of_invariant {X K : Type*} [Finite K] (f : X → Set X) (inv : X → K)
    (hf : ∀ x y, inv x = inv y → f x = f y) : Finite (Set.range f) := by
  classical
  let g : K → Set X := fun k => if hk : ∃ x, inv x = k then f hk.choose else ∅
  refine (Set.Finite.subset (Set.finite_range g) ?_).to_subtype
  rintro _ ⟨x, rfl⟩
  have hx : ∃ y, inv y = inv x := ⟨x, rfl⟩
  exact ⟨inv x, by simp only [g, dif_pos hx]; exact hf _ _ hx.choose_spec⟩
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice) (μ : Fin 4)
instance : NeZero Γ.side := ⟨by have := Γ.one_le_side; omega⟩
def slicePeriods : AddSubgroup (LatticePoint 1) := Γ.lattice.periods ⊓ sliceLattice μ
def vertexOrbit (x : SliceSite μ) : Set (SliceSite μ) :=
  {x' | ∃ γ ∈ Γ.slicePeriods μ, (x' : LatticePoint 1) = x + γ}
def linkOrbit (l : SliceLink μ) : Set (SliceLink μ) :=
  {l' | ∃ γ ∈ Γ.slicePeriods μ, l'.1 = CutoffLattice.translateLink l.1 γ}
def faceOrbit (p : SlicePlaquette μ) : Set (SlicePlaquette μ) :=
  {p' | ∃ γ ∈ Γ.slicePeriods μ, p'.1 = CutoffLattice.translateFace p.1 γ}
abbrev VertexOrbits : Type := Set.range (Γ.vertexOrbit μ)
abbrev LinkOrbits : Type := Set.range (Γ.linkOrbit μ)
abbrev FaceOrbits : Type := Set.range (Γ.faceOrbit μ)
variable {μ}
def vertexClass (x : SliceSite μ) : Γ.VertexOrbits μ := ⟨Γ.vertexOrbit μ x, x, rfl⟩
def linkClass (l : SliceLink μ) : Γ.LinkOrbits μ := ⟨Γ.linkOrbit μ l, l, rfl⟩
def faceClass (p : SlicePlaquette μ) : Γ.FaceOrbits μ := ⟨Γ.faceOrbit μ p, p, rfl⟩
variable {Γ}
def vertexRep (c : Γ.VertexOrbits μ) : SliceSite μ := c.2.choose
def linkRep (c : Γ.LinkOrbits μ) : SliceLink μ := c.2.choose
def faceRep (c : Γ.FaceOrbits μ) : SlicePlaquette μ := c.2.choose
theorem linkClass_linkRep (c : Γ.LinkOrbits μ) :
    Γ.linkClass (linkRep c) = c :=
  Subtype.ext c.2.choose_spec
variable (Γ)
theorem sub_mem_periods {x x' : LatticePoint 1}
    (hx : ∀ ν, ((level ν x : ℤ) : ZMod Γ.side) = (level ν x' : ℤ)) :
    x' - x ∈ Γ.lattice.periods := by
  rw [Γ.periods_eq]
  refine AddSubgroup.mem_addSubgroupOf.mpr ?_
  have hk : ∀ ν, ∃ k : ℤ, level ν x' - level ν x = (Γ.side : ℤ) * k := fun ν =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hx ν)
  choose k hk using hk
  refine ⟨k, fun ν => ?_⟩
  have e := congrArg (fun t : ℤ => (t : ℝ)) (hk ν)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, level_cast] at e
  change (x' : AmbientSpace) ν - (x : AmbientSpace) ν = _
  rw [e, mul_comm]
def coordResidues (x : LatticePoint 1) : Fin 4 → ZMod Γ.side := fun ν => (level ν x : ℤ)
theorem vertexOrbit_eq_of_sub_mem {x x' : SliceSite μ}
    (hx : (x' : LatticePoint 1) - x ∈ Γ.slicePeriods μ) : Γ.vertexOrbit μ x = Γ.vertexOrbit μ x' := by
  ext z
  constructor
  · rintro ⟨γ, hγ, hz⟩
    refine ⟨γ - ((x' : LatticePoint 1) - x), sub_mem hγ hx, ?_⟩
    rw [hz]
    abel
  · rintro ⟨γ, hγ, hz⟩
    refine ⟨γ + ((x' : LatticePoint 1) - x), add_mem hγ hx, ?_⟩
    rw [hz]
    abel
instance : Finite (Γ.VertexOrbits μ) :=
  finite_range_of_invariant (Γ.vertexOrbit μ) (fun x : SliceSite μ => Γ.coordResidues x) fun x x' hx =>
    Γ.vertexOrbit_eq_of_sub_mem
      (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem_periods (congrFun hx), (sliceLattice μ).sub_mem x'.2 x.2⟩)
theorem translateLink_translateLink (l : Link 1) (γ δ : LatticePoint 1) :
    CutoffLattice.translateLink (CutoffLattice.translateLink l γ) δ =
      CutoffLattice.translateLink l (γ + δ) :=
  Link.ext (add_assoc _ _ _) (add_assoc _ _ _)
theorem translateLink_zero (l : Link 1) : CutoffLattice.translateLink l 0 = l :=
  Link.ext (add_zero _) (add_zero _)
theorem linkOrbit_eq_of_mem {l l' : SliceLink μ} (hl : l' ∈ Γ.linkOrbit μ l) :
    Γ.linkOrbit μ l' = Γ.linkOrbit μ l := by
  obtain ⟨γ, hγ, hl⟩ := hl
  ext c
  constructor
  · rintro ⟨δ, hδ, hc⟩
    exact ⟨γ + δ, add_mem hγ hδ, by rw [hc, hl, translateLink_translateLink]⟩
  · rintro ⟨δ, hδ, hc⟩
    refine ⟨δ - γ, sub_mem hδ hγ, ?_⟩
    rw [hc, hl, translateLink_translateLink]
    congr 1
    abel
theorem self_mem_linkOrbit (l : SliceLink μ) : l ∈ Γ.linkOrbit μ l :=
  ⟨0, zero_mem _, (translateLink_zero l.1).symm⟩
instance : Finite (Γ.LinkOrbits μ) :=
  finite_range_of_invariant (Γ.linkOrbit μ)
    (fun l : SliceLink μ => (Γ.coordResidues (l.source : LatticePoint 1), l.axis)) fun l l' hl => by
    have h₁ : Γ.coordResidues (l.source : LatticePoint 1) = Γ.coordResidues (l'.source : LatticePoint 1) :=
      congrArg Prod.fst hl
    have h₂ : l.axis = l'.axis := congrArg Prod.snd hl
    have hm : l' ∈ Γ.linkOrbit μ l := by
      refine ⟨(l'.source : LatticePoint 1) - l.source,
        AddSubgroup.mem_inf.mpr
          ⟨Γ.sub_mem_periods (congrFun h₁), (sliceLattice μ).sub_mem l'.source.2 l.source.2⟩, ?_⟩
      have e₁ : l.1.terminal = l.1.initial + axisStep 1 l.axis := by
        rw [← l.terminal_sub_initial]
        abel
      have e₂ : l'.1.terminal = l'.1.initial + axisStep 1 l'.axis := by
        rw [← l'.terminal_sub_initial]
        abel
      refine Link.ext ?_ ?_
      · change l'.1.initial = l.1.initial + (l'.1.initial - l.1.initial)
        abel
      · change l'.1.terminal = l.1.terminal + (l'.1.initial - l.1.initial)
        rw [e₁, e₂, h₂]
        abel
    exact (Γ.linkOrbit_eq_of_mem hm).symm
theorem translateFace_translateFace (p : ElementaryPlaquette 1) (γ δ : LatticePoint 1) :
    CutoffLattice.translateFace (CutoffLattice.translateFace p γ) δ =
      CutoffLattice.translateFace p (γ + δ) :=
  ElementaryPlaquette.ext (add_assoc _ _ _) rfl rfl
theorem faceOrbit_eq_of_mem {p p' : SlicePlaquette μ} (hp : p' ∈ Γ.faceOrbit μ p) :
    Γ.faceOrbit μ p' = Γ.faceOrbit μ p := by
  obtain ⟨γ, hγ, hp⟩ := hp
  ext c
  constructor
  · rintro ⟨δ, hδ, hc⟩
    exact ⟨γ + δ, add_mem hγ hδ, by rw [hc, hp, translateFace_translateFace]⟩
  · rintro ⟨δ, hδ, hc⟩
    refine ⟨δ - γ, sub_mem hδ hγ, ?_⟩
    rw [hc, hp, translateFace_translateFace]
    congr 1
    abel
instance : Finite (Γ.FaceOrbits μ) :=
  finite_range_of_invariant (Γ.faceOrbit μ)
    (fun p : SlicePlaquette μ => (Γ.coordResidues p.1.corner, p.1.lowAxis, p.1.highAxis)) fun p p' hp => by
    have h₁ : Γ.coordResidues p.1.corner = Γ.coordResidues p'.1.corner := congrArg Prod.fst hp
    have h₂ : p.1.lowAxis = p'.1.lowAxis := congrArg (fun t => t.2.1) hp
    have h₃ : p.1.highAxis = p'.1.highAxis := congrArg (fun t => t.2.2) hp
    have hm : p' ∈ Γ.faceOrbit μ p := by
      refine ⟨p'.1.corner - p.1.corner, AddSubgroup.mem_inf.mpr
          ⟨Γ.sub_mem_periods (congrFun h₁), (sliceLattice μ).sub_mem p'.origin.2 p.origin.2⟩, ?_⟩
      refine ElementaryPlaquette.ext ?_ h₂.symm h₃.symm
      change p'.1.corner = p.1.corner + (p'.1.corner - p.1.corner)
      abel
    exact (Γ.faceOrbit_eq_of_mem hm).symm
theorem vertexClass_source_eq {l l' : SliceLink μ} (hl : l' ∈ Γ.linkOrbit μ l) :
    Γ.vertexClass l'.source = Γ.vertexClass l.source := by
  obtain ⟨γ, hγ, hl⟩ := hl
  refine Subtype.ext (Γ.vertexOrbit_eq_of_sub_mem ?_).symm
  have : l'.1.initial = l.1.initial + γ := congrArg Link.initial hl
  change l'.1.initial - l.1.initial ∈ _
  rw [this]
  simpa using hγ
theorem vertexClass_target_eq {l l' : SliceLink μ} (hl : l' ∈ Γ.linkOrbit μ l) :
    Γ.vertexClass l'.target = Γ.vertexClass l.target := by
  obtain ⟨γ, hγ, hl⟩ := hl
  refine Subtype.ext (Γ.vertexOrbit_eq_of_sub_mem ?_).symm
  have : l'.1.terminal = l.1.terminal + γ := congrArg Link.terminal hl
  change l'.1.terminal - l.1.terminal ∈ _
  rw [this]
  simpa using hγ
def orbitSource (c : Γ.LinkOrbits μ) : Γ.VertexOrbits μ := Γ.vertexClass (linkRep c).source
def orbitTarget (c : Γ.LinkOrbits μ) : Γ.VertexOrbits μ := Γ.vertexClass (linkRep c).target
theorem mem_linkOrbit_linkRep (l : SliceLink μ) :
    l ∈ Γ.linkOrbit μ (linkRep (Γ.linkClass l)) := by
  have hl : Γ.linkOrbit μ (linkRep (Γ.linkClass l)) = Γ.linkOrbit μ l :=
    congrArg Subtype.val (Γ.linkClass_linkRep (Γ.linkClass l))
  rw [hl]
  exact Γ.self_mem_linkOrbit l
theorem orbitSource_linkClass (l : SliceLink μ) :
    Γ.orbitSource (Γ.linkClass l) = Γ.vertexClass l.source :=
  (Γ.vertexClass_source_eq (Γ.mem_linkOrbit_linkRep l)).symm
theorem orbitTarget_linkClass (l : SliceLink μ) :
    Γ.orbitTarget (Γ.linkClass l) = Γ.vertexClass l.target :=
  (Γ.vertexClass_target_eq (Γ.mem_linkOrbit_linkRep l)).symm
def levelClass (j : ℤ) : ZMod Γ.side := j
def levelRep (c : ZMod Γ.side) : ℤ := (c.val : ℤ)
def spatialQuotientLink (c : ZMod Γ.side) (e : Γ.LinkOrbits μ) : Γ.lattice.QuotientLink :=
  Γ.lattice.linkClass (spatialLink μ (Γ.levelRep c) (linkRep e))
def temporalQuotientLink (c : ZMod Γ.side) (v : Γ.VertexOrbits μ) : Γ.lattice.QuotientLink :=
  Γ.lattice.linkClass (temporalLink μ (Γ.levelRep c) (vertexRep v))
def sliceField (U : Γ.lattice.QuotientField) (c : ZMod Γ.side) :
    Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary :=
  fun e => U (Γ.spatialQuotientLink c e)
def temporalSliceField (U : Γ.lattice.QuotientField) (c : ZMod Γ.side) :
    Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary :=
  fun v => U (Γ.temporalQuotientLink c v)
def orbitGaugeAct (g : Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary)
    (u : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) :
    Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary :=
  fun e => g (Γ.orbitSource e) * u e * (g (Γ.orbitTarget e))⁻¹
theorem orbitGaugeAct_linkClass (g : Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary)
    (u : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) (l : SliceLink μ) :
    Γ.orbitGaugeAct g u (Γ.linkClass l) =
      g (Γ.vertexClass l.source) * u (Γ.linkClass l) * (g (Γ.vertexClass l.target))⁻¹ := by
  rw [orbitGaugeAct, orbitSource_linkClass, orbitTarget_linkClass]
def holonomyOfFamily (p : SlicePlaquette μ) (u : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.specialUnitary :=
  plaquetteHolonomy p (S := univ) (subset_univ _) fun l => u (Γ.linkClass l.1)
def orbitHolonomy (c : Γ.FaceOrbits μ) (u : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.specialUnitary :=
  Γ.holonomyOfFamily (faceRep c) u
def sliceEnergy (β : ℝ) (u : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) : ℂ :=
  (β : ℂ) * ∑ᶠ c : Γ.FaceOrbits μ, (1 - (1 / 2 : ℂ) *
    ComplexMatrix2.fullTrace ((Γ.orbitHolonomy c u : ComplexMatrix2.specialUnitary) : ComplexMatrix2))
variable (μ)
abbrev SliceL2 : Type := HaarL2 (Γ.LinkOrbits μ)
variable {μ}
def IsGaugeRep (g : Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary)
    (T : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) : Prop :=
  ∀ φ : Γ.SliceL2 μ, (T φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ)
    =ᵐ[ComplexMatrix2.haarPi (Γ.LinkOrbits μ)]
    fun u => (φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ) (Γ.orbitGaugeAct g⁻¹ u)
def gaugeRep (g : Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary) : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  Classical.epsilon (Γ.IsGaugeRep g)
def IsGaugeProjection (T : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) : Prop :=
  ∀ φ : Γ.SliceL2 μ, (T φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ)
    =ᵐ[ComplexMatrix2.haarPi (Γ.LinkOrbits μ)]
    fun u => ∫ g, (φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ) (Γ.orbitGaugeAct g⁻¹ u)
      ∂ComplexMatrix2.haarPi (Γ.VertexOrbits μ)
variable (μ) in
def gaugeProjection : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ := Classical.epsilon (Γ.IsGaugeProjection (μ := μ))
def IsBoltzmannMultiplier (β : ℝ) (T : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) : Prop :=
  ∀ φ : Γ.SliceL2 μ, (T φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ)
    =ᵐ[ComplexMatrix2.haarPi (Γ.LinkOrbits μ)]
    fun u => Complex.exp (-Γ.sliceEnergy β u) * (φ : (Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) → ℂ) u
variable (μ) in
def boltzmannMultiplier (β : ℝ) : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  Classical.epsilon (Γ.IsBoltzmannMultiplier β)
variable (μ) in
def halfTransfer (β : ℝ) : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  (sqrtLinkOperator β (Γ.LinkOrbits μ)).comp (Γ.gaugeProjection μ)
variable (μ) in
def transfer (β : ℝ) : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  ((Γ.halfTransfer μ β).comp (Γ.boltzmannMultiplier μ β)).comp
    (Γ.halfTransfer μ β)
end CubicPeriodSublattice
namespace Block
variable {μ : Fin 4} (B : Block μ)
theorem links_subset_linksWithin :
    (B.links : Set (SliceLink μ)) ⊆ linksWithin B.vertices :=
  fun l hl => ⟨⟨l, hl, Or.inl rfl⟩, ⟨l, hl, Or.inr rfl⟩⟩
end Block
section BlockGauge
variable {μ : Fin 4} (B : Block μ)
def IsBlockGaugeRep (g : B.vertices → ComplexMatrix2.specialUnitary)
    (T : HaarL2 (B.links : Set (SliceLink μ)) →L[ℂ]
      HaarL2 (B.links : Set (SliceLink μ))) : Prop :=
  ∀ φ : HaarL2 (B.links : Set (SliceLink μ)),
    (T φ : (↥(B.links : Set (SliceLink μ)) → ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[ComplexMatrix2.haarPi (B.links : Set (SliceLink μ))]
      fun u => (φ : (↥(B.links : Set (SliceLink μ)) → ComplexMatrix2.specialUnitary) → ℂ)
        (gaugeAct B.links_subset_linksWithin g⁻¹ u)
def blockGaugeRep (g : B.vertices → ComplexMatrix2.specialUnitary) :
    HaarL2 (B.links : Set (SliceLink μ)) →L[ℂ]
      HaarL2 (B.links : Set (SliceLink μ)) :=
  Classical.epsilon (IsBlockGaugeRep B g)
end BlockGauge
end TransferOperators
end YangMills.Construction
end
