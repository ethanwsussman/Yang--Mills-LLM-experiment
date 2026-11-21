import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace BoxTorus
def Space (ℓ : Fin 4 → ℝ) : Type := (μ : Fin 4) → AddCircle (ℓ μ)
instance (ℓ : Fin 4 → ℝ) : AddCommGroup (Space ℓ) :=
  inferInstanceAs (AddCommGroup ((μ : Fin 4) → AddCircle (ℓ μ)))
def basisVector (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
def projection (ℓ : Fin 4 → ℝ) : (Fin 4 → ℝ) →+ Space ℓ where
  toFun x μ := (x μ : AddCircle (ℓ μ))
  map_zero' := rfl
  map_add' _ _ := rfl
def periods (ℓ : Fin 4 → ℝ) : AddSubgroup (Fin 4 → ℝ) :=
  AddSubgroup.pi univ fun μ => AddSubgroup.zmultiples (ℓ μ)
theorem projection_surjective (ℓ : Fin 4 → ℝ) : Function.Surjective (projection ℓ) := by
  intro x
  choose w hw using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨w, funext hw⟩
theorem projection_ker (ℓ : Fin 4 → ℝ) : (projection ℓ).ker = periods ℓ := by
  ext x
  simp only [AddMonoidHom.mem_ker, periods, AddSubgroup.mem_pi, mem_univ, forall_const]
  constructor
  · intro h μ
    exact (QuotientAddGroup.eq_zero_iff _).mp (congrFun h μ)
  · intro h
    funext μ
    exact (QuotientAddGroup.eq_zero_iff _).mpr (h μ)
instance (ℓ : Fin 4 → ℝ) : TopologicalSpace (Space ℓ) :=
  TopologicalSpace.coinduced (projection ℓ) inferInstance
theorem isOpen_iff_preimage {ℓ : Fin 4 → ℝ} (O : Set (Space ℓ)) :
    IsOpen O ↔ IsOpen (projection ℓ ⁻¹' O) := Iff.rfl
variable {ℓ : Fin 4 → ℝ}
def IsLiftOf (w : Fin 4 → ℝ) (x : Space ℓ) : Prop := projection ℓ w = x
def translate (x : Space ℓ) (w : Fin 4 → ℝ) : Space ℓ := x + projection ℓ w
def image (ℓ : Fin 4 → ℝ) (S : Set (Fin 4 → ℝ)) : Set (Space ℓ) := projection ℓ '' S
def hyperplane (ℓ : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ) : Set (Space ℓ) :=
  image ℓ {w | w μ = c}
def slab (ℓ : Fin 4 → ℝ) (μ : Fin 4) (c c' : ℝ) : Set (Space ℓ) :=
  image ℓ {w | c < w μ ∧ w μ < c'}
def torusDist (x y : Space ℓ) : ℝ :=
  sInf ((fun z : Fin 4 → ℝ => Real.sqrt (∑ μ, z μ ^ 2)) '' {z | IsLiftOf z (x - y)})
def IsDistPreserving (g : Space ℓ → Space ℓ) : Prop :=
  Function.Bijective g ∧ ∀ x y, torusDist (g x) (g y) = torusDist x y
def gridSubgroup (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) : AddSubgroup (Space ℓ) where
  carrier := {x | ∃ n : Fin 4 → ℤ, x = projection ℓ fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L κ}
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨n', rfl⟩
    refine ⟨n + n', ?_⟩
    rw [← map_add]
    congr 1
    funext μ
    simp [add_mul]
  zero_mem' := ⟨0, by
    rw [← map_zero (projection ℓ)]
    congr 1
    funext μ
    simp⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    rw [← map_neg]
    congr 1
    funext μ
    simp
abbrev GridPoint (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) : Type := ↥(gridSubgroup L κ ℓ)
variable {L : ℕ} {κ : ℤ}
instance : Countable (GridPoint L κ ℓ) := by
  have h : Function.Surjective (fun n : Fin 4 → ℤ =>
      (⟨projection ℓ fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L κ, ⟨n, rfl⟩⟩ :
        GridPoint L κ ℓ)) := by
    rintro ⟨x, n, rfl⟩
    exact ⟨n, rfl⟩
  exact h.countable
def gridStep (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) (ν : Fin 4) : GridPoint L κ ℓ :=
  ⟨projection ℓ (PeriodicLattice.meshSize L κ • basisVector ν), ⟨Pi.single ν 1, by
    congr 1
    funext μ
    by_cases h : μ = ν
    · subst h; simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne h]⟩⟩
def IsNeighbourStep (x x' : GridPoint L κ ℓ) (ν : Fin 4) (σ : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧
    (x' : Space ℓ) = translate (x : Space ℓ) ((σ * PeriodicLattice.meshSize L κ) • basisVector ν)
theorem IsNeighbourStep.symm {x x' : GridPoint L κ ℓ} {ν : Fin 4} {σ : ℝ}
    (h : IsNeighbourStep x x' ν σ) : IsNeighbourStep x' x ν (-σ) := by
  refine ⟨h.1.symm.imp (fun e => by simp [e]) (fun e => by simp [e]), ?_⟩
  rw [h.2, translate, translate, neg_mul, neg_smul, map_neg, add_neg_cancel_right]
@[ext]
structure DirectedEdge (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) where
  source : GridPoint L κ ℓ
  target : GridPoint L κ ℓ
  isNeighbour : ∃ (ν : Fin 4) (σ : ℝ), IsNeighbourStep source target ν σ
instance : Countable (DirectedEdge L κ ℓ) := by
  have h : Function.Injective (fun b : DirectedEdge L κ ℓ => (b.source, b.target)) := by
    intro b b' hb
    exact DirectedEdge.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  exact h.countable
namespace DirectedEdge
def HasAxis (b : DirectedEdge L κ ℓ) (ν : Fin 4) : Prop :=
  ∃ σ : ℝ, IsNeighbourStep b.source b.target ν σ
def IsSegmentSet (b : DirectedEdge L κ ℓ) (S : Set (Space ℓ)) : Prop :=
  ∃ (ν : Fin 4) (σ : ℝ), IsNeighbourStep b.source b.target ν σ ∧
    S = {p | ∃ t ∈ Icc (0 : ℝ) 1,
      p = translate (b.source : Space ℓ) ((t * σ * PeriodicLattice.meshSize L κ) • basisVector ν)}
def ends (b : DirectedEdge L κ ℓ) : Set (GridPoint L κ ℓ) := {b.source, b.target}
def flip (b : DirectedEdge L κ ℓ) : DirectedEdge L κ ℓ where
  source := b.target
  target := b.source
  isNeighbour := by
    obtain ⟨ν, σ, h⟩ := b.isNeighbour
    exact ⟨ν, -σ, h.symm⟩
def IsForward (b : DirectedEdge L κ ℓ) : Prop := ∃ ν : Fin 4, IsNeighbourStep b.source b.target ν 1
theorem flip_isForward {b : DirectedEdge L κ ℓ} (h : ¬ b.IsForward) : b.flip.IsForward := by
  obtain ⟨ν, σ, hs⟩ := b.isNeighbour
  rcases hs.1 with e | e
  · exact absurd ⟨ν, e ▸ hs⟩ h
  · refine ⟨ν, ?_⟩
    have := hs.symm
    rw [e, neg_neg] at this
    exact this
def LiesIn (b : DirectedEdge L κ ℓ) (S : Set (Space ℓ)) : Prop :=
  ∀ T, b.IsSegmentSet T → T ⊆ S
end DirectedEdge
abbrev ForwardEdge (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) : Type :=
  {b : DirectedEdge L κ ℓ // b.IsForward}
abbrev GaugeConfig (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) : Type :=
  ForwardEdge L κ ℓ → Conventions.StandingParameters.gaugeGroup
instance : BorelSpace (GaugeConfig L κ ℓ) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Conventions.StandingParameters.gaugeGroup :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance
def haarConfigMeasure (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) : Measure (GaugeConfig L κ ℓ) :=
  Matrices.ComplexMatrix2.haarPi (ForwardEdge L κ ℓ)
def edgeVariable (U : GaugeConfig L κ ℓ) (b : DirectedEdge L κ ℓ) :
    Conventions.StandingParameters.gaugeGroup :=
  open Classical in
  if h : b.IsForward then U ⟨b, h⟩ else (U ⟨b.flip, DirectedEdge.flip_isForward h⟩)⁻¹
def forwardPart (E : Set (DirectedEdge L κ ℓ)) : Set (ForwardEdge L κ ℓ) :=
  {b | b.1 ∈ E ∨ b.1.flip ∈ E}
def IsBoundedBorelOfEdges (E : Set (DirectedEdge L κ ℓ))
    (F : GaugeConfig L κ ℓ → ℂ) : Prop :=
  ∃ f : (↥(forwardPart E) → Conventions.StandingParameters.gaugeGroup) → ℂ,
    Measurable f ∧ (∃ C : ℝ, ∀ u, ‖f u‖ ≤ C) ∧ ∀ U, F U = f fun b => U b.1
@[ext]
structure Face (L : ℕ) (κ : ℤ) (ℓ : Fin 4 → ℝ) where
  corner : GridPoint L κ ℓ
  dir₁ : Fin 4
  dir₂ : Fin 4
  dir₁_lt_dir₂ : dir₁ < dir₂
def edgeFrom (x : GridPoint L κ ℓ) (ν : Fin 4) : DirectedEdge L κ ℓ where
  source := x
  target := x + gridStep L κ ℓ ν
  isNeighbour := ⟨ν, 1, Or.inl rfl, by simp [translate, gridStep]⟩
namespace Face
def vertexSet (p : Face L κ ℓ) : Set (GridPoint L κ ℓ) :=
  {p.corner, p.corner + gridStep L κ ℓ p.dir₁,
    p.corner + gridStep L κ ℓ p.dir₁ + gridStep L κ ℓ p.dir₂,
    p.corner + gridStep L κ ℓ p.dir₂}
end Face
def faceHolonomy (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ) :
    Conventions.StandingParameters.gaugeGroup :=
  edgeVariable U (edgeFrom p.corner p.dir₁) *
    edgeVariable U (edgeFrom (p.corner + gridStep L κ ℓ p.dir₁) p.dir₂) *
    (edgeVariable U (edgeFrom (p.corner + gridStep L κ ℓ p.dir₂) p.dir₁))⁻¹ *
    (edgeVariable U (edgeFrom p.corner p.dir₂))⁻¹
def faceEnergy (U : GaugeConfig L κ ℓ) (p : Face L κ ℓ) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re
def wilsonAction (U : GaugeConfig L κ ℓ) : ℝ := ∑ᶠ p : Face L κ ℓ, faceEnergy U p
end BoxTorus
open BoxTorus
structure CellGrid (L : ℕ) (κ : ℤ) where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  cellLength : ℝ
  cellLength_pos : 0 < cellLength
  cellLength_div_meshSize : ∃ z : ℤ, cellLength / PeriodicLattice.meshSize L κ = z
  counts : Fin 4 → ℕ
  counts_pos : ∀ μ, 0 < counts μ
  counts_even : ∀ μ, Even (counts μ)
  four_meshSize_le : ∀ μ, 4 * PeriodicLattice.meshSize L κ ≤ counts μ * cellLength
  centre : Fin 4 → ℝ
  centre_mem : ∀ μ, ∃ z : ℤ, centre μ = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)
namespace CellGrid
variable {L : ℕ} {κ : ℤ}
def sideLengths (d : CellGrid L κ) (μ : Fin 4) : ℝ := d.counts μ * d.cellLength
def numCells (d : CellGrid L κ) : ℕ := ∏ μ, d.counts μ
abbrev CellIndex (d : CellGrid L κ) : Type := (μ : Fin 4) → ZMod (d.counts μ)
abbrev Space (d : CellGrid L κ) : Type := BoxTorus.Space d.sideLengths
abbrev GridPoint (d : CellGrid L κ) : Type := BoxTorus.GridPoint L κ d.sideLengths
abbrev DirectedEdge (d : CellGrid L κ) : Type := BoxTorus.DirectedEdge L κ d.sideLengths
abbrev ForwardEdge (d : CellGrid L κ) : Type := BoxTorus.ForwardEdge L κ d.sideLengths
abbrev GaugeConfig (d : CellGrid L κ) : Type := BoxTorus.GaugeConfig L κ d.sideLengths
abbrev Face (d : CellGrid L κ) : Type := BoxTorus.Face L κ d.sideLengths
def wilsonAction (d : CellGrid L κ) (U : d.GaugeConfig) : ℝ := BoxTorus.wilsonAction U
theorem exists_sideLengths_eq (d : CellGrid L κ) :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ μ,
      d.sideLengths μ = ((d.counts μ : ℤ) * z : ℤ) * PeriodicLattice.meshSize L κ := by
  have hL : (L : ℝ) ≠ 0 := by
    have := d.admissible.2
    exact_mod_cast (by omega : L ≠ 0)
  have ha : PeriodicLattice.meshSize L κ ≠ 0 := zpow_ne_zero _ hL
  obtain ⟨z, hz⟩ := d.cellLength_div_meshSize
  have hc : d.cellLength = z * PeriodicLattice.meshSize L κ := by
    rw [← hz]
    field_simp
  refine ⟨z, ?_, fun μ => ?_⟩
  · rintro rfl
    have := d.cellLength_pos
    simp [hc] at this
  · simp only [sideLengths, hc]
    push_cast
    ring
instance (d : CellGrid L κ) : Finite d.GridPoint := by
  obtain ⟨z, hz, hs⟩ := d.exists_sideLengths_eq
  have hM : ∀ μ, (d.counts μ : ℤ) * z ≠ 0 := fun μ =>
    mul_ne_zero (by exact_mod_cast (d.counts_pos μ).ne') hz
  have : Finite ↥(Icc (0 : Fin 4 → ℤ) fun μ => |(d.counts μ : ℤ) * z|) :=
    (Set.finite_Icc _ _).to_subtype
  refine Finite.of_surjective (α := ↥(Icc (0 : Fin 4 → ℤ) fun μ => |(d.counts μ : ℤ) * z|))
    (fun r => (⟨projection d.sideLengths fun μ => (r.1 μ : ℝ) * PeriodicLattice.meshSize L κ,
      ⟨r.1, rfl⟩⟩ : d.GridPoint)) ?_
  rintro ⟨x, n, rfl⟩
  refine ⟨⟨fun μ => n μ % ((d.counts μ : ℤ) * z), Set.mem_Icc.mpr
    ⟨fun μ => Int.emod_nonneg _ (hM μ), fun μ => (Int.emod_lt_abs _ (hM μ)).le⟩⟩, ?_⟩
  refine Subtype.ext (funext fun μ => ?_)
  refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-(n μ / ((d.counts μ : ℤ) * z)), ?_⟩
  have h := Int.emod_add_mul_ediv (n μ) ((d.counts μ : ℤ) * z)
  have h' : (n μ : ℝ) = ((n μ % ((d.counts μ : ℤ) * z) : ℤ) : ℝ) +
      (((d.counts μ : ℤ) * z : ℤ) : ℝ) * ((n μ / ((d.counts μ : ℤ) * z) : ℤ) : ℝ) := by
    exact_mod_cast h.symm
  rw [zsmul_eq_mul, hs μ]
  show _ = ((n μ % ((d.counts μ : ℤ) * z) : ℤ) : ℝ) * PeriodicLattice.meshSize L κ -
    (n μ : ℝ) * PeriodicLattice.meshSize L κ
  rw [h']
  push_cast
  ring
instance (d : CellGrid L κ) : Finite d.DirectedEdge :=
  Finite.of_injective (fun b : d.DirectedEdge => (b.source, b.target)) fun _ _ hb =>
    BoxTorus.DirectedEdge.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
instance (d : CellGrid L κ) : Finite d.Face :=
  Finite.of_injective (fun p : d.Face => (p.corner, p.dir₁, p.dir₂)) fun p p' hp => by
    simp only [Prod.mk.injEq] at hp
    exact BoxTorus.Face.ext hp.1 hp.2.1 hp.2.2
end CellGrid
end YangMills.Construction
end
