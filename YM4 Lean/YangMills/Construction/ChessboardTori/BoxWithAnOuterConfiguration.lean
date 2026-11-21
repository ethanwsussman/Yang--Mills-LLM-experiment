import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.LinksAndTheReplacementOfAConfigurationOnAFiniteSet
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice GibbsAtFixedSpacing
namespace ChessboardTori
theorem ReflectionGrid.isBounded_block {D : ChessboardSetup} (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    Bornology.IsBounded (g.block k) := by
  refine (Metric.isBounded_Icc
    (fun μ => g.origin μ + g.cellSide * k μ)
    (fun μ => g.origin μ + g.cellSide * k μ + PeriodicLattice.torusSide D.L D.m)).subset fun x hx => ?_
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · have := (hx μ).1
    simp only at this ⊢
    linarith
  · have := (hx μ).2
    simp only at this ⊢
    linarith
namespace ChessboardSetup
variable (D : ChessboardSetup)
open Classical in
def boxLinks (B : Set AmbientSpace) : Finset D.Link :=
  if h : (positiveLinksWithin D.mesh B).Finite then h.toFinset else ∅
theorem coe_boxLinks {B : Set AmbientSpace} (h : (positiveLinksWithin D.mesh B).Finite) :
    (D.boxLinks B : Set D.Link) = positiveLinksWithin D.mesh B := by
  simp [boxLinks, h]
theorem coe_boxLinks_subset_positive (B : Set AmbientSpace) :
    (D.boxLinks B : Set D.Link) ⊆ positiveLinkSet D.mesh := by
  by_cases h : (positiveLinksWithin D.mesh B).Finite
  · rw [D.coe_boxLinks h]
    exact inter_subset_left
  · simp [boxLinks, h]
theorem hasNoOppositePairs_boxLinks (B : Set AmbientSpace) :
    HasNoOppositePairs (D.boxLinks B : Set D.Link) := fun _ hb hr =>
  opposite_notMem_positiveLinks D.mesh_pos (D.coe_boxLinks_subset_positive B hb)
    (D.coe_boxLinks_subset_positive B hr)
def interiorPlaquettes (B : Set AmbientSpace) : Set D.Plaquette :=
  {p | ∀ b ∈ p.edges, b ∈ D.boxLinks B}
def boundaryPlaquetteCount (B : Set AmbientSpace) : ℕ :=
  {p : D.Plaquette | (∃ b ∈ p.edges, b ∈ D.boxLinks B) ∧
    ∃ b ∈ p.edges, b ∉ D.boxLinks B}.ncard
def torusBoundaryPlaquetteCount (B : Set AmbientSpace) : ℕ :=
  {p' : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) |
    ¬ ∃ p ∈ D.interiorPlaquettes B, CutoffLattice.projectFace D.L D.m D.K p = p'}.ncard
def IsBoxLocalObservable (B : Set AmbientSpace) (Ψ : D.GaugeField → ℂ) : Prop :=
  IsBoundedObservable Ψ ∧ DependsOnlyOnLinks (D.boxLinks B : Set D.Link) Ψ
abbrev BoxLinkVariables (B : Set AmbientSpace) : Type := LinkVariables (D.boxLinks B : Set D.Link)
def boxHaar (B : Set AmbientSpace) : Measure (D.BoxLinkVariables B) :=
  LinkVariables.haarMeasure (D.boxLinks B : Set D.Link)
def overwriteBox (B : Set AmbientSpace) (V : D.BoxLinkVariables B) (ξ : D.GaugeField) : D.GaugeField :=
  overwriteLinks (D.hasNoOppositePairs_boxLinks B) V ξ
theorem restrictField_overwriteBox (B : Set AmbientSpace) (V : D.BoxLinkVariables B) (ξ : D.GaugeField) :
    restrictField (D.overwriteBox B V ξ) (D.boxLinks B : Set D.Link) = V :=
  funext fun b => overwriteLinks_apply_of_mem (D.hasNoOppositePairs_boxLinks B) V ξ b
def evalOnBox {E : Type*} (B : Set AmbientSpace) (Ψ : D.GaugeField → E) (V : D.BoxLinkVariables B) : E :=
  Ψ (D.overwriteBox B V (trivialField D.mesh))
variable {D}
theorem evalOnBox_eq {E : Type*} {B : Set AmbientSpace} {Ψ : D.GaugeField → E}
    (hΨ : DependsOnlyOnLinks (D.boxLinks B : Set D.Link) Ψ) {V : D.BoxLinkVariables B}
    {U : D.GaugeField} (hU : restrictField U (D.boxLinks B : Set D.Link) = V) :
    D.evalOnBox B Ψ V = Ψ U :=
  hΨ _ _ ((D.restrictField_overwriteBox B V _).trans hU.symm)
theorem evalOnBox_eq_overwriteBox {E : Type*} {B : Set AmbientSpace} {Ψ : D.GaugeField → E}
    (hΨ : DependsOnlyOnLinks (D.boxLinks B : Set D.Link) Ψ) (V : D.BoxLinkVariables B)
    (ξ : D.GaugeField) : D.evalOnBox B Ψ V = Ψ (D.overwriteBox B V ξ) :=
  evalOnBox_eq hΨ (D.restrictField_overwriteBox B V ξ)
theorem dependsOnlyOnLinks_faceEnergy {B : Set AmbientSpace} {p : D.Plaquette}
    (hp : p ∈ D.interiorPlaquettes B) :
    DependsOnlyOnLinks (D.boxLinks B : Set D.Link)
      (fun U : D.GaugeField => faceEnergy U p) := by
  intro U U' h
  have agree : ∀ b ∈ p.edges, U b = U' b := fun b hb =>
    congrFun h ⟨b, Finset.mem_coe.mpr (hp b hb)⟩
  simp only [faceEnergy, faceHolonomy]
  rw [agree _ (by simp [ElementaryPlaquette.edges]), agree (Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis)
    (by simp [ElementaryPlaquette.edges]), agree (Link.forwardFrom (p.corner + axisStep D.mesh p.highAxis) p.lowAxis)
    (by simp [ElementaryPlaquette.edges]), agree (Link.forwardFrom p.corner p.highAxis)
    (by simp [ElementaryPlaquette.edges])]
variable (D)
def freeBoxPartition (B : Set AmbientSpace) (Ψ : D.GaugeField → ℂ) : ℂ :=
  ∫ V, D.evalOnBox B Ψ V *
      (Real.exp (-D.β * ∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) : ℂ)
    ∂D.boxHaar B
def boundaryConditionPartition (B : Set AmbientSpace) (ξ : D.GaugeField) (Ψ : D.GaugeField → ℂ) : ℂ :=
  ∫ V, D.evalOnBox B Ψ V *
      (Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B V ξ) p) : ℂ)
    ∂D.boxHaar B
def torusPartition (Ψ : D.GaugeField → ℂ) : ℂ :=
  ∫ U, Ψ (D.liftField U) * (PeriodicLattice.boltzmannWeight D.β U : ℂ)
    ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
end ChessboardSetup
def boxBoundaryConstant : ℕ := 36
end ChessboardTori
end YangMills.Construction
end
