import YangMills.Construction.InfiniteLattice.FramesRectangularPeriodLatticesAndTheBox
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open NormalFamilies
def siteCube (z : LatticePoint 1) (ϱ : ℕ+) : Set (LatticePoint 1) :=
  {x | ∃ k : Fin 4 → ℕ, (∀ μ, k μ ≤ (ϱ : ℕ)) ∧
    ∀ μ, (x : AmbientSpace) μ = (z : AmbientSpace) μ + (k μ : ℝ)}
namespace LocalObservableArray
def IsSingleGenerated (𝔸 : LocalObservableArray) (A : GaugeField 1 → ℂ) : Prop :=
  𝔸.size = 1 ∧ ∀ ι, 𝔸.gen ι = A
def invIndex (𝔸 : LocalObservableArray) : ℝ := (𝔸.sublattice.index : ℝ)⁻¹
end LocalObservableArray
structure BoxTorusComparisonData where
  obs : GaugeField 1 → ℂ
  obs_mem : obs ∈ continuousLocalFunctions 1
  obs_im : ∀ U, (obs U).im = 0
  obs_nonconst : ¬ ∃ c : ℂ, ∀ U, obs U = c
  boxWidth : ℕ+
  obsAnchor : LatticePoint 1
  obs_support : LinksLieIn (observableSupport obs)
    ((fun x : LatticePoint 1 => (x : AmbientSpace)) '' siteCube obsAnchor boxWidth)
  normalFrame : OrthogonalNormalFrame
  sideLengths : Fin 4 → ℕ+
  periodSublattice : PeriodSublattice 1
  periodSublattice_isBoxShaped : periodSublattice.IsBoxShaped normalFrame sideLengths
  no_short_period : ∀ γ ∈ periodSublattice.periods, γ ≠ 0 →
    ((boxWidth : ℕ) : ℝ) + 1 < ‖(γ : AmbientSpace)‖
  translationGroup : AddSubgroup (LatticePoint 1)
  periods_le_translationGroup : periodSublattice.periods ≤ translationGroup
  translationGroup_finiteIndex : translationGroup.FiniteIndex
namespace BoxTorusComparisonData
variable (d : BoxTorusComparisonData)
def obsArray : LocalObservableArray where
  sublattice := d.translationGroup
  sublattice_finiteIndex := d.translationGroup_finiteIndex
  size := 1
  one_le_size := le_rfl
  gen := fun _ => d.obs
  gen_mem := fun _ => d.obs_mem
  gen_im := fun _ => d.obs_im
inductive Term : Type
  | plaquette (p : ElementaryPlaquette 1) : Term
  | shifted (v : d.translationGroup) : Term
variable {d}
def Term.anchor : d.Term → LatticePoint 1
  | .plaquette p => p.corner
  | .shifted v => d.obsAnchor + (v : LatticePoint 1)
def Term.links : d.Term → Set (Link 1)
  | .plaquette p => p.linkSet
  | .shifted v => observableSupport ((shift (v : LatticePoint 1)).actOn d.obs)
def Term.siteBox (T : d.Term) : Set (LatticePoint 1) := siteCube T.anchor d.boxWidth
def Term.IsInner (T : d.Term) : Prop := T.siteBox ⊆ d.normalFrame.fundamentalBox d.sideLengths
end BoxTorusComparisonData
end InfiniteLattice
end YangMills.Construction
end
