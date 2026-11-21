import YangMills.Construction.InfiniteLattice.CoveringOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks
namespace CutoffData
def withExpCoupling (d : CutoffData) (m' : ℕ+) (β' : ℝ) (hβ' : 0 < β') : CutoffData :=
  { d with m := m', coupling := β', coupling_pos := hβ' }
variable {d : CutoffData}
namespace CutoffWindow
def withExpCoupling (W : d.CutoffWindow) (m' : ℕ+) (β' : ℝ) (hβ' : 0 < β') :
    (d.withExpCoupling m' β' hβ').CutoffWindow where
  links := W.links
  finite := W.finite
  subset_links := W.subset_links
def InjectiveAtSide (W : d.CutoffWindow) (ℓ' : d.sideSet) : Prop :=
  InjOn (d.withSide ℓ').projLink (W.links ∪ W.rim)
def injectiveSides (W : d.CutoffWindow) : Set ℝ :=
  {ℓ' | ∃ h : ℓ' ∈ d.sideSet, W.InjectiveAtSide ⟨ℓ', h⟩}
def minSide (W : d.CutoffWindow) : ℝ := sInf W.injectiveSides
def BoundedBy (W : d.CutoffWindow) (ϱ : ℝ) : Prop :=
  ∀ b ∈ W.links ∪ W.rim, ∀ x ∈ linkEndpoints b, PeriodicLattice.supNormVec (x : AmbientSpace) ≤ ϱ
theorem injectiveAtSide_side_iff (W : d.CutoffWindow) :
    W.InjectiveAtSide ⟨d.side, d.side_mem_sideSet⟩ ↔ W.EmbedsInPeriodicLattice := by
  have h : d.sideExponent ⟨d.side, d.side_mem_sideSet⟩ = d.m :=
    (d.existsUnique_sideExponent d.side_mem_sideSet).unique (d.torusSide_sideExponent _) rfl
  show InjOn (projectLink d.L (d.sideExponent ⟨d.side, d.side_mem_sideSet⟩ : ℕ+) ((d.K : ℕ) : ℤ)) _ ↔
    InjOn (projectLink d.L (d.m : ℕ+) ((d.K : ℕ) : ℤ)) _
  rw [h]
  exact Iff.rfl
end CutoffWindow
end CutoffData
def WindowProjectionProperties : Prop :=
  ∀ d : CutoffData,
    (d.projLink '' d.links = d.positiveLinkSet ∧
      Function.Surjective d.projFace ∧
      (∀ p : ElementaryPlaquette d.spacing,
        d.projLink '' {b | ContainsLink p b} =
          {l | CutoffData.FaceContains (d := d) (d.projFace p) l}) ∧
      (∀ (y y' : d.PeriodicSite) (μ μ' : Fin 4),
        d.positiveLinkAt y μ = d.positiveLinkAt y' μ' → y = y' ∧ μ = μ') ∧
      (∀ (y : d.PeriodicSite) (μ : Fin 4), (d.positiveLinkAt y μ).opposite ∉ d.positiveLinkSet) ∧
      (∀ (x x' : LatticePoint d.spacing) (μ μ' : Fin 4),
        d.projLink (Link.forwardFrom x μ) = d.projLink (Link.forwardFrom x' μ') ↔
          μ = μ' ∧ (x : AmbientSpace) - (x' : AmbientSpace) ∈ latticeSubgroup d.side) ∧
      (∀ (U : d.PeriodicFields) (b : Link d.spacing), b ∈ d.links →
        d.liftField U b = U.linkValue (d.projLink b)) ∧
      (∀ (U : d.PeriodicFields) (p : ElementaryPlaquette d.spacing),
        ((faceHolonomy (d.liftField U) p : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2) =
          PeriodicLattice.plaquetteHolonomy U.1 (d.projFace p)) ∧
      Continuous d.liftField) ∧
    ∀ W : d.CutoffWindow,
      {P : d.PeriodicPlaquette | ∃ l ∈ d.projLinks W.links, CutoffData.FaceContains (d := d) P l} =
        d.projFace '' W.faces ∧
      (W.EmbedsInPeriodicLattice →
        d.projLinks W.links ∩ d.projLinks W.rim = ∅ ∧
        InjOn d.projFace W.faces ∧
        ∀ ℓ' : d.sideSet, d.side ≤ ℓ' → W.InjectiveAtSide ℓ') ∧
      (∃ ϱ : ℝ, 0 < ϱ ∧ W.BoundedBy ϱ) ∧
      (∀ ϱ : ℝ, 0 < ϱ → W.BoundedBy ϱ → d.side / 2 > ϱ → W.EmbedsInPeriodicLattice) ∧
      W.injectiveSides.Nonempty ∧
      IsLeast W.injectiveSides W.minSide ∧
      W.injectiveSides = {ℓ' | ℓ' ∈ d.sideSet ∧ ℓ' ≥ W.minSide} ∧
      (∀ (m' : ℕ+) (β' : ℝ) (hβ' : 0 < β'),
        (W.withExpCoupling m' β' hβ').minSide = W.minSide) ∧
      ∀ ℓ' ∈ d.sideSet, ∀ ϱ : ℝ, 0 < ϱ → W.BoundedBy ϱ → ℓ' / 2 > ϱ → W.minSide ≤ ℓ'
end YangMills.Construction.CutoffLinks
