import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ReflectionPositivity
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace PlaquetteNondegeneracy
variable (D : CutoffMirrors.MirrorData)
abbrev CutoffSite : Type := PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)
abbrev CutoffBond : Type := PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ)
abbrev CutoffPlaquette : Type := PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)
abbrev cutoffGaugeFields : Set (CutoffBond D → Matrices.ComplexMatrix2) :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
def meshPoint (n : Fin 4 → ℤ) : Fin 4 → ℝ := fun ν => D.spacing * (n ν : ℝ)
def signedAxisStep (q : Fin 4 × ℤˣ) : Fin 4 → ℝ :=
  (((q.2 : ℤ) : ℝ) * D.spacing) • PeriodicLattice.coordVec q.1
def MeshAndSiteCount : Prop :=
  (D.L : ℝ) ^ ((D.m : ℕ) + (D.K : ℕ)) = (D.sitesPerSide : ℝ) ∧
    2 ≤ D.sitesPerSide ∧
    D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing ∧
    D.side / D.spacing = 2 * (D.sitesPerSide : ℝ) ∧
    (4 : ℝ) ≤ 2 * (D.sitesPerSide : ℝ) ∧
    (InfiniteLattice.latticeSubgroup D.side : Set (Fin 4 → ℝ)) ⊆
      InfiniteLattice.latticeSubgroup D.spacing ∧
    (D.latticeSubgroup : Set D.Torus) =
      D.proj '' (InfiniteLattice.latticeSubgroup D.spacing : Set (Fin 4 → ℝ)) ∧
    Nat.card D.latticeSubgroup = (2 * D.sitesPerSide) ^ 4 ∧
    (∀ x ∈ D.latticeSubgroup, ∀ y, D.IsLiftOf x y → y ∈ InfiniteLattice.latticeSubgroup D.spacing) ∧
    ∀ n n' : Fin 4 → ℤ, D.proj (meshPoint D n) = D.proj (meshPoint D n') ↔
      ∃ k : Fin 4 → ℤ, ∀ ν, n ν - n' ν = 2 * (D.sitesPerSide : ℤ) * k ν
def BondAxisAndSign : Prop :=
  Function.Injective (fun q : Fin 4 × ℤˣ => D.proj (signedAxisStep D q)) ∧
    ∀ b : CutoffBond D,
      (∃! q : Fin 4 × ℤˣ, D.DiffEq (b.target : D.Torus) (b.source : D.Torus) (signedAxisStep D q)) ∧
        Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
def vertexList (p : CutoffPlaquette D) : List (CutoffSite D) :=
  [p.origin, p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis,
    p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis +
      PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis,
    p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis]
theorem mem_vertexList (p : CutoffPlaquette D) (c : CutoffSite D) :
    c ∈ vertexList D p ↔ c ∈ p.vertices := by
  simp [vertexList, PeriodicLattice.Plaquette.vertices]
def PlaquetteVerticesDistinct : Prop :=
  ∀ p : CutoffPlaquette D, (vertexList D p).Nodup ∧
    ∀ p' : CutoffPlaquette D, p.vertices = p'.vertices → p = p'
def bottomEdge (p : CutoffPlaquette D) : CutoffBond D :=
  PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis
def rightEdge (p : CutoffPlaquette D) : CutoffBond D :=
  PeriodicLattice.Bond.forwardFrom
    (p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis) p.secondAxis
def topEdge (p : CutoffPlaquette D) : CutoffBond D :=
  PeriodicLattice.Bond.forwardFrom
    (p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis) p.firstAxis
def leftEdge (p : CutoffPlaquette D) : CutoffBond D :=
  PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis
def HolonomyOfPositiveEdges : Prop :=
  ∀ p : CutoffPlaquette D,
    (bottomEdge D p).IsPositivelyOriented ∧ (rightEdge D p).IsPositivelyOriented ∧
      (topEdge D p).IsPositivelyOriented ∧ (leftEdge D p).IsPositivelyOriented ∧
      (topEdge D p).target = p.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis +
        PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis ∧
      ∀ U ∈ cutoffGaugeFields D,
        PeriodicLattice.plaquetteHolonomy U p =
          U (bottomEdge D p) * U (rightEdge D p) * (U (topEdge D p))⁻¹ *
            (U (leftEdge D p))⁻¹
def TraceIndependentOfTraversal : Prop :=
  ∀ (p : CutoffPlaquette D) (z₀ z₁ z₂ z₃ : CutoffSite D) (b₀ b₁ b₂ b₃ : CutoffBond D),
    ({z₀, z₁, z₂, z₃} : Set (CutoffSite D)) = p.vertices →
    b₀.source = z₀ → b₀.target = z₁ → b₁.source = z₁ → b₁.target = z₂ →
    b₂.source = z₂ → b₂.target = z₃ → b₃.source = z₃ → b₃.target = z₀ →
    ∀ U ∈ cutoffGaugeFields D,
      (1 / 2 : ℝ) * (Matrices.ComplexMatrix2.fullTrace (U b₀ * U b₁ * U b₂ * U b₃)).re =
        (1 / 2 : ℝ) * (Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U p)).re
def NondegeneracyStatement : Prop :=
  ∀ D : CutoffMirrors.MirrorData,
    MeshAndSiteCount D ∧ BondAxisAndSign D ∧ PlaquetteVerticesDistinct D ∧
      HolonomyOfPositiveEdges D ∧ TraceIndependentOfTraversal D
end PlaquetteNondegeneracy
end
end YangMills.Construction.ReflectionPositivity
