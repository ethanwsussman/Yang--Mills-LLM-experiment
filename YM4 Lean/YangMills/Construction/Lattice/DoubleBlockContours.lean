import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.ContourPaths
import YangMills.Construction.Lattice.StepSequencePaths
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace DoubleBlock
variable {L m : ℕ} {j j' : ℤ}
def axisSequence {y : Site L m j} {x : Site L m j'} (σ : AxisOrdering y x) : List (Fin 4) :=
  (List.finRange _).map fun i => ((σ i : offsetAxes y x) : Fin 4)
def signedBoxSites (z : Site L m j') (n : Fin 4 → ℤ) : Set (Site L m j') :=
  {w | ∃ t : Fin 4 → ℤ, (∀ μ, n μ ≠ 0 → 0 ≤ t μ ∧ t μ ≤ |n μ|) ∧
    w = z + ∑ μ ∈ Finset.univ.filter (fun μ => n μ ≠ 0), (t μ * (n μ).sign) • unitStep L m j' μ}
def positiveUnitStep (L m : ℕ) (j' : ℤ) (ν : Fin 4) : UnitStepVec L m j' :=
  ⟨unitStep L m j' ν, ν, Or.inl rfl⟩
def BlockSiteContours (y : Site L m j) (x : Site L m j') (n : Fin 4 → ℤ) : Prop :=
  ∑ μ, |n μ| ≤ 2 * ((L : ℤ) - 1) ∧
  (∀ Γ ∈ contourSet y x, ∃ w : StepWord L m j',
    w.length = ∑ μ, (n μ).natAbs ∧ pathOfWord (y.toSublattice j') w = Γ) ∧
  (∀ Γ ∈ contourSet y x, ∀ Γ' ∈ contourSet y x, ∀ w w' : StepWord L m j',
    pathOfWord (y.toSublattice j') w = Γ → pathOfWord (y.toSublattice j') w' = Γ' →
      IsPermutationOf w' w) ∧
  (∀ Γ ∈ contourSet y x, ∀ w : StepWord L m j', pathOfWord (y.toSublattice j') w = Γ →
    partialSumSites (y.toSublattice j') w = signedBoxSites (y.toSublattice j') n) ∧
  (∀ z ∈ signedBoxSites (y.toSublattice j') n, (z : FourTorus L m) ∈ unitBlock y) ∧
  (∀ Γ ∈ contourSet y x, ∀ b ∈ Γ,
    (b.source : FourTorus L m) ∈ unitBlock y ∧ (b.target : FourTorus L m) ∈ unitBlock y)
def ContoursAcrossBond (c : Bond L m j) (ν : Fin 4) (x : Site L m j')
    (σ : AxisOrdering c.source x) (a : StepWord L m j') : Prop :=
  let x' : Site L m j' := x + L • unitStep L m j' ν
  let e : StepWord L m j' := List.replicate L (positiveUnitStep L m j' ν)
  let lo : Site L m j' := c.source.toSublattice j'
  let hi : Site L m j' := c.target.toSublattice j'
  (x' : FourTorus L m) ∈ unitBlock c.target ∧
  (∃ σ' : AxisOrdering c.target x', axisSequence σ' = axisSequence σ ∧
    pathOfWord hi a = orderedContour c.target x' σ') ∧
  IsPermutationOf (a ++ e) (e ++ a) ∧ IsPermutationOf (e ++ a) (a ++ e) ∧
  (a ++ e).length = a.length + L ∧ (e ++ a).length = a.length + L ∧
  ((a.length : ℤ) + L ≤ 3 * (L : ℤ) - 2) ∧
  pathOfWord lo (a ++ e) = orderedContour c.source x σ ++ axialPath x x' ∧
  pathOfWord lo (e ++ a) = axialPath lo hi ++ pathOfWord hi a ∧
  (∀ z ∈ partialSumSites lo (a ++ e), (z : FourTorus L m) ∈ bondDoubleBlock c) ∧
  (∀ z ∈ partialSumSites lo (e ++ a), (z : FourTorus L m) ∈ bondDoubleBlock c) ∧
  (∀ b ∈ axialPath x x',
    (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧ (b.target : FourTorus L m) ∈ bondDoubleBlock c) ∧
  (∀ b ∈ axialPath lo hi,
    (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧ (b.target : FourTorus L m) ∈ bondDoubleBlock c)
def DoubleBlockContoursStatement : Prop :=
  ∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ k : ℕ, k < K → ∀ c : BondAtLevel L m K (k + 1),
    (∀ y : SiteAtLevel L m K (k + 1), (y = c.source ∨ y = c.target) →
      unitBlock y ⊆ bondDoubleBlock c ∧
      ∀ x : SiteAtLevel L m K k, (x : FourTorus L m) ∈ unitBlock y →
        (∃ n : Fin 4 → ℤ, IsBlockOffset y x n) ∧
        ∀ n : Fin 4 → ℤ, IsBlockOffset y x n → BlockSiteContours y x n) ∧
    (∀ ν : Fin 4, c.target = c.source + unitStep L m (levelDepth K (k + 1)) ν →
      ∀ x : SiteAtLevel L m K k, (x : FourTorus L m) ∈ unitBlock c.source →
      ∀ (σ : AxisOrdering c.source x) (a : StepWord L m (levelDepth K k)),
        pathOfWord (c.source.toSublattice (levelDepth K k)) a = orderedContour c.source x σ →
        ContoursAcrossBond c ν x σ a)
end DoubleBlock
end PeriodicLattice
end YangMills.Construction
