import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
structure MirrorData extends Conventions.StandingParameters where
  β : ℝ
  β_pos : 0 < β
inductive Ambient where
  | torus
  | euclidean
namespace MirrorData
variable (D : MirrorData)
def mesh : ℝ := PeriodicLattice.meshSize D.L (D.K : ℕ)
abbrev torusSublattice : AddSubgroup D.Torus := PeriodicLattice.sublattice D.L D.m (D.K : ℕ)
def halfSideCount : ℕ := D.L ^ ((D.m : ℕ) + (D.K : ℕ))
theorem side_div_mesh : D.side / D.mesh = 2 * (D.halfSideCount : ℝ) := by
  have hL : (D.L : ℝ) ≠ 0 := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : D.L ≠ 0)
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide, mesh,
    PeriodicLattice.meshSize, halfSideCount]
  rw [zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
abbrev flatLattice : AddSubgroup (Fin 4 → ℝ) := InfiniteLattice.latticeSubgroup D.mesh
end MirrorData
namespace Ambient
variable (D : MirrorData)
def Point : Ambient → Type
  | torus => D.Torus
  | euclidean => Fin 4 → ℝ
def Site : Ambient → Type
  | torus => PeriodicLattice.Site D.L D.m (D.K : ℕ)
  | euclidean => InfiniteLattice.LatticePoint D.mesh
def Bond : Ambient → Type
  | torus => PeriodicLattice.Bond D.L D.m (D.K : ℕ)
  | euclidean => InfiniteLattice.Link D.mesh
def Plaquette : Ambient → Type
  | torus => PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)
  | euclidean => InfiniteLattice.ElementaryPlaquette D.mesh
end Ambient
namespace MirrorData
variable (D : MirrorData)
def projection (y : Fin 4 → ℝ) : D.Torus :=
  TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y
def IsLiftOf (x : D.Torus) (y : Fin 4 → ℝ) : Prop :=
  PeriodicLattice.IsLevelLift D.L D.m D.K D.K x y
theorem isLiftOf_iff (x : D.Torus) (y : Fin 4 → ℝ) : D.IsLiftOf x y ↔ D.projection y = x := by
  have hunit : ∀ r : ℝ, PeriodicLattice.toLevelUnits D.L D.K D.K r = r := by
    intro r
    simp [PeriodicLattice.toLevelUnits, PeriodicLattice.levelDepth]
  constructor
  · rintro ⟨v, hv, hy⟩
    funext μ
    have : y μ = v μ := by rw [hy μ, hunit]
    simp only [projection, TorusMetric.torusProj]
    rw [this]
    exact hv μ
  · intro h
    refine ⟨y, fun μ => congrFun h μ, fun μ => (hunit _).symm⟩
def shift (x : D.Torus) (v : Fin 4 → ℝ) : D.Torus :=
  PeriodicLattice.shiftBy D.L D.m D.K D.K x v
def shiftSet (Z : Set D.Torus) (v : Fin 4 → ℝ) : Set D.Torus := (fun x => D.shift x v) '' Z
end MirrorData
def intCombination (α : ℝ) (w : Fin 4 → ℤ) : Fin 4 → ℝ :=
  α • ∑ μ, (w μ : ℝ) • PeriodicLattice.coordVec μ
def coordSet (μ : Fin 4) (P : ℝ → Prop) : Set (Fin 4 → ℝ) := {y | P (y μ)}
def translateSet (A : Set ℝ) (α : ℝ) : Set ℝ := {t | ∃ α' ∈ A, t = α' + α}
namespace MirrorData
variable (D : MirrorData)
def periodize (A : Set ℝ) : Set ℝ := {t | ∃ α' ∈ A, ∃ n : ℤ, t = α' + D.side * n}
def Induces (s' : (Fin 4 → ℝ) → Fin 4 → ℝ) (s : D.Torus → D.Torus) : Prop :=
  s ∘ D.projection = D.projection ∘ s'
end MirrorData
end YangMills.Construction.ReflectionPositivity.AxisMirror
