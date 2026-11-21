import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.GridElementaryProperties
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def axisReflection (μ : Fin 4) (k : ℤ) (y : ℝ) : ℝ :=
  2 * (g.origin μ + k * g.cellSide) - y
theorem axisReflection_involutive (μ : Fin 4) (k : ℤ) :
    Function.Involutive (g.axisReflection μ k) := by
  intro y
  simp [axisReflection]
def axisReflectionPerm (μ : Fin 4) (k : ℤ) : Equiv.Perm ℝ :=
  Function.Involutive.toPerm (g.axisReflection μ k) (g.axisReflection_involutive μ k)
def axisGroup (μ : Fin 4) : Subgroup (Equiv.Perm ℝ) :=
  Subgroup.closure (range (g.axisReflectionPerm μ))
def reflectElem (μ : Fin 4) (k : ℤ) : g.reflectionGroup :=
  ⟨g.reflectPerm μ k, Subgroup.subset_closure ⟨(μ, k), rfl⟩⟩
def ReflectionGroupIsDihedralProduct : Prop :=
  (∀ μ, (∀ f : Equiv.Perm ℝ, f ∈ g.axisGroup μ ↔
        (∃ k : ℤ, ⇑f = g.axisReflection μ k) ∨ ∃ t : ℤ, ∀ y, f y = y + 2 * t * g.cellSide) ∧
      Nonempty (g.axisGroup μ ≃* DihedralGroup 0)) ∧
    (∃ φ : (∀ μ, g.axisGroup μ) ≃* g.reflectionGroup,
      ∀ (f : ∀ μ, g.axisGroup μ) (x : AmbientSpace) (μ : Fin 4), (φ f).1 x μ = (f μ).1 (x μ)) ∧
    ∀ r ∈ g.reflectionGroup, r '' (D.gridPoints : Set AmbientSpace) = D.gridPoints
def UniqueElementMapsCell : Prop :=
  ∀ C ∈ g.cellSet, ∀ C' ∈ g.cellSet, ∃! r : g.reflectionGroup, r.1 '' C = C'
def OrientationSignIsHom : Prop :=
  (∃ χ : g.reflectionGroup →* ℤˣ, ∀ r : g.reflectionGroup, χ r = orientationSign r.1) ∧
    (∀ (μ : Fin 4) (k : ℤ), orientationSign (g.reflect μ k) = -1) ∧
    ∀ t : Fin 4 → ℤ, ∃ r ∈ g.reflectionGroup,
      (r : AmbientSpace → AmbientSpace) = translate (fun μ => 2 * g.cellSide * t μ) ∧
        orientationSign r = 1
def TransportLaws : Prop :=
  (∀ C ∈ g.cellSet, ∀ C' ∈ g.cellSet, ∀ C'' ∈ g.cellSet,
    ∀ F ∈ cellObservables (D := D) C, ∀ F' ∈ cellObservables (D := D) C,
      g.transportTo C C' F ∈ cellObservables (D := D) C' ∧
      g.transportTo C C F = F ∧
      g.transportTo C' C'' (g.transportTo C C' F) = g.transportTo C C'' F ∧
      g.transportTo C C' (F * F') = g.transportTo C C' F * g.transportTo C C' F' ∧
      g.transportTo C C' (F + F') = g.transportTo C C' F + g.transportTo C C' F' ∧
      g.transportTo C C' (fun U => starRingEnd ℂ (F U)) =
        (fun U => starRingEnd ℂ (g.transportTo C C' F U)) ∧
      g.transportTo C C' 1 = 1 ∧
      ∀ (μ : Fin 4) (k : ℤ),
        (fun U => starRingEnd ℂ
          ((g.toLatticeSym (g.reflectElem μ k)).actOn (g.transportTo C C' F) U)) =
          g.transportTo C (g.reflect μ k '' C') F) ∧
    ∀ C ∈ g.cellSet, ∀ F ∈ cellObservables (D := D) C,
      (g.transportTo C g.baseCell F ∈ cellObservables (D := D) g.baseCell ∧
        g.transportTo g.baseCell C (g.transportTo C g.baseCell F) = F) ∧
      ∀ F' ∈ cellObservables (D := D) g.baseCell, g.transportTo g.baseCell C F' = F →
        F' = g.transportTo C g.baseCell F
def InducedTorusMapsFormQuotient : Prop :=
  ∃ φ : g.reflectionGroup →* Equiv.Perm D.Torus,
    (∀ r : g.reflectionGroup, D.proj ∘ r.1 = φ r ∘ D.proj) ∧
    φ.ker = D.periodTranslations.subgroupOf g.reflectionGroup ∧
    (fun e : Equiv.Perm D.Torus => (e : D.Torus → D.Torus)) '' (φ.range : Set _) =
      g.inducedTorusMaps ∧
    φ.range = Subgroup.closure (range fun p : Fin 4 × ℤ => φ (g.reflectElem p.1 p.2))
end ReflectionGrid
def ReflectionGroupAndTransport.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    g.ReflectionGroupIsDihedralProduct ∧ g.UniqueElementMapsCell ∧ g.OrientationSignIsHom ∧
    g.TransportLaws ∧
    (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      g.DescendsToTorus ∧ g.InducedTorusMapsFormQuotient ∧ g.TorusGroupQuotient) ∧
    ∀ (b : ℕ) (k : Fin 4 → ℤ),
      (g.coarsen b k).IsCoarse ∧ (g.coarsen b k).cellSide = (D.L : ℝ) ^ b * g.cellSide ∧
        (g.coarsen b k).origin = fun μ => g.origin μ + g.cellSide * k μ
end YangMills.Construction.ChessboardTori
end
