import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
abbrev Params.halfEdge (D : Params) : ℝ := (D.L : ℝ) ^ (D.m : ℕ)
namespace Kind
variable (D : Params) (E : Kind)
def HasBetweenMember (G : Set (Set (E.Pt D))) : Prop :=
  ∀ S W : Set (E.Pt D), IsCompactQ D E S → IsOpenQ D E W → S ⊆ W →
    ∃ Q ∈ G, S ⊆ Q ∧ Q ⊆ W
end Kind
open Kind
def TorusBoxDiameterBound : Prop :=
  ∀ D : Params,
    (∀ x x' : Fin 4 → ℝ, TorusMetric.euclidNormVec (x - x') < D.halfEdge →
      quotDist D torus (quotMap D torus x) (quotMap D torus x') =
        TorusMetric.euclidNormVec (x - x')) ∧
    (∀ b : RationalBox, AdmitsBox D b torus ↔ b.diam < D.halfEdge) ∧
    (∀ b : RationalBox, AdmitsBox D b torus →
      (∀ x ∈ b.toSet, ∀ x' ∈ b.toSet,
        quotDist D torus (quotMap D torus x) (quotMap D torus x') =
          TorusMetric.euclidNormVec (x - x')) ∧
      Set.InjOn (quotMap D torus) b.toSet ∧
      setDiam D torus (quotMap D torus '' b.toSet) = ENNReal.ofReal b.diam) ∧
    (∀ b : RationalBox, D.halfEdge ≤ b.diam →
      ENNReal.ofReal D.halfEdge ≤ setDiam D torus (quotMap D torus '' b.toSet)) ∧
    (∀ b : RationalBox, AdmitsBox D b torus ↔
      setDiam D torus (quotMap D torus '' b.toSet) < ENNReal.ofReal D.halfEdge) ∧
    (Set.univ ∈ supportStock D torus) ∧
    ((fun _ => (1 : ℝ)) ∈ c1Set D torus) ∧
    supportQ D torus (fun _ => (1 : ℝ)) = Set.univ ∧
    ENNReal.ofReal (quotDist D torus (quotMap D torus fun _ => D.halfEdge)
      (quotMap D torus 0)) ≤ setDiam D torus Set.univ ∧
    IsLeast (Set.range fun k : Fin 4 → ℤ =>
        D.halfEdge * Real.sqrt (∑ μ, (1 - 2 * (k μ : ℝ)) ^ 2))
      (quotDist D torus (quotMap D torus fun _ => D.halfEdge) (quotMap D torus 0)) ∧
    quotDist D torus (quotMap D torus fun _ => D.halfEdge) (quotMap D torus 0) =
      2 * D.halfEdge ∧
    (∀ G : Set (Set (torus.Pt D)),
      (∀ Q ∈ G, setDiam D torus Q < ENNReal.ofReal D.halfEdge) →
        ¬ HasBetweenMember D torus G) ∧
    ∀ Q : Set (torus.Pt D), Set.univ ⊆ Q → Q ⊆ Set.univ → Q = Set.univ
end YangMills.Construction.PeriodicSpace
