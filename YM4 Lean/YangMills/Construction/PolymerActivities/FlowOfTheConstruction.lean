import YangMills.Construction.FlowConstants.ReferenceWindow
import YangMills.Construction.PolymerActivities.GaussianNormaliserFunctionalOfAStep
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set ParameterChoice
noncomputable section
namespace PeriodicLattice
namespace CubesOfStep
namespace TorusExpansions
variable {c : ChoiceUpToDegreeConstants} {K k : ℕ} {x : ℕ → ℝ} {m' : ℕ} {C : Fin 2 → ℝ}
  {s : ActivityDomainKind}
variable (E : TorusExpansions c K k x m' C s)
def HasRealStiffness (F : EffectiveAction.TorusActivityFamily c.L K (k + 1)) : Prop :=
  E.sizes.IsConsistent F ∧ ∃ b : ℝ, EffectiveAction.HasStiffness c.εv c.L K (k + 1)
    (c.L ^ m') (E.sizes.infiniteVolumeFamily F) (b : ℂ)
def couplingShift : ℝ := (E.sizes.infiniteVolumeStiffness c.εv E.fullFamilies).re
def unmarkedCouplingShift : ℝ :=
  (E.sizes.infiniteVolumeStiffness c.εv E.unmarkedFamilies).re
def markedCouplingShift : ℝ :=
  (E.sizes.infiniteVolumeStiffness c.εv E.markedFamilies).re
end TorusExpansions
variable (c : ChoiceUpToDegreeConstants) (K : ℕ) (C : Fin 2 → ℝ) (s : ActivityDomainKind)
abbrev logCubeSide : ℕ := Nat.log c.L c.M
abbrev FlowExpansions (t : ℕ) (x : ℕ → ℝ) : Type 1 :=
  ∀ k : Fin t, TorusExpansions c K k x (logCubeSide c) C s
abbrev FlowRemainders : Type := ℝ → ∀ n : ℕ, ℕ → LocalActivities c.L n K
structure PriorStepsCompleted {t : ℕ} {x : ℕ → ℝ} (R : FlowExpansions c K C s t x)
    (ρ : ∀ n : ℕ, ℕ → LocalActivities c.L n K) (E₀ : ℝ) (k : Fin t) : Prop where
  families_mem : ∀ n ∈ (R k).sizes.sizes,
    AreCompletedFamilies c x (m := n) (K := K) ((R k).params n) C s ((R k).completed n) k E₀
  unmarked_eq : ∀ n ∈ (R k).sizes.sizes, ∀ i : Fin t, i < k →
    ((R k).completed n).unmarked ((i : ℕ) + 1) = (R i).unmarkedFamilies n
  marked_eq : ∀ n ∈ (R k).sizes.sizes, ∀ i : Fin t, i < k →
    ((R k).completed n).marked ((i : ℕ) + 1) = (R i).markedFamilies n
  unmarkedShift_eq : ∀ n ∈ (R k).sizes.sizes, ∀ i : Fin t, i < k →
    ((R k).completed n).unmarkedShift ((i : ℕ) + 1) = (R i).unmarkedCouplingShift
  markedShift_eq : ∀ n ∈ (R k).sizes.sizes, ∀ i : Fin t, i < k →
    ((R k).completed n).markedShift ((i : ℕ) + 1) = (R i).markedCouplingShift
  parts_defined : ∀ i : Fin t, i < k → (R i).HasRealStiffness (R i).unmarkedFamilies ∧
    (R i).HasRealStiffness (R i).markedFamilies
  remainder_eq : ∀ n ∈ (R k).sizes.sizes, ∀ i : ℕ, 1 ≤ i → i ≤ k →
    ((R k).completed n).remainder i = ρ n i
structure IsFlow {t : ℕ} {x : ℕ → ℝ} (R : FlowExpansions c K C s t x)
    (N : ChoiceConstants c) (ρ : FlowRemainders c K) (E₀ β : ℝ) : Prop where
  level_le : t ≤ K
  init_eq : x 0 = β
  beta_pos : 0 < β
  bound_pos : 0 < E₀
  params_eq : ∀ k : Fin t, ∀ n ∈ (R k).sizes.sizes, (R k).params n = N
  completed : ∀ k : Fin t, PriorStepsCompleted c K C s R (ρ β) E₀ k
  shift_defined : ∀ k : Fin t, (R k).HasRealStiffness (R k).fullFamilies
  succ_eq : ∀ k : Fin t, x ((k : ℕ) + 1) = x k - (R k).couplingShift
structure IsRegularFlow {t : ℕ} {x : ℕ → ℝ} (R : FlowExpansions c K C s t x)
    (N : ChoiceConstants c) (ρ : FlowRemainders c K) (E₀ β : ℝ) : Prop
    extends IsFlow c K C s R N ρ E₀ β where
  sizes_eq : ∀ k k' : Fin t, (R k).sizes.sizes = (R k').sizes.sizes
  mem_regularClass : ∀ k : Fin t, (k : ℕ) + 1 < t → ∀ n ∈ (R k).sizes.sizes,
    (R k).fullFamilies n ∈ N.rootedBoundedClass C c.q x s K ((k : ℕ) + 1) c.κ E₀
      (connectedRegions c.L n (coarseCubeIndex K N.cubeExp ((k : ℕ) + 1)))
  last_mem : ∃ (Cf : ℝ) (y : ℕ → ℝ), ∀ k : Fin t, (k : ℕ) + 1 = t →
    (∀ ι : Fin 2, min (Thresholds.couplingRadius C c.q x ι k)
      (Thresholds.couplingRadius C c.q x ι ((k : ℕ) + 1)) ≤
      Thresholds.couplingRadius C c.q y ι ((k : ℕ) + 1)) ∧
    ∀ n ∈ (R k).sizes.sizes, (R k).fullFamilies n ∈
      N.rootedBoundedClass C c.q y s K ((k : ℕ) + 1) c.κ Cf
        (connectedRegions c.L n (coarseCubeIndex K N.cubeExp ((k : ℕ) + 1)))
  one_lt : ∀ k ≤ t, 1 < x k
variable (N : ChoiceConstants c) (ρ : FlowRemainders c K)
def IsConstructionFlow (E₀ β : ℝ) (t : ℕ) (x : ℕ → ℝ) : Prop :=
  ∃ R : FlowExpansions c K C s t x, IsRegularFlow c K C s R N ρ E₀ β
def maxFlowLevel (E₀ β : ℝ) : ℕ∞ :=
  sSup {d | ∃ (t : ℕ) (x : ℕ → ℝ), d = (t : ℕ∞) ∧ IsConstructionFlow c K C s N ρ E₀ β t x}
def flowOfInverseCoupling (E₀ β : ℝ) : ℕ → ℝ :=
  Classical.epsilon fun x => ∀ t : ℕ, (t : ℕ∞) ≤ maxFlowLevel c K C s N ρ E₀ β →
    IsConstructionFlow c K C s N ρ E₀ β t x
variable {c K C s N ρ}
end CubesOfStep
end PeriodicLattice
namespace FlowConstants
open PeriodicLattice.CubesOfStep
variable (T : DerivedConstants) (a : FullChoice) (K : ℕ)
  (s : PeriodicLattice.ActivityDomainKind)
  (ρ : FlowRemainders
    a.toChoiceUpToDegreeConstants K)
def flowFirstPassageWindow (g : ℝ) : Set ℝ :=
  firstPassageWindow T a.toChoiceUpToCoupling
    (flowOfInverseCoupling _ K ![a.C₀, a.C₁] s (PeriodicLattice.ChoiceConstants.ofFullChoice T a)
      ρ a.E₀)
    (maxFlowLevel _ K ![a.C₀, a.C₁] s (PeriodicLattice.ChoiceConstants.ofFullChoice T a) ρ a.E₀) g K
end FlowConstants
end
end YangMills.Construction
