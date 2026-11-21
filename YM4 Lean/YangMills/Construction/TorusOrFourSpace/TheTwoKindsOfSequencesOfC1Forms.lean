import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.SequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.C1FormSeqKinds
open Kind
variable (D : Params) (E : Kind)
def EventuallyInDomains : Prop :=
  ∀ (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞) (_Ψ : C1FormSeq D E J₀ ρ) (n : ℕ),
    2 ≤ n → ∀ f ∈ sepC1Tuples D E n,
      ∃ jf : ℤ, ∀ j : J₀.carrier, jf ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
        f ∈ sepC1TuplesInBall D E n (ρ j)
def C1SubmoduleLeLipschitz (A : Set (E.Pt D)) : Prop :=
  ∃ W W' : Submodule ℝ (E.Pt D → ℝ),
    (W : Set (E.Pt D → ℝ)) = c1SupportedIn D E A ∧
      (W' : Set (E.Pt D → ℝ)) = lipschitzSupportedIn D E A ∧ W ≤ W'
def RestrictionsAreC1FormSeq (C : BoundFamily) : Prop :=
  ∀ (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (Φ : BoundedPartialHierarchySeq D E J₀ ρ C),
    (∀ (j : J₀.carrier) (n : ℕ), 1 ≤ n →
      sepC1TuplesInBall D E n (ρ j) ⊆
        sepLipTuplesWithin D E n (centredBall D E (ρ j))) ∧
    (∀ A : Set (E.Pt D), C1SubmoduleLeLipschitz D E A) ∧
    ∃ Ψ : BoundedC1FormSeq D E J₀ ρ C, Ψ.IsRestrictionOf Φ
variable {D E}
def RealizesFamily {J₀ : Sequences.PNatIndexSet} {C : BoundFamily}
    (Ψ : BoundedC1FormSeq D E J₀ (fun _ => ∞) C) (Φ : J₀.carrier → Hierarchy D E) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : R ∈ allowedRadii D E), Ψ.threshold n hn R hR = 1) ∧
  ∀ (j : J₀.carrier) (n : ℕ) (hn : 2 ≤ n) (f : sepC1TuplesInBall D E n ∞),
    Ψ.func j n hn f = (Φ j).func n hn ⟨f.1, f.2.1⟩
theorem RealizesFamily.isHierarchyFamily {J₀ : Sequences.PNatIndexSet} {C : BoundFamily}
    {Ψ : BoundedC1FormSeq D E J₀ (fun _ => ∞) C} {Φ : J₀.carrier → Hierarchy D E}
    (h : RealizesFamily Ψ Φ) (hΦ : ∀ j, Φ j ∈ boundedHierarchies D E C) :
    Ψ.IsHierarchyFamily :=
  ⟨h.1, Φ, hΦ, h.2⟩
variable (D E)
def FamilyIsC1FormSeq (θ : RadiusRatio) (C : BoundFamily) (J₀ : Sequences.PNatIndexSet)
    (Φ : J₀.carrier → Hierarchy D E) : Prop :=
  ∃ Ψ : BoundedC1FormSeq D E J₀ (fun _ => ∞) C, RealizesFamily Ψ Φ ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R), Ψ.thresholdAtRadius θ n hn R hR = 1
def allPNat : Sequences.PNatIndexSet :=
  ⟨Set.univ, Set.infinite_univ⟩
def HierarchyFamiliesAreC1FormSeqs (θ : RadiusRatio) (C : BoundFamily) : Prop :=
  (∀ (J₀ : Sequences.PNatIndexSet) (Φ : J₀.carrier → Hierarchy D E),
    (∀ j, Φ j ∈ boundedHierarchies D E C) → FamilyIsC1FormSeq D E θ C J₀ Φ) ∧
  ∀ Φ ∈ boundedHierarchies D E C, FamilyIsC1FormSeq D E θ C allPNat fun _ => Φ
def Statement : Prop :=
  ∀ (D : Params) (θ : RadiusRatio) (E : Kind) (C : BoundFamily),
    EventuallyInDomains D E ∧
    RestrictionsAreC1FormSeq D E C ∧
    HierarchyFamiliesAreC1FormSeqs D E θ C
end YangMills.Construction.PeriodicSpace.C1FormSeqKinds
end
