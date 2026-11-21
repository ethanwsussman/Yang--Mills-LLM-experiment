import YangMills.Construction.TorusOrFourSpace.ApproximationByMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.SequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SeparatedExtension
open Kind
open YangMills.Construction.Sequences
section Preliminaries
variable {D : Params} {E : Kind} {J₀ : PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞} {C : BoundFamily}
def IsGoodThreshold (Ψ : BoundedC1FormSeq D E J₀ ρ C) (θ : RadiusRatio) (n : ℕ)
    (hn : 2 ≤ n) (R' : ℝ) (hR' : 0 < R') (j₁ : ℤ) : Prop :=
  ∀ j : J₀.carrier, j₁ ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
    Ψ.thresholdAtRadius θ n hn R' hR' ≤ (((j.1 : ℕ+) : ℕ) : ℤ) ∧ ENNReal.ofReal R' < ρ j
def HasLimitAt (Ψ : BoundedC1FormSeq D E J₀ ρ C) {J : PNatIndexSet}
    (hJ : J.carrier ⊆ J₀.carrier) (n : ℕ) (hn : 2 ≤ n) (g : FnTuple D E n) : Prop :=
  ∃ (j' : ℤ) (hg : ∀ j : (J.filterGe j').carrier,
      g ∈ sepC1TuplesInBall D E n (ρ ⟨j.1, hJ j.2.1⟩)),
    IndexedLimits.LimitExistsAlong J j' fun j =>
      ((Ψ.func ⟨j.1, hJ j.2.1⟩ n hn ⟨g, hg j⟩ : ℝ) : ℂ)
def EventuallyDefinedAlong (_Ψ : BoundedC1FormSeq D E J₀ ρ C) {J : PNatIndexSet}
    (hJ : J.carrier ⊆ J₀.carrier) : Prop :=
  ∀ n, 2 ≤ n → ∀ f ∈ sepC1Tuples D E n,
    DiagonalLimits.EventuallyAlong J fun j =>
      ∀ hj : j ∈ J.carrier, f ∈ sepC1TuplesInBall D E n (ρ ⟨j, hJ hj⟩)
def restrictFamily (Ψ : BoundedC1FormSeq D E J₀ ρ C) {J : PNatIndexSet}
    (hJ : J.carrier ⊆ J₀.carrier) (hdef : EventuallyDefinedAlong Ψ hJ) :
    IndexedFunctionalFamily D E J where
  dom j n := sepC1TuplesInBall D E n (ρ ⟨j.1, hJ j.2⟩)
  func j n hn f := Ψ.func ⟨j.1, hJ j.2⟩ n hn f
  eventually_mem_dom := hdef
end Preliminaries
section Parts
variable (D : Params) (E : Kind)
def ApproximantValuesClose (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∀ (J₀ : PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞) (Ψ : BoundedC1FormSeq D E J₀ ρ C)
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (f : FnTuple D E n)
    (hf : f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r)) (d : ℝ) (hd : 0 < d),
    ENNReal.ofReal d ≤ supportGap D E f →
      (∃ j₁ : ℤ, IsGoodThreshold Ψ θ n hn (r + d / 3) (add_pos hr (div_pos hd three_pos)) j₁) ∧
      ∀ j₁ : ℤ, IsGoodThreshold Ψ θ n hn (r + d / 3) (add_pos hr (div_pos hd three_pos)) j₁ →
        ∀ ε : ℝ, 0 < ε → ∀ φ : FnTuple D E n,
          DiagonalLimits.IsFamilyApproximant D E f hf.1 d hd F ε φ →
          ∀ j : J₀.carrier, j₁ ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
            ∃ (hfj : f ∈ sepC1TuplesInBall D E n (ρ j))
              (hφj : φ ∈ sepC1TuplesInBall D E n (ρ j)),
              |Ψ.func j n hn ⟨f, hfj⟩ - Ψ.func j n hn ⟨φ, hφj⟩| ≤
                effConstAt P E C n (d / 3) (r + d / 3) *
                  DiagonalLimits.approxDefect D E f ε
def OneIsGoodThresholdForHierarchies (θ : RadiusRatio) (C : BoundFamily) : Prop :=
  ∀ (J₀ : PNatIndexSet) (Ψ : BoundedC1FormSeq D E J₀ (fun _ => ∞) C),
    Ψ.IsHierarchyFamily →
    ∀ (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (f : FnTuple D E n),
      f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r) →
      ∀ (d : ℝ) (hd : 0 < d), ENNReal.ofReal d ≤ supportGap D E f →
        IsGoodThreshold Ψ θ n hn (r + d / 3) (add_pos hr (div_pos hd three_pos)) 1
def FamilyLimitsExtend (F : DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∀ (J₀ : PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞) (Ψ : BoundedC1FormSeq D E J₀ ρ C)
    (J : PNatIndexSet) (hJ : J.carrier ⊆ J₀.carrier),
    (∀ (m : ℕ) (hm : 2 ≤ m) (φ : FnTuple D E m),
      (⟨m, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuplesGeTwo →
        HasLimitAt Ψ hJ m hm φ) →
    ∃ (hdef : EventuallyDefinedAlong Ψ hJ) (Φ : Hierarchy D E),
      (restrictFamily Ψ hJ hdef).TendsToOnSep Φ ∧ Φ ∈ boundedHierarchies D E C
end Parts
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily),
    ApproximantValuesClose D E θ P F C ∧
    OneIsGoodThresholdForHierarchies D E θ C ∧
    FamilyLimitsExtend D E F C
end YangMills.Construction.PeriodicSpace.SeparatedExtension
