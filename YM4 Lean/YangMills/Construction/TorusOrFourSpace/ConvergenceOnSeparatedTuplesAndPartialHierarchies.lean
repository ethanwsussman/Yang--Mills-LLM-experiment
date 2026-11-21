import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import YangMills.Construction.TorusOrFourSpace.LimitsAlongSetsOfIndices
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
structure IndexedFunctionalFamily (J : Sequences.PNatIndexSet) where
  dom : J.carrier → (n : ℕ) → Set (FnTuple D E n)
  func : (j : J.carrier) → (n : ℕ) → 2 ≤ n → dom j n → ℝ
  eventually_mem_dom : ∀ n, 2 ≤ n → ∀ f ∈ sepC1Tuples D E n,
    DiagonalLimits.EventuallyAlong J fun j => ∀ hj : j ∈ J.carrier, f ∈ dom ⟨j, hj⟩ n
variable {D E}
def IndexedFunctionalFamily.ofHierarchy {J : Sequences.PNatIndexSet}
    (Φ : J.carrier → Hierarchy D E) : IndexedFunctionalFamily D E J where
  dom _ n := sepC1Tuples D E n
  func j n hn f := (Φ j).func n hn f
  eventually_mem_dom _ _ _ hf := ⟨0, fun _ _ _ _ => hf⟩
def IndexedFunctionalFamily.TendsToOnSep {J : Sequences.PNatIndexSet}
    (F : IndexedFunctionalFamily D E J) (Φ : Hierarchy D E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
    ∃ (k : ℤ) (hf : ∀ j : (J.filterGe k).carrier, f.1 ∈ F.dom ⟨j.1, j.2.1⟩ n),
      IndexedLimits.ConvergesToAlong J k
        (fun j => ((F.func ⟨j.1, j.2.1⟩ n hn ⟨f.1, hf j⟩ : ℝ) : ℂ))
        ((Φ.func n hn f : ℝ) : ℂ)
variable (D E)
abbrev SepTuplesAll : Type :=
  Σ n : {n : ℕ // 2 ≤ n}, sepC1Tuples D E n.1
variable {D E}
def Hierarchy.evalAll (Φ : Hierarchy D E) : SepTuplesAll D E → ℝ :=
  fun x => Φ.func x.1.1 x.1.2 x.2
abbrev sepConvTopology (S : Set (Hierarchy D E)) : TopologicalSpace S :=
  TopologicalSpace.induced (fun Φ : S => Hierarchy.evalAll Φ.1) inferInstance
variable (E)
structure RadiiTendToTop (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞) : Prop where
  pos : ∀ j, 0 < ρ j
  eventually_gt : ∀ r : ℝ, 0 < r →
    DiagonalLimits.EventuallyAlong J₀ fun j =>
      ∀ hj : j ∈ J₀.carrier, ENNReal.ofReal r < ρ ⟨j, hj⟩
  eq_top_of_torus : E = torus → ∀ j, ρ j = ∞
variable (D)
structure PartialHierarchySeq (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞) where
  radii : RadiiTendToTop E J₀ ρ
  func : (j : J₀.carrier) → (n : ℕ) → 2 ≤ n →
    sepLipTuplesWithin D E n (centredBall D E (ρ j)) → ℝ
  multilinear : ∀ j n (hn : 2 ≤ n),
    IsMultilinearOn D E (sepLipTuplesWithin D E n (centredBall D E (ρ j)))
      (func j n hn)
  symmetric : ∀ j n (hn : 2 ≤ n),
    IsPermSymmetricOn D E (sepLipTuplesWithin D E n (centredBall D E (ρ j)))
      (func j n hn)
namespace PartialHierarchySeq
variable {D E} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
def BoundedFrom (Φ : PartialHierarchySeq D E J₀ ρ) (C : BoundFamily) (n : ℕ) (hn : 2 ≤ n)
    (R : ℝ) (k : ℤ) : Prop :=
  ∀ j : J₀.carrier, k ≤ (((j.1 : ℕ+) : ℕ) : ℤ) → ∀ d : ℝ, 0 < d →
    ∀ f : sepLipTuplesWithin D E n (centredBall D E (ρ j)),
      f.1 ∈ lipTuplesSpacedInBalls D E n d R →
        ENNReal.ofReal |Φ.func j n hn f| ≤
          ENNReal.ofReal (C.val n d R) * ∏ i, sharpNormQ D E (f.1 i)
def EventuallyBounded (Φ : PartialHierarchySeq D E J₀ ρ) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∀ R ∈ allowedRadii D E, ∃ k : ℤ, Φ.BoundedFrom C n hn R k
end PartialHierarchySeq
structure BoundedPartialHierarchySeq (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (C : BoundFamily) extends PartialHierarchySeq D E J₀ ρ where
  threshold : (n : ℕ) → 2 ≤ n → (R : ℝ) → R ∈ allowedRadii D E → ℤ
  boundedFrom : ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : R ∈ allowedRadii D E),
    toPartialHierarchySeq.BoundedFrom C n hn R (threshold n hn R hR)
variable {D E}
end YangMills.Construction.PeriodicSpace.Kind
