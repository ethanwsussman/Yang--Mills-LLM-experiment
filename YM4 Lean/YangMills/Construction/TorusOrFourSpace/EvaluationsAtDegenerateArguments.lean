import YangMills.Construction.TorusOrFourSpace.ArbitraryFamilyOfDenseSets
import YangMills.Construction.TorusOrFourSpace.ConvergenceOnSeparatedTuplesAndPartialHierarchies
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.EquicontinuityInequalities
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace DiagonalLimits
def TendsToWhereDefined {𝕜 : Type*} [RCLike 𝕜] (J : Sequences.PNatIndexSet)
    (Defined : ℕ+ → Prop) (x : ∀ j, Defined j → 𝕜) (z : 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → EventuallyAlong J fun j => ∃ h : Defined j, ‖x j h - z‖ < ε
end DiagonalLimits
namespace Kind
section Numbers
variable (D : Params) (E : Kind)
def tupleRadius {n : ℕ} (φ : FnTuple D E n) : ℝ :=
  (max 1 (⨆ i, setDiam D E (supportQ D E (φ i)))).toReal
variable {D}
open Classical in
def tupleBound {θ : RadiusRatio} (P : TorusPartitionChoice D θ) (C : BoundFamily)
    {n : ℕ} (φ : FnTuple D E n) : ℝ :=
  if 2 ≤ n ∧ supportGap D E φ < ∞ then
    effConstAt P E C n (supportGap D E φ).toReal (tupleRadius D E φ) *
      ∏ i, sharpNormReal D E (φ i)
  else 0
variable {E}
theorem tupleBound_of_supportGap_lt_top {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    (C : BoundFamily) {n : ℕ} (hn : 2 ≤ n) (φ : FnTuple D E n) (hφ : supportGap D E φ < ∞) :
    tupleBound E P C φ =
      effConstAt P E C n (supportGap D E φ).toReal (tupleRadius D E φ) *
        ∏ i, sharpNormReal D E (φ i) :=
  if_pos ⟨hn, hφ⟩
theorem tupleBound_of_supportGap_eq_top {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    (C : BoundFamily) {n : ℕ} (φ : FnTuple D E n) (hφ : supportGap D E φ = ∞) :
    tupleBound E P C φ = 0 :=
  if_neg fun h => absurd h.2 (by simp [hφ])
end Numbers
section Preliminaries
variable (D : Params) (E : Kind)
def WithinDist (S S' : Set (E.Pt D)) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ y ∈ S, infDistPt D E y S' ≤ ENNReal.ofReal η
def SatisfiesSepEstimate (C : BoundFamily) {n : ℕ} (_hn : 2 ≤ n)
    (Ψ : sepC1Tuples D E n → ℝ) : Prop :=
  ∀ d R : ℝ, 0 < d → R ∈ allowedRadii D E → ∀ A : Fin n → Set (E.Pt D),
    (∀ l, ∃ S, IsClosedBallWithRadius D E S R ∧ A l ⊆ S) →
    DiagonalLimits.PairwiseSetDistGe D E A d →
    ∀ f g : sepC1Tuples D E n,
      (∀ l, supportQ D E (f.1 l) ∪ supportQ D E (g.1 l) ⊆ A l) →
      EquicontinuityBounds D E (C.val n d R) (Ψ f) (Ψ g) f.1 g.1
def SupportsInBall {n : ℕ} (f : FnTuple D E n) (ρ : ℝ≥0∞) : Prop :=
  0 < ρ ∧ ρ < ∞ ∧ ∀ i, supportQ D E (f i) ⊆ centredBall D E ρ
theorem mem_sepC1TuplesInBall_of_supportsInBall {n : ℕ} {f : FnTuple D E n} {ρ : ℝ≥0∞}
    (hf : f ∈ sepC1Tuples D E n) (hρ : SupportsInBall D E f ρ) :
    f ∈ sepC1TuplesInBall D E n ρ :=
  ⟨hf, hρ.2.2⟩
def IsGapValue {n : ℕ} (f : FnTuple D E n) (d : ℝ) : Prop :=
  (supportGap D E f ≠ ∞ → d = (supportGap D E f).toReal) ∧ (supportGap D E f = ∞ → 0 < d)
end Preliminaries
namespace Hierarchy
variable {D : Params} {E : Kind}
open Classical in
def evalSigma (Φ : Hierarchy D E) (φ : Σ n : ℕ, FnTuple D E n) : ℝ :=
  if h : 2 ≤ φ.1 ∧ φ.2 ∈ sepC1Tuples D E φ.1 then
    Φ.func φ.1 h.1 ⟨φ.2, h.2⟩
  else 0
theorem evalSigma_of_sep (Φ : Hierarchy D E) {n : ℕ} (hn : 2 ≤ n)
    (f : sepC1Tuples D E n) : Φ.evalSigma ⟨n, f.1⟩ = Φ.func n hn f :=
  dif_pos ⟨hn, f.2⟩
def SatisfiesSepEstimate (Φ : Hierarchy D E) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), Kind.SatisfiesSepEstimate D E C hn (Φ.func n hn)
end Hierarchy
namespace PartialHierarchySeq
variable {D : Params} {E : Kind} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
def IsDefinedAt (_Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) {n : ℕ}
    (f : FnTuple D E n) : Prop :=
  f ∈ sepC1TuplesInBall D E n (ρ j)
open Classical in
def evalAt (Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) (n : ℕ) (hn : 2 ≤ n)
    (f : FnTuple D E n) : ℝ :=
  if h : f ∈ sepLipTuplesWithin D E n (centredBall D E (ρ j)) then
    Φ.func j n hn ⟨f, h⟩
  else 0
theorem evalAt_of_mem (Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) {n : ℕ} (hn : 2 ≤ n)
    (f : sepLipTuplesWithin D E n (centredBall D E (ρ j))) :
    Φ.evalAt j n hn f.1 = Φ.func j n hn f :=
  dif_pos f.2
def HoldsAt (Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) {n : ℕ} (hn : 2 ≤ n)
    (f : FnTuple D E n) (P : ℝ → Prop) : Prop :=
  Φ.IsDefinedAt j f ∧ P (Φ.evalAt j n hn f)
open Classical in
def evalSigma (Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier)
    (φ : Σ n : ℕ, FnTuple D E n) : ℝ :=
  if h : 2 ≤ φ.1 then Φ.evalAt j φ.1 h φ.2 else 0
def TendsToOnSepAlong (Φ : PartialHierarchySeq D E J₀ ρ) (J : Sequences.PNatIndexSet)
    (_hJ : J.carrier ⊆ J₀.carrier) (Ξ : Hierarchy D E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
    DiagonalLimits.TendsToWhereDefined J
      (fun j => ∃ hj : j ∈ J₀.carrier, Φ.IsDefinedAt ⟨j, hj⟩ f.1)
      (fun _ h => Φ.evalAt ⟨_, h.fst⟩ n hn f.1) (Ξ.func n hn f)
end PartialHierarchySeq
section Convergence
variable {D : Params} {E : Kind}
def ConvergesOnSep {J : Sequences.PNatIndexSet} (Φ : J.carrier → Hierarchy D E) : Prop :=
  ∃ Ξ : Hierarchy D E, (IndexedFunctionalFamily.ofHierarchy Φ).TendsToOnSep Ξ
def ConvergesAtSigma (Φ : ℕ+ → Hierarchy D E) (φ : Σ n : ℕ, FnTuple D E n) : Prop :=
  ∃ x : ℝ, Filter.Tendsto (fun j => (Φ j).evalSigma φ) Filter.atTop (𝓝 x)
def IsSeqClosedHierarchies (S : Set (Hierarchy D E)) : Prop :=
  ∀ (J : Sequences.PNatIndexSet) (Φ : J.carrier → Hierarchy D E) (Ξ : Hierarchy D E),
    (∀ j, Φ j ∈ S) → (IndexedFunctionalFamily.ofHierarchy Φ).TendsToOnSep Ξ →
      Ξ ∈ S
def BoundedDeterminedOn (F : DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∀ Φ ∈ boundedHierarchies D E C, ∀ Φ' ∈ boundedHierarchies D E C,
    (∀ φ ∈ F.tuples, Φ.evalSigma φ = Φ'.evalSigma φ) → Φ = Φ'
end Convergence
end Kind
end YangMills.Construction.PeriodicSpace
