import YangMills.Construction.ReflectionPositivity.FrameOfFunctionalsOnSeparatedTuplesDefs
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open Filter Function Topology
open scoped Matrix
noncomputable section
namespace YangMills.Construction.SeparatedTuples
open InfiniteLattice (AmbientSpace)
open Mirrors (ReflectingHyperplane)
open SeparatedTupleFunctionals (c1CompactSuppIn)
open TestFunctions (partialDerivR4)
namespace BasicFacts
theorem linearCombination_mem_c1CompactSuppIn {U : Set AmbientSpace} {f g : RealValued}
    (hf : f ∈ c1CompactSuppIn ℝ U) (hg : g ∈ c1CompactSuppIn ℝ U) (a b : ℝ) :
    a • f + b • g ∈ c1CompactSuppIn ℝ U := by
  obtain ⟨⟨⟨hfc, hfk⟩, hfd⟩, hfs⟩ := hf
  obtain ⟨⟨⟨hgc, hgk⟩, hgd⟩, hgs⟩ := hg
  have hsub : tsupport (a • f + b • g) ⊆ tsupport f ∪ tsupport g := by
    refine closure_minimal (fun x hx => ?_) (isClosed_closure.union isClosed_closure)
    by_contra hn
    have hfx : f x = 0 := by
      by_contra hne
      exact hn (Or.inl (subset_closure hne))
    have hgx : g x = 0 := by
      by_contra hne
      exact hn (Or.inr (subset_closure hne))
    exact hx (by simp [hfx, hgx])
  refine ⟨⟨⟨(hfc.const_smul a).add (hgc.const_smul b),
    (hfk.union hgk).of_isClosed_subset isClosed_closure hsub⟩, fun j => ?_⟩,
    hsub.trans (Set.union_subset hfs hgs)⟩
  obtain ⟨hfdiff, hfcont⟩ := hfd j
  obtain ⟨hgdiff, hgcont⟩ := hgd j
  have hderiv : ∀ x : AmbientSpace, HasDerivAt
      (fun t : ℝ => (a • f + b • g) (x + t • Pi.single j (1 : ℝ)))
      (a * partialDerivR4 j f x + b * partialDerivR4 j g x) 0 := fun x =>
    ((hfdiff x).hasDerivAt.const_mul a).add ((hgdiff x).hasDerivAt.const_mul b)
  refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
  have heq : partialDerivR4 j (a • f + b • g) =
      fun x => a * partialDerivR4 j f x + b * partialDerivR4 j g x :=
    funext fun x => (hderiv x).deriv
  rw [heq]
  exact (continuous_const.mul hfcont).add (continuous_const.mul hgcont)
def c1CompactSubmodule (U : Set AmbientSpace) : Submodule ℝ RealValued where
  carrier := c1CompactSuppIn ℝ U
  zero_mem' := by
    have hempty : tsupport (0 : RealValued) = ∅ := tsupport_zero
    have hderiv : ∀ (j : Fin 4) (x : AmbientSpace), HasDerivAt
        (fun t : ℝ => (0 : RealValued) (x + t • Pi.single j (1 : ℝ))) 0 0 :=
      fun _ _ => hasDerivAt_const _ _
    have hcpt : IsCompact (tsupport (0 : RealValued)) := by
      rw [hempty]
      exact isCompact_empty
    have hin : tsupport (0 : RealValued) ⊆ U := by
      rw [hempty]
      exact Set.empty_subset U
    refine ⟨⟨⟨continuous_const, hcpt⟩, fun j =>
      ⟨fun x => (hderiv j x).differentiableAt, ?_⟩⟩, hin⟩
    have heq : partialDerivR4 j (0 : RealValued) = fun _ => 0 :=
      funext fun x => (hderiv j x).deriv
    rw [heq]
    exact continuous_const
  add_mem' := by
    intro f g hf hg
    simpa using linearCombination_mem_c1CompactSuppIn hf hg 1 1
  smul_mem' := by
    intro a f hf
    simpa using linearCombination_mem_c1CompactSuppIn hf hf a 0
def IsometryActionOnTuples : Prop :=
  ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → ∀ X Y : SepTuple,
    IsDisjointlySupported (pushList r X.1) ∧
    (∀ i, i < X.size → tsupport ((push r X).componentAt i) = r '' tsupport (X.componentAt i)) ∧
    (SepTuple.Composable (push r X) (push r Y) ↔ SepTuple.Composable X Y) ∧
    (SepTuple.Composable X Y →
      SepTuple.juxt (push r X) (push r Y) = push r (SepTuple.juxt X Y))
def SeparatedOfLinearCombinationInOneEntry : Prop :=
  ∀ (P Q : List RealValued) (f g : RealValued) (a b : ℝ),
    IsDisjointlySupported (P ++ f :: Q) → IsDisjointlySupported (P ++ g :: Q) →
      IsDisjointlySupported (P ++ (a • f + b • g) :: Q)
def ReflectedJuxtapositionAtHyperplane : Prop :=
  ∀ (H : ReflectingHyperplane) (X Y : SepTuple),
    X ∈ supportedIn H.positiveSide → Y ∈ supportedIn H.positiveSide →
    (∀ f ∈ (push H.reflect X).1, tsupport f ⊆ {x | H.normalVec ⬝ᵥ x < H.offset}) ∧
    SepTuple.Composable (push H.reflect X) Y
def IsMultilinearOnC1Spaces (σ : TupleFunctional) {k : ℕ} (U : Fin k → Set AmbientSpace) : Prop :=
  ∃ Φ : MultilinearMap ℝ (fun i => c1CompactSubmodule (U i)) ℝ,
    ∀ f : (i : Fin k) → c1CompactSubmodule (U i),
      ∃ T : SepTuple, T.1 = List.ofFn (fun i => (f i : RealValued)) ∧ Φ f = σ T
def EntrywiseLinearIffMultilinearOnC1 : Prop :=
  ∀ σ : TupleFunctional, σ.IsEntrywiseLinear ↔
    ∀ k : ℕ, 1 ≤ k → ∀ U : Fin k → Set AmbientSpace, (∀ i, IsOpen (U i)) →
      Pairwise (Disjoint on fun i => closure (U i)) → IsMultilinearOnC1Spaces σ U
def PushSpanProperties : Prop :=
  ∀ r s : AmbientSpace → AmbientSpace, IsEuclidIsometry r → IsEuclidIsometry s →
    ∀ (v w : AmbientSpace) (F : FormalSpan),
    pushSpan (r ∘ s) F = pushSpan r (pushSpan s F) ∧
    pushSpan (translate v) (pushSpan (translate w) F) = pushSpan (translate (v + w)) F ∧
    pushSpan (translate 0) F = F ∧
    conjugation (pushSpan r F) = pushSpan r (conjugation F) ∧
    (∀ U : Set AmbientSpace, IsOpen U →
      push r '' supportedIn U = supportedIn (r '' U) ∧
      (spanIn U).map (pushSpan r) = spanIn (r '' U)) ∧
    ∀ U V : Set AmbientSpace, IsOpen U → IsOpen V → Disjoint U V →
      ∀ G ∈ spanIn U, ∀ G' ∈ spanIn V,
        formalMul (pushSpan r G) (pushSpan r G') = pushSpan r (formalMul G G')
def TendstoAdmissiblyWithNorm (N : RealValued → ℝ) (n₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple) :
    Prop :=
  1 ≤ n₀ ∧ (∀ n, n₀ ≤ n → (s n).size = X.size) ∧
    ∃ K : Fin X.size → Set AmbientSpace, (∀ i, IsCompact (K i)) ∧ Pairwise (Disjoint on K) ∧
      (∀ n, n₀ ≤ n → ∀ i : Fin X.size,
        tsupport ((s n).componentAt i) ∪ tsupport (X.componentAt i) ⊆ K i) ∧
      ∀ i : Fin X.size, Tendsto (fun n => N ((s n).componentAt i - X.componentAt i)) atTop (𝓝 0)
def IsContinuousWithNorm (N : RealValued → ℝ) (σ : TupleFunctional) : Prop :=
  ∀ (n₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple), TendstoAdmissiblyWithNorm N n₀ s X →
    Tendsto (fun n => σ (s n)) atTop (𝓝 (σ X))
def SharpNormEquivalentToC1Norm : Prop :=
  ∀ M : ℝ, 1 ≤ M →
    (∀ (n₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple),
      TendstoAdmissibly n₀ s X ↔
        TendstoAdmissiblyWithNorm (TestFunctions.sharpNormR4 M) n₀ s X) ∧
    ∀ σ : TupleFunctional,
      σ.IsAdmissiblyContinuous ↔ IsContinuousWithNorm (TestFunctions.sharpNormR4 M) σ
def MainFacts : Prop :=
  IsometryActionOnTuples ∧ SeparatedOfLinearCombinationInOneEntry ∧
    ReflectedJuxtapositionAtHyperplane ∧ EntrywiseLinearIffMultilinearOnC1 ∧
    PushSpanProperties ∧ SharpNormEquivalentToC1Norm
end BasicFacts
end YangMills.Construction.SeparatedTuples
end
