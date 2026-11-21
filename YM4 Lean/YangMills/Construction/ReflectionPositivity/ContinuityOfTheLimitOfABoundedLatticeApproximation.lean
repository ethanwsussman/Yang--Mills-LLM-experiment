import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContinuity
def SatisfiesDifferenceBound (σ : SeparatedTuples.SepTuple → ℝ)
    (C : ∀ k : ℕ, (Fin k → Set InfiniteLattice.AmbientSpace) → ℝ)
    (N : SeparatedTuples.RealValued → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set InfiniteLattice.AmbientSpace, (∀ l, IsCompact (A l)) →
    Pairwise (Function.onFun Disjoint A) →
    ∀ (f g : Fin k → SeparatedTuples.RealValued)
      (hf : SeparatedTuples.IsDisjointlySupported (List.ofFn f))
      (hg : SeparatedTuples.IsDisjointlySupported (List.ofFn g)),
      (∀ l, tsupport (f l) ∪ tsupport (g l) ⊆ A l) →
      |σ ⟨List.ofFn f, hf⟩ - σ ⟨List.ofFn g, hg⟩| ≤
        C k A * ∑ l, N (f l - g l) * ∏ l' ∈ Finset.univ.erase l, max (N (f l')) (N (g l'))
def TranslationContinuousOnTuples (σ : SeparatedTuples.SepTuple → ℝ) : Prop :=
  ∀ (X Y : SeparatedTuples.SepTuple) (v : InfiniteLattice.AmbientSpace),
    SeparatedTuples.SepTuple.Composable Y
      (SeparatedTuples.push (SeparatedTuples.translate v) X) →
    ∃ δ : ℝ, 0 < δ ∧
      (∀ w : InfiniteLattice.AmbientSpace, LatticeConventions.euclidNorm (w - v) ≤ δ →
        SeparatedTuples.SepTuple.Composable Y
            (SeparatedTuples.push (SeparatedTuples.translate w) X) ∧
          SeparatedTuples.SepTuple.Composable
            (SeparatedTuples.push (SeparatedTuples.translate w) X) Y) ∧
      Tendsto (fun w : InfiniteLattice.AmbientSpace =>
          σ (SeparatedTuples.SepTuple.juxt Y
            (SeparatedTuples.push (SeparatedTuples.translate w) X))) (𝓝 v)
        (𝓝 (σ (SeparatedTuples.SepTuple.juxt Y
          (SeparatedTuples.push (SeparatedTuples.translate v) X)))) ∧
      Tendsto (fun w : InfiniteLattice.AmbientSpace =>
          σ (SeparatedTuples.SepTuple.juxt
            (SeparatedTuples.push (SeparatedTuples.translate w) X) Y)) (𝓝 v)
        (𝓝 (σ (SeparatedTuples.SepTuple.juxt
          (SeparatedTuples.push (SeparatedTuples.translate v) X) Y)))
def TranslationContinuousOnSpans (σ : SeparatedTuples.TupleFunctional) : Prop :=
  ∀ (Z W : SeparatedTuples.FormalSpan) (v : InfiniteLattice.AmbientSpace),
    (∀ X ∈ Z.support, ∀ Y ∈ W.support, SeparatedTuples.SepTuple.Composable Y
      (SeparatedTuples.push (SeparatedTuples.translate v) X)) →
    ∃ δ : ℝ, 0 < δ ∧
      (∀ w : InfiniteLattice.AmbientSpace, LatticeConventions.euclidNorm (w - v) ≤ δ →
        ∀ X ∈ Z.support, ∀ Y ∈ W.support,
        SeparatedTuples.SepTuple.Composable Y
            (SeparatedTuples.push (SeparatedTuples.translate w) X) ∧
          SeparatedTuples.SepTuple.Composable
            (SeparatedTuples.push (SeparatedTuples.translate w) X) Y) ∧
      Tendsto (fun w : InfiniteLattice.AmbientSpace =>
          σ.spanExtension (SeparatedTuples.formalMul W
            (SeparatedTuples.pushSpan (SeparatedTuples.translate w) Z))) (𝓝 v)
        (𝓝 (σ.spanExtension (SeparatedTuples.formalMul W
          (SeparatedTuples.pushSpan (SeparatedTuples.translate v) Z)))) ∧
      Tendsto (fun w : InfiniteLattice.AmbientSpace =>
          σ.spanExtension (SeparatedTuples.formalMul
            (SeparatedTuples.pushSpan (SeparatedTuples.translate w) Z) W)) (𝓝 v)
        (𝓝 (σ.spanExtension (SeparatedTuples.formalMul
          (SeparatedTuples.pushSpan (SeparatedTuples.translate v) Z) W)))
def LimitIsContinuousFunctional : Prop :=
  ∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L)
    (C : ∀ k : ℕ, (Fin k → Set InfiniteLattice.AmbientSpace) → ℝ)
    (σ : SeparatedTuples.SepTuple → ℝ),
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
    ApproximatingSequences.LatticeApproximation.IsC1ConstantFamily T C →
    LimitConventions.ApproxTriple.ConvergesTo T σ →
    ∃ F : SeparatedTuples.TupleFunctional, F.toFun = σ ∧ F.IsPermInvariant ∧ F.IsEntrywiseLinear ∧
      SatisfiesDifferenceBound σ C TestFunctions.c1NormR4 ∧ F.IsAdmissiblyContinuous ∧
      (∀ M : ℝ, 1 ≤ M → SatisfiesDifferenceBound σ C (TestFunctions.sharpNormR4 M)) ∧
      TranslationContinuousOnTuples σ ∧ TranslationContinuousOnSpans F
end YangMills.Construction.ReflectionPositivity.LimitContinuity
end
