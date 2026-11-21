import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ApproximatingSequences
open YangMills.Construction.SeparatedTuples (IsC1c RealValued SepTuple)
open YangMills.Construction.TestFunctions (c1NormR4 sharpNormR4)
open YangMills.Construction.ReflectionPositivity.AxisMirror in
def LatticeApproximation.IsBoundedWithConstants (D : MirrorData) (T : LatticeApproximation D.L)
    (M : ℝ) (C : ∀ k : ℕ, (Fin k → Set (Fin 4 → ℝ)) → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set (Fin 4 → ℝ), (∀ i, IsCompact (A i)) →
    Pairwise (Function.onFun Disjoint A) →
    ∀ (n : ℕ+) (g : Fin k → (Fin 4 → ℝ) → ℝ),
      List.ofFn g ∈ Ambient.separatedN D .euclidean k →
      (∀ i, Ambient.closedSupport D .euclidean (g i) ⊆ A i) →
      |∫ U, T.latticeProduct n (List.ofFn g) U ∂T.state n| ≤
        C k A * ∏ i, sharpNormR4 M (g i)
open YangMills.Construction.ReflectionPositivity.AxisMirror in
theorem LatticeApproximation.isUniformlyBounded_iff_exists_constants (D : MirrorData)
    (T : LatticeApproximation D.L) (M : ℝ) (hM : 1 ≤ M) :
    T.IsUniformlyBounded D M hM ↔ ∃ C, T.IsBoundedWithConstants D M C := by
  classical
  constructor
  · intro h
    refine ⟨fun k A => if hA : 1 ≤ k ∧ (∀ i, IsCompact (A i)) ∧
        Pairwise (Function.onFun Disjoint A) then (h k hA.1 A hA.2.1 hA.2.2).choose else 0, ?_⟩
    intro k hk A hcpt hdisj n g hg hsupp
    have hA : 1 ≤ k ∧ (∀ i, IsCompact (A i)) ∧ Pairwise (Function.onFun Disjoint A) :=
      ⟨hk, hcpt, hdisj⟩
    simp only [dif_pos hA]
    exact (h k hk A hcpt hdisj).choose_spec n g hg hsupp
  · rintro ⟨C, hC⟩ k hk A hcpt hdisj
    exact ⟨C k A, hC k hk A hcpt hdisj⟩
open YangMills.Construction.ReflectionPositivity.AxisMirror in
def LimitsOnTuplesImplyBounded : Prop :=
  (∀ (D : MirrorData) (T : LatticeApproximation D.L),
    (∀ X : SepTuple, ∃ s : ℝ,
      Tendsto (fun n => ∫ U, T.latticeProduct n X.1 U ∂T.state n) atTop (𝓝 s)) →
    T.HasC1Constants ∧ T.IsBoundedForSomeM D) ∧
  (∀ M : ℝ, 1 ≤ M → ∀ g : RealValued, IsC1c g →
    c1NormR4 g ≤ sharpNormR4 M g ∧ sharpNormR4 M g ≤ 80 * M * c1NormR4 g) ∧
  (∀ (D : MirrorData) (T : LatticeApproximation D.L),
    (∀ M : ℝ, 1 ≤ M →
      (∀ C, T.IsC1ConstantFamily C → T.IsBoundedWithConstants D M C) ∧
      (∀ C', T.IsBoundedWithConstants D M C' →
        T.IsC1ConstantFamily fun k A => (80 * M) ^ k * C' k A)) ∧
    (T.IsBoundedForSomeM D ↔ T.HasC1Constants) ∧
    (T.HasC1Constants → ∀ (M : ℝ) (hM : 1 ≤ M), T.IsUniformlyBounded D M hM))
end YangMills.Construction.ReflectionPositivity.ApproximatingSequences
