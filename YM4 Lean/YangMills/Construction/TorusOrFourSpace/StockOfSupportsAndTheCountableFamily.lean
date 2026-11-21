import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Kind
variable (P : Params) (Y : Kind)
structure IsFunctionSpaceNorm (N : (Y.Pt P → ℝ) → ℝ≥0∞)
    (V : Set (Y.Pt P → ℝ)) : Prop where
  zero_mem : 0 ∈ V
  lincomb_mem : ∀ f ∈ V, ∀ g ∈ V, ∀ s t : ℝ, s • f + t • g ∈ V
  finite : ∀ f ∈ V, N f < ⊤
  definite : ∀ f ∈ V, N f = 0 → f = 0
  homog : ∀ f ∈ V, ∀ s : ℝ, N (s • f) = ENNReal.ofReal |s| * N f
  triangle : ∀ f ∈ V, ∀ g ∈ V, N (f + g) ≤ N f + N g
def IsCompleteWrt (N : (Y.Pt P → ℝ) → ℝ≥0∞) (V : Set (Y.Pt P → ℝ)) : Prop :=
  ∀ u : ℕ → Y.Pt P → ℝ, (∀ j, u j ∈ V) →
    (∀ ε : ℝ, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, N (u i - u j) < ENNReal.ofReal ε) →
    ∃ f ∈ V, ∀ ε : ℝ, 0 < ε → ∃ J, ∀ j ≥ J, N (u j - f) < ENNReal.ofReal ε
def IsSeparableBanachWrt (N : (Y.Pt P → ℝ) → ℝ≥0∞) (V : Set (Y.Pt P → ℝ)) : Prop :=
  IsFunctionSpaceNorm P Y N V ∧ IsCompleteWrt P Y N V ∧
    ∃ A, A ⊆ V ∧ A.Countable ∧ IsDenseWrt P Y N V A
def minPairwiseDist {n : ℕ} (Q : Fin n → Set (Y.Pt P)) : ℝ≥0∞ :=
  ⨅ i, ⨅ k, ⨅ _ : i ≠ k, setInfDist P Y (Q i) (Q k)
end Kind
open Kind
def SupportStockAndCountableFamily : Prop :=
  ∀ P : Params,
    (∀ b : RationalBox, b.diam < P.side / 2 →
      (∀ x ∈ b.toSet, ∀ x' ∈ b.toSet,
        quotDist P torus (quotMap P torus x) (quotMap P torus x') =
          TorusMetric.euclidNormVec (x - x')) ∧
      Set.InjOn (quotMap P torus) b.toSet) ∧
    ∀ Y : Kind,
      ((supportStock P Y).Countable ∧ ∀ Q ∈ supportStock P Y, IsCompactQ P Y Q) ∧
      (∀ Q ∈ supportStock P Y,
        c1VanishingOutside P Y Q = c1SupportedIn P Y Q ∧
        (∀ f ∈ c1VanishingOutside P Y Q, ∀ y, y ∉ Q → gradVec P Y f y = 0) ∧
        IsSeparableBanachWrt P Y (euclidC1Norm P Y) (c1VanishingOutside P Y Q) ∧
        ∀ A, A ⊆ c1VanishingOutside P Y Q →
          IsDenseWrt P Y (euclidC1Norm P Y) (c1VanishingOutside P Y Q) A →
          IsDenseWrt P Y (sharpNormQ P Y) (c1VanishingOutside P Y Q) A) ∧
      (∀ S W : Set (Y.Pt P), IsCompactQ P Y S → IsOpenQ P Y W → S ⊆ W →
        ∃ Q ∈ supportStock P Y, S ⊆ Q ∧ Q ⊆ W) ∧
      ∀ F : supportStock P Y → Set (Y.Pt P → ℝ), IsDenseFamily P Y F →
        (tupleFamily P Y F).Countable ∧
        ∀ (n : ℕ) (φ : Fin n → Y.Pt P → ℝ) (Q : Fin n → supportStock P Y),
          (⟨n, φ⟩ : Σ n : ℕ, Fin n → Y.Pt P → ℝ) ∈ tupleFamily P Y F →
          IsBuiltFrom P Y F φ Q →
          φ ∈ sepC1Tuples P Y n ∧
          (∀ i, supportQ P Y (φ i) ⊆ (Q i : Set (Y.Pt P))) ∧
          (2 ≤ n →
            minPairwiseDist P Y (fun i => (Q i : Set (Y.Pt P))) ≤ supportGap P Y φ ∧
            0 < minPairwiseDist P Y (fun i => (Q i : Set (Y.Pt P))))
end YangMills.Construction.PeriodicSpace
