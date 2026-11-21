import YangMills.Construction.Continuum.OrthogonalBlockEmbedding
import YangMills.Construction.Continuum.SettingOfRotationsOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.Orthogonal YangMills.Construction.TestFunctions
open YangMills.Construction.SeparatedTuples YangMills.Construction.Rotations
namespace YangMills.Construction.Rotations.OrthogonalSetting
def HasSeparatedBounds (M : ℝ) (σ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ d R : ℝ, 0 < d → 0 < R →
    0 ≤ B k d R ∧ SeparatedBound M σ k d R (B k d R)
def rotateEntriesOn (Q : orthogonalGroupFour) (I : Finset ℕ) (X : List RealValued) :
    List RealValued :=
  (X.zipIdx 1).map fun p => if p.2 ∈ I then orthogonalAct Q p.1 else p.1
def RotatedEntriesTelescoping : Prop :=
  ∀ (M : ℝ) (σ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ), 1 ≤ M → σ.IsEntrywiseLinear →
    HasSeparatedBounds M σ B →
    ∀ (k : ℕ) (d r : ℝ) (h : SepTuple), 1 ≤ k → 0 < d → 0 < r → h.size = k →
      (∀ f ∈ h.1, tsupport f ⊆ closedBallR4 0 r) →
      h.1.Pairwise (fun f g => ENNReal.ofReal d ≤ setDistR4 (tsupport f) (tsupport g)) →
      ∀ (Q : orthogonalGroupFour) (I : Finset ℕ), matrixOperatorNorm (Q.1 - 1) * r ≤ d / 4 →
        I ⊆ Finset.Icc 1 k →
        ∃ hI : IsDisjointlySupported (rotateEntriesOn Q I h.1),
          |σ ⟨rotateEntriesOn Q I h.1, hI⟩ - σ h| ≤
            B k (d / 2) (r + d) *
              ∑ l ∈ I, sharpNormR4 M (orthogonalAct Q (h.componentAt (l - 1)) - h.componentAt (l - 1)) *
                ∏ l' ∈ (Finset.Icc 1 k).erase l, sharpNormR4 M (h.componentAt (l' - 1))
end YangMills.Construction.Rotations.OrthogonalSetting
end
