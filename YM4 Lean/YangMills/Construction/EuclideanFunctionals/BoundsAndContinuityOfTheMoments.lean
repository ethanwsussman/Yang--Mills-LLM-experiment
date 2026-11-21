import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.Moments
def momentAt (S : ConnFamily) {n : ℕ} (h : Fin n → R4 → ℂ) : ℂ :=
  centeredFnFree S (complexTuple h)
def partitionConst (C : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ) : ℝ :=
  ∑ π ∈ YangMills.Construction.SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, C J.card d R
def SeparatedInBalls {n : ℕ} (A : Fin n → Set R4) (R d : ℝ) : Prop :=
  (∀ l, ∃ x, A l ⊆ YangMills.Construction.TestFunctions.closedBallR4 x R) ∧
    Pairwise fun k l => ENNReal.ofReal d ≤ YangMills.Construction.TestFunctions.setDistR4 (A k) (A l)
def EntriesSupportedIn {n : ℕ} (A : Fin n → Set R4) (h : Fin n → R4 → ℂ) : Prop :=
  ∀ l, h l ∈ C1c ℂ ∧ supp (h l) ⊆ A l
def MomentBoundHolds (c : SharpScale) (S : ConnFamily) (C : ℕ → ℝ → ℝ → ℝ) (d R : ℝ) {n : ℕ}
    (h : Fin n → R4 → ℂ) : Prop :=
  ‖momentAt S h‖ ≤ 2 ^ n * partitionConst C n d R * ∏ l, c.sharpNorm (h l)
def MomentLipschitzBound (c : SharpScale) (S : ConnFamily) (C : ℕ → ℝ → ℝ → ℝ) (d R : ℝ) {n : ℕ}
    (h h' : Fin n → R4 → ℂ) : Prop :=
  ‖momentAt S h - momentAt S h'‖ ≤
    2 ^ n * partitionConst C n d R *
      ∑ l, c.sharpNorm (h l - h' l) *
        ∏ k ∈ Finset.univ.erase l, max (c.sharpNorm (h k)) (c.sharpNorm (h' k))
def MomentContinuous (S : ConnFamily) {n : ℕ} (A : Fin n → Set R4) (h : Fin n → R4 → ℂ) : Prop :=
  ∀ g : ℕ → Fin n → R4 → ℂ, (∀ j, 1 ≤ j → EntriesSupportedIn A (g j)) →
    (∀ l, TendstoC1 (fun j => g j l) (h l)) →
      Tendsto (fun j => momentAt S (g j)) atTop (𝓝 (momentAt S h))
def PartitionConstLocal (n : ℕ) (d R : ℝ) : Prop :=
  ∀ C C' : ℕ → ℝ → ℝ → ℝ, (∀ k, 2 ≤ k → k ≤ n → C k d R = C' k d R) →
    partitionConst C n d R = partitionConst C' n d R
def MomentBoundsTheorem : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S) (n : ℕ), 2 ≤ n →
    ∀ (R d : ℝ), 0 < R → 0 < d → ∀ A : Fin n → Set R4, SeparatedInBalls A R d →
      ∀ h h' : Fin n → R4 → ℂ, EntriesSupportedIn A h → EntriesSupportedIn A h' →
        MomentBoundHolds c S σ.clusterConst d R h ∧
          MomentLipschitzBound c S σ.clusterConst d R h h' ∧
            MomentContinuous S A h ∧ PartitionConstLocal n d R
end YangMills.Construction.EuclideanFunctionals.Moments
