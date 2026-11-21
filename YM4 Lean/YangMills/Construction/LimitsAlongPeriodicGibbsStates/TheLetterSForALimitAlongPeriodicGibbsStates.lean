import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open AmbientPoints R4TupleForms
namespace PeriodicGibbsLimit
variable {s : Conventions.StandingParameters}
def HasMultilinearConnected (σ : FinTuple s → ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → IsTupleMultilinear (connectedOf σ n)
noncomputable def connectedFamily (σ : FinTuple s → ℝ) (hσ : HasMultilinearConnected σ) :
    ConnectedFamily s .euclidean :=
  ⟨fun n _ => connectedOf σ n, hσ⟩
noncomputable def centredOfLimit (σ : FinTuple s → ℝ)
    (hσ : HasMultilinearConnected σ) : FinTuple s → ℝ :=
  (connectedFamily σ hσ).centred
theorem centredOfLimit_apply (σ : FinTuple s → ℝ) (hσ : HasMultilinearConnected σ)
    (X : FinTuple s) :
    centredOfLimit σ hσ X =
      ∑ π ∈ SetPartition.singletonFree X.1.1, ∏ J ∈ π.parts,
        connectedOf σ J.card (restrictSeparated ⟨X.1.2, X.2⟩ J) := by
  unfold centredOfLimit ConnectedFamily.centred
  refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
  exact dif_pos (two_le_card_of_mem_singletonFree hπ hJ)
end PeriodicGibbsLimit
end YangMills.Construction
