import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongTheScaleAndATop
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaleDerivatives
open BlockAverages ColdStepAtMirrorFrames DensityMeans ScaledVariables
def observableAlongList {F : BlockFrame}
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) : ℝ :=
  Ob q.1.1 q.1.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V)
theorem lt_iff_lt_card_filter_of_monotone {m : ℕ} (f : Fin m → ℕ) (hf : Monotone f) (i : ℕ) (j : Fin m) :
    f j < i ↔ (j : ℕ) < (Finset.univ.filter fun j' : Fin m => f j' < i).card := by
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter fun j' : Fin m => f j' < i := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hf (Finset.mem_Iic.mp hj')) h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hc
    have hsub : (Finset.univ.filter fun j' : Fin m => f j' < i) ⊆ Finset.Iio j := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      rw [Finset.mem_Iio]
      by_contra h2
      exact hc (lt_of_le_of_lt (hf (not_lt.mp h2)) hj')
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
variable {i k : ℕ}
abbrev orderList (J : Finset (Fin (i + k))) : Fin J.card ↪o Fin (i + k) := J.orderEmbOfFin rfl
def scaleCount (J : Finset (Fin (i + k))) : ℕ :=
  (Finset.univ.filter fun j : Fin J.card => ((orderList J j : Fin (i + k)) : ℕ) < i).card
theorem orderList_lt_iff (J : Finset (Fin (i + k))) (j : Fin J.card) :
    ((orderList J j : Fin (i + k)) : ℕ) < i ↔ (j : ℕ) < scaleCount J :=
  lt_iff_lt_card_filter_of_monotone (fun j => ((orderList J j : Fin (i + k)) : ℕ))
    (fun _ _ h => (orderList J).monotone h) i j
theorem scaleCount_le_card (J : Finset (Fin (i + k))) : scaleCount J ≤ J.card := by
  have := Finset.card_le_univ
    (Finset.univ.filter fun j : Fin J.card => ((orderList J j : Fin (i + k)) : ℕ) < i)
  simpa [scaleCount] using this
def topIndices (J : Finset (Fin (i + k))) (u : Fin (J.card - scaleCount J)) : Fin k :=
  ⟨((orderList J ⟨scaleCount J + u, by have := scaleCount_le_card J; omega⟩ : Fin (i + k)) : ℕ) - i, by
    have h1 := (orderList J ⟨scaleCount J + u, by have := scaleCount_le_card J; omega⟩ : Fin (i + k)).2
    have h2 := (orderList_lt_iff J ⟨scaleCount J + u, by have := scaleCount_le_card J; omega⟩).not.mpr
      (by simp)
    omega⟩
def derivAlongParameterListStatement : Prop :=
  (∀ (F : BlockFrame) (i k : ℕ) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
    (ζ : StepVariable (finiteCells F)) (n : ℕ),
    ContDiffAt ℝ n (observableAlongList Ob V c X) ((l, ζ), 0) → ∀ I : Finset (Fin (i + k)), I.card ≤ n →
    mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I ζ =
      scaleDeriv Ob V (c ∘ topIndices I) (X ∘ topIndices I) (scaleCount I) ζ l) ∧
  (∀ (F : BlockFrame) (i k : ℕ)
    (f : (ℝ × BondField ↥(chordBonds (finiteCells F))) × (Fin k → ℝ) → ℝ) (l : ℝ)
    (ζ : StepVariable (finiteCells F)) (n : ℕ), ContDiffAt ℝ n f ((l, ζ), 0) →
    ∀ I : Finset (Fin (i + k)), 1 + I.card ≤ n →
    ContDiffAt ℝ 1 (mixedDerivAt (shiftedAlongScale i l f) I) ζ) ∧
  (∀ (i k : ℕ) (J : Finset (Fin (i + k))), scaleCount J ≤ i ∧ J.card - scaleCount J ≤ k) ∧
  (∀ (i k : ℕ) (J : Finset (Fin (i + k))), (∀ a ∈ J, (a : ℕ) < i) → scaleCount J = J.card) ∧
  ∀ (i k : ℕ) (J : Finset (Fin (i + k))) (b : Fin k), Fin.natAdd i b ∈ J → ∃ u, topIndices J u = b
end YangMills.Construction.ScaleDerivatives
end
