import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Lattice.ToolboxMeanLinearAverageIsTheAbsorbedAverage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K n : ℕ}
namespace CentredAverage
theorem bondFormSumAlong_congr {j : ℤ} {A B : Bond L m j → ComplexMatrix2} {γ : List (Bond L m j)}
    (h : ∀ b ∈ γ, A b = B b) : bondFormSumAlong A γ = bondFormSumAlong B γ := by
  simp only [bondFormSumAlong, List.map_congr_left h]
theorem contourFormAverage_congr {j j' : ℤ} {A B : Bond L m j' → ComplexMatrix2}
    {y : Site L m j} {x : Site L m j'} (h : ∀ γ ∈ contourSet y x, ∀ b ∈ γ, A b = B b) :
    contourFormAverage A y x = contourFormAverage B y x := by
  unfold contourFormAverage
  congr 1
  exact Finset.sum_congr rfl fun τ _ => bondFormSumAlong_congr (h _ ⟨τ, rfl⟩)
theorem eval_opposite_of_isPositivelyOriented {P : SymmetricBondSet L m K n} (a : LieBondField P)
    {b : BondAtLevel L m K n} (hb : b.IsPositivelyOriented)
    (hop : ¬ b.opposite.IsPositivelyOriented) :
    a.eval b.opposite = -a.eval b := by
  by_cases hP : b ∈ P.bonds
  · rw [a.eval_opposite ⟨b, hP, hb⟩ hop, a.eval_of_positive ⟨b, hP, hb⟩]
  · have hz₁ : a.eval b = 0 := by
      have hn : ¬ (b ∈ P.bonds ∧ b.IsPositivelyOriented) := fun h => hP h.1
      have hn' : ¬ (b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented) := fun h => hop h.2
      simp only [LieBondField.eval]
      rw [dif_neg hn, dif_neg hn']
    have hz₂ : a.eval b.opposite = 0 := by
      have hn : ¬ (b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented) := fun h => hop h.2
      have hn' : ¬ (b.opposite.opposite ∈ P.bonds ∧ b.opposite.opposite.IsPositivelyOriented) :=
        fun h => hP h.1
      simp only [LieBondField.eval]
      rw [dif_neg hn, dif_neg hn']
    rw [hz₁, hz₂, neg_zero]
theorem isBondForm_eval {P : SymmetricBondSet L m K n} (a : LieBondField P)
    (hop : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    IsBondForm complexLieAlgebra fun b : BondAtLevel L m K n => (a.eval b : ComplexMatrix2) := by
  refine ⟨fun b _ => (a.eval b).2, fun b => ?_⟩
  have hneg : a.eval b.opposite = -a.eval b := by
    by_cases hb : b.IsPositivelyOriented
    · exact eval_opposite_of_isPositivelyOriented a hb (hop b hb)
    · have h := eval_opposite_of_isPositivelyOriented a
        (Bond.opposite_isPositivelyOriented hb) hb
      have hinv : b.opposite.opposite = b := rfl
      rw [hinv] at h
      rw [h, neg_neg]
  simp only [hneg]
  rfl
end CentredAverage
open CentredAverage in
theorem centredLinearAverageEqScaled_holds (hPaths : BlockPaths.Statement) :
    CentredLinearAverageEqScaled := by
  intro L hL m K n hm hn c hc a
  obtain ⟨hodd, h13⟩ := hL
  have hop : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented := fun b hb =>
    Bond.opposite_not_isPositivelyOriented (by omega) (by simp only [levelDepth]; omega) hb
  refine ⟨⟨fun b => (a.eval b : ComplexMatrix2), isBondForm_eval a hop, fun b => ?_⟩,
    fun A hA hAa => ?_⟩
  · exact congrArg Subtype.val (a.eval_of_positive b)
  have hagree : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      lieFieldMatrices a b = A b := by
    intro b hb
    by_cases hpos : b.IsPositivelyOriented
    · have h := hAa ⟨b, hb, hpos⟩
      change (a.eval b : ComplexMatrix2) = A b
      rw [h, a.eval_of_positive ⟨b, hb, hpos⟩]
    · have hopp := Bond.opposite_isPositivelyOriented hpos
      have hmem : b.opposite ∈ (doubleBlockSymmetricSet c).bonds :=
        (doubleBlockSymmetricSet c).opposite_mem b hb
      have e₁ := a.eval_opposite ⟨b.opposite, hmem, hopp⟩ hpos
      have e₂ := hA.2 b.opposite
      have e₃ := hAa ⟨b.opposite, hmem, hopp⟩
      have hinv : b.opposite.opposite = b := rfl
      simp only [hinv] at e₁ e₂
      change (a.eval b : ComplexMatrix2) = A b
      rw [e₁, e₂, e₃]
      rfl
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨-, hcμ⟩ := hPaths L m K hodd h13 hm n hn
  obtain ⟨hD, -, -, -, hP⟩ := hcμ c μ hμ
  obtain ⟨-, -, -, hImg, hShift, -⟩ := hD
  have htarget : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hShift x hx, ← hImg]
    exact ⟨x, hx, rfl⟩
  have hterm : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      contourFormMean .centred (lieFieldMatrices a) c.source x +
          bondFormSumAlong (lieFieldMatrices a) (crossingPath c x) -
          contourFormMean .centred (lieFieldMatrices a) c.target (shiftAcross c x) =
        contourFormAverage A c.source x + bondFormSumAlong A (crossingPath c x) -
          contourFormAverage A c.target (shiftAcross c x) := by
    intro x hx
    have e₁ : contourFormAverage (lieFieldMatrices a) c.source x =
        contourFormAverage A c.source x :=
      contourFormAverage_congr fun γ hγ b hb =>
        hagree b ((hP.1 c.source (Or.inl rfl) x hx).1 γ hγ b hb)
    have e₂ : bondFormSumAlong (lieFieldMatrices a) (crossingPath c x) =
        bondFormSumAlong A (crossingPath c x) :=
      bondFormSumAlong_congr fun b hb => hagree b (hP.2 x hx b hb)
    have e₃ : contourFormAverage (lieFieldMatrices a) c.target (shiftAcross c x) =
        contourFormAverage A c.target (shiftAcross c x) :=
      contourFormAverage_congr fun γ hγ b hb =>
        hagree b ((hP.1 c.target (Or.inr rfl) (shiftAcross c x) (htarget x hx)).1 γ hγ b hb)
    change contourFormAverage _ c.source x + _ - contourFormAverage _ c.target (shiftAcross c x) = _
    rw [e₁, e₂, e₃]
  change inverseFourthPowerWeight L • (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source, _) =
    inverseFourthPowerWeight L • linearBlockSum A c
  unfold linearBlockSum
  rw [finsum_mem_congr rfl hterm]
end YangMills.Construction.PeriodicLattice
