import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.IteratesOfSmallConfigurationsAreInTheComplexGroup
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.SmallIterates
theorem bond_opposite_opposite {L m : ℕ} {j : ℤ} (b : PeriodicLattice.Bond L m j) :
    b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem complexBlockAverage_of_pos {L m : ℕ} {j j' : ℤ}
    (U : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {c : PeriodicLattice.Bond L m j} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage U c = PeriodicLattice.complexBlockAverageOnPositive U c :=
  if_pos hc
theorem complexBlockAverage_of_not_pos {L m : ℕ} {j j' : ℤ}
    (U : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {c : PeriodicLattice.Bond L m j} (hc : ¬c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage U c =
      (PeriodicLattice.complexBlockAverageOnPositive U c.opposite)⁻¹ :=
  if_neg hc
theorem complexBlockAverage_mem_fieldsIn (h₁ : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (h₂ : Tower.SmoothingNearIdentity)
    (h₃ : PeriodicLattice.LevelBondOrientationDichotomy)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2} (hV : V ∈ Tower.smallComplexFields L n k j) :
    (PeriodicLattice.complexBlockAverage V : Tower.Edge L n k (j + 1) → Matrices.ComplexMatrix2) ∈
      Tower.fieldsIn L n k (j + 1) PeriodicLattice.complexGaugeGroup := by
  have hρ := (h₂.1 L hL).2.2
  have hk : 0 < k := by omega
  have hpos : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c hc
    have hdom := (hρ.periodic n k j hn hj c hc).subset_complexDomain
      (show V ∈ Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c from
        ⟨⟨fun b _ => hV.1.1 b (mem_univ b), fun b _ => hV.1.2 b (mem_univ b)⟩, fun b _ => hV.2 b⟩)
    exact ((h₁.2 L k (j + 1) hL (by omega) hj).1 n hn c V hc hdom).2
  have hinv : ∀ X : Matrices.ComplexMatrix2, X ∈ PeriodicLattice.complexGaugeGroup →
      X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by
    intro X hX
    have hX' : X.det = 1 := hX
    show (X⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, hX']
    simp
  have hneg : ∀ c : Tower.Edge L n k (j + 1), c.opposite.IsPositivelyOriented →
      ¬c.IsPositivelyOriented →
      (PeriodicLattice.complexBlockAverage V : Tower.Edge L n k (j + 1) → Matrices.ComplexMatrix2) c =
        (PeriodicLattice.complexBlockAverage V c.opposite)⁻¹ := by
    intro c hr hc
    rw [complexBlockAverage_of_not_pos _ hc, complexBlockAverage_of_pos _ hr]
  have hall : ∀ c : Tower.Edge L n k (j + 1),
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c
    rcases h₃ L n k hL hn hk (j + 1) hj c with ⟨hc, -⟩ | ⟨hr, hc⟩
    · exact hpos c hc
    · rw [hneg c hr hc]
      exact hinv _ (hpos _ hr)
  refine ⟨fun c _ => hall c, fun c _ => ?_⟩
  rcases h₃ L n k hL hn hk (j + 1) hj c with ⟨hc, hr⟩ | ⟨hr, hc⟩
  · have hrr : ¬c.opposite.IsPositivelyOriented := hr
    have := hneg c.opposite (by rw [bond_opposite_opposite]; exact hc) hrr
    rw [bond_opposite_opposite] at this
    exact this
  · rw [hneg c hr hc]
    have hdet : (PeriodicLattice.complexBlockAverage V c.opposite : Matrices.ComplexMatrix2).det = 1 :=
      hpos _ hr
    rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)]
theorem smallIterates_holds (h₁ : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (h₂ : Tower.SmoothingNearIdentity)
    (h₃ : PeriodicLattice.LevelBondOrientationDichotomy) : SmallIteratesInComplexGaugeGroup := by
  intro L hL k n hn hk U hU j hj
  rcases Nat.lt_or_ge j k with hlt | hge
  · exact (hU.2 j hlt).1
  · have hjk : j = k := le_antisymm hj hge
    subst hjk
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact complexBlockAverage_mem_fieldsIn h₁ h₂ h₃ hL hn (Nat.lt_succ_self i)
      (hU.2 i (Nat.lt_succ_self i))
end YangMills.Construction.LocalKernels.SmallIterates
end
