import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurations
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.IterMeansOfLift
theorem link_pos_or_opposite_pos {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem bond_opposite_opposite {L m : ℕ} {j : ℤ} (b : PeriodicLattice.Bond L m j) :
    b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem fullSmoothing_of_pos {L : ℕ} {a a' : ℝ}
    (U : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : c.IsPositivelyOriented) :
    Tower.FullSpace.complexSmoothing L U c = Tower.FullSpace.complexSmoothingPositive L U c :=
  if_pos hc
theorem fullSmoothing_of_not_pos {L : ℕ} {a a' : ℝ}
    (U : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : ¬c.IsPositivelyOriented) :
    Tower.FullSpace.complexSmoothing L U c =
      (Tower.FullSpace.complexSmoothingPositive L U c.opposite)⁻¹ :=
  if_neg hc
theorem blockAverage_of_pos {L m : ℕ} {j j' : ℤ}
    (U : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {c : PeriodicLattice.Bond L m j} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage U c = PeriodicLattice.complexBlockAverageOnPositive U c :=
  if_pos hc
theorem blockAverage_of_not_pos {L m : ℕ} {j j' : ℤ}
    (U : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {c : PeriodicLattice.Bond L m j} (hc : ¬c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage U c =
      (PeriodicLattice.complexBlockAverageOnPositive U c.opposite)⁻¹ :=
  if_neg hc
section Step
variable {L n k : ℕ}
theorem projEdge_surjective (h₁ : Tower.EdgeProjectionProperties)
    (h₄ : PeriodicLiftCells.CellsAndClassesHold)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) {j : ℕ}
    (hj : j ≤ k) (b : Tower.Edge L n k j) : ∃ b', Tower.FullSpace.projEdge L n k j b' = b := by
  have hc := (h₄ L hL k n hn).1 j hj
  have lift : ∀ c : Tower.Edge L n k j, c.IsPositivelyOriented →
      ∃ b', Tower.FullSpace.projEdge L n k j b' = c := by
    intro c hpos
    obtain ⟨x, hx⟩ := (hc.1 .edge).1 (⟨c, hpos⟩ : Tower.PositiveEdge L n k j)
    have hx' : projPositiveEdge L n k j x = ⟨c, hpos⟩ := hx
    refine ⟨(show PeriodicOperators.PosEdge L k j from x).1, ?_⟩
    rw [← hc.2.2.1 x, hx']
  rcases h₉ L n k hL hn hk j hj b with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact lift b hp
  · obtain ⟨b', hb'⟩ := lift b.opposite hp
    refine ⟨b'.opposite, ?_⟩
    rw [← ((h₁ L n k j hL hn hj).1 b').2.2.2, hb']
    exact bond_opposite_opposite b
theorem lift_mem_smallComplexFields (h₇ : LiftIsGaugeField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j) :
    liftGaugeField L n k j V ∈ Tower.FullSpace.smallComplexFields L k j :=
  ⟨(h₇ L n k j hL hn hj V).2 hV.1, fun _ => hV.2 _⟩
theorem smoothingPositive_lift (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₇ : LiftIsGaugeField)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j)
    (c : Tower.FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) :
    Tower.FullSpace.complexSmoothingPositive L (liftGaugeField L n k j V) c =
      PeriodicLattice.complexBlockAverageOnPositive V (Tower.FullSpace.projEdge L n k (j + 1) c) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have hρ := (h₆.1 L hL).2.2
  have hVe := lift_mem_smallComplexFields h₇ hL hn hj.le hV
  have hcfg := h₂ L hL0 hL k hk n hn j hj c hc
  have hsets := (h₃ L hL0 hL k hk n hn).2 j hj c hc
  have hOn : Tower.FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup
      (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c)
      (liftGaugeField L n k j V) :=
    ⟨fun b _ => hVe.1.1 b, fun b _ => hVe.1.2 b⟩
  have hdom := (hρ.fullSpace k j hj c hc).subset_complexDomain
    (show liftGaugeField L n k j V ∈
        Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c from
      ⟨hOn, fun b _ => hVe.2 b⟩)
  have hcpos : (Tower.FullSpace.projEdge L n k (j + 1) c).IsPositivelyOriented :=
    ((h₁ L n k (j + 1) hL hn hj).1 c).2.2.1 hc
  have e₁ := hcfg.complexSmoothing_eq _ hdom
  have hagree : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock
      (Tower.FullSpace.projEdge L n k (j + 1) c) : Set (Tower.Edge L n k j)),
      Tower.FullSpace.projField L n k j (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c)
        (liftGaugeField L n k j V) b = V b := by
    intro b hb
    rw [← hsets.doubleCubeLinks_image] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hcfg.projField_spec _ hOn).1 b' hb'
  have e₂ := (h₈ L n k j hL.1 hL.2 hn hj _ hcpos).average_eq _ _ hagree
  rw [fullSmoothing_of_pos _ hc, blockAverage_of_pos _ hcpos] at e₁
  rw [e₁, e₂]
theorem complexSmoothing_lift (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₇ : LiftIsGaugeField)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j) :
    (Tower.FullSpace.complexSmoothing L (liftGaugeField L n k j V) :
        Tower.FullSpace.Edge L k (j + 1) → Matrices.ComplexMatrix2) =
      liftGaugeField L n k (j + 1) (PeriodicLattice.complexBlockAverage V) := by
  funext c
  show _ = PeriodicLattice.complexBlockAverage V (Tower.FullSpace.projEdge L n k (j + 1) c)
  have hq := h₁ L n k (j + 1) hL hn hj
  by_cases hc : c.IsPositivelyOriented
  · rw [fullSmoothing_of_pos _ hc, blockAverage_of_pos _ ((hq.1 c).2.2.1 hc)]
    exact smoothingPositive_lift h₁ h₂ h₃ h₆ h₇ h₈ hL hn hj hV c hc
  · have hr : c.opposite.IsPositivelyOriented := (link_pos_or_opposite_pos c).resolve_left hc
    have hrq : (Tower.FullSpace.projEdge L n k (j + 1) c).opposite.IsPositivelyOriented := by
      rw [(hq.1 c).2.2.2]
      exact (hq.1 c.opposite).2.2.1 hr
    have hnq : ¬(Tower.FullSpace.projEdge L n k (j + 1) c).IsPositivelyOriented := by
      rcases h₉ L n k hL hn (by omega) (j + 1) hj (Tower.FullSpace.projEdge L n k (j + 1) c) with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hrq h
      · exact h
    rw [fullSmoothing_of_not_pos _ hc, blockAverage_of_not_pos _ hnq, (hq.1 c).2.2.2]
    rw [smoothingPositive_lift h₁ h₂ h₃ h₆ h₇ h₈ hL hn hj hV _ hr]
theorem blockAverage_mem_fieldsIn (h₅ : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j) :
    (PeriodicLattice.complexBlockAverage V : Tower.Edge L n k (j + 1) → Matrices.ComplexMatrix2) ∈
      Tower.fieldsIn L n k (j + 1) PeriodicLattice.complexGaugeGroup := by
  have hρ := (h₆.1 L hL).2.2
  have hk : 0 < k := by omega
  have hpos : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c hc
    have hdom := (hρ.periodic n k j hn hj c hc).subset_complexDomain
      (show V ∈ Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c from
        ⟨⟨fun b _ => hV.1.1 b (mem_univ b), fun b _ => hV.1.2 b (mem_univ b)⟩, fun b _ => hV.2 b⟩)
    exact ((h₅.2 L k (j + 1) hL (by omega) hj).1 n hn c V hc hdom).2
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
    rw [blockAverage_of_not_pos _ hc, blockAverage_of_pos _ hr]
  have hall : ∀ c : Tower.Edge L n k (j + 1),
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c
    rcases h₉ L n k hL hn hk (j + 1) hj c with ⟨hc, -⟩ | ⟨hr, hc⟩
    · exact hpos c hc
    · rw [hneg c hr hc]
      exact hinv _ (hpos _ hr)
  refine ⟨fun c _ => hall c, fun c _ => ?_⟩
  rcases h₉ L n k hL hn hk (j + 1) hj c with ⟨hc, hr⟩ | ⟨hr, hc⟩
  · have hrr : ¬c.opposite.IsPositivelyOriented := hr
    have := hneg c.opposite (by rw [bond_opposite_opposite]; exact hc) hrr
    rw [bond_opposite_opposite] at this
    exact this
  · rw [hneg c hr hc]
    have hdet : (PeriodicLattice.complexBlockAverage V c.opposite : Matrices.ComplexMatrix2).det = 1 :=
      hpos _ hr
    rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)]
end Step
theorem claim_holds (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₄ : PeriodicLiftCells.CellsAndClassesHold)
    (h₅ : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₇ : LiftIsGaugeField)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy) : Claim := by
  intro L hL k n hn hk U hU
  have key : ∀ i : ℕ, i ≤ k →
      ((∀ j < i, PeriodicLattice.complexBlockFieldAtLevel j U ∈ Tower.smallComplexFields L n k j) ↔
        ∀ j < i, Tower.FullSpace.complexIter L k j (liftGaugeField L n k 0 U) ∈
          Tower.FullSpace.smallComplexFields L k j) ∧
      ((∀ j < i, PeriodicLattice.complexBlockFieldAtLevel j U ∈ Tower.smallComplexFields L n k j) →
        Tower.FullSpace.complexIter L k i (liftGaugeField L n k 0 U) =
            liftGaugeField L n k i (PeriodicLattice.complexBlockFieldAtLevel i U) ∧
          PeriodicLattice.complexBlockFieldAtLevel i U ∈
            Tower.fieldsIn L n k i PeriodicLattice.complexGaugeGroup) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨⟨fun _ j hj => absurd hj (Nat.not_lt_zero j),
        fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩, fun _ => ⟨rfl, hU⟩⟩
    | succ i ih =>
      intro hi
      have hik : i < k := hi
      obtain ⟨ihe, ihs⟩ := ih hik.le
      refine ⟨⟨fun h j hj => ?_, fun h j hj => ?_⟩, fun h => ?_⟩
      · have h' : ∀ j < i, PeriodicLattice.complexBlockFieldAtLevel j U ∈
            Tower.smallComplexFields L n k j := fun j hj => h j (by omega)
        by_cases hji : j < i
        · exact ihe.mp h' j hji
        · have hje : j = i := by omega
          subst hje
          rw [(ihs h').1]
          exact lift_mem_smallComplexFields h₇ hL hn hik.le (h j (Nat.lt_succ_self j))
      · have h' := ihe.mpr fun j hj => h j (by omega)
        by_cases hji : j < i
        · exact h' j hji
        · have hje : j = i := by omega
          subst hje
          obtain ⟨e, hc⟩ := ihs h'
          have hs := h j (Nat.lt_succ_self j)
          rw [e] at hs
          refine ⟨hc, fun b => ?_⟩
          obtain ⟨b', rfl⟩ := projEdge_surjective h₁ h₄ h₉ hL hn (by omega) hik.le b
          exact hs.2 b'
      · have h' : ∀ j < i, PeriodicLattice.complexBlockFieldAtLevel j U ∈
            Tower.smallComplexFields L n k j := fun j hj => h j (by omega)
        obtain ⟨e, -⟩ := ihs h'
        have hs := h i (Nat.lt_succ_self i)
        refine ⟨?_, blockAverage_mem_fieldsIn h₅ h₆ h₉ hL hn hik hs⟩
        show Tower.FullSpace.complexSmoothing L
            (Tower.FullSpace.complexIter L k i (liftGaugeField L n k 0 U)) = _
        rw [e]
        exact complexSmoothing_lift h₁ h₂ h₃ h₆ h₇ h₈ h₉ hL hn hik hs
  have hE := (h₇ L n k 0 hL hn (Nat.zero_le k) U).2 hU
  refine ⟨⟨fun h => ⟨hE, (key k le_rfl).1.mp h.2⟩, fun h => ⟨hU, (key k le_rfl).1.mpr h.2⟩⟩,
    fun h j hj => ?_⟩
  exact ((key j hj).2 fun i hi => h.2 i (by omega)).1
end YangMills.Construction.LocalKernels.IterMeansOfLift
end
