import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.ComplexAveragesFromBondsAreTheComplexIterates
import YangMills.Construction.Lattice.ContinuationOfTheMinimiserUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfComplexAverages
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import YangMills.Construction.Lattice.ObjectsOfSequencesUnderIsometries
import YangMills.Construction.Lattice.TowerConfigurationsOfTheContinuationUnderIsometries
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ContinuedTowerFieldIsometry
variable {L m K : ℕ}
section EvaluationMaps
variable {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
theorem regularConstrainedCriticalSet_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V =
      regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V' := by
  have hc : linkConstraintSet (Averaging.smoothingRadius L) Ω (activeBondSet K k Ω) V =
      linkConstraintSet (Averaging.smoothingRadius L) Ω (activeBondSet K k Ω) V' := by
    ext U
    simp only [linkConstraintSet, mem_ofPred_eq]
    refine and_congr_right fun _ => forall₂_congr fun q hq => ?_
    rw [h q hq]
  ext U
  simp only [regularConstrainedCriticalSet, IsConstrainedCritical, mem_ofPred_eq, hc]
theorem hasActiveCriticalOrbit_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    HasActiveCriticalOrbit ε K k Ω V = HasActiveCriticalOrbit ε K k Ω V' := by
  simp only [HasActiveCriticalOrbit, HasUniqueCriticalOrbit, regularConstrainedCriticalSet_congr ε h]
theorem isActiveGaugeRepresentative_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    IsActiveGaugeRepresentative ε K k Ω V = IsActiveGaugeRepresentative ε K k Ω V' := by
  funext U
  simp only [IsActiveGaugeRepresentative, regularConstrainedCriticalSet_congr ε h]
theorem hasActiveGaugeRepresentative_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    HasActiveGaugeRepresentative ε K k Ω V = HasActiveGaugeRepresentative ε K k Ω V' := by
  simp only [HasActiveGaugeRepresentative, hasActiveCriticalOrbit_congr ε h,
    isActiveGaugeRepresentative_congr ε h]
theorem activeGaugeRepresentative_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    activeGaugeRepresentative ε K k Ω V = activeGaugeRepresentative ε K k Ω V' := by
  simp only [activeGaugeRepresentative, isActiveGaugeRepresentative_congr ε h]
theorem mem_activeRegularRealFields_of_eqOn {εBar : ℝ} (h : ∀ j ≤ k, V j = V' j)
    (hV : V ∈ activeRegularRealFields εBar K k Ω) :
    V' ∈ activeRegularRealFields εBar K k Ω := by
  obtain ⟨h₁, h₂, h₃⟩ := hV
  refine ⟨fun j hj => ?_, fun p a b => ?_, fun q hq p a b => ?_⟩
  · rw [← h j hj]
    exact h₁ j hj
  · rw [← h 0 (Nat.zero_le k)]
    exact h₂ p a b
  · have hmix : levelMixedField (Averaging.smoothingRadius L) K q (activeBondsAt K k Ω) V' =
        levelMixedField (Averaging.smoothingRadius L) K q (activeBondsAt K k Ω) V := by
      funext c
      simp only [levelMixedField, h (q + 1) hq, h q hq.le]
    rw [hmix]
    exact h₃ q hq p a b
theorem mem_activeRegularRealFields_congr (εBar : ℝ) (h : ∀ j ≤ k, V j = V' j) :
    V ∈ activeRegularRealFields εBar K k Ω ↔
      V' ∈ activeRegularRealFields εBar K k Ω :=
  ⟨mem_activeRegularRealFields_of_eqOn h,
    mem_activeRegularRealFields_of_eqOn fun j hj => (h j hj).symm⟩
theorem fst_le_of_mem_activeBondSet {q : Σ j : ℕ, BondAtLevel L m K j}
    (hq : q ∈ activeBondSet K k Ω) : q.1 ≤ k :=
  hq.1.1
theorem expTwistedDatum_congr (h : ∀ j ≤ k, V j = V' j) (B : ActiveFamily L m K k Ω) :
    ∀ q ∈ activeBondSet K k Ω, expTwistedDatum B V q.1 q.2 =
      expTwistedDatum B V' q.1 q.2 := by
  intro q hq
  simp only [expTwistedDatum, h q.1 (fst_le_of_mem_activeBondSet hq)]
theorem isMinimizerContinuation_congr (ε εBar rB : ℝ) (h : ∀ j ≤ k, V j = V' j) :
    IsMinimizerContinuation ε εBar rB K k Ω V =
      IsMinimizerContinuation ε εBar rB K k Ω V' := by
  have hset : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2 := fun q hq => by
    rw [h q.1 (fst_le_of_mem_activeBondSet hq)]
  have hB : IsBallDatum ε εBar K k Ω V = IsBallDatum ε εBar K k Ω V' := by
    simp only [IsBallDatum, hasActiveCriticalOrbit_congr ε hset,
      mem_activeRegularRealFields_congr εBar h]
  have hr : ∀ B : ActiveFamily L m K k Ω, HasActiveGaugeRepresentative ε K k Ω
      (expTwistedDatum B V) = HasActiveGaugeRepresentative ε K k Ω
        (expTwistedDatum B V') := fun B =>
    hasActiveGaugeRepresentative_congr ε (expTwistedDatum_congr h B)
  have hs : ∀ B : ActiveFamily L m K k Ω, activeGaugeRepresentative ε K k Ω
      (expTwistedDatum B V) = activeGaugeRepresentative ε K k Ω
        (expTwistedDatum B V') := fun B =>
    activeGaugeRepresentative_congr ε (expTwistedDatum_congr h B)
  funext Φ
  simp only [IsMinimizerContinuation, hB, hr, hs]
theorem hasUniqueMinimizerContinuation_congr (ε εBar rB : ℝ) (h : ∀ j ≤ k, V j = V' j) :
    HasUniqueMinimizerContinuation ε εBar rB K k Ω V =
      HasUniqueMinimizerContinuation ε εBar rB K k Ω V' := by
  simp only [HasUniqueMinimizerContinuation, isMinimizerContinuation_congr ε εBar rB h]
theorem continuedMinimalField_congr (ε εBar rB : ℝ) (h : ∀ j ≤ k, V j = V' j) :
    continuedMinimalField ε εBar rB K k Ω V =
      continuedMinimalField ε εBar rB K k Ω V' := by
  funext B
  simp only [continuedMinimalField, minimizerContinuation,
    isMinimizerContinuation_congr ε εBar rB h]
theorem inv_inv_of_mem_compactGaugeGroup {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g⁻¹⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem regular_and_hasRepresentative_of_hasUnique {ε εBar rB : ℝ}
    (h : HasUniqueMinimizerContinuation ε εBar rB K k Ω V) :
    V ∈ activeRegularRealFields εBar K k Ω ∧ HasActiveGaugeRepresentative ε K k Ω V := by
  classical
  obtain ⟨Φ, ⟨hball, -, -, N, ⟨-, D, -, h0, hDN⟩, hN⟩, -⟩ := h
  refine ⟨hball.1, ?_⟩
  have hz : ∀ q ∈ activeBondSet K k Ω,
      expTwistedDatum (0 : ActiveFamily L m K k Ω) V q.1 q.2 = V q.1 q.2 := by
    rintro ⟨j, b⟩ hq
    have hconf := hball.1.1 j (fst_le_of_mem_activeBondSet hq)
    have hb : b ∈ activeBondsAt K k Ω j := ⟨hq.1.2, hq.2⟩
    have hfam : ∀ c : BondAtLevel L m K j, familyAtLevel
        (0 : ActiveFamily L m K k Ω) j c = 0 := by
      intro c
      simp only [familyAtLevel]
      split_ifs <;> rfl
    simp only [expTwistedDatum, expTwist, hfam, smul_zero, ComplexMatrix2.matExp,
      NormedSpace.exp_zero, one_mul]
    split_ifs with hp
    · rfl
    · rw [hconf.2 b hb]
      exact inv_inv_of_mem_compactGaugeGroup (hconf.1 b hb)
  rw [← hasActiveGaugeRepresentative_congr ε hz]
  exact (hN 0 (hDN h0)).1
end EvaluationMaps
structure TransportsFrom (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop where
  endpoints : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target
  endpoints_symm : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
      ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target
  chains : PreservesChainObjects i σ
  blockFields : ∀ K : ℕ, BlockFieldEquivariant K i σ
  complexAverages : PreservesComplexBlockAverages σ i
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem bondPreimage_bondImage (h : TransportsFrom σ i) (hj : i ≤ j) (c : Bond L m j) :
    bondPreimage σ (bondImage σ c) = c := by
  have e := h.endpoints j hj c
  have p := h.endpoints_symm j hj (bondImage σ c)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem bondImage_bondPreimage (h : TransportsFrom σ i) (hj : i ≤ j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b := by
  have e := h.endpoints j hj (bondPreimage σ b)
  have p := h.endpoints_symm j hj b
  apply Bond.ext <;> apply Subtype.ext
  · rw [e.1, p.1]; simp
  · rw [e.2, p.2]; simp
theorem transportGaugeField_bondImage (h : TransportsFrom σ i) (hj : i ≤ j)
    (U : Bond L m j → ComplexMatrix2) (c : Bond L m j) :
    transportGaugeField σ U (bondImage σ c) = U c :=
  congrArg U (bondPreimage_bondImage h hj c)
theorem bondPreimage_opposite (h : TransportsFrom σ i) (hj : i ≤ j) (b : Bond L m j) :
    bondPreimage σ b.opposite = (bondPreimage σ b).opposite := by
  have p := h.endpoints_symm j hj b
  have q := h.endpoints_symm j hj b.opposite
  apply Bond.ext <;> apply Subtype.ext
  · exact q.1.trans p.2.symm
  · exact q.2.trans p.1.symm
theorem mem_equiv_image_iff (X : Set (FourTorus L m)) (t : FourTorus L m) :
    t ∈ σ '' X ↔ σ.symm t ∈ X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.mem_image_equiv_iff <;> assumption
theorem mem_bondsInside_image (h : TransportsFrom σ i) (hj : i ≤ j) (X : Set (FourTorus L m))
    (b : Bond L m j) :
    b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      bondPreimage σ b ∈ (bondsInside X : Set (Bond L m j)) := by
  have p := h.endpoints_symm j hj b
  show ((b.source : FourTorus L m) ∈ σ '' X ∧ (b.target : FourTorus L m) ∈ σ '' X) ↔
    (((bondPreimage σ b).source : FourTorus L m) ∈ X ∧
      ((bondPreimage σ b).target : FourTorus L m) ∈ X)
  rw [p.1, p.2, mem_equiv_image_iff, mem_equiv_image_iff]
theorem bondsInside_image (h : TransportsFrom σ i) (hj : i ≤ j) (X : Set (FourTorus L m)) :
    (bondsInside (σ '' X) : Set (Bond L m j)) = bondImage σ '' bondsInside X := by
  ext b
  rw [mem_bondsInside_image h hj]
  constructor
  · exact fun hb => ⟨_, hb, bondImage_bondPreimage h hj b⟩
  · rintro ⟨c, hc, rfl⟩
    rwa [bondPreimage_bondImage h hj]
theorem extendByOne_transport (h : TransportsFrom σ i) (hj : i ≤ j) (X : Set (FourTorus L m))
    (U : Bond L m j → ComplexMatrix2) :
    extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U) =
      transportGaugeField σ (extendByOne (bondsInside X) U) := by
  funext b
  have hiff := mem_bondsInside_image h hj X b
  simp only [extendByOne, transportGaugeField]
  by_cases hb : b ∈ (bondsInside (σ '' X) : Set (Bond L m j))
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (mt hiff.2 hb)]
theorem bondsInside_isReversalClosed (X : Set (FourTorus L m)) :
    IsReversalClosed (bondsInside X : Set (Bond L m j)) :=
  fun _ hb => ⟨hb.2, hb.1⟩
theorem isGaugeField_transport (h : TransportsFrom σ i) (hj : i ≤ j) {G : Set ComplexMatrix2}
    {X : Set (FourTorus L m)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField G (bondsInside X) U) :
    IsGaugeField G (bondsInside (σ '' X)) (transportGaugeField σ U) := by
  refine ⟨fun b hb => hU.1 _ ((mem_bondsInside_image h hj X b).1 hb), fun b hb => ?_⟩
  show U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
  rw [bondPreimage_opposite h hj]
  exact hU.2 _ ((mem_bondsInside_image h hj X b).1 hb)
theorem isGaugeField_extendByOne {G : Set ComplexMatrix2} {S : Set (Bond L m j)}
    (hS : IsReversalClosed S) {U : Bond L m j → ComplexMatrix2} (hU : IsGaugeField G S U) :
    IsGaugeField G S (extendByOne S U) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · simpa [extendByOne, hb] using hU.1 b hb
  · simpa [extendByOne, hb, hS b hb] using hU.2 b hb
end Bonds
section Averages
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ}
theorem levelDepth_antitone {j n : ℕ} (hj : j ≤ n) : levelDepth K n ≤ levelDepth K j := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.levelDepth_anti <;> assumption
theorem averagingOnDeterminingSet_image (h : TransportsFrom σ i) {j : ℕ} (hjK : j ≤ K)
    (hij : i ≤ levelDepth K j) (X : Set (FourTorus L m)) {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) :
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
        (transportGaugeField σ U) j : BondAtLevel L m K j → ComplexMatrix2) =
      transportGaugeField σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j) := by
  have hi0 : i ≤ levelDepth K 0 := hij.trans (levelDepth_antitone (Nat.zero_le j))
  show blockFieldAtLevel _ j (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U)) = _
  rw [extendByOne_transport h hi0]
  exact h.blockFields K j hjK hij _
    (extendByOne_mem_compactGaugeFields (bondsInside_isReversalClosed X) hU)
theorem complexBlockDatum_image (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hjK : j ≤ K)
    (hij : i ≤ levelDepth K j) {X : Set (FourTorus L m)} {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W) (c : BondAtLevel L m K j) :
    (ComplexAverageIsDefined K (bondsInside X) (extendByOne (bondsInside X) W) j c →
      ComplexAverageIsDefined K (bondsInside (σ '' X))
        (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ W)) j
        (bondImage σ c) →
      complexBlockDatum K (σ '' X) (transportGaugeField σ W) j (bondImage σ c) =
        complexBlockDatum K X W j c) ∧
    (IsTorusTranslation σ →
      (ComplexAverageIsDefined K (bondsInside (σ '' X))
        (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ W)) j
        (bondImage σ c) ↔
      ComplexAverageIsDefined K (bondsInside X) (extendByOne (bondsInside X) W) j c)) := by
  have hi0 : i ≤ levelDepth K 0 := hij.trans (levelDepth_antitone (Nat.zero_le j))
  have hC : extendByOne (bondsInside X) W ∈
      complexGaugeFields (bondsInside X : Set (BondAtLevel L m K 0)) :=
    isGaugeField_extendByOne (bondsInside_isReversalClosed X) hW
  have hid := ((h.complexAverages K).2 j hjK hij (bondsInside X)
    (bondsInside_isReversalClosed X)) c
  have hB := bondsInside_image h hi0 X (j := levelDepth K 0)
  have br := hbridge L m K hL hm (bondsInside X) (extendByOne (bondsInside X) W) j hjK c
  have br' := hbridge L m K hL hm (bondsInside (σ '' X))
    (transportGaugeField σ (extendByOne (bondsInside X) W)) j hjK (bondImage σ c)
  simp only [complexBlockDatum, extendByOne_transport h hi0 X W]
  rw [hB] at br' ⊢
  constructor
  · intro hd hd'
    have f := br.1.1 hd
    have f' := br'.1.1 hd'
    rw [br.2 f, br'.2 f']
    have e := hid.2.2.1 (extendByOne (bondsInside X) W) ⟨⟨hC, f'⟩, ⟨hC, f⟩⟩
    exact e.trans (transportGaugeField_bondImage h hij _ c)
  · intro ht
    have e := hid.2.2.2 ht
    rw [br'.1, br.1]
    have := Set.ext_iff.1 e (extendByOne (bondsInside X) W)
    exact ⟨fun f' => (this.1 ⟨hC, f'⟩).2, fun f => (this.2 ⟨hC, f⟩).2⟩
end Averages
section Family
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ}
def blockRatio (K : ℕ) (X : Set (FourTorus L m)) (W U : BondAtLevel L m K 0 → ComplexMatrix2)
    (j : ℕ) (b : BondAtLevel L m K j) : ComplexMatrix2 :=
  complexBlockDatum K X W j b *
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j b)⁻¹
theorem blockRatio_image (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hjK : j ≤ K)
    (hij : i ≤ levelDepth K j) {X : Set (FourTorus L m)}
    {W U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W)
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) (c : BondAtLevel L m K j)
    (hd : ComplexAverageIsDefined K (bondsInside X) (extendByOne (bondsInside X) W) j c)
    (hd' : ComplexAverageIsDefined K (bondsInside (σ '' X))
      (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ W)) j (bondImage σ c)) :
    blockRatio K (σ '' X) (transportGaugeField σ W) (transportGaugeField σ U) j
        (bondImage σ c) = blockRatio K X W U j c := by
  simp only [blockRatio]
  rw [(complexBlockDatum_image h hbridge hL hm hjK hij hW c).1 hd hd',
    averagingOnDeterminingSet_image h hjK hij X hU, transportGaugeField_bondImage h hij]
theorem complexBlockDatum_opposite {X : Set (FourTorus L m)}
    {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W) {j : ℕ} {b : BondAtLevel L m K j}
    (hb : ¬b.IsPositivelyOriented) (hb' : b.opposite.IsPositivelyOriented)
    (hd : ComplexAverageIsDefined K (bondsInside X) (extendByOne (bondsInside X) W) j
      b.opposite) :
    complexBlockDatum K X W j b = (complexBlockDatum K X W j b.opposite)⁻¹ := by
  have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
  cases j with
  | zero =>
    have hC := isGaugeField_extendByOne (bondsInside_isReversalClosed X) hW
    have := hC.2 b.opposite hd
    rw [hrr] at this
    exact this
  | succ j =>
    show complexBlockAverage _ b = (complexBlockAverage _ b.opposite)⁻¹
    rw [complexBlockAverage, complexBlockAverage, if_neg hb, if_pos hb']
theorem logSeries_reversed_ratio (hlog : ComplexMatrix2.LogSeriesConjugateInverse)
    {A B : ComplexMatrix2} (hB : B ∈ compactGaugeGroup)
    (h₁ : ComplexMatrix2.operatorNorm (A * B⁻¹ - 1) < 1)
    (h₂ : ComplexMatrix2.operatorNorm (A⁻¹ * B⁻¹⁻¹ - 1) < 1) :
    ComplexMatrix2.logSeries (A⁻¹ * B⁻¹⁻¹) =
      -(B⁻¹ * ComplexMatrix2.logSeries (A * B⁻¹) * B⁻¹⁻¹) := by
  have hBu : IsUnit B.det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.1 hB).2]
    exact isUnit_one
  have hTu : IsUnit (B⁻¹).det := Matrix.isUnit_nonsing_inv_det B hBu
  have hX : IsUnit (A * B⁻¹) := by
    have := isUnit_one_sub_of_norm_lt_one (x := 1 - A * B⁻¹) (by
      rw [norm_sub_rev]
      exact h₁)
    simpa using this
  have hT : IsUnit B⁻¹ := (Matrix.isUnit_iff_isUnit_det _).2 hTu
  have hmat : A⁻¹ * B⁻¹⁻¹ = B⁻¹ * (A * B⁻¹)⁻¹ * B⁻¹⁻¹ := by
    rw [Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hTu, one_mul]
  rw [hmat] at h₂ ⊢
  exact hlog _ _ hX hT h₁ h₂
theorem opposite_mem_determiningBondsAt {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} {j : ℕ}
    {b : BondAtLevel L m K j} (hb : b ∈ determiningBondsAt K k Ω j) :
    b.opposite ∈ determiningBondsAt K k Ω j :=
  ⟨hb.1.symm, hb.2.2, hb.2.1⟩
theorem opposite_mem_activeBondSet {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} {j : ℕ}
    {b : BondAtLevel L m K j}
    (hq : (⟨j, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω) :
    (⟨j, b.opposite⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω := by
  have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
  refine ⟨⟨hq.1.1, opposite_mem_determiningBondsAt hq.1.2⟩,
    fun hin => hq.2 ⟨hin.1, ?_, hin.2.2.symm⟩⟩
  have := opposite_mem_determiningBondsAt hin.2.1
  rwa [hrr] at this
theorem levelDepth_bounds {n : ℕ} (hnK : n ≤ K) {j : ℕ} (hj : j ≤ n) :
    -(m : ℤ) ≤ levelDepth K j ∧ (0 : ℤ) ≤ levelDepth K j := by
  simp only [levelDepth]
  omega
theorem activeBondSet_imageChain (h : TransportsFrom σ i) {n : ℕ}
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) (Ω' : ℕ → Set (FourTorus L m)) :
    activeBondSet K n (imageChain σ Ω') = bondSetImage σ (activeBondSet K n Ω') :=
  (h.chains K n Ω' (imageChain σ Ω') hdep fun _ _ => rfl).2.2.2.2.2.2.2.1
theorem logRatioFamily_image (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hlog : ComplexMatrix2.LogSeriesConjugateInverse)
    (horient : BondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hnK : n ≤ K)
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) {Ω' : ℕ → Set (FourTorus L m)}
    {X : Set (FourTorus L m)} {W U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W)
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U)
    (hreal : ∀ j ≤ n, IsGaugeField compactGaugeGroup (activeBondsAt K n Ω' j)
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j))
    (hd : HasComplexBlockDatum K n Ω' X W)
    (hd' : HasComplexBlockDatum K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W))
    (hb : ∀ q ∈ activeBondSet K n Ω',
      ComplexMatrix2.operatorNorm (blockRatio K X W U q.1 q.2 - 1) < 1)
    (hb' : ∀ q ∈ activeBondSet K n (imageChain σ Ω'),
      ComplexMatrix2.operatorNorm (blockRatio K (σ '' X) (transportGaugeField σ W)
        (transportGaugeField σ U) q.1 q.2 - 1) < 1) :
    logRatioFamily K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W)
        (transportGaugeField σ U) =
      twistedActiveFamily σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
        (logRatioFamily K n Ω' X W U) := by
  classical
  funext p
  obtain ⟨⟨j', b'⟩, hp, hpos⟩ := p
  have hp₀ := hp
  rw [activeBondSet_imageChain h hdep] at hp₀
  obtain ⟨⟨j, b⟩, hq, he⟩ := hp₀
  cases he
  have hjn : j ≤ n := fst_le_of_mem_activeBondSet hq
  have hij := hdep j hjn
  have hjK := hjn.trans hnK
  have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
  have hrat := blockRatio_image h hbridge hL hm hjK hij hW hU b (hd _ hq) (hd' _ hp)
  show (Complex.I)⁻¹ • ComplexMatrix2.logSeries (blockRatio K (σ '' X) (transportGaugeField σ W)
      (transportGaugeField σ U) j (bondImage σ b)) =
    twistedFormValue σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j)
      (familyAtLevel (logRatioFamily K n Ω' X W U) j) (bondImage σ b)
  simp only [twistedFormValue, bondPreimage_bondImage h hij]
  by_cases hbp : b.IsPositivelyOriented
  · rw [if_pos hbp, familyAtLevel, dif_pos ⟨hq, hbp⟩, hrat]
    rfl
  · have hdepth : -(m : ℤ) < levelDepth K j := by
      have := (levelDepth_bounds (m := m) hnK hjn).2
      omega
    have hbr : b.opposite.IsPositivelyOriented := by
      rcases horient L m hL hm _ hdepth b with h₁ | h₁
      · exact absurd h₁.1 hbp
      · exact h₁.1
    have hq' := opposite_mem_activeBondSet hq
    have hconf := hreal j hjn
    have hmem : b ∈ activeBondsAt K n Ω' j := ⟨hq.1.2, hq.2⟩
    have hmem' : b.opposite ∈ activeBondsAt K n Ω' j := ⟨hq'.1.2, hq'.2⟩
    have hUb : averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j b =
        (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j b.opposite)⁻¹ := by
      have := hconf.2 b.opposite hmem'
      rwa [hrr] at this
    have hWb := complexBlockDatum_opposite hW hbp hbr (hd _ hq')
    have hratb : blockRatio K X W U j b =
        (complexBlockDatum K X W j b.opposite)⁻¹ *
          (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j b.opposite)⁻¹⁻¹ := by
      simp only [blockRatio]
      rw [hWb, hUb]
    have hr₂ := hb' _ hp
    simp only [hrat] at hr₂
    rw [hratb] at hr₂
    have hb₁ := hb _ hq'
    simp only [blockRatio] at hb₁
    have hl := logSeries_reversed_ratio hlog (hconf.1 _ hmem') hb₁ hr₂
    rw [if_neg hbp, familyAtLevel, dif_pos ⟨hq', hbr⟩, hrat, hratb, hl]
    show _ = -ComplexMatrix2.conjugateBy _
      ((Complex.I)⁻¹ • ComplexMatrix2.logSeries (blockRatio K X W U j b.opposite))
    simp only [ComplexMatrix2.conjugateBy, blockRatio, mul_smul_comm, smul_mul_assoc, smul_neg]
end Family
section Translation
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem isTorusTranslation_symm (hσ : IsTorusTranslation σ) : IsTorusTranslation σ.symm := by
  obtain ⟨v, hv⟩ := hσ
  refine ⟨-v, fun x => ?_⟩
  have h1 : ∀ y : Fin 4 → ℝ, (1 : SignedFrame).actOnVector y = y := by
    intro y
    funext μ
    simp [SignedFrame.actOnVector]
  rw [Equiv.symm_apply_eq, hv]
  simp [h1]
structure PreservesOrientation (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop where
  image : ∀ b : Bond L m j, b.IsPositivelyOriented → (bondImage σ b).IsPositivelyOriented
  preimage : ∀ b : Bond L m j, b.IsPositivelyOriented → (bondPreimage σ b).IsPositivelyOriented
theorem not_positive_bondPreimage (h : TransportsFrom σ i) (hj : i ≤ j)
    (hk : PreservesOrientation σ j) {b : Bond L m j} (hb : ¬b.IsPositivelyOriented) :
    ¬(bondPreimage σ b).IsPositivelyOriented := fun hp => hb (by
  have := hk.image _ hp
  rwa [bondImage_bondPreimage h hj] at this)
theorem not_positive_bondImage (h : TransportsFrom σ i) (hj : i ≤ j)
    (hk : PreservesOrientation σ j) {b : Bond L m j} (hb : ¬b.IsPositivelyOriented) :
    ¬(bondImage σ b).IsPositivelyOriented := fun hp => hb (by
  have := hk.preimage _ hp
  rwa [bondPreimage_bondImage h hj] at this)
theorem expTwist_transport (h : TransportsFrom σ i) (hj : i ≤ j) (hk : PreservesOrientation σ j)
    (A U : Bond L m j → ComplexMatrix2) :
    expTwist (transportForm σ A) (transportGaugeField σ U) =
      transportGaugeField σ (expTwist A U) := by
  classical
  funext b
  simp only [transportGaugeField, transportForm, expTwist]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, if_pos (hk.preimage b hb)]
  · rw [if_neg hb, if_neg (not_positive_bondPreimage h hj hk hb), bondPreimage_opposite h hj]
theorem isPolarDecomposition_image (h : TransportsFrom σ i) (hi0 : i ≤ levelDepth K 0)
    (hk : PreservesOrientation σ (levelDepth K 0)) {ξ : ℝ} {X : Set (FourTorus L m)}
    {W U : BondAtLevel L m K 0 → ComplexMatrix2} (H : IsPolarDecomposition ξ K X W U) :
    IsPolarDecomposition ξ K (σ '' X) (transportGaugeField σ W) (transportGaugeField σ U) := by
  obtain ⟨hU, hW, A, hA, hE⟩ := H
  refine ⟨⟨isGaugeField_transport h hi0 hU.1, fun b hb =>
      hU.2 _ (mt (mem_bondsInside_image h hi0 X b).2 hb)⟩, isGaugeField_transport h hi0 hW,
    transportForm σ A, ⟨fun b hb => hA.1 _ (hk.preimage b hb), fun b => ?_⟩, ?_⟩
  · show A (bondPreimage σ b.opposite) = -A (bondPreimage σ b)
    rw [bondPreimage_opposite h hi0]
    exact hA.2 _
  · have e : ((ξ : ℂ) • transportForm σ A) = transportForm σ ((ξ : ℂ) • A) := rfl
    rw [e, expTwist_transport h hi0 hk, extendByOne_transport h hi0, ← hE]
theorem transport_symm_transport (h : TransportsFrom σ i) (hj : i ≤ j)
    (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U :=
  funext fun b => congrArg U (bondPreimage_bondImage h hj b)
theorem isPolarDecomposition_image_iff (h : TransportsFrom σ i) (h' : TransportsFrom σ.symm i)
    (hi0 : i ≤ levelDepth K 0) (hk : PreservesOrientation σ (levelDepth K 0)) {ξ : ℝ}
    {X : Set (FourTorus L m)} {W U : BondAtLevel L m K 0 → ComplexMatrix2} :
    IsPolarDecomposition ξ K X W U ↔
      IsPolarDecomposition ξ K (σ '' X) (transportGaugeField σ W) (transportGaugeField σ U) := by
  refine ⟨isPolarDecomposition_image h hi0 hk, fun H => ?_⟩
  have hk' : PreservesOrientation σ.symm (levelDepth K 0) := ⟨hk.preimage, hk.image⟩
  have := isPolarDecomposition_image h' hi0 hk' H
  rwa [transport_symm_transport h hi0, transport_symm_transport h hi0,
    Equiv.symm_image_image] at this
theorem bondImage_mem_activeBondSet (h : TransportsFrom σ i) {n : ℕ}
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) {Ω' : ℕ → Set (FourTorus L m)} {a : ℕ}
    {b : BondAtLevel L m K a}
    (hq : (⟨a, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K n Ω') :
    (⟨a, bondImage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈
      activeBondSet K n (imageChain σ Ω') := by
  rw [activeBondSet_imageChain h hdep]
  exact ⟨⟨a, b⟩, hq, rfl⟩
theorem hasComplexBlockDatum_image_iff (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hnK : n ≤ K)
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) (ht : IsTorusTranslation σ)
    {Ω' : ℕ → Set (FourTorus L m)} {X : Set (FourTorus L m)}
    {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W) :
    HasComplexBlockDatum K n Ω' X W ↔
      HasComplexBlockDatum K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W) := by
  constructor
  · intro hd q' hq'
    rw [activeBondSet_imageChain h hdep] at hq'
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hq'
    exact ((complexBlockDatum_image h hbridge hL hm
      ((fst_le_of_mem_activeBondSet hq).trans hnK) (hdep a (fst_le_of_mem_activeBondSet hq))
      hW b).2 ht).2 (hd _ hq)
  · rintro hd' ⟨a, b⟩ hq
    exact ((complexBlockDatum_image h hbridge hL hm
      ((fst_le_of_mem_activeBondSet hq).trans hnK) (hdep a (fst_le_of_mem_activeBondSet hq))
      hW b).2 ht).1 (hd' _ (bondImage_mem_activeBondSet h hdep hq))
theorem blockRatio_bounds_image_iff (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hnK : n ≤ K)
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) {Ω' : ℕ → Set (FourTorus L m)}
    {X : Set (FourTorus L m)} {W U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W)
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U)
    (hd : HasComplexBlockDatum K n Ω' X W)
    (hd' : HasComplexBlockDatum K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W)) :
    (∀ q ∈ activeBondSet K n Ω',
        ComplexMatrix2.operatorNorm (blockRatio K X W U q.1 q.2 - 1) < 1) ↔
      ∀ q ∈ activeBondSet K n (imageChain σ Ω'),
        ComplexMatrix2.operatorNorm (blockRatio K (σ '' X) (transportGaugeField σ W)
          (transportGaugeField σ U) q.1 q.2 - 1) < 1 := by
  constructor
  · intro hb q' hq'
    have hq₀ := hq'
    rw [activeBondSet_imageChain h hdep] at hq₀
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hq₀
    show ComplexMatrix2.operatorNorm (blockRatio K (σ '' X) (transportGaugeField σ W)
      (transportGaugeField σ U) a (bondImage σ b) - 1) < 1
    rw [blockRatio_image h hbridge hL hm ((fst_le_of_mem_activeBondSet hq).trans hnK)
      (hdep a (fst_le_of_mem_activeBondSet hq)) hW hU b (hd _ hq) (hd' _ hq')]
    exact hb _ hq
  · rintro hb' ⟨a, b⟩ hq
    have hq' := bondImage_mem_activeBondSet (σ := σ) h hdep hq
    have := hb' _ hq'
    simp only [blockRatio_image h hbridge hL hm ((fst_le_of_mem_activeBondSet hq).trans hnK)
      (hdep a (fst_le_of_mem_activeBondSet hq)) hW hU b (hd _ hq) (hd' _ hq')] at this
    exact this
theorem supBall_comp_surjective {α β : Type} {f : α → β} (hf : Function.Surjective f)
    (A : β → ComplexMatrix2) (r : ℝ) :
    A ∘ f ∈ GroupLieProduct.supBall α r ↔ A ∈ GroupLieProduct.supBall β r := by
  have hn : GroupLieProduct.supNorm (A ∘ f) = GroupLieProduct.supNorm A :=
    hf.iSup_comp fun b => ComplexMatrix2.operatorNorm (A b)
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b => ?_, hn ▸ h₂⟩
    obtain ⟨a, rfl⟩ := hf b
    exact h₁ a
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun a => h₁ (f a), hn.symm ▸ h₂⟩
theorem logRatioFamily_mem_ball_image_iff (h : TransportsFrom σ i)
    (hbridge : ComplexAverageEqComplexIterate)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hnK : n ≤ K)
    (hdep : ∀ q ≤ n, i ≤ levelDepth K q) (hk : ∀ a ≤ n, PreservesOrientation σ (levelDepth K a))
    {Ω' : ℕ → Set (FourTorus L m)} {X : Set (FourTorus L m)}
    {W U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W)
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U)
    (hd : HasComplexBlockDatum K n Ω' X W)
    (hd' : HasComplexBlockDatum K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W))
    (rB : ℝ) :
    logRatioFamily K n Ω' X W U ∈ complexFamilyBall (activeBondSet K n Ω') rB ↔
      logRatioFamily K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W)
          (transportGaugeField σ U) ∈
        complexFamilyBall (activeBondSet K n (imageChain σ Ω')) rB := by
  let f : PositiveBondIn (activeBondSet K n Ω') →
      PositiveBondIn (activeBondSet K n (imageChain σ Ω')) := fun p =>
    ⟨⟨p.1.1, bondImage σ p.1.2⟩, bondImage_mem_activeBondSet h hdep p.2.1,
      (hk _ (fst_le_of_mem_activeBondSet p.2.1)).image _ p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨⟨a', b'⟩, hp, hpos⟩
    have hp₀ := hp
    rw [activeBondSet_imageChain h hdep] at hp₀
    obtain ⟨⟨a, b⟩, hq, he⟩ := hp₀
    cases he
    refine ⟨⟨⟨a, b⟩, hq, ?_⟩, rfl⟩
    by_contra hb
    exact not_positive_bondImage h (hdep a (fst_le_of_mem_activeBondSet hq))
      (hk a (fst_le_of_mem_activeBondSet hq)) hb hpos
  have hcomp : logRatioFamily K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W)
      (transportGaugeField σ U) ∘ f = logRatioFamily K n Ω' X W U := by
    funext p
    obtain ⟨⟨a, b⟩, hq, hb⟩ := p
    show (Complex.I)⁻¹ • ComplexMatrix2.logSeries (blockRatio K (σ '' X)
        (transportGaugeField σ W) (transportGaugeField σ U) a (bondImage σ b)) =
      (Complex.I)⁻¹ • ComplexMatrix2.logSeries (blockRatio K X W U a b)
    rw [blockRatio_image h hbridge hL hm ((fst_le_of_mem_activeBondSet hq).trans hnK)
      (hdep a (fst_le_of_mem_activeBondSet hq)) hW hU b (hd _ hq)
      (hd' _ (bondImage_mem_activeBondSet h hdep hq))]
  rw [← hcomp]
  exact supBall_comp_surjective hf _ rB
end Translation
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.symm_mem_latticeIsometries <;> assumption
theorem transportsFrom_of_mem (hG : LatticeIsometryGroupActionStatement)
    (hO : IsometryPreservesChainObjects) (hA : AveragingMapsEquivariant)
    (hC : ComplexAveragesCommuteWithIsometries.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) :
    TransportsFrom σ i where
  endpoints := fun j hj => ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.1
  endpoints_symm := fun j hj =>
    ((hG L m i hs hm hi).2.2.2.2 σ.symm (symm_mem_latticeIsometries hG hs hm hi hσ) j hj).1.2.2.2.1
  chains := hO L m i σ hs hm hi hσ
  blockFields := fun K => (hA L m hs hm i hi σ hσ K).2.1
  complexAverages := hC L m i σ hs hm hi hσ
end ContinuedTowerFieldIsometry
open ContinuedTowerFieldIsometry in
theorem continuedTowerField_isometry
    (hCont : IsometriesPreserveMinimizerContinuation)
    (hA : AveragingMapsEquivariant)
    (hC : ComplexAveragesCommuteWithIsometries.Statement)
    (hbridge : ComplexAverageEqComplexIterate)
    (hO : IsometryPreservesChainObjects)
    (hG : LatticeIsometryGroupActionStatement)
    (horient : BondOrientationDichotomy)
    (hlog : Matrices.ComplexMatrix2.LogSeriesConjugateInverse)
    (hT : TwistedTransportIsometryInvariance) :
    continuedTowerField_isometry_statement := by
  intro L m hL hm i hi σ hσ ε εBar rB ξ hε hεB hrB hξ K n e r Ω' X hseq hsep hX hsupp W U
  have hs := symm_mem_latticeIsometries hG hL hm hi hσ
  have h := transportsFrom_of_mem hG hO hA hC hL hm hi hσ
  have h' := transportsFrom_of_mem hG hO hA hC hL hm hi hs
  have hnK : n ≤ K := hseq.2.2.1
  have hin : i ≤ levelDepth K n := hseq.index_le_levelDepth
  have hdep : ∀ q ≤ n, i ≤ levelDepth K q := fun q hq => hin.trans (levelDepth_antitone hq)
  have hi0 := hdep 0 (Nat.zero_le n)
  have hV : IsGaugeField compactGaugeGroup (bondsInside X) U → ∀ j ≤ n,
      averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
          (transportGaugeField σ U) j =
        datumImage σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U) j :=
    fun hU j hj => averagingOnDeterminingSet_image h (hj.trans hnK) (hdep j hj) X hU
  have hchild := hCont L m hL hm i hi σ hσ ε εBar rB hε hεB hrB K n e r Ω' hseq hsep
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
  refine ⟨?_, fun ht => ?_⟩
  · intro H H'
    obtain ⟨⟨hdec, hd, hreg, hrep, hb, hball⟩, hone⟩ := H
    obtain ⟨⟨-, hd', -, -, hb', -⟩, hone'⟩ := H'
    have hU := hdec.1.1
    have hW := hdec.2.1
    have hone'' : HasUniqueMinimizerContinuation ε εBar rB K n (imageChain σ Ω')
        (datumImage σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)) := by
      rw [← hasUniqueMinimizerContinuation_congr ε εBar rB (hV hU)]
      exact hone'
    have fam := logRatioFamily_image h hbridge hlog horient hL hm hnK hdep hW hU hreg.1 hd hd'
      hb hb'
    have child := hchild.1 hone hone''
    show InComplexStabilizerOrbit _ _
      (continuedMinimalField ε εBar rB K n (imageChain σ Ω')
        (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
          (transportGaugeField σ U))
        (logRatioFamily K n (imageChain σ Ω') (σ '' X) (transportGaugeField σ W)
          (transportGaugeField σ U)))
      (transportGaugeField σ (continuedMinimalField ε εBar rB K n Ω'
        (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
        (logRatioFamily K n Ω' X W U)))
    rw [continuedMinimalField_congr ε εBar rB (hV hU), fam]
    exact (child.2 _ hball).2.1
  · have hiff := hchild.2 ht
    have hk : ∀ a ≤ n, PreservesOrientation σ (levelDepth K a) := by
      intro a ha
      have hlt : -(m : ℤ) < levelDepth K a := by
        have := (levelDepth_bounds (m := m) hnK ha).2
        omega
      exact ⟨fun b hb => (hT L m i σ hL hm hi hσ).1 (Or.inl ht) _ hlt (hdep a ha) b hb,
        fun b hb => (hT L m i σ.symm hL hm hi hs).1 (Or.inl (isTorusTranslation_symm ht)) _ hlt
          (hdep a ha) b hb⟩
    have hk0 := hk 0 (Nat.zero_le n)
    constructor
    · rintro ⟨⟨hdec, hd, -, -, hb, hball⟩, hone⟩
      have hU := hdec.1.1
      have hW := hdec.2.1
      have hone' : HasUniqueMinimizerContinuation ε εBar rB K n (imageChain σ Ω')
          (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
            (transportGaugeField σ U)) := by
        rw [hasUniqueMinimizerContinuation_congr ε εBar rB (hV hU)]
        exact hiff.1 hone
      have hd' := (hasComplexBlockDatum_image_iff h hbridge hL hm hnK hdep ht hW).1 hd
      obtain ⟨hr₁, hr₂⟩ := regular_and_hasRepresentative_of_hasUnique hone'
      exact ⟨⟨isPolarDecomposition_image h hi0 hk0 hdec, hd', hr₁, hr₂,
        (blockRatio_bounds_image_iff h hbridge hL hm hnK hdep hW hU hd hd').1 hb,
        (logRatioFamily_mem_ball_image_iff h hbridge hL hm hnK hdep hk hW hU hd hd' rB).1 hball⟩,
        hone'⟩
    · rintro ⟨⟨hdec', hd', -, -, hb', hball'⟩, hone'⟩
      have hdec := (isPolarDecomposition_image_iff h h' hi0 hk0).2 hdec'
      have hU := hdec.1.1
      have hW := hdec.2.1
      have hone : HasUniqueMinimizerContinuation ε εBar rB K n Ω'
          (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U) := by
        refine hiff.2 ?_
        rw [← hasUniqueMinimizerContinuation_congr ε εBar rB (hV hU)]
        exact hone'
      have hd := (hasComplexBlockDatum_image_iff h hbridge hL hm hnK hdep ht hW).2 hd'
      obtain ⟨hr₁, hr₂⟩ := regular_and_hasRepresentative_of_hasUnique hone
      exact ⟨⟨hdec, hd, hr₁, hr₂,
        (blockRatio_bounds_image_iff h hbridge hL hm hnK hdep hW hU hd hd').2 hb',
        (logRatioFamily_mem_ball_image_iff h hbridge hL hm hnK hdep hk hW hU hd hd' rB).2 hball'⟩,
        hone⟩
end YangMills.Construction.PeriodicLattice
