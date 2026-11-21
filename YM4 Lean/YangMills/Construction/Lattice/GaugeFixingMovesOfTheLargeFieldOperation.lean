import YangMills.Construction.Lattice.HowATermIsRead
import YangMills.Construction.Lattice.ListOfTheOperationsOfALevel
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.LargeFieldGaugeMoves
open BorelKernels TermEvaluation ConfigSpaces CubesOfStep CentralBlock
inductive Clause where
  | a | b | c | d | e | f | g
structure OperationMoveIndex where
  major : ℕ
  minor : Option Clause
def moveOfDecomposition : Lattice.LargeFieldDecomposition → OperationMoveIndex
  | .regularityOfTheFirstBackground => ⟨2, some .a⟩
  | .regularityOfTheNextBackground _ => ⟨2, some .a⟩
  | .approximateFluctuationTest _ => ⟨2, some .c⟩
  | .completionOfTheFluctuationTests _ => ⟨2, some .d⟩
  | .smallFieldTestOfTheFluctuationField _ => ⟨2, some .f⟩
  | .extendibilityOfTheExteriorField => ⟨3, none⟩
  | .smallFieldTestOfTheMainStep => ⟨4, some .c⟩
  | .testAtTheLastShell => ⟨4, some .d⟩
  | .testOfTheDenominator => ⟨5, none⟩
def moveOfSlot : OperationList.Slot → OperationMoveIndex
  | .split e => moveOfDecomposition e
  | .stageGaugeFixing _ => ⟨2, some .b⟩
  | .stageIndicatorRemoval _ => ⟨2, some .e⟩
  | .collarShift _ => ⟨2, some .f⟩
  | .stageIntegration _ => ⟨2, some .g⟩
  | .boxIntegration => ⟨4, some .a⟩
  | .frameSum => ⟨4, some .c⟩
  | .nestGaugeFixing => ⟨4, some .c⟩
  | .mixedGaugeChange => ⟨4, some .c⟩
  | .regularityRemoval => ⟨4, some .e⟩
  | .referenceLaw => ⟨5, none⟩
  | .referenceLawLiteral => ⟨5, none⟩
  | .localization => ⟨6, none⟩
  | .classSplit => ⟨7, none⟩
  | .boxTestRemoval => ⟨7, none⟩
  | .boxTreeRemoval => ⟨7, none⟩
  | .exponentiation => ⟨8, none⟩
universe u w
section EvaluationMaps
variable {L m K k : ℕ} {Stored : Type}
inductive StateEvaluation (v : BondField L m K k Stored) (𝔅 : Finset (GradedBond L m K))
    (𝒴 : Type u) [MeasurableSpace 𝒴] (𝒲 : Type w) [MeasurableSpace 𝒲] (Lebesgue : Type) where
  | literal {Named : Type} {O : Named → Type u} [hO : ∀ n, MeasurableSpace (O n)]
      (holds : 𝒴 ≃ᵐ FixedValues v 𝔅 Lebesgue × ∀ n, O n) (object : ∀ n, FixedValues v 𝔅 Lebesgue → O n)
      (e : 𝒲 ≃ᵐ AuxiliaryValues Stored Lebesgue)
  | framed {C Named : Type} {O : Named → Type u} [hO : ∀ n, MeasurableSpace (O n)]
      (holds : 𝒴 ≃ᵐ FramedFixedValues C v 𝔅 Lebesgue × ∀ n, O n)
      (object : ∀ n, FramedFixedValues C v 𝔅 Lebesgue → O n)
      (e : 𝒲 ≃ᵐ TermEvaluation.FrameChoice C × AuxiliaryValues Stored Lebesgue)
namespace StateEvaluation
variable {v : BondField L m K k Stored} {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u}
  [MeasurableSpace 𝒴] {𝒲 : Type w} [MeasurableSpace 𝒲] {Lebesgue : Type}
def toConfig : StateEvaluation v 𝔅 𝒴 𝒲 Lebesgue → LevelStateSpace L m K k 𝒲 →
    ConfigSpaces.ConfigSpace 𝔅 𝒴
  | .literal (Named := _) (O := _) (hO := _) holds object e, q =>
      configPoint v 𝔅 holds object (q.1, e q.2)
  | .framed (C := _) (Named := _) (O := _) (hO := _) holds object e, q =>
      framedConfigPoint v 𝔅 holds object ((e q.2).1, (q.1, (e q.2).2))
def pushforward (ρ : StateEvaluation v 𝔅 𝒴 𝒲 Lebesgue) (ν : ComplexStateMeasure L m K k 𝒲) :
    ComplexMeasure (ConfigSpaces.ConfigSpace 𝔅 𝒴) :=
  ν.map ρ.toConfig
end StateEvaluation
end EvaluationMaps
section Moves
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m)))
def stageSites (n : ℕ) : Set (SiteAtLevel c.L m K (stageLevel c x k n + 1)) :=
  newGaugeSites c x S Q n (⋃₀ Q)
def boxEntranceBond (X : Set (FourTorus c.L m)) (r : SignedFrame) : BondAtLevel c.L m K k :=
  rotatedBoxEntranceBond r (levelDepth K k) (S.componentBoxSites c.r x Q X)
def boxEntrancePoint (X : Set (FourTorus c.L m)) (r : SignedFrame) : FourTorus c.L m :=
  Classical.epsilon fun y : FourTorus c.L m =>
    (y = ((boxEntranceBond c x S Q X r).source : FourTorus c.L m) ∨
      y = ((boxEntranceBond c x S Q X r).target : FourTorus c.L m)) ∧
    y ∉ S.innerBox c.r x Q
variable {Stored Lebesgue : Type}
def TouchesInnerBox (b : GradedBond c.L m K) : Prop :=
  (b.2.source : FourTorus c.L m) ∈ S.innerBox c.r x Q ∨ (b.2.target : FourTorus c.L m) ∈ S.innerBox c.r x Q
structure IsMixedDatum (v : BondField c.L m K k Stored) : Prop where
  covers_iff : ∀ b : GradedBond c.L m K, v.Covers b ↔
    b ∈ activeBondSet K k (S.trimmedDomain c.r x Q) ∨
      OrientedEdgeEnds.flip b ∈ activeBondSet K k (S.trimmedDomain c.r x Q)
  stored_of : ∀ b : v.support, b.1.1 < k ∨ TouchesInnerBox c x S Q b.1 →
    ∃ s, v.coord b = Sum.inr s
  block_of : ∀ b : v.support, b.1.1 = k → ¬TouchesInnerBox c x S Q b.1 →
    ∃ p : PositivelyOrientedBond c.L m (levelDepth K k), b.1 = ⟨k, p.1⟩ ∧ v.coord b = Sum.inl p
variable {v : BondField c.L m K k Stored} {𝔅 : Finset (GradedBond c.L m K)} {𝒴 : Type u}
  [MeasurableSpace 𝒴] {𝒲 : Type w} [MeasurableSpace 𝒲]
def innerBoxPoints [Finite (SiteAtLevel c.L m K k)] (X : Set (FourTorus c.L m)) :
    Finset (FourTorus c.L m) :=
  (Set.toFinite (Subtype.val '' S.componentBoxSites c.r x Q X)).toFinset
end Moves
end PeriodicLattice.LargeFieldGaugeMoves
end YangMills.Construction
