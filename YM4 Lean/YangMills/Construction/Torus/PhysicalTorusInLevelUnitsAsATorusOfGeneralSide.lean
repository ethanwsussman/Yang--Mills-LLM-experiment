import YangMills.Construction.Geometry.ToriGeneralSide
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set YangMills.Construction.TorusMetric
namespace GeneralTorus
structure LevelUnitParams where
  L : ℕ
  blocking : Blocking.DimFourOddBlockingFactorGeThirteen 4 L
  m : ℕ
  m_pos : 0 < m
  K : ℕ
  K_pos : 0 < K
  t : ℕ
  t_le : t ≤ K
  blockExp : ℕ
  gapExp : ℕ
namespace LevelUnitParams
variable (P : LevelUnitParams)
abbrev PhysSpace : Type := PeriodicLattice.FourTorus P.L P.m
def toScaleData : ScaleData :=
  physicalInLevelUnits P.L P.blocking P.m P.K P.t P.t_le P.blockExp P.gapExp
def seqScales : SeparatedSequences.ScaleData :=
  ⟨P.K, P.t, P.t, P.blockExp, P.t_le, P.t_le⟩
def gapFactor : ℝ := (P.L : ℝ) ^ P.gapExp
def lengthFactor : ℝ := (P.L : ℝ) ^ (P.K - P.t)
theorem L_ne_zero : (P.L : ℝ) ≠ 0 := by
  have := P.blocking.thirteen_le
  exact_mod_cast (by omega : P.L ≠ 0)
theorem physSide_ne_zero : PeriodicLattice.torusSide P.L P.m ≠ 0 :=
  mul_ne_zero two_ne_zero (pow_ne_zero _ P.L_ne_zero)
theorem torusSide_ne_zero : P.toScaleData.torusSide ≠ 0 :=
  mul_ne_zero two_ne_zero (pow_ne_zero _ P.L_ne_zero)
def levelEquiv : P.PhysSpace ≃+ P.toScaleData.Space :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle (PeriodicLattice.torusSide P.L P.m) P.toScaleData.torusSide
      P.physSide_ne_zero P.torusSide_ne_zero
def scaleSegment (s : LiftedSegment) : LiftedSegment :=
  ⟨P.lengthFactor • s.tail, P.lengthFactor • s.head⟩
abbrev readPoint (x : P.PhysSpace) : P.toScaleData.Space := P.levelEquiv x
def IsReadOf (Ω : ℕ → Set P.PhysSpace) (B : SeparatedChain P.toScaleData) : Prop :=
  ∀ n, B.set n = P.readPoint '' SeparatedSequences.truncatedMember P.seqScales Ω n
def TorusLatticesAgree : Prop :=
  P.toScaleData.levelSpacing P.t = 1 ∧
    IsEvenMultipleOf P.toScaleData.torusSide (P.toScaleData.levelSpacing P.t) ∧
    P.toScaleData.torusSide = 2 * (P.L : ℝ) ^ (P.m + P.K - P.t) ∧
    P.toScaleData.torusSide =
      PeriodicLattice.toLevelUnits P.L P.K P.t (PeriodicLattice.torusSide P.L P.m) ∧
    (∀ v : Fin 4 → ℝ, P.readPoint (torusProj (PeriodicLattice.torusSide P.L P.m) v) =
      torusProj P.toScaleData.torusSide (P.lengthFactor • v)) ∧
    ∀ n ≤ P.t,
      P.toScaleData.levelSpacing n =
          PeriodicLattice.toLevelUnits P.L P.K P.t
            (PeriodicLattice.meshSize P.L (PeriodicLattice.levelDepth P.K n)) ∧
        P.readPoint '' (PeriodicLattice.sublattice P.L P.m (PeriodicLattice.levelDepth P.K n) :
            Set P.PhysSpace) =
          (P.toScaleData.levelSublattice n : Set P.toScaleData.Space)
def LevelCubesAgree : Prop :=
  ∀ n ≤ P.t,
    (-(P.m : ℤ) ≤ PeriodicLattice.coarseCubeIndex P.K P.blockExp n ↔
      P.blockExp ≤ P.m + P.K - n) ∧
    (P.blockExp ≤ P.m + P.K - n ↔
      IsEvenMultipleOf P.toScaleData.torusSide (P.toScaleData.blockLength n)) ∧
    (P.blockExp ≤ P.m + P.K - n →
      (fun Q => P.readPoint '' Q) ''
          PeriodicLattice.standardCubePartition P.L P.m
            (PeriodicLattice.coarseCubeIndex P.K P.blockExp n) =
        P.toScaleData.blockPartition n)
def SeparatedSequencesAgree : Prop :=
  (∀ Ω : ℕ → Set P.PhysSpace,
      SeparatedSequences.IsSeparatedSequence P.seqScales P.gapFactor Ω →
      ∃ B : SeparatedChain P.toScaleData, P.IsReadOf Ω B) ∧
    ∀ B : SeparatedChain P.toScaleData, ∃ Ω : ℕ → Set P.PhysSpace,
      SeparatedSequences.IsSeparatedSequence P.seqScales P.gapFactor Ω ∧ P.IsReadOf Ω B
def SequenceObjectsAgree : Prop :=
  ∀ (Ω : ℕ → Set P.PhysSpace) (B : SeparatedChain P.toScaleData),
    SeparatedSequences.IsSeparatedSequence P.seqScales P.gapFactor Ω → P.IsReadOf Ω B →
      (∀ n, B.shell n = P.readPoint '' SeparatedSequences.layerSet P.seqScales Ω n) ∧
      (∀ n ≤ P.t, B.shellSites n =
        (fun y : PeriodicLattice.SiteAtLevel P.L P.m P.K n => P.readPoint (y : P.PhysSpace)) ''
          SeparatedSequences.layerLatticeSites P.seqScales Ω n) ∧
      (∀ n ≤ P.t, ∀ y ∈ SeparatedSequences.layerLatticeSites P.seqScales Ω n,
        B.localSpacing (P.readPoint (y : P.PhysSpace)) = P.seqScales.levelMesh P.L n ∧
        B.localCube (P.readPoint (y : P.PhysSpace)) =
          P.readPoint '' SeparatedSequences.siteBlock P.seqScales y ∧
        B.localDoubleCube (P.readPoint (y : P.PhysSpace)) =
          P.readPoint '' SeparatedSequences.doubledSiteBlock P.seqScales y) ∧
      (∀ Γ : List LiftedSegment, B.scaledLength (Γ.map P.scaleSegment) =
        SeparatedSequences.layerWeightedLength P.seqScales Ω Γ) ∧
      ∀ y y' : P.PhysSpace,
        ENNReal.ofReal (B.scaledDist (P.readPoint y) (P.readPoint y')) =
          SeparatedSequences.layerWeightedDist P.seqScales Ω y y'
def EvaluationAgrees : Prop :=
  ∀ P : LevelUnitParams,
    P.TorusLatticesAgree ∧ P.LevelCubesAgree ∧ P.SeparatedSequencesAgree ∧
      P.SequenceObjectsAgree
end LevelUnitParams
end GeneralTorus
end YangMills.Construction
