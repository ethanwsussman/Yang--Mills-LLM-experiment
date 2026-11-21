import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.EuclideanFunctionals.CentredFunctionalOnSeparatedTensors
import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TwoSettings
def AffineIsometryIffMotion : Prop :=
  ∀ g : R4 → R4, YangMills.Construction.Euclidean.IsAffineIsometryR4 g ↔ ∃ r : EuclidMotion, ∀ x, r x = g x
def mulOverSupport (F A : FreeSep) : FreeSep :=
  F.sum fun X c => A.sum fun Y c' => (c * c') • toFree (listAppend X.1 Y.1)
def IsFinSumIn (U : Set R4) (F : FreeSep) {m : ℕ} (z : Fin m → ℂ) (X : Fin m → FnList) :
    Prop :=
  (∀ b, X b ∈ sepIn U) ∧ F = ∑ b, z b • toFree (X b)
def IsBilinMul (U U' : Set R4) (F F' G : FreeSep) : Prop :=
  F ∈ freeSpanIn U ∧ F' ∈ freeSpanIn U' ∧
    ∀ (m m' : ℕ) (z : Fin m → ℂ) (X : Fin m → FnList) (z' : Fin m' → ℂ) (Y : Fin m' → FnList),
      IsFinSumIn U F z X → IsFinSumIn U' F' z' Y →
        G = ∑ b, ∑ b', (z b * z' b') • toFree (listAppend (X b) (Y b'))
def MulAgrees : Prop :=
  ∀ U U' U'' : Set R4, IsOpen U → IsOpen U' → IsOpen U'' →
    Disjoint U U' → Disjoint U U'' → Disjoint U' U'' →
    ∀ F ∈ finCombIn U, ∀ A ∈ finCombIn U', ∀ A' ∈ finCombIn U'',
      MulDefined F A ∧
      freeMul F A = mulOverSupport F A ∧
      IsBilinMul U U' F A (freeMul F A) ∧
      TupleRules.MulDefined3 F A A' ∧
      freeMul3 F A A' = mulOverSupport (mulOverSupport F A) A' ∧
      IsBilinMul (U ∪ U') U'' (freeMul F A) A' (freeMul3 F A A')
def ComplexTuplesAgree : Prop :=
  ∀ (n : ℕ) (h : Fin n → R4 → ℂ), ComplexComponents h →
    complexList h = complexTuple h ∧
    SameTensors (complexList h) (complexTuple h) ∧
    ∀ S : ConnFamily, centeredFnFree S (complexList h) =
      centeredFnFree S (complexTuple h)
open Classical in
def TensorCompFormula : Prop :=
  (∀ X : sepAll, tensorCompZero (toFree X.1) = if X.1 = [] then 1 else 0) ∧
  ∀ q : ℕ, 1 ≤ q → ∀ (X : sepAll) (x : YangMills.Construction.TestSpaces.PointTuple q),
    tensorComp q (toFree X.1) x =
      if hq : X.1.length = q then ∏ l : Fin q, ((X.1.get (Fin.cast hq.symm l) (x l) : ℝ) : ℂ) else 0
def TensorSpansAgree : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (q : ℕ),
    sepTensorSpan q =
      YangMills.Construction.LatticeLimits.ModelSpace.sepTensorsTop s
        YangMills.Construction.LatticeLimits.ModelSpace.euclidean q
def SepClassesAgree : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (n : ℕ)
    (f : YangMills.Construction.LatticeLimits.ModelSpace.FunTuple s
      YangMills.Construction.LatticeLimits.ModelSpace.euclidean n),
    f ∈ YangMills.Construction.LatticeLimits.ModelSpace.sepTuplesIn s
        YangMills.Construction.LatticeLimits.ModelSpace.euclidean n ⊤ ↔
      (List.ofFn f : FnList) ∈ sepN n
def familyOnSep (S : ConnFamily) (s : YangMills.Construction.Conventions.StandingParameters) :
    YangMills.Construction.LatticeLimits.ModelSpace.FunctionalSeq s
      YangMills.Construction.LatticeLimits.ModelSpace.euclidean ⊤ :=
  fun n X => S.evalAt n (List.ofFn X.1)
def FunctionalsAgree (S : ConnFamily) (s : YangMills.Construction.Conventions.StandingParameters) :
    Prop :=
  YangMills.Construction.LatticeLimits.ModelSpace.IsMultilinearSeq (familyOnSep S s) ∧
  (∀ (q : ℕ) (f : YangMills.Construction.LatticeLimits.ModelSpace.FunTuple s
      YangMills.Construction.LatticeLimits.ModelSpace.euclidean q)
    (hf : f ∈ YangMills.Construction.LatticeLimits.ModelSpace.sepTuplesIn s
      YangMills.Construction.LatticeLimits.ModelSpace.euclidean q ⊤),
    YangMills.Construction.LatticeLimits.ModelSpace.centredSum (familyOnSep S s) q ⟨f, hf⟩ =
      centeredAt S (List.ofFn f)) ∧
  ∀ q : ℕ, 1 ≤ q → ∀ A : YangMills.Construction.LatticeLimits.ModelSpace.sepTensors s
      YangMills.Construction.LatticeLimits.ModelSpace.euclidean q ⊤,
    centeredOnTensor S q A.1 =
      YangMills.Construction.LatticeLimits.ModelSpace.centredLinearForm (familyOnSep S s) q A
def FunctionNormsFormula (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (c : SharpScale) (f : R4 → 𝕜),
    ((∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      IsLUB (Set.range fun x => ‖f x‖) (YangMills.Construction.TestFunctions.uniformNorm f)) ∧
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * YangMills.Construction.Euclidean.euclidNorm (x - y)) →
      IsLeast {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * YangMills.Construction.Euclidean.euclidNorm (x - y)}
        (YangMills.Construction.TestFunctions.lipConstR4 f)) ∧
    c.sharpNorm f = max (YangMills.Construction.TestFunctions.uniformNorm f)
      (40 * c.M * YangMills.Construction.TestFunctions.lipConstR4 f)
def BallsAndDistsAgree : Prop :=
  (∀ (x : R4) (R : ℝ), 0 < R →
    YangMills.Construction.TestFunctions.closedBallR4 x R =
      {y | YangMills.Construction.Euclidean.euclidNorm (y - x) ≤ R}) ∧
  ∀ A A' : Set R4,
    YangMills.Construction.Euclidean.euclidSetDist A A' =
        YangMills.Construction.TestFunctions.setDistR4 A A' ∧
    YangMills.Construction.TestFunctions.setDistR4 A ∅ = ⊤ ∧
    YangMills.Construction.TestFunctions.setDistR4 ∅ A' = ⊤
open Classical in
def FreeSpaceFormula : Prop :=
  (∀ n : ℕ, ∀ X ∈ sepN n, X.length = n) ∧
  (∀ X Y : sepAll, toFree X.1 Y = if Y = X then 1 else 0) ∧
  (∀ U : Set R4, IsOpen U → finCombIn U = freeSpanIn U) ∧
  ∀ (m : ℕ) (c : Fin m → ℂ) (X : Fin m → sepAll),
    freeConj (∑ b, c b • toFree (X b).1) = ∑ b, conj (c b) • toFree (X b).1
def ActionFormula : Prop :=
  (∀ (r : EuclidMotion) (α : Type) (f : R4 → α) (x : R4), r.actFn f (r x) = f x) ∧
  (∀ (r : EuclidMotion) (X : FnList), r.actList X = X.map r.actFn) ∧
  (∀ r : EuclidMotion, r.actList [] = []) ∧
  (∀ (r : EuclidMotion) (X : sepAll), r.actFree (toFree X.1) = toFree (r.actList X.1)) ∧
  ∀ v : R4, (∀ x, EuclidMotion.transl v x = x + v) ∧
    ∀ (α : Type) (f : R4 → α) (x : R4),
      (EuclidMotion.transl v).actFn f x = f (x - v)
def CenteredFnFormula (S : ConnFamily) : Prop :=
  centeredAt S [] = 1 ∧
  (∀ f : R4 → ℝ, [f] ∈ sepAll → centeredAt S [f] = 0) ∧
  (∀ n : ℕ, 2 ≤ n → ∀ f : Fin n → R4 → ℝ, List.ofFn f ∈ sepAll →
    centeredAt S (List.ofFn f) =
      ∑ π ∈ YangMills.Construction.SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k))) ∧
  ∀ X : sepAll, centeredFnFree S (toFree X.1) = (centeredFn S X : ℂ)
def OSFormFormula (S : ConnFamily) : Prop :=
  ∀ F ∈ finCombIn upperHalf, ∀ A ∈ finCombIn upperHalf,
    MulDefined (flipConj F) A ∧
    osForm S F A = centeredFnFree S (freeMul (flipConj F) A)
def FlipAndGroupsFormula : Prop :=
  (∀ μ ν : Fin 4, YangMills.Construction.PeriodicLattice.coordVec μ ν = if ν = μ then 1 else 0) ∧
  (∀ x y : R4, timeFlip x = y ↔ spatialProj y = spatialProj x ∧ y 3 = -x 3) ∧
  upperHalf = {x | 0 < x 3} ∧
  (∀ w : EuclidMotion, w ∈ hyperoctahedral ↔ w.offset = 0 ∧
    ∃ (p : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ), (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
      ∀ (x : R4) (μ : Fin 4), w.lin x μ = ε μ * x (p μ)) ∧
  ∀ w : EuclidMotion, w ∈ timeStabilizer ↔ w ∈ hyperoctahedral ∧ w timeVec = timeVec
def TensorProdFormula : Prop :=
  (∀ q q' : ℕ, 1 ≤ q → 1 ≤ q' →
    ∀ (A : YangMills.Construction.TestSpaces.PointTuple q → ℂ)
      (A' : YangMills.Construction.TestSpaces.PointTuple q' → ℂ)
      (x : YangMills.Construction.TestSpaces.PointTuple (q + q')),
    YangMills.Construction.TestSpaces.tensorFun A A' x =
      A (fun i => x (Fin.castAdd q' i)) * A' (fun j => x (Fin.natAdd q j))) ∧
  ∀ (q : ℕ) (c : ℂ) (A : YangMills.Construction.TestSpaces.PointTuple q → ℂ),
    YangMills.Construction.TestSpaces.scalarTensorLeft c A = c • A ∧
      YangMills.Construction.TestSpaces.scalarTensorRight A c = c • A
def TwoSettingsAgree : Prop :=
  AffineIsometryIffMotion ∧ MulAgrees ∧
    ComplexTuplesAgree ∧ TensorCompFormula ∧
    TensorSpansAgree ∧ SepClassesAgree ∧
    (∀ (S : ConnFamily) (s : YangMills.Construction.Conventions.StandingParameters),
      FunctionalsAgree S s) ∧
    FunctionNormsFormula ℝ ∧ FunctionNormsFormula ℂ ∧
    BallsAndDistsAgree ∧ FreeSpaceFormula ∧ ActionFormula ∧
    (∀ S : ConnFamily, CenteredFnFormula S ∧ OSFormFormula S) ∧
    FlipAndGroupsFormula ∧ TensorProdFormula
end YangMills.Construction.EuclideanFunctionals.TwoSettings
