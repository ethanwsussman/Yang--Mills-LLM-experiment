import YangMills.Construction.ReflectionPositivity.InstancesOfTheInequalityAtAMirror
import YangMills.Construction.ReflectionPositivity.LinkMirrorAboveTheHyperplaneAndLatticeFunctionsOfACombination
import Mathlib
set_option autoImplicit false
open Filter
open scoped ComplexConjugate ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.LimitPositivity
open Ambient
def OnTorus : Prop :=
  ∀ (D : MirrorData) (S : LatticeDataSeq D torus) (T : FunctionalFamily D torus),
    S.TendsToFamily T → ∀ (P : CoordMirror) (I : P.PositivityInstance D torus),
      I.HoldsReal T.centeredFunctional
abbrev LipTuple (D : MirrorData) (n : ℕ) : Type :=
  LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n
abbrev LipFamily (D : MirrorData) : Type :=
  LimitSpaces.Ambient.periodic.TupleFunctionals D.toStandingParameters .lip Set.univ
def IsConnectedLimit (D : MirrorData) (β : ℕ+ → ℝ) (Ψ : LipFamily D) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : LipTuple D n),
    Tendsto (fun k : ℕ+ => SchwingerFunctions.connectedSchwinger D.L D.m k (β k) f.1) atTop
      (𝓝 ((Ψ n hn f : ℝ) : ℂ))
def SharpBounded (D : MirrorData) (M : LimitSpaces.SharpParameter)
    (Ψ : LipFamily D) : Prop :=
  ∃ C : ℕ → ℝ → ℝ, (∀ n, 2 ≤ n → ∀ d, 0 < d → 0 ≤ C n d) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ f : LipTuple D n,
      (Pairwise fun i j => ENNReal.ofReal d ≤
        LimitSpaces.Ambient.periodic.infSetDist D.toStandingParameters
          (LimitSpaces.Ambient.periodic.closedSupport D.toStandingParameters (f.1 i))
          (LimitSpaces.Ambient.periodic.closedSupport D.toStandingParameters (f.1 j))) →
      |Ψ n hn f| ≤ C n d *
        ∏ i, LimitSpaces.Ambient.normSharp D.toStandingParameters M .periodic (f.1 i)
def limitCentred {D : MirrorData} (Ψ : LipFamily D) (X : sepLipTuples D) : ℝ :=
  LimitSpaces.Ambient.periodic.centredSum D.toStandingParameters Ψ ⟨X.1.get, X.2⟩
def limitCentredSmooth {D : MirrorData} (Ψ : LipFamily D) (X : separatedAll D torus) : ℝ :=
  evalOrZero (limitCentred Ψ) X.1
def BoundedLimitCondition : Prop :=
  ∀ (D : MirrorData) (M : LimitSpaces.SharpParameter) (k₀ : ℕ+) (β : ℕ+ → ℝ),
    (∀ k, k₀ ≤ k → 0 < β k) → ∀ Ψ : LipFamily D,
      IsConnectedLimit D β Ψ → SharpBounded D M Ψ →
      ∀ μ : Fin 4,
        (∀ c ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters,
          ∀ I : (⟨μ, c⟩ : CoordMirror).LipPositivityInstance D,
            I.HoldsReal (limitCentred Ψ)) ∧
        (∀ (c : ℝ) (I : (⟨μ, c⟩ : CoordMirror).PositivityInstance D torus),
          I.HoldsReal (limitCentredSmooth Ψ))
section Euclidean
variable {D : MirrorData} (S : LatticeDataSeq D euclidean) (T : FunctionalFamily D euclidean)
  {r r' : ℕ} (c : Fin r → ℂ) (X : Fin r → separatedWithin D euclidean (upperHalf D))
  (c' : Fin r' → ℂ) (Y : Fin r' → separatedWithin D euclidean (upperHalf D))
def latticePairing (j : ℕ+) : ℂ :=
  (S.linkLevel j).thetaForm (S.latticeFn c X j) (S.latticeFn c' Y j)
def limitPairing : ℂ :=
  (CoordMirror.timeAt 0).reflectionForm D euclidean (fun Z => (T.centeredFunctional Z : ℂ))
    (TupleCombination.sumOf c X) (TupleCombination.sumOf c' Y)
def LatticePairingEventually : Prop :=
  ∀ᶠ j in atTop,
    S.latticeFn c X j ∈ (S.linkLevel j).halfAlgebra .pos ∧
    S.latticeFn c' Y j ∈ (S.linkLevel j).halfAlgebra .pos ∧
    latticePairing S c X c' Y j = ∑ i, ∑ k, conj (c i) * c' k *
      ((S.centredAt j ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean
        (X i).1 (Y k).1) : ℝ) : ℂ) ∧
    0 ≤ latticePairing S c X c X j
def PairingTendsto : Prop :=
  Tendsto (latticePairing S c X c' Y) atTop (𝓝 (limitPairing T c X c' Y))
def PairingPosSemidef : Prop :=
  ∀ F : TupleCombination D euclidean (upperHalf D),
    0 ≤ (CoordMirror.timeAt 0).reflectionForm D euclidean (fun Z => (T.centeredFunctional Z : ℂ)) F F
end Euclidean
def OnEuclidean : Prop :=
  ∀ (D : MirrorData) (S : LatticeDataSeq D euclidean) (T : FunctionalFamily D euclidean),
    S.TendsToFamily T →
    (∀ (r r' : ℕ) (c : Fin r → ℂ) (X : Fin r → separatedWithin D euclidean (upperHalf D))
      (c' : Fin r' → ℂ) (Y : Fin r' → separatedWithin D euclidean (upperHalf D)),
      LatticePairingEventually S c X c' Y ∧
      PairingTendsto S T c X c' Y ∧
      0 ≤ limitPairing T c X c X) ∧
    PairingPosSemidef T ∧
    ∀ (P : CoordMirror) (I : P.PositivityInstance D euclidean),
      I.HoldsReal T.centeredFunctional
def LimitPositivityStatement : Prop :=
  OnTorus ∧ BoundedLimitCondition ∧ OnEuclidean
end YangMills.Construction.ReflectionPositivity.AxisMirror.LimitPositivity
end
