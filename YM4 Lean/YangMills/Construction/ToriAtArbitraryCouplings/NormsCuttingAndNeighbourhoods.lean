import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import YangMills.Construction.ToriAtArbitraryCouplings.TheSeparationAtEveryLength
import YangMills.Construction.Torus.DistanceOfAPointAndASetAndNeighbourhoodsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace LipschitzEstimates
variable (s : TorusSide) (m' : ℕ) (E : Ambient)
def C1NormComparison : Prop :=
  ∀ f ∈ s.c1CompactSet E,
    TestFunctions.IsBoundedFun f ∧ TestFunctions.IsLipschitzFor (s.pointDist E) f ∧
      ENNReal.ofReal (s.lipConst E f) ≤ s.gradSupNorm E f ∧
      s.gradSupNorm E f ≤
        2 * ENNReal.ofReal (⨆ μ : Fin 4, TestFunctions.uniformNorm (s.partialD μ E f)) ∧
      s.c1NormOn E f ≤ s.c1GradNorm E f ∧
      s.c1GradNorm E f ≤ 2 * s.c1NormOn E f ∧
      s.sharpNormAt m' E f ≤ 40 * (cubeEdge s.L m' : ℝ) * s.c1GradNorm E f ∧
      40 * (cubeEdge s.L m' : ℝ) * s.c1GradNorm E f ≤ 80 * (cubeEdge s.L m' : ℝ) * s.c1NormOn E f
def C1ClassesLipschitz : Prop :=
  (∀ A : Set (s.Point E), s.c1SuppIn E A ⊆ s.lipSuppIn E A) ∧
    ∀ n : ℕ+, s.sepOfLength E n ⊆ s.lipDisjointOfLength E n
def SharpNormSeminorm : Prop :=
  (∀ f ∈ s.lipSuppIn E univ,
    TestFunctions.IsBoundedFun f ∧ TestFunctions.IsLipschitzFor (s.pointDist E) f) ∧
    ∃ (V : Submodule ℝ (s.Point E → ℝ)) (p : Seminorm ℝ V),
      (V : Set (s.Point E → ℝ)) = s.lipSuppIn E univ ∧
        ∀ f : V, p f = s.sharpNormAt m' E (f : s.Point E → ℝ)
def LipschitzCutoffBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (χ : s.Point E → ℝ) (h : s.Point E → 𝕜),
    (∀ x, χ x ∈ Icc (0 : ℝ) 1) → TestFunctions.IsLipschitzFor (s.pointDist E) χ →
      TestFunctions.IsBoundedFun h → TestFunctions.IsLipschitzFor (s.pointDist E) h →
        TestFunctions.IsLipschitzFor (s.pointDist E) (fun x => ((χ x : ℝ) : 𝕜) * h x) ∧
          s.sharpNormAt m' E (fun x => ((χ x : ℝ) : 𝕜) * h x) ≤
            (1 + 40 * (cubeEdge s.L m' : ℝ) * s.lipConst E χ) * s.sharpNormAt m' E h ∧
          s.closedSupport E (fun x => ((χ x : ℝ) : 𝕜) * h x) ⊆
            s.closedSupport E χ ∩ s.closedSupport E h
def CompactSetsSeparated : Prop :=
  (∀ A A' : Set (s.Point E), s.IsCompactWrt E A → s.IsCompactWrt E A' → Disjoint A A' →
    s.PositivelySeparated E A A') ∧
    ∀ (n : ℕ+) (X : s.FnTuple E), X ∈ s.lipDisjointOfLength E n →
      0 < s.gapAllLengths E X
def CompactThickenings : Prop :=
  ∀ (P : Set (s.Point E)) (η : ℝ), s.IsCompactWrt E P → 0 < η →
    s.IsOpenWrt E (AmbientPoints.openThickening s.asMirrorData.toStandingParameters E P η) ∧
      s.IsCompactWrt E (AmbientPoints.closedThickening s.asMirrorData.toStandingParameters E P η)
def ThickeningSeparation : Prop :=
  ∀ (P P' : Set (s.Point E)) (d η : ℝ), s.IsCompactWrt E P → s.IsCompactWrt E P' → 0 < d →
    ENNReal.ofReal d ≤ s.setDist E P P' → 0 < η → η < d / 2 →
      ENNReal.ofReal (d - 2 * η) ≤
        s.setDist E (AmbientPoints.closedThickening s.asMirrorData.toStandingParameters E P η)
          (AmbientPoints.closedThickening s.asMirrorData.toStandingParameters E P' η)
def Combined : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (E : Ambient),
    (C1NormComparison s m' E ∧ C1ClassesLipschitz s E ∧ SharpNormSeminorm s m' E) ∧
      LipschitzCutoffBound s m' E ∧
        CompactSetsSeparated s E ∧ CompactThickenings s E ∧
          ThickeningSeparation s E
end LipschitzEstimates
end YangMills.Construction.ToriAtArbitraryCouplings
end
