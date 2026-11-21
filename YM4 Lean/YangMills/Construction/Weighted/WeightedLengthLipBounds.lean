import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.LengthDensity
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted
def MeetOnlyAtEnds (S : ℝ) (s s' : LiftedSegment) : Prop :=
  s.support S ∩ s'.support S ⊆
    {s.pointAt S 0, s.pointAt S 1} ∩ {s'.pointAt S 0, s'.pointAt S 1}
def LipschitzL1LipLeOne {S : ℝ} (f : Torus4 S → ℝ) : Prop :=
  LipschitzL1 f ∧ ∀ z, localLip f z ≤ 1
def WeightedLengthAndLip : Prop :=
  ∀ G : GivenChain,
    (∀ Γ : List LiftedSegment,
      setLIntegralL1 (segmentsSupport G.data.side Γ)
          (fun x => ENNReal.ofReal (G.chain.weightDensity x)) ≤
        ENNReal.ofReal (G.chain.weightedLength Γ) ∧
      ((∀ s ∈ Γ, l1NormVec s.displacement < G.data.side) →
        Γ.Pairwise (MeetOnlyAtEnds G.data.side) →
        ENNReal.ofReal (G.chain.weightedLength Γ) =
          setLIntegralL1 (segmentsSupport G.data.side Γ)
            (fun x => ENNReal.ofReal (G.chain.weightDensity x)))) ∧
    (∀ y ∈ G.chain.allSites, ∀ x ∈ interior (G.chain.siteCube y),
      G.chain.weightDensity x = (G.chain.siteScale y)⁻¹) ∧
    (∀ A : Set G.data.Space, A.Nonempty →
      LipschitzL1LipLeOne fun z : G.data.Space => (setSupDist {z} A).toReal) ∧
    (∀ x : G.data.Space, LipschitzL1LipLeOne fun z : G.data.Space => torusL1Norm (z - x)) ∧
    (∀ f₁ f₂ : G.data.Space → ℝ, LipschitzL1 f₁ → LipschitzL1 f₂ →
      ∀ s₁ s₂ ρ : ℝ, 0 ≤ s₁ → 0 ≤ s₂ → 0 ≤ ρ → ∀ x : G.data.Space,
        localLip (fun z => s₁ * f₁ z + s₂ * f₂ z) x ≤
          ENNReal.ofReal s₁ * localLip f₁ x +
            ENNReal.ofReal s₂ * localLip f₂ x ∧
        localLip (fun z => min (f₁ z) ρ) x ≤ localLip f₁ x ∧
        localLip (fun z => f₁ z * f₂ z) x ≤
          ENNReal.ofReal |f₁ x| * localLip f₂ x +
            ENNReal.ofReal |f₂ x| * localLip f₁ x ∧
        ((∀ᶠ z in 𝓝 x, f₁ z = f₁ x) → localLip f₁ x = 0))
end Weighted
end YangMills.Construction
