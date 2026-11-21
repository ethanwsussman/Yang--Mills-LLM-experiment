import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def chartMove (U A : ChainChart F) (τ : ℝ) : ChainChart F :=
  ⟨fun x i => U.fine x i + τ • A.fine x i, fun j y i => U.coarse j y i + τ • A.coarse j y i⟩
def chartSum (U A : ChainChart F) : ChainChart F := chartMove U A 1
def IsStationaryAlong (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (U A : ChainChart F) : Prop :=
  HasDerivAt (fun τ : ℝ => chartAction a S R (chartMove U A τ) V) 0 0
def ChartEqOnBonds (S : Finset F.Cell) (U U' : ChainChart F) : Prop :=
  (∀ b ∈ innerBonds S 0, U.fine b.1 b.2 = U'.fine b.1 b.2) ∧
    ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1), U.coarse j c.1 c.2 = U'.coarse j c.1 c.2
def oneSiteWeights (F : BlockFrame) : F.SiteWeights := fun _ _ => 1
def chartBondMisfit (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  chartChain R U V (j + 1) c.1 c.2 *
    (polarUnit (gaugedContourAverage (chartChain R U V j) (chartGauge R U (j + 1)) c))⁻¹
def normSubOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
open Classical in
def localQuarticSum (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (p : F.Site 0)
    (r : ℝ) : ℝ :=
  ∑ b ∈ (innerBonds S j).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j),
    normSubOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) ^ 4
open Classical in
def localCurvatureSum (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) (r : ℝ) : ℝ :=
  ∑ q ∈ (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r),
    ‖((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2
open Classical in
def localMisfitSum (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (p : F.Site 0) (r : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range F.top).filter (fun j => (F.blockSide : ℝ) ^ (j + 1) ≤ r),
    ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
      normSubOne (chartBondMisfit R U V j c) ^ 2
def cellMisfitSum (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (j e : ℕ) (z : F.Cell) : ℝ :=
  ∑ c ∈ bondsOver S {z} (j + 1), normSubOne (chartBondMisfit R U V j c) ^ e
def referenceSecondDeriv (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (U A : ChainChart F) : ℝ :=
  deriv (fun τ : ℝ => deriv (fun σ : ℝ => chartAction a S R
    (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ U τ) A σ) V) 0) 0
end BlockAverages
end YangMills.Construction
end
