import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def classWeight (F : BlockFrame) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) : F.SiteWeights :=
  fun j x => Real.exp (φ (enclosingCell x)) * (scaleRadius F j p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ)
def invertedWeights (w : F.SiteWeights) : F.SiteWeights := fun j x => (w j x)⁻¹
def covariantDiff (R : F.GaugeField 0) (ξ : F.Site 0 → ℍ[ℝ]) : F.Site 0 → Fin 4 → ℍ[ℝ] :=
  fun x i => adjointAction (R x i) (ξ (x + unitStep 0 i)) - ξ x
def cellwiseL4Norm (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : ℝ :=
  Real.sqrt (∑ z ∈ S, Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4))
def weightedBondL2Norm (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : ℝ :=
  Real.sqrt (∑ b ∈ innerBonds S 0, (w b.1 * ‖f b.1 b.2‖) ^ 2)
def baseOnlyChart (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : ChainChart F := ⟨u, fun _ _ _ => 0⟩
def cellBondNorm (q : ℝ) (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (z : F.Cell) : ℝ :=
  (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ q) ^ (1 / q)
def cellPlaquetteNorm (q : ℝ) (S : Finset F.Cell) (w : F.Site 0 → ℝ)
    (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ]) (z : F.Cell) : ℝ :=
  (∑ p ∈ plaquettesOver S {z} 0, (w p.1 * ‖g p‖) ^ q) ^ (1 / q)
def cellSiteNorm (q : ℝ) (S : Finset F.Cell) (w : F.Site 0 → ℝ) (ξ : F.Site 0 → ℍ[ℝ]) (z : F.Cell) : ℝ := by
  classical exact
    (∑ x ∈ (sitesOfCells S 0).filter (fun x => enclosingCell x = z), (w x * ‖ξ x‖) ^ q) ^ (1 / q)
def cellTopNorm (S : Finset F.Cell) (w : F.Cell → ℝ) (f : F.Cell → Fin 4 → ℍ[ℝ]) (z : F.Cell) : ℝ :=
  Real.sqrt (∑ c ∈ bondsOver S {z} F.top, (w (c.1 : F.Cell) * ‖f c.1 c.2‖) ^ 2)
end YangMills.Construction.BlockAverages
end
