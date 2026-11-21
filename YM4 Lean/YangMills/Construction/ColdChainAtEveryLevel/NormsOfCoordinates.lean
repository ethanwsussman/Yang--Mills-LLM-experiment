import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ℍ[ℝ] :=
  (g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
def linearizedCurl (R : F.GaugeField 0) (a : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) : ℍ[ℝ] :=
  let μ := p.2.1
  let ν := p.2.2
  let x := p.1
  let r1 := R x μ
  let r2 := R (x + unitStep 0 μ) ν
  let r3 := R (x + unitStep 0 ν) μ
  let r4 := R x ν
  (a x μ : ℍ[ℝ]) + adjointAction r1 (a (x + unitStep 0 μ) ν) -
    adjointAction (r1 * r2 * r3⁻¹) (a (x + unitStep 0 ν) μ) -
    adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) (a x ν)
def parallelAverage {j : ℕ} (R : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    ∑ r ∈ Finset.range F.blockSide,
      adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)
def linearPart (R : F.FieldChain) (U : ChainChart F) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => fun x i => U.fine x i
  | j + 1 => fun y i => parallelAverage (R j) (linearPart R U j) (y, i) +
      if j + 1 < F.top then ((U.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) else 0
def bondsOver (S B : Finset F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4) := by
  classical exact (innerBonds S j).filter fun b => enclosingCell b.1 ∈ B
def plaquettesOver (S B : Finset F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4 × Fin 4) := by
  classical exact (innerPlaquettes S j).filter fun p => enclosingCell p.1 ∈ B
abbrev BlockFrame.SiteWeights (F : BlockFrame) : Type := (j : ℕ) → F.Site j → ℝ
def localNormSq (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) +
    ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 +
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2
def cellBall (S : Finset F.Cell) (z : F.Cell) (r : ℕ) : Finset F.Cell := by
  classical exact S.filter fun y => cellSupDist z y ≤ r
def localNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : ℝ :=
  Real.sqrt (localNormSq S (cellBall S z 3) R U w)
def weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ z ∈ S, localNorm S R U w z ^ 2)
def baseDistance {j : ℕ} (x : F.Site j) (p : F.Site 0) : ℕ :=
  Finset.univ.sup fun i => (((baseSite x - p) i).valMinAbs).natAbs
def scaleRadius (F : BlockFrame) (j : ℕ) (p : F.Site 0) (x : F.Site j) : ℝ :=
  min ((F.blockSide : ℝ) ^ F.top) (max ((F.blockSide : ℝ) ^ j) (baseDistance x p))
def decayWeights (F : BlockFrame) (δ θ : ℝ) (p : F.Site 0) (y0 : F.Cell) : F.SiteWeights :=
  fun j x => Real.exp (-δ * cellSupDist (enclosingCell x) y0) *
    (scaleRadius F j p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ)
def supWeightedNorm (S : Finset F.Cell) (δ : ℝ) (R : F.FieldChain) (U : ChainChart F) : ℝ :=
  ⨆ y0 : F.Cell, weightedNorm S R U (decayWeights F δ 0 0 y0)
def quadraticFormNormSq (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) : ℝ :=
  ∑ p ∈ plaquettesOver S S 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 +
    a * ∑ c ∈ bondsOver S S F.top, (w F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2
end YangMills.Construction.BlockAverages
end
