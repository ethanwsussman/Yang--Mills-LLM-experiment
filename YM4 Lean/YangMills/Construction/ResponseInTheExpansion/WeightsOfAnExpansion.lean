import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
def fineSide (L : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => fineSide L t (n * L)
theorem fineSide_eq (L t n : ℕ) : fineSide L t n = n * L ^ t := by
  induction t generalizing n with
  | zero => simp [fineSide]
  | succ t ih => rw [fineSide, ih, pow_succ]; ring
instance instNeZeroFineSide (L t n : ℕ) [NeZero L] [NeZero n] : NeZero (fineSide L t n) :=
  ⟨by
    rw [fineSide_eq]
    exact mul_ne_zero (NeZero.ne n) (pow_ne_zero _ (NeZero.ne L))⟩
abbrev PlaquetteWeight (m : ℕ) : Type := TorusFields.TorusPlaquette m → ℝ
abbrev OrientedPlaquette (m : ℕ) : Type := {p : TorusFields.TorusPlaquette m // p.2.1 < p.2.2}
def constOneWeight (m : ℕ) : PlaquetteWeight m := fun _ => 1
def translateWeight {m : ℕ} (u : TorusFields.TorusSite m) (h : PlaquetteWeight m) : PlaquetteWeight m :=
  fun p => h (p.1 + u, p.2)
def doubledBarycentre {m : ℕ} (p : TorusFields.TorusPlaquette m) : TorusFields.TorusSite (2 * m) := fun i =>
  ((2 * (p.1 i).val + (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0) : ℕ) : ZMod (2 * m))
def barycentreDist (L t : ℕ) {m : ℕ} (p p' : TorusFields.TorusPlaquette m) : ℝ :=
  (TorusFields.supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) / (2 * (L : ℝ) ^ t)
def weightSup {m : ℕ} (h : PlaquetteWeight m) : ℝ := ⨆ p : OrientedPlaquette m, |h p.1|
def weightLipschitz (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : ℝ :=
  ⨆ pp : OrientedPlaquette m × OrientedPlaquette m, |h pp.1.1 - h pp.2.1| / barycentreDist L t pp.1.1 pp.2.1
def weightNorm (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : ℝ := max (weightSup h) (weightLipschitz L t h)
def fineBlock (L : ℕ) [NeZero L] :
    (t n : ℕ) → [NeZero n] → TorusFields.TorusSite n → Finset (TorusFields.TorusSite (fineSide L t n))
  | 0, _, _, y => {y}
  | t + 1, n, _, Y => (TorusLumps.sitesInBlocks L {Y}).biUnion fun y => fineBlock L t (n * L) y
def fineCentre (L t : ℕ) {n : ℕ} (y : TorusFields.TorusSite n) : TorusFields.TorusSite (fineSide L t n) :=
  TorusFields.siteOfInt fun i => (L : ℤ) ^ t * ((y i).cast : ℤ)
def fineTranslate (L t n : ℕ) (v : Fin 4 → ℤ) : TorusFields.TorusSite (fineSide L t n) :=
  TorusFields.siteOfInt fun i => (L : ℤ) ^ t * v i
def IsPlaquetteAt (L : ℕ) [NeZero L] (t : ℕ) {n : ℕ} [NeZero n] (y : TorusFields.TorusSite n)
    (p : TorusFields.TorusPlaquette (fineSide L t n)) : Prop :=
  p.2.1 < p.2.2 ∧ ∃ c ∈ TorusFields.plaquetteVertices p.1 p.2.1 p.2.2, c ∈ fineBlock L t n y
def vertexMultiplicity {n : ℕ} (y : TorusFields.TorusSite n) (p : TorusFields.TorusPlaquette n) : ℝ :=
  (((TorusFields.plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ)
def blockMean (L : ℕ) [NeZero L] :
    (t n : ℕ) → [NeZero n] → TorusFields.TorusSite n → PlaquetteWeight (fineSide L t n) → ℝ
  | 0, _, _, y, h => (1 / 24) * ∑ p ∈ TorusFields.plaquettesIn Finset.univ, vertexMultiplicity y p * h p
  | t + 1, n, _, Y, h => ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, blockMean L t (n * L) y h
def WeightsAgreeAt (L : ℕ) [NeZero L] (t : ℕ) {n n' : ℕ} [NeZero n] (y : TorusFields.TorusSite n)
    (y' : TorusFields.TorusSite n')
    (h : PlaquetteWeight (fineSide L t n)) (h' : PlaquetteWeight (fineSide L t n')) : Prop :=
  ∀ (z : Fin 4 → ℤ) (μ ν : Fin 4), (∀ i, |z i| ≤ (L : ℤ) ^ t) →
    IsPlaquetteAt L t y (fineCentre L t y + TorusFields.siteOfInt z, μ, ν) →
    h (fineCentre L t y + TorusFields.siteOfInt z, μ, ν) = h' (fineCentre L t y' + TorusFields.siteOfInt z, μ, ν)
def plaquetteEnergyOf {n : ℕ} (W : TorusFields.TorusField n) (p : TorusFields.TorusPlaquette n) : ℝ :=
  TorusFields.plaquetteEnergy W p.1 p.2.1 p.2.2
def siteResponse {n : ℕ} [NeZero n] (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n)
    (h : PlaquetteWeight n) : ℝ :=
  ∑ p ∈ TorusFields.plaquettesIn Finset.univ, vertexMultiplicity y p / 4 * (h p * plaquetteEnergyOf W p)
end WeightedResponses
end YangMills.Construction
end
