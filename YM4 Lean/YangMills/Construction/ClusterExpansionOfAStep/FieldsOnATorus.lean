import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace TorusFields
open YangMills.Construction.BlockAverages
theorem isCompact_unitary_quaternion : IsCompact (unitary ℍ[ℝ] : Set ℍ[ℝ]) := by
  have hclosed : IsClosed (unitary ℍ[ℝ] : Set ℍ[ℝ]) := by
    have hset : (unitary ℍ[ℝ] : Set ℍ[ℝ]) = {q | star q * q = 1} ∩ {q | q * star q = 1} := by
      ext q
      simp [Unitary.mem_iff]
    rw [hset]
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hbdd : Bornology.IsBounded (unitary ℍ[ℝ] : Set ℍ[ℝ]) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℍ[ℝ])) (r := 1)).subset ?_
    intro q hq
    have hnormSq : Quaternion.normSq q = 1 := by
      have hstar := (Unitary.mem_iff.mp hq).1
      rw [Quaternion.star_mul_self] at hstar
      simpa using congrArg (fun z : ℍ[ℝ] => z.re) hstar
    have hsq : ‖q‖ * ‖q‖ = 1 := by rw [← Quaternion.normSq_eq_norm_mul_self, hnormSq]
    have hle : ‖q‖ ≤ 1 := by nlinarith [norm_nonneg q]
    simpa [Metric.mem_closedBall, dist_zero_right] using hle
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd
instance : CompactSpace UnitQuaternion := isCompact_iff_compactSpace.mp isCompact_unitary_quaternion
instance : MeasurableSpace UnitQuaternion := borel UnitQuaternion
instance : BorelSpace UnitQuaternion := ⟨rfl⟩
def haarUnit : Measure UnitQuaternion := Measure.haarMeasure ⊤
instance : IsProbabilityMeasure haarUnit := ⟨Measure.haarMeasure_self⟩
instance : haarUnit.IsHaarMeasure := by unfold haarUnit; infer_instance
abbrev TorusSite (n : ℕ) : Type := Fin 4 → ZMod n
abbrev TorusField (n : ℕ) : Type := TorusSite n → Fin 4 → UnitQuaternion
abbrev TorusBond (n : ℕ) : Type := TorusSite n × Fin 4
variable {n : ℕ}
def unitStep (n : ℕ) (i : Fin 4) : TorusSite n := Pi.single i 1
def trivialField (n : ℕ) : TorusField n := fun _ _ => 1
def supDist (x y : TorusSite n) : ℕ := Finset.univ.sup fun i => ((x i - y i).valMinAbs).natAbs
def siteOfInt (z : Fin 4 → ℤ) : TorusSite n := fun i => (z i : ZMod n)
def holonomy (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : UnitQuaternion :=
  W x μ * W (x + unitStep n μ) ν * (W (x + unitStep n ν) μ)⁻¹ * (W x ν)⁻¹
def curvature (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : ℝ :=
  ‖((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖
def plaquetteVertices (x : TorusSite n) (μ ν : Fin 4) : List (TorusSite n) :=
  [x, x + unitStep n μ, x + unitStep n ν, x + unitStep n μ + unitStep n ν]
def IsCold (s : ℝ) (W : TorusField n) : Prop := ∀ x μ ν, μ < ν → curvature W x μ ν < s
def gaugeTransform (g : TorusSite n → UnitQuaternion) (W : TorusField n) : TorusField n :=
  fun x i => g x * W x i * (g (x + unitStep n i))⁻¹
def translate (u : TorusSite n) (W : TorusField n) : TorusField n := fun x i => W (x + u) i
structure TorusIsometry where
  axisPerm : Equiv.Perm (Fin 4)
  axisSign : Fin 4 → ℤ
  offset : Fin 4 → ℤ
  axisSign_unit : ∀ i, axisSign i = 1 ∨ axisSign i = -1
def TorusIsometry.mapSite (g : TorusIsometry) (x : TorusSite n) : TorusSite n :=
  fun i => (g.axisSign i : ZMod n) * x (g.axisPerm i) + (g.offset i : ZMod n)
def TorusIsometry.Transports (g : TorusIsometry) (W W' : TorusField n) : Prop :=
  ∀ x k, if g.axisSign (g.axisPerm.symm k) = 1 then W' (g.mapSite x) (g.axisPerm.symm k) = W x k
    else (W' (g.mapSite x - unitStep n (g.axisPerm.symm k)) (g.axisPerm.symm k))⁻¹ = W x k
def perturb {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) : TorusField n :=
  fun x i => expUnit (∑ l, if c l = (x, i) then σ l • X l else 0) * W x i
def mixedDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (G : TorusField n → E)
    (W : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) : E :=
  iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0 (fun l => Pi.single l 1)
def ContDiffThreeAt (G : TorusField n → ℝ) (W : TorusField n) : Prop :=
  ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0
def supportDiam {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n) : ℕ :=
  max (Finset.univ.sup fun l : Fin k => supDist y (c l).1)
    (Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => supDist (c l).1 (c l').1)
def OffsetInBox (r : ℕ) (h : Fin 4 → ℤ) : Prop := ∀ i, |h i| ≤ (r : ℤ)
def BondOffsetInBox (r : ℕ) (b : (Fin 4 → ℤ) × Fin 4) : Prop :=
  OffsetInBox r b.1 ∧ OffsetInBox r (b.1 + Pi.single b.2 1)
def fieldHaar (n : ℕ) [NeZero n] : Measure (TorusField n) :=
  Measure.pi fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit
instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (fieldHaar n) := by
  unfold fieldHaar
  infer_instance
def plaquetteEnergy (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : ℝ :=
  1 - ((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]).re
abbrev TorusPlaquette (n : ℕ) : Type := TorusSite n × Fin 4 × Fin 4
open Classical in
def plaquettesIn [NeZero n] (S : Finset (TorusSite n)) : Finset (TorusPlaquette n) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S
def wilsonAction [NeZero n] (S : Finset (TorusSite n)) (W : TorusField n) : ℝ :=
  ∑ p ∈ plaquettesIn S, plaquetteEnergy W p.1 p.2.1 p.2.2
def readAtLevel (F : BlockFrame) (j : ℕ) (W : TorusField n) : F.GaugeField j :=
  fun x i => W (fun k => ((siteCoords x k : ℤ) : ZMod n)) i
open Classical in
def cellsOfSites (F : BlockFrame) (S : Finset (TorusSite n)) : Finset F.Cell :=
  S.image fun x => siteOfCoords F.top fun i => ((x i).cast : ℤ)
def torusFrame (L t n : ℕ) : BlockFrame := ⟨L, t, fun _ => n⟩
def actionAtLevel [NeZero n] (a : ℝ) (L : ℕ) : ℕ → Finset (TorusSite n) → TorusField n → ℝ
  | 0, S, W => wilsonAction S W
  | t + 1, S, W =>
    minimalAction a (cellsOfSites (torusFrame L t n) S) (t + 1)
      (readAtLevel (torusFrame L t n) (t + 1) W)
end TorusFields
end YangMills.Construction
end
