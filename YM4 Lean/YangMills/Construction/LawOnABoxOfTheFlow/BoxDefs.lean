import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
instance : MeasurableSpace BlockAverages.imaginaryQuaternions := borel BlockAverages.imaginaryQuaternions
instance : BorelSpace BlockAverages.imaginaryQuaternions := ⟨rfl⟩
def boxRadius (κ₀ x : ℝ) : ℕ := ⌈x ^ κ₀⌉₊
def boxScale (x : ℝ) : ℝ := 2 * x ^ (-(1 / 2 : ℝ)) * Real.log x
def coarseningSteps (L R : ℕ) : ℕ := sInf {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s}
variable {n : ℕ} [NeZero n]
open Classical in
def bondsWithin (S : Finset (TorusFields.TorusSite n)) : Finset (TorusFields.TorusBond n) :=
  Finset.univ.filter fun b => b.1 ∈ S ∧ b.1 + TorusFields.unitStep n b.2 ∈ S
open Classical in
def bondsTouching (o : TorusFields.TorusSite n) (R : ℕ) : Finset (TorusFields.TorusBond n) :=
  Finset.univ.filter fun b => b.1 ∈ ResponseInTheExpansion.supBall o R ∨
    b.1 + TorusFields.unitStep n b.2 ∈ ResponseInTheExpansion.supBall o R
abbrev OuterField (o : TorusFields.TorusSite n) (R : ℕ) : Type :=
  {b : TorusFields.TorusBond n // b ∉ bondsTouching o R} → BlockAverages.UnitQuaternion
abbrev InnerField (o : TorusFields.TorusSite n) (R : ℕ) : Type :=
  {b : TorusFields.TorusBond n // b ∈ bondsTouching o R} → BlockAverages.UnitQuaternion
def restrictOuter (o : TorusFields.TorusSite n) (R : ℕ) (W : TorusFields.TorusField n) : OuterField o R :=
  fun b => W b.1.1 b.1.2
def restrictInner (o : TorusFields.TorusSite n) (R : ℕ) (W : TorusFields.TorusField n) : InnerField o R :=
  fun b => W b.1.1 b.1.2
open Classical in
def glueField {o : TorusFields.TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R) :
    TorusFields.TorusField n := fun x i =>
  if h : (x, i) ∈ bondsTouching o R then w ⟨(x, i), h⟩ else u ⟨(x, i), h⟩
variable {ℓ : TorusLumps.StepParameters}
abbrev OuterData (T : WeightedResponses.StageTower ℓ) (k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ) : Type :=
  OuterField o R × (Σ Y : Finset (TorusFields.TorusSite n), (Y → (T.stage k).labels.Ω))
def outerData (T : WeightedResponses.StageTower ℓ) (k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ)
    (q : WeightedResponses.StageState T k n) : OuterData T k o R :=
  (restrictOuter o R q.1, q.2)
def exponentialField (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    TorusFields.TorusField n := fun x i => BlockAverages.expUnit (A (x, i))
def bondNormSq (S : Finset (TorusFields.TorusSite n))
    (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ b ∈ bondsWithin S, ‖v b‖ ^ 2
def curlNormSq (S : Finset (TorusFields.TorusSite n))
    (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ p ∈ TorusFields.plaquettesIn S, ‖ResponseInTheExpansion.lieFormCurl v p‖ ^ 2
def hessianForm (a : ℝ) (L k : ℕ) (S : Finset (TorusFields.TorusSite n))
    (u v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ b : TorusFields.TorusBond n, ∑ b' : TorusFields.TorusBond n,
    TorusFields.mixedDeriv (TorusFields.actionAtLevel a L k S) (TorusFields.trivialField n) ![b, b'] ![u b, v b']
def latticeGrad (φ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond n) :
    BlockAverages.imaginaryQuaternions :=
  φ b.1 - φ (b.1 + TorusFields.unitStep n b.2)
def covariantGrad (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (χ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond n) :
    BlockAverages.imaginaryQuaternions :=
  χ b.1 - ColdStepAtMirrorFrames.adjointAction (BlockAverages.expUnit (A b)) (χ (b.1 + TorusFields.unitStep n b.2))
def gaugeSlice (o : TorusFields.TorusSite n) (R : ℕ)
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    Submodule ℝ (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) where
  carrier := {ζ | (∀ b, b ∉ bondsTouching o R → ζ b = 0) ∧
    ∀ χ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions,
      (∀ z, z ∉ ResponseInTheExpansion.supBall o R → χ z = 0) →
      ∑ b : TorusFields.TorusBond n, inner ℝ (ζ b) (covariantGrad A χ b) = 0}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun b hb => by simp [hu b hb, hv b hb], fun χ hχ => ?_⟩
    have := hu' χ hχ
    have := hv' χ hχ
    simp only [Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
    linarith
  zero_mem' := by
    refine ⟨fun b _ => rfl, fun χ _ => ?_⟩
    simp
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    refine ⟨fun b hb => by simp [hu b hb], fun χ hχ => ?_⟩
    simp only [Pi.smul_apply, inner_smul_left, ← Finset.mul_sum, hu' χ hχ]
    simp
def sliceEllipsoid (a : ℝ) (L k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ)
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (c : ℝ) :
    Set (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :=
  {ζ | ζ ∈ gaugeSlice o R A ∧ hessianForm a L k (ResponseInTheExpansion.supBall o (2 * R)) (A + ζ) (A + ζ) ≤ c}
def subspaceVolume (V : Submodule ℝ (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)) :
    Measure (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :=
  (Measure.addHaar : Measure V).map Subtype.val
def normalize {X : Type} [MeasurableSpace X] (μ : Measure X) : Measure X := (μ Set.univ)⁻¹ • μ
def sliceGaussian (a : ℝ) (L k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ) (x : ℝ)
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    Measure (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :=
  normalize ((subspaceVolume (gaugeSlice o R A)).withDensity fun ζ => ENNReal.ofReal
    (Real.exp (-(x / 2) * hessianForm a L k (ResponseInTheExpansion.supBall o (2 * R)) (A + ζ) (A + ζ))))
def chartPoint (A ζ : BlockAverages.imaginaryQuaternions) : ℍ[ℝ] :=
  (((Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ : ℍ[ℝ])) *
    ((BlockAverages.expUnit A : BlockAverages.UnitQuaternion) : ℍ[ℝ])
def IsInChart (S : Finset (TorusFields.TorusSite n))
    (A ζ : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (W : TorusFields.TorusField n) : Prop :=
  ∀ b ∈ bondsWithin S, ((W b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = chartPoint (A b) (ζ b)
structure IsAxialSmall (o : TorusFields.TorusSite n) (R : ℕ) (δ : ℝ)
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) : Prop where
  curvature_le : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
    TorusFields.curvature (exponentialField A) p.1 p.2.1 p.2.2 ≤ δ
  norm_le : ∀ b ∈ bondsWithin (ResponseInTheExpansion.supBall o (2 * R)), ‖A b‖ ≤ 7 * R * δ
  curlNormSq_le : curlNormSq (ResponseInTheExpansion.supBall o (2 * R)) A ≤ 2 ^ 13 * (R : ℝ) ^ 4 * δ ^ 2
  bondNormSq_le : bondNormSq (ResponseInTheExpansion.supBall o (2 * R)) A ≤ 2 ^ 16 * (R : ℝ) ^ 6 * δ ^ 2
def IsSupportedGauge (o : TorusFields.TorusSite n) (R : ℕ)
    (γ : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) : Prop :=
  ∀ z, z ∉ ResponseInTheExpansion.supBall o R → γ z = 1
def imaginaryUnitI : BlockAverages.imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
def curlCoeff (p : TorusFields.TorusPlaquette n) (b : TorusFields.TorusBond n) : ℝ :=
  open Classical in
  (if b = (p.1, p.2.1) then 1 else 0) + (if b = (p.1 + TorusFields.unitStep n p.2.1, p.2.2) then 1 else 0) -
    (if b = (p.1 + TorusFields.unitStep n p.2.2, p.2.1) then 1 else 0) - (if b = (p.1, p.2.2) then 1 else 0)
def gradCoeff (z : TorusFields.TorusSite n) (b : TorusFields.TorusBond n) : ℝ :=
  open Classical in (if z = b.1 then 1 else 0) - (if z = b.1 + TorusFields.unitStep n b.2 then 1 else 0)
abbrev TouchingBond (o : TorusFields.TorusSite n) (R : ℕ) : Type :=
  {b : TorusFields.TorusBond n // b ∈ bondsTouching o R}
def regularizedHessian (a : ℝ) (L k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ) :
    Matrix (TouchingBond o R) (TouchingBond o R) ℝ := fun b b' =>
  TorusFields.mixedDeriv (TorusFields.actionAtLevel a L k (ResponseInTheExpansion.supBall o (2 * R)))
      (TorusFields.trivialField n) ![b.1, b'.1] ![imaginaryUnitI, imaginaryUnitI] +
    ∑ z ∈ ResponseInTheExpansion.supBall o R, gradCoeff z b.1 * gradCoeff z b'.1
open Classical in
def curlCovariance (a : ℝ) (L k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ)
    (p p' : TorusFields.TorusPlaquette n) : ℝ :=
  ∑ b : TouchingBond o R, ∑ b' : TouchingBond o R,
    curlCoeff p b.1 * (regularizedHessian a L k o R)⁻¹ b b' * curlCoeff p' b'.1
def forwardDiff {E : Type} [AddCommGroup E] (i : Fin 4) (F : TorusFields.TorusPlaquette n → E)
    (p : TorusFields.TorusPlaquette n) : E :=
  F (p.1 + TorusFields.unitStep n i, p.2) - F p
def iteratedDiff {E : Type} [AddCommGroup E] (l : List (Fin 4)) (F : TorusFields.TorusPlaquette n → E) :
    TorusFields.TorusPlaquette n → E :=
  l.foldr forwardDiff F
def curlQuadForm (a : ℝ) (L k : ℕ) (o : TorusFields.TorusSite n) (R : ℕ)
    (u : TorusFields.TorusPlaquette n → Fin 3 → ℝ) : ℝ :=
  ∑ e : Fin 3, ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
    ∑ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
      u p e * curlCovariance a L k o R p p' * u p' e
def toUnit (q : ℍ[ℝ]) : BlockAverages.UnitQuaternion :=
  open Classical in if h : q ∈ unitary ℍ[ℝ] then ⟨q, h⟩ else 1
def colourPairing (S : Finset (TorusFields.TorusSite n)) (u : TorusFields.TorusPlaquette n → Fin 3 → ℝ)
    (F : TorusFields.TorusPlaquette n → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ e : Fin 3, ∑ p ∈ TorusFields.plaquettesIn S, u p e * BlockAverages.imaginaryComponent e (F p)
end BoxGaussian
end YangMills.Construction
end
