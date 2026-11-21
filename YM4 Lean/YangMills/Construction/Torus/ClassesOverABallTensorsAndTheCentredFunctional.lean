import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.Torus.OriginBallsProjectionsAndTensorsOfSeveralPoints
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.LatticeFamiliesTranslationsAndCentredFunctionalsOnBalls
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable (s : Conventions.StandingParameters) (E : Ambient)
abbrev ballSepTuples (q : ℕ) (ρ : ℝ≥0∞) : Set (Fin q → Pt s E → ℝ) :=
  sepTuplesIn q (originBall s E ρ)
def ballSepTensors (q : ℕ) (ρ : ℝ≥0∞) : Submodule ℂ (Tuple s E q → ℂ) :=
  (PeriodicSpace.Kind.sepTensorSpanOnBall (paramsOf s) (kindOf E) ρ q).comap
    (LinearMap.funLeft ℂ ℂ fun y i => (ptEquiv s E).symm (y i))
variable {s E}
def IsRealMultilinearOn {q : ℕ} {ρ : ℝ≥0∞} (Ψ : ballSepTuples s E q ρ → ℝ) : Prop :=
  TupleForm.IsMultilinear fun f => ((Ψ f : ℝ) : ℂ)
theorem restrictTuple_mem_sepTuplesIn {q : ℕ} {O : Set (Pt s E)}
    {f : Fin q → Pt s E → ℝ} (hf : f ∈ sepTuplesIn q O) (J : Finset (Fin q)) :
    restrictTuple f J ∈ sepTuplesIn J.card O :=
  ⟨⟨fun _ => hf.1.1 _, fun _ => hf.1.2.1 _,
    fun _ _ hij => hf.1.2.2 _ _ ((J.orderEmbOfFin rfl).injective.ne hij)⟩, fun _ => hf.2 _⟩
variable (s E) in
structure RealMultilinearBallFamily (ρ : ℝ≥0∞) where
  func : (n : ℕ) → 2 ≤ n → ballSepTuples s E n ρ → ℝ
  multilinear : ∀ (n : ℕ) (hn : 2 ≤ n), IsRealMultilinearOn (func n hn)
namespace RealMultilinearBallFamily
variable {ρ : ℝ≥0∞} (Ψ : RealMultilinearBallFamily s E ρ)
def blockFactor {q : ℕ} (f : ballSepTuples s E q ρ) (J : Finset (Fin q)) : ℝ :=
  if h : 2 ≤ J.card then
    Ψ.func J.card h ⟨restrictTuple f.1 J, restrictTuple_mem_sepTuplesIn f.2 J⟩
  else 0
def centredFunc {q : ℕ} (f : ballSepTuples s E q ρ) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts, Ψ.blockFactor f J
end RealMultilinearBallFamily
def ConnectedFamily.centredAt (S : ConnectedFamily s E) {q : ℕ}
    (f : separatedTuples s E q) : ℝ :=
  S.centred (toAllSeparated f)
end YangMills.Construction.AmbientPoints
