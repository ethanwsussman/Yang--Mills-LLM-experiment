import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open YangMills.Construction.SpectralCalculus
open YangMills.Construction.InfiniteLattice (AmbientSpace)
abbrev halfSpaceDomain (n : AmbientSpace) : Submodule ℂ (AmbientSpace → ℂ) := cc1In (posHalfSpace n)
def reflectedForm (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace)
    (u w : halfSpaceDomain n) : ℂ :=
  complexifyForm S (reflectFun n (conjFun (u : AmbientSpace → ℂ))) w
structure IsSeparatedPair (n : AmbientSpace) (c δ : ℝ) (u₁ u₂ : AmbientSpace → ℂ) : Prop where
  gap_pos : 0 < δ
  left_mem : u₁ ∈ compactC1Complex
  right_mem : u₂ ∈ compactC1Complex
  left_tsupport : tsupport u₁ ⊆ {x | euclidDot n x ≤ c}
  right_tsupport : tsupport u₂ ⊆ {x | c + δ ≤ euclidDot n x}
def slideRange (δ : ℝ) : Set ℝ := {s | -δ < s}
def slideFn (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace)
    (u₁ u₂ : AmbientSpace → ℂ) (s : ℝ) : ℂ :=
  complexifyForm S u₁ (translateFun (s • n) u₂)
structure IsReflectedFormData (σ : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n : AmbientSpace) : Prop where
  isDisjointForm : IsDisjointForm S
  mem_normals : n ∈ reflectionNormals
  admissible : IsAdmissibleForm σ S
abbrev ReflectedSpace (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace) : Type :=
  SeparatedCompletion (reflectedForm S n)
def reflectedClass (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace)
    (u : halfSpaceDomain n) : ReflectedSpace S n :=
  constClass (reflectedForm S n) u
def IsUnitNormalTo (n e : AmbientSpace) : Prop :=
  euclidNorm e = 1 ∧ euclidDot e n = 0
def ActsByTranslation (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n v : AmbientSpace)
    (A : ReflectedSpace S n →L[ℂ] ReflectedSpace S n) : Prop :=
  ∀ u : halfSpaceDomain n, ∃ hu : translateFun v (u : AmbientSpace → ℂ) ∈ halfSpaceDomain n,
    A (reflectedClass S n u) = reflectedClass S n ⟨_, hu⟩
def transferSemigroup (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace)
    (s : ℝ≥0) : ReflectedSpace S n →L[ℂ] ReflectedSpace S n :=
  Classical.epsilon (ActsByTranslation S n ((s : ℝ) • n))
def lateralGroup (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n e : AmbientSpace) (s : ℝ) :
    ReflectedSpace S n →L[ℂ] ReflectedSpace S n :=
  Classical.epsilon (ActsByTranslation S n (s • e))
def IsJointSpectralMeasure (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n e : AmbientSpace)
    (P : ProjValuedMeasure (ReflectedSpace S n)) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ),
    P.IsBoundedSpectralIntegral (spectralCharacter t s)
      (transferSemigroup S n t * lateralGroup S n e s)
open Classical in
theorem nonempty_projValuedMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Nonempty (ProjValuedMeasure H) := by
  let z : SpectralPlane := (0, 0)
  let ν : MeasureTheory.ComplexMeasure SpectralPlane :=
    MeasureTheory.SignedMeasure.toComplexMeasure (MeasureTheory.Measure.dirac z).toSignedMeasure 0
  refine ⟨⟨fun B => if z ∈ B.1 then 1 else 0, fun B => ?_, ?_, fun B B' => ?_, fun u v => ?_⟩⟩
  · split_ifs
    · exact ⟨fun u v => rfl, mul_one _⟩
    · exact ⟨fun u v => by simp, mul_zero _⟩
  · simp
  · by_cases hB : z ∈ B.1 <;> by_cases hB' : z ∈ B'.1 <;> simp [hB, hB']
  · refine ⟨inner ℂ u v • ν, fun B => ?_⟩
    have hν : ν B.1 = if z ∈ B.1 then 1 else 0 := by
      simp only [ν, MeasureTheory.SignedMeasure.toComplexMeasure_apply]
      rw [MeasureTheory.Measure.toSignedMeasure_apply_measurable B.2,
        MeasureTheory.measureReal_def, MeasureTheory.Measure.dirac_apply' z B.2]
      by_cases hB : z ∈ B.1 <;> apply Complex.ext <;> simp [hB]
    simp only [FunLike.coe_smul, Pi.smul_apply, hν]
    by_cases hB : z ∈ B.1 <;> simp [hB]
def jointSpectralMeasure (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n e : AmbientSpace) :
    ProjValuedMeasure (ReflectedSpace S n) :=
  haveI := nonempty_projValuedMeasure (ReflectedSpace S n)
  Classical.epsilon (IsJointSpectralMeasure S n e)
def reflectedHamiltonian (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n e : AmbientSpace) :
    PartialOperator (ReflectedSpace S n) :=
  (jointSpectralMeasure S n e).spectralIntegral coordFst
def reflectedMomentum (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n e : AmbientSpace) :
    PartialOperator (ReflectedSpace S n) :=
  (jointSpectralMeasure S n e).spectralIntegral coordSnd
end TwoPoints
end YangMills.Construction
end
