import YangMills.Construction.Continuum.OrthogonalBlockEmbedding
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace YangMills.Construction.OrthogonalAction
open Orthogonal SeparatedTuples
open InfiniteLattice (AmbientSpace)
open TimeAxis (upperHalfSpace timeComponent timeIdx)
open TorusLifts (hyperoctahedralGroupEuclidean)
def matMap (Q : orthogonalGroupFour) : AmbientSpace → AmbientSpace := fun x => Q.1 *ᵥ x
abbrev unitTime : AmbientSpace := PeriodicLattice.coordVec timeIdx
def gradR4 (f : RealValued) (x : AmbientSpace) : AmbientSpace :=
  fun μ => TestFunctions.partialDerivR4 μ f x
def timeStabilizer : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {w | w ∈ hyperoctahedralGroupEuclidean ∧ w unitTime = unitTime}
  mul_mem' := by
    rintro w w' ⟨hw, fw⟩ ⟨hw', fw'⟩
    exact ⟨mul_mem hw hw', by rw [Equiv.Perm.mul_apply, fw', fw]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := by
    rintro w ⟨hw, fw⟩
    exact ⟨inv_mem hw, by rw [Equiv.Perm.inv_eq_iff_eq, fw]⟩
def IsEmbeddingOf (w : Equiv.Perm AmbientSpace) (R : orthogonalGroupThree) : Prop :=
  ⇑w = matMap (embedOrthogonal R)
def spatialPart (w : Equiv.Perm AmbientSpace) : orthogonalGroupThree :=
  Classical.epsilon (IsEmbeddingOf w)
def ActionLaws (Q Q' : orthogonalGroupFour) : Prop :=
  (∀ f : RealValued, IsC1c f →
    IsC1c (orthogonalAct Q f) ∧
    orthogonalAct Q (orthogonalAct Q' f) = orthogonalAct (Q * Q') f ∧
    tsupport (orthogonalAct Q f) = matMap Q '' tsupport f ∧
    (∀ M : ℝ, 1 ≤ M →
      TestFunctions.sharpNormR4 M (orthogonalAct Q f) = TestFunctions.sharpNormR4 M f) ∧
    (∫ x, orthogonalAct Q f x) = ∫ x, f x ∧
    ∀ x, gradR4 (orthogonalAct Q f) x =
      Q.1 *ᵥ gradR4 f ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x)) ∧
  Function.Bijective (push (matMap Q)) ∧
  (∀ X : SepTuple, (push (matMap Q) X).size = X.size) ∧
  (∀ X : SepTuple, push (matMap Q) (push (matMap Q') X) = push (matMap (Q * Q')) X) ∧
  (∀ (X : SepTuple) (I : Finset ℕ), I ⊆ Finset.Icc 1 X.size →
    (push (matMap Q) X).subtuple I = push (matMap Q) (X.subtuple I)) ∧
  ∀ X Y : SepTuple, SepTuple.Composable X Y →
    SepTuple.Composable (push (matMap Q) X) (push (matMap Q) Y) ∧
    push (matMap Q) (SepTuple.juxt X Y) = SepTuple.juxt (push (matMap Q) X) (push (matMap Q) Y)
def EmbeddingLaws (R R' : orthogonalGroupThree) : Prop :=
  (∀ x : AmbientSpace, timeComponent (matMap (embedOrthogonal R) x) = timeComponent x) ∧
  (∀ x : AmbientSpace, matMap (embedOrthogonal R) (TimeAxis.timeReflection x) =
    TimeAxis.timeReflection (matMap (embedOrthogonal R) x)) ∧
  matMap (embedOrthogonal R) unitTime = unitTime ∧
  (∀ v : Fin 3 → ℝ, matMap (embedOrthogonal R) (spacetimePoint v 0) = spacetimePoint (R.1 *ᵥ v) 0) ∧
  embedOrthogonal (R * R') = embedOrthogonal R * embedOrthogonal R' ∧
  embedOrthogonal 1 = 1 ∧
  matrixOperatorNorm ((embedOrthogonal R).1 - 1) = matrixOperatorNorm (R.1 - 1) ∧
  matMap (embedOrthogonal R) '' upperHalfSpace = upperHalfSpace ∧
  matMap (embedOrthogonal R) '' {x | timeComponent x < 0} = {x | timeComponent x < 0}
def UpperHalfSpaceLaws (R : orthogonalGroupThree) : Prop :=
  (∀ X ∈ supportedIn upperHalfSpace, ∀ Y ∈ supportedIn upperHalfSpace,
    SepTuple.Composable (push TimeAxis.timeReflection X) Y) ∧
  (∀ X ∈ supportedIn upperHalfSpace,
    (∀ t : ℝ, 0 ≤ t → push (translate (t • unitTime)) X ∈ supportedIn upperHalfSpace) ∧
    ∀ v : Fin 3 → ℝ, push (translate (spacetimePoint v 0)) X ∈ supportedIn upperHalfSpace) ∧
  Set.BijOn (pushSpan (matMap (embedOrthogonal R)))
    (spanIn upperHalfSpace : Set FormalSpan)
    (spanIn upperHalfSpace : Set FormalSpan) ∧
  Set.InvOn (pushSpan (matMap (embedOrthogonal R⁻¹))) (pushSpan (matMap (embedOrthogonal R)))
    (spanIn upperHalfSpace : Set FormalSpan)
    (spanIn upperHalfSpace : Set FormalSpan) ∧
  pushSpan (matMap (embedOrthogonal R)) (basisVec SepTuple.nil) = basisVec SepTuple.nil ∧
  ∀ F ∈ spanIn upperHalfSpace, ∀ F' ∈ spanIn upperHalfSpace,
    formalMul
        (pushSpan TimeAxis.timeReflection (conjugation (pushSpan (matMap (embedOrthogonal R)) F)))
        (pushSpan (matMap (embedOrthogonal R)) F') =
      pushSpan (matMap (embedOrthogonal R))
        (formalMul (pushSpan TimeAxis.timeReflection (conjugation F)) F') ∧
    (∀ t : ℝ, 0 ≤ t →
      pushSpan (matMap (embedOrthogonal R)) (pushSpan (translate (t • unitTime)) F) =
        pushSpan (translate (t • unitTime)) (pushSpan (matMap (embedOrthogonal R)) F)) ∧
    ∀ v : Fin 3 → ℝ,
      pushSpan (matMap (embedOrthogonal R)) (pushSpan (translate (spacetimePoint v 0)) F) =
        pushSpan (translate (spacetimePoint (R.1 *ᵥ v) 0))
          (pushSpan (matMap (embedOrthogonal R)) F)
def StabilizerLaws : Prop :=
  (∀ w ∈ timeStabilizer,
    IsEmbeddingOf w (spatialPart w) ∧
    (∀ R : orthogonalGroupThree, IsEmbeddingOf w R → R = spatialPart w) ∧
    (∀ i, ∃! j, (spatialPart w).1 i j ≠ 0) ∧ (∀ j, ∃! i, (spatialPart w).1 i j ≠ 0) ∧
    ∀ i j, (spatialPart w).1 i j ≠ 0 →
      (spatialPart w).1 i j = 1 ∨ (spatialPart w).1 i j = -1) ∧
  (∀ w ∈ timeStabilizer, ∀ w' ∈ timeStabilizer,
    spatialPart (w * w') = spatialPart w * spatialPart w') ∧
  Set.InjOn spatialPart (timeStabilizer : Set (Equiv.Perm AmbientSpace))
def Laws.Statement : Prop :=
  (∀ Q Q' : orthogonalGroupFour, ActionLaws Q Q') ∧
  (∀ R R' : orthogonalGroupThree, EmbeddingLaws R R') ∧
  (∀ R : orthogonalGroupThree, UpperHalfSpaceLaws R) ∧
  StabilizerLaws
end YangMills.Construction.OrthogonalAction
