import YangMills.Construction.ReflectionPositivity.TranslatesOfPositiveCombinationsAndTheirReflectedProducts
import YangMills.Construction.TotalDensitiesGiveASystem.LawsOfTheTopStatement
import Mathlib
set_option autoImplicit false
open Filter
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ConditionDefaults
open SeparatedTuples ReflectionPositivity.TupleForm LimitTheorem SystemsWithFiveBounds
open InfiniteLattice (AmbientSpace)
open Mirrors (ReflectingHyperplane)
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (spanClass posClass timeBasisVec embedSpatial)
open TorusTransport (hyperoctahedral)
open TestSpaces (SepTupleOfCard)
open TorusMetric (euclidNormVec)
structure ActsWithoutFallback (r : AmbientSpace → AmbientSpace) : Prop where
  right_inv : ∀ y, r (invMap r y) = y
  left_inv : ∀ x, invMap r (r x) = x
  push_eq_pushList : ∀ X : SepTuple, (push r X).1 = pushList r X.1
def PreservesPositiveSpan (r : AmbientSpace → AmbientSpace) : Prop :=
  ∀ F : PositiveSpan, ∃ hG : pushSpan r F.1 ∈ spanIn TimeAxis.upperHalfSpace,
    ∀ (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)),
      spanClass σ h (pushSpan r F.1) = posClass σ h ⟨_, hG⟩
structure ActionsWellDefined : Prop where
  isometry_and_inverse : ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r →
    ActsWithoutFallback r ∧ IsEuclidIsometry (invMap r) ∧ ActsWithoutFallback (invMap r)
  translate_isometry : ∀ v : AmbientSpace, IsEuclidIsometry (translate v)
  hyperoctahedral_isometry : ∀ w : hyperoctahedral, IsEuclidIsometry w.1
  rigidMotion_isometry : ∀ r : Motions.RigidMotion, IsEuclidIsometry r.toFun
  rotation_isometry : ∀ R : Orthogonal.orthogonalGroupFour, IsEuclidIsometry (rotationMap R)
  mirror_isometry : ∀ M : ReflectingHyperplane, IsEuclidIsometry M.reflect
  timeReflection_isometry : IsEuclidIsometry TimeAxis.timeReflection
structure ProductsWellDefined : Prop where
  at_mirror : ∀ (M : ReflectingHyperplane) (X Y : SepTuple), X ∈ supportedIn M.positiveSide →
    Y ∈ supportedIn M.positiveSide →
    SepTuple.Composable (push M.reflect X) Y ∧
      (SepTuple.juxt (push M.reflect X) Y).1 = pushList M.reflect X.1 ++ Y.1
  exists_tuple_at_mirror : ∀ (M : ReflectingHyperplane) (n : ℕ),
    ∃ X ∈ supportedIn M.positiveSide, X.1.length = n ∧ ∀ f ∈ X.1, f ≠ 0
  exists_not_reflectionPositive : ∀ M : ReflectingHyperplane,
    ∃ σ : TupleFunctional, ¬ σ.IsReflectionPositive M
  spanExtension_formalMul : ∀ (σ : TupleFunctional) (G G' : FormalSpan),
    σ.spanExtension (formalMul G G') =
      ∑ Z ∈ G.support, ∑ Y ∈ G'.support, G Z * G' Y * (σ (SepTuple.juxt Z Y) : ℂ)
  reflectConj_support : ∀ F : PositiveSpan, ∀ Z ∈ (reflectConj F).support,
    ∃ X ∈ supportedIn TimeAxis.upperHalfSpace, Z.1 = pushList TimeAxis.timeReflection X.1
  at_form : ∀ F F' : PositiveSpan, ∀ Z ∈ (reflectConj F).support, ∀ Y ∈ F'.1.support,
    SepTuple.Composable Z Y ∧ (SepTuple.juxt Z Y).1 = Z.1 ++ Y.1
  at_matrixElement : ∀ (F F' : PositiveSpan) (t : ℝ≥0) (a : Fin 3 → ℝ),
    ∀ Z ∈ (reflectConj F).support,
      ∀ Y ∈ (pushSpan (translate ((t : ℝ) • timeBasisVec + embedSpatial a)) F'.1).support,
        SepTuple.Composable Z Y ∧ (SepTuple.juxt Z Y).1 = Z.1 ++ Y.1
  exists_form_not_posSemidef : ∃ σ : TupleFunctional, ¬ IsPosSemidef (reflectionForm σ)
  at_cluster : ∀ (X Y : SepTuple) (v : AmbientSpace), SepTuple.Composable X (push (translate v) Y) →
    (SepTuple.juxt X (push (translate v) Y)).1 = X.1 ++ pushList (translate v) Y.1
  exists_far : ∀ ρ : ℝ, ∃ v : AmbientSpace, ρ ≤ euclidNormVec v
structure ClassesWellDefined : Prop where
  timeShift : ∀ t : ℝ≥0, PreservesPositiveSpan (translate ((t : ℝ) • timeBasisVec))
  spatialShift : ∀ a : Fin 3 → ℝ, PreservesPositiveSpan (translate (embedSpatial a))
  timeVecStabilizer : ∀ w : TorusSymmetries.timeVecStabilizer, PreservesPositiveSpan w.1.1
  spatialRotation : ∀ R : Orthogonal.orthogonalGroupThree,
    PreservesPositiveSpan (rotationMap (Orthogonal.embedOrthogonal R))
structure FarProductsWellDefined : Prop where
  shiftedJuxt_eq : ∀ (X : SepTuple) (P : List (SepTuple × AmbientSpace)),
    IsDisjointlySupported (shiftedComponents X P) →
    (shiftedJuxt X P).1 =
      X.1 ++ P.flatMap fun p : SepTuple × AmbientSpace => pushList (SeparatedTuples.translate p.2) p.1.1
  iterLimitValue_eq : ∀ (s : SepTuple → ℝ) (X : SepTuple) (Y : List SepTuple) (vs : List AmbientSpace),
    vs ∈ iterLimitDomain X Y Set.univ 0 →
      ∃ Z : SepTuple, Z.1 = X.1 ++ (Y.zip vs).flatMap
          (fun p : SepTuple × AmbientSpace => pushList (SeparatedTuples.translate p.2) p.1.1) ∧
        iterLimitValue s X Y Set.univ 0 vs = s Z
  eventually_mem_domain : ∀ (X : SepTuple) (Y : List SepTuple) (k : ℕ), k < Y.length →
    ∀ vs ∈ iterLimitDomain X Y Set.univ (k + 1),
    ∀ᶠ v in atInfinityWithin Set.univ, v :: vs ∈ iterLimitDomain X Y Set.univ k
  neBot : (atInfinityWithin (Set.univ : Set AmbientSpace)).NeBot
  domain_last : ∀ (X : SepTuple) (Y : List SepTuple), iterLimitDomain X Y Set.univ Y.length = {[]}
structure PremisesSatisfiable : Prop where
  exists_linear_combination : ∀ (A B : List RealValued) (f f' : RealValued) (α α' : ℝ) (X X' : SepTuple),
    X.1 = A ++ f :: B → X'.1 = A ++ f' :: B → ∃ Z : SepTuple, Z.1 = A ++ (α • f + α' • f') :: B
  exists_slot_combination : ∀ (n : ℕ) (i : Fin n) (b b' : ℝ) (X X' : SepTupleOfCard n),
    (∀ j, j ≠ i → X.1 j = X'.1 j) →
      ∃ X'' : SepTupleOfCard n, X''.1 i = b • X.1 i + b' • X'.1 i ∧ ∀ j, j ≠ i → X''.1 j = X.1 j
  exists_permuted : ∀ (n : ℕ) (X : SepTupleOfCard n) (ς : Equiv.Perm (Fin n)),
    ∃ Y : SepTupleOfCard n, Y.1 = fun i => X.1 (ς i)
  exists_dilates : ∀ (n : ℕ) (X : SepTupleOfCard n),
    ∃ Y : ℕ → SepTupleOfCard n, ∀ i, (Y i).1 = TotalDensities.dyadicRescale i X.1
  exists_nonzero_smooth : ∀ m : ℕ, ∃ φ : TestSpaces.PointTuple (m + 1) → ℂ,
    φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) ∧ φ ≠ 0
  exists_nonzero_testFn : ∀ m : ℕ, ∃ φ : TestFn (offDiagonal (m + 1)), φ.1 ≠ 0
  posSemidef_of_reconstruction : ∀ σ : TupleFunctional, ReconstructionConditions σ →
    IsPosSemidef (reflectionForm σ)
def NonvacuityStatement : Prop :=
  ActionsWellDefined ∧ ProductsWellDefined ∧ ClassesWellDefined ∧ FarProductsWellDefined ∧
    PremisesSatisfiable ∧ PositiveTranslates.Statement
end YangMills.Construction.ConditionDefaults
end
