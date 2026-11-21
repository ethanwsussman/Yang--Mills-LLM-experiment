import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def IsDisjointSupportPair (f h : AmbientSpace → ℂ) : Prop :=
  f ∈ compactC1Complex ∧ h ∈ compactC1Complex ∧ DisjointSupports f h
def ReflectionsLieInSymmetryGroups : Prop :=
  ∀ n ∈ reflectionNormals, (∃ w ∈ hyperoctahedralPerms, ⇑w = reflectAcross n) ∧
    (n ∈ planeReflectionNormals → ∃ w ∈ dihedralInPlane, ⇑w = reflectAcross n)
def IsIsometricInvolutiveReflection (n : AmbientSpace) : Prop :=
  (∃ l : AmbientSpace →ₗ[ℝ] AmbientSpace, ⇑l = reflectAcross n ∧
      ∀ x, euclidNorm (l x) = euclidNorm x) ∧
    reflectAcross n ∘ reflectAcross n = id ∧
    (∀ x, euclidDot n (reflectAcross n x) = -euclidDot n x) ∧
    ∀ (E : Type) (f : AmbientSpace → E) (v : AmbientSpace) (s : ℝ),
      reflectFun n (translateFun v f) = translateFun (reflectAcross n v) (reflectFun n f) ∧
      reflectFun n (translateFun (s • n) f) = translateFun ((-s) • n) (reflectFun n f) ∧
      (euclidDot v n = 0 → reflectFun n (translateFun v f) = translateFun v (reflectFun n f))
structure PreservesNormsAndBallSupport (sc : FixedScale) (f g : AmbientSpace → ℂ) : Prop where
  mem : g ∈ compactC1Complex
  uniformNorm_eq :
    YangMills.Construction.TestFunctions.uniformNorm g =
      YangMills.Construction.TestFunctions.uniformNorm f
  lipConst_eq :
    YangMills.Construction.TestFunctions.lipConstR4 g =
      YangMills.Construction.TestFunctions.lipConstR4 f
  sharpNorm_eq : sc.sharpNorm g = sc.sharpNorm f
  ballSupport : ∀ (c : AmbientSpace) (R : ℝ), 0 < R → tsupport f ⊆ euclidClosedBall c R →
    ∃ c' : AmbientSpace, tsupport g ⊆ euclidClosedBall c' R
def SymmetriesPreserve (sc : FixedScale) (f : AmbientSpace → ℂ) : Prop :=
  (∀ v : AmbientSpace, PreservesNormsAndBallSupport sc f (translateFun v f) ∧
      lebesgueIntegral (translateFun v f) = lebesgueIntegral f ∧
      tsupport (translateFun v f) = minkowskiSum (tsupport f) {v}) ∧
    (∀ n : AmbientSpace, euclidNorm n = 1 → PreservesNormsAndBallSupport sc f (reflectFun n f) ∧
      lebesgueIntegral (reflectFun n f) = lebesgueIntegral f ∧
      tsupport (reflectFun n f) = reflectAcross n '' tsupport f) ∧
    (∀ w ∈ hyperoctahedralPerms, PreservesNormsAndBallSupport sc f (actOn w f) ∧
      lebesgueIntegral (actOn w f) = lebesgueIntegral f ∧
      tsupport (actOn w f) = ⇑w '' tsupport f) ∧
    PreservesNormsAndBallSupport sc f (conjFun f) ∧
      lebesgueIntegral (conjFun f) = (starRingEnd ℂ) (lebesgueIntegral f) ∧
      tsupport (conjFun f) = tsupport f
def ReImPartsControlled (sc : FixedScale) : Prop :=
  ∀ u v : AmbientSpace → ℂ, (∀ x, (u x).im = 0) → (∀ x, (v x).im = 0) →
    u + Complex.I • v ∈ compactC1Complex →
      u ∈ compactC1Real ∧ v ∈ compactC1Real ∧
        tsupport u ⊆ tsupport (u + Complex.I • v) ∧
        tsupport v ⊆ tsupport (u + Complex.I • v) ∧
        sc.sharpNorm u ≤ sc.sharpNorm (u + Complex.I • v) ∧
        sc.sharpNorm v ≤ sc.sharpNorm (u + Complex.I • v)
def ComplexifyDefinedAt (f h : AmbientSpace → ℂ) : Prop :=
  realPartFun f ∈ compactC1Real ∧ imagPartFun f ∈ compactC1Real ∧
    realPartFun h ∈ compactC1Real ∧ imagPartFun h ∈ compactC1Real ∧
    DisjointSupports (realPartFun f) (realPartFun h) ∧
    DisjointSupports (imagPartFun f) (imagPartFun h) ∧
    DisjointSupports (realPartFun f) (imagPartFun h) ∧
    DisjointSupports (imagPartFun f) (realPartFun h)
def ComplexifyDefinedSymm (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∀ f h : AmbientSpace → ℂ, IsDisjointSupportPair f h →
    ComplexifyDefinedAt f h ∧ complexifyForm S f h = complexifyForm S h f
def ComplexifyLinear (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∀ (a b : ℂ) (f g h : AmbientSpace → ℂ), IsDisjointSupportPair f h →
    IsDisjointSupportPair g h →
      IsDisjointSupportPair (a • f + b • g) h ∧
      complexifyForm S (a • f + b • g) h =
        a * complexifyForm S f h + b * complexifyForm S g h ∧
      complexifyForm S h (a • f + b • g) =
        a * complexifyForm S h f + b * complexifyForm S h g
def ComplexifyInvariant (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∀ r ∈ euclideanMotions, ∀ f h : AmbientSpace → ℂ, IsDisjointSupportPair f h →
    IsDisjointSupportPair (actOn r f) (actOn r h) ∧
      complexifyForm S (actOn r f) (actOn r h) = complexifyForm S f h
def ComplexifyConjCommute (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∀ f h : AmbientSpace → ℂ, IsDisjointSupportPair f h →
    IsDisjointSupportPair (conjFun f) (conjFun h) ∧
      complexifyForm S (conjFun f) (conjFun h) = (starRingEnd ℂ) (complexifyForm S f h)
def ComplexifyBallBound (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ d R : ℝ, 0 < d → 0 < R → ∀ c c' : AmbientSpace, ∀ f ∈ compactC1Complex,
    ∀ h ∈ compactC1Complex,
    tsupport f ⊆ euclidClosedBall c R → tsupport h ⊆ euclidClosedBall c' R →
      SeparatedBy d (tsupport f) (tsupport h) →
        ‖complexifyForm S f h‖ ≤ 4 * C d R * sc.sharpNorm f * sc.sharpNorm h
def IsReflectionPositive (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∀ n ∈ reflectionNormals, ∀ f ∈ cc1In (posHalfSpace n),
    IsDisjointSupportPair (reflectFun n (conjFun f)) f ∧
      IsRealNonneg (complexifyForm S (reflectFun n (conjFun f)) f)
def AdmissibleFormConsequences.Statement : Prop :=
  ReflectionsLieInSymmetryGroups ∧
    (∀ n : AmbientSpace, euclidNorm n = 1 → IsIsometricInvolutiveReflection n) ∧
    (∀ f ∈ compactC1Complex,
      YangMills.Construction.TestFunctions.IsBoundedFun f ∧
        YangMills.Construction.TestFunctions.IsLipschitzFor
          YangMills.Construction.TestFunctions.euclidDistR4 f) ∧
    (∀ sc : FixedScale, (∀ f ∈ compactC1Complex, SymmetriesPreserve sc f) ∧
      ReImPartsControlled sc) ∧
    ∀ (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (C : ℝ → ℝ → ℝ),
      IsDisjointForm S → IsAdmissibleForm sc S → IsBallDecayBound sc S C →
        (ComplexifyDefinedSymm S ∧ ComplexifyLinear S ∧
          ComplexifyInvariant S ∧ ComplexifyConjCommute S ∧
          ComplexifyBallBound sc S C) ∧
        IsReflectionPositive S
end YangMills.Construction.TwoPoints
end
