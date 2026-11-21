import YangMills.Construction.EuclideanFunctionals.ElementOfTheOrthogonalGroupAsAnIsometry
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open RealPlane
namespace OrthogonalInvariance
def FunctionAction : Prop :=
  ∀ (A B : Matrix.orthogonalGroup (Fin 4) ℝ) (f : R4 → ℂ), f ∈ C1c ℂ →
    (EuclidMotion.ofOrthogonalMatrix A).actFn f ∈ C1c ℂ ∧
    (∀ (a b : ℂ) (g : R4 → ℂ), g ∈ C1c ℂ →
      (EuclidMotion.ofOrthogonalMatrix A).actFn (a • f + b • g) =
        a • (EuclidMotion.ofOrthogonalMatrix A).actFn f + b • (EuclidMotion.ofOrthogonalMatrix A).actFn g) ∧
    (EuclidMotion.ofOrthogonalMatrix A).actFn (fun x => conj (f x)) =
      (fun x => conj ((EuclidMotion.ofOrthogonalMatrix A).actFn f x)) ∧
    (IsRealValued f → IsRealValued ((EuclidMotion.ofOrthogonalMatrix A).actFn f)) ∧
    (∀ u v : R4 → ℝ, u ∈ C1c ℝ → v ∈ C1c ℝ →
      (EuclidMotion.ofOrthogonalMatrix A).actFn (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) =
        fun x => (((EuclidMotion.ofOrthogonalMatrix A).actFn u x : ℝ) : ℂ) +
          Complex.I * (((EuclidMotion.ofOrthogonalMatrix A).actFn v x : ℝ) : ℂ)) ∧
    (EuclidMotion.ofOrthogonalMatrix A).actFn ((EuclidMotion.ofOrthogonalMatrix B).actFn f) =
      (EuclidMotion.ofOrthogonalMatrix (A * B)).actFn f
def SupportBallDistanceTuple : Prop :=
  ∀ A : Matrix.orthogonalGroup (Fin 4) ℝ,
    (∀ f : R4 → ℂ, f ∈ C1c ℂ →
      supp ((EuclidMotion.ofOrthogonalMatrix A).actFn f) = EuclidMotion.ofOrthogonalMatrix A '' supp f) ∧
    (∀ (x : R4) (r : ℝ), 0 < r →
      EuclidMotion.ofOrthogonalMatrix A '' EuclideanBalls.euclidBall x r =
        EuclideanBalls.euclidBall (EuclidMotion.ofOrthogonalMatrix A x) r) ∧
    (∀ S T : Set R4, S.Nonempty → T.Nonempty →
      TestFunctions.setDistR4 (EuclidMotion.ofOrthogonalMatrix A '' S) (EuclidMotion.ofOrthogonalMatrix A '' T) =
        TestFunctions.setDistR4 S T) ∧
    ∀ n : ℕ,
      (fun (h : Fin n → R4 → ℂ) i => (EuclidMotion.ofOrthogonalMatrix A).actFn (h i)) ''
          disjointComplexTuples n = disjointComplexTuples n ∧
      (EuclidMotion.ofOrthogonalMatrix A).actList '' sepN n = sepN n
def NormInvariance : Prop :=
  ∀ (c : SharpScale) (A : Matrix.orthogonalGroup (Fin 4) ℝ) (f : R4 → ℂ),
    f ∈ C1c ℂ →
    TestFunctions.uniformNorm ((EuclidMotion.ofOrthogonalMatrix A).actFn f) = TestFunctions.uniformNorm f ∧
    TestFunctions.lipConstR4 ((EuclidMotion.ofOrthogonalMatrix A).actFn f) = TestFunctions.lipConstR4 f ∧
    c.sharpNorm ((EuclidMotion.ofOrthogonalMatrix A).actFn f) = c.sharpNorm f
def TranslationCompat : Prop :=
  ∀ (A : Matrix.orthogonalGroup (Fin 4) ℝ) (f : R4 → ℂ) (u : R4),
    f ∈ C1c ℂ →
    (EuclidMotion.ofOrthogonalMatrix A).actFn ((EuclidMotion.transl u).actFn f) =
      (EuclidMotion.transl (EuclidMotion.ofOrthogonalMatrix A u)).actFn
        ((EuclidMotion.ofOrthogonalMatrix A).actFn f)
def RotationRules : Prop :=
  ∀ t : ℝ,
    LinearMap.toMatrix' (rotateLin t) ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ∧
    (rotateMotion t)⁻¹ = rotateMotion (-t) ∧
    (∀ x : R4, rotateMotion t x 1 = x 1 ∧ rotateMotion t x 2 = x 2) ∧
    rotateMotion t timeVec = Real.cos t • timeVec + Real.sin t • PeriodicLattice.coordVec 0 ∧
    rotateMotion t (PeriodicLattice.coordVec 0) =
      (-Real.sin t) • timeVec + Real.cos t • PeriodicLattice.coordVec 0
def PlateRotation : Prop :=
  ∀ (t : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ), α ∈ RealPlane.complexProfiles →
    φ ∈ RealPlane.realLabels →
    (rotateMotion t).actFn (RealPlane.productFunction α φ) =
      RealPlane.productFunction (α ∘ RealPlane.rotate (-t)) φ ∧
    α ∘ RealPlane.rotate (-t) ∈ RealPlane.complexProfiles ∧
    tsupport (α ∘ RealPlane.rotate (-t)) = RealPlane.rotate t '' tsupport α
def tuplesWithZeroComponent (n : ℕ) : Submodule ℂ FreeSep :=
  Submodule.span ℂ (toFree '' {Z | Z ∈ sepN n ∧ ∃ g ∈ Z, g = 0})
def ComplexTupleImages : Prop :=
  ∀ (A : Matrix.orthogonalGroup (Fin 4) ℝ) (u : R4) (n : ℕ) (h : Fin n → R4 → ℂ),
    h ∈ disjointComplexTuples n →
    (fun i => (EuclidMotion.ofOrthogonalMatrix A).actFn (h i)) ∈ disjointComplexTuples n ∧
    (EuclidMotion.ofOrthogonalMatrix A).actFree (complexTuple h) =
      complexTuple (fun i => (EuclidMotion.ofOrthogonalMatrix A).actFn (h i)) ∧
    (fun i => (EuclidMotion.transl u).actFn (h i)) ∈ disjointComplexTuples n ∧
    (EuclidMotion.transl u).actFree (complexTuple h) =
      complexTuple (fun i => (EuclidMotion.transl u).actFn (h i))
def ComplexTupleMul : Prop :=
  ∀ (n m : ℕ) (h : Fin n → R4 → ℂ) (g : Fin m → R4 → ℂ),
    h ∈ disjointComplexTuples n → g ∈ disjointComplexTuples m →
    (∀ i j, Disjoint (supp (h i)) (supp (g j))) →
    MulDefined (complexTuple h) (complexTuple g) ∧
    Fin.append h g ∈ disjointComplexTuples (n + m) ∧
    (((∀ i, IsRealValued (h i)) ∧ ∀ j, IsRealValued (g j)) ∨
        ((∃ i, ¬IsRealValued (h i)) ∧ ∃ j, ¬IsRealValued (g j)) ∨ n = 0 ∨ m = 0 →
      freeMul (complexTuple h) (complexTuple g) = complexTuple (Fin.append h g)) ∧
    freeMul (complexTuple h) (complexTuple g) -
        complexTuple (Fin.append h g) ∈ tuplesWithZeroComponent (n + m)
def FreeAction : Prop :=
  ∀ (A B : Matrix.orthogonalGroup (Fin 4) ℝ) (u : R4) (F G : FreeSep),
    (EuclidMotion.ofOrthogonalMatrix A).actFree ((EuclidMotion.ofOrthogonalMatrix B).actFree F) =
      (EuclidMotion.ofOrthogonalMatrix (A * B)).actFree F ∧
    freeConj ((EuclidMotion.ofOrthogonalMatrix A).actFree F) =
      (EuclidMotion.ofOrthogonalMatrix A).actFree (freeConj F) ∧
    freeConj ((EuclidMotion.transl u).actFree F) = (EuclidMotion.transl u).actFree (freeConj F) ∧
    (EuclidMotion.ofOrthogonalMatrix A).actFree ((EuclidMotion.transl u).actFree F) =
      (EuclidMotion.transl (EuclidMotion.ofOrthogonalMatrix A u)).actFree
        ((EuclidMotion.ofOrthogonalMatrix A).actFree F) ∧
    (MulDefined F G →
      MulDefined ((EuclidMotion.ofOrthogonalMatrix A).actFree F)
        ((EuclidMotion.ofOrthogonalMatrix A).actFree G) ∧
      MulDefined ((EuclidMotion.transl u).actFree F) ((EuclidMotion.transl u).actFree G) ∧
      (EuclidMotion.ofOrthogonalMatrix A).actFree (freeMul F G) =
        freeMul ((EuclidMotion.ofOrthogonalMatrix A).actFree F)
          ((EuclidMotion.ofOrthogonalMatrix A).actFree G) ∧
      (EuclidMotion.transl u).actFree (freeMul F G) =
        freeMul ((EuclidMotion.transl u).actFree F) ((EuclidMotion.transl u).actFree G))
def GradientTransform : Prop :=
  ∀ (A : Matrix.orthogonalGroup (Fin 4) ℝ) (f : R4 → ℂ) (x : R4) (μ : Fin 4),
    f ∈ C1c ℂ →
    TestFunctions.partialDerivR4 μ ((EuclidMotion.ofOrthogonalMatrix A).actFn f) x =
      ∑ ν, (A.1 μ ν : ℂ) * TestFunctions.partialDerivR4 ν f ((EuclidMotion.ofOrthogonalMatrix A)⁻¹ x)
def ContinuousAtOne : Prop :=
  ∀ (c : SharpScale) (f : R4 → ℂ), f ∈ C1c ℂ →
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : Matrix.orthogonalGroup (Fin 4) ℝ,
      EuclideanBalls.opNormEuclid (A.1 - 1) ≤ η →
        c.sharpNorm ((EuclidMotion.ofOrthogonalMatrix A).actFn f - f) ≤ ε
def Holds : Prop :=
  FunctionAction ∧ SupportBallDistanceTuple ∧ NormInvariance ∧ TranslationCompat ∧
    RotationRules ∧ PlateRotation ∧ ComplexTupleImages ∧
    ComplexTupleMul ∧ FreeAction ∧ GradientTransform ∧ ContinuousAtOne
end OrthogonalInvariance
end YangMills.Construction.EuclideanFunctionals
