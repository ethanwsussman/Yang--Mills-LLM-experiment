import YangMills.Construction.Continuum.ReflectionOfTestFunctionsInAHyperplane
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.MotionsTranslations
def translateOfOrder (v : Fin 4 → ℝ) {n : ℕ} (φ : Motions.TensorVal ℂ n) : Motions.TensorVal ℂ n :=
  WightmanReconstruction.actOfOrder (UpperHalfTensors.translateMotion v) φ
section Affine
variable {n : ℕ}
abbrev CoordIdx (n : ℕ) : Type := Fin n × Fin 4
abbrev CoordMatrix (n : ℕ) : Type := Matrix (CoordIdx n) (CoordIdx n) ℝ
def affineApply (M : CoordMatrix n) (w x : TestSpaces.PointTuple n) : TestSpaces.PointTuple n :=
  fun i μ => (∑ c : CoordIdx n, M (i, μ) c * x c.1 c.2) + w i μ
def affineComp (M : CoordMatrix n) (w : TestSpaces.PointTuple n)
    (f : TestSpaces.PointTuple n → ℂ) : TestSpaces.PointTuple n → ℂ :=
  fun x => f (affineApply M w x)
def invFrobeniusNorm (M : CoordMatrix n) : ℝ :=
  Real.sqrt (∑ a, ∑ b, M⁻¹ a b ^ 2)
def affineWeightConst (M : CoordMatrix n) (w : TestSpaces.PointTuple n) : ℝ :=
  1 + 2 * invFrobeniusNorm M ^ 2 * (1 + TestSpaces.tupleNorm w ^ 2)
def EntryBound (M : CoordMatrix n) (c : ℝ) : Prop :=
  1 ≤ c ∧ ∀ a b, |M a b| ≤ c
def DerivExpansion (M : CoordMatrix n) (w : TestSpaces.PointTuple n)
    (φ : TestSpaces.PointTuple n → ℂ) (p : ℕ) (α : TestSpaces.MultiIdx4 n) : Prop :=
  ∃ (entries : Fin ((4 * n) ^ p) → Fin p → CoordIdx n × CoordIdx n)
    (γ : Fin ((4 * n) ^ p) → TestSpaces.MultiIdx4 n),
    (∀ t, TestSpaces.idxOrder (γ t) = p) ∧
      ∀ x, TestSpaces.multiDeriv α (affineComp M w φ) x =
        ∑ t, ((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
          affineComp M w (TestSpaces.multiDeriv (γ t) φ) x
end Affine
def MotionTensorProd : Prop :=
  ∀ (q q' : ℕ) (r : Motions.RigidMotion) (φ : Motions.TensorVal ℂ q) (ψ : Motions.TensorVal ℂ q'),
    φ ∈ WightmanReconstruction.schwartzOfOrder q → ψ ∈ WightmanReconstruction.schwartzOfOrder q' →
      WightmanReconstruction.actOfOrder r (HyperplaneReflection.tensorVal φ ψ) =
        HyperplaneReflection.tensorVal (WightmanReconstruction.actOfOrder r φ)
          (WightmanReconstruction.actOfOrder r ψ)
def TranslatePreservesPlus : Prop :=
  ∀ n : ℕ, 0 < n → ∀ φ ∈ WightmanReconstruction.schwartzPlus n, ∀ v : Fin 4 → ℝ, 0 ≤ v 3 →
    Motions.actOnFun (UpperHalfTensors.translateMotion v) φ ∈ WightmanReconstruction.schwartzPlus n
def ReflectTranslate : Prop :=
  ∀ (q : ℕ) (φ : Motions.TensorVal ℂ q), φ ∈ WightmanReconstruction.schwartzOfOrder q →
    (∀ v : Fin 4 → ℝ, Motions.reflectConjVal (translateOfOrder v φ) =
      translateOfOrder (TestSpaces.timeReflect v) (Motions.reflectConjVal φ)) ∧
    (∀ t : ℝ, Motions.reflectConjVal (translateOfOrder (t • PeriodicLattice.coordVec 3) φ) =
      translateOfOrder ((-t) • PeriodicLattice.coordVec 3) (Motions.reflectConjVal φ)) ∧
    ∀ v ∈ EuclideanFunctionals.spatialVecs,
      Motions.reflectConjVal (translateOfOrder v φ) = translateOfOrder v (Motions.reflectConjVal φ)
def AffineCompBounds : Prop :=
  ∀ n : ℕ, 0 < n → ∀ φ ∈ TestSpaces.schwartzSet n,
    ∀ (M : CoordMatrix n) (w : TestSpaces.PointTuple n) (c : ℝ),
    IsUnit M → EntryBound M c →
      (∀ x : TestSpaces.PointTuple n, 1 + TestSpaces.tupleNorm x ^ 2 ≤
        affineWeightConst M w * (1 + TestSpaces.tupleNorm (affineApply M w x) ^ 2)) ∧
      affineComp M w φ ∈ TestSpaces.schwartzSet n ∧
      (∀ (p : ℕ) (α : TestSpaces.MultiIdx4 n), TestSpaces.idxOrder α = p → DerivExpansion M w φ p α) ∧
      ∀ k : ℕ, 0 < k → TestSpaces.weightedSeminorm k (affineComp M w φ) ≤
        ENNReal.ofReal ((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
          TestSpaces.weightedSeminorm k φ
def DerivSchwartzBounds : Prop :=
  ∀ n : ℕ, 0 < n → ∀ φ ∈ TestSpaces.schwartzSet n, ∀ β : TestSpaces.MultiIdx4 n,
    TestSpaces.multiDeriv β φ ∈ TestSpaces.schwartzSet n ∧
      ∀ k : ℕ, 0 < k → TestSpaces.weightedSeminorm k (TestSpaces.multiDeriv β φ) ≤
        TestSpaces.weightedSeminorm (k + TestSpaces.idxOrder β) φ
def Statement : Prop :=
  MotionTensorProd ∧ TranslatePreservesPlus ∧ ReflectTranslate ∧
    AffineCompBounds ∧ DerivSchwartzBounds
end YangMills.Construction.MotionsTranslations
end
