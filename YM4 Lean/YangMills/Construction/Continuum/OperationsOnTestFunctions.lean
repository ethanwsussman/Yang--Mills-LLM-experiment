import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.ReflectionOfTestFunctionsInAHyperplane
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.TestFunctionOps
open YangMills.Construction.Motions YangMills.Construction.TestSpaces
def motionBound (r : RigidMotion) (n k : ℕ) : ℝ :=
  4 ^ k * (2 * (1 + (n : ℝ) * TorusMetric.euclidNormVec r.shift ^ 2)) ^ ((k : ℝ) / 2)
def complexify {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) : Fin n → (Fin 4 → ℝ) → ℂ :=
  fun i u => (f i u : ℂ)
theorem tensorProd_complexify {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) (x : PointTuple n) :
    tensorProd (complexify f) x = ((tensorProd f x : ℝ) : ℂ) := by
  simp [tensorProd, complexify]
def PreservesClasses (n : ℕ) (σ : Equiv.Perm (Fin n)) (r : RigidMotion)
    (φ : PointTuple n → ℂ) : Prop :=
  permuteArgs σ φ ∈ schwartzSet n ∧
    actOnFun r φ ∈ schwartzSet n ∧
    reflectConj φ ∈ schwartzSet n ∧
    (φ ∈ flatSchwartzSet n →
      permuteArgs σ φ ∈ flatSchwartzSet n ∧
        actOnFun r φ ∈ flatSchwartzSet n ∧
        reflectConj φ ∈ flatSchwartzSet n) ∧
    reflectConj φ = actOnFun RigidMotion.timeReflection fun x => conj (φ x)
def IsLinearOnSchwartz (n : ℕ) (σ : Equiv.Perm (Fin n)) (r : RigidMotion) : Prop :=
  ∀ φ ∈ schwartzSet n, ∀ ψ ∈ schwartzSet n, ∀ a b : ℂ,
    permuteArgs σ (a • φ + b • ψ) =
        a • permuteArgs σ φ + b • permuteArgs σ ψ ∧
      actOnFun r (a • φ + b • ψ) =
        a • actOnFun r φ + b • actOnFun r ψ ∧
      reflectConj (a • φ + b • ψ) = conj a • reflectConj φ + conj b • reflectConj ψ
def SeminormBounds (n k : ℕ) (σ : Equiv.Perm (Fin n)) (r : RigidMotion)
    (φ : PointTuple n → ℂ) : Prop :=
  weightedSeminorm k (permuteArgs σ φ) = weightedSeminorm k φ ∧
    weightedSeminorm k (reflectConj φ) = weightedSeminorm k φ ∧
    weightedSeminorm k (actOnFun r φ) ≤
      ENNReal.ofReal (motionBound r n k) * weightedSeminorm k φ
def ActsOnTensorProd (n : ℕ) (σ : Equiv.Perm (Fin n)) (r : RigidMotion)
    (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  actOnFun r (tensorProd (complexify f)) =
      tensorProd (complexify (actOnTuple r f)) ∧
    permuteArgs σ (tensorProd (complexify f)) =
      tensorProd (complexify fun j => f (σ.symm j)) ∧
    reflectConj (tensorProd (complexify f)) = tensorProd (complexify (reflectTuple f)) ∧
    actOnTuple r f ∈ disjointSupportTuples Set.univ n ∧
    HasSmoothComponents Set.univ (actOnTuple r f) ∧
    (fun j => f (σ.symm j)) ∈ disjointSupportTuples Set.univ n ∧
    HasSmoothComponents Set.univ (fun j => f (σ.symm j)) ∧
    reflectTuple f ∈ disjointSupportTuples Set.univ n ∧
    HasSmoothComponents Set.univ (reflectTuple f)
def ReflectedProduct {p q : ℕ} (X : Fin p → (Fin 4 → ℝ) → ℝ)
    (Y : Fin q → (Fin 4 → ℝ) → ℝ) : Prop :=
  concatTuple (reflectTuple X) Y ∈ disjointSupportTuples Set.univ (p + q) ∧
    HasSmoothComponents Set.univ (concatTuple (reflectTuple X) Y) ∧
    tupleTensor (complexify (concatTuple (reflectTuple X) Y)) =
      HyperplaneReflection.tensorVal (reflectConjVal (tupleTensor (complexify X)))
        (tupleTensor (complexify Y))
def OperationsStatement : Prop :=
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ (σ : Equiv.Perm (Fin n)) (r : RigidMotion),
    IsLinearOnSchwartz n σ r ∧
    (∀ φ ∈ schwartzSet n,
      PreservesClasses n σ r φ ∧ SeminormBounds n k σ r φ ∧
      (VanishesToInfiniteOrderOff φ (positiveTimeLocus n) ↔
        VanishesToInfiniteOrderOff (reflectConj φ) (negativeTimeLocus n))) ∧
    (∀ s : RigidMotion, s.shift = r.shift → motionBound s n k = motionBound r n k) ∧
    (∀ f ∈ disjointSupportTuples Set.univ n, HasSmoothComponents Set.univ f →
      ActsOnTensorProd n σ r f)) ∧
  (∀ (p q : ℕ) (X : Fin p → (Fin 4 → ℝ) → ℝ) (Y : Fin q → (Fin 4 → ℝ) → ℝ),
    X ∈ disjointSupportTuples upperHalfSpace p → HasSmoothComponents upperHalfSpace X →
    Y ∈ disjointSupportTuples upperHalfSpace q → HasSmoothComponents upperHalfSpace Y →
    ReflectedProduct X Y)
end YangMills.Construction.TestFunctionOps
end
