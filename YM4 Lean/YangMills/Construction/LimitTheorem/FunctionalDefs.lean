import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.Continuum.OrthogonalBlockEmbedding
import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import YangMills.Construction.ReflectionPositivity.ReconstructionOfTheLimitOfALatticeApproximation
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped ComplexOrder InnerProductSpace NNReal Topology
noncomputable section
namespace YangMills.Construction
namespace LimitTheorem
open TestSpaces (SepTupleOfCard flatSchwartzSet)
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass vacuum
  timeShift spaceShift embedSpatial)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open TorusTransport (hyperoctahedral)
open InfiniteLattice (AmbientSpace)
def evalOnMap (σ : TupleFunctional) (X : TestSpaces.SepTuple) : ℝ :=
  σ (TupleLists.toList X)
def connectedFn (σ : TupleFunctional) {n : ℕ} (X : SepTupleOfCard n) : ℝ :=
  TestSpaces.cumulant (evalOnMap σ) X
abbrev CumulantFamily : Type := (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ
def centredOf (S : CumulantFamily) : TupleFunctional where
  toFun X := TestSpaces.centredOfCumulants S (TupleLists.ofList X)
  map_nil := by
    have hnil : TupleLists.ofList SepTuple.nil = TestSpaces.sepTupleNil := by
      rw [← TupleLists.toList_sepTupleNil, TupleLists.ofList_toList]
    rw [hnil]
    exact TestSpaces.centredOfCumulants_nil S
def HasCumulants (σ : TupleFunctional) (S : CumulantFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n), connectedFn σ X = S n hn X
def shiftMotion (v : Fin 4 → ℝ) : Motions.RigidMotion :=
  ⟨1, one_mem _, v⟩
def ofOrthogonal (R : Orthogonal.orthogonalGroupFour) : Motions.RigidMotion :=
  ⟨R.1, R.2, 0⟩
def IsHyperoctahedralMotion (r : Motions.RigidMotion) : Prop :=
  ∃ w : hyperoctahedral, ∀ x, r.mat.mulVec x = w.1 x
def IsFamilyInvariant (S : CumulantFamily) (r : Motions.RigidMotion) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
    ∃ h : Motions.actOnTuple r X.1 ∈ TestSpaces.disjointSupportTuples Set.univ n,
      S n hn ⟨_, h⟩ = S n hn X
def IsFamilySymmetric (S : CumulantFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X Y : SepTupleOfCard n) (ς : Equiv.Perm (Fin n)),
    (Y.1 = fun i => X.1 (ς i)) → S n hn Y = S n hn X
def IsMotionInvariant (σ : TupleFunctional) (r : Motions.RigidMotion) : Prop :=
  σ.IsInvariant r.toFun
def compInv (σ : TupleFunctional) (r : AmbientSpace → AmbientSpace) : TupleFunctional where
  toFun X := σ (push (invMap r) X)
  map_nil := by rw [push_nil]; exact σ.map_nil
def IsReflectionPositiveAxial (σ : TupleFunctional) : Prop :=
  ∀ M : Mirrors.ReflectingHyperplane, M.normalVec ∈ Mirrors.axialNormals →
    σ.IsReflectionPositive M
def IsReflectionPositiveDiagonal (σ : TupleFunctional) : Prop :=
  ∀ M : Mirrors.ReflectingHyperplane, M.normalVec ∈ Mirrors.diagonalNormals →
    σ.IsReflectionPositive M
def offDiagonal (n : ℕ) : Set (TestSpaces.PointTuple n) := (TestSpaces.diagonalLocus n)ᶜ
abbrev TestFn {n : ℕ} (V : Set (TestSpaces.PointTuple n)) : Type :=
  {φ : TestSpaces.PointTuple n → ℂ // φ ∈ TestSpaces.smoothCompactSupp V}
def IsDistribution {n : ℕ} (V : Set (TestSpaces.PointTuple n)) (u : TestFn V → ℂ) : Prop :=
  (∀ (a b : ℂ) (φ ψ χ : TestFn V), χ.1 = a • φ.1 + b • ψ.1 →
      u χ = a * u φ + b * u ψ) ∧
    ∀ C : Set (TestSpaces.PointTuple n), IsCompact C → C ⊆ V → ∃ (p : ℕ) (c : ℝ), 0 ≤ c ∧
      ∀ φ : TestFn V, tsupport φ.1 ⊆ C →
        ENNReal.ofReal ‖u φ‖ ≤ ENNReal.ofReal c * TestSpaces.derivSupNorm p φ.1
def AgreesOnTensors {n : ℕ} (Φ : SepTupleOfCard n → ℝ)
    (u : TestFn (offDiagonal n) → ℂ) : Prop :=
  ∀ X : SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
    ∃ h : TestSpaces.tensorProdComplex X.1 ∈ TestSpaces.smoothCompactSupp (offDiagonal n),
      u ⟨_, h⟩ = ((Φ X : ℝ) : ℂ)
def IsRegular (σ : TupleFunctional) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ u, IsDistribution (offDiagonal n) u ∧
    AgreesOnTensors (fun X : SepTupleOfCard n => evalOnMap σ ⟨n, X⟩) u
section Reconstruction
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
def HasReconstruction : Prop :=
  ReflectionPositivity.Reconstruction.VacuumProperties σ h ∧
    ReflectionPositivity.LimitReconstruction.TimeSemigroupProperties σ h ∧
    ReflectionPositivity.LimitReconstruction.SpaceShiftProperties σ h ∧
    ReflectionPositivity.Reconstruction.MatrixElementFormula σ h
def ActsOnClasses (r : AmbientSpace → AmbientSpace)
    (U : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop :=
  ∀ F : PositiveSpan,
    U (posClass σ h F) = spanClass σ h (pushSpan r F.1)
def CommutesWithHamiltonian {Γ : Type*}
    (U : Γ → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop :=
  ∀ (w : Γ) (t : ℝ≥0), Commute (U w) (timeShift σ h t)
structure IsUnitaryRep {Γ : Type*} [Group Γ]
    (U : Γ → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop where
  unitary : ∀ w, (∀ ψ, ‖U w ψ‖ = ‖ψ‖) ∧ Function.Surjective (U w)
  map_mul : ∀ w w', U w ∘L U w' = U (w * w')
end Reconstruction
end LimitTheorem
end YangMills.Construction
end
