import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
variable {L m k j : ℕ}
def descendingChain (W : Edge L m k k → Matrices.ComplexMatrix2) {j : ℕ} (hj : j ≤ k) :
    Edge L m k j → Matrices.ComplexMatrix2 :=
  Nat.decreasingInduction (motive := fun a _ => Edge L m k a → Matrices.ComplexMatrix2)
    (fun a _ V => chosenProlong L m k a V) W hj
theorem descendingChain_top (W : Edge L m k k → Matrices.ComplexMatrix2) :
    descendingChain W (le_refl k) = W :=
  Nat.decreasingInduction_self _ _
theorem descendingChain_of_lt (W : Edge L m k k → Matrices.ComplexMatrix2) {a : ℕ} (ha : a < k) :
    descendingChain W ha.le = chosenProlong L m k a (descendingChain W ha) := by
  exact Nat.decreasingInduction_succ_left
    (motive := fun a _ => Edge L m k a → Matrices.ComplexMatrix2) _ _ ha ha.le
def chainBottom (W : Edge L m k k → Matrices.ComplexMatrix2) : Edge L m k 0 → Matrices.ComplexMatrix2 :=
  descendingChain W (Nat.zero_le k)
theorem chosenProlongComp_descendingChain (W : Edge L m k k → Matrices.ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) :
    chosenProlongComp L m k j (descendingChain W hj) = chosenProlongComp L m k k W := by
  refine Nat.decreasingInduction (motive := fun a h =>
    chosenProlongComp L m k a (descendingChain W h) = chosenProlongComp L m k k W) ?_ ?_ hj
  · intro a ha ih
    rw [← ih, descendingChain_of_lt W ha]
    rfl
  · rw [descendingChain_top]
theorem chainBottom_eq (W : Edge L m k k → Matrices.ComplexMatrix2) :
    chainBottom W = chosenProlongComp L m k k W :=
  chosenProlongComp_descendingChain W (Nat.zero_le k)
def smoothingIterDifferential (L m k j : ℕ) (U : Edge L m k 0 → Matrices.ComplexMatrix2) :
    edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k j :=
  leftDifferentialLinear (smoothingIter L m k j) U
def topConstraintMap (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) :
    edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k k :=
  smoothingIterDifferential L m k k (chainBottom W)
def smoothingIterFibre (O : Set (Edge L m k 0 → Matrices.ComplexMatrix2))
    (W : Edge L m k k → Matrices.ComplexMatrix2) : Set (Edge L m k 0 → Matrices.ComplexMatrix2) :=
  {U' | U' ∈ O ∧ smoothingIter L m k k U' = W}
structure IsSmoothingFibreNhd (L m k : ℕ) (O : Set (Edge L m k 0 → Matrices.ComplexMatrix2)) :
    Prop where
  isOpenNhd : IsOpenNhdOfOne O
  fibre_structure : EventuallyNearIdentity (fieldSpace L m k k) fun W =>
    IsAnalyticFieldSubmanifold (smoothingIterFibre O W) ∧ ∀ U' ∈ smoothingIterFibre O W,
      ∀ B : Edge L m k 0 → Matrices.ComplexMatrix2,
        B ∈ (fieldCurveData L m k 0).tangentSpan (smoothingIterFibre O W) U' ↔
          B ∈ edgeFormSpace L m k 0 ∧ leftDifferential (smoothingIter L m k k) U' B = 0
  critical_bottom : EventuallyNearIdentity (fieldSpace L m k k) fun W =>
    (fieldCurveData L m k 0).IsCriticalOn (smoothingIterFibre O W) (plaquetteAction L m k)
      (chainBottom W)
def smoothingFibreNhd (L m k : ℕ) : Set (Edge L m k 0 → Matrices.ComplexMatrix2) :=
  Classical.epsilon (IsSmoothingFibreNhd L m k)
def fibreRestrictedHessian (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (LinearMap.ker (topConstraintMap L m k W)) :=
  (fieldCurveData L m k 0).hessianForm (S := LinearMap.ker (topConstraintMap L m k W))
    (fun B => B.1.1) (smoothingIterFibre (smoothingFibreNhd L m k) W) (plaquetteAction L m k)
    (chainBottom W)
abbrev FineOnlyFamily (L m k : ℕ) : Type :=
  ∀ a : Fin k, FineOnlyVertex L m k a → Matrices.ComplexMatrix2
def fineOnlyFamilySpace (L m k : ℕ) : Submodule ℝ (FineOnlyFamily L m k) :=
  Submodule.pi univ fun a => fineOnlyFunctions L m k a
def fineOnlyFamilyPairing (f g : FineOnlyFamily L m k) : ℂ :=
  ∑ a, fineOnlyPairing (f a) (g a)
def fineOnlyFamilyNorm (f : FineOnlyFamily L m k) : ℝ :=
  Real.sqrt (fineOnlyFamilyPairing f f).re
def contourFamily (W : Edge L m k k → Matrices.ComplexMatrix2) (B : edgeFormSpace L m k 0) :
    FineOnlyFamily L m k :=
  fun a => contourLogDeriv L m k a (descendingChain W a.is_lt.le)
    (smoothingIterDifferential L m k a (chainBottom W) B : edgeFormSpace L m k a).1
def augmentedHessianValue (W : Edge L m k k → Matrices.ComplexMatrix2)
    (B : LinearMap.ker (topConstraintMap L m k W)) : ℝ :=
  fibreRestrictedHessian L m k W B + fineOnlyFamilyNorm (contourFamily W B.1) ^ 2
def augmentedHessian (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (LinearMap.ker (topConstraintMap L m k W)) :=
  Classical.epsilon fun T : QuadraticForm ℝ (LinearMap.ker (topConstraintMap L m k W)) =>
    ∀ B, T B = augmentedHessianValue W B
def vertexFunctionsVanishingAtTop (L m k : ℕ) :
    Submodule ℝ (Vertex L m k 0 → Matrices.ComplexMatrix2) where
  carrier := {f | f ∈ vertexFunctionSpace L m k 0 ∧ restrictVertexFunction k f = 0}
  add_mem' := by
    rintro f g ⟨hf, rf⟩ ⟨hg, rg⟩
    refine ⟨Submodule.add_mem _ hf hg, funext fun x => ?_⟩
    have ef := congrFun rf x
    have eg := congrFun rg x
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, Pi.zero_apply] at ef eg
    simp [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, ef, eg]
  zero_mem' := ⟨Submodule.zero_mem _, rfl⟩
  smul_mem' := by
    rintro c f ⟨hf, rf⟩
    refine ⟨Submodule.smul_mem _ c hf, funext fun x => ?_⟩
    have ef := congrFun rf x
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, Pi.zero_apply] at ef
    simp [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, ef]
def fineOnlyComponents (f : Vertex L m k 0 → Matrices.ComplexMatrix2) : FineOnlyFamily L m k :=
  fun a x => restrictVertexFunction (a : ℕ) f x.1
def totalGaussianNormaliser (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) : ℝ :=
  constrainedGaussianOnEdgeForms (topConstraintMap L m k W) (augmentedHessian L m k W)
def TotalNormaliserWellDefined (W : Edge L m k k → Matrices.ComplexMatrix2) : Prop :=
  (∀ B, augmentedHessian L m k W B = augmentedHessianValue W B) ∧ (augmentedHessian L m k W).PosDef
def logTotalNormaliserRatio (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) : ℝ :=
  if k = 0 then 0
  else Real.log (totalGaussianNormaliser L m k W) -
    Real.log (totalGaussianNormaliser L m k (trivialField L m k k))
def LogTotalNormaliserWellDefined (W : Edge L m k k → Matrices.ComplexMatrix2) : Prop :=
  k = 0 ∨ TotalNormaliserWellDefined W ∧ TotalNormaliserWellDefined (trivialField L m k k)
def scaledTopField (hL : 0 < L) (hj : j ≤ k) (W' : Edge L m k j → Matrices.ComplexMatrix2) :
    Edge L (scaledExponent m k j) j j → Matrices.ComplexMatrix2 :=
  transportTotal (scaleEdge hL hj j) W'
def logLevelNormaliserRatio (hL : 0 < L) (hj : j ≤ k) (W' : Edge L m k j → Matrices.ComplexMatrix2) :
    ℝ :=
  logTotalNormaliserRatio L (scaledExponent m k j) j (scaledTopField hL hj W')
def LogLevelNormaliserWellDefined (hL : 0 < L) (hj : j ≤ k)
    (W' : Edge L m k j → Matrices.ComplexMatrix2) : Prop :=
  LogTotalNormaliserWellDefined (scaledTopField hL hj W')
end Tower
end YangMills.Construction
end
