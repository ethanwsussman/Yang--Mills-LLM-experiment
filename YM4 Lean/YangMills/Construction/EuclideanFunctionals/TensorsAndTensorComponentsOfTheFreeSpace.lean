import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
theorem tensorFun_apply {k k' : ℕ} (a : TestSpaces.PointTuple k → ℂ)
    (a' : TestSpaces.PointTuple k' → ℂ) (x : TestSpaces.PointTuple (k + k')) :
    TestSpaces.tensorFun a a' x =
      a (fun i => x (Fin.castAdd k' i)) * a' (fun j => x (Fin.natAdd k j)) :=
  rfl
def stdParamsR4 : Conventions.StandingParameters where
  L := 13
  isAdmissible := ⟨by decide, le_rfl⟩
  K := 1
  m := 1
def tensorOfFns {n : ℕ} (h : Fin n → R4 → ℂ) : TestSpaces.PointTuple n → ℂ :=
  LimitSpaces.Ambient.tensorProd stdParamsR4 LimitSpaces.Ambient.euclidean h
theorem tensorOfFns_apply {n : ℕ} (h : Fin n → R4 → ℂ) (x : TestSpaces.PointTuple n) :
    tensorOfFns h x = ∏ l, h l (x l) :=
  rfl
def cplxEntries (X : FnList) {n : ℕ} (hX : X.length = n) (i : Fin n) : R4 → ℂ :=
  fun x => ((X.get (Fin.cast hX.symm i) x : ℝ) : ℂ)
def tensorOfNil : ℂ := 1
def tensorAt (n : ℕ) (X : sepAll) : TestSpaces.PointTuple n → ℂ :=
  open Classical in if hX : X.1.length = n then tensorOfFns (cplxEntries X.1 hX) else 0
def tensorAtZero (X : sepAll) : ℂ :=
  open Classical in if X.1.length = 0 then tensorOfNil else 0
def tensorComp (n : ℕ) : FreeSep →ₗ[ℂ] TestSpaces.PointTuple n → ℂ :=
  liftLin (tensorAt n)
def tensorCompZero : FreeSep →ₗ[ℂ] ℂ := liftLin tensorAtZero
def SameTensors (F F' : FreeSep) : Prop :=
  tensorCompZero F = tensorCompZero F' ∧
    ∀ n, 1 ≤ n → tensorComp n F = tensorComp n F'
theorem tensorAt_of_length {n : ℕ} (X : sepAll) (hX : X.1.length = n) :
    tensorAt n X = tensorOfFns (cplxEntries X.1 hX) := by
  simp [tensorAt, hX]
theorem tensorAt_of_length_ne {n : ℕ} (X : sepAll) (hX : X.1.length ≠ n) :
    tensorAt n X = 0 := by
  simp [tensorAt, hX]
theorem tensorComp_zero_apply (F : FreeSep) (e : TestSpaces.PointTuple 0) :
    tensorComp 0 F e = tensorCompZero F := by
  have h : (LinearMap.proj e : (TestSpaces.PointTuple 0 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ tensorComp 0 =
      tensorCompZero := by
    refine freeBasis.ext fun X => ?_
    rw [freeBasis_apply, LinearMap.comp_apply, tensorComp, liftLin_toFree,
      tensorCompZero, liftLin_toFree]
    by_cases hX : X.1.length = 0
    · rw [tensorAt_of_length X hX]
      simp [tensorAtZero, tensorOfNil, hX, tensorOfFns_apply]
    · rw [tensorAt_of_length_ne X hX]
      simp [tensorAtZero, hX]
  exact LinearMap.congr_fun h F
theorem sameTensors_iff (F F' : FreeSep) :
    SameTensors F F' ↔ ∀ n, tensorComp n F = tensorComp n F' := by
  constructor
  · rintro ⟨h₀, h⟩ n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · funext e
      rw [tensorComp_zero_apply, tensorComp_zero_apply, h₀]
    · exact h n hn
  · intro h
    refine ⟨?_, fun n _ => h n⟩
    have e : TestSpaces.PointTuple 0 := fun i => i.elim0
    rw [← tensorComp_zero_apply F e, ← tensorComp_zero_apply F' e, h 0]
end YangMills.Construction.EuclideanFunctionals
