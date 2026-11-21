import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.OperationsOnTestFunctions
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import Reconstruction.MinkowskiSpace.SchwartzFunctionsThatStandInTheVectorsAtRealPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPointVectors
theorem schwartzSet_of_cast {N m : ℕ} (h : m = N) {φ : TestSpaces.PointTuple m → ℂ}
    (hφ : φ ∈ TestSpaces.schwartzSet m) :
    (fun z : TestSpaces.PointTuple N => φ fun j => z (Fin.cast h j)) ∈ TestSpaces.schwartzSet N := by
  subst h
  exact hφ
theorem schwartzSet_const_mul (hBasic : TestSpaces.Elementary.BasicProperties) {k : ℕ} (hk : 0 < k)
    (c : ℂ) {φ : TestSpaces.PointTuple k → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet k) :
    (fun x => c * φ x) ∈ TestSpaces.schwartzSet k := by
  have hlin := ((hBasic k hk).1.1 φ hφ φ hφ c 0).1.1
  have hEq : (fun x => c * φ x) = TestSpaces.Elementary.linComb c φ 0 φ := by
    funext x
    simp [TestSpaces.Elementary.linComb]
  rw [hEq]
  exact hlin
theorem tensorFun_const_left_mem (hBasic : TestSpaces.Elementary.BasicProperties) {m : ℕ} (c : ℂ)
    {ψ : TestSpaces.PointTuple (m + 1) → ℂ} (hψ : ψ ∈ TestSpaces.schwartzSet (m + 1)) :
    TestSpaces.tensorFun (q := 0) (fun _ => c) ψ ∈ TestSpaces.schwartzSet (0 + (m + 1)) := by
  have hmem := schwartzSet_of_cast (Nat.zero_add (m + 1)).symm
    (schwartzSet_const_mul hBasic (Nat.succ_pos m) c hψ)
  have hEq : TestSpaces.tensorFun (q := 0) (fun _ => c) ψ =
      fun z : TestSpaces.PointTuple (0 + (m + 1)) =>
        c * ψ fun j => z (Fin.cast (Nat.zero_add (m + 1)).symm j) := by
    funext z
    have hRight : TestSpaces.rightPart (q := 0) z =
        fun j => z (Fin.cast (Nat.zero_add (m + 1)).symm j) := by
      funext j
      exact congrArg z (Fin.ext (by simp))
    simp only [TestSpaces.tensorFun, hRight]
  rw [hEq]
  exact hmem
theorem tensorFun_const_right_mem (hBasic : TestSpaces.Elementary.BasicProperties) {p : ℕ} (c : ℂ)
    {φ : TestSpaces.PointTuple (p + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (p + 1)) :
    TestSpaces.tensorFun (q' := 0) φ (fun _ => c) ∈ TestSpaces.schwartzSet (p + 1 + 0) := by
  have hmem := schwartzSet_const_mul hBasic (Nat.succ_pos p) c hφ
  have hEq : TestSpaces.tensorFun (q' := 0) φ (fun _ => c) =
      fun z : TestSpaces.PointTuple (p + 1 + 0) => c * φ z := by
    funext z
    have hLeft : TestSpaces.leftPart (q' := 0) z = z := rfl
    simp only [TestSpaces.tensorFun, hLeft, mul_comm]
  rw [hEq]
  exact hmem
theorem starVal_mem_schwartzOfOrder (hBasic : TestSpaces.Elementary.BasicProperties)
    (hOps : TestFunctionOps.OperationsStatement) (k : ℕ) (ψ : Motions.TensorVal ℂ k)
    (hψ : ψ ∈ WightmanReconstruction.schwartzOfOrder k) :
    starVal ψ ∈ WightmanReconstruction.schwartzOfOrder k := by
  cases k with
  | zero => exact Set.mem_univ _
  | succ m =>
    have hψ' : (ψ : TestSpaces.PointTuple (m + 1) → ℂ) ∈ TestSpaces.schwartzSet (m + 1) := hψ
    have hperm := (((hOps.1 (m + 1) 1 (Nat.succ_pos m) one_pos Fin.revPerm
      Motions.RigidMotion.timeReflection).2.1 ψ hψ').1).1
    exact ((hBasic (m + 1) (Nat.succ_pos m)).1.1 _ hperm _ hperm 0 0).1.2.1
theorem translateVal_mem_schwartzOfOrder (hOps : TestFunctionOps.OperationsStatement) (k : ℕ)
    (φ : Motions.TensorVal ℂ k) (a : MinkowskiSpace.RealVec4)
    (hφ : φ ∈ WightmanReconstruction.schwartzOfOrder k) :
    translateVal a φ ∈ WightmanReconstruction.schwartzOfOrder k := by
  cases k with
  | zero => exact Set.mem_univ _
  | succ m =>
    have hφ' : (φ : TestSpaces.PointTuple (m + 1) → ℂ) ∈ TestSpaces.schwartzSet (m + 1) := hφ
    exact (((hOps.1 (m + 1) 1 (Nat.succ_pos m) one_pos 1
      ⟨1, one_mem _, a⟩).2.1 φ hφ').1).2.1
theorem hyperplaneTensorVal_mem_schwartzOfOrder (hBasic : TestSpaces.Elementary.BasicProperties)
    (hFacts : TestSpaces.TestSpaceFacts.Statement) (q q' : ℕ)
    (φ : Motions.TensorVal ℂ q) (ψ : Motions.TensorVal ℂ q')
    (hφ : φ ∈ WightmanReconstruction.schwartzOfOrder q)
    (hψ : ψ ∈ WightmanReconstruction.schwartzOfOrder q') :
    HyperplaneReflection.tensorVal φ ψ ∈ WightmanReconstruction.schwartzOfOrder (q + q') := by
  cases q with
  | zero =>
    cases q' with
    | zero => exact Set.mem_univ _
    | succ m =>
      have hψ' : (ψ : TestSpaces.PointTuple (m + 1) → ℂ) ∈ TestSpaces.schwartzSet (m + 1) := hψ
      exact tensorFun_const_left_mem hBasic φ hψ'
  | succ p =>
    have hφ' : (φ : TestSpaces.PointTuple (p + 1) → ℂ) ∈ TestSpaces.schwartzSet (p + 1) := hφ
    cases q' with
    | zero =>
      exact tensorFun_const_right_mem hBasic ψ hφ'
    | succ m =>
      have hψ' : (ψ : TestSpaces.PointTuple (m + 1) → ℂ) ∈ TestSpaces.schwartzSet (m + 1) := hψ
      exact (hFacts.1 (p + 1) (m + 1) 1 (Nat.succ_pos p) (Nat.succ_pos m) one_pos φ hφ' ψ hψ').1
theorem tensorProd_mem_schwartzSet (hFacts : TestSpaces.TestSpaceFacts.Statement) (k : ℕ) :
    ∀ f : Fin (k + 1) → (Fin 4 → ℝ) → ℂ, (∀ i, f i ∈ WightmanTheory.schwartzR4) →
      TestSpaces.tensorProd f ∈ TestSpaces.schwartzSet (k + 1) := by
  induction k with
  | zero =>
    intro f hf
    have hEq : TestSpaces.tensorProd f = WightmanTheory.asOnePointFn (f 0) := by
      funext x
      simp [TestSpaces.tensorProd, WightmanTheory.asOnePointFn]
    rw [hEq]
    exact hf 0
  | succ k ih =>
    intro f hf
    have h₁ := ih (fun i => f i.castSucc) fun i => hf _
    have h₂ : WightmanTheory.asOnePointFn (f (Fin.last (k + 1))) ∈ TestSpaces.schwartzSet 1 :=
      hf (Fin.last (k + 1))
    have hmem := (hFacts.1 (k + 1) 1 1 (Nat.succ_pos k) one_pos one_pos _ h₁ _ h₂).1
    convert hmem using 1
    funext x
    simp only [TestSpaces.tensorProd, TestSpaces.tensorFun, WightmanTheory.asOnePointFn,
      TestSpaces.leftPart, TestSpaces.rightPart]
    rw [Fin.prod_univ_castSucc]
    rfl
theorem schwartzClosure_holds (hBasic : TestSpaces.Elementary.BasicProperties)
    (hOps : TestFunctionOps.OperationsStatement)
    (hFacts : TestSpaces.TestSpaceFacts.Statement) : SchwartzClosure := by
  refine ⟨starVal_mem_schwartzOfOrder hBasic hOps, ?_,
    fun k φ a hφ => translateVal_mem_schwartzOfOrder hOps k φ a hφ, ?_⟩
  · intro k' k ψ φ hψ hφ
    exact hyperplaneTensorVal_mem_schwartzOfOrder hBasic hFacts k' k _ φ
      (starVal_mem_schwartzOfOrder hBasic hOps k' ψ hψ) hφ
  · intro k f hf
    cases k with
    | zero => exact Set.mem_univ _
    | succ m => exact tensorProd_mem_schwartzSet hFacts m f hf
end YangMills.Construction.RealPointVectors
