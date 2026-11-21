import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TestSpaces
variable {n q q' : ℕ}
def appendTuples (x : PointTuple q) (y : PointTuple q') : PointTuple (q + q') := Fin.append x y
def leftPart (z : PointTuple (q + q')) : PointTuple q := fun i => z (Fin.castAdd q' i)
def rightPart (z : PointTuple (q + q')) : PointTuple q' := fun j => z (Fin.natAdd q j)
theorem appendTuples_leftPart_rightPart (z : PointTuple (q + q')) :
    appendTuples (leftPart z) (rightPart z) = z := by apply _root_.YangMills.Construction.ConfigSpace.concatConfig_headArgs_tailArgs <;> assumption
def tensorFun (φ : PointTuple q → ℂ) (ψ : PointTuple q' → ℂ) : PointTuple (q + q') → ℂ :=
  fun z => φ (leftPart z) * ψ (rightPart z)
theorem tensorFun_appendTuples (φ : PointTuple q → ℂ) (ψ : PointTuple q' → ℂ) (x : PointTuple q)
    (y : PointTuple q') : tensorFun φ ψ (appendTuples x y) = φ x * ψ y := by apply _root_.YangMills.Construction.ConfigSpace.tensorFn_concatConfig <;> assumption
def scalarTensorLeft (c : ℂ) (ψ : PointTuple q' → ℂ) : PointTuple q' → ℂ := fun y => c * ψ y
def scalarTensorRight (φ : PointTuple q → ℂ) (c : ℂ) : PointTuple q → ℂ := fun x => c * φ x
section Splitting
variable (A : Finset (Fin n))
theorem card_compl_indices : Aᶜ.card = n - A.card := by
  simp [Finset.card_compl]
def restrictTo (x : PointTuple n) : PointTuple A.card :=
  fun t => x (A.orderEmbOfFin rfl t)
def restrictToCompl (x : PointTuple n) : PointTuple (n - A.card) :=
  fun t => x (Aᶜ.orderEmbOfFin (card_compl_indices A) t)
def mergeTuples (y : PointTuple (n - A.card)) (w : PointTuple A.card) : PointTuple n := fun i =>
  if h : i ∈ A then w ((A.orderIsoOfFin rfl).symm ⟨i, h⟩)
  else y ((Aᶜ.orderIsoOfFin (card_compl_indices A)).symm ⟨i, Finset.mem_compl.2 h⟩)
theorem restrictTo_mergeTuples (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    restrictTo A (mergeTuples A y w) = w := by
  funext t
  have hmem : A.orderEmbOfFin rfl t ∈ A := Finset.orderEmbOfFin_mem A rfl t
  have hiso : (⟨A.orderEmbOfFin rfl t, hmem⟩ : A) = A.orderIsoOfFin rfl t :=
    Subtype.ext (Finset.coe_orderIsoOfFin_apply A rfl t).symm
  simp only [restrictTo, mergeTuples, dif_pos hmem, hiso, OrderIso.symm_apply_apply]
theorem restrictToCompl_mergeTuples (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    restrictToCompl A (mergeTuples A y w) = y := by
  funext t
  have hmem : Aᶜ.orderEmbOfFin (card_compl_indices A) t ∈ Aᶜ :=
    Finset.orderEmbOfFin_mem Aᶜ (card_compl_indices A) t
  have hnot : Aᶜ.orderEmbOfFin (card_compl_indices A) t ∉ A := Finset.mem_compl.1 hmem
  have hiso : (⟨Aᶜ.orderEmbOfFin (card_compl_indices A) t, hmem⟩ : (Aᶜ : Finset (Fin n))) =
      Aᶜ.orderIsoOfFin (card_compl_indices A) t :=
    Subtype.ext (Finset.coe_orderIsoOfFin_apply Aᶜ (card_compl_indices A) t).symm
  simp only [restrictToCompl, mergeTuples, dif_neg hnot, hiso, OrderIso.symm_apply_apply]
theorem mergeTuples_restrictToCompl_restrictTo (x : PointTuple n) :
    mergeTuples A (restrictToCompl A x) (restrictTo A x) = x := by
  funext i
  by_cases h : i ∈ A
  · simp only [mergeTuples, dif_pos h, restrictTo]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · simp only [mergeTuples, dif_neg h, restrictToCompl]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
theorem tupleNorm_sq_eq_compl_add (x : PointTuple n) :
    tupleNorm x ^ 2 =
      tupleNorm (restrictToCompl A x) ^ 2 + tupleNorm (restrictTo A x) ^ 2 := by
  have reindex : ∀ (s : Finset (Fin n)) {k : ℕ} (h : s.card = k) (f : Fin n → ℝ),
      ∑ t : Fin k, f (s.orderEmbOfFin h t) = ∑ i ∈ s, f i := by
    intro s k h f
    rw [← Finset.sum_coe_sort s f, ← Equiv.sum_comp (s.orderIsoOfFin h).toEquiv]
    exact Finset.sum_congr rfl fun t _ => by simp
  simp only [tupleNorm_sq, restrictToCompl, restrictTo]
  rw [reindex Aᶜ (card_compl_indices A) fun i => TorusMetric.euclidNormVec (x i) ^ 2,
    reindex A rfl fun i => TorusMetric.euclidNormVec (x i) ^ 2, add_comm,
    Finset.sum_add_sum_compl]
theorem orderEmbOfFin_univ_eq_cast (s : Finset (Fin n)) (hs : s = Finset.univ) {k : ℕ}
    (h : s.card = k) (hk : k = n) (t : Fin k) : s.orderEmbOfFin h t = Fin.cast hk t :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := Fin.cast hk) (by simp [hs])
    (fun _ _ hab => hab)) t).symm
theorem restrictTo_univ (x : PointTuple n) :
    restrictTo (Finset.univ : Finset (Fin n)) x = fun t => x (Fin.cast (by simp) t) := by
  funext t
  exact congrArg x (orderEmbOfFin_univ_eq_cast _ rfl rfl (by simp) t)
theorem mergeTuples_univ (y : PointTuple (n - (Finset.univ : Finset (Fin n)).card))
    (w : PointTuple (Finset.univ : Finset (Fin n)).card) :
    mergeTuples Finset.univ y w = fun i => w (Fin.cast (by simp) i) := by
  have hzero : n - (Finset.univ : Finset (Fin n)).card = 0 := by simp
  have hy : y = restrictToCompl Finset.univ fun i => w (Fin.cast (by simp) i) :=
    funext fun t => absurd t.isLt (by omega)
  have hw : w = restrictTo Finset.univ fun i => w (Fin.cast (by simp) i) := by
    rw [restrictTo_univ]
    rfl
  have hx := mergeTuples_restrictToCompl_restrictTo Finset.univ
    (fun i => w (Fin.cast (by simp) i) : PointTuple n)
  rwa [← hy, ← hw] at hx
end Splitting
theorem tupleNorm_of_fin_zero (e : PointTuple 0) : tupleNorm e = 0 := by
  simp [tupleNorm]
section Integration
variable (A : Finset (Fin n)) (φ : PointTuple n → ℂ)
def integrableFibers : Set (PointTuple (n - A.card)) :=
  {y | Integrable fun w : PointTuple A.card => φ (mergeTuples A y w)}
def integrateOut (y : PointTuple (n - A.card)) : ℂ :=
  ∫ w : PointTuple A.card, φ (mergeTuples A y w)
theorem integrable_and_integral_fin_zero {k : ℕ} (hk : k = 0) (f : PointTuple k → ℂ)
    (w₀ : PointTuple k) : Integrable f ∧ ∫ w, f w = f w₀ := by
  subst hk
  have hvol : (volume : Measure (PointTuple 0)) = Measure.dirac w₀ := by
    rw [volume_pi, Measure.pi_of_empty]
    exact congrArg _ (Subsingleton.elim _ _)
  have hf : f = fun _ => f w₀ := funext fun w => congrArg f (Subsingleton.elim _ _)
  rw [hvol, hf]
  simp
theorem integrableFibers_empty : integrableFibers (∅ : Finset (Fin n)) φ = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (integrable_and_integral_fin_zero (by simp) _ fun t => absurd t.isLt (by simp)).1
theorem integrable_and_integral_comp_finCast {m : ℕ} (h : n = m) (f : PointTuple n → ℂ) :
    (Integrable (fun w : PointTuple m => f fun i => w (Fin.cast h i)) ↔ Integrable f) ∧
      ∫ w : PointTuple m, f (fun i => w (Fin.cast h i)) = ∫ x, f x := by
  subst h
  exact ⟨Iff.rfl, rfl⟩
theorem mem_integrableFibers_univ (y : PointTuple (n - (Finset.univ : Finset (Fin n)).card)) :
    y ∈ integrableFibers Finset.univ φ ↔ Integrable φ := by
  simp only [integrableFibers, Set.mem_ofPred_eq, mergeTuples_univ]
  exact (integrable_and_integral_comp_finCast (by simp) φ).1
theorem integrateOut_univ (y : PointTuple (n - (Finset.univ : Finset (Fin n)).card)) :
    integrateOut Finset.univ φ y = ∫ x, φ x := by
  simp only [integrateOut, mergeTuples_univ]
  exact (integrable_and_integral_comp_finCast (by simp) φ).2
end Integration
def weightIntegral (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : Fin 4 → ℝ, ENNReal.ofReal ((1 + TorusMetric.euclidNormVec u ^ 2) ^ (-(k : ℝ) / 2))
end YangMills.Construction.TestSpaces
