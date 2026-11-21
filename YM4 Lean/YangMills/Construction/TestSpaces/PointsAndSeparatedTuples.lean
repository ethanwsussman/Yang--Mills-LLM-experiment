import YangMills.Construction.ConfigSpace.TimeSlicesAndOpenSets
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
abbrev PointTuple (n : ℕ) : Type := Fin n → Fin 4 → ℝ
variable {n : ℕ}
def tupleNorm (x : PointTuple n) : ℝ := Real.sqrt (∑ i, ∑ μ, x i μ ^ 2)
theorem tupleNorm_sq (x : PointTuple n) :
    tupleNorm x ^ 2 = ∑ i, TorusMetric.euclidNormVec (x i) ^ 2 := by apply _root_.YangMills.Construction.ConfigSpace.euclidNorm_sq_eq_sum_sq <;> assumption
def timeCoord (x : PointTuple n) (i : Fin n) : ℝ := x i 3
def timeReflect (u : Fin 4 → ℝ) : Fin 4 → ℝ := ![u 0, u 1, u 2, -u 3]
def timeReflectTuple (x : PointTuple n) : PointTuple n := fun i => timeReflect (x i)
def timeReflectSet (Z : Set (PointTuple n)) : Set (PointTuple n) := timeReflectTuple '' Z
abbrev MultiIdx4 (n : ℕ) : Type := Fin n → Fin 4 → ℕ
def idxOrder (α : MultiIdx4 n) : ℕ := ∑ i, ∑ μ, α i μ
def idxChoose (α γ : MultiIdx4 n) : ℕ := ∏ i, ∏ μ, (α i μ).choose (γ i μ)
section Derivatives
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def coordDeriv (i : Fin n) (μ : Fin 4) (g : PointTuple n → F) : PointTuple n → F :=
  fun x => lineDeriv ℝ g x (Pi.single i (Pi.single μ 1))
def multiDeriv (α : MultiIdx4 n) (g : PointTuple n → F) : PointTuple n → F :=
  (List.finRange n).foldr
    (fun i h => (List.finRange 4).foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) g
def derivSupNorm (p : ℕ) (φ : PointTuple n → F) : ℝ≥0∞ :=
  ⨆ (x : PointTuple n) (α : MultiIdx4 n) (_ : idxOrder α ≤ p),
    ENNReal.ofReal ‖multiDeriv α φ x‖
def weightedSeminorm (k : ℕ) (φ : PointTuple n → F) : ℝ≥0∞ :=
  ⨆ (x : PointTuple n) (α : MultiIdx4 n) (_ : idxOrder α ≤ k),
    ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α φ x‖)
end Derivatives
section CompactSupport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def smoothCompactSupp (U : Set E) : Set (E → F) :=
  {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}
def c1CompactSupp (U : Set E) : Set (E → F) :=
  {φ | ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}
end CompactSupport
def schwartzSet (n : ℕ) : Set (PointTuple n → ℂ) :=
  {φ | ContDiff ℝ ∞ φ ∧ ∀ k : ℕ, 0 < k → weightedSeminorm k φ < ⊤}
def diagonalLocus (n : ℕ) : Set (PointTuple n) := (TestFunctions.injectiveTuples (Fin 4 → ℝ) n)ᶜ
theorem mem_diagonalLocus_iff (x : PointTuple n) :
    x ∈ diagonalLocus n ↔ ∃ i i', i < i' ∧ x i = x i' := by
  simp only [diagonalLocus, TestFunctions.injectiveTuples, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨i, i', hx, hne⟩ := h
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, i', hlt, hx⟩
    · exact ⟨i', i, hlt, hx.symm⟩
  · rintro ⟨i, i', hlt, hx⟩ hinj
    exact hlt.ne (hinj hx)
def flatSchwartzSet (n : ℕ) : Set (PointTuple n → ℂ) :=
  {φ | φ ∈ schwartzSet n ∧
    ∀ (α : MultiIdx4 n), ∀ x ∈ diagonalLocus n, multiDeriv α φ x = 0}
def disjointSupportTuples (O : Set (Fin 4 → ℝ)) (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {f | (∀ i, f i ∈ c1CompactSupp O) ∧
    Pairwise fun i i' => Disjoint (tsupport (f i)) (tsupport (f i'))}
theorem disjointSupportTuples_zero (O : Set (Fin 4 → ℝ)) :
    disjointSupportTuples O 0 = {fun i => i.elim0} := by
  ext f
  simp only [disjointSupportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim _ _
  · intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
def HasSmoothComponents (O : Set (Fin 4 → ℝ)) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ i, f i ∈ smoothCompactSupp O
theorem hasSmoothComponents_of_fin_zero (O : Set (Fin 4 → ℝ)) (f : Fin 0 → (Fin 4 → ℝ) → ℝ) :
    HasSmoothComponents O f := fun i => i.elim0
def tensorProd {R : Type*} [CommMonoid R] (f : Fin n → (Fin 4 → ℝ) → R) : PointTuple n → R :=
  fun x => ∏ i, f i (x i)
end YangMills.Construction.TestSpaces
