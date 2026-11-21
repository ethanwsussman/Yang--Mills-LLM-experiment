import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import YangMills.Construction.Conventions.LatticeAndStateDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open AmbientPoints Continuum.SeparatedFourTuples
open LatticeConventions (Direction euclidDot basisVector)
open InfiniteLattice (GaugeField LatticeSymmetry LatticePoint)
noncomputable section
namespace InfiniteLattice.EuclideanMirrors
section Tuples
variable {s : Conventions.StandingParameters}
theorem mem_sepTuplesIn_iff {O : Set (EuclideanFour s)} {X : SepTuple s} :
    X ∈ sepTuplesIn O ↔ ∀ i, tsupport (tupleComponents X i) ⊆ O := by
  rw [mem_sepTuplesIn]
  refine forall_congr' fun i => ⟨fun h => h.2.2, fun h => ?_⟩
  exact ⟨((tupleComponents_mem X).1 i).1, ((tupleComponents_mem X).1 i).2, h⟩
def joinTuple (X Y : SepTuple s) : FunctionTuple s .euclidean :=
  ⟨tupleLength X + tupleLength Y, appendTuple X Y⟩
theorem joinTuple_mem_allSeparatedTuples {X Y : SepTuple s} (h : CanConcat X Y) :
    joinTuple X Y ∈ allSeparatedTuples s .euclidean :=
  appendTuple_mem h
end Tuples
def reflectionNormals : Set (Fin 4 → ℝ) :=
  {n | (∃ κ : Direction, n = basisVector κ) ∨
    ∃ κ lam : Direction, κ < lam ∧
      (n = basisVector κ + basisVector lam ∨ n = basisVector κ - basisVector lam)}
abbrev ReflNormal : Type := ↥reflectionNormals
namespace ReflNormal
def sqNorm (n : ReflNormal) : ℝ := TorusMetric.euclidNormVec n.1 ^ 2
def dual (n : ReflNormal) : Fin 4 → ℝ := (n.sqNorm)⁻¹ • n.1
theorem sqNorm_eq_euclidDot (n : ReflNormal) : n.sqNorm = euclidDot n.1 n.1 := by
  rw [sqNorm, TorusMetric.euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun μ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun μ _ => sq _
theorem sqNorm_eq_one_or_two (n : ReflNormal) : n.sqNorm = 1 ∨ n.sqNorm = 2 := by
  rw [sqNorm_eq_euclidDot]
  obtain ⟨n, ⟨κ, rfl⟩ | ⟨κ, lam, hlt, rfl | rfl⟩⟩ := n
  · left
    fin_cases κ <;> simp [euclidDot, basisVector, Fin.sum_univ_four]
  · right
    fin_cases κ <;> fin_cases lam <;> first
      | exact absurd hlt (by decide)
      | (simp [euclidDot, basisVector, Fin.sum_univ_four]; try norm_num)
  · right
    fin_cases κ <;> fin_cases lam <;> first
      | exact absurd hlt (by decide)
      | (simp [euclidDot, basisVector, Fin.sum_univ_four]; try norm_num)
theorem sqNorm_ne_zero (n : ReflNormal) : n.sqNorm ≠ 0 := by
  rcases n.sqNorm_eq_one_or_two with h | h <;> rw [h] <;> norm_num
end ReflNormal
def hyperplaneReflection (n : ReflNormal) (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x - (2 * (euclidDot n.1 x - c)) • n.dual
theorem euclidDot_dual (n : ReflNormal) : euclidDot n.1 n.dual = 1 := by
  have h : euclidDot n.1 n.dual = (n.sqNorm)⁻¹ * euclidDot n.1 n.1 := by
    simp only [euclidDot, ReflNormal.dual, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [h, ← ReflNormal.sqNorm_eq_euclidDot, inv_mul_cancel₀ n.sqNorm_ne_zero]
theorem euclidDot_hyperplaneReflection (n : ReflNormal) (c : ℝ) (x : Fin 4 → ℝ) :
    euclidDot n.1 (hyperplaneReflection n c x) = 2 * c - euclidDot n.1 x := by
  have h : euclidDot n.1 (hyperplaneReflection n c x) =
      euclidDot n.1 x - 2 * (euclidDot n.1 x - c) * euclidDot n.1 n.dual := by
    simp only [euclidDot, hyperplaneReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [h, euclidDot_dual]
  ring
theorem hyperplaneReflection_hyperplaneReflection (n : ReflNormal) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflection n c (hyperplaneReflection n c x) = x := by
  have h := euclidDot_hyperplaneReflection n c x
  funext μ
  simp only [hyperplaneReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]
  ring
theorem euclidNormVec_hyperplaneReflection_sub (n : ReflNormal) (c : ℝ) (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (hyperplaneReflection n c x - hyperplaneReflection n c y) =
      TorusMetric.euclidNormVec (x - y) := by
  have hq := n.sqNorm_eq_euclidDot
  have hq0 := n.sqNorm_ne_zero
  have hsum : ∀ v : Fin 4 → ℝ, ∑ μ, v μ ^ 2 = euclidDot v v := fun v =>
    Finset.sum_congr rfl fun μ _ => sq _
  have hsub : hyperplaneReflection n c x - hyperplaneReflection n c y =
      (x - y) - (2 * euclidDot n.1 (x - y)) • n.dual := by
    have hd : euclidDot n.1 (x - y) = euclidDot n.1 x - euclidDot n.1 y := by
      simp only [euclidDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    funext μ
    simp only [hyperplaneReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd]
    ring
  rw [hsub]
  unfold TorusMetric.euclidNormVec
  rw [hsum, hsum]
  congr 1
  generalize x - y = w
  have hn : euclidDot n.dual n.dual = (n.sqNorm)⁻¹ := by
    have h : euclidDot n.dual n.dual = (n.sqNorm)⁻¹ * ((n.sqNorm)⁻¹ * euclidDot n.1 n.1) := by
      simp only [euclidDot, ReflNormal.dual, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [h, ← hq, inv_mul_cancel₀ hq0, mul_one]
  have hw : euclidDot w n.dual = (n.sqNorm)⁻¹ * euclidDot n.1 w := by
    simp only [euclidDot, ReflNormal.dual, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have hexp : ∀ t : ℝ, euclidDot (w - t • n.dual) (w - t • n.dual) =
      euclidDot w w - 2 * t * euclidDot w n.dual + t ^ 2 * euclidDot n.dual n.dual := by
    intro t
    simp only [euclidDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [hexp, hn, hw]
  field_simp
  ring
def hyperplaneReflectionEquiv (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ) :
    EuclideanFour s ≃ EuclideanFour s where
  toFun := hyperplaneReflection n c
  invFun := hyperplaneReflection n c
  left_inv := hyperplaneReflection_hyperplaneReflection n c
  right_inv := hyperplaneReflection_hyperplaneReflection n c
theorem isDistIsometry_hyperplaneReflectionEquiv (s : Conventions.StandingParameters)
    (n : ReflNormal) (c : ℝ) : IsDistIsometry (hyperplaneReflectionEquiv s n c) :=
  fun (x y : Fin 4 → ℝ) => euclidNormVec_hyperplaneReflection_sub n c x y
structure AffineMirror where
  normal : ReflNormal
  offset : ℝ
namespace AffineMirror
variable (M : AffineMirror)
def carrier : Set (Fin 4 → ℝ) := {x | euclidDot M.normal.1 x = M.offset}
def IsAxial : Prop := M.normal.sqNorm = 1
def IsDiagonal : Prop := M.normal.sqNorm = 2
def reflect : (Fin 4 → ℝ) → Fin 4 → ℝ := EuclideanMirrors.hyperplaneReflection M.normal M.offset
def positiveSide : Set (Fin 4 → ℝ) := {x | M.offset < euclidDot M.normal.1 x}
def IsLatticeAligned (a' : ℝ) : Prop :=
  (M.normal.sqNorm = 1 → ∃ k : ℤ, M.offset = (a' / 2) * (k : ℝ)) ∧
    (M.normal.sqNorm = 2 → ∃ k : ℤ, M.offset = a' * (k : ℝ))
end AffineMirror
end InfiniteLattice.EuclideanMirrors
end
end YangMills.Construction
