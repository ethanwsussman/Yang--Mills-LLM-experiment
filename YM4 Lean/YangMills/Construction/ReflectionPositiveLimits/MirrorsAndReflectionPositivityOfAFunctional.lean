import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.ReflectionPositiveLimits.NormsReflectionsCubesAndLatticesOfFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ComplexOrder
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.TorusMetric (euclidNormVec)
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open EuclidIsometry
def admissibleNormals : Set Space :=
  {n | (∃ μ, n = coordVec μ) ∨
    ∃ μ ν, μ ≠ ν ∧
      (n = coordVec μ + coordVec ν ∨
        n = coordVec μ - coordVec ν)}
theorem ne_zero_of_mem_admissibleNormals {n : Space} (hn : n ∈ admissibleNormals) : n ≠ 0 := by
  intro h0
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, ν, hne, rfl | rfl⟩
  · simpa [coordVec] using congrFun h0 μ
  · simpa [coordVec, Pi.single_apply, hne] using congrFun h0 μ
  · simpa [coordVec, Pi.single_apply, hne] using congrFun h0 μ
theorem euclidInner_sub_right (n x y : Space) :
    euclidInner n (x - y) = euclidInner n x - euclidInner n y := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_sub_right <;> assumption
theorem euclidInner_smul_right (n x : Space) (t : ℝ) :
    euclidInner n (t • x) = t * euclidInner n x := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.euclidDot_smul <;> assumption
theorem euclidNormVec_sq (n : Space) : euclidNormVec n ^ 2 = euclidInner n n := by
  rw [euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem euclidInner_coordVec (μ : Fin 4) (x : Space) :
    euclidInner (coordVec μ) x = x μ := by
  simp [euclidInner, coordVec, Pi.single_apply]
theorem euclidNormVec_sq_pos {n : Space} (hn : n ≠ 0) : 0 < euclidNormVec n ^ 2 := by
  rw [euclidNormVec_sq]
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hn
  exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
    ⟨μ, Finset.mem_univ μ, mul_self_pos.2 hμ⟩
structure NormalMirror where
  normal : Space
  offset : ℝ
  normal_mem : normal ∈ admissibleNormals
namespace NormalMirror
def posSide (P : NormalMirror) : Set Space := {x | P.offset < euclidInner P.normal x}
def negSide (P : NormalMirror) : Set Space := {x | euclidInner P.normal x < P.offset}
def reflectPt (P : NormalMirror) (x : Space) : Space :=
  x - (2 * (euclidInner P.normal x - P.offset) / euclidNormVec P.normal ^ 2) • P.normal
theorem inner_self_ne_zero (P : NormalMirror) : euclidInner P.normal P.normal ≠ 0 := by
  rw [← euclidNormVec_sq]
  exact (euclidNormVec_sq_pos (ne_zero_of_mem_admissibleNormals P.normal_mem)).ne'
theorem euclidInner_reflectPt (P : NormalMirror) (x : Space) :
    euclidInner P.normal (P.reflectPt x) - P.offset =
      -(euclidInner P.normal x - P.offset) := by
  have hP := P.inner_self_ne_zero
  rw [reflectPt, euclidInner_sub_right, euclidInner_smul_right, euclidNormVec_sq]
  field_simp
  ring
theorem sum_sq_sub_smul (n d : Space) (s : ℝ) (hs : s * euclidInner n n = 2 * euclidInner n d) :
    ∑ μ, (d - s • n) μ ^ 2 = ∑ μ, d μ ^ 2 := by
  have e : ∑ μ, (d - s • n) μ ^ 2 =
      ∑ μ, d μ ^ 2 - 2 * s * euclidInner n d + s * (s * euclidInner n n) := by
    simp only [euclidInner, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, hs]
  ring
theorem reflectPt_preserves_dist (P : NormalMirror) (x y : Space) :
    euclidNormVec (P.reflectPt x - P.reflectPt y) = euclidNormVec (x - y) := by
  have hP := P.inner_self_ne_zero
  have e : P.reflectPt x - P.reflectPt y =
      (x - y) - (2 * euclidInner P.normal (x - y) / euclidInner P.normal P.normal) • P.normal := by
    funext μ
    simp only [reflectPt, euclidNormVec_sq, euclidInner_sub_right, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [e, euclidNormVec, euclidNormVec, sum_sq_sub_smul]
  field_simp
def reflectIso (P : NormalMirror) : EuclidIsometry := ⟨P.reflectPt, P.reflectPt_preserves_dist⟩
theorem push_reflectIso_mem {P : NormalMirror} {X : Tuple} (hX : X ∈ tuplesSupportedIn P.posSide) :
    push P.reflectIso X ∈ tuplesSupportedIn P.negSide := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn]
  intro y hy
  have hz : P.offset < euclidInner P.normal (P.reflectIso.symm.toFun y) := hX f hf hy
  have e := P.euclidInner_reflectPt (P.reflectIso.symm.toFun y)
  have e' : P.reflectPt (P.reflectIso.symm.toFun y) = y := P.reflectIso.toFun_symm y
  rw [e'] at e
  change euclidInner P.normal y < P.offset
  linarith
theorem disjoint_negSide_posSide (P : NormalMirror) : Disjoint P.negSide P.posSide :=
  Set.disjoint_left.2 fun x (h : euclidInner P.normal x < P.offset)
    (h' : P.offset < euclidInner P.normal x) => lt_asymm h h'
theorem concatenable_reflectIso {P : NormalMirror} {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn P.posSide) (hY : Y ∈ tuplesSupportedIn P.posSide) :
    Concatenable (push P.reflectIso X) Y :=
  concatenable_of_disjoint P.disjoint_negSide_posSide (push_reflectIso_mem hX) hY
end NormalMirror
def ReflectionPositiveAt (P : NormalMirror) (σ : Tuple → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (X : ι → Tuple) (α : ι → ℂ)
    (hX : ∀ b, X b ∈ tuplesSupportedIn P.posSide),
    0 ≤ ∑ b, ∑ b', conj (α b) * α b' *
      (σ (concat (push P.reflectIso (X b)) (X b')
        (NormalMirror.concatenable_reflectIso (hX b) (hX b'))) : ℂ)
def timeZeroMirror : NormalMirror where
  normal := coordVec timeAxis
  offset := 0
  normal_mem := Or.inl ⟨_, rfl⟩
theorem timeZeroMirror_reflectIso (x : Space) :
    timeZeroMirror.reflectIso.toFun x = reflectTime x := by
  change x - (2 * (euclidInner (coordVec timeAxis) x - 0) /
      euclidNormVec (coordVec timeAxis) ^ 2) • coordVec timeAxis =
    x - (2 * x timeAxis) • coordVec timeAxis
  have h : (coordVec timeAxis : Space) timeAxis = 1 := by
    simp [coordVec]
  rw [euclidNormVec_sq, euclidInner_coordVec, euclidInner_coordVec, h]
  simp
theorem timeZeroMirror_posSide : timeZeroMirror.posSide = upperHalfSpace := by
  ext x
  simp [NormalMirror.posSide, timeZeroMirror, upperHalfSpace, euclidInner_coordVec]
end YangMills.Construction.ReflectionPositivity
