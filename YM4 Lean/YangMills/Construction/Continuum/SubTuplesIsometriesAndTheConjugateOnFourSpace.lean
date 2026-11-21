import YangMills.Construction.InfiniteLattice.SeparatedTuplesOfFourSpaceAsSymbols
import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Continuum.SeparatedFourTuples
variable {s : YangMills.Construction.Conventions.StandingParameters}
theorem restrictTuple_mem_separated {k : ℕ} {f : Fin k → EuclideanFour s → ℝ}
    (hf : f ∈ separatedTuples s .euclidean k) (A : Finset (Fin k)) :
    restrictTuple f A ∈ separatedTuples s .euclidean A.card :=
  ⟨fun _ => hf.1 _, fun _ _ h => hf.2 fun e => h ((A.orderEmbOfFin rfl).injective e)⟩
def sepSubTuple (X : SepTuple s) (A : Finset (Fin (tupleLength X))) : SepTuple s :=
  ⟨⟨A.card, restrictTuple (tupleComponents X) A⟩, restrictTuple_mem_separated (tupleComponents_mem X) A⟩
abbrev EuclidFour : Type := EuclideanSpace ℝ (Fin 4)
theorem dist_toLp_eq_euclidNormVec (x y : Fin 4 → ℝ) :
    dist (WithLp.toLp 2 x : EuclidFour) (WithLp.toLp 2 y) =
      YangMills.Construction.TorusMetric.euclidNormVec (x - y) := by apply _root_.YangMills.Construction.AmbientPoints.dist_toLp_eq_euclidNormVec <;> assumption
def equivEuclidean : EuclideanFour s ≃ᵢ EuclidFour where
  toFun x := WithLp.toLp 2 x
  invFun y := WithLp.ofLp y
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun := Isometry.of_dist_eq fun x y => dist_toLp_eq_euclidNormVec x y
def homeomorphPi : EuclideanFour s ≃ₜ (Fin 4 → ℝ) :=
  equivEuclidean.toHomeomorph.trans (PiLp.homeomorph 2 fun _ : Fin 4 => ℝ)
theorem tsupport_comp_homeo {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (h : P ≃ₜ Q) (g : Q → ℝ) : tsupport (g ∘ h) = h ⁻¹' tsupport g := by
  rw [tsupport, Function.support_comp_eq_preimage, tsupport, h.preimage_closure]
variable (s) in
abbrev FourIsometry : Type := {r : EuclideanFour s ≃ EuclideanFour s // IsDistIsometry r}
theorem isDistIsometry_symm {r : EuclideanFour s ≃ EuclideanFour s} (hr : IsDistIsometry r) :
    IsDistIsometry r.symm := by apply _root_.YangMills.Construction.FourSpaceSymbols.isDistIsometry_symm <;> assumption
theorem contDiff_of_isDistIsometry {r : EuclideanFour s ≃ EuclideanFour s}
    (hr : IsDistIsometry r) :
    ContDiff (E := Fin 4 → ℝ) (F := Fin 4 → ℝ) ℝ 1 (fun x => r x) := by
  have hi : Isometry
      (fun x : EuclidFour => (WithLp.toLp 2 (r (WithLp.ofLp x : Fin 4 → ℝ)) : EuclidFour)) :=
    Isometry.of_dist_eq fun x y => by
      have h₁ := dist_toLp_eq_euclidNormVec (r (WithLp.ofLp x : Fin 4 → ℝ))
        (r (WithLp.ofLp y : Fin 4 → ℝ))
      have h₂ := dist_toLp_eq_euclidNormVec (WithLp.ofLp x) (WithLp.ofLp y)
      have h₃ := hr (WithLp.ofLp x : Fin 4 → ℝ) (WithLp.ofLp y : Fin 4 → ℝ)
      simp only [WithLp.toLp_ofLp] at h₂
      exact h₁.trans (h₃.trans h₂.symm)
  have h : ContDiff ℝ 1
      (fun x : EuclidFour => (WithLp.toLp 2 (r (WithLp.ofLp x : Fin 4 → ℝ)) : EuclidFour)) :=
    hi.affineIsometryOfStrictConvexSpace.toContinuousAffineMap.contDiff
  have h₁ : ContDiff ℝ 1 (fun x : Fin 4 → ℝ => (WithLp.toLp 2 x : EuclidFour)) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h₂ : ContDiff ℝ 1 (fun x : EuclidFour => (WithLp.ofLp x : Fin 4 → ℝ)) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).contDiff
  exact h₂.comp (h.comp h₁)
def isometryToHomeomorph (r : FourIsometry s) : EuclideanFour s ≃ₜ EuclideanFour s :=
  (IsometryEquiv.mk r.1 (Isometry.of_dist_eq fun x y => r.2 x y)).toHomeomorph
theorem transportTuple_mem {k : ℕ} (r : FourIsometry s) {f : Fin k → EuclideanFour s → ℝ}
    (hf : f ∈ separatedTuples s .euclidean k) :
    transportTuple r.1 f ∈ separatedTuples s .euclidean k := by
  have hs : ∀ i, tsupport (transportTuple r.1 f i) =
      (isometryToHomeomorph r).symm ⁻¹' tsupport (f i) :=
    fun i => tsupport_comp_homeo (isometryToHomeomorph r).symm (f i)
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · have h₁ : ContDiff ℝ 1 (f i ∘ proj s .euclidean) := (hf.1 i).1
    exact h₁.comp (contDiff_of_isDistIsometry (isDistIsometry_symm r.2))
  · rw [hs]
    exact (isometryToHomeomorph r).symm.isCompact_preimage.2 (hf.1 i).2
  · change Disjoint (tsupport _) (tsupport _)
    rw [hs, hs]
    exact (hf.2 hij).preimage _
def transportSep (r : FourIsometry s) (X : SepTuple s) : SepTuple s :=
  ⟨⟨tupleLength X, transportTuple r.1 (tupleComponents X)⟩, transportTuple_mem r (tupleComponents_mem X)⟩
def translateEquiv (v : Fin 4 → ℝ) : EuclideanFour s ≃ EuclideanFour s where
  toFun := fun x : Fin 4 → ℝ => x + v
  invFun := fun x : Fin 4 → ℝ => x - v
  left_inv := fun x : Fin 4 → ℝ => add_sub_cancel_right x v
  right_inv := fun x : Fin 4 → ℝ => sub_add_cancel x v
def translateIsometry (v : Fin 4 → ℝ) : FourIsometry s :=
  ⟨translateEquiv v, fun x y => by
    have h : ∀ a b : Fin 4 → ℝ, YangMills.Construction.TorusMetric.euclidNormVec ((a + v) - (b + v)) =
        YangMills.Construction.TorusMetric.euclidNormVec (a - b) := fun a b => by
      rw [add_sub_add_right_eq_sub]
    exact h x y⟩
def translateFn {Y : Type*} (v : Fin 4 → ℝ) (f : EuclideanFour s → Y) : EuclideanFour s → Y :=
  transportFn (translateIsometry v).1 f
def translateSep (v : Fin 4 → ℝ) (X : SepTuple s) : SepTuple s :=
  transportSep (translateIsometry v) X
def permuteLen {k : ℕ} (ς : Equiv.Perm (Fin k)) (X : SepTupleLen s k) : SepTupleLen s k :=
  ⟨permuteTuple ς X.1, fun i => X.2.1 (ς i), fun _ _ h => X.2.2 (ς.injective.ne h)⟩
def IsSymmLen {n : ℕ} (σ : SepTupleLen s n → ℝ) : Prop :=
  ∀ (X : SepTupleLen s n) (ς : Equiv.Perm (Fin n)), σ (permuteLen ς X) = σ X
def IsSymm (σ : SepTuple s → ℝ) : Prop :=
  ∀ k, IsSymmLen fun X : SepTupleLen s k => σ (ofFixedLength X)
def IsMultilinLen {n : ℕ} (σ : SepTupleLen s n → ℝ) : Prop :=
  ∀ (i : Fin n) (t t' : ℝ) (X X' X'' : SepTupleLen s n),
    (∀ j, j ≠ i → X.1 j = X'.1 j) → X''.1 i = t • X.1 i + t' • X'.1 i →
      (∀ j, j ≠ i → X''.1 j = X.1 j) → σ X'' = t * σ X + t' * σ X'
def IsMultilin (σ : SepTuple s → ℝ) : Prop :=
  ∀ k, 1 ≤ k → IsMultilinLen fun X : SepTupleLen s k => σ (ofFixedLength X)
theorem mem_separatedTuples_iff {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    (f : Fin n → EuclideanFour s → ℝ) ∈ separatedTuples s .euclidean n ↔
      f ∈ YangMills.Construction.TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have hs : ∀ g : (Fin 4 → ℝ) → ℝ, tsupport (g ∘ (homeomorphPi (s := s))) =
      (homeomorphPi (s := s)) ⁻¹' tsupport g := fun g => tsupport_comp_homeo homeomorphPi g
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ⟨(h₁ i).1, ?_, Set.subset_univ _⟩, fun i j hij => ?_⟩
    · have h := (h₁ i).2
      have h' : IsCompact ((homeomorphPi (s := s)) ⁻¹' tsupport (f i)) := by
        rw [← hs]
        exact h
      exact homeomorphPi.isCompact_preimage.1 h'
    · have h := h₂ hij
      refine Disjoint.of_preimage (homeomorphPi (s := s)).surjective ?_
      rw [← hs, ← hs]
      exact h
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ⟨(h₁ i).1, ?_⟩, fun i j hij => ?_⟩
    · have h : IsCompact ((homeomorphPi (s := s)) ⁻¹' tsupport (f i)) :=
        homeomorphPi.isCompact_preimage.2 (h₁ i).2.1
      rw [← hs] at h
      exact h
    · have h := (h₂ hij).preimage (homeomorphPi (s := s))
      rw [← hs, ← hs] at h
      exact h
variable (s) in
def sepLenEquiv (n : ℕ) : SepTupleLen s n ≃ YangMills.Construction.TestSpaces.SepTupleOfCard n where
  toFun X := ⟨X.1, (mem_separatedTuples_iff X.1).1 X.2⟩
  invFun Y := ⟨Y.1, (mem_separatedTuples_iff Y.1).2 Y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (s) in
def sepTupleEquiv : SepTuple s ≃ YangMills.Construction.TestSpaces.SepTuple where
  toFun X := ⟨tupleLength X, sepLenEquiv s _ ⟨tupleComponents X, tupleComponents_mem X⟩⟩
  invFun Y := ofFixedLength ((sepLenEquiv s Y.1).symm Y.2)
  left_inv _ := rfl
  right_inv _ := rfl
end YangMills.Construction.Continuum.SeparatedFourTuples
