import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
open TestFunctions TorusMetric
abbrev Space : Type := Fin 4 → ℝ
abbrev ScalarField : Type := Space → ℝ
def c1Compact (O : Set Space) : Set ScalarField :=
  {f | IsC1R4 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O}
def continuousCompact : Set ScalarField :=
  {f | Continuous f ∧ IsCompact (tsupport f)}
def separatedSet : Set (List ScalarField) :=
  {X | (∀ f ∈ X, f ∈ c1Compact univ) ∧
    X.Pairwise fun f g => Disjoint (tsupport f) (tsupport g)}
abbrev Tuple : Type := ↥separatedSet
def Tuple.len (X : Tuple) : ℕ := X.1.length
def nilTuple : Tuple := ⟨[], by simp [separatedSet]⟩
def tuplesSupportedIn (O : Set Space) : Set Tuple :=
  {X | ∀ f ∈ X.1, tsupport f ⊆ O}
abbrev TupleComb : Type := Tuple →₀ ℂ
def basisOf (X : Tuple) : TupleComb := Finsupp.single X 1
def combsSupportedIn (O : Set Space) : Submodule ℂ TupleComb :=
  Submodule.span ℂ (basisOf '' tuplesSupportedIn O)
def conjComb (Z : TupleComb) : TupleComb :=
  Z.mapRange (starRingEnd ℂ) (map_zero _)
theorem conjComb_sum {ι : Type*} (s : Finset ι) (α : ι → ℂ) (X : ι → Tuple) :
    conjComb (∑ b ∈ s, α b • basisOf (X b)) =
      ∑ b ∈ s, conj (α b) • basisOf (X b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjComb]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    ext Y
    by_cases h : X b = Y <;> simp [conjComb, basisOf, h]
def Concatenable (X Y : Tuple) : Prop :=
  ∀ f ∈ X.1, ∀ g ∈ Y.1, Disjoint (tsupport f) (tsupport g)
theorem append_mem_separatedSet {X Y : Tuple} (h : Concatenable X Y) :
    X.1 ++ Y.1 ∈ separatedSet := by
  refine ⟨fun f hf => ?_, List.pairwise_append.2 ⟨X.2.2, Y.2.2, h⟩⟩
  rcases List.mem_append.1 hf with hf | hf
  · exact X.2.1 f hf
  · exact Y.2.1 f hf
def concat (X Y : Tuple) (h : Concatenable X Y) : Tuple :=
  ⟨X.1 ++ Y.1, append_mem_separatedSet h⟩
def concatBasis (X Y : Tuple) : TupleComb :=
  open Classical in
  if h : Concatenable X Y then basisOf (concat X Y h) else 0
def concatBilin : TupleComb →ₗ[ℂ] TupleComb →ₗ[ℂ] TupleComb :=
  Finsupp.linearCombination ℂ fun X => Finsupp.linearCombination ℂ (concatBasis X)
def concatOn (O O' : Set Space) :
    combsSupportedIn O →ₗ[ℂ] combsSupportedIn O' →ₗ[ℂ] TupleComb :=
  concatBilin.domRestrict₁₂ (combsSupportedIn O) (combsSupportedIn O')
theorem concatenable_of_disjoint {O O' : Set Space} (h : Disjoint O O')
    {X Y : Tuple} (hX : X ∈ tuplesSupportedIn O) (hY : Y ∈ tuplesSupportedIn O') :
    Concatenable X Y :=
  fun f hf g hg => h.mono (hX f hf) (hY g hg)
structure EuclidIsometry where
  toFun : Space → Space
  preserves_dist : ∀ x y, euclidNormVec (toFun x - toFun y) = euclidNormVec (x - y)
namespace EuclidIsometry
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)
theorem dist_toLp_eq (x y : Space) :
    dist (WithLp.toLp 2 x : E4) (WithLp.toLp 2 y) = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.AmbientPoints.dist_toLp_eq_euclidNormVec <;> assumption
def toE4 (r : EuclidIsometry) (x : E4) : E4 :=
  WithLp.toLp 2 (r.toFun (WithLp.ofLp x))
theorem isometry_toE4 (r : EuclidIsometry) : Isometry r.toE4 :=
  Isometry.of_dist_eq fun x y => by
    have h := dist_toLp_eq (WithLp.ofLp x) (WithLp.ofLp y)
    simp only [WithLp.toLp_ofLp] at h
    rw [toE4, toE4, dist_toLp_eq, r.preserves_dist, h]
theorem contDiff_toFun (r : EuclidIsometry) : ContDiff ℝ 1 r.toFun := by
  have h : ContDiff ℝ 1 r.toE4 :=
    r.isometry_toE4.affineIsometryOfStrictConvexSpace.toContinuousAffineMap.contDiff
  have h₁ : ContDiff ℝ 1 (fun x : Space => (WithLp.toLp 2 x : E4)) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h₂ : ContDiff ℝ 1 (fun x : E4 => (WithLp.ofLp x : Space)) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).contDiff
  exact h₂.comp (h.comp h₁)
theorem bijective_toFun (r : EuclidIsometry) : Function.Bijective r.toFun := by
  have hi : Function.Injective r.toE4 := r.isometry_toE4.injective
  have hs : Function.Surjective r.toE4 := by
    let a := r.isometry_toE4.affineIsometryOfStrictConvexSpace
    have hl : Function.Surjective a.linearIsometry.toLinearMap :=
      LinearMap.injective_iff_surjective.1 a.linearIsometry.injective
    exact (AffineMap.linear_surjective_iff a.toAffineMap).1 hl
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have := @hi (WithLp.toLp 2 x) (WithLp.toLp 2 y) (by simp [toE4, h])
    simpa using this
  · obtain ⟨x, hx⟩ := hs (WithLp.toLp 2 y)
    refine ⟨WithLp.ofLp x, ?_⟩
    have := congrArg WithLp.ofLp hx
    simpa [toE4] using this
def toPerm (r : EuclidIsometry) : Space ≃ Space := Equiv.ofBijective r.toFun r.bijective_toFun
def symm (r : EuclidIsometry) : EuclidIsometry where
  toFun := r.toPerm.symm
  preserves_dist x y := by
    rw [← r.preserves_dist]
    have h : ∀ z, r.toFun (r.toPerm.symm z) = z := r.toPerm.apply_symm_apply
    rw [h, h]
theorem toFun_symm (r : EuclidIsometry) (x : Space) : r.toFun (r.symm.toFun x) = x :=
  r.toPerm.apply_symm_apply x
theorem symm_toFun (r : EuclidIsometry) (x : Space) : r.symm.toFun (r.toFun x) = x :=
  r.toPerm.symm_apply_apply x
def toHomeo (r : EuclidIsometry) : Space ≃ₜ Space where
  toEquiv := r.toPerm
  continuous_toFun := r.contDiff_toFun.continuous
  continuous_invFun := r.symm.contDiff_toFun.continuous
def translate (v : Space) : EuclidIsometry where
  toFun x := x + v
  preserves_dist x y := by simp
theorem symm_translate (v x : Space) : (translate v).symm.toFun x = x - v := by
  apply (translate v).bijective_toFun.1
  rw [toFun_symm]
  simp [translate]
end EuclidIsometry
open EuclidIsometry
def pushFn (r : EuclidIsometry) (f : ScalarField) : ScalarField := f ∘ r.symm.toFun
theorem tsupport_pushFn (r : EuclidIsometry) (f : ScalarField) :
    tsupport (pushFn r f) = r.symm.toFun ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f r.toHomeo.symm
theorem map_pushFn_mem (r : EuclidIsometry) (X : Tuple) :
    X.1.map (pushFn r) ∈ separatedSet := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h₁, h₂, -⟩ := X.2.1 f hf
    refine ⟨ContDiff.comp h₁ r.symm.contDiff_toFun, ?_, subset_univ _⟩
    rw [tsupport_pushFn]
    exact r.toHomeo.symm.isCompact_preimage.2 h₂
  · refine List.pairwise_map.2 (X.2.2.imp fun h => ?_)
    rw [tsupport_pushFn, tsupport_pushFn]
    exact h.preimage _
def push (r : EuclidIsometry) (X : Tuple) : Tuple :=
  ⟨X.1.map (pushFn r), map_pushFn_mem r X⟩
def pushComb (r : EuclidIsometry) : TupleComb →ₗ[ℂ] TupleComb :=
  Finsupp.lmapDomain ℂ ℂ (push r)
theorem push_translate (v : Space) (X : Tuple) :
    (push (translate v) X).1 = X.1.map fun f x => f (x - v) := by
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp [pushFn, symm_translate]
def IsNormalizedFunctional (σ : Tuple → ℝ) : Prop := σ nilTuple = 1
def linearExt (σ : Tuple → ℝ) : TupleComb →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun X => (σ X : ℂ)
def componentAt (X : Tuple) (i : ℕ) : ScalarField := X.1.getD i 0
def AdmissiblyTendsto (n₀ : ℤ) (seq : ℤ → Tuple) (X : Tuple) : Prop :=
  (∀ n ≥ n₀, (seq n).len = X.len) ∧
    ∃ A : Fin X.len → Set Space, (∀ i, IsCompact (A i)) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧
      (∀ n ≥ n₀, ∀ i : Fin X.len, tsupport (componentAt (seq n) i) ∪ tsupport (componentAt X i) ⊆ A i) ∧
      ∀ i : Fin X.len, Tendsto (fun n => c1NormR4 (componentAt (seq n) i - componentAt X i)) atTop (𝓝 0)
theorem tsupport_linComb_subset (α α' : ℝ) (f f' : ScalarField) :
    tsupport (α • f + α' • f') ⊆ tsupport f ∪ tsupport f' := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport f).union (isClosed_tsupport f'))
  by_contra h
  rw [mem_union, not_or] at h
  have h₁ : f x = 0 := image_eq_zero_of_notMem_tsupport h.1
  have h₂ : f' x = 0 := image_eq_zero_of_notMem_tsupport h.2
  exact hx (by simp [h₁, h₂])
theorem linComb_mem {pre post : List ScalarField} {f f' : ScalarField} (α α' : ℝ)
    (h : pre ++ f :: post ∈ separatedSet) (h' : pre ++ f' :: post ∈ separatedSet) :
    pre ++ (α • f + α' • f') :: post ∈ separatedSet := by
  have hsub := tsupport_linComb_subset α α' f f'
  have hf := h.1 f (by simp)
  have hf' := h'.1 f' (by simp)
  have hc : α • f + α' • f' ∈ c1Compact univ := by
    refine ⟨ContDiff.add (contDiff_const.smul hf.1) (contDiff_const.smul hf'.1),
      (hf.2.1.union hf'.2.1).of_isClosed_subset (isClosed_tsupport _) hsub, subset_univ _⟩
  have hp := h.2
  have hp' := h'.2
  simp only [List.pairwise_append, List.pairwise_cons] at hp hp'
  refine ⟨fun g hg => ?_, ?_⟩
  · rcases List.mem_append.1 hg with hg | hg
    · exact h.1 g (by simp [hg])
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact hc
      · exact h.1 g (by simp [hg])
  · simp only [List.pairwise_append, List.pairwise_cons]
    refine ⟨hp.1, ⟨fun a ha => ?_, hp.2.1.2⟩, fun a ha b hb => ?_⟩
    · exact (disjoint_union_left.2 ⟨hp.2.1.1 a ha, hp'.2.1.1 a ha⟩).mono_left hsub
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact (disjoint_union_right.2
          ⟨hp.2.2 a ha _ (by simp), hp'.2.2 a ha _ (by simp)⟩).mono_right hsub
      · exact hp.2.2 a ha b (by simp [hb])
def IsAdmissiblyContinuous (σ : Tuple → ℝ) : Prop :=
  ∀ (n₀ : ℤ) (seq : ℤ → Tuple) (X : Tuple),
    AdmissiblyTendsto n₀ seq X → Tendsto (fun n => σ (seq n)) atTop (𝓝 (σ X))
def IsPermInvariant (σ : Tuple → ℝ) : Prop :=
  ∀ X Y : Tuple, X.1.Perm Y.1 → σ X = σ Y
def IsSlotLinear (σ : Tuple → ℝ) : Prop :=
  ∀ (pre post : List ScalarField) (f f' : ScalarField) (α α' : ℝ)
    (h : pre ++ f :: post ∈ separatedSet) (h' : pre ++ f' :: post ∈ separatedSet),
    σ ⟨pre ++ (α • f + α' • f') :: post, linComb_mem α α' h h'⟩ =
      α * σ ⟨_, h⟩ + α' * σ ⟨_, h'⟩
def IsIsomInvariant (r : EuclidIsometry) (σ : Tuple → ℝ) : Prop :=
  ∀ X, σ (push r X) = σ X
def IsTranslInvariant (σ : Tuple → ℝ) : Prop :=
  ∀ v, IsIsomInvariant (translate v) σ
end ReflectionPositivity
end YangMills.Construction
