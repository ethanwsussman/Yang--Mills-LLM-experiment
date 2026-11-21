import YangMills.Construction.Torus.IsometriesPermutationsAndSubTuplesKeepTuplesSeparated
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open Matrix
namespace AmbientPoints.TupleStability
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem isometry_of_isDistIsometry {r : Pt s E ≃ Pt s E} (h : IsDistIsometry r) : Isometry r :=
  Isometry.of_dist_eq h
theorem isDistIsometry_symm {r : Pt s E ≃ Pt s E} (h : IsDistIsometry r) :
    IsDistIsometry r.symm := by
  intro x y
  have := h (r.symm x) (r.symm y)
  simpa using this.symm
def homeomorphOfIsDistIsometry {r : Pt s E ≃ Pt s E} (h : IsDistIsometry r) :
    Pt s E ≃ₜ Pt s E where
  toEquiv := r
  continuous_toFun := (isometry_of_isDistIsometry h).continuous
  continuous_invFun := (isometry_of_isDistIsometry (isDistIsometry_symm h)).continuous
theorem tsupport_transportFn {r : Pt s E ≃ Pt s E} (h : IsDistIsometry r) {X : Type}
    [Zero X] (f : Pt s E → X) : tsupport (transportFn r f) = r '' tsupport f := by
  have hsupp : Function.support (transportFn r f) = r '' Function.support f := by
    ext x
    constructor
    · intro hx
      exact ⟨r.symm x, hx, r.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [transportFn, Function.mem_support] using hy
  have hcl := (homeomorphOfIsDistIsometry h).image_closure (Function.support f)
  unfold tsupport
  rw [hsupp]
  exact hcl.symm
theorem contDiff_affineMotion (R : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    ContDiff ℝ 1 (fun x : Fin 4 → ℝ => R *ᵥ x + v) := by
  have hlin : ContDiff ℝ 1 (fun x : Fin 4 → ℝ => R *ᵥ x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)).contDiff
  exact hlin.add contDiff_const
theorem isC1Fn_transportFn_of_motion {r : Pt s E ≃ Pt s E} (R : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → ℝ) (hm : ∀ x, r.symm (proj s E x) = proj s E (R *ᵥ x + v))
    {f : Pt s E → ℝ} (hf : IsC1Fn f) : IsC1Fn (transportFn r f) := by
  have hcomp : transportFn r f ∘ proj s E =
      (f ∘ proj s E) ∘ fun x : Fin 4 → ℝ => R *ᵥ x + v := by
    funext x
    simp only [Function.comp, transportFn, hm x]
  unfold IsC1Fn
  rw [hcomp]
  exact ContDiff.comp hf (contDiff_affineMotion R v)
theorem isC1Fn_transportFn (hY : Tower.OrthogonalMotions.Classification)
    (s : Conventions.StandingParameters) (E : Ambient) (r : Pt s E ≃ Pt s E)
    (h : IsDistIsometry r) (f : Pt s E → ℝ) (hf : IsC1Fn f) : IsC1Fn (transportFn r f) := by
  have hs := isDistIsometry_symm h
  cases E with
  | torus =>
    obtain ⟨-, -, -, hT⟩ := hY
    obtain ⟨-, -, hlift, -⟩ := hT s.L s.m s.isAdmissible s.m.pos
    obtain ⟨R, -, -, v, hv⟩ := hlift r.symm hs
    exact isC1Fn_transportFn_of_motion R v hv hf
  | euclidean =>
    obtain ⟨-, hM, -, -⟩ := hY
    obtain ⟨R, -, v, hv⟩ := hM r.symm hs
    exact isC1Fn_transportFn_of_motion R v hv hf
theorem tsupport_add_subset (f g : Pt s E → ℝ) :
    tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport f).union (isClosed_tsupport g))
  by_contra hn
  simp only [Set.mem_union, not_or] at hn
  have hf : f x = 0 := image_eq_zero_of_notMem_tsupport hn.1
  have hg : g x = 0 := image_eq_zero_of_notMem_tsupport hn.2
  exact hx (by simp [hf, hg])
theorem tsupport_smul_subset (c : ℝ) (f : Pt s E → ℝ) : tsupport (c • f) ⊆ tsupport f := by
  refine closure_mono fun x hx hfx => hx ?_
  simp [hfx]
def c1Submodule (A : Set (Pt s E)) : Submodule ℝ (Pt s E → ℝ) where
  carrier := c1CompactlySupportedIn A
  zero_mem' := by
    have hz : tsupport (0 : Pt s E → ℝ) = ∅ := by simp [tsupport]
    refine ⟨contDiff_const, ?_, ?_⟩
    · rw [hz]
      exact isCompact_empty
    · rw [hz]
      exact Set.empty_subset _
  add_mem' := by
    rintro f g ⟨hf, hfc, hfA⟩ ⟨hg, hgc, hgA⟩
    refine ⟨ContDiff.add hf hg, ?_, ?_⟩
    · exact (hfc.union hgc).of_isClosed_subset (isClosed_tsupport _) (tsupport_add_subset f g)
    · exact (tsupport_add_subset f g).trans (Set.union_subset hfA hgA)
  smul_mem' := by
    rintro c f ⟨hf, hfc, hfA⟩
    refine ⟨ContDiff.const_smul c hf, ?_, ?_⟩
    · exact hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset c f)
    · exact (tsupport_smul_subset c f).trans hfA
theorem disjoint_of_positivelySeparated {A B : Set (Pt s E)}
    (h : PositivelySeparated s E A B) : Disjoint A B := by apply _root_.YangMills.Construction.AmbientPoints.PositivelySeparated.disjoint <;> assumption
theorem permuteTuple_mem {n : ℕ} {f : Fin n → Pt s E → ℝ} (hf : f ∈ separatedTuples s E n)
    (σ : Equiv.Perm (Fin n)) : permuteTuple σ f ∈ separatedTuples s E n :=
  ⟨fun i => hf.1 (σ i), fun _ _ hij => hf.2 (σ.injective.ne hij)⟩
theorem restrictTuple_mem {n : ℕ} {f : Fin n → Pt s E → ℝ} (hf : f ∈ separatedTuples s E n)
    (J : Finset (Fin n)) : restrictTuple f J ∈ separatedTuples s E J.card :=
  ⟨fun _ => hf.1 _, fun _ _ hij => hf.2 ((J.orderEmbOfFin rfl).injective.ne hij)⟩
theorem transportTuple_mem (hY : Tower.OrthogonalMotions.Classification)
    {n : ℕ} {f : Fin n → Pt s E → ℝ} (hf : f ∈ separatedTuples s E n)
    (r : Pt s E ≃ Pt s E) (h : IsDistIsometry r) :
    transportTuple r f ∈ separatedTuples s E n := by
  refine ⟨fun i => ⟨isC1Fn_transportFn hY s E r h _ (hf.1 i).1, ?_⟩,
    fun i j hij => ?_⟩
  · change IsCompact (tsupport (transportFn r (f i)))
    rw [tsupport_transportFn h]
    exact (hf.1 i).2.image (isometry_of_isDistIsometry h).continuous
  · change Disjoint (tsupport (transportFn r (f i)))
      (tsupport (transportFn r (f j)))
    rw [tsupport_transportFn h, tsupport_transportFn h]
    exact (Set.disjoint_image_iff r.injective).2 (hf.2 hij)
theorem separatedTupleStability_of_classification (hY : Tower.OrthogonalMotions.Classification) :
    SeparatedTupleStability.holds := by
  intro s E
  refine ⟨fun r h => ⟨isDistIsometry_symm h, (isometry_of_isDistIsometry h).continuous,
      (isometry_of_isDistIsometry (isDistIsometry_symm h)).continuous,
      fun X _ f => tsupport_transportFn h f⟩,
    fun r h f hf => isC1Fn_transportFn hY s E r h f hf,
    fun n _ f hf => ⟨permuteTuple_mem hf, fun J _ => restrictTuple_mem hf J,
      fun r h => ⟨transportTuple_mem hY hf r h, fun J _ => rfl⟩⟩,
    fun A => ⟨c1Submodule A, rfl⟩, fun n _ A hA f hf => ?_⟩
  have hmem : ∀ i, f i ∈ c1CompactlySupportedIn (A i) := fun i => hf i (Set.mem_univ i)
  refine ⟨fun i => ⟨(hmem i).1, (hmem i).2.1⟩, fun i j hij => ?_⟩
  exact (disjoint_of_positivelySeparated (hA hij)).mono (hmem i).2.2 (hmem j).2.2
end AmbientPoints.TupleStability
end YangMills.Construction
end
