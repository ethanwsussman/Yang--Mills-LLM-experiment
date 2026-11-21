import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.EuclideanFunctionals.SharpNormOnFunctionsOfClassC1Proof
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZeroProof
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotationsProof
import YangMills.Construction.RotationInvariance.WhatAnOrthogonalMapPreserves
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TorusMetric
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance
open YangMills.Construction.RealPlane
def unitScale : SharpScale := ⟨1, le_rfl⟩
theorem ofOrthogonalMatrix_mul (Q Q' : Matrix.orthogonalGroup (Fin 4) ℝ) :
    EuclidMotion.ofOrthogonalMatrix (Q * Q') =
      EuclidMotion.ofOrthogonalMatrix Q * EuclidMotion.ofOrthogonalMatrix Q' :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.ofOrthogonalMatrix_apply,
      EuclidMotion.ofOrthogonalMatrix_apply, EuclidMotion.ofOrthogonalMatrix_apply,
      Matrix.mulVec_mulVec]
    rfl
theorem ofOrthogonalMatrix_mul_transl (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (u : R4) :
    EuclidMotion.ofOrthogonalMatrix Q * EuclidMotion.transl u =
      EuclidMotion.transl (EuclidMotion.ofOrthogonalMatrix Q u) * EuclidMotion.ofOrthogonalMatrix Q :=
  EuclidMotion.ext_of_apply fun x => by
    simp only [EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.ofOrthogonalMatrix_apply, Matrix.mulVec_add]
theorem actFn_actFn {α : Type*} (g g' : EuclidMotion) (f : R4 → α) :
    g.actFn (g'.actFn f) = (g * g').actFn f := by
  funext x
  simp only [EuclidMotion.actFn, mul_inv_rev, EuclidMotion.mul_apply]
theorem actFn_one {α : Type*} (f : R4 → α) : (1 : EuclidMotion).actFn f = f := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.actFn_one <;> assumption
theorem actFn_actFn_inv {α : Type*} (g : EuclidMotion) (f : R4 → α) :
    g.actFn ((g⁻¹).actFn f) = f := by
  rw [actFn_actFn, mul_inv_cancel, actFn_one]
theorem injective_coe (g : EuclidMotion) : Function.Injective fun x : R4 => g x :=
  g.toPerm.injective
theorem surjective_coe (g : EuclidMotion) : Function.Surjective fun x : R4 => g x :=
  g.toPerm.surjective
theorem actFn_mem_disjointComplexTuples (hP : TupleRules.ReImAndMotionOfFns)
    (g : EuclidMotion) {n : ℕ} {h : Fin n → R4 → ℂ} (hh : h ∈ disjointComplexTuples n) :
    (fun l => g.actFn (h l)) ∈ disjointComplexTuples n := by
  refine ⟨fun l => (hP unitScale g g (h l) (hh.1 l)).2.2.2.1, fun k l hkl => ?_⟩
  show Disjoint (supp (g.actFn (h k))) (supp (g.actFn (h l)))
  rw [(hP unitScale g g (h k) (hh.1 k)).2.2.2.2.1, (hP unitScale g g (h l) (hh.1 l)).2.2.2.2.1]
  exact (Set.disjoint_image_iff (injective_coe g)).2 (hh.2 hkl)
theorem sepNIn_univ (n : ℕ) :
    sepNIn n Set.univ = sepN n := by
  ext X
  exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_iUnion.2 ⟨n, h⟩, fun _ _ => Set.subset_univ _⟩⟩
theorem image_euclidBall (g : EuclidMotion) (x : R4) (ρ : ℝ) :
    (fun z : R4 => g z) '' EuclideanBalls.euclidBall x ρ = EuclideanBalls.euclidBall (g x) ρ := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show euclidNormVec (g z - g x) < ρ
    rw [EuclidMotion.euclidNormVec_sub]
    exact hz
  · intro hy
    refine ⟨g⁻¹ y, ?_, g.apply_inv_apply y⟩
    show euclidNormVec (g⁻¹ y - x) < ρ
    rw [← EuclidMotion.euclidNormVec_sub g, g.apply_inv_apply]
    exact hy
theorem setDistR4_image (g : EuclidMotion) (S S' : Set R4) :
    TestFunctions.setDistR4 ((fun z : R4 => g z) '' S) ((fun z : R4 => g z) '' S') =
      TestFunctions.setDistR4 S S' := by
  simp only [TestFunctions.setDistR4, iInf_image, EuclidMotion.euclidNormVec_sub]
theorem functionAction (hP : TupleRules.ReImAndMotionOfFns) :
    FunctionAction := by
  intro Q Q' f hf
  refine ⟨(hP unitScale _ (EuclidMotion.ofOrthogonalMatrix Q') f hf).2.2.2.1, fun a b g _ => rfl, rfl,
    fun hr x => hr _, fun h' h'' _ _ => rfl, ?_⟩
  rw [actFn_actFn, ofOrthogonalMatrix_mul]
theorem supportBallDistanceTuple (hP : TupleRules.ReImAndMotionOfFns)
    (hI : TupleRules.MotionOfListsAndCombs) :
    SupportBallDistanceTuple := by
  intro Q
  refine ⟨fun f hf => (hP unitScale _ (EuclidMotion.ofOrthogonalMatrix Q) f hf).2.2.2.2.1,
    fun x ρ _ => image_euclidBall _ x ρ, fun S S' _ _ => setDistR4_image _ S S',
    fun n => ⟨?_, ?_⟩⟩
  · ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact actFn_mem_disjointComplexTuples hP _ hh
    · intro hk
      exact ⟨fun l => (EuclidMotion.ofOrthogonalMatrix Q)⁻¹.actFn (k l),
        actFn_mem_disjointComplexTuples hP _ hk, funext fun l => actFn_actFn_inv _ (k l)⟩
  · have hb := (hI (EuclidMotion.ofOrthogonalMatrix Q) Set.univ isOpen_univ).2.1 n
    rw [Set.image_univ_of_surjective (surjective_coe _), sepNIn_univ] at hb
    exact hb.1.image_eq
theorem uniformNorm_actFn (g : EuclidMotion) (f : R4 → ℂ) :
    TestFunctions.uniformNorm (g.actFn f) = TestFunctions.uniformNorm f :=
  (g⁻¹).toPerm.surjective.iSup_comp (fun x => ‖f x‖)
theorem lipConstR4_actFn (g : EuclidMotion) (f : R4 → ℂ) :
    TestFunctions.lipConstR4 (g.actFn f) = TestFunctions.lipConstR4 f := by
  refine congrArg sInf (Set.ext fun C => and_congr Iff.rfl ⟨fun hC x y => ?_, fun hC x y => ?_⟩)
  · have := hC (g x) (g y)
    change ‖f (g⁻¹ (g x)) - f (g⁻¹ (g y))‖ ≤ C * euclidNormVec (g x - g y) at this
    rw [EuclidMotion.inv_apply_apply, EuclidMotion.inv_apply_apply,
      EuclidMotion.euclidNormVec_sub] at this
    exact this
  · have := hC (g⁻¹ x) (g⁻¹ y)
    change ‖f (g⁻¹ x) - f (g⁻¹ y)‖ ≤ C * euclidNormVec (g⁻¹ x - g⁻¹ y) at this
    rw [EuclidMotion.euclidNormVec_sub] at this
    exact this
theorem normInvariance (hP : TupleRules.ReImAndMotionOfFns) :
    NormInvariance := fun c Q f hf =>
  ⟨uniformNorm_actFn _ f, lipConstR4_actFn _ f,
    (hP c _ (EuclidMotion.ofOrthogonalMatrix Q) f hf).2.2.2.2.2.2.2.2⟩
theorem translationCompat : TranslationCompat := by
  intro Q f u _
  rw [actFn_actFn, actFn_actFn, ofOrthogonalMatrix_mul_transl]
theorem rotationRules (hM : ProductMotions.RotationsSpecialOrthogonal) :
    RotationRules := by
  intro t
  obtain ⟨-, -, -, h₄, h₅⟩ := hM t
  refine ⟨h₄, h₅, fun x => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [rotateMotion_apply]
    simp [rotateFour, ofComponents, orthogonalComponent]
  · rw [rotateMotion_apply]
    simp [rotateFour, ofComponents, orthogonalComponent]
  · rw [rotateMotion_apply]
    funext i
    fin_cases i <;>
      simp [rotateFour, ofComponents, RealPlane.rotate, planeComponent, orthogonalComponent,
        PeriodicLattice.coordVec]
  · rw [rotateMotion_apply]
    funext i
    fin_cases i <;>
      simp [rotateFour, ofComponents, RealPlane.rotate, planeComponent, orthogonalComponent,
        PeriodicLattice.coordVec]
theorem continuous_rotate (t : ℝ) : Continuous (rotate t) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_rotate <;> assumption
theorem rotate_rotate (s t : ℝ) (y : RealPlane) :
    rotate s (rotate t y) = rotate (s + t) y := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.rotate_rotate <;> assumption
theorem rotate_zero (y : RealPlane) : rotate 0 y = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.rotate_zero <;> assumption
def rotateHomeomorph (t : ℝ) : RealPlane ≃ₜ RealPlane where
  toFun := rotate t
  invFun := rotate (-t)
  left_inv y := by rw [rotate_rotate, neg_add_cancel, rotate_zero]
  right_inv y := by rw [rotate_rotate, add_neg_cancel, rotate_zero]
  continuous_toFun := continuous_rotate t
  continuous_invFun := continuous_rotate (-t)
theorem plateRotation (hA : ProductMotions.MotionsActOnPlaneFactor)
    (hI : ProductMotions.MotionImagesAreProducts) : PlateRotation := by
  intro t α φ hα hφ
  refine ⟨(hA α hα φ hφ 0 t).2.1, (hI α hα φ hφ 0 t).2.1, ?_⟩
  have h := tsupport_comp_eq_preimage α (rotateHomeomorph (-t))
  have e : (rotateHomeomorph (-t) : RealPlane → RealPlane) = rotate (-t) := rfl
  rw [e] at h
  rw [h]
  ext y
  constructor
  · intro hy
    refine ⟨rotate (-t) y, hy, ?_⟩
    rw [rotate_rotate, add_neg_cancel, rotate_zero]
  · rintro ⟨z, hz, rfl⟩
    show rotate (-t) (rotate t z) ∈ tsupport α
    rw [rotate_rotate, neg_add_cancel, rotate_zero]
    exact hz
section ComplexTuples
variable {n n' : ℕ}
theorem nil_mem_sepAll : ([] : FnList) ∈ sepAll := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.nil_mem_sepAll <;> assumption
theorem actFree_toFree_nil (g : EuclidMotion) : g.actFree (toFree []) = toFree [] :=
  liftLin_toFree (fun X : sepAll => toFree (g.actList X.1)) ⟨[], nil_mem_sepAll⟩
theorem actFree_complexTuple (hW : TupleRules.ComplexTupleRules)
    (g : EuclidMotion) {h : Fin n → R4 → ℂ} (hh : h ∈ disjointComplexTuples n) :
    g.actFree (complexTuple h) = complexTuple fun l => g.actFn (h l) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [complexTuple_of_length_zero, complexTuple_of_length_zero]
    exact actFree_toFree_nil g
  · exact (hW Set.univ isOpen_univ g n h ((mem_disjointComplexTuples_iff hn h).1 hh)
      fun _ => Set.subset_univ _).2.2.2.2.2.2.1
theorem complexTupleImages (hP : TupleRules.ReImAndMotionOfFns)
    (hW : TupleRules.ComplexTupleRules) : ComplexTupleImages :=
  fun _ _ _ _ hh => ⟨actFn_mem_disjointComplexTuples hP _ hh, actFree_complexTuple hW _ hh,
    actFn_mem_disjointComplexTuples hP _ hh, actFree_complexTuple hW _ hh⟩
open Classical in
theorem complexTuple_eq_sum (h : Fin n → R4 → ℂ) :
    complexTuple h = ∑ ε ∈ admissibleSigns h,
      (Complex.I ^ ∑ l, (ε l : ℕ)) • toFree (List.ofFn fun l => reOrImPart (ε l) (h l)) := by
  rw [complexTuple]
  split_ifs with hr
  · have hs : admissibleSigns h = {0} := by
      ext ε
      simp only [admissibleSigns, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨fun hε => funext fun l => hε l (hr l), fun hε l _ => by rw [hε]; rfl⟩
    rw [hs, Finset.sum_singleton]
    simp [reOrImPart]
  · rfl
theorem reImParts_mem_sepAll (hP : TupleRules.ReImAndMotionOfFns)
    {h : Fin n → R4 → ℂ} (hh : h ∈ disjointComplexTuples n) (ε : Fin n → Fin 2) :
    List.ofFn (fun l => reOrImPart (ε l) (h l)) ∈ sepAll := by
  have hm : ∀ (e : Fin 2) (l : Fin n), reOrImPart e (h l) ∈ C1c ℝ := by
    intro e l
    obtain ⟨h₁, h₂, -⟩ := hP unitScale 1 1 (h l) (hh.1 l)
    by_cases he : e = 0
    · simpa [reOrImPart, he] using h₁
    · simpa [reOrImPart, he] using h₂
  have hs : ∀ (e : Fin 2) (l : Fin n), supp (reOrImPart e (h l)) ⊆ supp (h l) := by
    intro e l
    obtain ⟨-, -, h₃, -⟩ := hP unitScale 1 1 (h l) (hh.1 l)
    by_cases he : e = 0
    · simpa [reOrImPart, he] using Set.subset_union_left.trans h₃
    · simpa [reOrImPart, he] using Set.subset_union_right.trans h₃
  refine Set.mem_iUnion.2 ⟨n, List.length_ofFn, ?_, ?_⟩
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact hm _ l
  · exact List.pairwise_ofFn.2 fun i j hij => (hh.2 hij.ne).mono (hs _ _) (hs _ _)
theorem freeMul_toFree {T U : FnList} (hT : T ∈ sepAll) (hU : U ∈ sepAll) :
    freeMul (toFree T) (toFree U) = toFree (listAppend T U) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeMul_toFree <;> assumption
open Classical in
theorem sum_admissibleSigns_append {V : Type*} [AddCommMonoid V] (h : Fin n → R4 → ℂ)
    (h' : Fin n' → R4 → ℂ) (F : (Fin (n + n') → Fin 2) → V) :
    ∑ ε ∈ admissibleSigns (Fin.append h h'), F ε =
      ∑ ε ∈ admissibleSigns h, ∑ ε' ∈ admissibleSigns h', F (Fin.append ε ε') := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun ε => (fun l => ε (Fin.castAdd n' l), fun k => ε (Fin.natAdd n k)))
    (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    have hε' := (Finset.mem_filter.1 hε).2
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun l hl => ?_⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k hk => ?_⟩⟩
    · exact hε' (Fin.castAdd n' l) (by rwa [Fin.append_left])
    · exact hε' (Fin.natAdd n k) (by rwa [Fin.append_right])
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩
    induction i using Fin.addCases with
    | left l =>
      rw [Fin.append_left] at hi ⊢
      exact (Finset.mem_filter.1 h₁).2 l hi
    | right k =>
      rw [Fin.append_right] at hi ⊢
      exact (Finset.mem_filter.1 h₂).2 k hi
  · intro ε _
    exact Fin.append_castAdd_natAdd
  · intro p _
    refine Prod.ext (funext fun l => ?_) (funext fun k => ?_)
    · exact Fin.append_left _ _ l
    · exact Fin.append_right _ _ k
  · intro ε _
    rw [Fin.append_castAdd_natAdd]
theorem combSupp_complexTuple_subset
    (hW : TupleRules.ComplexTupleRules) {h : Fin n → R4 → ℂ}
    (hh : h ∈ disjointComplexTuples n) :
    combSupp (complexTuple h) ⊆ ⋃ l, supp (h l) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x hx
    rw [complexTuple_of_length_zero] at hx
    simp only [combSupp, Set.mem_iUnion] at hx
    obtain ⟨X, hX, f, hf, -⟩ := hx
    rw [toFree_of_mem nil_mem_sepAll] at hX
    have hX' := Finset.mem_singleton.1 (Finsupp.support_single_subset hX)
    subst hX'
    cases hf
  · exact (hW Set.univ isOpen_univ 1 n h ((mem_disjointComplexTuples_iff hn h).1 hh)
      fun _ => Set.subset_univ _).2.1
theorem append_mem_disjointComplexTuples {h : Fin n → R4 → ℂ} {h' : Fin n' → R4 → ℂ}
    (hh : h ∈ disjointComplexTuples n) (hh' : h' ∈ disjointComplexTuples n')
    (hd : ∀ l k, Disjoint (supp (h l)) (supp (h' k))) :
    Fin.append h h' ∈ disjointComplexTuples (n + n') := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.addCases with
    | left l => rw [Fin.append_left]; exact hh.1 l
    | right k => rw [Fin.append_right]; exact hh'.1 k
  · show Disjoint (supp (Fin.append h h' i)) (supp (Fin.append h h' j))
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [Fin.append_left, Fin.append_left]
        exact hh.2 fun e => hij (by rw [e])
      | right b =>
        rw [Fin.append_left, Fin.append_right]
        exact hd a b
    | right a =>
      induction j using Fin.addCases with
      | left b =>
        rw [Fin.append_right, Fin.append_left]
        exact (hd b a).symm
      | right b =>
        rw [Fin.append_right, Fin.append_right]
        exact hh'.2 fun e => hij (by rw [e])
theorem freeMul_complexTuple (hP : TupleRules.ReImAndMotionOfFns)
    {h : Fin n → R4 → ℂ} {h' : Fin n' → R4 → ℂ} (hh : h ∈ disjointComplexTuples n)
    (hh' : h' ∈ disjointComplexTuples n') :
    freeMul (complexTuple h) (complexTuple h') =
      complexTuple (Fin.append h h') := by
  classical
  rw [complexTuple_eq_sum h, complexTuple_eq_sum h',
    complexTuple_eq_sum (Fin.append h h'), sum_admissibleSigns_append,
    LinearMap.map_sum₂]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ε' _ => ?_
  rw [map_smul, freeMul_toFree (reImParts_mem_sepAll hP hh ε) (reImParts_mem_sepAll hP hh' ε'),
    smul_smul, Fin.sum_univ_add, pow_add, List.ofFn_add]
  have e : ∀ i : Fin n, Fin.castLE (Nat.le_add_right n n') i = Fin.castAdd n' i := fun _ => rfl
  simp only [e, Fin.append_left, Fin.append_right]
  rfl
theorem complexTupleMul (hP : TupleRules.ReImAndMotionOfFns)
    (hW : TupleRules.ComplexTupleRules) : ComplexTupleMul := by
  intro n n' h h' hh hh' hd
  have hc := freeMul_complexTuple hP hh hh'
  refine ⟨?_, append_mem_disjointComplexTuples hh hh' hd, fun _ => hc, ?_⟩
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (combSupp_complexTuple_subset hW hh hx)
    obtain ⟨k, hk⟩ :=
      Set.mem_iUnion.1 (combSupp_complexTuple_subset hW hh' hx')
    exact Set.disjoint_left.1 (hd l k) hl hk
  · rw [hc, sub_self]
    exact Submodule.zero_mem _
theorem freeAction (hA : TupleRules.MotionOnFree)
    (hR : TupleRules.DefinedMulRules) : FreeAction := by
  intro Q Q' u F F'
  refine ⟨?_, (hA _ 1 F).2.1, (hA _ 1 F).2.1, ?_, fun hd => ⟨(hR _ F F' hd).2.2.2.1,
    (hR _ F F' hd).2.2.2.1, (hR _ F F' hd).2.2.2.2, (hR _ F F' hd).2.2.2.2⟩⟩
  · rw [(hA _ _ F).1, ofOrthogonalMatrix_mul]
  · rw [(hA _ _ F).1, (hA _ _ F).1, ofOrthogonalMatrix_mul_transl]
end ComplexTuples
theorem inv_apply_eq_transpose_mulVec (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (x : R4) :
    (EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x = Q.1ᵀ.mulVec x := by
  have hQ : Q.1 * Q.1ᵀ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 Q.2
  have h := EuclidMotion.inv_apply_apply (EuclidMotion.ofOrthogonalMatrix Q) (Q.1ᵀ.mulVec x)
  rwa [EuclidMotion.ofOrthogonalMatrix_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at h
theorem hasDerivAt_line {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (x v : R4) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact ((hf.differentiable (by norm_num)) _).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h := hd.comp_hasDerivAt (0 : ℝ) hl
  exact h
theorem partialDerivR4_eq_fderiv {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (μ : Fin 4) (x : R4) :
    TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.partialDerivR4_eq_fderiv <;> assumption
theorem partialDerivR4_sub {f g : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (μ : Fin 4) (x : R4) :
    TestFunctions.partialDerivR4 μ (f - g) x =
      TestFunctions.partialDerivR4 μ f x - TestFunctions.partialDerivR4 μ g x := by
  rw [EuclideanFunctionals.SharpNormC1.partialDerivR4_sub hf hg μ x,
    partialDerivR4_eq_fderiv hf, partialDerivR4_eq_fderiv hg]
theorem partialDerivR4_actFn (Q : Matrix.orthogonalGroup (Fin 4) ℝ) {f : R4 → ℂ}
    (hf : ContDiff ℝ 1 f) (x : R4) (μ : Fin 4) :
    TestFunctions.partialDerivR4 μ ((EuclidMotion.ofOrthogonalMatrix Q).actFn f) x =
      ∑ ν, (Q.1 μ ν : ℂ) *
        TestFunctions.partialDerivR4 ν f ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x) := by
  set y := (EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x with hy
  set v : R4 := Q.1ᵀ.mulVec (Pi.single μ (1 : ℝ)) with hv
  have e : (fun t : ℝ =>
      (EuclidMotion.ofOrthogonalMatrix Q).actFn f (x + t • Pi.single μ (1 : ℝ))) =
      fun t : ℝ => f (y + t • v) := by
    funext t
    simp only [EuclidMotion.actFn, hy, hv, inv_apply_eq_transpose_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_smul]
  have hvν : ∀ ν, v ν = Q.1 μ ν := fun ν => by
    simp [hv]
  have hsum : v = ∑ ν, v ν • (Pi.single ν (1 : ℝ) : R4) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h₁ : TestFunctions.partialDerivR4 μ ((EuclidMotion.ofOrthogonalMatrix Q).actFn f) x =
      fderiv ℝ f y v := by
    show deriv _ 0 = _
    rw [e]
    exact (hasDerivAt_line hf y v).deriv
  rw [h₁]
  conv_lhs => rw [hsum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, hvν, partialDerivR4_eq_fderiv hf, Complex.real_smul]
theorem gradientTransform : GradientTransform := by
  intro Q f x μ hf
  exact partialDerivR4_actFn Q ((mem_C1c_iff_mem_compactC1 f).1 hf).1 x μ
theorem euclidNormVec_smul (c : ℝ) (z : R4) : euclidNormVec (c • z) = |c| * euclidNormVec z := by apply _root_.YangMills.DeltaSharedProofs.p501477 <;> assumption
theorem euclidNormVec_neg (z : R4) : euclidNormVec (-z) = euclidNormVec z := by
  simp [euclidNormVec]
theorem bddAbove_opNormEuclid_set (A : Matrix (Fin 4) (Fin 4) ℝ) :
    BddAbove ((fun x => Euclidean.euclidNorm (A.mulVec x)) ''
      {x | Euclidean.euclidNorm x ≤ 1}) := by
  let L : R4 →L[ℝ] R4 := LinearMap.toContinuousLinearMap A.mulVecLin
  refine ⟨2 * ‖L‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ 1 := (SeparatedTuplesR4.norm_le_euclidNormVec x).trans hx
  have h₁ : euclidNormVec (A.mulVec x) ≤ 2 * ‖A.mulVec x‖ :=
    SeparatedTuplesR4.euclidNormVec_le_two_mul_norm _
  have h₂ : ‖A.mulVec x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have h₃ : ‖L‖ * ‖x‖ ≤ ‖L‖ := mul_le_of_le_one_right (norm_nonneg _) hx'
  show euclidNormVec (A.mulVec x) ≤ _
  linarith
theorem euclidNormVec_mulVec_le (A : Matrix (Fin 4) (Fin 4) ℝ) (x : R4) :
    euclidNormVec (A.mulVec x) ≤ EuclideanBalls.opNormEuclid A * euclidNormVec x := by
  by_cases hx : euclidNormVec x = 0
  · have h0 : x = 0 := norm_le_zero_iff.1
      ((SeparatedTuplesR4.norm_le_euclidNormVec x).trans hx.le)
    simp [h0, euclidNormVec]
  · have hs : 0 < euclidNormVec x := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
    set s := euclidNormVec x with hsdef
    have hy : Euclidean.euclidNorm (s⁻¹ • x) ≤ 1 := by
      show euclidNormVec (s⁻¹ • x) ≤ 1
      rw [euclidNormVec_smul, abs_of_pos (inv_pos.2 hs), ← hsdef, inv_mul_cancel₀ hs.ne']
    have h₁ : euclidNormVec (A.mulVec (s⁻¹ • x)) ≤ EuclideanBalls.opNormEuclid A :=
      le_csSup (bddAbove_opNormEuclid_set A) ⟨s⁻¹ • x, hy, rfl⟩
    have h₂ : A.mulVec x = s • A.mulVec (s⁻¹ • x) := by
      rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    rw [h₂, euclidNormVec_smul, abs_of_pos hs, mul_comm]
    exact mul_le_mul_of_nonneg_right h₁ hs.le
theorem abs_apply_le_opNormEuclid (A : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    |A μ ν| ≤ EuclideanBalls.opNormEuclid A := by
  have h₁ := euclidNormVec_mulVec_le A (Pi.single ν (1 : ℝ))
  have h₂ : euclidNormVec (Pi.single ν (1 : ℝ) : R4) = 1 := by
    simp [euclidNormVec, Pi.single_apply, ite_pow]
  rw [h₂, mul_one] at h₁
  have h₃ : A.mulVec (Pi.single ν (1 : ℝ)) μ = A μ ν := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h₄ := (norm_le_pi_norm (A.mulVec (Pi.single ν (1 : ℝ))) μ).trans
    ((SeparatedTuplesR4.norm_le_euclidNormVec _).trans h₁)
  rwa [h₃, Real.norm_eq_abs] at h₄
theorem euclidNormVec_inv_apply (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (x : R4) :
    euclidNormVec ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x) = euclidNormVec x := by
  have h := EuclidMotion.euclidNormVec_sub (EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x 0
  have h₀ : (EuclidMotion.ofOrthogonalMatrix Q)⁻¹ (0 : R4) = 0 := by
    rw [inv_apply_eq_transpose_mulVec, Matrix.mulVec_zero]
  rwa [h₀, sub_zero, sub_zero] at h
theorem euclidNormVec_inv_apply_sub_le (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (x : R4) :
    euclidNormVec ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x - x) ≤
      EuclideanBalls.opNormEuclid (Q.1 - 1) * euclidNormVec x := by
  have h := EuclidMotion.euclidNormVec_sub (EuclidMotion.ofOrthogonalMatrix Q)
    ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x) x
  rw [EuclidMotion.apply_inv_apply, EuclidMotion.ofOrthogonalMatrix_apply] at h
  rw [← h, ← euclidNormVec_neg, neg_sub]
  have e : Q.1.mulVec x - x = (Q.1 - 1).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  exact euclidNormVec_mulVec_le _ x
theorem exists_uniform_close {E : Type*} [NormedAddCommGroup E] {u : R4 → E} (hu : Continuous u)
    {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ∀ x, ρ < euclidNormVec x → u x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q : Matrix.orthogonalGroup (Fin 4) ℝ,
      EuclideanBalls.opNormEuclid (Q.1 - 1) ≤ η →
        ∀ x, ‖u ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x) - u x‖ ≤ ε := by
  have hc : HasCompactSupport u := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : R4) ρ) fun x hx => hρ x ?_
    have hx' : ρ < ‖x‖ := by simpa using hx
    exact hx'.trans_le (SeparatedTuplesR4.norm_le_euclidNormVec x)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous hu) ε hε
  refine ⟨δ / (2 * ρ), by positivity, fun Q hQ x => ?_⟩
  by_cases hx : euclidNormVec x ≤ ρ
  · have h₁ : euclidNormVec ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x - x) ≤ δ / (2 * ρ) * ρ :=
      (euclidNormVec_inv_apply_sub_le Q x).trans
        (mul_le_mul hQ hx (Real.sqrt_nonneg _) (by positivity))
    have h₂ : δ / (2 * ρ) * ρ = δ / 2 := by
      field_simp
    have h₃ : dist ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x) x < δ := by
      rw [dist_eq_norm]
      have := SeparatedTuplesR4.norm_le_euclidNormVec ((EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x - x)
      linarith
    have h₄ := hd h₃
    rw [dist_eq_norm] at h₄
    exact h₄.le
  · have hx' := not_le.1 hx
    rw [hρ x hx', hρ _ (by rwa [euclidNormVec_inv_apply]), sub_zero, norm_zero]
    exact hε.le
theorem gradSup_le_two_mul {f : R4 → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ μ x, ‖TestFunctions.partialDerivR4 μ f x‖ ≤ δ) :
    SharpNormC1.gradSup f ≤ 2 * δ := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.gradSup_le_two_mul <;> assumption
theorem continuousAtOne (hP : TupleRules.ReImAndMotionOfFns)
    (hF : SharpNormC1.BoundedAndLipschitz)
    (hB : ∀ c, SharpNormC1.SharpLeGrad c) : ContinuousAtOne := by
  intro c f hf ε hε
  obtain ⟨hcd, hcs⟩ : ContDiff ℝ 1 f ∧ HasCompactSupport f := (mem_C1c_iff_mem_compactC1 f).1 hf
  have hM := c.one_le
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : R4)
  have hρ₀ : 0 < 2 * |R| + 1 := by positivity
  have hout : ∀ x, 2 * |R| + 1 < euclidNormVec x → x ∉ tsupport f := by
    intro x hx hxs
    have h₁ : ‖x‖ ≤ R := by simpa using hR hxs
    have h₂ := SeparatedTuplesR4.euclidNormVec_le_two_mul_norm x
    have h₃ := le_abs_self R
    linarith
  have hpartial : ∀ ν, TestFunctions.partialDerivR4 ν f =
      fun x => fderiv ℝ f x (Pi.single ν (1 : ℝ)) := fun ν =>
    funext (partialDerivR4_eq_fderiv hcd ν)
  have hcont : Continuous fun (x : R4) (ν : Fin 4) => TestFunctions.partialDerivR4 ν f x := by
    refine continuous_pi fun ν => ?_
    rw [hpartial]
    exact (hcd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvan : ∀ x, 2 * |R| + 1 < euclidNormVec x →
      (fun ν : Fin 4 => TestFunctions.partialDerivR4 ν f x) = 0 := by
    intro x hx
    funext ν
    rw [partialDerivR4_eq_fderiv hcd, fderiv_of_notMem_tsupport ℝ (hout x hx)]
    rfl
  have hδ₀ : 0 < ε / (80 * c.M) := by positivity
  set δ := ε / (80 * c.M) with hδdef
  obtain ⟨η₀, hη₀, H₀⟩ := exists_uniform_close hcd.continuous hρ₀
    (fun x hx => image_eq_zero_of_notMem_tsupport (hout x hx)) hδ₀
  obtain ⟨η₁, hη₁, H₁⟩ := exists_uniform_close hcont hρ₀ hvan (half_pos hδ₀)
  choose C hC using (hF f hf).2.1
  have hB₀ : 0 < ∑ ν, |C ν| + 1 := by positivity
  set B := ∑ ν, |C ν| + 1 with hBdef
  have hCB : ∀ ν y, ‖TestFunctions.partialDerivR4 ν f y‖ ≤ B := fun ν y => by
    have h₁ : |C ν| ≤ ∑ ν, |C ν| :=
      Finset.single_le_sum (f := fun ν => |C ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ν)
    have h₂ := hC ν y
    have h₃ := le_abs_self (C ν)
    linarith
  have hη₂ : 0 < δ / (8 * B) := by positivity
  refine ⟨min (min η₀ η₁) (δ / (8 * B)), lt_min (lt_min hη₀ hη₁) hη₂, fun Q hQ => ?_⟩
  have hQ₀ := hQ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hQ₁ := hQ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hQ₂ := hQ.trans (min_le_right _ _)
  have hQf := (mem_C1c_iff_mem_compactC1 _).1
    (hP c (EuclidMotion.ofOrthogonalMatrix Q) 1 f hf).2.2.2.1
  have hg : (EuclidMotion.ofOrthogonalMatrix Q).actFn f - f ∈ C1c ℂ :=
    (mem_C1c_iff_mem_compactC1 _).2 ⟨hQf.1.sub hcd, hQf.2.sub hcs⟩
  have hsup : TestFunctions.uniformNorm ((EuclidMotion.ofOrthogonalMatrix Q).actFn f - f) ≤ δ :=
    ciSup_le fun x => H₀ Q hQ₀ x
  have hder : ∀ μ x, ‖TestFunctions.partialDerivR4 μ
      ((EuclidMotion.ofOrthogonalMatrix Q).actFn f - f) x‖ ≤ δ := by
    intro μ x
    set y := (EuclidMotion.ofOrthogonalMatrix Q)⁻¹ x with hy
    have he : TestFunctions.partialDerivR4 μ ((EuclidMotion.ofOrthogonalMatrix Q).actFn f - f) x =
        ∑ ν, (((Q.1 - 1) μ ν : ℝ) : ℂ) * TestFunctions.partialDerivR4 ν f y +
          (TestFunctions.partialDerivR4 μ f y - TestFunctions.partialDerivR4 μ f x) := by
      rw [partialDerivR4_sub hQf.1 hcd, partialDerivR4_actFn Q hcd]
      have h₁ : ∑ ν, (((Q.1 - 1) μ ν : ℝ) : ℂ) * TestFunctions.partialDerivR4 ν f y =
          ∑ ν, (Q.1 μ ν : ℂ) * TestFunctions.partialDerivR4 ν f y -
            TestFunctions.partialDerivR4 μ f y := by
        have hone : ∀ ν, (((1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν : ℝ) : ℂ) *
            TestFunctions.partialDerivR4 ν f y =
              if μ = ν then TestFunctions.partialDerivR4 ν f y else 0 := by
          intro ν
          rw [Matrix.one_apply]
          split_ifs <;> simp
        simp only [Matrix.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, hone,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [h₁]
      ring
    have hs : ‖∑ ν, (((Q.1 - 1) μ ν : ℝ) : ℂ) * TestFunctions.partialDerivR4 ν f y‖ ≤ δ / 2 := by
      calc ‖∑ ν, (((Q.1 - 1) μ ν : ℝ) : ℂ) * TestFunctions.partialDerivR4 ν f y‖
          ≤ ∑ ν, ‖(((Q.1 - 1) μ ν : ℝ) : ℂ) * TestFunctions.partialDerivR4 ν f y‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _ν : Fin 4, δ / (8 * B) * B := by
            refine Finset.sum_le_sum fun ν _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul ((abs_apply_le_opNormEuclid _ μ ν).trans hQ₂) (hCB ν y)
              (norm_nonneg _) hη₂.le
        _ = δ / 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
            norm_num
    have hd : ‖TestFunctions.partialDerivR4 μ f y - TestFunctions.partialDerivR4 μ f x‖ ≤ δ / 2 := by
      have h₁ := H₁ Q hQ₁ x
      have h₂ := norm_le_pi_norm
        ((fun ν => TestFunctions.partialDerivR4 ν f y) -
          fun ν => TestFunctions.partialDerivR4 ν f x) μ
      exact h₂.trans h₁
    rw [he]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hs hd
      _ = δ := by ring
  have hgrad := gradSup_le_two_mul hδ₀.le hder
  refine (hB c _ hg).2.trans (max_le (hsup.trans ?_) ?_)
  · rw [hδdef]
    exact div_le_self hε.le (by linarith)
  · have h₁ : 40 * c.M * SharpNormC1.gradSup
        ((EuclidMotion.ofOrthogonalMatrix Q).actFn f - f) ≤ 40 * c.M * (2 * δ) :=
      mul_le_mul_of_nonneg_left hgrad (by linarith)
    have h₂ : 40 * c.M * (2 * δ) = ε := by
      rw [hδdef]
      field_simp
      norm_num
    linarith
theorem holds_of_rules (hT : TupleRules.TupleSpanActionRules) (hS : SharpNormC1.Main)
    (hM : ProductMotions.MotionFacts) : Holds := by
  obtain ⟨hP, hI, hA, -, -, hR, -, hW, -⟩ := hT
  obtain ⟨hF, hC⟩ := hS
  obtain ⟨hM₁, -, -, hM₄, hM₅⟩ := hM
  exact ⟨functionAction hP, supportBallDistanceTuple hP hI, normInvariance hP,
    translationCompat, rotationRules hM₁, plateRotation hM₄ hM₅,
    complexTupleImages hP hW, complexTupleMul hP hW, freeAction hA hR,
    gradientTransform, continuousAtOne hP hF fun c => (hC c).1⟩
end YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance
end
