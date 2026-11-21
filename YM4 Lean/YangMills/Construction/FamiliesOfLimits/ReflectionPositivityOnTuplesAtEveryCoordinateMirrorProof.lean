import YangMills.Construction.FamiliesOfLimits.ReflectionPositivityOnTuplesAtEveryCoordinateMirror
import YangMills.Construction.TorusOrFourSpace.LinearExtensionToTensors
import Mathlib
set_option autoImplicit false
open YangMills.Construction.AmbientPoints YangMills.Construction.ToriLimits YangMills.Construction.ToriLimits.GrowingVolumeLimits
open YangMills.Construction.TorusTransport.TestFunctionOrders
open YangMills.Construction.CentredTensorMoments (realTupleTensor)
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits.CoordinateMirrorPositivity
variable {s : Conventions.StandingParameters} {Y : PeriodicSpace.Params}
theorem mem_sepC1Tuples_of_mem {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) :
    f ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean n := by
  have h := (ToriLimits.mem_sepTuplesR4_iff s f).1 hf
  exact (BallTuples.mem_sepC1Tuples_euclidean_iff f).2 ⟨h.1, h.2.1, h.2.2⟩
theorem mem_positiveSide_axisMirror_iff (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    x ∈ AmbientMirror.positiveSide s .euclidean (axisMirror μ c) ↔ c < x μ := by
  change c < LatticeConventions.euclidDot (LatticeConventions.basisVector μ) x ↔ c < x μ
  rw [AmbientMirror.euclidDot_basisVector]
theorem reflect_axisMirror (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    (AmbientMirror.reflect s .euclidean (axisMirror μ c) x : Fin 4 → ℝ) =
      (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ)) x := by
  have hq := AmbientMirror.sqNorm_basisVector μ (Or.inl ⟨μ, rfl⟩)
  change x - (2 * (LatticeConventions.euclidDot (LatticeConventions.basisVector μ) x - c)) •
      InfiniteLattice.EuclideanMirrors.ReflNormal.dual
        ⟨LatticeConventions.basisVector μ, Or.inl ⟨μ, rfl⟩⟩ =
    ReflectionPositivity.AxisMirror.euclidReflect μ c x
  rw [InfiniteLattice.EuclideanMirrors.ReflNormal.dual, hq, AmbientMirror.euclidDot_basisVector,
    inv_one, one_smul]
  simp only [ReflectionPositivity.AxisMirror.euclidReflect, LatticeConventions.basisVector,
    PeriodicLattice.coordVec]
theorem realTupleTensor_mem_above (μ : Fin 4) (c : ℝ) (X : PositiveSideTuples s μ c) :
    realTupleTensor X.1.2 ∈
      sepTensorSubmodule Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) X.1.1 := by
  obtain ⟨⟨q, f⟩, hX, ho⟩ := X
  cases q with
  | zero => exact Submodule.mem_top
  | succ q =>
    change realTupleTensor f ∈
      sepTensorSpanOn Y (q + 1) (openHalfSpace μ c : Set (Fin 4 → ℝ))
    refine Submodule.subset_span ⟨f, ⟨mem_sepC1Tuples_of_mem hX, fun i => ?_⟩, rfl⟩
    have hsup : PeriodicSpace.Kind.supportQ Y .euclidean (f i) = tsupport (f i) :=
      (BallTuples.supportQ_euclidean Y (f i)).trans
        (BallTuples.tsupport_pt_euclidean s (f i)).symm
    intro x hx
    exact (mem_positiveSide_axisMirror_iff μ c x).1 (ho i (hsup.subset hx))
theorem realTupleTensor_mem_univ {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean n) :
    realTupleTensor f ∈ sepTensorSubmodule Y Set.univ n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ q => exact realTensor_mem_sepTensorSpanOn Y ⟨f, hf⟩
theorem momentExtensionAt_of_mem (Ξ : EuclidHierarchy Y) {n : ℕ} {A : OrderedTestFun n}
    (h : A ∈ sepTensorSubmodule Y Set.univ n) :
    momentExtensionAt Ξ ⟨n, A⟩ = momentExtension Ξ n ⟨A, h⟩ :=
  dif_pos h
theorem momentExtensionAt_sum (Ξ : EuclidHierarchy Y) {ι : Type*} (n : ℕ) (T : Finset ι)
    (b : ι → ℂ) (A : ι → OrderedTestFun n)
    (hA : ∀ t ∈ T, A t ∈ sepTensorSubmodule Y Set.univ n) :
    momentExtensionAt Ξ ⟨n, ∑ t ∈ T, b t • A t⟩ = ∑ t ∈ T, b t * momentExtensionAt Ξ ⟨n, A t⟩ := by
  have hs : ∑ t ∈ T, b t • A t ∈ sepTensorSubmodule Y Set.univ n :=
    Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (hA t ht)
  have he : (⟨∑ t ∈ T, b t • A t, hs⟩ : sepTensorSubmodule Y Set.univ n) =
      ∑ t ∈ T.attach, b t.1 • (⟨A t.1, hA t.1 t.2⟩ : sepTensorSubmodule Y Set.univ n) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact (Finset.sum_attach T fun t => b t • A t).symm
  rw [momentExtensionAt_of_mem Ξ hs, he, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_)
    (Finset.sum_attach T fun t => b t * momentExtensionAt Ξ ⟨n, A t⟩)
  rw [map_smul, momentExtensionAt_of_mem Ξ (hA t.1 t.2), smul_eq_mul]
theorem momentExtensionAt_sum_sum (Ξ : EuclidHierarchy Y) {ι κ : Type*} (n : ℕ) (I : Finset ι)
    (K : Finset κ) (b : ι → κ → ℂ) (A : ι → κ → OrderedTestFun n)
    (hA : ∀ i ∈ I, ∀ k ∈ K, A i k ∈ sepTensorSubmodule Y Set.univ n) :
    momentExtensionAt Ξ ⟨n, ∑ i ∈ I, ∑ k ∈ K, b i k • A i k⟩ =
      ∑ i ∈ I, ∑ k ∈ K, b i k * momentExtensionAt Ξ ⟨n, A i k⟩ := by
  rw [← Finset.sum_product' I K (fun i k => b i k • A i k),
    ← Finset.sum_product' I K (fun i k => b i k * momentExtensionAt Ξ ⟨n, A i k⟩)]
  exact momentExtensionAt_sum Ξ n (I ×ˢ K) (fun p => b p.1 p.2) (fun p => A p.1 p.2)
    fun p hp => hA _ (Finset.mem_product.1 hp).1 _ (Finset.mem_product.1 hp).2
theorem existsUnique_momentExtension (hL : PeriodicSpace.Kind.TensorExtension.Claim)
    (Ξ : EuclidHierarchy Y) (q : ℕ) (hq : 1 ≤ q) :
    ∃! T, IsMomentExtension Ξ (q := q) T := by
  obtain ⟨T, hT, hu⟩ := (((hL Y .euclidean).2 Ξ).2 q hq).2
  let e := LinearEquiv.ofEq _ _ (sepTensorSpanOn_univ Y q)
  refine ⟨T ∘ₗ e.toLinearMap, fun X => hT X, fun T₁ h₁ => ?_⟩
  have h := hu (T₁ ∘ₗ e.symm.toLinearMap) fun f => h₁ f
  ext x
  have hx := congrArg (fun R => R (e x)) h
  simpa using hx
theorem momentExtension_spec (hL : PeriodicSpace.Kind.TensorExtension.Claim)
    (Ξ : EuclidHierarchy Y) (q : ℕ) :
    IsMomentExtension Ξ (momentExtension Ξ (q + 1)) :=
  Classical.epsilon_spec (p := IsMomentExtension Ξ (q := q + 1))
    (existsUnique_momentExtension hL Ξ (q + 1) (by omega)).exists
theorem momentExtensionAt_realTupleTensor (hL : PeriodicSpace.Kind.TensorExtension.Claim)
    (Ξ : EuclidHierarchy Y) {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean n) :
    momentExtensionAt Ξ ⟨n, realTupleTensor f⟩ = ((Ξ.partitionMoment ⟨f, hf⟩ : ℝ) : ℂ) := by
  rw [momentExtensionAt_of_mem Ξ (realTupleTensor_mem_univ hf)]
  cases n with
  | zero =>
    rw [Ξ.partitionMoment_zero]
    simp [momentExtension, ReflectionSpaces.orderZeroMoments,
      realTupleTensor, CentredTensorMoments.tupleTensor]
  | succ q => exact momentExtension_spec hL Ξ q ⟨f, hf⟩
def singleSeq (A : GradedTestFun) : TestFamily := Pi.single A.1 A.2
theorem eq_mk_singleSeq (A : GradedTestFun) {n : ℕ} (h : A.1 = n) :
    A = ⟨n, singleSeq A n⟩ := by
  obtain ⟨m, b⟩ := A
  obtain rfl : m = n := h
  simp [singleSeq]
theorem singleSeq_add (m : ℕ) {a b c : OrderedTestFun m} (h : a = b + c) :
    singleSeq ⟨m, a⟩ = singleSeq ⟨m, b⟩ + singleSeq ⟨m, c⟩ := by
  subst h
  exact Pi.single_add m b c
theorem singleSeq_smul (m : ℕ) (z : ℂ) {a b : OrderedTestFun m} (h : a = z • b) :
    singleSeq ⟨m, a⟩ = z • singleSeq ⟨m, b⟩ := by
  subst h
  funext n
  by_cases hn : n = m
  · subst hn
    simp [singleSeq]
  · simp [singleSeq, Pi.single_eq_of_ne hn]
def gradedTensorBilin (q q' : ℕ) : OrderedTestFun q →ₗ[ℂ] OrderedTestFun q' →ₗ[ℂ] TestFamily :=
  LinearMap.mk₂ ℂ (fun a b => singleSeq (gradedTensor ⟨q, a⟩ ⟨q', b⟩))
    (fun a a' b => by
      rcases q with _ | q <;> rcases q' with _ | q'
      · exact singleSeq_add _ (add_mul _ _ _)
      · exact singleSeq_add _ (funext fun x => add_mul _ _ _)
      · exact singleSeq_add _ (funext fun x => mul_add _ _ _)
      · exact singleSeq_add _ (funext fun x => add_mul _ _ _))
    (fun z a b => by
      rcases q with _ | q <;> rcases q' with _ | q'
      · exact singleSeq_smul _ z (mul_assoc _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_assoc _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_left_comm _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_assoc _ _ _))
    (fun a b b' => by
      rcases q with _ | q <;> rcases q' with _ | q'
      · exact singleSeq_add _ (mul_add _ _ _)
      · exact singleSeq_add _ (funext fun x => mul_add _ _ _)
      · exact singleSeq_add _ (funext fun x => add_mul _ _ _)
      · exact singleSeq_add _ (funext fun x => mul_add _ _ _))
    (fun z a b => by
      rcases q with _ | q <;> rcases q' with _ | q'
      · exact singleSeq_smul _ z (mul_left_comm _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_left_comm _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_assoc _ _ _)
      · exact singleSeq_smul _ z (funext fun x => mul_left_comm _ _ _))
theorem gradedTensorBilin_apply (q q' : ℕ) (a : OrderedTestFun q) (b : OrderedTestFun q') :
    gradedTensorBilin q q' a b = singleSeq (gradedTensor ⟨q, a⟩ ⟨q', b⟩) :=
  rfl
theorem gradedTensor_realTupleTensor (P R : FunctionTuple s .euclidean) :
    gradedTensor ⟨P.1, realTupleTensor P.2⟩ ⟨R.1, realTupleTensor R.2⟩ =
      ⟨(tupleAppend P R).1, realTupleTensor (tupleAppend P R).2⟩ := by
  obtain ⟨p, f⟩ := P
  obtain ⟨q, g⟩ := R
  rcases p with _ | p
  · have he : tupleAppend (⟨0, f⟩ : FunctionTuple s .euclidean) ⟨q, g⟩ = ⟨q, g⟩ := by
      have hf : (⟨0, f⟩ : FunctionTuple s .euclidean) = nilTuple s .euclidean :=
        Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))
      rw [hf, nilTuple_tupleAppend]
    rw [he]
    rcases q with _ | q
    · exact congrArg (Sigma.mk 0) (one_mul _)
    · exact congrArg (Sigma.mk (q + 1)) (funext fun x => one_mul _)
  · rcases q with _ | q
    · have he : tupleAppend (⟨p + 1, f⟩ : FunctionTuple s .euclidean) ⟨0, g⟩ = ⟨p + 1, f⟩ := by
        have hg : (⟨0, g⟩ : FunctionTuple s .euclidean) = nilTuple s .euclidean :=
          Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))
        rw [hg, tupleAppend_nilTuple]
      rw [he]
      exact congrArg (Sigma.mk (p + 1)) (funext fun x => one_mul _)
    · refine congrArg (Sigma.mk (p + 1 + (q + 1))) ?_
      refine (tensor_prodTensor _ _).trans ?_
      change prodTensor _ = prodTensor fun l x =>
        (((tupleAppend (⟨p + 1, f⟩ : FunctionTuple s .euclidean) ⟨q + 1, g⟩).2 l x : ℝ) : ℂ)
      refine congrArg prodTensor (funext fun i => ?_)
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · simp [tupleAppend, Fin.append_left]
      · simp [tupleAppend, Fin.append_right]
theorem gradedTensorBilin_tensorSeq {q q' : ℕ} {P R : FunctionTuple s .euclidean}
    (hP : P.1 = q) (hR : R.1 = q') :
    gradedTensorBilin q q' (tensorSeq P q) (tensorSeq R q') =
      tensorSeq (tupleAppend P R) := by
  subst hP hR
  rw [gradedTensorBilin_apply]
  simp only [tensorSeq, Pi.single_eq_same]
  rw [gradedTensor_realTupleTensor]
  rfl
theorem conjReflectTest_zero (μ : Fin 4) (c : ℝ) (q : ℕ) :
    CentredTensorMoments.conjReflectTest μ c (0 : OrderedTestFun q) = 0 := by
  cases q with
  | zero => exact map_zero _
  | succ q => exact funext fun x => map_zero (starRingEnd ℂ)
theorem conjReflectTest_add (μ : Fin 4) (c : ℝ) {q : ℕ} (a b : OrderedTestFun q) :
    CentredTensorMoments.conjReflectTest μ c (a + b) =
      CentredTensorMoments.conjReflectTest μ c a +
        CentredTensorMoments.conjReflectTest μ c b := by
  cases q with
  | zero => exact map_add (starRingEnd ℂ) _ _
  | succ q => exact funext fun x => map_add (starRingEnd ℂ) _ _
theorem conjReflectTest_smul (μ : Fin 4) (c : ℝ) {q : ℕ} (z : ℂ) (a : OrderedTestFun q) :
    CentredTensorMoments.conjReflectTest μ c (z • a) =
      conj z • CentredTensorMoments.conjReflectTest μ c a := by
  cases q with
  | zero => exact map_mul (starRingEnd ℂ) _ _
  | succ q => exact funext fun x => map_mul (starRingEnd ℂ) _ _
theorem conjReflectTest_sum (μ : Fin 4) (c : ℝ) {q : ℕ} {ι : Type*} (T : Finset ι) (b : ι → ℂ)
    (A : ι → OrderedTestFun q) :
    CentredTensorMoments.conjReflectTest μ c (∑ t ∈ T, b t • A t) =
      ∑ t ∈ T, conj (b t) • CentredTensorMoments.conjReflectTest μ c (A t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using conjReflectTest_zero μ c q
  | insert t T ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht, conjReflectTest_add, conjReflectTest_smul, ih]
theorem conjReflectTest_realTupleTensor (μ : Fin 4) (c : ℝ) (X : FunctionTuple s .euclidean) :
    CentredTensorMoments.conjReflectTest μ c (realTupleTensor X.2) =
      realTupleTensor (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) X).2 := by
  obtain ⟨q, f⟩ := X
  cases q with
  | zero => exact map_one (starRingEnd ℂ)
  | succ q =>
    funext x
    change conj (∏ i, ((f i _ : ℝ) : ℂ)) =
      ∏ i, ((AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) ⟨q + 1, f⟩).2 i (x i) : ℂ)
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.conj_ofReal]
    have h := congrFun
      (AmbientMirror.transportTuple_reflect s .euclidean (axisMirror μ c) f i) (x i)
    refine congrArg Complex.ofReal (Eq.trans ?_ h.symm)
    exact congrArg (f i) (reflect_axisMirror μ c (x i)).symm
theorem conjReflectTest_tensorSeq (μ : Fin 4) (c : ℝ) (X : FunctionTuple s .euclidean) (q : ℕ) :
    CentredTensorMoments.conjReflectTest μ c (tensorSeq X q) =
      tensorSeq (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) X) q := by
  by_cases h : q = X.1
  · subst h
    have h₂ : (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) X).1 = X.1 := rfl
    simp only [tensorSeq]
    rw [Pi.single_eq_same]
    refine (conjReflectTest_realTupleTensor μ c X).trans ?_
    exact (Pi.single_eq_same (M := fun q => OrderedTestFun q) _ _).symm
  · have h₂ : q ≠ (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) X).1 := h
    simp only [tensorSeq]
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h₂]
    exact conjReflectTest_zero μ c q
theorem combinationSeq_mem {r : ℕ} (μ : Fin 4) (c : ℝ) (X : Fin r → PositiveSideTuples s μ c)
    (a : Fin r → ℂ) :
    combinationSeq (fun i => (X i).1) a ∈ finiteSeqsAbove Y μ c := by
  refine ⟨fun q => Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_,
    (Finset.univ.sup fun i => (X i).1.1) + 1, fun q hq => ?_⟩
  · have hq : (X i).1.1 = q := (Finset.mem_filter.1 hi).2
    subst hq
    simp only [tensorSeq]
    rw [Pi.single_eq_same]
    exact realTupleTensor_mem_above μ c (X i)
  · refine Finset.sum_eq_zero fun i hi => ?_
    have h1 : (X i).1.1 = q := (Finset.mem_filter.1 hi).2
    have h2 : (X i).1.1 ≤ Finset.univ.sup fun i => (X i).1.1 :=
      Finset.le_sup (f := fun i => (X i).1.1) (Finset.mem_univ i)
    omega
theorem thetaReflect_combinationSeq {r : ℕ} (μ : Fin 4) (c : ℝ)
    (X : Fin r → FunctionTuple s .euclidean) (a : Fin r → ℂ) (q : ℕ) :
    thetaReflect μ c (combinationSeq X a) q =
      ∑ i with (X i).1 = q, conj (a i) •
        tensorSeq (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) (X i)) q := by
  change CentredTensorMoments.conjReflectTest μ c
    (∑ i with (X i).1 = q, a i • tensorSeq (X i) q) = _
  rw [conjReflectTest_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [conjReflectTest_tensorSeq]
theorem gradedTensorBilin_sum (q q' : ℕ) {ι κ : Type*} (I : Finset ι) (K : Finset κ) (u : ι → ℂ)
    (v : κ → ℂ) (P : ι → OrderedTestFun q) (R : κ → OrderedTestFun q') :
    gradedTensorBilin q q' (∑ i ∈ I, u i • P i) (∑ k ∈ K, v k • R k) =
      ∑ i ∈ I, ∑ k ∈ K, (u i * v k) • gradedTensorBilin q q' (P i) (R k) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_)
  rw [mul_comm]
theorem reflectedTensor_combinationSeq {r : ℕ} (μ : Fin 4) (c : ℝ)
    (X : Fin r → PositiveSideTuples s μ c) (a : Fin r → ℂ) (q q' : ℕ) :
    reflectedTensor μ c (combinationSeq (fun i => (X i).1) a)
        (combinationSeq (fun i => (X i).1) a) q q' =
      ⟨q + q', ∑ i with (X i).1.1 = q, ∑ k with (X k).1.1 = q', (conj (a i) * a k) •
        tensorSeq (AmbientMirror.reflectAppend s .euclidean (axisMirror μ c) (X i) (X k)).1
          (q + q')⟩ := by
  refine (eq_mk_singleSeq _ (gradedTensor_fst _ _)).trans ?_
  refine congrArg (Sigma.mk (q + q')) ?_
  change gradedTensorBilin q q' (thetaReflect μ c (combinationSeq (fun i => (X i).1) a) q)
    (∑ k with (X k).1.1 = q', a k • tensorSeq (X k).1 q') (q + q') = _
  rw [thetaReflect_combinationSeq, gradedTensorBilin_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hb := gradedTensorBilin_tensorSeq
    (P := AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) (X i).1) (R := (X k).1)
    (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hk).2
  rw [Pi.smul_apply, hb]
  rfl
theorem partitionMoment_eq_centredMap {Ξ : EuclidHierarchy Y} {S : SeparatedTupleFunctions s}
    (hv : LimitFamilyAsVolumeLimit.HierarchyAgrees Ξ S)
    (X : allSeparatedTuples s .euclidean)
    (hX : X.1.2 ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean X.1.1) :
    Ξ.partitionMoment ⟨X.1.2, hX⟩ = TupleHilbert.centredMap S X := by
  unfold PeriodicSpace.Kind.Hierarchy.partitionMoment TupleHilbert.centredMap
    AmbientPoints.centredOfMaps
  refine Eq.trans ?_ (Finset.sum_attach (SetPartition.singletonFree X.1.1) _)
  refine Finset.sum_congr rfl fun π _ => ?_
  refine Eq.trans ?_ (Finset.prod_attach π.1.parts _)
  refine Finset.prod_congr rfl fun J _ => ?_
  have hc := PeriodicSpace.two_le_card_of_mem_partitionsNoSingletons π.2 J.2
  unfold AmbientPoints.mapFamilyBlockFactor
  rw [dif_pos hc]
  change _ = (S _ hc _).re
  rw [hv _ hc _ (mem_sepC1Tuples_of_mem (restrictSeparated ⟨X.1.2, X.2⟩ J.1).2),
    Complex.ofReal_re]
  rfl
theorem tensorSeq_mem (Z : allSeparatedTuples s .euclidean) (n : ℕ) :
    tensorSeq Z.1 n ∈ sepTensorSubmodule Y Set.univ n := by
  by_cases h : n = Z.1.1
  · subst h
    simp only [tensorSeq]
    rw [Pi.single_eq_same]
    exact realTupleTensor_mem_univ (mem_sepC1Tuples_of_mem Z.2)
  · simp only [tensorSeq]
    rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _
theorem momentExtensionAt_tensorSeq (hL : PeriodicSpace.Kind.TensorExtension.Claim)
    {Ξ : EuclidHierarchy Y} {S : SeparatedTupleFunctions s}
    (hv : LimitFamilyAsVolumeLimit.HierarchyAgrees Ξ S)
    (Z : allSeparatedTuples s .euclidean) {n : ℕ} (h : Z.1.1 = n) :
    momentExtensionAt Ξ ⟨n, tensorSeq Z.1 n⟩ = ((TupleHilbert.centredMap S Z : ℝ) : ℂ) := by
  subst h
  simp only [tensorSeq]
  rw [Pi.single_eq_same, momentExtensionAt_realTupleTensor hL Ξ (mem_sepC1Tuples_of_mem Z.2),
    partitionMoment_eq_centredMap hv]
theorem finsum_fibres_eq_sum {r : ℕ} (key : Fin r → ℕ) (t : Fin r → Fin r → ℂ) :
    ∑ᶠ p : ℕ × ℕ, ∑ i with key i = p.1, ∑ k with key k = p.2, t i k = ∑ i, ∑ k, t i k := by
  classical
  let g : Fin r × Fin r → ℕ × ℕ := fun x => (key x.1, key x.2)
  have hG : ∀ p : ℕ × ℕ, ∑ i with key i = p.1, ∑ k with key k = p.2, t i k =
      ∑ x with g x = p, t x.1 x.2 := fun p => by
    rw [← Finset.sum_product']
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨i, k⟩
    simp [g, Prod.ext_iff]
  have hsup : Function.support (fun p : ℕ × ℕ => ∑ x with g x = p, t x.1 x.2) ⊆
      ((Finset.univ.image g : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := fun p hp => by
    by_contra h
    refine hp (Finset.sum_eq_zero fun x hx => ?_)
    exact absurd (Finset.mem_coe.2 (Finset.mem_image.2 ⟨x, Finset.mem_univ x,
      (Finset.mem_filter.1 hx).2⟩)) h
  rw [finsum_congr hG, finsum_eq_sum_of_support_subset _ hsup,
    Finset.sum_fiberwise_of_maps_to fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)]
  exact Fintype.sum_prod_type _
theorem reflectionForm_combinationSeq (hL : PeriodicSpace.Kind.TensorExtension.Claim)
    {Ξ : EuclidHierarchy Y} {S : SeparatedTupleFunctions s}
    (hv : LimitFamilyAsVolumeLimit.HierarchyAgrees Ξ S)
    {r : ℕ} (μ : Fin 4) (c : ℝ) (X : Fin r → PositiveSideTuples s μ c) (a : Fin r → ℂ) :
    reflectionForm Ξ μ c (combinationSeq (fun i => (X i).1) a)
        (combinationSeq (fun i => (X i).1) a) =
      AmbientMirror.gramSum s .euclidean (axisMirror μ c) (TupleHilbert.centredMap S) X a := by
  unfold reflectionForm AmbientMirror.gramSum
  rw [← finsum_fibres_eq_sum (fun i => (X i).1.1)]
  refine finsum_congr fun p => ?_
  rw [reflectedTensor_combinationSeq,
    momentExtensionAt_sum_sum Ξ _ _ _ _ _ fun _ _ _ _ => tensorSeq_mem _ _]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
  rw [momentExtensionAt_tensorSeq hL hv _ (by
    change (X i).1.1 + (X k).1.1 = p.1 + p.2
    rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hk).2])]
theorem holds (hL : PeriodicSpace.Kind.TensorExtension.Claim) : Holds := by
  intro D T C J Ξ cl s S hv
  obtain ⟨u, hu⟩ := cl.existenceAndBounds.exists_memberFamily
  have hold : ∀ (μ : Fin 4) (c : ℝ) (r : ℕ) (X : Fin r → PositiveSideTuples s μ c)
      (a : Fin r → ℂ), ExpansionsHold Ξ (TupleHilbert.centredMap S) μ c X a :=
    fun μ c r X a =>
    { reflected_eq := thetaReflect_combinationSeq μ c _ a
      tensor_eq := reflectedTensor_combinationSeq μ c X a
      sum_eq := reflectionForm_combinationSeq hL hv μ c X a
      sum_nonneg := by
        rw [← reflectionForm_combinationSeq hL hv μ c X a]
        exact (cl.osPositivity.holdsAtMirrors u hu μ c).2.1.2.2.2 _
          (combinationSeq_mem μ c X a) }
  refine ⟨partitionMoment_eq_centredMap hv, fun q hq => existsUnique_momentExtension hL Ξ q hq,
    fun q => momentExtension_spec hL Ξ q, fun μ c => ⟨hold μ c, fun r X a => ?_⟩⟩
  obtain ⟨x, hx, hxe⟩ := (hold μ c r X a).sum_nonneg
  rw [← hxe]
  exact ⟨Complex.ofReal_im x, by simpa using hx⟩
end YangMills.Construction.FamiliesOfLimits.CoordinateMirrorPositivity
end
