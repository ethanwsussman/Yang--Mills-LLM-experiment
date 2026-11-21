import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import Reconstruction.Continuum.CompositionTranslationsAndTensors
import Reconstruction.Continuum.IsometriesAreMotionsAndTheTwoFormsOfSeparatedTuplesAgree
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.MotionComposition
theorem invFun_compMotion (r r' : Motions.RigidMotion) (u : Fin 4 → ℝ) :
    (UpperHalfTensors.compMotion r r').invFun u = r'.invFun (r.invFun u) := by
  have h := (UpperHalfTensors.compMotion r r').invFun_toFun (r'.invFun (r.invFun u))
  rwa [UpperHalfTensors.compMotion_toFun, Motions.RigidMotion.toFun_invFun,
    Motions.RigidMotion.toFun_invFun] at h
theorem actOnFun_actOnFun {n : ℕ} {F : Type*} (r r' : Motions.RigidMotion)
    (φ : TestSpaces.PointTuple n → F) :
    Motions.actOnFun r (Motions.actOnFun r' φ) =
      Motions.actOnFun (UpperHalfTensors.compMotion r r') φ := by
  funext x
  simp only [Motions.actOnFun, invFun_compMotion]
theorem semiconj_list_foldr {β γ : Type*} (C : β → β) (l : List γ) (T : γ → β → β)
    (h : ∀ a, Function.Semiconj C (T a) (T a)) :
    Function.Semiconj C (fun b => l.foldr T b) (fun b => l.foldr T b) := by
  induction l with
  | nil => intro b; rfl
  | cons a l ih =>
    intro b
    exact (h a _).trans (congrArg (T a) (ih b))
section Derivatives
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def shiftAll (w : Fin 4 → ℝ) (x : TestSpaces.PointTuple n) : TestSpaces.PointTuple n :=
  fun i => x i - w
theorem semiconj_coordDeriv (w : Fin 4 → ℝ) (i : Fin n) (μ : Fin 4) :
    Function.Semiconj (fun g : TestSpaces.PointTuple n → F => g ∘ shiftAll w)
      (TestSpaces.coordDeriv i μ) (TestSpaces.coordDeriv i μ) := by
  intro g
  funext x
  simp only [TestSpaces.coordDeriv, Function.comp, lineDeriv]
  congr 1
  funext t
  congr 1
  funext j
  simp only [shiftAll, Pi.add_apply]
  abel
theorem multiDeriv_comp_shiftAll (w : Fin 4 → ℝ) (α : TestSpaces.MultiIdx4 n)
    (g : TestSpaces.PointTuple n → F) :
    TestSpaces.multiDeriv α (g ∘ shiftAll w) = TestSpaces.multiDeriv α g ∘ shiftAll w := by
  refine (semiconj_list_foldr (fun g : TestSpaces.PointTuple n → F => g ∘ shiftAll w)
    (List.finRange n) _ ?_ g).symm
  intro i
  refine semiconj_list_foldr _ (List.finRange 4) _ fun μ => ?_
  exact (semiconj_coordDeriv w i μ).iterate_right _
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem translateFun_eq_comp_shiftAll (w : Fin 4 → ℝ) (φ : TestSpaces.PointTuple n → F) :
    SmoothSeparatedTuples.translateFun w φ = φ ∘ shiftAll w :=
  funext fun x => SmoothSeparatedTuples.translateFun_apply w φ x
theorem multiDeriv_translateFun (w : Fin 4 → ℝ) (α : TestSpaces.MultiIdx4 n)
    (φ : TestSpaces.PointTuple n → F) (x : TestSpaces.PointTuple n) :
    TestSpaces.multiDeriv α (SmoothSeparatedTuples.translateFun w φ) x =
      TestSpaces.multiDeriv α φ (shiftAll w x) := by
  rw [translateFun_eq_comp_shiftAll, multiDeriv_comp_shiftAll]
  rfl
end Derivatives
theorem euclidNormVec_sq (u : Fin 4 → ℝ) : TorusMetric.euclidNormVec u ^ 2 = ∑ μ, u μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem euclidNormVec_sq_le_two_mul (u v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec u ^ 2 ≤
      2 * TorusMetric.euclidNormVec (u - v) ^ 2 + 2 * TorusMetric.euclidNormVec v ^ 2 := by
  simp only [euclidNormVec_sq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (u μ - 2 * v μ)]
theorem one_add_tupleNorm_sq_le {n : ℕ} (v : Fin 4 → ℝ) (x : TestSpaces.PointTuple n) :
    1 + TestSpaces.tupleNorm x ^ 2 ≤
      (2 + 2 * (n : ℝ) * TorusMetric.euclidNormVec v ^ 2) *
        (1 + TestSpaces.tupleNorm (shiftAll v x) ^ 2) := by
  have hsum : TestSpaces.tupleNorm x ^ 2 ≤
      2 * TestSpaces.tupleNorm (shiftAll v x) ^ 2 +
        2 * (n : ℝ) * TorusMetric.euclidNormVec v ^ 2 := by
    rw [TestSpaces.tupleNorm_sq, TestSpaces.tupleNorm_sq, Finset.mul_sum]
    calc ∑ i, TorusMetric.euclidNormVec (x i) ^ 2
        ≤ ∑ i, (2 * TorusMetric.euclidNormVec (shiftAll v x i) ^ 2 +
            2 * TorusMetric.euclidNormVec v ^ 2) :=
          Finset.sum_le_sum fun i _ => euclidNormVec_sq_le_two_mul (x i) v
      _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hB : 0 ≤ TestSpaces.tupleNorm (shiftAll v x) ^ 2 := sq_nonneg _
  have hV : 0 ≤ 2 * (n : ℝ) * TorusMetric.euclidNormVec v ^ 2 := by positivity
  nlinarith [mul_nonneg hV hB]
theorem weightedSeminorm_translateFun_le {n : ℕ} (k : ℕ) (v : Fin 4 → ℝ)
    (φ : TestSpaces.PointTuple n → ℂ) :
    TestSpaces.weightedSeminorm k (SmoothSeparatedTuples.translateFun v φ) ≤
      ENNReal.ofReal (translationFactor n k v) * TestSpaces.weightedSeminorm k φ := by
  have hC : 0 ≤ translationFactor n k v := by
    unfold translationFactor
    positivity
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  rw [multiDeriv_translateFun]
  set y := shiftAll v x
  set d := ‖TestSpaces.multiDeriv α φ y‖
  have hw : (1 + TestSpaces.tupleNorm x ^ 2) ^ ((k : ℝ) / 2) ≤
      translationFactor n k v * (1 + TestSpaces.tupleNorm y ^ 2) ^ ((k : ℝ) / 2) := by
    rw [translationFactor, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (one_add_tupleNorm_sq_le v x) (by positivity)
  calc ENNReal.ofReal ((1 + TestSpaces.tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * d)
      ≤ ENNReal.ofReal
          (translationFactor n k v * ((1 + TestSpaces.tupleNorm y ^ 2) ^ ((k : ℝ) / 2) * d)) := by
        rw [← mul_assoc]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
    _ = ENNReal.ofReal (translationFactor n k v) *
          ENNReal.ofReal ((1 + TestSpaces.tupleNorm y ^ 2) ^ ((k : ℝ) / 2) * d) :=
        ENNReal.ofReal_mul hC
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        unfold TestSpaces.weightedSeminorm
        exact le_iSup_of_le y (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
theorem translateFun_mem_schwartzSet (hOps : TestFunctionOps.OperationsStatement)
    {n : ℕ} (hn : 0 < n) (w : Fin 4 → ℝ) {φ : TestSpaces.PointTuple n → ℂ}
    (hφ : φ ∈ TestSpaces.schwartzSet n) :
    SmoothSeparatedTuples.translateFun w φ ∈ TestSpaces.schwartzSet n :=
  ((hOps.1 n 1 hn one_pos (Equiv.refl _)
    (SmoothSeparatedTuples.pureTranslation w)).2.1 φ hφ).1.2.1
theorem add_mem_positiveTimeLocus {n : ℕ} {w : Fin 4 → ℝ} (hw : 0 ≤ w 3)
    {x : TestSpaces.PointTuple n} (hx : x ∈ TestSpaces.positiveTimeLocus n) :
    (fun i => x i + w) ∈ TestSpaces.positiveTimeLocus n := by
  refine ⟨fun i j hij => hx.1 (add_right_cancel hij), fun i => ?_⟩
  have h : x i 3 > 0 := hx.2 i
  show x i 3 + w 3 > 0
  linarith
theorem translateFun_mem_positiveTimeSchwartz (hOps : TestFunctionOps.OperationsStatement)
    {n : ℕ} (hn : 0 < n) {w : Fin 4 → ℝ} (hw : 0 ≤ w 3) {φ : TestSpaces.PointTuple n → ℂ}
    (hφ : φ ∈ SchwartzAxioms.positiveTimeSchwartz n) :
    SmoothSeparatedTuples.translateFun w φ ∈ SchwartzAxioms.positiveTimeSchwartz n := by
  obtain ⟨hs, -, hV, hf⟩ := hφ
  have hτ := translateFun_mem_schwartzSet hOps hn w hs
  refine ⟨hτ, hτ.1, hV, fun x hx => ?_⟩
  have hy : shiftAll w x ∈ (TestSpaces.positiveTimeLocus n)ᶜ := by
    intro hy
    apply hx
    have h := add_mem_positiveTimeLocus hw hy
    simpa [shiftAll] using h
  refine ⟨hτ.1, ?_, fun α => ?_⟩
  · rw [SmoothSeparatedTuples.translateFun_apply]
    exact (hf _ hy).2.1
  · rw [multiDeriv_translateFun]
    exact (hf _ hy).2.2 α
theorem translateFun_translateFun_neg {n : ℕ} (v : Fin 4 → ℝ)
    (φ : TestSpaces.PointTuple n → ℂ) :
    SmoothSeparatedTuples.translateFun v (SmoothSeparatedTuples.translateFun (-v) φ) = φ := by
  funext x
  simp only [SmoothSeparatedTuples.translateFun_apply]
  congr 1
  funext i
  simp
theorem translationsPreservePositive_holds (hOps : TestFunctionOps.OperationsStatement)
    {n : ℕ} (hn : 0 < n) : TranslationsPreservePositive n := by
  refine ⟨fun t ht φ hφ => translateFun_mem_positiveTimeSchwartz hOps hn ?_ hφ, fun v hv => ?_⟩
  · simpa [SchwartzAxioms.timeUnitVector, TimeAxis.timeIdx] using ht
  · have hv3 : v 3 = 0 := hv
    refine Set.Subset.antisymm ?_ fun φ hφ => ?_
    · rintro _ ⟨φ, hφ, rfl⟩
      exact translateFun_mem_positiveTimeSchwartz hOps hn hv3.ge hφ
    · refine ⟨SmoothSeparatedTuples.translateFun (-v) φ, ?_, translateFun_translateFun_neg v φ⟩
      exact translateFun_mem_positiveTimeSchwartz hOps hn (by simp [hv3]) hφ
theorem reflectConj_translateFun {n : ℕ} (w : Fin 4 → ℝ) (φ : TestSpaces.PointTuple n → ℂ) :
    Motions.reflectConj (SmoothSeparatedTuples.translateFun w φ) =
      SmoothSeparatedTuples.translateFun (TestSpaces.timeReflect w) (Motions.reflectConj φ) := by
  funext x
  simp only [Motions.reflectConj, SmoothSeparatedTuples.translateFun_apply]
  congr 2
  funext i μ
  fin_cases μ <;> simp [TestSpaces.timeReflectTuple, TestSpaces.timeReflect] <;> ring
theorem timeReflect_smul_timeUnitVector (t : ℝ) :
    TestSpaces.timeReflect (t • SchwartzAxioms.timeUnitVector) =
      (-t) • SchwartzAxioms.timeUnitVector := by
  funext μ
  fin_cases μ <;> simp [TestSpaces.timeReflect, SchwartzAxioms.timeUnitVector, TimeAxis.timeIdx]
theorem timeReflect_of_isPurelySpatial {v : Fin 4 → ℝ} (hv : TimeAxis.IsPurelySpatial v) :
    TestSpaces.timeReflect v = v := by
  have hv3 : v 3 = 0 := hv
  funext μ
  fin_cases μ <;> simp [TestSpaces.timeReflect, hv3]
theorem reflectConjTranslations_holds {n : ℕ} (φ : TestSpaces.PointTuple n → ℂ) :
    ReflectConjTranslations φ :=
  ⟨fun t => by rw [reflectConj_translateFun, timeReflect_smul_timeUnitVector],
    fun v hv => by rw [reflectConj_translateFun, timeReflect_of_isPurelySpatial hv]⟩
theorem valToFun_actOnTensorVal (r : Motions.RigidMotion) {q : ℕ} (F : Motions.TensorVal ℂ q) :
    HyperplaneReflection.valToFun (SmoothSeparatedTuples.actOnTensorVal r F) =
      Motions.actOnFun r (HyperplaneReflection.valToFun F) := by
  cases q <;> rfl
theorem funToVal_valToFun {q : ℕ} (F : Motions.TensorVal ℂ q) :
    HyperplaneReflection.funToVal (HyperplaneReflection.valToFun F) = F := by
  cases q <;> rfl
theorem motionsDistributeOverTensor_holds : MotionsDistributeOverTensor := by
  intro q q' χ ψ r
  rw [← funToVal_valToFun
      (SmoothSeparatedTuples.actOnTensorVal r (HyperplaneReflection.tensorVal χ ψ)),
    valToFun_actOnTensorVal, HyperplaneReflection.tensorVal, HyperplaneReflection.valToFun_funToVal,
    HyperplaneReflection.tensorVal, valToFun_actOnTensorVal, valToFun_actOnTensorVal]
  rfl
theorem tupleTensor_translateFamily {q : ℕ} (w : Fin 4 → ℝ) (f : Fin q → (Fin 4 → ℝ) → ℝ) :
    Motions.tupleTensor (TestFunctionOps.complexify (SmoothSeparatedTuples.translateFamily w f)) =
      SmoothSeparatedTuples.translateTensorVal w
        (Motions.tupleTensor (TestFunctionOps.complexify f)) := by
  cases q <;> rfl
theorem isOpen_upperHalfSpace : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply TimeAxis.timeIdx)
theorem pureTranslation_image_upperHalfSpace {w : Fin 4 → ℝ}
    (hw : 0 ≤ TimeAxis.timeComponent w) :
    (SmoothSeparatedTuples.pureTranslation w).toFun '' TimeAxis.upperHalfSpace ⊆
      TimeAxis.upperHalfSpace := by
  rintro _ ⟨u, hu, rfl⟩
  have h : (SmoothSeparatedTuples.pureTranslation w).toFun u = u + w := by
    simp [Motions.RigidMotion.toFun, SmoothSeparatedTuples.pureTranslation]
  have hu' : TimeAxis.timeComponent u > 0 := hu
  rw [h]
  show TimeAxis.timeComponent (u + w) > 0
  have : TimeAxis.timeComponent (u + w) =
      TimeAxis.timeComponent u + TimeAxis.timeComponent w := rfl
  linarith
theorem tupleTranslation_holds (hTwo : SeparatedTupleForms.TwoFormsAgree)
    {X : SeparatedTuples.SepTuple}
    (hX : X ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace) {w : Fin 4 → ℝ}
    (hw : 0 ≤ TimeAxis.timeComponent w) :
    TupleTranslation X w := by
  obtain ⟨-, -, -, -, -, hO, -, -⟩ := hTwo
  have hP := isOpen_upperHalfSpace
  have hrP := pureTranslation_image_upperHalfSpace hw
  obtain ⟨hLen, hSm, -, hAct⟩ := (hO _ hP).2 X.1.length
  unfold SeparatedTupleForms.SizedTuplesEq at hLen
  unfold SeparatedTupleForms.SmoothTuplesEq at hSm
  obtain ⟨f, hf, hfX⟩ := (Set.ext_iff.1 hLen X.1).1 ⟨X, ⟨hX, rfl⟩, rfl⟩
  have hfe : f = tupleComponentFun X :=
    List.ofFn_injective (hfX.trans (List.ofFn_get X.1).symm)
  subst hfe
  obtain ⟨hOpen, hSep, hSmooth⟩ := ((hAct _ hf).1 (SmoothSeparatedTuples.pureTranslation w)).1
  have hSep' : Motions.actOnTuple (SmoothSeparatedTuples.pureTranslation w) (tupleComponentFun X) ∈
      TestSpaces.disjointSupportTuples TimeAxis.upperHalfSpace X.1.length :=
    ((hO _ hOpen).2 X.1.length).2.2.1 _ hP hrP hSep
  obtain ⟨Y, ⟨hY, hYl⟩, hYe⟩ := (Set.ext_iff.1 hLen _).2 ⟨_, hSep', rfl⟩
  refine ⟨⟨Y, hY, hYe, hYl⟩, fun hXs => ⟨?_, tupleTensor_translateFamily w _⟩⟩
  obtain ⟨f', ⟨-, hf's⟩, hf'X⟩ := (Set.ext_iff.1 hSm X.1).1 ⟨X, ⟨hXs, rfl⟩, rfl⟩
  have hf'e : f' = tupleComponentFun X :=
    List.ofFn_injective (hf'X.trans (List.ofFn_get X.1).symm)
  subst hf'e
  have hGs := hSmooth hf's
  have hG : TestSpaces.HasSmoothComponents TimeAxis.upperHalfSpace
      (Motions.actOnTuple (SmoothSeparatedTuples.pureTranslation w) (tupleComponentFun X)) :=
    fun i => ⟨(hGs i).1, (hGs i).2.1, (hGs i).2.2.trans hrP⟩
  obtain ⟨Y', hY', hY'e⟩ := (Set.ext_iff.1 hSm _).2 ⟨_, ⟨hSep', hG⟩, rfl⟩
  exact ⟨Y', hY'.1, hY'e⟩
theorem compositionTranslationStatement_holds (hOps : TestFunctionOps.OperationsStatement)
    (hTwo : SeparatedTupleForms.TwoFormsAgree) : CompositionTranslationStatement :=
  ⟨fun _ k _ _ φ _ => ⟨fun r r' => actOnFun_actOnFun r r' φ,
      fun v => weightedSeminorm_translateFun_le k v φ⟩,
    fun _ hn => ⟨translationsPreservePositive_holds hOps hn, fun φ _ => reflectConjTranslations_holds φ⟩,
    motionsDistributeOverTensor_holds,
    fun _ _ hX hw => tupleTranslation_holds hTwo hX hw⟩
end YangMills.Construction.MotionComposition
end
