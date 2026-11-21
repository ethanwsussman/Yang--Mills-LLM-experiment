import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.RotationInvariance.EntireFunctionOfTheAngleOnAPencilProof
import YangMills.Construction.RotationInvariance.FunctionalAndPlaneKernelsAreLinearInEachLabel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube MeasureTheory Set
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.LabelLinearity
theorem scalarEquiv_apply (c : ℂ) (i : Fin 1) : scalarEquiv c i = c := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
section Holomorphic
variable {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} {f g : (Fin p → ℂ × ℂ) → ℂ}
theorem continuousOn_of_holomorphicOnTuples (h : HolomorphicOnTuples O f) : ContinuousOn f O := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicRotationCovariance.continuousOn_of_holomorphicOnTuples <;> assumption
theorem holomorphicOnTuples_linComb (c c' : ℂ) (hf : HolomorphicOnTuples O f)
    (hg : HolomorphicOnTuples O g) :
    HolomorphicOnTuples O fun v => c * f v + c' * g v := by
  have key : scalarEquiv ∘ (fun v => c * f v + c' * g v) ∘ (pairTupleEquiv p).symm =
      fun z => c • (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) z +
        c' • (scalarEquiv ∘ g ∘ (pairTupleEquiv p).symm) z := by
    funext z i
    simp [scalarEquiv_apply]
  refine ⟨hf.1, ?_, fun a ha j => ?_⟩
  · show ContinuousOn (scalarEquiv ∘ (fun v => c * f v + c' * g v) ∘
      (pairTupleEquiv p).symm) _
    rw [key]
    exact (hf.2.1.const_smul c).add (hg.2.1.const_smul c')
  · have h1 := hf.2.2 a ha j
    have h2 := hg.2.2 a ha j
    filter_upwards [h1, h2] with ζ e1 e2
    show DifferentiableAt ℂ (fun ζ => (scalarEquiv ∘ (fun v => c * f v + c' * g v) ∘
      (pairTupleEquiv p).symm) (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ
    rw [key]
    exact (e1.const_smul c).add (e2.const_smul c')
end Holomorphic
section Integrals
variable {n : ℕ} {α : Fin n → RealPlane → ℂ}
theorem integrable_profileIntegrand (hc : ∀ i, Continuous (α i)) (hs : ∀ i, HasCompactSupport (α i))
    {F : (Fin n → RealPlane) → ℂ}
    (hF : ContinuousOn F (Set.univ.pi fun i => tsupport (α i))) :
    Integrable (profileIntegrand α F) := by apply _root_.YangMills.Construction.EuclideanFunctionals.AngleFunctionOnPencil.integrable_profileIntegrand <;> assumption
theorem profileIntegral_linComb (hc : ∀ i, Continuous (α i))
    (hs : ∀ i, HasCompactSupport (α i)) (c c' : ℂ) {F G : (Fin n → RealPlane) → ℂ}
    (hF : ContinuousOn F (Set.univ.pi fun i => tsupport (α i)))
    (hG : ContinuousOn G (Set.univ.pi fun i => tsupport (α i))) :
    profileIntegral α (fun y => c * F y + c' * G y) =
      c * profileIntegral α F + c' * profileIntegral α G := by
  unfold profileIntegral
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_profileIntegrand hc hs hF).const_mul c)
      ((integrable_profileIntegrand hc hs hG).const_mul c')]
  congr 1
  funext y
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · simp only [profileIntegrand, indicator_of_mem hy]
    ring
  · simp [profileIntegrand, indicator_of_notMem hy]
end Integrals
section Ordered
variable {n : ℕ} {α : Fin n → RealPlane → ℂ}
theorem inner_rotatedDirection_rightAngleZero (y : RealPlane) :
    inner ℝ (rotatedDirection rightAngleZero) y = y 0 := by
  rw [rotatedDirection_rightAngleZero, inner_eq_coord_sum]
  simp [RealPlane.unitX]
theorem coord_zero_lt_of_succ (h : FunsTimeSeparated α) (i : ℕ) (hi : i + 1 < n)
    {y z : RealPlane} (hy : y ∈ tsupport (α ⟨i, Nat.lt_of_succ_lt hi⟩))
    (hz : z ∈ tsupport (α ⟨i + 1, hi⟩)) : y 0 < z 0 := by
  obtain ⟨-, -, hc, hn, hord⟩ := h
  have h1 := (isGreatest_supInner (rotatedDirection rightAngleZero) (hc ⟨i, Nat.lt_of_succ_lt hi⟩)
    (hn _)).2 (mem_image_of_mem _ hy)
  have h2 := (isLeast_infInner (rotatedDirection rightAngleZero) (hc ⟨i + 1, hi⟩) (hn _)).2
    (mem_image_of_mem _ hz)
  have h3 := hord i hi
  simp only [inner_rotatedDirection_rightAngleZero] at h1 h2
  linarith
theorem coord_zero_lt_of_lt_add (h : FunsTimeSeparated α) (d : ℕ) :
    ∀ (k : ℕ) (hk : k + d + 1 < n) {y z : RealPlane},
      y ∈ tsupport (α ⟨k, by omega⟩) → z ∈ tsupport (α ⟨k + d + 1, hk⟩) → y 0 < z 0 := by
  induction d with
  | zero =>
    intro k hk y z hy hz
    exact coord_zero_lt_of_succ h k hk hy hz
  | succ d ih =>
    intro k hk y z hy hz
    obtain ⟨w, hw⟩ := h.2.2.2.1 ⟨k + d + 1, by omega⟩
    exact (ih k (by omega) hy hw).trans (coord_zero_lt_of_succ h (k + d + 1) (by omega) hw hz)
theorem pairwise_disjoint_tsupport (h : FunsTimeSeparated α) :
    Pairwise fun k l => Disjoint (tsupport (α k)) (tsupport (α l)) := by
  have key : ∀ k l : Fin n, k < l → Disjoint (tsupport (α k)) (tsupport (α l)) := by
    intro k l hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hkl)
    have hl : l = ⟨k.1 + d + 1, by omega⟩ := Fin.ext hd
    refine Set.disjoint_left.2 fun x hx hx' => lt_irrefl (x 0) ?_
    rw [hl] at hx'
    exact coord_zero_lt_of_lt_add h d k.1 (by omega) hx hx'
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · exact key k l hlt
  · exact (key l k hlt).symm
end Ordered
theorem embedPlane_mem_forwardTube {y : RealPlane} (h : 0 < y 0) : embedPlane y ∈ forwardTube := by
  simp [forwardTube, lightConePlus, lightConeMinus, embedPlane, h]
theorem embedPlaneTuple_successiveDifferences_mem {q : ℕ} {α : Fin (q + 1) → RealPlane → ℂ}
    (h : FunsTimeSeparated α) {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ Set.univ.pi fun i => tsupport (α i)) :
    embedPlaneTuple (successiveDifferences y) ∈ forwardTubePow q := by
  intro i _
  refine embedPlane_mem_forwardTube ?_
  have h1 := coord_zero_lt_of_succ h i.1 (by omega) (hy _ (mem_univ _)) (hy _ (mem_univ _))
  simpa [successiveDifferences] using h1
theorem continuous_embedPlaneTuple_successiveDifferences (q : ℕ) :
    Continuous fun y : Fin (q + 1) → RealPlane => embedPlaneTuple (successiveDifferences y) := by
  have h0 : Continuous embedPlane :=
    (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj (0 : Fin 2) : RealPlane →L[ℝ] ℝ).continuous).prodMk
      (Complex.continuous_ofReal.comp
        (EuclideanSpace.proj (1 : Fin 2) : RealPlane →L[ℝ] ℝ).continuous)
  exact continuous_pi fun _ => h0.comp ((continuous_apply _).sub (continuous_apply _))
section Products
open YangMills.Construction.EuclideanFunctionals.TranslationRules
variable {q : ℕ} {S : ConnFamily}
theorem productFunctions_complexComponents (hP : ProductFunctionsInC1c)
    {α : Fin (q + 1) → RealPlane → ℂ} (hα : ∀ l, α l ∈ complexProfiles)
    (hd : Pairwise fun k l => Disjoint (tsupport (α k)) (tsupport (α l)))
    (φ : Fin (q + 1) → realLabels) : ComplexComponents fun l => productFunction (α l) (φ l) :=
  ⟨by omega, fun l => (hP _ (hα l) _ (φ l).2).1, fun k l hkl =>
    Set.disjoint_left.2 fun _ hx hy =>
      Set.disjoint_left.1 (hd hkl) ((hP _ (hα k) _ (φ k).2).2 hx).1
        ((hP _ (hα l) _ (φ l).2).2 hy).1⟩
theorem productFunction_labelLinComb (α : RealPlane → ℂ) (a a' : ℝ) (ψ ψ' : realLabels) :
    productFunction α (labelLinComb a ψ a' ψ') =
      (a : ℂ) • productFunction α ψ + (a' : ℂ) • productFunction α ψ' := by
  funext x
  simp [productFunction, labelLinComb]
  ring
theorem productFunctions_update (α : Fin (q + 1) → RealPlane → ℂ) (φ : Fin (q + 1) → realLabels)
    (j : Fin (q + 1)) (ψ : realLabels) :
    (fun l => productFunction (α l) (Function.update φ j ψ l)) =
      Function.update (fun l => productFunction (α l) (φ l)) j (productFunction (α j) ψ) := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp
  · simp [Function.update_of_ne hl]
theorem centeredFnAtProducts_labelLinComb (hP : ProductFunctionsInC1c)
    (hL : TensorComponents.IsComplexMultilinear S)
    {α : Fin (q + 1) → RealPlane → ℂ} (hα : ∀ l, α l ∈ complexProfiles)
    (hd : Pairwise fun k l => Disjoint (tsupport (α k)) (tsupport (α l)))
    (φ : Fin (q + 1) → realLabels) (j : Fin (q + 1)) (ψ : realLabels) (a a' : ℝ) :
    centeredFnAtProducts S α (Function.update φ j (labelLinComb a (φ j) a' ψ)) =
      a * centeredFnAtProducts S α φ + a' * centeredFnAtProducts S α (Function.update φ j ψ) := by
  have H := productFunctions_complexComponents hP hα hd φ
  have H' := productFunctions_complexComponents hP hα hd (Function.update φ j ψ)
  rw [productFunctions_update] at H'
  have h := (hL (q + 1) j (a : ℂ) (a' : ℂ) _ _ H H').2
  unfold centeredFnAtProducts
  rw [productFunctions_update, productFunctions_update, productFunction_labelLinComb]
  exact h
theorem centeredFnAtProducts_eq_zero_of_profile_eq_zero (hP : ProductFunctionsInC1c)
    (hL : TensorComponents.IsComplexMultilinear S)
    {α : Fin (q + 1) → RealPlane → ℂ} (hα : ∀ l, α l ∈ complexProfiles)
    (hd : Pairwise fun k l => Disjoint (tsupport (α k)) (tsupport (α l)))
    (φ : Fin (q + 1) → realLabels) {l : Fin (q + 1)} (hl : α l = 0) :
    centeredFnAtProducts S α φ = 0 := by
  have H := productFunctions_complexComponents hP hα hd φ
  have hz : productFunction (α l) (φ l) = 0 := by
    funext x
    simp [productFunction, hl]
  have hup : ∀ g : R4 → ℂ, g = 0 →
      Function.update (fun k => productFunction (α k) (φ k)) l g =
        fun k => productFunction (α k) (φ k) := by
    rintro g rfl
    rw [← hz]
    exact Function.update_eq_self _ _
  have h := (hL (q + 1) l 0 0 _ (productFunction (α l) (φ l)) H (by rw [hup _ hz]; exact H)).2
  rw [hup _ (by simp)] at h
  simpa [centeredFnAtProducts] using h
end Products
theorem holds (hT : TensorComponents.CenteredSeesTensorComps)
    (hK : PlaneKernelProps.Holds) (hR : TranslationRules.TranslationAndMotionFacts) :
    Holds := by
  intro m S d q hq φ j ψ a a'
  obtain ⟨-, -, -, hL, -⟩ := hT S
  have hP := hR.2.2.1
  refine ⟨fun α hα hd => ⟨productFunctions_complexComponents hP hα hd φ,
    centeredFnAtProducts_labelLinComb hP hL hα hd φ j ψ a a', ?_⟩, ?_⟩
  · rintro ⟨l, hl⟩
    exact centeredFnAtProducts_eq_zero_of_profile_eq_zero hP hL hα hd φ hl
  · intro v hv
    have k := (hK m S d q hq φ).1
    have k' := (hK m S d q hq (Function.update φ j ψ)).1
    have hg : IsPlaneKernel S (Function.update φ j (labelLinComb a (φ j) a' ψ))
        (fun v => a * planeKernel S φ v + a' * planeKernel S (Function.update φ j ψ) v) := by
      refine ⟨holomorphicOnTuples_linComb _ _ k.holomorphic k'.holomorphic, fun α hα hord => ?_⟩
      have hd := pairwise_disjoint_tsupport hord
      have cont : ∀ K : (Fin q → ℂ × ℂ) → ℂ, HolomorphicOnTuples (forwardTubePow q) K →
          ContinuousOn (fun y => K (embedPlaneTuple (successiveDifferences y)))
            (Set.univ.pi fun i => tsupport (α i)) := fun K hK' =>
        (continuousOn_of_holomorphicOnTuples hK').comp
          (continuous_embedPlaneTuple_successiveDifferences q).continuousOn
          fun y hy => embedPlaneTuple_successiveDifferences_mem hord hy
      rw [centeredFnAtProducts_labelLinComb hP hL hα hd φ j ψ a a', k.integral_eq α hα hord,
        k'.integral_eq α hα hord]
      exact (profileIntegral_linComb (fun i => (hα i).1.continuous)
        (fun i => (hα i).2) _ _ (cont _ k.holomorphic) (cont _ k'.holomorphic)).symm
    exact ((hK m S d q hq _).2.1 _ hg v hv).symm
end YangMills.Construction.EuclideanFunctionals.LabelLinearity
end
