import YangMills.Construction.Matrices.TensorOperatorOfAnIntegralOperatorProof
import YangMills.Construction.Matrices.TensorOperatorOnProductsAndItsMatrixElements
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsFollowsABijection
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsLinearAndReal
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsOfAProductIsAProduct
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory YangMills.Construction.Matrices YangMills.Construction.SpinHarmonics
open YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichProduct
section Classes
variable {I : Type} [Countable I]
theorem toHaarL2_congr {f g : (I → ComplexMatrix2.specialUnitary) → ℂ}
    (h : f =ᵐ[ComplexMatrix2.haarPi I] g) : toHaarL2 f = toHaarL2 g := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.toHaarL2_congr_ae <;> assumption
theorem toHaarL2_coe (φ : HaarL2 I) :
    toHaarL2 (φ : (I → ComplexMatrix2.specialUnitary) → ℂ) = φ := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.toHaarL2_coeFn <;> assumption
theorem coe_toHaarL2 {f : (I → ComplexMatrix2.specialUnitary) → ℂ}
    (h : MemLp f 2 (ComplexMatrix2.haarPi I)) :
    (toHaarL2 f : (I → ComplexMatrix2.specialUnitary) → ℂ) =ᵐ[ComplexMatrix2.haarPi I] f := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.coeFn_toHaarL2 <;> assumption
end Classes
section Part
variable {B : Type} [Finite B]
theorem measurable_restrictTo (S : Set B) :
    Measurable (restrictTo S : (B → ComplexMatrix2.specialUnitary) → ↥S → ComplexMatrix2.specialUnitary) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem measurePreserving_restrictTo (hJ : GlueMeasurePreserving) (S : Set B) :
    MeasurePreserving
      (restrictTo S : (B → ComplexMatrix2.specialUnitary) → ↥S → ComplexMatrix2.specialUnitary)
      (ComplexMatrix2.haarPi B) (ComplexMatrix2.haarPi ↥S) := by
  refine ⟨measurable_restrictTo S, ?_⟩
  rw [← (hJ B S).map_eq, Measure.map_map (measurable_restrictTo S) (hJ B S).measurable]
  have h : (restrictTo S : (B → ComplexMatrix2.specialUnitary) → ↥S → ComplexMatrix2.specialUnitary) ∘
      (fun p : (↥S → ComplexMatrix2.specialUnitary) × (↥Sᶜ → ComplexMatrix2.specialUnitary) =>
        glue S p.1 p.2) = Prod.fst := by
    funext p
    exact congrArg Prod.fst ((splitEquiv (X := ComplexMatrix2.specialUnitary) S).right_inv p)
  rw [h, Measure.map_fst_prod]
  simp
theorem tensorFn_congr (hJ : GlueMeasurePreserving)
    {P : Set B} {f f' : (↥P → ComplexMatrix2.specialUnitary) → ℂ}
    {h h' : (↥Pᶜ → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : f =ᵐ[ComplexMatrix2.haarPi ↥P] f') (hh : h =ᵐ[ComplexMatrix2.haarPi ↥Pᶜ] h') :
    tensorFn P f h =ᵐ[ComplexMatrix2.haarPi B] tensorFn P f' h' := by
  have h₁ := (measurePreserving_restrictTo hJ P).quasiMeasurePreserving.ae_eq_comp hf
  have h₂ := (measurePreserving_restrictTo hJ Pᶜ).quasiMeasurePreserving.ae_eq_comp hh
  filter_upwards [h₁, h₂] with u e₁ e₂
  simp only [Function.comp_apply] at e₁ e₂
  simp only [tensorFn, e₁, e₂]
theorem inner_comp_restrictTo (hJ : GlueMeasurePreserving)
    (S : Set B) {t t' : (↥S → ComplexMatrix2.specialUnitary) → ℂ}
    (ht : MemLp t 2 (ComplexMatrix2.haarPi ↥S)) (ht' : MemLp t' 2 (ComplexMatrix2.haarPi ↥S)) :
    (inner ℂ (toHaarL2 (t ∘ restrictTo S)) (toHaarL2 (t' ∘ restrictTo S)) : ℂ) =
      inner ℂ (toHaarL2 t) (toHaarL2 t') := by
  have hp := measurePreserving_restrictTo (B := B) hJ S
  have h₁ := ht.comp_measurePreserving hp
  have h₂ := ht'.comp_measurePreserving hp
  have e₁ := hp.quasiMeasurePreserving.ae_eq_comp (coe_toHaarL2 ht)
  have e₂ := hp.quasiMeasurePreserving.ae_eq_comp (coe_toHaarL2 ht')
  rw [L2.inner_def, L2.inner_def]
  have hg : AEStronglyMeasurable (fun z : ↥S → ComplexMatrix2.specialUnitary =>
      (inner ℂ ((toHaarL2 t : HaarL2 ↥S) z) ((toHaarL2 t' : HaarL2 ↥S) z) : ℂ))
      (ComplexMatrix2.haarPi ↥S) :=
    (Lp.aestronglyMeasurable _).inner (Lp.aestronglyMeasurable _)
  have hm := integral_map (μ := ComplexMatrix2.haarPi B) hp.measurable.aemeasurable
    (f := fun z : ↥S → ComplexMatrix2.specialUnitary =>
      (inner ℂ ((toHaarL2 t : HaarL2 ↥S) z) ((toHaarL2 t' : HaarL2 ↥S) z) : ℂ))
    (by rw [hp.map_eq]; exact hg)
  rw [hp.map_eq] at hm
  rw [hm]
  refine integral_congr_ae ?_
  filter_upwards [coe_toHaarL2 h₁, coe_toHaarL2 h₂, e₁, e₂] with w a b c d
  simp only [Function.comp_apply] at c d
  rw [a, b, c, d]
  rfl
def IndepOn (P : Set B) (T : (B → ComplexMatrix2.specialUnitary) → ℂ) : Prop :=
  ∀ w w' : B → ComplexMatrix2.specialUnitary, (∀ b, b ∉ P → w b = w' b) → T w = T w'
def onCompl (P : Set B) (T : (B → ComplexMatrix2.specialUnitary) → ℂ)
    (z : ↥Pᶜ → ComplexMatrix2.specialUnitary) : ℂ :=
  T (glue P (fun _ => 1) z)
variable {P : Set B} {T T' : (B → ComplexMatrix2.specialUnitary) → ℂ}
theorem onCompl_restrictTo (hT : IndepOn P T) (w : B → ComplexMatrix2.specialUnitary) :
    onCompl P T (restrictTo Pᶜ w) = T w :=
  hT _ _ fun b hb => glue_of_notMem P _ _ ⟨b, hb⟩
theorem onCompl_comp (hT : IndepOn P T) : onCompl P T ∘ restrictTo Pᶜ = T :=
  funext (onCompl_restrictTo hT)
theorem mul_eq_tensorFn (hT : IndepOn P T) (f : (↥P → ComplexMatrix2.specialUnitary) → ℂ) :
    (fun w => f (restrictTo P w) * T w) = tensorFn P f (onCompl P T) := by
  funext w
  simp only [tensorFn, onCompl_restrictTo hT]
theorem measurable_onCompl (hJ : GlueMeasurePreserving)
    (hm : Measurable T) : Measurable (onCompl P T) :=
  hm.comp ((hJ B P).measurable.comp
    (measurable_prodMk_left (x := fun _ => (1 : ComplexMatrix2.specialUnitary))))
theorem memLp_onCompl (hJ : GlueMeasurePreserving)
    (hT : IndepOn P T) (hm : Measurable T) (hl : MemLp T 2 (ComplexMatrix2.haarPi B)) :
    MemLp (onCompl P T) 2 (ComplexMatrix2.haarPi ↥Pᶜ) := by
  have hp := measurePreserving_restrictTo (B := B) hJ Pᶜ
  have h : MemLp (onCompl P T ∘ restrictTo Pᶜ) 2 (ComplexMatrix2.haarPi B) := by
    rwa [onCompl_comp hT]
  rw [← hp.map_eq]
  exact (memLp_map_measure_iff
    (by rw [hp.map_eq]; exact (measurable_onCompl hJ hm).aestronglyMeasurable)
    hp.measurable.aemeasurable).2 h
theorem memLp_mul_restrictTo (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner) {f : (↥P → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : MemLp f 2 (ComplexMatrix2.haarPi ↥P)) (hT : IndepOn P T) (hm : Measurable T)
    (hl : MemLp T 2 (ComplexMatrix2.haarPi B)) :
    MemLp (fun w => f (restrictTo P w) * T w) 2 (ComplexMatrix2.haarPi B) := by
  rw [mul_eq_tensorFn hT]
  have hh := memLp_onCompl hJ hT hm hl
  exact (hE B P f f _ _ hf hf hh hh).1
theorem inner_mul_restrictTo (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner) {f f' : (↥P → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : MemLp f 2 (ComplexMatrix2.haarPi ↥P)) (hf' : MemLp f' 2 (ComplexMatrix2.haarPi ↥P))
    (hT : IndepOn P T) (hm : Measurable T) (hl : MemLp T 2 (ComplexMatrix2.haarPi B))
    (hT' : IndepOn P T') (hm' : Measurable T') (hl' : MemLp T' 2 (ComplexMatrix2.haarPi B)) :
    (inner ℂ (toHaarL2 fun w => f (restrictTo P w) * T w)
      (toHaarL2 fun w => f' (restrictTo P w) * T' w) : ℂ) =
      inner ℂ (toHaarL2 f) (toHaarL2 f') * inner ℂ (toHaarL2 T) (toHaarL2 T') := by
  have hh := memLp_onCompl hJ hT hm hl
  have hh' := memLp_onCompl hJ hT' hm' hl'
  rw [mul_eq_tensorFn hT, mul_eq_tensorFn hT', (hE B P f f' _ _ hf hf' hh hh').2]
  have h := inner_comp_restrictTo (B := B) hJ Pᶜ hh hh'
  rw [onCompl_comp hT, onCompl_comp hT'] at h
  rw [h]
theorem tensorOne_mul (hO : TensorOneOnProductsForAll)
    (hJ : GlueMeasurePreserving) [Nonempty B]
    (hn : P.Nonempty) (hu : P ≠ Set.univ)
    (X : HaarL2 ↥P →L[ℂ] HaarL2 ↥P) {f : (↥P → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : MemLp f 2 (ComplexMatrix2.haarPi ↥P)) (hT : IndepOn P T) (hm : Measurable T)
    (hl : MemLp T 2 (ComplexMatrix2.haarPi B)) :
    tensorOne P X (toHaarL2 fun w => f (restrictTo P w) * T w) =
      toHaarL2 fun w =>
        (X (toHaarL2 f) : (↥P → ComplexMatrix2.specialUnitary) → ℂ) (restrictTo P w) * T w := by
  rw [mul_eq_tensorFn hT, mul_eq_tensorFn hT]
  have hh := memLp_onCompl hJ hT hm hl
  have hx := ((hO B P hn hu X).1 (toHaarL2 f) (toHaarL2 (onCompl P T))).2
  have e₁ : toHaarL2 (tensorFn P f (onCompl P T)) =
      toHaarL2 (tensorFn P (toHaarL2 f : HaarL2 ↥P)
        (toHaarL2 (onCompl P T) : HaarL2 ↥Pᶜ)) :=
    toHaarL2_congr (tensorFn_congr hJ (coe_toHaarL2 hf).symm (coe_toHaarL2 hh).symm)
  have e₂ : toHaarL2 (tensorFn P (X (toHaarL2 f) : (↥P → ComplexMatrix2.specialUnitary) → ℂ)
        (onCompl P T)) =
      toHaarL2 (tensorFn P (X (toHaarL2 f) : (↥P → ComplexMatrix2.specialUnitary) → ℂ)
        (toHaarL2 (onCompl P T) : HaarL2 ↥Pᶜ)) :=
    toHaarL2_congr (tensorFn_congr hJ (Filter.EventuallyEq.refl _ _)
      (coe_toHaarL2 hh).symm)
  rw [e₁, e₂]
  exact hx
end Part
section Products
variable {B : Type} [Finite B]
def blockProd {n : ℕ} (parts : Fin n → Set B)
    (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ)
    (T : (B → ComplexMatrix2.specialUnitary) → ℂ) (w : B → ComplexMatrix2.specialUnitary) : ℂ :=
  (∏ i, f i (restrictTo (parts i) w)) * T w
theorem blockProd_zero (parts : Fin 0 → Set B)
    (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ)
    (T : (B → ComplexMatrix2.specialUnitary) → ℂ) : blockProd parts f T = T := by
  funext w
  simp [blockProd]
theorem blockProd_succ {n : ℕ} (parts : Fin (n + 1) → Set B)
    (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ)
    (T : (B → ComplexMatrix2.specialUnitary) → ℂ) :
    blockProd parts f T = fun w => f 0 (restrictTo (parts 0) w) *
      blockProd (fun i => parts i.succ) (fun i => f i.succ) T w := by
  funext w
  simp only [blockProd, Fin.prod_univ_succ, mul_assoc]
theorem blockProd_succ' {n : ℕ} (parts : Fin (n + 1) → Set B)
    (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ)
    (T : (B → ComplexMatrix2.specialUnitary) → ℂ) :
    blockProd parts f T = blockProd (fun i => parts i.succ) (fun i => f i.succ)
      (fun w => f 0 (restrictTo (parts 0) w) * T w) := by
  funext w
  simp only [blockProd, Fin.prod_univ_succ]
  ring
theorem indepOn_blockProd {n : ℕ} {parts : Fin n → Set B}
    {f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ}
    {T : (B → ComplexMatrix2.specialUnitary) → ℂ} {S : Set B}
    (hd : ∀ i, Disjoint (parts i) S) (hT : IndepOn S T) :
    IndepOn S (blockProd parts f T) := by
  intro w w' h
  have e : ∀ i, restrictTo (parts i) w = restrictTo (parts i) w' := fun i =>
    funext fun b => h b (Set.disjoint_left.1 (hd i) b.2)
  simp only [blockProd, e, hT w w' h]
theorem indepOn_mul {P S : Set B} {f : (↥P → ComplexMatrix2.specialUnitary) → ℂ}
    {T : (B → ComplexMatrix2.specialUnitary) → ℂ}
    (hd : Disjoint P S) (hT : IndepOn S T) :
    IndepOn S fun w => f (restrictTo P w) * T w := by
  intro w w' h
  have e : restrictTo P w = restrictTo P w' :=
    funext fun b => h b (Set.disjoint_left.1 hd b.2)
  simp only [e, hT w w' h]
theorem measurable_blockProd {n : ℕ} {parts : Fin n → Set B}
    {f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ}
    {T : (B → ComplexMatrix2.specialUnitary) → ℂ} (hf : ∀ i, Measurable (f i))
    (hT : Measurable T) : Measurable (blockProd parts f T) := by
  have h : Measurable fun w : B → ComplexMatrix2.specialUnitary =>
      ∏ i, f i (restrictTo (parts i) w) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_restrictTo (parts i))
  exact h.mul hT
theorem pairwise_disjoint_succ {n : ℕ} {parts : Fin (n + 1) → Set B}
    (hd : Pairwise (Function.onFun Disjoint parts)) :
    Pairwise (Function.onFun Disjoint fun i : Fin n => parts i.succ) :=
  fun _ _ hij => hd ((Fin.succ_injective _).ne hij)
theorem memLp_blockProd (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner) :
    ∀ {n : ℕ} (parts : Fin n → Set B), Pairwise (Function.onFun Disjoint parts) →
      ∀ (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ), (∀ i, Measurable (f i)) →
      (∀ i, MemLp (f i) 2 (ComplexMatrix2.haarPi ↥(parts i))) →
      ∀ T : (B → ComplexMatrix2.specialUnitary) → ℂ, Measurable T →
      MemLp T 2 (ComplexMatrix2.haarPi B) →
      (∀ i, IndepOn (parts i) T) → MemLp (blockProd parts f T) 2 (ComplexMatrix2.haarPi B) := by
  intro n
  induction n with
  | zero =>
    intro parts _ f _ _ T _ hl _
    rwa [blockProd_zero]
  | succ n ih =>
    intro parts hd f hfm hfl T hm hl hi
    rw [blockProd_succ]
    exact memLp_mul_restrictTo hJ hE (hfl 0)
      (indepOn_blockProd (fun i => hd (Fin.succ_ne_zero i)) (hi 0))
      (measurable_blockProd (fun i => hfm i.succ) hm)
      (ih _ (pairwise_disjoint_succ hd) _ (fun i => hfm i.succ) (fun i => hfl i.succ) T hm hl
        fun i => hi i.succ)
theorem tensorOneList_apply_blockProd (hO : TensorOneOnProductsForAll)
    (hJ : GlueMeasurePreserving) (hE : TensorFnMemL2Inner) [Nonempty B] :
    ∀ {n : ℕ} (parts : Fin n → Set B), Pairwise (Function.onFun Disjoint parts) →
      (∀ i, (parts i).Nonempty) → (∀ i, parts i ≠ Set.univ) →
      ∀ (Xs : ∀ i, HaarL2 ↥(parts i) →L[ℂ] HaarL2 ↥(parts i))
        (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ), (∀ i, Measurable (f i)) →
      (∀ i, MemLp (f i) 2 (ComplexMatrix2.haarPi ↥(parts i))) →
      ∀ T : (B → ComplexMatrix2.specialUnitary) → ℂ, Measurable T →
      MemLp T 2 (ComplexMatrix2.haarPi B) →
      (∀ i, IndepOn (parts i) T) →
      (List.ofFn fun i => tensorOne (parts i) (Xs i)).prod
          (toHaarL2 (blockProd parts f T)) =
        toHaarL2 (blockProd parts
          (fun i => (Xs i (toHaarL2 (f i)) : (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ))
          T) := by
  intro n
  induction n with
  | zero =>
    intro parts _ _ _ Xs f _ _ T _ _ _
    simp [blockProd_zero]
  | succ n ih =>
    intro parts hd hn hu Xs f hfm hfl T hm hl hi
    have hrep : ∀ i, Measurable
        (Xs i (toHaarL2 (f i)) : (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ) :=
      fun i => (Lp.stronglyMeasurable _).measurable
    have hrepl : ∀ i, MemLp
        (Xs i (toHaarL2 (f i)) : (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ) 2
        (ComplexMatrix2.haarPi ↥(parts i)) := fun i => Lp.memLp _
    have hm' : Measurable fun w => f 0 (restrictTo (parts 0) w) * T w :=
      ((hfm 0).comp (measurable_restrictTo _)).mul hm
    have hl' := memLp_mul_restrictTo hJ hE (hfl 0) (hi 0) hm hl
    have e₁ : (List.ofFn fun i => tensorOne (parts i) (Xs i)).prod =
        tensorOne (parts 0) (Xs 0) *
          (List.ofFn fun i : Fin n => tensorOne (parts i.succ) (Xs i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have hIH := ih (fun i => parts i.succ) (pairwise_disjoint_succ hd) (fun i => hn i.succ)
      (fun i => hu i.succ) (fun i => Xs i.succ) (fun i => f i.succ) (fun i => hfm i.succ)
      (fun i => hfl i.succ) _ hm' hl'
      (fun i => indepOn_mul (hd (Fin.succ_ne_zero i).symm) (hi i.succ))
    have e₂ : blockProd (fun i : Fin n => parts i.succ)
          (fun i => (Xs i.succ (toHaarL2 (f i.succ)) :
            (↥(parts i.succ) → ComplexMatrix2.specialUnitary) → ℂ))
          (fun w => f 0 (restrictTo (parts 0) w) * T w) =
        fun w => f 0 (restrictTo (parts 0) w) * blockProd (fun i : Fin n => parts i.succ)
          (fun i => (Xs i.succ (toHaarL2 (f i.succ)) :
            (↥(parts i.succ) → ComplexMatrix2.specialUnitary) → ℂ)) T w := by
      funext w
      simp only [blockProd]
      ring
    rw [e₁, ContinuousLinearMap.mul_apply, blockProd_succ' parts f T, hIH, e₂,
      tensorOne_mul hO hJ (hn 0) (hu 0) (Xs 0) (hfl 0)
        (indepOn_blockProd (fun i => hd (Fin.succ_ne_zero i)) (hi 0))
        (measurable_blockProd (fun i => hrep i.succ) hm)
        (memLp_blockProd hJ hE _ (pairwise_disjoint_succ hd) _ (fun i => hrep i.succ)
          (fun i => hrepl i.succ) T hm hl fun i => hi i.succ),
      blockProd_succ parts _ T]
theorem inner_blockProd (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner) :
    ∀ {n : ℕ} (parts : Fin n → Set B), Pairwise (Function.onFun Disjoint parts) →
      ∀ (f : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ), (∀ i, Measurable (f i)) →
      (∀ i, MemLp (f i) 2 (ComplexMatrix2.haarPi ↥(parts i))) →
      ∀ (g : ∀ i, (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ), (∀ i, Measurable (g i)) →
      (∀ i, MemLp (g i) 2 (ComplexMatrix2.haarPi ↥(parts i))) →
      ∀ T : (B → ComplexMatrix2.specialUnitary) → ℂ, Measurable T →
      MemLp T 2 (ComplexMatrix2.haarPi B) →
      (∀ i, IndepOn (parts i) T) →
      ∀ T' : (B → ComplexMatrix2.specialUnitary) → ℂ, Measurable T' →
      MemLp T' 2 (ComplexMatrix2.haarPi B) →
      (∀ i, IndepOn (parts i) T') →
      (inner ℂ (toHaarL2 (blockProd parts f T)) (toHaarL2 (blockProd parts g T')) : ℂ) =
        (∏ i, (inner ℂ (toHaarL2 (f i)) (toHaarL2 (g i)) : ℂ)) *
          inner ℂ (toHaarL2 T) (toHaarL2 T') := by
  intro n
  induction n with
  | zero =>
    intro parts _ f _ _ g _ _ T _ _ _ T' _ _ _
    simp [blockProd_zero]
  | succ n ih =>
    intro parts hd f hfm hfl g hgm hgl T hm hl hi T' hm' hl' hi'
    rw [blockProd_succ parts f T, blockProd_succ parts g T',
      inner_mul_restrictTo hJ hE (hfl 0) (hgl 0)
        (indepOn_blockProd (fun i => hd (Fin.succ_ne_zero i)) (hi 0))
        (measurable_blockProd (fun i => hfm i.succ) hm)
        (memLp_blockProd hJ hE _ (pairwise_disjoint_succ hd) _ (fun i => hfm i.succ)
          (fun i => hfl i.succ) T hm hl fun i => hi i.succ)
        (indepOn_blockProd (fun i => hd (Fin.succ_ne_zero i)) (hi' 0))
        (measurable_blockProd (fun i => hgm i.succ) hm')
        (memLp_blockProd hJ hE _ (pairwise_disjoint_succ hd) _ (fun i => hgm i.succ)
          (fun i => hgl i.succ) T' hm' hl' fun i => hi' i.succ),
      ih (fun i => parts i.succ) (pairwise_disjoint_succ hd) (fun i => f i.succ)
        (fun i => hfm i.succ) (fun i => hfl i.succ) (fun i => g i.succ) (fun i => hgm i.succ)
        (fun i => hgl i.succ) T hm hl (fun i => hi i.succ) T' hm' hl' (fun i => hi' i.succ),
      Fin.prod_univ_succ, mul_assoc]
end Products
section Norm
theorem norm_list_ofFn_prod_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ∀ {n : ℕ} (a : Fin n → H →L[ℂ] H), ‖(List.ofFn a).prod‖ ≤ ∏ i, ‖a i‖ := by
  intro n
  induction n with
  | zero =>
    intro a
    rw [List.ofFn_zero, List.prod_nil, Fin.prod_univ_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    intro a
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _))
end Norm
section Sections
variable {β : ℝ}
theorem continuous_sqrtLinkKernel_left (hR : SqrtLinkFacts.SqrtLinkKernelFacts) (hβ : 0 < β)
    (A : Type) [Finite A] (v : A → ComplexMatrix2.specialUnitary) :
    Continuous fun x : A → ComplexMatrix2.specialUnitary => sqrtLinkKernel β x v := by
  cases isEmpty_or_nonempty A with
  | inl h =>
    have e : (fun x : A → ComplexMatrix2.specialUnitary => sqrtLinkKernel β x v) =
        fun _ => 1 := by
      funext x
      simp [sqrtLinkKernel, finprod_of_isEmpty]
    rw [e]
    exact continuous_const
  | inr h =>
    obtain ⟨⟨-, -, hc⟩, -⟩ := (hR β hβ).1 A
    have hm : Continuous fun w : A → ComplexMatrix2.specialUnitary => (w, v) :=
      Continuous.prodMk continuous_id continuous_const
    have hcomp := hc.comp hm
    exact hcomp
theorem memLp_two_of_continuous {A : Type} [Finite A]
    {t : (A → ComplexMatrix2.specialUnitary) → ℂ} (ht : Continuous t) :
    MemLp t 2 (ComplexMatrix2.haarPi A) := by
  let ψ : C(A → ComplexMatrix2.specialUnitary, ℂ) := ⟨t, ht⟩
  exact MemLp.of_bound ht.aestronglyMeasurable ‖ψ‖
    (Filter.Eventually.of_forall fun w => ψ.norm_coe_le_norm w)
theorem sqrtKernelSandwich_one (hL : SandwichKernelLinearStatement)
    (hβ : 0 < β) (A : Type) [Finite A] (x y : A → ComplexMatrix2.specialUnitary) :
    sqrtKernelSandwich β 1 x y = linkProductKernel β x y := by
  cases isEmpty_or_nonempty A with
  | inr h => exact (hL β hβ A).2.1 x y
  | inl h =>
    have e : ∀ v : A → ComplexMatrix2.specialUnitary,
        sqrtLinkKernelSlice β v = toHaarL2 fun _ => 1 := by
      intro v
      unfold sqrtLinkKernelSlice
      congr 1
      funext w
      simp [sqrtLinkKernel, finprod_of_isEmpty]
    have hc := coe_toHaarL2 (I := A) (memLp_const (1 : ℂ))
    have hb : linkProductKernel β x y = 1 := by simp [linkProductKernel, finprod_of_isEmpty]
    simp only [sqrtKernelSandwich, ContinuousLinearMap.one_apply, e]
    rw [hb, L2.inner_def]
    refine (integral_congr_ae (g := fun _ => (1 : ℂ)) ?_).trans (by simp)
    filter_upwards [hc] with w h
    rw [h]
    simp
variable {B : Type} [Finite B]
def blockSlice (β : ℝ) {n : ℕ} (parts : Fin n → Set B) (v : B → ComplexMatrix2.specialUnitary)
    (i : Fin n) (x : ↥(parts i) → ComplexMatrix2.specialUnitary) : ℂ :=
  sqrtLinkKernel β x (restrictTo (parts i) v)
def restSlice (β : ℝ) (R : Set B) (v w : B → ComplexMatrix2.specialUnitary) : ℂ :=
  sqrtLinkKernel β (restrictTo R w) (restrictTo R v)
theorem sqrtLinkKernel_eq_prod {n : ℕ} {parts : Fin n → Set B} {R : Set B}
    (h : IsPartitionWithRest parts R) (w u : B → ComplexMatrix2.specialUnitary) :
    sqrtLinkKernel β w u =
      (∏ i, sqrtLinkKernel β (restrictTo (parts i) w) (restrictTo (parts i) u)) *
        sqrtLinkKernel β (restrictTo R w) (restrictTo R u) := by
  obtain ⟨-, hd, hR, hU⟩ := h
  let g : B → ℂ := fun b => sqrtKernel β (w b) (u b)
  have e : ∀ S : Set B, sqrtLinkKernel β (restrictTo S w) (restrictTo S u) =
      ∏ᶠ b ∈ S, g b := fun S => finprod_set_coe_eq_finprod_mem (f := g) S
  have e₀ : sqrtLinkKernel β w u = ∏ᶠ b ∈ (Set.univ : Set B), g b := by
    rw [finprod_mem_univ]
    rfl
  rw [e₀, ← hU,
    finprod_mem_union (Set.disjoint_iUnion_left.2 hR) (Set.toFinite _) (Set.toFinite _),
    finprod_mem_iUnion hd (fun _ => Set.toFinite _), finprod_eq_prod_of_fintype]
  simp only [e]
theorem sqrtLinkKernelSlice_eq {n : ℕ} {parts : Fin n → Set B} {R : Set B}
    (h : IsPartitionWithRest parts R) (v : B → ComplexMatrix2.specialUnitary) :
    sqrtLinkKernelSlice β v =
      toHaarL2 (blockProd parts (blockSlice β parts v) (restSlice β R v)) := by
  unfold sqrtLinkKernelSlice
  congr 1
  funext w
  exact sqrtLinkKernel_eq_prod h w v
end Sections
section Cases
variable {β : ℝ} {B : Type} [Finite B]
theorem tensorOne_eq_linkRelabelOp (hJ : GlueMeasurePreserving)
    (hF : SandwichKernelRelabelStatement) (hβ : 0 < β) {P : Set B}
    [Nonempty ↥P] (hP : ∀ b, b ∈ P) (X : HaarL2 ↥P →L[ℂ] HaarL2 ↥P) :
    tensorOne P X = linkRelabelOp (Subtype.val : ↥P → B) X := by
  have hb : Function.Bijective (Subtype.val : ↥P → B) :=
    ⟨Subtype.val_injective, fun b => ⟨⟨b, hP b⟩, rfl⟩⟩
  obtain ⟨-, hin, hval, -, -⟩ := hF β hβ ↥P B Subtype.val X hb
  have hinj : Function.Injective (linkRelabel (Subtype.val : ↥P → B)) := by
    intro φ ψ h
    have h₁ := hin φ φ
    have h₂ := hin φ ψ
    have h₃ := hin ψ φ
    have h₄ := hin ψ ψ
    rw [h] at h₁ h₂ h₃
    have h₀ : (inner ℂ (φ - ψ) (φ - ψ) : ℂ) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h₁, ← h₂, ← h₃, ← h₄]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h₀)
  let extend : (↥P → ComplexMatrix2.specialUnitary) → B → ComplexMatrix2.specialUnitary :=
    fun v b => v ⟨b, hP b⟩
  have hres := measurePreserving_restrictTo (B := B) hJ P
  have hext_m : Measurable extend := measurable_pi_lambda _ fun b => measurable_pi_apply _
  have e₁ : extend ∘ restrictTo P = id := by
    funext w b
    rfl
  have hext : MeasurePreserving extend (ComplexMatrix2.haarPi ↥P) (ComplexMatrix2.haarPi B) := by
    refine ⟨hext_m, ?_⟩
    rw [← hres.map_eq, Measure.map_map hext_m hres.measurable, e₁, Measure.map_id]
  have hG : ∀ F : HaarL2 B, Function.invFun (linkRelabel (Subtype.val : ↥P → B)) F =
      toHaarL2 fun v => F (extend v) := by
    intro F
    have hml : MemLp (fun v => F (extend v)) 2 (ComplexMatrix2.haarPi ↥P) :=
      (Lp.memLp F).comp_measurePreserving hext
    have hrG : linkRelabel (Subtype.val : ↥P → B) (toHaarL2 fun v => F (extend v)) = F := by
      have h := hres.quasiMeasurePreserving.ae_eq_comp (coe_toHaarL2 hml)
      have h' : (fun u' : B → ComplexMatrix2.specialUnitary =>
          ((toHaarL2 fun v => F (extend v) : HaarL2 ↥P) :
            (↥P → ComplexMatrix2.specialUnitary) → ℂ) (u' ∘ Subtype.val))
          =ᵐ[ComplexMatrix2.haarPi B] F := by
        filter_upwards [h] with w hw
        exact hw
      exact (toHaarL2_congr h').trans (toHaarL2_coe F)
    calc Function.invFun (linkRelabel (Subtype.val : ↥P → B)) F
        = Function.invFun (linkRelabel (Subtype.val : ↥P → B))
            (linkRelabel Subtype.val (toHaarL2 fun v => F (extend v))) := by rw [hrG]
      _ = toHaarL2 fun v => F (extend v) := Function.leftInverse_invFun hinj _
  have hT : ∀ F, linkRelabelOp (Subtype.val : ↥P → B) X F = tensorOneApply P X F := by
    intro F
    rw [hval F, hG F]
    unfold tensorOneApply
    rw [dif_pos hP]
    rfl
  refine ContinuousLinearMap.ext fun F => ?_
  exact (Classical.epsilon_spec (p := fun T : HaarL2 B →L[ℂ] HaarL2 B =>
    ∀ F, T F = tensorOneApply P X F) ⟨_, hT⟩ F).trans (hT F).symm
theorem formula_of_ne_univ (hO : TensorOneOnProductsForAll)
    (hS : TensorOneSeriesConvergesForAll)
    (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hL : SandwichKernelLinearStatement) (hβ : 0 < β) [Nonempty B]
    {n : ℕ} {parts : Fin n → Set B} {R : Set B}
    (Xs : ∀ i, HaarL2 ↥(parts i) →L[ℂ] HaarL2 ↥(parts i))
    (h : IsPartitionWithRest parts R) (hu : ∀ i, parts i ≠ Set.univ) :
    KernelProductFormula β parts R Xs := by
  obtain ⟨hn, hd, hdR, -⟩ := id h
  refine ⟨?_, fun u u' => ?_⟩
  · refine (norm_list_ofFn_prod_le _).trans
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_)
    exact (hS B (parts i) (hn i) (hu i) (Xs i)).2
  · have hSc : ∀ (v : B → ComplexMatrix2.specialUnitary) (i : Fin n),
        Continuous (blockSlice β parts v i) :=
      fun v i => continuous_sqrtLinkKernel_left hR hβ _ _
    have hTc : ∀ v : B → ComplexMatrix2.specialUnitary,
        Continuous fun x : ↥R → ComplexMatrix2.specialUnitary =>
          sqrtLinkKernel β x (restrictTo R v) :=
      fun v => continuous_sqrtLinkKernel_left hR hβ _ _
    have hm : ∀ v, Measurable (restSlice β R v) :=
      fun v => (hTc v).measurable.comp (measurable_restrictTo R)
    have hl : ∀ v, MemLp (restSlice β R v) 2 (ComplexMatrix2.haarPi B) :=
      fun v => (memLp_two_of_continuous (hTc v)).comp_measurePreserving
        (measurePreserving_restrictTo hJ R)
    have hi : ∀ v i, IndepOn (parts i) (restSlice β R v) := by
      intro v i w w' hww
      have e : restrictTo R w = restrictTo R w' :=
        funext fun b => hww b (Set.disjoint_right.1 (hdR i) b.2)
      simp only [restSlice, e]
    have hfm : ∀ v i, Measurable (blockSlice β parts v i) := fun v i => (hSc v i).measurable
    have hfl : ∀ v i, MemLp (blockSlice β parts v i) 2 (ComplexMatrix2.haarPi ↥(parts i)) :=
      fun v i => memLp_two_of_continuous (hSc v i)
    have hrep : ∀ i, Measurable (Xs i (toHaarL2 (blockSlice β parts u' i)) :
        (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ) :=
      fun i => (Lp.stronglyMeasurable _).measurable
    have hrepl : ∀ i, MemLp (Xs i (toHaarL2 (blockSlice β parts u' i)) :
        (↥(parts i) → ComplexMatrix2.specialUnitary) → ℂ) 2
        (ComplexMatrix2.haarPi ↥(parts i)) := fun i => Lp.memLp _
    change (inner ℂ (sqrtLinkKernelSlice β u)
      (tensorOneProduct parts Xs (sqrtLinkKernelSlice β u')) : ℂ) = _
    rw [sqrtLinkKernelSlice_eq h u, sqrtLinkKernelSlice_eq h u', tensorOneProduct,
      tensorOneList_apply_blockProd hO hJ hE parts hd hn hu Xs _ (hfm u') (hfl u') _ (hm u')
        (hl u') (hi u'),
      inner_blockProd hJ hE parts hd _ (hfm u) (hfl u) _ hrep hrepl _ (hm u) (hl u) (hi u) _
        (hm u') (hl u') (hi u')]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [toHaarL2_coe]
      rfl
    · have e := inner_comp_restrictTo hJ R (memLp_two_of_continuous (hTc u))
        (memLp_two_of_continuous (hTc u'))
      exact e.trans (sqrtKernelSandwich_one hL hβ ↥R _ _)
end Cases
theorem sandwichKernelProduct (hO : TensorOneOnProductsForAll)
    (hS : TensorOneSeriesConvergesForAll)
    (hJ : GlueMeasurePreserving)
    (hE : TensorFnMemL2Inner)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hL : SandwichKernelLinearStatement)
    (hF : SandwichKernelRelabelStatement) : SandwichKernelProductStatement := by
  intro β hβ B _ _ n parts R Xs h
  by_cases hw : ∃ i, parts i = Set.univ
  · obtain ⟨i, hi⟩ := hw
    have hall : ∀ j, j = i := by
      intro j
      by_contra hne
      obtain ⟨b, hb⟩ := h.1 j
      exact Set.disjoint_left.1 (h.2.1 hne) hb (hi ▸ Set.mem_univ b)
    have hn : n = 1 := by simpa using Fintype.card_eq_one_iff.2 ⟨i, hall⟩
    subst hn
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have hP : ∀ b, b ∈ parts 0 := fun b => hi ▸ Set.mem_univ b
    have : Nonempty ↥(parts 0) := (h.1 0).to_subtype
    have hRe : IsEmpty ↥R := ⟨fun b => Set.disjoint_left.1 (h.2.2.1 0) (hP b.1) b.2⟩
    have hprod : tensorOneProduct parts Xs =
        linkRelabelOp (Subtype.val : ↥(parts 0) → B) (Xs 0) := by
      rw [← tensorOne_eq_linkRelabelOp hJ hF hβ hP (Xs 0)]
      simp [tensorOneProduct]
    obtain ⟨-, -, -, hnorm, hker⟩ := hF β hβ ↥(parts 0) B Subtype.val (Xs 0)
      ⟨Subtype.val_injective, fun b => ⟨⟨b, hP b⟩, rfl⟩⟩
    refine ⟨?_, fun u u' => ?_⟩
    · rw [hprod, hnorm]
      simp
    · rw [hprod, hker, finprod_of_isEmpty, mul_one, Fin.prod_univ_one]
      rfl
  · exact formula_of_ne_univ hO hS hJ hE hR hL hβ Xs h fun i e => hw ⟨i, e⟩
end YangMills.Construction.TransferOperators.SandwichProduct
end
