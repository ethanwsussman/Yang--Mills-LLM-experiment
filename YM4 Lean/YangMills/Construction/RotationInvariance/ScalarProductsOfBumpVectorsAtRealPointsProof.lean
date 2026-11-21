import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.EuclideanFunctionals.RulesForTheTensorComponentsProof
import YangMills.Construction.EuclideanFunctionals.VectorsOfPlatesAndTheProductFormula
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctions
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import YangMills.Construction.RotationInvariance.ScalarProductsOfBumpVectorsAtRealPoints
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube ReflectionPositivity.AxisMirror
namespace EuclideanFunctionals.MollifierInnerAtRealPoints
open PlateVectorsProduct
def mollifierProduct (ρ : RealPlane → ℝ) (u : RealPlane) (ψ : RealPlane → ℝ) : R4 → ℂ :=
  productFunction (translateProfile u (ofRealFun ρ)) ψ
def realMollifierProduct (ρ : RealPlane → ℝ) (u : RealPlane) (ψ : RealPlane → ℝ) :
    R4 → ℝ :=
  fun x => (mollifierProduct ρ u ψ x).re
theorem mollifierProduct_apply (ρ : RealPlane → ℝ) (u : RealPlane) (ψ : RealPlane → ℝ)
    (x : R4) :
    mollifierProduct ρ u ψ x = ((ρ (planeComponent x - u) * ψ (orthogonalComponent x) : ℝ) : ℂ) := by
  simp [mollifierProduct, productFunction, translateProfile, ofRealFun]
theorem realMollifierProduct_apply (ρ : RealPlane → ℝ) (u : RealPlane)
    (ψ : RealPlane → ℝ) (x : R4) :
    realMollifierProduct ρ u ψ x = ρ (planeComponent x - u) * ψ (orthogonalComponent x) := by
  rw [realMollifierProduct, mollifierProduct_apply, Complex.ofReal_re]
theorem isRealValued_mollifierProduct (ρ : RealPlane → ℝ) (u : RealPlane)
    (ψ : RealPlane → ℝ) : IsRealValued (mollifierProduct ρ u ψ) := fun x => by
  rw [mollifierProduct_apply, Complex.ofReal_im]
theorem supp_mollifierProduct (ρ : RealPlane → ℝ) (u : RealPlane)
    (ψ : RealPlane → ℝ) : supp (mollifierProduct ρ u ψ) = supp (realMollifierProduct ρ u ψ) := by
  have hset : {x | mollifierProduct ρ u ψ x ≠ 0} = {x | realMollifierProduct ρ u ψ x ≠ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, mollifierProduct_apply, realMollifierProduct_apply, ne_eq,
      Complex.ofReal_eq_zero]
  change MetricNotions.closureWrt _ {x | mollifierProduct ρ u ψ x ≠ 0} =
    MetricNotions.closureWrt _ {x | realMollifierProduct ρ u ψ x ≠ 0}
  rw [hset]
theorem realMollifierProduct_mem_C1c {ρ : RealPlane → ℝ} {u : RealPlane}
    {ψ : RealPlane → ℝ} (h : mollifierProduct ρ u ψ ∈ C1c ℂ) :
    realMollifierProduct ρ u ψ ∈ C1c ℝ := by
  refine ⟨?_, ?_⟩
  · have hc : ContDiff ℝ 1 (mollifierProduct ρ u ψ) := h.1
    exact Complex.reCLM.contDiff.comp hc
  · have h₂ := h.2
    change MetricNotions.IsCompactWrt _ (supp (mollifierProduct ρ u ψ)) at h₂
    change MetricNotions.IsCompactWrt _ (supp (realMollifierProduct ρ u ψ))
    rw [← supp_mollifierProduct]
    exact h₂
theorem norm_reflectFirst_sub (y u : RealPlane) : ‖reflectFirst y - u‖ = ‖y - reflectFirst u‖ := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  congr 1
  simp [reflectFirst]
  ring
theorem mirror_actFn_realMollifierProduct
    (hMot : TranslationRules.MotionsOnPlaneFactor)
    {ρ : RealPlane → ℝ} (hρ : ofRealFun ρ ∈ complexProfiles)
    (hrad : ∀ y y', ‖y‖ = ‖y'‖ → ρ y = ρ y') (u : RealPlane) {ψ : RealPlane → ℝ}
    (hψ : ψ ∈ realLabels) :
    timeFlip.actFn (realMollifierProduct ρ u ψ) = realMollifierProduct ρ (reflectFirst u) ψ := by
  have hu := (hMot _ hρ ψ hψ u 0).2.2.2.1
  have h := (hMot _ hu ψ hψ 0 0).2.2.1
  have e₁ : (fun x => conj (productFunction (translateProfile u (ofRealFun ρ)) ψ x)) =
      mollifierProduct ρ u ψ := by
    funext x
    change conj (mollifierProduct ρ u ψ x) = _
    rw [mollifierProduct_apply, Complex.conj_ofReal]
  have e₂ : (fun y => conj (translateProfile u (ofRealFun ρ) y)) ∘ reflectFirst =
      translateProfile (reflectFirst u) (ofRealFun ρ) := by
    funext y
    simp only [Function.comp, translateProfile, ofRealFun, Complex.conj_ofReal]
    rw [hrad _ _ (norm_reflectFirst_sub y u)]
  rw [e₁, e₂] at h
  funext x
  exact congrArg Complex.re (congrFun h x)
theorem complexTuple_of_real {n : ℕ} (h : Fin n → R4 → ℂ)
    (hr : ∀ l, IsRealValued (h l)) :
    complexTuple h = toFree (List.ofFn fun l x => (h l x).re) := by
  rw [complexTuple, if_pos hr]
theorem complexTuple_cast {p r : ℕ} (e : p = r) (h : Fin r → R4 → ℂ) :
    complexTuple (fun k : Fin p => h (Fin.cast e k)) = complexTuple h := by
  subst e
  rfl
theorem centeredFnFree_toFree (S : ConnFamily) {X : FnList} (h : X ∈ sepAll) :
    centeredFnFree S (toFree X) = (centeredFn S ⟨X, h⟩ : ℂ) :=
  liftLin_toFree _ ⟨X, h⟩
theorem freeConj_toFree {X : FnList} (h : X ∈ sepAll) : freeConj (toFree X) = toFree X := by
  rw [toFree_of_mem h, freeConj, Finsupp.mapRange_single, map_one]
theorem freeMul_toFree {X Y : FnList} (hX : X ∈ sepAll) (hY : Y ∈ sepAll) :
    freeMul (toFree X) (toFree Y) = toFree (listAppend X Y) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeMul_toFree <;> assumption
theorem inner_classOrZero_toFree {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S)
    {X Y : FnList} (hX : X ∈ sepAll) (hY : Y ∈ sepAll) (hA : timeFlip.actList X ∈ sepAll)
    (hXm : toFree X ∈ finCombIn upperHalf)
    (hYm : toFree Y ∈ finCombIn upperHalf) :
    ⟪readClass σ.recon.cls (toFree X), readClass σ.recon.cls (toFree Y)⟫_ℂ =
      centeredFnFree S (toFree (listAppend (timeFlip.actList X) Y)) := by
  rw [readClass, readClass, dif_pos hXm, dif_pos hYm, σ.recon.inner_cls]
  change centeredFnFree S (freeMul (timeFlip.actFree (freeConj (toFree X))) (toFree Y)) = _
  have hm : timeFlip.actFree (toFree X) = toFree (timeFlip.actList X) :=
    liftLin_toFree _ ⟨X, hX⟩
  rw [freeConj_toFree hX, hm, freeMul_toFree hA hY]
def revLeft (n n' : ℕ) : Equiv.Perm (Fin (n + n')) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv)
theorem revLeft_castAdd (n n' : ℕ) (i : Fin n) :
    revLeft n n' (Fin.castAdd n' i) = Fin.castAdd n' (Fin.rev i) := by
  simp [revLeft]
theorem revLeft_natAdd (n n' : ℕ) (i : Fin n') :
    revLeft n n' (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [revLeft]
def mollifierFamily {p : ℕ} (ρ : RealPlane → ℝ) (c : Fin p → RealPlane)
    (ψ : Fin p → realLabels) : Fin p → R4 → ℝ :=
  fun i => realMollifierProduct ρ (c i) (ψ i)
section
variable {n n' : ℕ} (a : Fin n → RealPlane) (b : Fin n' → RealPlane)
theorem reflectAppend_castAdd_rev (i : Fin n) :
    reflectAppend a b (Fin.castAdd n' (Fin.rev i)) = reflectFirst (a i) := by
  rw [reflectAppend, Fin.append_left, Fin.rev_rev]
theorem reflectAppend_natAdd (i : Fin n') : reflectAppend a b (Fin.natAdd n i) = b i := by
  rw [reflectAppend, Fin.append_right]
theorem gramLabelOrder_castAdd_rev (φ : Fin n → realLabels) (φ' : Fin n' → realLabels)
    (i : Fin n) : gramLabelOrder φ φ' (Fin.castAdd n' (Fin.rev i)) = φ i := by
  rw [gramLabelOrder, Fin.append_left, Fin.rev_rev]
theorem gramLabelOrder_natAdd (φ : Fin n → realLabels) (φ' : Fin n' → realLabels) (i : Fin n') :
    gramLabelOrder φ φ' (Fin.natAdd n i) = φ' i := by
  rw [gramLabelOrder, Fin.append_right]
theorem reflectAppend_time_lt (i : ℕ) (hi : i < n) :
    reflectAppend a b ⟨i, by omega⟩ 0 = -a ⟨n - 1 - i, by omega⟩ 0 := by
  have e : (⟨i, by omega⟩ : Fin (n + n')) = Fin.castAdd n' (Fin.rev ⟨n - 1 - i, by omega⟩) := by
    ext
    simp [Fin.val_rev]
    omega
  rw [e, reflectAppend_castAdd_rev]
  simp [reflectFirst]
theorem reflectAppend_time_ge (i : ℕ) (hi : n ≤ i) (h₂ : i < n + n') :
    reflectAppend a b ⟨i, h₂⟩ 0 = b ⟨i - n, by omega⟩ 0 := by
  have e : (⟨i, h₂⟩ : Fin (n + n')) = Fin.natAdd n ⟨i - n, by omega⟩ := by
    ext
    simp
    omega
  rw [e, reflectAppend_natAdd]
theorem time_gap_of_ordered {η : ℝ} {a : Fin n → RealPlane} {b : Fin n' → RealPlane}
    (ha : a ∈ orderedTimeTuples n η) (hb : b ∈ orderedTimeTuples n' η) (k : ℕ)
    (hk : k + 1 < n + n') :
    η / 2 ≤ reflectAppend a b ⟨k + 1, hk⟩ 0 - reflectAppend a b ⟨k, by omega⟩ 0 := by
  rcases lt_trichotomy (k + 1) n with h | h | h
  · rw [reflectAppend_time_lt a b (k + 1) h, reflectAppend_time_lt a b k (by omega)]
    have h₁ := ha.2 (n - 2 - k) (by omega)
    have e₁ : (⟨n - 1 - k, by omega⟩ : Fin n) = ⟨n - 2 - k + 1, by omega⟩ := Fin.ext (by simp; omega)
    have e₂ : (⟨n - 1 - (k + 1), by omega⟩ : Fin n) = ⟨n - 2 - k, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e₁, e₂]
    linarith
  · rw [reflectAppend_time_ge a b (k + 1) (by omega) hk, reflectAppend_time_lt a b k (by omega)]
    have h₁ := ha.1 (by omega)
    have h₂ := hb.1 (by omega)
    have e₁ : (⟨n - 1 - k, by omega⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    have e₂ : (⟨k + 1 - n, by omega⟩ : Fin n') = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    rw [e₁, e₂]
    linarith
  · rw [reflectAppend_time_ge a b (k + 1) (by omega) hk,
      reflectAppend_time_ge a b k (by omega) (by omega)]
    have h₁ := hb.2 (k - n) (by omega)
    have e₁ : (⟨k + 1 - n, by omega⟩ : Fin n') = ⟨k - n + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e₁]
    linarith
end
theorem realTuple_mem_successiveDomain (hA : GramKernelArgsFacts) {p : ℕ} {η : ℝ} (hη : 0 < η)
    {c : Fin p → RealPlane} (hc : c ∈ orderedTimeTuples p η) :
    realTuple c ∈ successiveDomain p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun i h => absurd h (by omega)⟩
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hmono : StrictMono fun i => c i 0 := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have h : c i.succ 0 - c i.castSucc 0 > η / 2 := hc.2 i (by omega)
      change c i.castSucc 0 < c i.succ 0
      linarith
    have hpos : 0 < c ⟨0, by omega⟩ 0 := by
      have h := hc.1 (by omega)
      linarith
    have hmem : realTuple c ∈ successiveDomain (q + 1) ∩ Set.range realTuple := by
      rw [(hA.1 (q + 1) (by omega)).1]
      exact ⟨c, ⟨hpos, hmono⟩, rfl⟩
    exact hmem.1
theorem holds (hP : PlateVectorsProduct.Holds)
    (hE : RealTuples.realFunctionTuples)
    (hM : TranslationRules.TranslationAndMotionFacts)
    (hI : MomentSymmetry.ReductionHolds)
    (hA : GramKernelArgsFacts)
    (hF : CenteredInitialValues.InitialValues) :
    MollifierInnerAtRealPoints.Holds := by
  intro m S d η hη δ hδ j n n' φ φ' a ha b hb
  obtain ⟨-, hMot, hC1, -⟩ := hM
  have hTwo := (hE m S d).2.2
  obtain ⟨hη0, hη1⟩ := hη
  have hrp := hδ.ofRealFun_mem hη0 j
  have hprod : ∀ (u : RealPlane) (ψ : RealPlane → ℝ), ψ ∈ realLabels →
      mollifierProduct (δ j) u ψ ∈ C1c ℂ := fun u ψ hψ =>
    (hC1 _ (hMot _ hrp.1 ψ hψ u 0).2.2.2.1 ψ hψ).1
  have hreal : ∀ (u : RealPlane) (ψ : RealPlane → ℝ), ψ ∈ realLabels →
      realMollifierProduct (δ j) u ψ ∈ C1c ℝ := fun u ψ hψ =>
    realMollifierProduct_mem_C1c (hprod u ψ hψ)
  have hsep : ∀ (p : ℕ) (f : Fin p → R4 → ℝ), (∀ l, f l ∈ C1c ℝ) →
      (Pairwise fun k l => Disjoint (supp (f k)) (supp (f l))) →
      List.ofFn f ∈ sepAll := by
    intro p f hm hd
    rcases p with _ | p
    · rw [List.ofFn_zero]
      exact (Ambient.nil_mem_separatedWithin defaultMirrorData Ambient.euclidean upperHalf).1
    · exact Ambient.separatedN_subset_separatedAll _ _ (p + 1) (hTwo (p + 1) (by omega) f hm hd).1
  let C : (RealPlane → ℝ) → ℝ := fun ψ =>
    open Classical in if h : ψ ∈ realLabels then d.base.labelConst ⟨ψ, h⟩ else 0
  have hC : ∀ ψ ∈ realLabels, ProductBoundWith d.base.sigma d.base.expo_pos
      d.base.frac_mem ψ (C ψ) := by
    intro ψ hψ
    simp only [C, dif_pos hψ]
    exact d.base.boundWith_labelConst ⟨ψ, hψ⟩
  have hPη := hP m S d.base.sigma d.base.expo d.base.frac
    d.base.expo_pos d.base.frac_mem C d.base.productBoundWithExponent hC
    d.base.cone η hη0 hη1
  have hvec : ∀ (p : ℕ) (ψ : Fin p → realLabels) (c : Fin p → RealPlane),
      c ∈ orderedTimeTuples p η →
      List.ofFn (mollifierFamily (δ j) c ψ) ∈ sepAll ∧
      toFree (List.ofFn (mollifierFamily (δ j) c ψ)) ∈ finCombIn upperHalf ∧
      d.mollifierVector η δ j ψ (realTuple c) =
        readClass d.base.sigma.recon.cls
          (toFree (List.ofFn (mollifierFamily (δ j) c ψ))) := by
    intro p ψ c hc
    have hL : LabelsProfilesInDisc d.base.frac η
        (fun _ : Fin p => ofRealFun (δ j)) (fun i => (ψ i : RealPlane → ℝ)) :=
      fun i => ⟨(ψ i).2, hrp.1, hrp.2⟩
    obtain ⟨hdis, -, -, hmem, hval⟩ := (hPη.1 p _ _ hL).2.2.2.2 c
      ⟨fun h => (hc.1 h).le, fun i h => (hc.2 i h).le⟩
    have htr : shiftedProducts c (fun _ : Fin p => ofRealFun (δ j))
        (fun i => (ψ i : RealPlane → ℝ)) = fun i => mollifierProduct (δ j) (c i) (ψ i) :=
      funext fun i => (hMot _ hrp.1 _ (ψ i).2 (c i) 0).1
    rw [htr] at hdis hmem hval
    have htw : entryProduct (fun i => mollifierProduct (δ j) (c i) (ψ i)) =
        toFree (List.ofFn (mollifierFamily (δ j) c ψ)) :=
      complexTuple_of_real _ fun l => isRealValued_mollifierProduct _ _ _
    rw [htw] at hmem hval
    refine ⟨hsep _ _ (fun l => hreal _ _ (ψ l).2) ?_, hmem, hval⟩
    intro k l hkl
    have h : Disjoint (supp (mollifierProduct (δ j) (c k) (ψ k)))
        (supp (mollifierProduct (δ j) (c l) (ψ l))) := hdis hkl
    rw [supp_mollifierProduct, supp_mollifierProduct] at h
    exact h
  obtain ⟨hXs, hXm, hXv⟩ := hvec n φ a ha
  obtain ⟨hYs, hYm, hYv⟩ := hvec n' φ' b hb
  have hmir : timeFlip.actList (List.ofFn (mollifierFamily (δ j) a φ)) =
      List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ) := by
    rw [EuclidMotion.actList, List.map_ofFn]
    congr 1
    funext i
    exact mirror_actFn_realMollifierProduct hMot hrp.1 (hδ.norm_eq j) (a i) (φ i).2
  have hchain : List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ) ∈ sepAll →
      ⟪d.mollifierVector η δ j φ (realTuple a), d.mollifierVector η δ j φ' (realTuple b)⟫_ℂ =
        centeredFnFree S (toFree (listAppend
          (List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ))
          (List.ofFn (mollifierFamily (δ j) b φ')))) := by
    intro hAs
    rw [hXv, hYv, inner_classOrZero_toFree d.base.sigma hXs hYs (hmir ▸ hAs) hXm hYm, hmir]
  have hlen : (listAppend (List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ))
      (List.ofFn (mollifierFamily (δ j) b φ'))).length = n + n' := by
    change (List.ofFn _ ++ List.ofFn _).length = _
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  rw [PlaneDataWithAperture.mollifierGramValue]
  by_cases hN : 2 ≤ n + n'
  · rw [dif_pos hN]
    have hq : n + n' - 1 + 1 = n + n' := by omega
    have hL : LabelsProfilesInDisc d.base.frac η
        (fun _ : Fin (n + n' - 1 + 1) => ofRealFun (δ j))
        (fun k => (gramLabelOrder φ φ' (Fin.cast hq k) : RealPlane → ℝ)) :=
      fun k => ⟨(gramLabelOrder φ φ' _).2, hrp.1, hrp.2⟩
    have hgap : ∀ i, η / 2 ≤ successiveDiffs
        (fun k : Fin (n + n' - 1 + 1) => reflectAppend a b (Fin.cast hq k)) i 0 := by
      intro i
      have h := time_gap_of_ordered ha hb i (by have := i.2; omega)
      simp only [successiveDiffs, PiLp.sub_apply]
      exact h
    obtain ⟨hdis, hval⟩ := (hPη.2 _ _ _ hL).2.2 _ hgap
    have hVdis : Pairwise fun k l : Fin (n + n') =>
        Disjoint (supp (mollifierProduct (δ j) (reflectAppend a b k) (gramLabelOrder φ φ' k)))
          (supp (mollifierProduct (δ j) (reflectAppend a b l) (gramLabelOrder φ φ' l))) := by
      intro k l hkl
      exact hdis (i := Fin.cast hq.symm k) (j := Fin.cast hq.symm l)
        fun e => hkl (Fin.cast_injective hq.symm e)
    have hV : ComplexComponents fun k : Fin (n + n') =>
        mollifierProduct (δ j) (reflectAppend a b k) (gramLabelOrder φ φ' k) :=
      ⟨by omega, fun k => hprod _ _ (gramLabelOrder φ φ' k).2, hVdis⟩
    have hSym := (hI m S d.base.sigma).1 (n + n') hN (revLeft n n') _ hV
    have hcast := complexTuple_cast hq fun k : Fin (n + n') =>
      mollifierProduct (δ j) (reflectAppend a b k) (gramLabelOrder φ φ' k)
    have hW : complexTuple ((fun k : Fin (n + n') =>
        mollifierProduct (δ j) (reflectAppend a b k) (gramLabelOrder φ φ' k)) ∘ revLeft n n') =
        toFree (listAppend (List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ))
          (List.ofFn (mollifierFamily (δ j) b φ'))) := by
      refine (complexTuple_of_real _ fun l => isRealValued_mollifierProduct _ _ _).trans ?_
      congr 1
      rw [List.ofFn_add]
      refine congrArg₂ (· ++ ·) (congrArg List.ofFn (funext fun i => ?_))
        (congrArg List.ofFn (funext fun i => ?_))
      · change (fun x => (mollifierProduct (δ j)
            (reflectAppend a b (revLeft n n' (Fin.castAdd n' i)))
            (gramLabelOrder φ φ' (revLeft n n' (Fin.castAdd n' i))) x).re) = _
        rw [revLeft_castAdd, reflectAppend_castAdd_rev, gramLabelOrder_castAdd_rev]
        rfl
      · rw [revLeft_natAdd, reflectAppend_natAdd, gramLabelOrder_natAdd]
        rfl
    have hAs : List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ) ∈ sepAll := by
      refine hsep _ _ (fun l => hreal _ _ (φ l).2) ?_
      intro k l hkl
      have h := hVdis (i := Fin.castAdd n' (Fin.rev k)) (j := Fin.castAdd n' (Fin.rev l))
        fun e => hkl (Fin.rev_injective (Fin.castAdd_injective _ _ e))
      beta_reduce at h
      rw [reflectAppend_castAdd_rev, reflectAppend_castAdd_rev, gramLabelOrder_castAdd_rev,
        gramLabelOrder_castAdd_rev, supp_mollifierProduct, supp_mollifierProduct] at h
      exact h
    have hargs : gramKernelArgs (realTuple a) (realTuple b) = fun i =>
        embedPlane (successiveDiffs
          (fun k : Fin (n + n' - 1 + 1) => reflectAppend a b (Fin.cast hq k)) i) :=
      funext fun k => (hA.2.2.1 n n' hN a b (realTuple_mem_successiveDomain hA hη0 ha)
        (realTuple_mem_successiveDomain hA hη0 hb)).1 k
    rw [hchain hAs, ← hW, hSym, ← hcast, hargs]
    exact hval
  · rw [dif_neg hN]
    have hn1 : n ≤ 1 := by omega
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn1
    have hAs : List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ) ∈ sepAll :=
      hsep _ _ (fun l => hreal _ _ (φ l).2) fun k l hkl => (hkl (Subsingleton.elim k l)).elim
    rw [hchain hAs]
    by_cases h0 : n + n' = 0
    · rw [if_pos h0, List.eq_nil_of_length_eq_zero (hlen.trans h0)]
      have hmem : ([] : FnList) ∈ sepAll :=
        (Ambient.nil_mem_separatedWithin defaultMirrorData Ambient.euclidean upperHalf).1
      have h₁ : centeredFn S ⟨[], hmem⟩ = 1 := (hF S).1
      rw [centeredFnFree_toFree S hmem, h₁, Complex.ofReal_one]
    · rw [if_neg h0]
      obtain ⟨f, hf⟩ := List.length_eq_one_iff.1 (hlen.trans (by omega : n + n' = 1))
      have hfm : f ∈ C1c ℝ := by
        have hmem : f ∈ listAppend
            (List.ofFn (mollifierFamily (δ j) (fun i => reflectFirst (a i)) φ))
            (List.ofFn (mollifierFamily (δ j) b φ')) := by
          rw [hf]
          exact List.mem_singleton.2 rfl
        rcases List.mem_append.1 hmem with h | h
        · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 h
          exact hreal _ _ (φ i).2
        · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 h
          exact hreal _ _ (φ' i).2
      have h₁ := (hF S).2.1 f hfm
      rw [hf]
      exact (centeredFnFree_toFree S
        (CenteredInitialValues.singleSep hfm).2).trans
        ((congrArg (fun r : ℝ => (r : ℂ)) h₁).trans Complex.ofReal_zero)
end EuclideanFunctionals.MollifierInnerAtRealPoints
end YangMills.Construction
end
