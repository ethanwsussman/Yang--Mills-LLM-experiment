import YangMills.Construction.ComplexAnalysis.BanachValuedAffineCoordinates
import YangMills.Construction.ComplexAnalysis.ScalarHolomorphyAgreement
import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import YangMills.Construction.EuclideanFunctionals.ForwardTubeAndTheSemigroupOfItsOperators
import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.EuclideanFunctionals.OperatorsOfThePlaneSemigroupExpansionAndProductsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.PlateOperatorOfAProfileInADisc
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntriesProof
import YangMills.Construction.EuclideanFunctionals.VectorsOfPlatesAndTheProductFormula
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PlateVectorsProduct
open ForwardTube RealPlane EuclidFunctionalWithRecon
open TupleConcat
open TubeSemigroup (RealPoints WordBounds)
variable {m : SharpScale} {S : ConnFamily}
theorem tubeWord_eq_apply_alternatingVec (σ : EuclidFunctionalWithRecon m S) :
    ∀ (n : ℕ) (B : Fin (n + 1) → σ.space →L[ℂ] σ.space) (u : Fin n → ℂ × ℂ),
      σ.tubeWord σ.recon.vac n B u =
        B 0 (σ.alternatingVec n u (Fin.tail B))
  | 0, _, _ => rfl
  | n + 1, B, u => by
    have h := tubeWord_eq_apply_alternatingVec σ n (Fin.tail B) (Fin.tail u)
    simp only [tubeWord, alternatingVec, h]
theorem alternatingVec_eq_tubeWord (σ : EuclidFunctionalWithRecon m S) (n : ℕ)
    (B : Fin n → σ.space →L[ℂ] σ.space) (w : Fin n → ℂ × ℂ) :
    σ.alternatingVec n w B =
      σ.tubeWord σ.recon.vac n
        (Fin.cons (α := fun _ => σ.space →L[ℂ] σ.space) 1 B) w := by
  rw [tubeWord_eq_apply_alternatingVec]
  simp [Fin.tail_cons]
theorem mem_shiftedTuples_iff (A : Set (ℂ × ℂ)) (n : ℕ) (η : ℝ) (x : Fin n → ℂ × ℂ) :
    x ∈ shiftedTuples A n η ↔ ∀ a, productArgs η x a ∈ A := by
  constructor
  · rintro ⟨h0, hs⟩ ⟨a, ha⟩
    cases a with
    | zero => simpa [productArgs] using h0 ha
    | succ i => simpa [productArgs] using hs i ha
  · intro H
    refine ⟨fun h => ?_, fun i h => ?_⟩
    · simpa [productArgs] using H ⟨0, h⟩
    · simpa [productArgs] using H ⟨i + 1, h⟩
def successiveDifferences (n : ℕ) : (Fin n → ℂ × ℂ) →ₗ[ℂ] (Fin n → ℂ × ℂ) where
  toFun x a := if h : (a : ℕ) = 0 then x a else x a - x ⟨a - 1, by omega⟩
  map_add' x y := by
    funext a
    by_cases h : (a : ℕ) = 0
    · simp [h]
    · simp only [h, dite_false, Pi.add_apply]
      abel
  map_smul' c x := by
    funext a
    by_cases h : (a : ℕ) = 0
    · simp [h]
    · simp only [h, dite_false, Pi.smul_apply, RingHom.id_apply, smul_sub]
theorem successiveDifferences_injective (n : ℕ) : Function.Injective (successiveDifferences n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ (k : ℕ) (h : k < n), x ⟨k, h⟩ = 0 := by
    intro k
    induction k with
    | zero =>
      intro h
      simpa [successiveDifferences] using congrFun hx ⟨0, h⟩
    | succ k ih =>
      intro h
      have h1 := congrFun hx ⟨k + 1, h⟩
      simp only [successiveDifferences, LinearMap.coe_mk, AddHom.coe_mk, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, dite_false, Nat.add_sub_cancel, Pi.zero_apply] at h1
      rw [ih (by omega), sub_zero] at h1
      exact h1
  funext a
  exact key a a.2
def argumentOffset (n : ℕ) (η : ℝ) (a : Fin n) : ℂ × ℂ :=
  if (a : ℕ) = 0 then -timeTranslate (η / 4) else -timeTranslate (η / 2)
theorem productArgs_eq {n : ℕ} (η : ℝ) (x : Fin n → ℂ × ℂ) :
    productArgs η x = successiveDifferences n x + argumentOffset n η := by
  funext a
  by_cases h : (a : ℕ) = 0
  · simp [productArgs, successiveDifferences, argumentOffset, h, sub_eq_add_neg]
  · simp [productArgs, successiveDifferences, argumentOffset, h, sub_eq_add_neg]
def pairTupleLinearEquiv (q : ℕ) : (Fin q → ℂ × ℂ) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (q * 2) where
  toEquiv := pairTupleEquiv q
  map_add' v w := by
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    match j with
    | 0 => simp [pairTupleEquiv_apply_fst]
    | 1 => simp [pairTupleEquiv_apply_snd]
  map_smul' c v := by
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    match j with
    | 0 => simp [pairTupleEquiv_apply_fst]
    | 1 => simp [pairTupleEquiv_apply_snd]
theorem holomorphicVectorOnTuples_comp_affine
    (hF : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {q : ℕ} (hq : 1 ≤ q)
    (D : (Fin q → ℂ × ℂ) →ₗ[ℂ] (Fin q → ℂ × ℂ)) (hD : Function.Injective D)
    (s : Fin q → ℂ × ℂ) {O : Set (Fin q → ℂ × ℂ)} {g : (Fin q → ℂ × ℂ) → Y}
    (hg : HolomorphicVectorOnTuples O g) :
    HolomorphicVectorOnTuples {x | D x + s ∈ O} fun x => g (D x + s) := by
  set L := pairTupleLinearEquiv q with hLdef
  have hLc : ∀ v, L v = pairTupleEquiv q v := fun _ => rfl
  have hLs : ∀ z, L.symm z = (pairTupleEquiv q).symm z := fun _ => rfl
  set Dc : Coordinates.ComplexCoordinates (q * 2) →ₗ[ℂ] Coordinates.ComplexCoordinates (q * 2) :=
    L.toLinearMap ∘ₗ D ∘ₗ L.symm.toLinearMap with hDc
  set J : Matrix (Fin (q * 2)) (Fin (q * 2)) ℂ := LinearMap.toMatrix' Dc with hJdef
  have hJv : ∀ z, J.mulVec z = Dc z := fun z => LinearMap.toMatrix'_mulVec Dc z
  have hJ : IsUnit J := by
    refine Matrix.mulVec_injective_iff_isUnit.1 ?_
    intro z z' h
    have h' : Dc z = Dc z' := by rw [← hJv, ← hJv]; exact h
    exact L.symm.injective (hD (L.injective h'))
  have key : ∀ z, J.mulVec z + L s = L (D (L.symm z) + s) := by
    intro z
    rw [hJv, map_add]
    rfl
  have h1 := (hF Y (q * 2) (by omega) _ _ hg).2.2 J (L s) hJ |>.1
  have hset : {z | J.mulVec z + L s ∈ pairTupleEquiv q '' O} =
      pairTupleEquiv q '' {x | D x + s ∈ O} := by
    ext z
    rw [Equiv.image_eq_preimage_symm, Equiv.image_eq_preimage_symm]
    simp only [mem_ofPred_eq, mem_preimage]
    rw [key, hLc, Equiv.symm_apply_apply, ← hLs]
  have hfun : (fun z => (g ∘ (pairTupleEquiv q).symm) (J.mulVec z + L s)) =
      (fun x => g (D x + s)) ∘ (pairTupleEquiv q).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [key, hLc, Equiv.symm_apply_apply, ← hLs]
  rw [hset, hfun] at h1
  exact h1
theorem embedPlane_add (y y' : RealPlane) : embedPlane (y + y') = embedPlane y + embedPlane y' := by
  simp [embedPlane]
theorem embedPlane_sub (y y' : RealPlane) : embedPlane (y - y') = embedPlane y - embedPlane y' := by
  simp [embedPlane]
theorem embedPlane_smul_unitX (s : ℝ) : embedPlane (s • unitX) = timeTranslate s := by
  simp [embedPlane, timeTranslate, unitX]
theorem smul_unitX_apply_zero (s : ℝ) : (s • unitX : RealPlane) 0 = s := by
  simp [unitX]
theorem embedPlane_mem_closedForwardTube {y : RealPlane} (hy : 0 ≤ y 0) :
    embedPlane y ∈ closedForwardTube := by
  simp [closedForwardTube, embedPlane, lightConePlus, lightConeMinus, hy]
theorem embedFour_add (y y' : RealPlane) :
    embedFour (y + y') = embedFour y + embedFour y' := by
  funext i
  simp [embedFour, add_mul]
  ring
theorem supp_zero : supp (0 : R4 → ℂ) = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨y, hy, -⟩ := h 1 one_pos
  exact hy rfl
theorem zero_mem_C1c : (0 : R4 → ℂ) ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.zero_mem_C1c <;> assumption
theorem transl_actFree_complexTuple (hR : TupleConcat.TupleFacts) {n : ℕ}
    {hs : Fin n → R4 → ℂ} (hm : ∀ l, hs l ∈ C1c ℂ)
    (hd : Pairwise fun k l => Disjoint (supp (hs k)) (supp (hs l))) (z : R4) :
    (EuclidMotion.transl z).actFree (complexTuple hs) =
      complexTuple fun l => (EuclidMotion.transl z).actFn (hs l) := by
  have hz : ComplexComponents (consEntries (0 : R4 → ℂ) hs) := by
    refine ⟨by omega, fun l => ?_, ?_⟩
    · refine Fin.cases ?_ (fun b => ?_) l
      · simpa [consEntries] using zero_mem_C1c
      · simpa [consEntries] using hm b
    · intro k l hkl
      induction k using Fin.cases with
      | zero =>
        induction l using Fin.cases with
        | zero => exact absurd rfl hkl
        | succ b =>
          simp only [consEntries, Fin.cons_zero, supp_zero]
          exact disjoint_bot_left
      | succ a =>
        induction l using Fin.cases with
        | zero =>
          simp only [consEntries, Fin.cons_zero, supp_zero]
          exact disjoint_bot_right
        | succ b =>
          simp only [consEntries, Fin.cons_succ]
          exact hd fun h => hkl (by rw [h])
  exact (hR.1 n 0 hs z hz).1
theorem transl_actFn_transl_actFn {β : Type*} (z z' : R4) (f : R4 → β) :
    (EuclidMotion.transl z).actFn ((EuclidMotion.transl z').actFn f) =
      (EuclidMotion.transl (z + z')).actFn f := by
  funext x
  simp only [EuclidMotion.actFn_transl]
  congr 1
  abel
theorem planeShift_actFn_planeShift_actFn {β : Type*} (y y' : RealPlane) (f : R4 → β) :
    (planeShift y).actFn ((planeShift y').actFn f) =
      (planeShift (y + y')).actFn f := by
  simp only [planeShift, transl_actFn_transl_actFn, embedFour_add]
theorem tsupport_translateProfile_subset (y : RealPlane) (α : RealPlane → ℂ) :
    tsupport (translateProfile y α) ⊆ {u | u - y ∈ tsupport α} := by
  refine closure_minimal ?_ ((isClosed_tsupport α).preimage (continuous_id.sub continuous_const))
  intro u hu
  exact subset_tsupport α hu
theorem abs_time_sub_lt_of_mem_supp (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts) {α : RealPlane → ℂ}
    {φ : RealPlane → ℝ} (hα : α ∈ complexProfiles) (hφ : φ ∈ realLabels) {ρ : ℝ}
    (hd : tsupport α ⊆ openDiscAt 0 ρ) (y : RealPlane) {x : R4}
    (hx : x ∈ supp ((planeShift y).actFn (productFunction α φ))) : |x 3 - y 0| < ρ := by
  have hm := hM.2.1 α hα φ hφ y 0
  rw [hm.1] at hx
  have h1 := (hR.2.2 _ hm.2.2.2.1 φ hφ).2 x hx
  have h2 := hd (tsupport_translateProfile_subset y α h1)
  have h3 : ‖planeComponent x - y‖ < ρ := by simpa [openDiscAt] using h2
  have h4 := PiLp.norm_apply_le (planeComponent x - y) 0
  have h5 : (planeComponent x - y) 0 = x 3 - y 0 := by simp [planeComponent]
  rw [h5, Real.norm_eq_abs] at h4
  exact lt_of_le_of_lt h4 h3
theorem gap_le_of_successive_gaps {n : ℕ} {η : ℝ} (hη : 0 < η) {x : Fin n → RealPlane}
    (hx : ∀ (i : ℕ) (h : i + 1 < n), η / 2 ≤ x ⟨i + 1, h⟩ 0 - x ⟨i, by omega⟩ 0) :
    ∀ a b : Fin n, a < b → η / 2 ≤ x b 0 - x a 0 := by
  have key : ∀ (k i : ℕ) (h : i + k + 1 < n),
      η / 2 ≤ x ⟨i + k + 1, h⟩ 0 - x ⟨i, by omega⟩ 0 := by
    intro k
    induction k with
    | zero => intro i h; exact hx i h
    | succ k ih =>
      intro i h
      have h1 := ih i (by omega)
      have h2 : η / 2 ≤ x ⟨i + (k + 1) + 1, h⟩ 0 - x ⟨i + k + 1, by omega⟩ 0 := hx (i + k + 1) h
      linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by simp only [Fin.mk_lt_mk] at hab; omega⟩
  exact key k a hb
theorem shiftedProducts_components_of_gaps (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts) {c η : ℝ}
    (hc : c ∈ productBoundFractions) (hη : 0 < η) {n : ℕ} {α : Fin n → RealPlane → ℂ}
    {φ : Fin n → RealPlane → ℝ} (h : LabelsProfilesInDisc c η α φ)
    {x : Fin n → RealPlane} (hx : ∀ a b : Fin n, a < b → η / 2 ≤ x b 0 - x a 0) :
    (∀ a, shiftedProducts x α φ a ∈ C1c ℂ) ∧
      Pairwise fun a b =>
        Disjoint (supp (shiftedProducts x α φ a)) (supp (shiftedProducts x α φ b)) := by
  have hcη : c * η < η / 4 := by nlinarith [hc.2]
  have hlt : ∀ a b : Fin n, a < b →
      Disjoint (supp (shiftedProducts x α φ a)) (supp (shiftedProducts x α φ b)) := by
    intro a b hab
    refine Set.disjoint_left.2 fun p h1 h2 => ?_
    have t1 := abs_lt.1 (abs_time_sub_lt_of_mem_supp hR hM (h a).2.1 (h a).1 (h a).2.2 (x a) h1)
    have t2 := abs_lt.1 (abs_time_sub_lt_of_mem_supp hR hM (h b).2.1 (h b).1 (h b).2.2 (x b) h2)
    have t3 := hx a b hab
    linarith [t1.1, t1.2, t2.1, t2.2]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have hm := hM.2.1 (α a) (h a).2.1 (φ a) (h a).1 (x a) 0
    change (planeShift (x a)).actFn (productFunction (α a) (φ a)) ∈ _
    rw [hm.1]
    exact (hR.2.2 _ hm.2.2.2.1 (φ a) (h a).1).1
  · rcases lt_or_gt_of_ne hab with h' | h'
    · exact hlt a b h'
    · exact (hlt b a h').symm
theorem quarter_le_time_of_timesSpaced {n : ℕ} {η : ℝ} (hη : 0 < η) {x : Fin n → RealPlane}
    (hx : TimesSpaced η x) (a : Fin n) : η / 4 ≤ x a 0 := by
  have g := gap_le_of_successive_gaps hη hx.2
  obtain ⟨a, ha⟩ := a
  cases a with
  | zero => exact hx.1 ha
  | succ i =>
    have h1 := hx.1 (by omega : 0 < n)
    have h2 := g ⟨0, by omega⟩ ⟨i + 1, ha⟩ (by simp [Fin.lt_def])
    linarith
theorem supp_shiftedProducts_subset_upperHalf (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts) {c η : ℝ}
    (hc : c ∈ productBoundFractions) (hη : 0 < η) {n : ℕ} {α : Fin n → RealPlane → ℂ}
    {φ : Fin n → RealPlane → ℝ} (h : LabelsProfilesInDisc c η α φ)
    {x : Fin n → RealPlane} (hx : TimesSpaced η x) (a : Fin n) :
    supp (shiftedProducts x α φ a) ⊆ upperHalf := by
  intro p hp
  have hcη : c * η < η / 4 := by nlinarith [hc.2]
  have t1 := abs_lt.1 (abs_time_sub_lt_of_mem_supp hR hM (h a).2.1 (h a).1 (h a).2.2 (x a) hp)
  have t2 := quarter_le_time_of_timesSpaced hη hx a
  change 0 < p 3
  linarith [t1.1]
theorem planeShift_actFree_shiftedProducts (hR : TupleConcat.TupleFacts)
    {n : ℕ} {α : Fin n → RealPlane → ℂ} {φ : Fin n → RealPlane → ℝ}
    {x y : Fin n → RealPlane} (w : RealPlane) (hxy : ∀ a, w + x a = y a)
    (hm : ∀ a, shiftedProducts x α φ a ∈ C1c ℂ)
    (hd : Pairwise fun a b =>
      Disjoint (supp (shiftedProducts x α φ a)) (supp (shiftedProducts x α φ b))) :
    (planeShift w).actFree (complexTuple (shiftedProducts x α φ)) =
      complexTuple (shiftedProducts y α φ) := by
  have h := transl_actFree_complexTuple hR hm hd (embedFour w)
  refine h.trans ?_
  congr 1
  funext a
  change (planeShift w).actFn ((planeShift (x a)).actFn _) =
    (planeShift (y a)).actFn _
  rw [planeShift_actFn_planeShift_actFn, hxy]
theorem timeTranslate_add (s t : ℝ) : timeTranslate (s + t) = timeTranslate s + timeTranslate t := by
  simp [timeTranslate]
theorem timeTranslate_half (η : ℝ) :
    timeTranslate (η / 2) = timeTranslate (η / 4) + timeTranslate (η / 4) := by
  rw [← timeTranslate_add]
  congr 1
  ring
theorem productVec_eq_reconClass_of_real (σ : EuclidFunctionalWithRecon m S)
    (hE : SmallDiscProduct.Holds)
    (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts)
    {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) {C : (RealPlane → ℝ) → ℝ}
    (hSat : ProductBoundWithExponent σ hp hc)
    (hAll : ∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ))
    (hT : RealPoints σ) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    ∀ (n : ℕ) (α : Fin n → RealPlane → ℂ) (φ : Fin n → RealPlane → ℝ),
      LabelsProfilesInDisc c η α φ → ∀ x : Fin n → RealPlane,
      TimesSpaced η x →
      entryProduct (shiftedProducts x α φ) ∈ finCombIn upperHalf ∧
        σ.productVec η α φ (fun a => embedPlane (x a)) =
          reconClass σ (entryProduct (shiftedProducts x α φ)) := by
  intro n
  induction n with
  | zero =>
    intro α φ _ x _
    have e : entryProduct (shiftedProducts x α φ) = toFree [] := entryProduct_zero _
    rw [e]
    refine ⟨emptyComb.2, ?_⟩
    change σ.recon.vac = readClass _ _
    rw [readClass, dif_pos (show toFree [] ∈ finCombIn upperHalf from emptyComb.2)]
    rfl
  | succ n ih =>
    intro α φ hαφ x hx
    have gx := gap_le_of_successive_gaps h0 hx.2
    have hfirst : η / 4 ≤ x 0 0 := hx.1 (Nat.succ_pos n)
    let x' : Fin n → RealPlane := fun a => x a.succ - x 0 - (η / 4) • unitX
    have hx' : TimesSpaced η x' := by
      constructor
      · intro h
        have h2 := gx 0 (Fin.succ ⟨0, h⟩) (Fin.succ_pos _)
        simp only [x', PiLp.sub_apply, smul_unitX_apply_zero]
        linarith
      · intro i h
        have h2 := hx.2 (i + 1) (by omega)
        simp only [x', Fin.succ_mk, PiLp.sub_apply, smul_unitX_apply_zero]
        linarith
    obtain ⟨hY', hΨ'⟩ := ih (Fin.tail α) (Fin.tail φ) (fun a => hαφ a.succ) x' hx'
    let u : Fin (n + 1) → RealPlane := fun a => x a - x 0 + (η / 4) • unitX
    have hu : TimesSpaced η u := by
      constructor
      · intro _
        change η / 4 ≤ (x 0 - x 0 + (η / 4) • unitX : RealPlane) 0
        rw [sub_self, zero_add, smul_unitX_apply_zero]
      · intro i h
        have h2 := hx.2 i h
        simp only [u, PiLp.add_apply, PiLp.sub_apply]
        linarith
    let w : RealPlane := x 0 - (η / 4) • unitX
    have hw : 0 ≤ w 0 := by
      simp only [w, PiLp.sub_apply, smul_unitX_apply_zero]
      linarith
    have eu := shiftedProducts_components_of_gaps hR hM hc h0 hαφ (gap_le_of_successive_gaps h0 hu.2)
    have ex' := shiftedProducts_components_of_gaps (α := Fin.tail α) (φ := Fin.tail φ) hR hM hc h0
      (fun a => hαφ a.succ) (gap_le_of_successive_gaps h0 hx'.2)
    let hs : Fin n → R4 → ℂ := fun a => shiftedProducts u α φ a.succ
    have e1 : consEntries (liftedProduct η (α 0) (φ 0)) hs = shiftedProducts u α φ := by
      funext a
      induction a using Fin.cases with
      | zero =>
        simp only [consEntries, Fin.cons_zero]
        change (EuclidMotion.transl ((η / 4) • timeVec)).actFn (productFunction (α 0) (φ 0)) =
          (planeShift (u 0)).actFn (productFunction (α 0) (φ 0))
        rw [← (hM.1.2.2.2 (η / 4)).1]
        congr 2
        simp [u]
      | succ b =>
        simp only [consEntries, Fin.cons_succ]
        rfl
    have e2 : liftedElement η (entryProduct (shiftedProducts x' (Fin.tail α) (Fin.tail φ))) =
        complexTuple hs := by
      rw [liftedElement, entryProduct, transl_actFree_complexTuple hR ex'.1 ex'.2]
      congr 1
      funext a
      change (EuclidMotion.transl ((η / 2) • timeVec)).actFn
          ((planeShift (x' a)).actFn (productFunction (α a.succ) (φ a.succ))) =
        (planeShift (u a.succ)).actFn (productFunction (α a.succ) (φ a.succ))
      rw [← (hM.1.2.2.2 (η / 2)).1, planeShift_actFn_planeShift_actFn]
      congr 2
      simp only [x', u]
      module
    have hentries : ComplexComponents (shiftedProducts u α φ) :=
      ⟨by omega, eu.1, eu.2⟩
    have hplus := supp_shiftedProducts_subset_upperHalf hR hM hc h0 hαφ hu
    obtain ⟨-, hlong, hcl⟩ := (hR.1 n (liftedProduct η (α 0) (φ 0)) hs 0
      (by rw [e1]; exact hentries)).2.2.2.2 (by rw [e1]; exact hplus)
    rw [consTuple, e1] at hlong
    have hcl' := hcl m S σ
    rw [consTuple, e1] at hcl'
    have hB := (hE m S σ p c hp hc C hSat hAll η h0 h1 (φ 0) (hαφ 0).1 (α 0) (hαφ 0).2.1
      (hαφ 0).2.2).2.2.1
    have step1 := hB _ hY'
    have e3 : productTimesLifted η (α 0) (φ 0)
        (entryProduct (shiftedProducts x' (Fin.tail α) (Fin.tail φ))) =
        singleMulTuple (liftedProduct η (α 0) (φ 0)) hs := by
      rw [productTimesLifted, e2]
      rfl
    have hTw := (hT w hw).2 ⟨_, hlong⟩
    have eT : (planeShift w).actFree (complexTuple (shiftedProducts u α φ)) =
        entryProduct (shiftedProducts x α φ) :=
      planeShift_actFree_shiftedProducts hR w (fun a => by simp only [w, u]; abel) eu.1 eu.2
    have hv : σ.productVec η α φ (fun a => embedPlane (x a)) =
        σ.wedgeIntegralOp (embedPlane w) (productOperator σ (φ 0) (α 0) η
          (σ.productVec η (Fin.tail α) (Fin.tail φ) fun a => embedPlane (x' a))) := by
      have a0 : productArgs η (fun a => embedPlane (x a)) 0 = embedPlane w := by
        simp [productArgs, w, embedPlane_sub, embedPlane_smul_unitX]
      have at' : Fin.tail (productArgs η fun a => embedPlane (x a)) =
          productArgs η fun a => embedPlane (x' a) := by
        funext a
        obtain ⟨a, ha⟩ := a
        cases a with
        | zero =>
          simp only [Fin.tail, productArgs, x', embedPlane_sub, embedPlane_smul_unitX,
            timeTranslate_half]
          simp
          abel
        | succ i =>
          simp only [Fin.tail, productArgs, x', embedPlane_sub, embedPlane_smul_unitX]
          simp
      change σ.wedgeIntegralOp (productArgs η _ 0) (productOperator σ (φ 0) (α 0) η
          (σ.alternatingVec n (Fin.tail (productArgs η _))
            (Fin.tail (σ.productOps η α φ)))) = _
      rw [a0, at']
      rfl
    refine ⟨?_, ?_⟩
    · rw [← eT]
      exact hTw.1
    · have hclass : reconClass σ (complexTuple (shiftedProducts u α φ)) =
          σ.recon.cls ⟨_, hlong⟩ := by
        rw [reconClass, readClass, dif_pos hlong]
      rw [hv, hΨ', step1, e3, hcl', hclass, hTw.2, eT]
      rfl
theorem nil_mem_sepAll : ([] : FnList) ∈ sepAll := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.nil_mem_sepAll <;> assumption
theorem mirror_freeConj_toFree_nil : timeFlip.actFree (freeConj (toFree [])) = toFree [] := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.flipConj_nil <;> assumption
theorem freeMul_toFree_nil (F : FreeSep) : freeMul (toFree []) F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.freeMul_nil_left <;> assumption
section Items
variable (σ : EuclidFunctionalWithRecon m S)
theorem prod_norm_productOps_le (hE : SmallDiscProduct.Holds)
    {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) {C : (RealPlane → ℝ) → ℝ}
    (hSat : ProductBoundWithExponent σ hp hc)
    (hAll : ∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ))
    {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {n : ℕ} {α : Fin n → RealPlane → ℂ}
    {φ : Fin n → RealPlane → ℝ} (h : LabelsProfilesInDisc c η α φ) :
    ∏ a, ‖σ.productOps η α φ a‖ ≤ plateFactorProduct p η C α φ :=
  Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun a _ =>
    (hE m S σ p c hp hc C hSat hAll η h0 h1 (φ a) (h a).1 (α a) (h a).2.1 (h a).2.2).2.2.2
theorem vectorBounds_of (hE : SmallDiscProduct.Holds)
    (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts)
    (hF : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    (hO : IsOpen forwardTube) (hCv : Convex ℝ forwardTube)
    {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) {C : (RealPlane → ℝ) → ℝ}
    (hSat : ProductBoundWithExponent σ hp hc)
    (hAll : ∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ))
    (hT : RealPoints σ) (hWd : WordBounds σ) (hvac : ‖σ.recon.vac‖ = 1)
    {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {n : ℕ} {α : Fin n → RealPlane → ℂ}
    {φ : Fin n → RealPlane → ℝ} (h : LabelsProfilesInDisc c η α φ) :
    VectorBounds σ p η C α φ := by
  set Ξ : (Fin n → ℂ × ℂ) → σ.space :=
    σ.tubeWord σ.recon.vac n
      (Fin.cons (α := fun _ => σ.space →L[ℂ] σ.space) 1 (σ.productOps η α φ))
    with hΞ
  have hΨ : ∀ x, σ.productVec η α φ x = Ξ (productArgs η x) := fun x =>
    alternatingVec_eq_tubeWord σ n _ _
  obtain ⟨hbound, -, hhol⟩ := hWd n
    (Fin.cons (α := fun _ => σ.space →L[ℂ] σ.space) 1 (σ.productOps η α φ))
    σ.recon.vac
  have hset : shiftedForwardTube n η = productArgs η ⁻¹' (Set.pi univ fun _ => forwardTube) := by
    ext x
    simp only [shiftedForwardTube, mem_shiftedTuples_iff, mem_preimage, Set.mem_pi, mem_univ,
      true_imp_iff]
  have hcont : Continuous (fun x : Fin n → ℂ × ℂ => productArgs η x) := by
    have e : (fun x : Fin n → ℂ × ℂ => productArgs η x) =
        fun x => successiveDifferences n x + argumentOffset n η :=
      funext (productArgs_eq η)
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional _).add continuous_const
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxa := (mem_shiftedTuples_iff _ _ _ _).1 hx
    have h2 := hbound (productArgs η x) (fun a _ => hxa a)
    rw [Fin.prod_univ_succ] at h2
    simp only [Fin.cons_zero, Fin.cons_succ, hvac, mul_one] at h2
    have h3 : ‖(1 : σ.space →L[ℂ] σ.space)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    rw [hΨ]
    calc ‖Ξ (productArgs η x)‖
        ≤ ‖(1 : σ.space →L[ℂ] σ.space)‖ * ∏ i, ‖σ.productOps η α φ i‖ := h2
      _ ≤ ∏ i, ‖σ.productOps η α φ i‖ :=
        mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _) h3
      _ ≤ _ := prod_norm_productOps_le σ hE hp hc hSat hAll h0 h1 h
  · rw [hset]
    exact (isOpen_set_pi finite_univ fun _ _ => hO).preimage hcont
  · intro x hx y hy a b ha hb hab
    have hxa := (mem_shiftedTuples_iff _ _ _ _).1 hx
    have hya := (mem_shiftedTuples_iff _ _ _ _).1 hy
    refine (mem_shiftedTuples_iff _ _ _ _).2 fun i => ?_
    have e : productArgs η (a • x + b • y) i =
        a • productArgs η x i + b • productArgs η y i := by
      obtain rfl : b = 1 - a := by linarith
      by_cases h' : (i : ℕ) = 0
      · simp only [productArgs, h', ↓reduceDIte, Pi.add_apply, Pi.smul_apply]
        module
      · simp only [productArgs, h', ↓reduceDIte, Pi.add_apply, Pi.smul_apply]
        module
    rw [e]
    exact hCv (hxa i) (hya i) ha hb hab
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e1 : shiftedForwardTube 0 η = Set.pi univ fun _ : Fin 0 => forwardTube := by
        rw [hset]
        ext x
        simp
      have e2 : σ.productVec η α φ = Ξ := by
        funext x
        rw [hΨ]
        congr 1
        exact Subsingleton.elim _ _
      rw [e1, e2]
      exact hhol
    · have h2 := holomorphicVectorOnTuples_comp_affine hF hn (successiveDifferences n)
        (successiveDifferences_injective n) (argumentOffset n η) hhol
      have e1 : shiftedForwardTube n η =
          {x | successiveDifferences n x + argumentOffset n η ∈ Set.pi univ fun _ => forwardTube} := by
        rw [hset]
        ext x
        simp only [mem_preimage, mem_ofPred_eq, productArgs_eq]
      have e2 : σ.productVec η α φ = fun x => Ξ (successiveDifferences n x + argumentOffset n η) := by
        funext x
        rw [hΨ, productArgs_eq]
      rw [e1, e2]
      exact h2
  · intro x hx
    have e := shiftedProducts_components_of_gaps hR hM hc h0 h (gap_le_of_successive_gaps h0 hx.2)
    obtain ⟨hmem, hcl⟩ :=
      productVec_eq_reconClass_of_real σ hE hR hM hp hc hSat hAll hT h0 h1 n α φ h x hx
    refine ⟨e.2, supp_shiftedProducts_subset_upperHalf hR hM hc h0 h hx, ?_, hmem, hcl⟩
    refine ⟨fun hn => ?_, fun i hi => ?_⟩
    · change embedPlane (x ⟨0, hn⟩) - timeTranslate (η / 4) ∈ closedForwardTube
      rw [← embedPlane_smul_unitX, ← embedPlane_sub]
      refine embedPlane_mem_closedForwardTube ?_
      have h2 := hx.1 hn
      simp only [PiLp.sub_apply, smul_unitX_apply_zero]
      linarith
    · change embedPlane (x ⟨i + 1, hi⟩) - embedPlane (x ⟨i, by omega⟩) - timeTranslate (η / 2) ∈
        closedForwardTube
      rw [← embedPlane_smul_unitX, ← embedPlane_sub, ← embedPlane_sub]
      refine embedPlane_mem_closedForwardTube ?_
      have h2 := hx.2 i hi
      simp only [PiLp.sub_apply, smul_unitX_apply_zero]
      linarith
theorem kernelFormula_of (hE : SmallDiscProduct.Holds)
    (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts)
    (hF : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    (hS : BanachValued.ScalarAgreement.Agreement)
    (hI : MomentSymmetry.MotionInvariant S)
    {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) {C : (RealPlane → ℝ) → ℝ}
    (hSat : ProductBoundWithExponent σ hp hc)
    (hAll : ∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ))
    (hT : RealPoints σ) (hWd : WordBounds σ) (hvac : ‖σ.recon.vac‖ = 1)
    (hone : σ.wedgeIntegralOp 0 = 1)
    {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {q : ℕ} {α : Fin (q + 1) → RealPlane → ℂ}
    {φ : Fin (q + 1) → RealPlane → ℝ} (h : LabelsProfilesInDisc c η α φ) :
    KernelFormula σ p η C α φ := by
  set B := σ.productOps η α φ with hBdef
  set Ξ : (Fin q → ℂ × ℂ) → σ.space :=
    σ.tubeWord σ.recon.vac q B with hΞ
  obtain ⟨hbound, -, hhol⟩ := hWd q B σ.recon.vac
  have hK : ∀ v, σ.productKernel η α φ v =
      ⟪σ.recon.vac, Ξ fun i => v i - timeTranslate (η / 2)⟫_ℂ := by
    intro v
    rw [hΞ, tubeWord_eq_apply_alternatingVec]
    rfl
  have hpow : ∀ v, v ∈ shiftedForwardTubePow q η ↔ ∀ i, v i - timeTranslate (η / 2) ∈ forwardTube := by
    intro v
    constructor
    · intro hv i
      obtain ⟨u, hu, e⟩ := hv i (mem_univ i)
      rw [← e]
      simpa using hu
    · intro hv i _
      exact ⟨v i - timeTranslate (η / 2), hv i, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · have : IsEmpty (Fin (0 * 2)) := ⟨fun i => i.elim0⟩
      refine ⟨?_, ?_, fun _ _ j => isEmptyElim j⟩
      · rcases (pairTupleEquiv 0 '' shiftedForwardTubePow 0 η).eq_empty_or_nonempty with e | e
        · rw [e]
          exact isOpen_empty
        · rw [Subsingleton.eq_univ_of_nonempty e]
          exact isOpen_univ
      · exact (continuous_of_const fun a b => by rw [Subsingleton.elim a b]).continuousOn
    · set s : Fin q → ℂ × ℂ := fun _ => -timeTranslate (η / 2) with hs
      have h2 := holomorphicVectorOnTuples_comp_affine hF hq LinearMap.id Function.injective_id s hhol
      have h3 := (hF σ.space (q * 2) (by omega) _ _ h2).2.1
        (innerSL ℂ σ.recon.vac)
      have h4 := (hS (q * 2) (by omega) _ h3.1 _).2 h3
      have e1 : shiftedForwardTubePow q η =
          {x | (LinearMap.id : (Fin q → ℂ × ℂ) →ₗ[ℂ] (Fin q → ℂ × ℂ)) x + s ∈
            Set.pi univ fun _ => forwardTube} := by
        ext v
        rw [hpow]
        simp [s, sub_eq_add_neg]
      have e2 : σ.productKernel η α φ = fun v => innerSL ℂ σ.recon.vac
          (Ξ ((LinearMap.id : (Fin q → ℂ × ℂ) →ₗ[ℂ] (Fin q → ℂ × ℂ)) v + s)) := by
        funext v
        rw [hK]
        change ⟪_, Ξ _⟫_ℂ = ⟪_, Ξ _⟫_ℂ
        congr 2
      unfold HolomorphicOnTuples Coordinates.ComplexCoordinates.IsHolomorphicVia
      rw [e1, e2]
      exact h4
  · intro v hv
    have hv' := (hpow v).1 hv
    have h2 := hbound (fun i => v i - timeTranslate (η / 2)) (fun i _ =>
      (⟨(hv' i).1.le, (hv' i).2.le⟩ : v i - timeTranslate (η / 2) ∈ closedForwardTube))
    rw [hvac, mul_one] at h2
    rw [hK]
    calc ‖⟪σ.recon.vac, Ξ fun i => v i - timeTranslate (η / 2)⟫_ℂ‖
        ≤ ‖σ.recon.vac‖ * ‖Ξ fun i => v i - timeTranslate (η / 2)‖ :=
          norm_inner_le_norm _ _
      _ = ‖Ξ fun i => v i - timeTranslate (η / 2)‖ := by rw [hvac, one_mul]
      _ ≤ ∏ i, ‖B i‖ := h2
      _ ≤ _ := prod_norm_productOps_le σ hE hp hc hSat hAll h0 h1 h
  · intro y hy
    have hy' : ∀ (i : ℕ) (hi : i + 1 < q + 1),
        η / 2 ≤ y ⟨i + 1, hi⟩ 0 - y ⟨i, by omega⟩ 0 := by
      intro i hi
      have h2 := hy ⟨i, by omega⟩
      simpa [successiveDiffs] using h2
    have gy := gap_le_of_successive_gaps h0 hy'
    have ey := shiftedProducts_components_of_gaps hR hM hc h0 h gy
    have eqP : productsOfShiftedProfiles y α φ = shiftedProducts y α φ := by
      funext a
      exact (hM.2.1 (α a) (h a).2.1 (φ a) (h a).1 (y a) 0).1.symm
    let x : Fin (q + 1) → RealPlane := fun a => y a - y 0 + (η / 4) • unitX
    have hx : TimesSpaced η x := by
      constructor
      · intro _
        change η / 4 ≤ (y 0 - y 0 + (η / 4) • unitX : RealPlane) 0
        rw [sub_self, zero_add, smul_unitX_apply_zero]
      · intro i hi
        have h2 := hy' i hi
        simp only [x, PiLp.add_apply, PiLp.sub_apply]
        linarith
    have ex := shiftedProducts_components_of_gaps hR hM hc h0 h (gap_le_of_successive_gaps h0 hx.2)
    obtain ⟨hmem, hcl⟩ :=
      productVec_eq_reconClass_of_real σ hE hR hM hp hc hSat hAll hT h0 h1 (q + 1) α φ h x hx
    refine ⟨by rw [eqP]; exact ey.2, ?_⟩
    have hzero : productArgs η (fun a => embedPlane (x a)) 0 = 0 := by
      simp [productArgs, x, embedPlane_smul_unitX]
    have htail : Fin.tail (productArgs η fun a => embedPlane (x a)) =
        fun i => embedPlane (successiveDiffs y i) - timeTranslate (η / 2) := by
      funext a
      simp [Fin.tail, productArgs, x, successiveDiffs, embedPlane_add, embedPlane_sub]
      rfl
    have hv : σ.productVec η α φ (fun a => embedPlane (x a)) =
        B 0 (σ.alternatingVec q
          (fun i => embedPlane (successiveDiffs y i) - timeTranslate (η / 2)) (Fin.tail B)) := by
      change σ.wedgeIntegralOp (productArgs η _ 0)
        (B 0 (σ.alternatingVec q (Fin.tail (productArgs η _)) (Fin.tail B))) = _
      rw [hzero, htail, hone]
      rfl
    have hval : σ.productKernel η α φ (fun i => embedPlane (successiveDiffs y i)) =
        ⟪σ.recon.vac, reconClass σ (entryProduct (shiftedProducts x α φ))⟫_ℂ := by
      rw [← hcl, hv]
      rfl
    have hinner : ⟪σ.recon.vac,
        reconClass σ (entryProduct (shiftedProducts x α φ))⟫_ℂ =
        centeredFnFree S (entryProduct (shiftedProducts x α φ)) := by
      have hcY : reconClass σ (entryProduct (shiftedProducts x α φ)) =
          σ.recon.cls ⟨_, hmem⟩ := by
        rw [reconClass, readClass, dif_pos hmem]
      rw [hcY]
      change ⟪σ.recon.cls emptyComb, σ.recon.cls ⟨_, hmem⟩⟫_ℂ = _
      rw [σ.recon.inner_cls]
      change centeredFnFree S (freeMul (timeFlip.actFree (freeConj (toFree []))) _) = _
      rw [mirror_freeConj_toFree_nil, freeMul_toFree_nil]
    have htrans := (hI (entryProduct (shiftedProducts x α φ))).1
      (embedFour (y 0 - (η / 4) • unitX))
    have hmove := planeShift_actFree_shiftedProducts (x := x) (y := y) hR
      (y 0 - (η / 4) • unitX)
      (fun a => by simp only [x]; abel) ex.1 ex.2
    rw [hval, hinner, eqP, ← hmove]
    exact htrans
end Items
theorem holds_of (hE : SmallDiscProduct.Holds)
    (hW : TubeSemigroup.Holds)
    (hTb : TubeSemigroup.ForwardTubeSemigroupFacts)
    (hL : ReconstructionMeasureOperatorFacts)
    (hR : TupleConcat.TupleFacts)
    (hM : TranslationRules.TranslationAndMotionFacts)
    (hI : MomentSymmetry.ReductionHolds)
    (hF : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    (hS : BanachValued.ScalarAgreement.Agreement) :
    Holds := by
  intro m S σ p c hp hc C hSat hAll hCone η h0 h1
  have hWall := hW m S σ hCone
  have hT := hWall.2.2.2.2.1
  have hWd := hWall.2.2.2.2.2
  have hone := hWall.2.1.1
  have hvac : ‖σ.recon.vac‖ = 1 := (hL m S σ).2.2.2.1.1
  obtain ⟨hO, hCv, -⟩ := hTb.1.2.1
  exact ⟨fun n α φ h => vectorBounds_of σ hE hR hM hF hO hCv hp hc hSat hAll hT hWd hvac
      h0 h1 h,
    fun q α φ h => kernelFormula_of σ hE hR hM hF hS (hI m S σ).2.1 hp hc hSat hAll hT hWd hvac
      hone h0 h1 h⟩
end YangMills.Construction.EuclideanFunctionals.PlateVectorsProduct
