import YangMills.Construction.Continuum.ConsistencyOfTheLocalFunctionalsProof
import YangMills.Construction.Continuum.ExtensionOfAFormToTheFlatFunctionsProof
import YangMills.Construction.Continuum.PiecesOfATensorHeldByOneSystem
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.PieceTensorSum
open Bumps ConfigSpace PieceProducts ShellPieces SmoothMaps TestFunctions TorusMetric
variable {n : ℕ}
theorem euclidNormVec_add_le (u w : Fin 4 → ℝ) :
    euclidNormVec (u + w) ≤ euclidNormVec u + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_le_two_mul_of_abs_le (u : Fin 4 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ c, |u c| ≤ M) : euclidNormVec u ≤ 2 * M := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
theorem mem_closedBox_iff (b y : Fin 4 → ℝ) (s : ℝ) :
    y ∈ closedBox b s ↔ ∀ c, |y c - b c| ≤ s / 2 := by apply _root_.YangMills.SharedProofs.p5872 <;> assumption
def gridBump (v : ℝ) (w : Fin 4 → ℤ) (y : Fin 4 → ℝ) : ℝ :=
  ∏ c, mollifiedIndicator (y c / v - w c)
def gridBumpMul (v : ℝ) (w : Fin 4 → ℤ) (f : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  fun y => (gridBump v w y : ℂ) * f y
theorem tsupport_gridBumpMul_subset (v : ℝ) (w : Fin 4 → ℤ) (f : (Fin 4 → ℝ) → ℂ) :
    tsupport (gridBumpMul v w f) ⊆ tsupport f := by
  refine closure_mono fun y hy => ?_
  simp only [Function.mem_support, gridBumpMul] at hy ⊢
  exact right_ne_zero_of_mul hy
theorem abs_le_of_mollifiedIndicator_ne_zero (hB : GevreyBumpBounds) (t : ℝ)
    (h : mollifiedIndicator t ≠ 0) : |t| ≤ 3 / 4 := by
  have hsub := hB.2.2.2.1.2.2.1
  have ht : t ∈ Set.Icc (-(3 / 4) : ℝ) (3 / 4) := hsub (subset_tsupport _ h)
  exact abs_le.mpr ht
theorem abs_sub_le_of_gridBump_ne_zero (hB : GevreyBumpBounds) {v : ℝ} (hv : 0 < v)
    (w : Fin 4 → ℤ) (y : Fin 4 → ℝ) (h : gridBump v w y ≠ 0) (c : Fin 4) :
    |y c - v * w c| ≤ 3 / 4 * v := by
  have hc : mollifiedIndicator (y c / v - w c) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) c (Finset.mem_univ c)
  have h₁ := abs_le_of_mollifiedIndicator_ne_zero hB _ hc
  have h₂ : y c - v * w c = v * (y c / v - w c) := by
    field_simp
  rw [h₂, abs_mul, abs_of_pos hv]
  nlinarith
theorem tsupport_gridBumpMul_subset_near (hB : GevreyBumpBounds) {v : ℝ} (hv : 0 < v)
    (w : Fin 4 → ℤ) (f : (Fin 4 → ℝ) → ℂ) :
    tsupport (gridBumpMul v w f) ⊆ {y | ∀ c, |y c - v * w c| ≤ 3 / 4 * v} := by
  refine closure_minimal (fun y hy => ?_) ?_
  · simp only [Function.mem_support, gridBumpMul] at hy
    have h₁ : (gridBump v w y : ℂ) ≠ 0 := left_ne_zero_of_mul hy
    exact abs_sub_le_of_gridBump_ne_zero hB hv w y (by exact_mod_cast h₁)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_le (by fun_prop) (by fun_prop)
theorem contDiff_gridBump (hB : GevreyBumpBounds) (v : ℝ) (w : Fin 4 → ℤ) :
    ContDiff ℝ ∞ (gridBump v w) := by
  have hb : ContDiff ℝ ∞ mollifiedIndicator := hB.2.2.2.1.1
  refine contDiff_prod fun c _ => hb.comp ?_
  exact ((contDiff_apply ℝ ℝ c).div_const v).sub contDiff_const
theorem exists_finset_sum_gridBump_eq_one (hB : GevreyBumpBounds) {v : ℝ} (hv : 0 < v) (R : ℝ) :
    ∃ Z : Finset (Fin 4 → ℤ), ∀ y : Fin 4 → ℝ, (∀ c, |y c| ≤ R) →
      ∑ w ∈ Z, gridBump v w y = 1 := by
  set L : ℕ := ⌈R / v⌉₊ + 1
  have hL : R / v + 3 / 4 ≤ L := by
    have := Nat.le_ceil (R / v)
    simp only [L]
    push_cast
    linarith
  set F : Finset ℤ := Finset.Icc (-(L : ℤ)) L
  refine ⟨Fintype.piFinset fun _ => F, fun y hy => ?_⟩
  have hone : ∀ c, ∑ l ∈ F, mollifiedIndicator (y c / v - l) = 1 := by
    intro c
    refine (hasSum_sum_of_ne_finset_zero fun l hl => ?_).unique (hB.2.2.2.1.2.2.2 _).1
    by_contra hne
    have h₁ := abs_le.mp (abs_le_of_mollifiedIndicator_ne_zero hB _ hne)
    have h₂ : |y c / v| ≤ R / v := by
      rw [abs_div, abs_of_pos hv]
      exact div_le_div_of_nonneg_right (hy c) hv.le
    have h₃ := abs_le.mp h₂
    apply hl
    rw [Finset.mem_Icc]
    constructor
    · have : (-(L : ℝ)) ≤ l := by linarith [h₁.1, h₁.2, h₃.1, h₃.2]
      exact_mod_cast this
    · have : (l : ℝ) ≤ L := by linarith [h₁.1, h₁.2, h₃.1, h₃.2]
      exact_mod_cast this
  have hp := Finset.prod_univ_sum (fun _ : Fin 4 => F)
    (fun c (l : ℤ) => mollifiedIndicator (y c / v - l))
  simp only [gridBump]
  rw [← hp]
  simp [hone]
def gridSystem {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 12) (r : Fin n → Fin 4 → ℤ) :
    PointSystem n where
  base := fun i c => v * r i c
  scale := 2 * v
  scale_pos := by positivity
  scale_le_half := by linarith
theorem gridSystem_isSeparated {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 12) (r : Fin n → Fin 4 → ℤ)
    (y₀ : Fin n → Fin 4 → ℝ) (h₀ : ∀ i c, |y₀ i c - v * r i c| ≤ 3 / 4 * v)
    (hd : ∀ i i', i ≠ i' → 12 * v ≤ euclidNormVec (y₀ i - y₀ i')) :
    (gridSystem hv hv' r).IsSeparated := by
  have hnear : ∀ i, ∀ b ∈ (gridSystem hv hv' r).outerBox i,
      euclidNormVec (y₀ i - b) ≤ 11 / 2 * v := by
    intro i b hb
    have hb' := (mem_closedBox_iff _ _ _).mp hb
    have := euclidNormVec_le_two_mul_of_abs_le (y₀ i - b) (11 / 4 * v) (by positivity) fun c => by
      have h₁ := abs_le.mp (h₀ i c)
      have h₂ := abs_le.mp (hb' c)
      simp only [gridSystem] at h₂
      simp only [Pi.sub_apply]
      rw [abs_le]
      constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    linarith
  have hlow : ENNReal.ofReal v ≤ (gridSystem hv hv' r).boxGap := by
    refine le_iInf fun i => le_iInf fun i' => le_iInf fun hne => ?_
    refine le_iInf₂ fun b hb => le_iInf₂ fun b' hb' => ENNReal.ofReal_le_ofReal ?_
    have h₁ := hd i i' hne
    have h₂ : y₀ i - y₀ i' = ((b - b') + (y₀ i - b)) + -(y₀ i' - b') := by abel
    have h₃ := euclidNormVec_add_le ((b - b') + (y₀ i - b)) (-(y₀ i' - b'))
    have h₄ := euclidNormVec_add_le (b - b') (y₀ i - b)
    have h₅ : euclidNormVec (-(y₀ i' - b')) = euclidNormVec (y₀ i' - b') := by
      simp only [euclidNormVec, Pi.neg_apply, neg_sq]
    rw [← h₂, h₅] at h₃
    linarith [hnear i b hb, hnear i' b' hb']
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hv) hlow
def supportedReal (S : Set (Fin 4 → ℝ)) : Submodule ℝ ((Fin 4 → ℝ) → ℂ) where
  carrier := {f | IsRealValued f ∧ ContDiff ℝ ∞ f ∧ tsupport f ⊆ S}
  add_mem' := by
    rintro f g ⟨hf, hf', hf''⟩ ⟨hg, hg', hg''⟩
    refine ⟨fun y => ?_, hf'.add hg', ?_⟩
    · simp [hf y, hg y]
    · have : tsupport (f + g) ⊆ tsupport f ∪ tsupport g :=
        closure_minimal ((Function.support_add f g).trans
          (union_subset_union (subset_tsupport _) (subset_tsupport _)))
          ((isClosed_tsupport f).union (isClosed_tsupport g))
      exact this.trans (union_subset hf'' hg'')
  zero_mem' := by
    refine ⟨fun y => by simp, contDiff_const, ?_⟩
    simp [tsupport]
  smul_mem' := by
    rintro t f ⟨hf, hf', hf''⟩
    refine ⟨fun y => ?_, hf'.const_smul t, ?_⟩
    · simp [hf y]
    · exact (closure_mono (Function.support_const_smul_subset t f)).trans hf''
theorem supportedTuple_mem (φ : smoothRealTupleSet n)
    (f : ∀ i, supportedReal (tsupport (φ.1 i))) :
    (fun i => (f i).1) ∈ smoothRealTupleSet n := by
  obtain ⟨⟨hφ, hdis⟩, -⟩ := φ.2
  refine ⟨⟨fun i => ⟨(f i).2.1, ?_, ?_, subset_univ _⟩, fun i i' h => ?_⟩, fun i => (f i).2.2.1⟩
  · simpa using contDiff_infty.mp (f i).2.2.1 1
  · exact IsCompact.of_isClosed_subset (hφ i).2.2.1 (isClosed_tsupport _) (f i).2.2.2
  · exact (hdis i i' h).mono (f i).2.2.2 (f i').2.2.2
def supportedTuple (φ : smoothRealTupleSet n) (f : ∀ i, supportedReal (tsupport (φ.1 i))) :
    smoothRealTupleSet n :=
  ⟨fun i => (f i).1, supportedTuple_mem φ f⟩
theorem supportedTuple_update [DecidableEq (Fin n)] (φ : smoothRealTupleSet n)
    (m : ∀ i, supportedReal (tsupport (φ.1 i))) (i : Fin n)
    (e : supportedReal (tsupport (φ.1 i))) :
    (supportedTuple φ (Function.update m i e)).1 =
      Function.update (supportedTuple φ m).1 i e.1 := by
  funext k
  by_cases h : k = i
  · subst h
    simp [supportedTuple]
  · simp [supportedTuple, Function.update_of_ne h]
theorem prod_update_apply [DecidableEq (Fin n)] (M : FnTuple n) (i : Fin n)
    (e : (Fin 4 → ℝ) → ℂ) (x : Config n) :
    ∏ k, (Function.update M i e k) (x k) = e (x i) * ∏ k ∈ Finset.univ.erase i, M k (x k) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
theorem tensorProd_update_add [DecidableEq (Fin n)] (M : FnTuple n) (i : Fin n)
    (e e' : (Fin 4 → ℝ) → ℂ) :
    tensorProd (Function.update M i (e + e')) =
      tensorProd (Function.update M i e) + tensorProd (Function.update M i e') := by
  funext x
  simp only [tensorProd, Pi.add_apply, prod_update_apply, add_mul]
theorem tensorProd_update_smul [DecidableEq (Fin n)] (M : FnTuple n) (i : Fin n) (t : ℝ)
    (e : (Fin 4 → ℝ) → ℂ) :
    tensorProd (Function.update M i (t • e)) = (t : ℂ) • tensorProd (Function.update M i e) := by
  funext x
  simp only [tensorProd, Pi.smul_apply, prod_update_apply, smul_eq_mul, Complex.real_smul,
    mul_assoc]
def multilinearOfForm (T : smoothRealTupleSet n → ℝ) (hT : IsRealMultilinearSmooth T)
    (φ : smoothRealTupleSet n) :
    MultilinearMap ℝ (fun i => supportedReal (tsupport (φ.1 i))) ℂ where
  toFun f := (T (supportedTuple φ f) : ℂ)
  map_update_add' := by
    intro inst m i e e'
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hag : AgreeExcept i (supportedTuple φ (Function.update m i e)).1
        (supportedTuple φ (Function.update m i e')).1 := by
      intro k hk
      rw [supportedTuple_update, supportedTuple_update, Function.update_of_ne hk,
        Function.update_of_ne hk]
    have h := (hT i (supportedTuple φ (Function.update m i e))
      (supportedTuple φ (Function.update m i e')) hag).1
      (supportedTuple φ (Function.update m i (e + e'))) (by
        rw [supportedTuple_update, supportedTuple_update, supportedTuple_update]
        simp [Function.update_idem])
    rw [h]
    push_cast
    rfl
  map_update_smul' := by
    intro inst m i t e
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hag : AgreeExcept i (supportedTuple φ (Function.update m i e)).1
        (supportedTuple φ (Function.update m i e)).1 := fun _ _ => rfl
    have h := (hT i (supportedTuple φ (Function.update m i e))
      (supportedTuple φ (Function.update m i e)) hag).2
      t (supportedTuple φ (Function.update m i (t • e))) (by
        rw [supportedTuple_update, supportedTuple_update]
        funext k
        by_cases hk : k = i
        · subst hk
          funext y
          simp
        · rw [Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk])
    rw [h]
    simp
def multilinearOfTensorMap (φ : smoothRealTupleSet n) (L : (Config n → ℂ) → ℂ)
    (hadd : ∀ f g : smoothRealTupleSet n,
      L (tensorProd f.1 + tensorProd g.1) = L (tensorProd f.1) + L (tensorProd g.1))
    (hsmul : ∀ (t : ℝ) (f : smoothRealTupleSet n),
      L ((t : ℂ) • tensorProd f.1) = t * L (tensorProd f.1)) :
    MultilinearMap ℝ (fun i => supportedReal (tsupport (φ.1 i))) ℂ where
  toFun f := L (tensorProd (supportedTuple φ f).1)
  map_update_add' := by
    intro _ m i e e'
    have h := hadd (supportedTuple φ (Function.update m i e))
      (supportedTuple φ (Function.update m i e'))
    rw [supportedTuple_update, supportedTuple_update] at h ⊢
    rw [supportedTuple_update, Submodule.coe_add, tensorProd_update_add]
    exact h
  map_update_smul' := by
    intro _ m i t e
    have h := hsmul t (supportedTuple φ (Function.update m i e))
    rw [supportedTuple_update] at h ⊢
    rw [supportedTuple_update, Submodule.coe_smul, tensorProd_update_smul, h]
    simp
theorem pieceMul_add (j : ℕ) (z : LatticePt n) (Φ Ψ : Config n → ℂ) :
    pieceMul j z (Φ + Ψ) = pieceMul j z Φ + pieceMul j z Ψ := by apply _root_.YangMills.Construction.FlatExtension.pieceMul_add <;> assumption
theorem pieceMul_smul (j : ℕ) (z : LatticePt n) (lam : ℂ) (Φ : Config n → ℂ) :
    pieceMul j z (lam • Φ) = lam • pieceMul j z Φ := by apply _root_.YangMills.Construction.FlatExtension.pieceMul_smul <;> assumption
theorem sumOverPiecesEqForm_holds
    (hHeld : PieceProducts.PieceSumOnSeparatedBoxes)
    (hSum : PieceLocalSum.PieceLocalSumBound)
    (hFacts : TupleFacts.BasicFacts)
    (hNorm : SchwartzSeminormsFinite)
    (hFlat : ProductBounds)
    (hLocal : LocalPairingProps.LocalPairingProperties)
    (hB : GevreyBumpBounds) :
    SumOverPiecesEqForm := by
  intro n c a G T hT φ
  have hn : 2 ≤ n := hT.1
  have hmult : IsRealMultilinearSmooth T := hT.2.2.2.1
  obtain ⟨-, ⟨-, hten, W, hW, hWflat⟩, -, -, -, hdist, -⟩ := hFacts n hn
  have htensor : ∀ f : smoothRealTupleSet n, tensorProd f.1 ∈ flatSchwartzSet n := by
    intro f
    apply hWflat
    rw [hW]
    exact (hten f.1 f.2).1
  have hsys : ∀ p : activeIndices n, (pieceBoxSystem p).IsSeparated ∧
      ∀ Φ ∈ smoothSet (Config n), pieceMul p.1.1 p.1.2 Φ ∈ (pieceBoxSystem p).supportedClass := by
    intro p
    have h := (hFlat n hn p.1.1 p.1.2 p.2).1
    exact ⟨h.1, fun Φ hΦ => (h.2.2.2.2.2 Φ hΦ).2.2⟩
  have hlin : ∀ p : activeIndices n,
      LocalPairingProps.PairingIsComplexLinear T (pieceBoxSystem p) := fun p =>
    (hLocal n c a G T (pieceBoxSystem p) hT (hsys p).1).2.1
  have hsummable : ∀ Φ ∈ flatSchwartzSet n, Summable fun p : activeIndices n =>
      localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 Φ) := by
    intro Φ hΦ
    have hfin : decaySeminorm (4 * n + 2) (10 * n + a - 2) Φ < ⊤ :=
      ((hNorm n (by omega) (4 * n + 2) (10 * n + a - 2) 0).1 Φ hΦ.1).1
    have hne : ∑' p : activeIndices n, ENNReal.ofReal
        ‖localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 Φ)‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
        (hSum n c a G T hT Φ hΦ)
    have h := ENNReal.summable_toReal hne
    have h' : Summable fun p : activeIndices n =>
        ‖localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 Φ)‖ := by
      simpa [ENNReal.toReal_ofReal, norm_nonneg] using h
    exact h'.of_norm
  set L : (Config n → ℂ) → ℂ := fun Φ =>
    ∑' p : activeIndices n, localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 Φ) with hL
  have hadd : ∀ f g : smoothRealTupleSet n,
      L (tensorProd f.1 + tensorProd g.1) = L (tensorProd f.1) + L (tensorProd g.1) := by
    intro f g
    have hterm : ∀ p : activeIndices n,
        localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd f.1 + tensorProd g.1)) =
          localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd f.1)) +
            localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd g.1)) := by
      intro p
      rw [pieceMul_add]
      exact (hlin p).1 _ ((hsys p).2 _ (htensor f).1.1) _ ((hsys p).2 _ (htensor g).1.1)
    simp only [hL, hterm]
    exact (hsummable _ (htensor f)).tsum_add (hsummable _ (htensor g))
  have hsmul : ∀ (t : ℝ) (f : smoothRealTupleSet n),
      L ((t : ℂ) • tensorProd f.1) = t * L (tensorProd f.1) := by
    intro t f
    have hterm : ∀ p : activeIndices n,
        localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 ((t : ℂ) • tensorProd f.1)) =
          t * localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd f.1)) := by
      intro p
      rw [pieceMul_smul]
      exact (hlin p).2 _ _ ((hsys p).2 _ (htensor f).1.1)
    simp only [hL, hterm]
    exact tsum_mul_left
  obtain ⟨⟨hφ, hdis⟩, hsm⟩ := φ.2
  have hcomplex : φ.1 ∈ smoothComplexTupleSet n :=
    ⟨fun i => ⟨hsm i, (hφ i).2.2.1⟩, hdis⟩
  obtain ⟨r₀, hr₀, hr₀L⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (hdist φ.1 hcomplex).1
  have hr₀' : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
  set v : ℝ := min (r₀ : ℝ) 1 / 12 with hvdef
  have hv : 0 < v := by
    have : 0 < min (r₀ : ℝ) 1 := lt_min hr₀' one_pos
    positivity
  have hv' : v ≤ 1 / 12 := by
    have : min (r₀ : ℝ) 1 ≤ 1 := min_le_right _ _
    simp only [hvdef]
    linarith
  have hfar : ∀ i i', i ≠ i' → ∀ y ∈ tsupport (φ.1 i), ∀ y' ∈ tsupport (φ.1 i'),
      12 * v ≤ euclidNormVec (y - y') := by
    intro i i' hne y hy y' hy'
    have h₁ : TupleFacts.minSupportSep φ.1 ≤
        setDistR4 (tsupport (φ.1 i)) (tsupport (φ.1 i')) :=
      (iInf_le _ i).trans ((iInf_le _ i').trans (iInf_le _ hne))
    have h₂ : setDistR4 (tsupport (φ.1 i)) (tsupport (φ.1 i')) ≤
        ENNReal.ofReal (euclidNormVec (y - y')) :=
      (iInf₂_le y hy).trans (iInf₂_le y' hy')
    have h₃ : ENNReal.ofReal r₀ ≤ ENNReal.ofReal (euclidNormVec (y - y')) := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact hr₀L.le.trans (h₁.trans h₂)
    have h₄ : (r₀ : ℝ) ≤ euclidNormVec (y - y') :=
      (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp h₃
    have h₅ : min (r₀ : ℝ) 1 ≤ r₀ := min_le_left _ _
    simp only [hvdef]
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ i, ∀ y ∈ tsupport (φ.1 i), ∀ c, |y c| ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_iUnion fun i => (hφ i).2.2.1).isBounded.exists_norm_le
    refine ⟨R, fun i y hy c => ?_⟩
    have h := hR y (mem_iUnion.mpr ⟨i, hy⟩)
    have h' := norm_le_pi_norm y c
    rw [Real.norm_eq_abs] at h'
    exact h'.trans h
  obtain ⟨Z, hZ⟩ := exists_finset_sum_gridBump_eq_one hB hv R
  let φW : ∀ i, supportedReal (tsupport (φ.1 i)) := fun i =>
    ⟨φ.1 i, (hφ i).1, hsm i, subset_rfl⟩
  let gW : ∀ i, (Fin 4 → ℤ) → supportedReal (tsupport (φ.1 i)) := fun i w =>
    ⟨gridBumpMul v w (φ.1 i), fun y => by
        simp [gridBumpMul, (hφ i).1 y],
      (Complex.ofRealCLM.contDiff.comp (contDiff_gridBump hB v w)).mul (hsm i),
      tsupport_gridBumpMul_subset v w _⟩
  have hcut : ∀ i, ∑ w ∈ Z, gW i w = φW i := by
    intro i
    apply Subtype.ext
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [gW, φW, gridBumpMul]
    rw [← Finset.sum_mul]
    by_cases hy : φ.1 i y = 0
    · simp [hy]
    · have h₁ : y ∈ tsupport (φ.1 i) := subset_tsupport _ hy
      have h₂ := hZ y (hR i y h₁)
      rw [← Complex.ofReal_sum, h₂]
      simp
  let A := multilinearOfTensorMap φ L hadd hsmul
  let B := multilinearOfForm T hmult φ
  have hchain : ∀ r ∈ Fintype.piFinset fun _ : Fin n => Z,
      A (fun i => gW i (r i)) = B (fun i => gW i (r i)) := by
    intro r _
    by_cases hz : ∃ i, gW i (r i) = 0
    · obtain ⟨i, hi⟩ := hz
      rw [A.map_coord_zero i hi, B.map_coord_zero i hi]
    · push Not at hz
      have hex : ∀ i, ∃ y, gridBumpMul v (r i) (φ.1 i) y ≠ 0 := by
        intro i
        by_contra hne
        push Not at hne
        exact hz i (Subtype.ext (funext hne))
      choose y₀ hy₀ using hex
      have hnear : ∀ i, y₀ i ∈ {y | ∀ c, |y c - v * r i c| ≤ 3 / 4 * v} := fun i =>
        tsupport_gridBumpMul_subset_near hB hv (r i) (φ.1 i) (subset_tsupport _ (hy₀ i))
      have hin : ∀ i, y₀ i ∈ tsupport (φ.1 i) := fun i =>
        tsupport_gridBumpMul_subset v (r i) (φ.1 i) (subset_tsupport _ (hy₀ i))
      have hsep := gridSystem_isSeparated hv hv' r y₀ hnear
        fun i i' hne => hfar i i' hne _ (hin i) _ (hin i')
      refine hHeld n c a G T hT (gridSystem hv hv' r) (supportedTuple φ fun i => gW i (r i)) hsep
        fun i y hy => ?_
      have h₁ := tsupport_gridBumpMul_subset_near hB hv (r i) (φ.1 i) hy
      refine (mem_closedBox_iff _ _ _).mpr fun k => ?_
      have h₂ := abs_le.mp (h₁ k)
      simp only [gridSystem]
      rw [abs_le]
      constructor <;> linarith [h₂.1, h₂.2]
  calc ∑' p : activeIndices n,
        localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd φ.1))
      = A φW := rfl
    _ = A (fun i => ∑ w ∈ Z, gW i w) := by simp only [hcut]
    _ = ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Z), A (fun i => gW i (r i)) :=
        A.map_sum_finset gW (fun _ => Z)
    _ = ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Z), B (fun i => gW i (r i)) :=
        Finset.sum_congr rfl hchain
    _ = B (fun i => ∑ w ∈ Z, gW i w) := (B.map_sum_finset gW (fun _ => Z)).symm
    _ = B φW := by simp only [hcut]
    _ = (T φ : ℂ) := rfl
end YangMills.Construction.PieceTensorSum
