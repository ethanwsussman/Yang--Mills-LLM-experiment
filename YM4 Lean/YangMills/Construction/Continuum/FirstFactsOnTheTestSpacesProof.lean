import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinityProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TestSpaces.Elementary
variable {n : ℕ}
section Derivatives
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
theorem multiDeriv_induction (R : (PointTuple n → F) → (PointTuple n → G) → Prop)
    (step : ∀ i μ h h', R h h' → R (coordDeriv i μ h) (coordDeriv i μ h'))
    (α : MultiIdx4 n) {g : PointTuple n → F} {g' : PointTuple n → G} (hg : R g g') :
    R (multiDeriv α g) (multiDeriv α g') := by
  have iter : ∀ (i : Fin n) (μ : Fin 4) (m : ℕ) (h : PointTuple n → F) (h' : PointTuple n → G),
      R h h' → R ((coordDeriv i μ)^[m] h) ((coordDeriv i μ)^[m] h') := by
    intro i μ m
    induction m with
    | zero => exact fun _ _ r => r
    | succ m ih =>
      intro h h' r
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact step _ _ _ _ (ih h h' r)
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (h : PointTuple n → F) (h' : PointTuple n → G),
      R h h' →
      R (l.foldr (fun μ k => (coordDeriv i μ)^[α i μ] k) h)
        (l.foldr (fun μ k => (coordDeriv i μ)^[α i μ] k) h') := by
    intro i l
    induction l with
    | nil => exact fun _ _ r => r
    | cons μ l ih => exact fun h h' r => iter i μ _ _ _ (ih h h' r)
  have outer : ∀ l : List (Fin n),
      R (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ k => (coordDeriv i μ)^[α i μ] k) h) g)
        (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ k => (coordDeriv i μ)^[α i μ] k) h) g') := by
    intro l
    induction l with
    | nil => exact hg
    | cons i l ih => exact inner i _ _ _ ih
  exact outer _
theorem multiDeriv_zero_idx (g : PointTuple n → F) : multiDeriv (0 : MultiIdx4 n) g = g := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.multiDeriv_zero <;> assumption
theorem coordDeriv_eq_fderiv_apply (i : Fin n) (μ : Fin 4) {g : PointTuple n → F}
    (hg : Differentiable ℝ g) :
    coordDeriv i μ g = fun x => fderiv ℝ g x (Pi.single i (Pi.single μ 1)) :=
  funext fun x => (hg x).lineDeriv_eq_fderiv
theorem differentiable_of_contDiff_top {g : PointTuple n → F} (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ g :=
  hg.differentiable (by simp)
theorem contDiff_coordDeriv (i : Fin n) (μ : Fin 4) {g : PointTuple n → F}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (coordDeriv i μ g) := by
  rw [coordDeriv_eq_fderiv_apply i μ (differentiable_of_contDiff_top hg)]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_multiDeriv (α : MultiIdx4 n) {g : PointTuple n → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (multiDeriv α g) :=
  multiDeriv_induction (G := F) (fun h _ => ContDiff ℝ ∞ h)
    (fun i μ _ _ r => contDiff_coordDeriv i μ r) α (g' := g) hg
theorem multiDeriv_clm_comp (L : F →L[ℝ] G) {g : PointTuple n → F} (hg : ContDiff ℝ ∞ g)
    (α : MultiIdx4 n) :
    multiDeriv α (fun x => L (g x)) = fun x => L (multiDeriv α g x) := by
  have step : ∀ (i : Fin n) (μ : Fin 4) (h : PointTuple n → F) (h' : PointTuple n → G),
      (ContDiff ℝ ∞ h ∧ h' = fun x => L (h x)) →
      (ContDiff ℝ ∞ (coordDeriv i μ h) ∧
        coordDeriv i μ h' = fun x => L (coordDeriv i μ h x)) := by
    rintro i μ h _ ⟨hh, rfl⟩
    refine ⟨contDiff_coordDeriv i μ hh, ?_⟩
    have hd := differentiable_of_contDiff_top hh
    have hd' : Differentiable ℝ fun x => L (h x) := L.differentiable.comp hd
    rw [coordDeriv_eq_fderiv_apply i μ hd', coordDeriv_eq_fderiv_apply i μ hd]
    funext x
    have key : fderiv ℝ (fun x => L (h x)) x = L.comp (fderiv ℝ h x) :=
      (L.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv
    rw [key]
    rfl
  exact (multiDeriv_induction (fun h h' => ContDiff ℝ ∞ h ∧ h' = fun x => L (h x)) step α
    (g := g) (g' := fun x => L (g x)) ⟨hg, rfl⟩).2
theorem multiDeriv_zero_fun (α : MultiIdx4 n) :
    multiDeriv α (fun _ : PointTuple n => (0 : F)) = fun _ => 0 := by
  have h := multiDeriv_clm_comp (0 : F →L[ℝ] F) (g := fun _ : PointTuple n => (0 : F))
    contDiff_const α
  simpa using h
theorem multiDeriv_eq_zero_of_not_mem {g : PointTuple n → F} (hg : ContDiff ℝ ∞ g)
    {T : Set (PointTuple n)} (hT : IsClosed T) (hv : ∀ x, x ∉ T → g x = 0) (α : MultiIdx4 n) :
    ∀ x, x ∉ T → multiDeriv α g x = 0 := by
  have step : ∀ (i : Fin n) (μ : Fin 4) (h _h' : PointTuple n → F),
      (ContDiff ℝ ∞ h ∧ ∀ x, x ∉ T → h x = 0) →
      (ContDiff ℝ ∞ (coordDeriv i μ h) ∧
        ∀ x, x ∉ T → coordDeriv i μ h x = 0) := by
    rintro i μ h _ ⟨hh, hz⟩
    refine ⟨contDiff_coordDeriv i μ hh, fun x hx => ?_⟩
    rw [coordDeriv_eq_fderiv_apply i μ (differentiable_of_contDiff_top hh)]
    have hev : h =ᶠ[nhds x] fun _ => 0 :=
      Filter.eventually_of_mem (hT.isOpen_compl.mem_nhds hx) hz
    simp [hev.fderiv_eq]
  exact (multiDeriv_induction (fun h _ => ContDiff ℝ ∞ h ∧ ∀ x, x ∉ T → h x = 0) step α
    (g := g) (g' := g) ⟨hg, hv⟩).2
end Derivatives
section Operations
theorem multiDeriv_linComb (c c' : ℂ) {φ φ' : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ContDiff ℝ ∞ φ') (α : MultiIdx4 n) :
    multiDeriv α (linComb c φ c' φ') =
      fun x => c * multiDeriv α φ x + c' * multiDeriv α φ' x := by
  have hg : ContDiff ℝ ∞ (fun x => (φ x, φ' x)) := hφ.prodMk hφ'
  have h1 : multiDeriv α φ = fun x => (multiDeriv α (fun x => (φ x, φ' x)) x).1 :=
    multiDeriv_clm_comp (ContinuousLinearMap.fst ℝ ℂ ℂ) hg α
  have h2 : multiDeriv α φ' = fun x => (multiDeriv α (fun x => (φ x, φ' x)) x).2 :=
    multiDeriv_clm_comp (ContinuousLinearMap.snd ℝ ℂ ℂ) hg α
  have h3 := multiDeriv_clm_comp
    (c • ContinuousLinearMap.fst ℝ ℂ ℂ + c' • ContinuousLinearMap.snd ℝ ℂ ℂ) hg α
  have e : linComb c φ c' φ' = fun x => c * φ x + c' * φ' x := rfl
  rw [h1, h2, e]
  simpa using h3
theorem contDiff_linComb (c c' : ℂ) {φ φ' : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ContDiff ℝ ∞ φ') :
    ContDiff ℝ ∞ (linComb c φ c' φ') :=
  (contDiff_const.mul hφ).add (contDiff_const.mul hφ')
def conjCLM : ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ)
def reCLMComplex : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
def imCLMComplex : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
theorem contDiff_conjPointwise {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (conjPointwise φ) := conjCLM.contDiff.comp hφ
theorem contDiff_rePart {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (rePart φ) := reCLMComplex.contDiff.comp hφ
theorem contDiff_imPart {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (imPart φ) := imCLMComplex.contDiff.comp hφ
theorem multiDeriv_conjPointwise {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (α : MultiIdx4 n) :
    multiDeriv α (conjPointwise φ) = conjPointwise (multiDeriv α φ) :=
  multiDeriv_clm_comp conjCLM hφ α
theorem multiDeriv_rePart {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (α : MultiIdx4 n) :
    multiDeriv α (rePart φ) = rePart (multiDeriv α φ) :=
  multiDeriv_clm_comp reCLMComplex hφ α
theorem multiDeriv_imPart {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (α : MultiIdx4 n) :
    multiDeriv α (imPart φ) = imPart (multiDeriv α φ) :=
  multiDeriv_clm_comp imCLMComplex hφ α
theorem weightedTerm_le_seminorm (k : ℕ) (φ : PointTuple n → ℂ) (x : PointTuple n)
    (α : MultiIdx4 n) (hα : idxOrder α ≤ k) :
    ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α φ x‖) ≤
      weightedSeminorm k φ :=
  le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
theorem polyWeight_nonneg (k : ℕ) (x : PointTuple n) :
    0 ≤ (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) :=
  Real.rpow_nonneg (by positivity) _
theorem weightedSeminorm_le_of_pointwise {ψ φ φ' : PointTuple n → ℂ} {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (h : ∀ (α : MultiIdx4 n) (x : PointTuple n), ‖multiDeriv α ψ x‖ ≤
      a * ‖multiDeriv α φ x‖ + b * ‖multiDeriv α φ' x‖) (k : ℕ) :
    weightedSeminorm k ψ ≤
      ENNReal.ofReal a * weightedSeminorm k φ + ENNReal.ofReal b * weightedSeminorm k φ' := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  have hW := polyWeight_nonneg k x
  set W := (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) with hWdef
  have e1 : ENNReal.ofReal (W * ‖multiDeriv α ψ x‖) ≤
      ENNReal.ofReal (a * (W * ‖multiDeriv α φ x‖) +
        b * (W * ‖multiDeriv α φ' x‖)) := by
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left (h α x) hW
    calc W * ‖multiDeriv α ψ x‖ ≤ _ := this
      _ = _ := by ring
  rw [ENNReal.ofReal_add (mul_nonneg ha (mul_nonneg hW (norm_nonneg _)))
    (mul_nonneg hb (mul_nonneg hW (norm_nonneg _))), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hb] at e1
  refine e1.trans (add_le_add ?_ ?_)
  · gcongr
    exact weightedTerm_le_seminorm k φ x α hα
  · gcongr
    exact weightedTerm_le_seminorm k φ' x α hα
theorem weightedSeminorm_mono (φ : PointTuple n → ℂ) {k k' : ℕ} (hk : k ≤ k') :
    weightedSeminorm k φ ≤ weightedSeminorm k' φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (weightedTerm_le_seminorm k' φ x α (hα.trans hk))
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (tupleNorm x)]) ?_
  have : (k : ℝ) ≤ k' := by exact_mod_cast hk
  linarith
theorem weightedSeminorm_linComb_le (c c' : ℂ) {φ φ' : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ContDiff ℝ ∞ φ') (k : ℕ) :
    weightedSeminorm k (linComb c φ c' φ') ≤
      ENNReal.ofReal ‖c‖ * weightedSeminorm k φ + ENNReal.ofReal ‖c'‖ * weightedSeminorm k φ' := by
  refine weightedSeminorm_le_of_pointwise (norm_nonneg _) (norm_nonneg _) (fun α x => ?_) k
  rw [multiDeriv_linComb c c' hφ hφ' α]
  exact (norm_add_le _ _).trans (by simp)
theorem weightedSeminorm_le_of_le {ψ φ : PointTuple n → ℂ}
    (h : ∀ (α : MultiIdx4 n) (x : PointTuple n),
      ‖multiDeriv α ψ x‖ ≤ ‖multiDeriv α φ x‖) (k : ℕ) :
    weightedSeminorm k ψ ≤ weightedSeminorm k φ := by
  have := weightedSeminorm_le_of_pointwise (ψ := ψ) (φ := φ) (φ' := φ) zero_le_one le_rfl
    (fun α x => by simpa using h α x) k
  simpa using this
theorem weightedSeminorm_conjPointwise {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    weightedSeminorm k (conjPointwise φ) = weightedSeminorm k φ := by
  have h : ∀ (α : MultiIdx4 n) (x : PointTuple n),
      ‖multiDeriv α (conjPointwise φ) x‖ = ‖multiDeriv α φ x‖ := by
    intro α x
    rw [multiDeriv_conjPointwise hφ α]
    exact Complex.norm_conj _
  exact le_antisymm (weightedSeminorm_le_of_le (fun α x => (h α x).le) k)
    (weightedSeminorm_le_of_le (fun α x => (h α x).ge) k)
theorem weightedSeminorm_rePart_le {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    weightedSeminorm k (rePart φ) ≤ weightedSeminorm k φ := by
  refine weightedSeminorm_le_of_le (fun α x => ?_) k
  rw [multiDeriv_rePart hφ α]
  simpa [rePart] using Complex.abs_re_le_norm _
theorem weightedSeminorm_imPart_le {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    weightedSeminorm k (imPart φ) ≤ weightedSeminorm k φ := by
  refine weightedSeminorm_le_of_le (fun α x => ?_) k
  rw [multiDeriv_imPart hφ α]
  simpa [imPart] using Complex.abs_im_le_norm _
theorem linComb_mem_schwartzSet (c c' : ℂ) {φ φ' : PointTuple n → ℂ}
    (hφ : φ ∈ schwartzSet n) (hφ' : φ' ∈ schwartzSet n) :
    linComb c φ c' φ' ∈ schwartzSet n := by
  refine ⟨contDiff_linComb c c' hφ.1 hφ'.1, fun k hk => ?_⟩
  refine (weightedSeminorm_linComb_le c c' hφ.1 hφ'.1 k).trans_lt ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφ.2 k hk),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφ'.2 k hk)⟩
theorem vanishesToInfiniteOrderOff_of_multiDeriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ψ : PointTuple n → F} {V : Set (PointTuple n)} (hs : ContDiff ℝ ∞ ψ)
    (hV : IsOpen V) (h : ∀ x ∈ Vᶜ, ∀ α : MultiIdx4 n, multiDeriv α ψ x = 0) :
    VanishesToInfiniteOrderOff ψ V :=
  ⟨hs, hV, fun x hx => ⟨hs, by simpa [multiDeriv_zero_idx] using h x hx 0, h x hx⟩⟩
theorem linComb_vanishesToInfiniteOrderOff (c c' : ℂ) {φ φ' : PointTuple n → ℂ}
    {V : Set (PointTuple n)} (hφ : VanishesToInfiniteOrderOff φ V)
    (hφ' : VanishesToInfiniteOrderOff φ' V) :
    VanishesToInfiniteOrderOff (linComb c φ c' φ') V := by
  refine vanishesToInfiniteOrderOff_of_multiDeriv (contDiff_linComb c c' hφ.1 hφ'.1) hφ.2.1 ?_
  intro x hx α
  rw [multiDeriv_linComb c c' hφ.1 hφ'.1 α]
  simp [(hφ.2.2 x hx).2.2 α, (hφ'.2.2 x hx).2.2 α]
theorem schwartzClosedUnderOps (n : ℕ) : SchwartzClosedUnderOps n := by
  refine ⟨fun φ hφ φ' hφ' c c' => ⟨⟨linComb_mem_schwartzSet c c' hφ hφ', ?_, ?_, ?_⟩, ?_, ?_⟩,
    fun V hV => ?_⟩
  · refine ⟨contDiff_conjPointwise hφ.1, fun k hk => ?_⟩
    rw [weightedSeminorm_conjPointwise hφ.1]
    exact hφ.2 k hk
  · exact ⟨contDiff_rePart hφ.1,
      fun k hk => (weightedSeminorm_rePart_le hφ.1 k).trans_lt (hφ.2 k hk)⟩
  · exact ⟨contDiff_imPart hφ.1,
      fun k hk => (weightedSeminorm_imPart_le hφ.1 k).trans_lt (hφ.2 k hk)⟩
  · intro k k' _ hkk
    exact ⟨weightedSeminorm_mono φ hkk, weightedSeminorm_linComb_le c c' hφ.1 hφ'.1 k,
      weightedSeminorm_conjPointwise hφ.1 k, weightedSeminorm_rePart_le hφ.1 k,
      weightedSeminorm_imPart_le hφ.1 k⟩
  · intro V _ hf hf'
    refine ⟨linComb_vanishesToInfiniteOrderOff c c' hf hf', ?_, ?_, ?_⟩
    · refine vanishesToInfiniteOrderOff_of_multiDeriv (contDiff_conjPointwise hφ.1) hf.2.1
        fun x hx α => ?_
      rw [multiDeriv_conjPointwise hφ.1 α]
      simp [conjPointwise, (hf.2.2 x hx).2.2 α]
    · refine vanishesToInfiniteOrderOff_of_multiDeriv (contDiff_rePart hφ.1) hf.2.1
        fun x hx α => ?_
      rw [multiDeriv_rePart hφ.1 α]
      simp [rePart, (hf.2.2 x hx).2.2 α]
    · refine vanishesToInfiniteOrderOff_of_multiDeriv (contDiff_imPart hφ.1) hf.2.1
        fun x hx α => ?_
      rw [multiDeriv_imPart hφ.1 α]
      simp [imPart, (hf.2.2 x hx).2.2 α]
  · refine ⟨{ carrier := {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ V}
              add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
    · rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
      have e : a + b = linComb 1 a 1 b := by
        funext x
        simp [linComb]
      rw [e]
      exact ⟨linComb_mem_schwartzSet 1 1 ha hb, linComb_vanishesToInfiniteOrderOff 1 1 hfa hfb⟩
    · have hz : ∀ α : MultiIdx4 n, multiDeriv α (0 : PointTuple n → ℂ) = fun _ => 0 :=
        fun α => multiDeriv_zero_fun α
      refine ⟨⟨contDiff_const, fun k _ => ?_⟩, ?_⟩
      · have : weightedSeminorm k (0 : PointTuple n → ℂ) = 0 := by
          simp [weightedSeminorm, hz]
        rw [this]
        exact ENNReal.zero_lt_top
      · exact vanishesToInfiniteOrderOff_of_multiDeriv contDiff_const hV fun x _ α => by rw [hz α]
    · rintro c a ⟨ha, hfa⟩
      have e : c • a = linComb c a 0 a := by
        funext x
        simp [linComb]
      rw [e]
      exact ⟨linComb_mem_schwartzSet c 0 ha ha, linComb_vanishesToInfiniteOrderOff c 0 hfa hfa⟩
end Operations
section OpenSets
theorem isOpen_injectiveTuples (n : ℕ) :
    IsOpen (TestFunctions.injectiveTuples (Fin 4 → ℝ) n) := by apply _root_.YangMills.Construction.ConfigSpace.isOpen_distinctArgs <;> assumption
theorem isOpen_timeCoord_pos (i : Fin n) : IsOpen {x : PointTuple n | timeCoord x i > 0} :=
  isOpen_lt continuous_const ((continuous_apply 3).comp (continuous_apply i))
theorem isOpen_positiveTimeLocus (n : ℕ) : IsOpen (positiveTimeLocus n) := by
  have e : positiveTimeLocus n = TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∩
      ⋂ i : Fin n, {x : PointTuple n | timeCoord x i > 0} := by
    ext x
    simp [positiveTimeLocus]
  rw [e]
  exact (isOpen_injectiveTuples n).inter
    (isOpen_iInter_of_finite fun i => isOpen_timeCoord_pos i)
theorem isOpen_negativeTimeLocus (n : ℕ) : IsOpen (negativeTimeLocus n) := by
  have e : negativeTimeLocus n = TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∩
      ⋂ i : Fin n, {x : PointTuple n | -timeCoord x i > 0} := by
    ext x
    simp [negativeTimeLocus]
  rw [e]
  refine (isOpen_injectiveTuples n).inter (isOpen_iInter_of_finite fun i => ?_)
  have hc : Continuous fun x : PointTuple n => timeCoord x i :=
    (continuous_apply 3).comp (continuous_apply i)
  exact isOpen_lt continuous_const hc.neg
theorem timeReflect_timeReflect (u : Fin 4 → ℝ) : timeReflect (timeReflect u) = u := by apply _root_.YangMills.Construction.Motions.RigidMotion.timeReflect_timeReflect <;> assumption
theorem timeReflect_apply_three (u : Fin 4 → ℝ) : timeReflect u 3 = -u 3 := by
  simp [timeReflect]
theorem timeReflectTuple_timeReflectTuple (x : PointTuple n) :
    timeReflectTuple (timeReflectTuple x) = x :=
  funext fun i => timeReflect_timeReflect (x i)
theorem timeReflect_injective : Function.Injective timeReflect :=
  Function.LeftInverse.injective timeReflect_timeReflect
theorem timeReflectTuple_mem_positiveTimeLocus {x : PointTuple n} (hx : x ∈ negativeTimeLocus n) :
    timeReflectTuple x ∈ positiveTimeLocus n :=
  ⟨timeReflect_injective.comp hx.1, fun i => by
    have := hx.2 i
    simpa [timeCoord, timeReflectTuple, timeReflect_apply_three] using this⟩
theorem timeReflectTuple_mem_negativeTimeLocus {x : PointTuple n} (hx : x ∈ positiveTimeLocus n) :
    timeReflectTuple x ∈ negativeTimeLocus n :=
  ⟨timeReflect_injective.comp hx.1, fun i => by
    have := hx.2 i
    simpa [timeCoord, timeReflectTuple, timeReflect_apply_three] using this⟩
theorem negativeTimeLocus_eq_timeReflectSet (n : ℕ) :
    negativeTimeLocus n = timeReflectSet (positiveTimeLocus n) := by
  ext x
  constructor
  · exact fun hx =>
      ⟨timeReflectTuple x, timeReflectTuple_mem_positiveTimeLocus hx,
        timeReflectTuple_timeReflectTuple x⟩
  · rintro ⟨y, hy, rfl⟩
    exact timeReflectTuple_mem_negativeTimeLocus hy
theorem mem_flatSchwartzSet_of_subset {φ : PointTuple n → ℂ} {V : Set (PointTuple n)}
    (hV : V ⊆ distinctLocus n) (hφ : φ ∈ schwartzSet n) (hf : VanishesToInfiniteOrderOff φ V) :
    φ ∈ flatSchwartzSet n :=
  ⟨hφ, fun α x hx => (hf.2.2 x fun hxV => hx (hV hxV)).2.2 α⟩
theorem openLociFacts (n : ℕ) : OpenLociFacts n := by
  refine ⟨isOpen_injectiveTuples n, isOpen_positiveTimeLocus n, isOpen_negativeTimeLocus n,
    negativeTimeLocus_eq_timeReflectSet n, ?_, ?_, ?_, ?_⟩
  · simp [distinctLocus, setPower]
  · ext x
    simp only [positiveTimeLocus, setPower, upperHalfSpace, timeCoord, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies]
    exact and_comm
  · ext φ
    constructor
    · rintro ⟨hφ, hz⟩
      exact ⟨hφ, vanishesToInfiniteOrderOff_of_multiDeriv hφ.1 (isOpen_injectiveTuples n)
        fun x hx α => hz α x hx⟩
    · rintro ⟨hφ, hf⟩
      exact mem_flatSchwartzSet_of_subset subset_rfl hφ hf
  · rintro φ hφ (hf | hf)
    · exact mem_flatSchwartzSet_of_subset (fun x hx => hx.1) hφ hf
    · exact mem_flatSchwartzSet_of_subset (fun x hx => hx.1) hφ hf
end OpenSets
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem continuous_tupleNorm : Continuous (tupleNorm : PointTuple n → ℝ) := by apply _root_.YangMills.Construction.TestSpaces.SchwartzTruncation.continuous_tupleNorm <;> assumption
theorem finite_setOf_idxOrder_le (n p : ℕ) : {α : MultiIdx4 n | idxOrder α ≤ p}.Finite := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.finite_setOf_order_le <;> assumption
theorem derivSupNorm_lt_top {φ : PointTuple n → F} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (p : ℕ) : derivSupNorm p φ < ⊤ := by
  have hb : ∀ α : MultiIdx4 n, ∃ C : ℝ, ∀ x, ‖multiDeriv α φ x‖ ≤ C := by
    intro α
    have hcs : HasCompactSupport (multiDeriv α φ) :=
      HasCompactSupport.intro hc.isCompact
        (multiDeriv_eq_zero_of_not_mem hs (isClosed_tsupport φ)
          (fun x hx => image_eq_zero_of_notMem_tsupport hx) α)
    exact (contDiff_multiDeriv α hs).continuous.bounded_above_of_compact_support hcs
  choose C hC using hb
  set S := (finite_setOf_idxOrder_le n p).toFinset
  have hle : derivSupNorm p φ ≤ ENNReal.ofReal (∑ α ∈ S, |C α|) := by
    refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
    have hmem : α ∈ S := (Set.Finite.mem_toFinset _).2 hα
    exact (hC α x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun α => |C α|) (fun _ _ => abs_nonneg _) hmem))
  exact hle.trans_lt ENNReal.ofReal_lt_top
theorem weightedSeminorm_le_of_closedBall {φ : PointTuple n → F} (hs : ContDiff ℝ ∞ φ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hv : ∀ x, x ∉ {x : PointTuple n | tupleNorm x ≤ ρ} → φ x = 0) (k : ℕ) :
    weightedSeminorm k φ ≤ ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2)) * derivSupNorm k φ := by
  have hT : IsClosed {x : PointTuple n | tupleNorm x ≤ ρ} :=
    isClosed_le continuous_tupleNorm continuous_const
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  by_cases hx : x ∈ {x : PointTuple n | tupleNorm x ≤ ρ}
  · have hx' : tupleNorm x ≤ ρ := hx
    have hnn : 0 ≤ tupleNorm x := Real.sqrt_nonneg _
    have hW : (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ρ ^ 2) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
    have hWρ : 0 ≤ (1 + ρ ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    calc ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α φ x‖)
        ≤ ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α φ x‖) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
      _ = ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2)) *
            ENNReal.ofReal ‖multiDeriv α φ x‖ := ENNReal.ofReal_mul hWρ
      _ ≤ _ := by
          gcongr
          exact le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
  · rw [multiDeriv_eq_zero_of_not_mem hs hT hv α x hx]
    simp
end CompactSupport
theorem smoothCompactSupp_facts {V : Set (PointTuple n)} (hV : IsOpen V) {φ : PointTuple n → ℂ}
    (hφ : φ ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ))) :
    φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ V ∧ (∀ p : ℕ, derivSupNorm p φ < ⊤) := by
  obtain ⟨hs, hc, hsub⟩ := hφ
  have hfin := derivSupNorm_lt_top hs hc
  refine ⟨⟨hs, fun k _ => ?_⟩, ?_, hfin⟩
  · obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn
      continuous_tupleNorm.continuousOn
    have hv : ∀ x, x ∉ {x : PointTuple n | tupleNorm x ≤ max C 0} → φ x = 0 := by
      intro x hx
      refine image_eq_zero_of_notMem_tsupport fun hxt => hx ?_
      have h1 := hC x hxt
      exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
    exact (weightedSeminorm_le_of_closedBall hs (le_max_right _ _) hv k).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin k))
  · exact vanishesToInfiniteOrderOff_of_multiDeriv hs hV fun x hx α =>
      multiDeriv_eq_zero_of_not_mem hs (isClosed_tsupport φ)
        (fun y hy => image_eq_zero_of_notMem_tsupport hy) α x fun hxt => hx (hsub hxt)
theorem compactSupportFacts (n : ℕ) : CompactSupportFacts n := by
  intro V hV φ hφ
  obtain ⟨h1, h2, h3⟩ := smoothCompactSupp_facts hV hφ
  exact ⟨h1, h2, h3, fun ρ hρ hv k _ => weightedSeminorm_le_of_closedBall hφ.1 hρ hv k⟩
section Tuples
theorem subtuple_mem_disjointSupportTuples {O : Set (Fin 4 → ℝ)} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ disjointSupportTuples O n) (J : Finset (Fin n)) :
    subtuple J f ∈ disjointSupportTuples O J.card :=
  ⟨fun _ => hf.1 _, fun _ _ hst => hf.2 fun h => hst ((J.orderEmbOfFin rfl).injective h)⟩
theorem isOpen_setPower {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) :
    IsOpen (setPower O : Set (PointTuple n)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => hO
theorem tensorProd_mem_smoothCompactSupp {O : Set (Fin 4 → ℝ)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples O n)
    (hs : HasSmoothComponents O f) :
    tensorProd f ∈ (smoothCompactSupp
      (setPower O ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) n) : Set (PointTuple n → ℝ)) := by
  set C : Set (PointTuple n) := Set.pi Set.univ fun i => tsupport (f i) with hCdef
  have hC : IsCompact C := isCompact_univ_pi fun i => (hs i).2.1
  have hvan : ∀ x, x ∉ C → tensorProd f x = 0 := by
    intro x hx
    simp only [hCdef, Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have hsub : tsupport (tensorProd f) ⊆ C :=
    closure_minimal (fun x hx => by_contra fun hxC => hx (hvan x hxC)) hC.isClosed
  refine ⟨?_, HasCompactSupport.intro hC hvan, hsub.trans ?_⟩
  · refine contDiff_prod fun i _ => ?_
    exact (hs i).1.comp (contDiff_apply ℝ (Fin 4 → ℝ) i)
  · intro x hx
    refine ⟨fun i _ => (hs i).2.2 (hx i (Set.mem_univ i)), ?_⟩
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.1 (hf.2 hne) (hx i (Set.mem_univ i))
      (hij ▸ hx j (Set.mem_univ j))
theorem tensorProdComplex_mem_smoothCompactSupp {U : Set (PointTuple n)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (h : tensorProd f ∈ (smoothCompactSupp U : Set (PointTuple n → ℝ))) :
    tensorProdComplex f ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp h.1, h.2.1.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero,
    (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero (tensorProd f)).trans h.2.2⟩
theorem subtupleTensorFacts (n : ℕ) : SubtupleTensorFacts n := by
  intro O hO f hf
  refine ⟨fun J => ⟨subtuple_mem_disjointSupportTuples hf J, fun hs _ => hs _⟩, fun hs => ?_⟩
  have hU : IsOpen (setPower O ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) n :
      Set (PointTuple n)) :=
    (isOpen_setPower hO).inter (isOpen_injectiveTuples n)
  have hT := tensorProd_mem_smoothCompactSupp hf hs
  obtain ⟨h1, h2, -⟩ :=
    smoothCompactSupp_facts hU (tensorProdComplex_mem_smoothCompactSupp hT)
  refine ⟨hT, mem_flatSchwartzSet_of_subset (fun x hx => hx.2) h1 h2, ?_⟩
  intro hOp
  subst hOp
  have e := (openLociFacts n).2.2.2.2.2.1
  rw [e]
  exact h2
end Tuples
section Constant
def weightIntegrand (k : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  (1 + TorusMetric.euclidNormVec u ^ 2) ^ (-(k : ℝ) / 2)
theorem one_le_one_add_euclidNormVec_sq (u : Fin 4 → ℝ) :
    1 ≤ 1 + TorusMetric.euclidNormVec u ^ 2 := by
  nlinarith [sq_nonneg (TorusMetric.euclidNormVec u)]
theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem continuous_weightIntegrand (k : ℕ) : Continuous (weightIntegrand k) := by
  refine Continuous.rpow_const (by have := continuous_euclidNormVec; fun_prop) fun u => Or.inl ?_
  exact (lt_of_lt_of_le one_pos (one_le_one_add_euclidNormVec_sq u)).ne'
theorem weightIntegrand_pos (k : ℕ) (u : Fin 4 → ℝ) : 0 < weightIntegrand k u :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_one_add_euclidNormVec_sq u)) _
theorem weightIntegral_pos (k : ℕ) : 0 < weightIntegral k := by
  have hm : Measurable fun u => ENNReal.ofReal (weightIntegrand k u) :=
    ENNReal.measurable_ofReal.comp (continuous_weightIntegrand k).measurable
  refine (lintegral_pos_iff_support hm).2 ?_
  have hsup : Function.support (fun u => ENNReal.ofReal (weightIntegrand k u)) = Set.univ :=
    Set.eq_univ_of_forall fun u => (ENNReal.ofReal_pos.2 (weightIntegrand_pos k u)).ne'
  rw [hsup]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty
theorem weightIntegral_le_weightIntegral_five {k : ℕ} (hk : 4 < k) :
    weightIntegral k ≤ weightIntegral 5 := by
  refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
  refine Real.rpow_le_rpow_of_exponent_le (one_le_one_add_euclidNormVec_sq u) ?_
  have : (5 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  linarith
theorem norm_le_euclidNormVec (u : Fin 4 → ℝ) : ‖u‖ ≤ TorusMetric.euclidNormVec u := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem weightIntegrand_five_le (u : Fin 4 → ℝ) :
    weightIntegrand 5 u ≤ ((1 / 2 : ℝ) ^ (-(5 : ℝ) / 2)) * (1 + ‖u‖) ^ (-(5 : ℝ)) := by
  have ha : 0 < 1 + ‖u‖ := by positivity
  have hn := norm_le_euclidNormVec u
  have hnn := norm_nonneg u
  have hlow : (1 / 2 : ℝ) * (1 + ‖u‖) ^ 2 ≤ 1 + TorusMetric.euclidNormVec u ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖u‖)]
  have hpos : 0 < (1 / 2 : ℝ) * (1 + ‖u‖) ^ 2 := by positivity
  have h1 : weightIntegrand 5 u ≤ ((1 / 2 : ℝ) * (1 + ‖u‖) ^ 2) ^ (-(5 : ℝ) / 2) := by
    have := Real.rpow_le_rpow_of_nonpos hpos hlow (z := -(5 : ℝ) / 2) (by norm_num)
    simpa [weightIntegrand] using this
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (1 + ‖u‖) 2, ← Real.rpow_mul ha.le]
  norm_num
theorem weightIntegral_five_lt_top : weightIntegral 5 < ⊤ := by
  have hint : Integrable (fun u : Fin 4 → ℝ =>
      ((1 / 2 : ℝ) ^ (-(5 : ℝ) / 2)) * (1 + ‖u‖) ^ (-(5 : ℝ))) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul _
  refine lt_of_le_of_lt
    (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (weightIntegrand_five_le u))
    hint.lintegral_lt_top
theorem weightIntegralBounds : WeightIntegralBounds := fun _ hk =>
  ⟨weightIntegral_pos _, (weightIntegral_le_weightIntegral_five hk).trans_lt
    weightIntegral_five_lt_top, weightIntegral_le_weightIntegral_five hk⟩
end Constant
theorem basicProperties : BasicProperties := fun n _ =>
  ⟨schwartzClosedUnderOps n, openLociFacts n, compactSupportFacts n, subtupleTensorFacts n,
    weightIntegralBounds⟩
end YangMills.Construction.TestSpaces.Elementary
end
