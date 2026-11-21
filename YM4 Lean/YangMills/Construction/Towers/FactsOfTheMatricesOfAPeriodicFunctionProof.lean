import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.TranslationsOnTheIndexSetsOfATower
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunction
import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLattice
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBonds
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnThePlaquettes
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheSites
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.PeriodicMultiplierMatrices
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Quotients (conjKernel)
open YangMills.Construction.Tower.PlaneWaves hiding shiftedFreq
open YangMills.Construction.Tower.PlaneWaveCalculus
section Points
variable {L k : ℕ}
theorem finestMesh_inv (L k : ℕ) : (finestMesh L k)⁻¹ = (L : ℝ) ^ k := by
  simp [finestMesh, meshAt, zpow_neg]
theorem neg_mem_freqBox {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) :
    -m ∈ freqBox L k := by
  rw [mem_freqBox] at hm ⊢
  intro ν
  simpa using hm ν
theorem exists_mem_freqBox_add_smul (hL : Odd L) (m : Fin 4 → ℤ) :
    ∃ m' ∈ freqBox L k, ∃ n : Fin 4 → ℤ, m = m' + ((L ^ k : ℕ) : ℤ) • n := by
  obtain ⟨h, hh⟩ := hL.pow (n := k)
  have hN : ((L ^ k : ℕ) : ℤ) = 2 * (h : ℤ) + 1 := by rw [hh]; push_cast; ring
  have hNpos : (0 : ℤ) < ((L ^ k : ℕ) : ℤ) := by rw [hN]; positivity
  refine ⟨fun μ => (m μ + h) % ((L ^ k : ℕ) : ℤ) - h, ?_, fun μ => (m μ + h) / ((L ^ k : ℕ) : ℤ), ?_⟩
  · rw [mem_freqBox]
    intro ν
    have e0 := Int.emod_nonneg (m ν + h) hNpos.ne'
    have e1 := Int.emod_lt_of_pos (m ν + h) hNpos
    have hr : ((finestMesh L k)⁻¹) = 2 * (h : ℝ) + 1 := by
      rw [finestMesh_inv]
      have : ((L ^ k : ℕ) : ℝ) = 2 * (h : ℝ) + 1 := by rw [hh]; push_cast; ring
      simpa using this
    rw [hr, abs_le]
    have a1 : -(h : ℤ) ≤ (m ν + h) % ((L ^ k : ℕ) : ℤ) - h := by linarith
    have a2 : (m ν + h) % ((L ^ k : ℕ) : ℤ) - h ≤ (h : ℤ) := by linarith
    have b1 : -(h : ℝ) ≤ (((m ν + h) % ((L ^ k : ℕ) : ℤ) - h : ℤ) : ℝ) := by exact_mod_cast a1
    have b2 : (((m ν + h) % ((L ^ k : ℕ) : ℤ) - h : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast a2
    constructor <;> linarith
  · funext μ
    have e := Int.emod_add_mul_ediv (m μ + h) ((L ^ k : ℕ) : ℤ)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
theorem shiftedFreq_mem_openImStrip {υ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip υ)
    (m : Fin 4 → ℤ) : PlaneWaves.shiftedFreq κ m ∈ openImStrip υ := fun μ => by
  have : (PlaneWaves.shiftedFreq κ m μ).im = (κ μ).im := by
    simp [PlaneWaves.shiftedFreq]
  rw [this]
  exact hκ μ
theorem conjVec_mem_openImStrip {υ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip υ) :
    conjVec κ ∈ openImStrip υ := fun μ => by
  simpa [conjVec] using hκ μ
theorem shiftedFreq_add_period (hL : 0 < L) (κ : Fin 4 → ℂ) (m n : Fin 4 → ℤ) :
    PlaneWaves.shiftedFreq κ (m + ((L ^ k : ℕ) : ℤ) • n) =
      periodShift L k (PlaneWaves.shiftedFreq κ m) n := by
  have hs : (meshC L k) = (((L : ℂ) ^ k))⁻¹ := by
    have h := finestMesh_inv L k
    have h' : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by rw [← h, inv_inv]
    simp only [meshC, h']
    push_cast
    rfl
  funext μ
  simp only [periodShift, PlaneWaves.shiftedFreq, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring
theorem shiftedFreq_addTwoPiInt (κ : Fin 4 → ℂ) (e m : Fin 4 → ℤ) :
    PlaneWaves.shiftedFreq (addTwoPiInt κ e) m = PlaneWaves.shiftedFreq κ (m + e) := by
  funext μ
  simp only [PlaneWaves.shiftedFreq, addTwoPiInt, Pi.add_apply]
  push_cast
  ring
theorem shiftedFreq_neg (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    PlaneWaves.shiftedFreq (-κ) (-m) = -PlaneWaves.shiftedFreq κ m := by
  funext μ
  simp only [PlaneWaves.shiftedFreq, Pi.neg_apply]
  push_cast
  ring
theorem neg_conjVec_shiftedFreq (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    -conjVec (PlaneWaves.shiftedFreq κ (-m)) =
      PlaneWaves.shiftedFreq (-conjVec κ) m := by
  funext μ
  simp only [PlaneWaves.shiftedFreq, conjVec, Pi.neg_apply, map_add, map_mul,
    Complex.conj_ofReal, map_intCast, map_ofNat]
  push_cast
  ring
end Points
section Pairings
open Classical
theorem tracelessPairing_smul_left {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (c : ℂ) :
    tracelessPairing (c • X) Y = tracelessPairing X (c • Y) := by
  have h1 : c • X ∈ ComplexMatrix2.traceless := ComplexMatrix2.traceless.smul_mem c hX
  have h2 : c • Y ∈ ComplexMatrix2.traceless := ComplexMatrix2.traceless.smul_mem c hY
  unfold tracelessPairing
  rw [dif_pos ⟨h1, hY⟩, dif_pos ⟨hX, h2⟩]
  simp only [OneLoop.traceForm, Matrix.smul_mul, Matrix.mul_smul]
variable {I : PeriodicData}
theorem wPairing_single [Finite I.UnitQuot] (w : I.UnitQuot → ℝ) (u : I.UnitQuot → ℂ)
    (c : I.UnitQuot) :
    wPairing w u (Pi.single c 1) = (w c : ℂ) * u c := by
  have := Fintype.ofFinite I.UnitQuot
  rw [wPairing, tsum_fintype, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem eq_of_wPairing [Finite I.UnitQuot] {w : I.UnitQuot → ℝ} (hw : ∀ c, w c ≠ 0)
    {u v : I.UnitQuot → ℂ} (h : ∀ g, wPairing w u g = wPairing w v g) : u = v := by
  classical
  funext c
  have e := h (Pi.single c 1)
  rw [wPairing_single, wPairing_single] at e
  exact mul_left_cancel₀ (by exact_mod_cast hw c) e
theorem wPairing_quotHomTranspose [Finite I.UnitQuot] (hw : ∀ c, I.quotWeight 1 c ≠ 0)
    (A : QuotHom I I) (f g : I.UnitQuot → ℂ) :
    wPairing (I.quotWeight 1) (quotHomTranspose A f) g =
      wPairing (I.quotWeight 1) f (A g) := by
  classical
  have := Fintype.ofFinite I.UnitQuot
  have hg : g = ∑ c, g c • (Pi.single c (1 : ℂ) : I.UnitQuot → ℂ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hA : ∀ c', A g c' = ∑ c, linearMapEntry A c' c * g c := by
    intro c'
    conv_lhs => rw [hg]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  rw [quotHomTranspose, linearMapOfEntries_eq_applyKernel]
  simp only [wPairing, tsum_fintype, applyKernel, wTranspose, hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
  have h1 : ((I.quotWeight 1 c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw c
  push_cast
  field_simp
end Pairings
structure CoeffExtraction (L k : ℕ) (I : PeriodicData) (D : Type) [Fintype D]
    (coef : (I.UnitQuot → ℂ) → D → (Fin 4 → ℤ) → ComplexMatrix2) : Prop where
  finite_quot : Finite I.UnitQuot
  weight_ne : ∀ c, I.quotWeight 1 c ≠ 0
  map_add : ∀ l l' d m, coef (l + l') d m = coef l d m + coef l' d m
  map_smul : ∀ (a : ℂ) l d m, coef (a • l) d m = a • coef l d m
  mem : ∀ l d m, coef l d m ∈ ComplexMatrix2.traceless
  separated : ∀ l, (∀ d, ∀ m ∈ freqBox L k, coef l d m = 0) → l = 0
  surj : ∀ Z : D → (Fin 4 → ℤ) → ComplexMatrix2, (∀ d m, Z d m ∈ ComplexMatrix2.traceless) →
    ∃ l, ∀ d, ∀ m ∈ freqBox L k, coef l d m = Z d m
  period : ∀ l d m (n : Fin 4 → ℤ), coef l d (m + ((L ^ k : ℕ) : ℤ) • n) = coef l d m
  phaseMul_eq : ∀ (e : Fin 4 → ℤ) l d m, coef (phaseMul I e l) d m = coef l d (m - e)
  wPairing_eq : ∀ l l', wPairing (I.quotWeight 1) l l' =
    ∑ m ∈ freqBox L k, ∑ d, tracelessPairing (coef l d m) (coef l' d (-m))
  conj_eq : ∀ l d m, coef (fun c => conj (l c)) d m = (coef l d (-m)).conjTranspose
section Abstract
variable {L k : ℕ} {I : PeriodicData} {D : Type} [Fintype D]
  {coef : (I.UnitQuot → ℂ) → D → (Fin 4 → ℤ) → ComplexMatrix2}
def ScalesCoeffs (L k : ℕ) (coef : (I.UnitQuot → ℂ) → D → (Fin 4 → ℤ) → ComplexMatrix2)
    (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ) (A : QuotHom I I) : Prop :=
  ∀ l d, ∀ m ∈ freqBox L k, coef (A l) d m = t (PlaneWaves.shiftedFreq κ m) • coef l d m
theorem CoeffExtraction.map_sub (h : CoeffExtraction L k I D coef) (l l' : I.UnitQuot → ℂ) (d : D)
    (m : Fin 4 → ℤ) :
    coef (l - l') d m = coef l d m - coef l' d m := by
  have e : l - l' = l + (-1 : ℂ) • l' := by simp [sub_eq_add_neg]
  rw [e, h.map_add, h.map_smul]
  simp [sub_eq_add_neg]
theorem CoeffExtraction.scalesCoeffs_unique (h : CoeffExtraction L k I D coef)
    {t : (Fin 4 → ℂ) → ℂ} {κ : Fin 4 → ℂ}
    {A B : QuotHom I I} (hA : ScalesCoeffs L k coef t κ A) (hB : ScalesCoeffs L k coef t κ B) :
    A = B := by
  refine LinearMap.ext fun l => sub_eq_zero.1 (h.separated _ fun d m hm => ?_)
  rw [h.map_sub, hA l d m hm, hB l d m hm, sub_self]
theorem CoeffExtraction.exists_scalesCoeffs (h : CoeffExtraction L k I D coef) (t : (Fin 4 → ℂ) → ℂ)
    (κ : Fin 4 → ℂ) :
    ∃ A, ScalesCoeffs L k coef t κ A := by
  classical
  let Φ : (I.UnitQuot → ℂ) →ₗ[ℂ] (D → freqBox L k → ComplexMatrix2) :=
    { toFun := fun l d m => coef l d m
      map_add' := fun l l' => by
        funext d m
        exact h.map_add l l' d m
      map_smul' := fun a l => by
        funext d m
        exact h.map_smul a l d m }
  let T : (D → freqBox L k → ComplexMatrix2) →ₗ[ℂ] (D → freqBox L k → ComplexMatrix2) :=
    { toFun := fun Z d m => t (PlaneWaves.shiftedFreq κ m) • Z d m
      map_add' := fun Z Z' => by
        funext d m
        exact smul_add _ _ _
      map_smul' := fun a Z => by
        funext d m
        change t _ • a • Z d m = a • t _ • Z d m
        exact smul_comm _ _ _ }
  have hker : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun l hl => h.separated l fun d m hm => ?_
    exact congrFun (congrFun hl d) ⟨m, hm⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective Φ hker
  refine ⟨g ∘ₗ T ∘ₗ Φ, fun l d m hm => ?_⟩
  obtain ⟨l', hl'⟩ := h.surj (fun d m => t (PlaneWaves.shiftedFreq κ m) • coef l d m)
    fun d m => ComplexMatrix2.traceless.smul_mem _ (h.mem l d m)
  have e : T (Φ l) = Φ l' := by
    funext d m
    exact (hl' d m m.2).symm
  have e' : (g ∘ₗ T ∘ₗ Φ) l = l' := by
    change g (T (Φ l)) = l'
    rw [e]
    exact LinearMap.congr_fun hg l'
  rw [e']
  exact hl' d m hm
theorem CoeffExtraction.scalesCoeffs_all (h : CoeffExtraction L k I D coef)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {υ : ℝ} {t : (Fin 4 → ℂ) → ℂ}
    (ht : ∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip υ) {A : QuotHom I I}
    (hA : ScalesCoeffs L k coef t κ A) (l : I.UnitQuot → ℂ) (d : D) (m : Fin 4 → ℤ) :
    coef (A l) d m = t (PlaneWaves.shiftedFreq κ m) • coef l d m := by
  obtain ⟨m', hm', n, rfl⟩ := exists_mem_freqBox_add_smul (k := k) hL.1 m
  have hLpos : 0 < L := hL.1.pos
  rw [h.period, h.period, hA l d m' hm', shiftedFreq_add_period hLpos,
    ht _ (shiftedFreq_mem_openImStrip hκ m') n]
theorem quotHomInverse_eq_of_comp {A B : QuotHom I I} (h1 : A.comp B = LinearMap.id)
    (h2 : B.comp A = LinearMap.id) : quotHomInverse A = B := by
  let u : (Module.End ℂ (I.UnitQuot → ℂ))ˣ := ⟨A, B, h1, h2⟩
  exact Ring.inverse_unit u
theorem CoeffExtraction.phaseMul_comp_neg (h : CoeffExtraction L k I D coef) (e : Fin 4 → ℤ) :
    (phaseMul I e).comp (phaseMul I (-e)) = LinearMap.id := by
  refine LinearMap.ext fun l => sub_eq_zero.1 (h.separated _ fun d m _ => ?_)
  rw [h.map_sub]
  change coef (phaseMul I e (phaseMul I (-e) l)) d m - _ = 0
  rw [h.phaseMul_eq, h.phaseMul_eq, sub_eq_zero]
  congr 1
  abel
def conjQuotHom (A : QuotHom I I) : QuotHom I I where
  toFun := fun f c => conj (A (fun c' => conj (f c')) c)
  map_add' := fun f g => by
    funext c
    have e : (fun c' => conj ((f + g) c')) = (fun c' => conj (f c')) + fun c' => conj (g c') := by
      funext c'
      simp
    change conj (A (fun c' => conj ((f + g) c')) c) = _
    rw [e, map_add]
    simp
  map_smul' := fun a f => by
    funext c
    have e : (fun c' => conj ((a • f) c')) = conj a • fun c' => conj (f c') := by
      funext c'
      simp
    change conj (A (fun c' => conj ((a • f) c')) c) = _
    rw [e, map_smul]
    simp
theorem linearMapEntry_conjQuotHom [Finite I.UnitQuot] (A : QuotHom I I) :
    linearMapEntry (conjQuotHom A) = conjKernel (linearMapEntry A) := by
  classical
  funext c' c
  have e : (fun c'' => conj ((Pi.single c (1 : ℂ) : I.UnitQuot → ℂ) c'')) = Pi.single c 1 := by
    funext c''
    by_cases hc : c'' = c
    · subst hc
      simp
    · simp [Pi.single_eq_of_ne hc]
  change conj (A (fun c'' => conj ((Pi.single c (1 : ℂ) : I.UnitQuot → ℂ) c'')) c') = _
  rw [e]
  rfl
theorem CoeffExtraction.multiplierMatrixFacts (h : CoeffExtraction L k I D coef)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {Multiplies : (Fin 4 → ℂ) → QuotHom I I → Prop} {M : (Fin 4 → ℂ) → QuotHom I I}
    {υ : ℝ} {t : (Fin 4 → ℂ) → ℂ}
    (hMul : ∀ κ A, Multiplies κ A ↔ ScalesCoeffs L k coef t κ A)
    (hM : ∀ κ, M κ = Classical.epsilon (Multiplies κ))
    (ht : ∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q) :
    MultiplierMatrixFacts I Multiplies M υ t := by
  have := h.finite_quot
  have hs : ∀ κ, ScalesCoeffs L k coef t κ (M κ) := fun κ => by
    rw [← hMul, hM]
    obtain ⟨A, hA⟩ := h.exists_scalesCoeffs t κ
    exact Classical.epsilon_spec (p := Multiplies κ) ⟨A, (hMul κ A).2 hA⟩
  have huniq : ∀ κ A, ScalesCoeffs L k coef t κ A → A = M κ := fun κ A hA =>
    h.scalesCoeffs_unique hA (hs κ)
  refine ⟨fun κ _ => ⟨(hMul κ _).2 (hs κ), fun A hA => huniq κ A ((hMul κ A).1 hA)⟩, ?_, ?_, ?_⟩
  · intro e κ hκ
    rw [quotHomInverse_eq_of_comp (h.phaseMul_comp_neg e) (by simpa using h.phaseMul_comp_neg (-e))]
    refine (huniq _ _ fun l d m hm => ?_).symm
    change coef (phaseMul I (-e) (M κ (phaseMul I e l))) d m = _
    rw [h.phaseMul_eq, h.scalesCoeffs_all hL ht hκ (hs κ), h.phaseMul_eq, shiftedFreq_addTwoPiInt]
    simp only [sub_neg_eq_add, add_sub_cancel_right]
  · intro heven κ hκ
    refine LinearMap.ext fun f => eq_of_wPairing h.weight_ne fun g => ?_
    rw [wPairing_quotHomTranspose h.weight_ne, h.wPairing_eq, h.wPairing_eq]
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun d _ => ?_
    rw [hs κ f d m hm, hs (-κ) g d (-m) (neg_mem_freqBox hm), shiftedFreq_neg,
      heven _ (shiftedFreq_mem_openImStrip hκ m)]
    exact (tracelessPairing_smul_left (h.mem _ _ _) (h.mem _ _ _) _).symm
  · intro heven hconj κ hκ
    have hc : ScalesCoeffs L k coef t (-conjVec κ) (conjQuotHom (M κ)) := fun l d m hm => by
      have hm' := neg_mem_freqBox hm
      have e : (conjQuotHom (M κ)) l = fun c => conj (M κ (fun c' => conj (l c')) c) := rfl
      rw [e, h.conj_eq, hs κ _ d _ hm', Matrix.conjTranspose_smul, h.conj_eq, neg_neg,
        Matrix.conjTranspose_conjTranspose]
      congr 1
      have hq := shiftedFreq_mem_openImStrip hκ (-m)
      change conj (t _) = _
      rw [hconj _ hq, ← heven _ (conjVec_mem_openImStrip hq), neg_conjVec_shiftedFreq]
    rw [← linearMapEntry_conjQuotHom, ← huniq _ _ hc]
end Abstract
section Waves
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem bilinDot_castVec (m : Fin 4 → ℤ) (x : AmbientSpace) :
    bilinDot (toComplexVec (castVec m)) (toComplexVec x) = ((∑ μ, (m μ : ℝ) * x μ : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec, castVec]
theorem fourierPhase_eq_conj (m : Fin 4 → ℤ) (x : AmbientSpace) :
    fourierPhase m x = conj (integerWave m x) := by
  rw [fourierPhase, integerWave, ← Complex.exp_conj, bilinDot_castVec]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring
theorem conj_fourierPhase_neg (m : Fin 4 → ℤ) (x : AmbientSpace) :
    conj (fourierPhase (-m) x) = fourierPhase m x := by
  rw [fourierPhase, fourierPhase, ← Complex.exp_conj, bilinDot_castVec, bilinDot_castVec]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Pi.neg_apply]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring
theorem fourierPhase_mul_integerWave (m e : Fin 4 → ℤ) (x : AmbientSpace) :
    fourierPhase m x * integerWave e x = fourierPhase (m - e) x := by
  rw [fourierPhase, fourierPhase, integerWave, ← Complex.exp_add, bilinDot_castVec,
    bilinDot_castVec, bilinDot_castVec]
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring
theorem integerWave_add_castVec (e n : Fin 4 → ℤ) (x : AmbientSpace) :
    integerWave e (x + castVec n) = integerWave e x := by
  have h : integerWave e (x + castVec n) =
      integerWave e x * Complex.exp (((∑ μ, e μ * n μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    rw [integerWave, integerWave, ← Complex.exp_add, bilinDot_castVec, bilinDot_castVec]
    congr 1
    simp only [Pi.add_apply, castVec, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem fourierPhase_add_period {L k : ℕ} (hL : 0 < L) (m n : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k 0) :
    fourierPhase (m + ((L ^ k : ℕ) : ℤ) • n) (x : AmbientSpace) = fourierPhase m (x : AmbientSpace) := by
  obtain ⟨z, hz⟩ := x.2
  have hη : (L : ℝ) ^ k * meshAt L k 0 = 1 := by
    have h := finestMesh_inv L k
    have h0 : finestMesh L k ≠ 0 := by
      intro e
      rw [e, inv_zero] at h
      exact (pow_ne_zero k (by exact_mod_cast hL.ne' : (L : ℝ) ≠ 0)) h.symm
    rw [← h]
    exact inv_mul_cancel₀ h0
  have h : fourierPhase (m + ((L ^ k : ℕ) : ℤ) • n) (x : AmbientSpace) =
      fourierPhase m (x : AmbientSpace) *
        Complex.exp (((-∑ μ, n μ * z μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    rw [fourierPhase, fourierPhase, ← Complex.exp_add, bilinDot_castVec, bilinDot_castVec]
    congr 1
    have e : ∑ μ, (((m + ((L ^ k : ℕ) : ℤ) • n) μ : ℤ) : ℝ) * (x : AmbientSpace) μ =
        ∑ μ, (m μ : ℝ) * (x : AmbientSpace) μ + ∑ μ, ((n μ * z μ : ℤ) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [hz μ]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      linear_combination ((n μ : ℝ) * (z μ : ℝ)) * hη
    rw [e]
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Waves
section Coefficients
open Classical
theorem pauliFamily_mem (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliFamily_conjTranspose (a : Fin 3) :
    (ComplexMatrix2.pauliFamily a).conjTranspose = ComplexMatrix2.pauliFamily a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.conjTranspose_apply]
theorem pauliFamily_sum_injective {c c' : Fin 3 → ℂ}
    (h : ∑ a, c a • ComplexMatrix2.pauliFamily a = ∑ a, c' a • ComplexMatrix2.pauliFamily a) :
    c = c' := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_injective <;> assumption
variable {L k : ℕ}
theorem fourierCoeff_add (hf : Finite (VertexClass L k)) (g g' : FullSpace.Vertex L k 0 → ComplexMatrix2)
    (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => g x + g' x) m = fourierCoeff L k g m + fourierCoeff L k g' m := by
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype, smul_add, Finset.sum_add_distrib]
theorem fourierCoeff_smul (hf : Finite (VertexClass L k)) (c : ℂ)
    (g : FullSpace.Vertex L k 0 → ComplexMatrix2) (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => c • g x) m = c • fourierCoeff L k g m := by
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_comm c, smul_comm (fourierPhase m _) c, smul_comm c]
theorem fourierCoeff_mem (hf : Finite (VertexClass L k)) {g : FullSpace.Vertex L k 0 → ComplexMatrix2}
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) (m : Fin 4 → ℤ) :
    fourierCoeff L k g m ∈ ComplexMatrix2.traceless := by
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype]
  exact ComplexMatrix2.traceless.smul_mem _
    (ComplexMatrix2.traceless.sum_mem fun c _ => ComplexMatrix2.traceless.smul_mem _ (hg _))
theorem fourierCoeff_integerWave_smul (e : Fin 4 → ℤ) (g : FullSpace.Vertex L k 0 → ComplexMatrix2)
    (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => integerWave e (x : InfiniteLattice.AmbientSpace) • g x) m =
      fourierCoeff L k g (m - e) := by
  simp only [PlaneWaves.fourierCoeff, smul_smul, fourierPhase_mul_integerWave]
theorem fourierCoeff_conjTranspose (hf : Finite (VertexClass L k))
    (g : FullSpace.Vertex L k 0 → ComplexMatrix2) (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => (g x).conjTranspose) m =
      (fourierCoeff L k g (-m)).conjTranspose := by
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact (conj_fourierPhase_neg m _).symm
theorem fourierCoeff_wave_sum (hF : FinestFourierSums.FourierFacts L k)
    (Z : (Fin 4 → ℤ) → ComplexMatrix2) {m₀ : Fin 4 → ℤ} (h₀ : m₀ ∈ freqBox L k) :
    fourierCoeff L k
        (fun x => ∑ m ∈ freqBox L k, integerWave m (x : InfiniteLattice.AmbientSpace) • Z m) m₀ =
      Z m₀ := by
  have := hF.finite_vertexClass
  let _ := Fintype.ofFinite (VertexClass L k)
  have ho := fun m (hm : m ∈ freqBox L k) => hF.orthonormal m₀ h₀ m hm
  simp only [finsum_eq_sum_of_fintype] at ho
  calc fourierCoeff L k
        (fun x => ∑ m ∈ freqBox L k, integerWave m (x : InfiniteLattice.AmbientSpace) • Z m) m₀
      = ∑ m ∈ freqBox L k, (((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ d : VertexClass L k,
          conj (integerWave m₀ (Quot.out d : FullSpace.Vertex L k 0)) *
            integerWave m (Quot.out d : FullSpace.Vertex L k 0)) • Z m := by
        simp only [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype, Finset.smul_sum, smul_smul,
          Finset.mul_sum, Finset.sum_smul, fourierPhase_eq_conj]
        rw [Finset.sum_comm]
    _ = ∑ m ∈ freqBox L k, (if m₀ = m then (1 : ℂ) else 0) • Z m :=
        Finset.sum_congr rfl fun m hm => by rw [ho m hm]
    _ = Z m₀ := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, h₀, if_true]
variable {P D : Type} [Fintype D] (f : (Fin 4 → ℤ) → P → P)
  (loc : P → InfiniteLattice.AmbientSpace) (w : ℝ)
abbrev pairedData : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × P) (fun n ι => (ι.1, f n ι.2)) (fun ι => loc ι.2) w
variable (L k) (rd : FullSpace.Vertex L k 0 → D → P)
def matrixAt (l : (pairedData f loc w).UnitQuot → ℂ) (d : D) :
    FullSpace.Vertex L k 0 → ComplexMatrix2 :=
  fun x => ofPauliCoeffs (fun ι => l ((pairedData f loc w).mkQuot 1 ι)) (rd x d)
def labelCoeff (l : (pairedData f loc w).UnitQuot → ℂ) (d : D) (m : Fin 4 → ℤ) :
    ComplexMatrix2 :=
  fourierCoeff L k (matrixAt L k f loc w rd l d) m
structure PlaceLayout : Prop where
  isPeriodic : IsPeriodic (pairedData f loc w)
  fourier : FinestFourierSums.FourierFacts L k
  pos_eq : ∀ x d, loc (rd x d) = (x : InfiniteLattice.AmbientSpace)
  translate_eq : ∀ n x d, f n (rd x d) = rd (FullSpace.vertexImage (intShift n) x) d
  bijective : Function.Bijective fun p : FullSpace.Vertex L k 0 × D => rd p.1 p.2
  expansion : ∀ l d x, matrixAt L k f loc w rd l d x =
    ∑ m ∈ freqBox L k, integerWave m (x : InfiniteLattice.AmbientSpace) •
      labelCoeff L k f loc w rd l d m
  wPairing_eq : ∀ l l', wPairing ((pairedData f loc w).quotWeight 1) l l' =
    ∑ m ∈ freqBox L k, ∑ d,
      tracelessPairing (labelCoeff L k f loc w rd l d m)
        (labelCoeff L k f loc w rd l' d (-m))
variable {f loc w L k rd}
omit [Fintype D] in
theorem matrixAt_mem (l : (pairedData f loc w).UnitQuot → ℂ) (d : D) (x : FullSpace.Vertex L k 0) :
    matrixAt L k f loc w rd l d x ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.sum_mem fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem a)
omit [Fintype D] in
theorem quotWeight_eq (c : (pairedData f loc w).UnitQuot) :
    (pairedData f loc w).quotWeight 1 c = w := by
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  exact (Classical.epsilon_spec (p := fun w' => ∀ ι', (pairedData f loc w).mkQuot 1 ι' =
    Quot.mk _ ι → (pairedData f loc w).weightOf ι' = w') ⟨w, fun _ _ => rfl⟩ ι rfl).symm
omit [Fintype D] in
theorem phaseOn_mkQuot (hI : IsPeriodic (pairedData f loc w)) (e : Fin 4 → ℤ)
    (ι : Fin 3 × P) :
    phaseOn (pairedData f loc w) e ((pairedData f loc w).mkQuot 1 ι) = integerWave e (loc ι.2) := by
  let h : (pairedData f loc w).UnitQuot → ℂ :=
    Quot.lift (fun ι : Fin 3 × P => integerWave e (loc ι.2)) (by
      rintro ι _ ⟨n, rfl⟩
      have e' := hI.pos_translate (1 • n) ι
      change loc (f (1 • n) ι.2) = loc ι.2 + _ at e'
      change integerWave e (loc ι.2) = integerWave e (loc (f (1 • n) ι.2))
      rw [e', integerWave_add_castVec])
  have hz : ∃ z, ∀ ι', (pairedData f loc w).mkQuot 1 ι' = (pairedData f loc w).mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec ((pairedData f loc w).pos ι'))) = z :=
    ⟨h ((pairedData f loc w).mkQuot 1 ι), fun ι' e' => by
      rw [← e']
      rfl⟩
  exact (Classical.epsilon_spec hz ι rfl).symm
theorem PlaceLayout.coeffRepresentation (h : PlaceLayout L k f loc w rd) (hpos : 0 < L) :
    CoeffExtraction L k (pairedData f loc w) D (labelCoeff L k f loc w rd) := by
  have hf := h.fourier.finite_vertexClass
  have hw : w ≠ 0 := (h.isPeriodic.weight_pos ()).ne'
  refine ⟨h.isPeriodic.finite_quot, fun c => by rw [quotWeight_eq]; exact hw, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h.wPairing_eq, ?_⟩
  · intro l l' d m
    have e : matrixAt L k f loc w rd (l + l') d =
        fun x => matrixAt L k f loc w rd l d x + matrixAt L k f loc w rd l' d x := by
      funext x
      simp only [matrixAt, ofPauliCoeffs, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [labelCoeff, e]
    exact fourierCoeff_add hf _ _ m
  · intro a l d m
    have e : matrixAt L k f loc w rd (a • l) d = fun x => a • matrixAt L k f loc w rd l d x := by
      funext x
      simp only [matrixAt, ofPauliCoeffs, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
    rw [labelCoeff, e]
    exact fourierCoeff_smul hf _ _ m
  · intro l d m
    exact fourierCoeff_mem hf (matrixAt_mem l d) m
  · intro l hl
    funext c
    obtain ⟨⟨a, y⟩, rfl⟩ := Quot.exists_rep c
    obtain ⟨⟨x, d⟩, rfl⟩ := h.bijective.2 y
    have e := h.expansion l d x
    rw [Finset.sum_eq_zero fun m hm => by rw [hl d m hm, smul_zero]] at e
    have e' : (fun a => l ((pairedData f loc w).mkQuot 1 (a, rd x d))) = fun _ => 0 :=
      pauliFamily_sum_injective (by simpa [matrixAt, ofPauliCoeffs] using e)
    exact congrFun e' a
  · intro Z hZ
    let g : D → FullSpace.Vertex L k 0 → ComplexMatrix2 := fun d x =>
      ∑ m ∈ freqBox L k, integerWave m (x : InfiniteLattice.AmbientSpace) • Z d m
    have hg : ∀ d x, g d x ∈ ComplexMatrix2.traceless := fun d x =>
      ComplexMatrix2.traceless.sum_mem fun m _ => ComplexMatrix2.traceless.smul_mem _ (hZ d m)
    have hper : ∀ d n x, g d (FullSpace.vertexImage (intShift n) x) = g d x := fun d n x =>
      Finset.sum_congr rfl fun m _ => congrArg (· • Z d m) (h.fourier.integerWave_periodic m n x)
    have hco : ∀ d x, ∃ c : Fin 3 → ℂ, g d x = ∑ a, c a • ComplexMatrix2.pauliFamily a :=
      fun d x => (ComplexMatrix2.existsUnique_traceless_eq_sum_pauliFamily (hg d x)).exists
    choose co hco using hco
    let inv := (Equiv.ofBijective _ h.bijective).symm
    have hinv : ∀ x d, inv (rd x d) = (x, d) := fun x d =>
      (Equiv.ofBijective _ h.bijective).symm_apply_apply (x, d)
    let F : Fin 3 × P → ℂ := fun ι => co (inv ι.2).2 (inv ι.2).1 ι.1
    have hF : ∀ a n y, F (a, f n y) = F (a, y) := by
      intro a n y
      obtain ⟨⟨x, d⟩, rfl⟩ := h.bijective.2 y
      change co (inv (f n (rd x d))).2 (inv (f n (rd x d))).1 a =
        co (inv (rd x d)).2 (inv (rd x d)).1 a
      rw [h.translate_eq, hinv, hinv]
      have e : co d (FullSpace.vertexImage (intShift n) x) = co d x :=
        pauliFamily_sum_injective (by rw [← hco, ← hco, hper])
      exact congrFun e a
    let l : (pairedData f loc w).UnitQuot → ℂ := Quot.lift F (by
      rintro ⟨a, y⟩ _ ⟨n, rfl⟩
      exact (hF a (1 • n) y).symm)
    refine ⟨l, fun d m hm => ?_⟩
    have e : matrixAt L k f loc w rd l d = g d := by
      funext x
      rw [hco d x]
      simp only [matrixAt, ofPauliCoeffs]
      refine Finset.sum_congr rfl fun a _ => ?_
      change F (a, rd x d) • _ = _
      change co (inv (rd x d)).2 (inv (rd x d)).1 a • _ = _
      rw [hinv]
    rw [labelCoeff, e]
    exact fourierCoeff_wave_sum h.fourier (Z d) hm
  · intro l d m n
    simp only [labelCoeff, PlaneWaves.fourierCoeff]
    congr 1
    refine finsum_congr fun c => ?_
    rw [fourierPhase_add_period hpos]
  · intro e l d m
    have e' : matrixAt L k f loc w rd (phaseMul (pairedData f loc w) e l) d =
        fun x : FullSpace.Vertex L k 0 =>
          integerWave e (x : InfiniteLattice.AmbientSpace) • matrixAt L k f loc w rd l d x := by
      funext x
      simp only [matrixAt, ofPauliCoeffs, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      change (phaseOn (pairedData f loc w) e _ * _) • _ = _
      rw [phaseOn_mkQuot h.isPeriodic, h.pos_eq]
    rw [labelCoeff, e']
    exact fourierCoeff_integerWave_smul e _ m
  · intro l d m
    have e' : matrixAt L k f loc w rd (fun c => conj (l c)) d =
        fun x => (matrixAt L k f loc w rd l d x).conjTranspose := by
      funext x
      simp only [matrixAt, ofPauliCoeffs, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        pauliFamily_conjTranspose]
      rfl
    rw [labelCoeff, e']
    exact fourierCoeff_conjTranspose hf _ m
end Coefficients
section Concrete
variable {L k : ℕ}
theorem vertexLayout (hF : FinestFourierSums.FourierFacts L k)
    (hI : IsPeriodic (colourVertices L k 0)) (hC : VertexCoeffFacts L k) :
    PlaceLayout L k (fun n x => FullSpace.vertexImage (intShift n) x)
      (fun x : FullSpace.Vertex L k 0 => (x : InfiniteLattice.AmbientSpace)) (meshAt L k 0 ^ 4)
      (fun x (_ : Unit) => x) where
  isPeriodic := hI
  fourier := hF
  pos_eq := fun _ _ => rfl
  translate_eq := fun _ _ _ => rfl
  bijective := ⟨fun p q e => Prod.ext e (Subsingleton.elim _ _), fun y => ⟨(y, ()), rfl⟩⟩
  expansion := fun l _ x => hC.expansion l x
  wPairing_eq := fun l l' => (hC.pairing_eq l l').trans
    (Finset.sum_congr rfl fun _ _ => by rw [Fintype.sum_unique]; rfl)
theorem edgeLayout (hF : FinestFourierSums.FourierFacts L k)
    (hI : IsPeriodic (colourEdges L k 0)) (hC : EdgeCoeffFacts L k)
    (hT : ∀ (n : Fin 4 → ℤ) (c : Fin 3) (b : PosEdge L k 0) (μ : Fin 4),
      b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k 0) μ →
      ((colourEdges L k 0).translate n (c, b) : Fin 3 × PosEdge L k 0) =
        (c, TowerTranslations.posEdgeForward
          (FullSpace.vertexImage (intShift n) b.1.initial) μ))
    (hη : meshAt L k 0 ≠ 0) :
    PlaceLayout L k (fun n b => shiftEdge n b)
      (fun b : PosEdge L k 0 => (b.1.initial : InfiniteLattice.AmbientSpace))
      (meshAt L k 0 ^ 4) (fun x μ => edgeAt L k x μ) where
  isPeriodic := hI
  fourier := hF
  pos_eq := fun _ _ => rfl
  translate_eq := fun n x μ =>
    congrArg Prod.snd
      (hT n 0 (edgeAt L k x μ) μ (by simp [edgeAt, InfiniteLattice.Link.forwardFrom]))
  bijective := by
    constructor
    · rintro ⟨x, μ⟩ ⟨x', μ'⟩ e
      have e1 : x = x' := congrArg (fun b : PosEdge L k 0 => b.1.initial) e
      subst e1
      have e2 : x + InfiniteLattice.axisStep _ μ = x + InfiniteLattice.axisStep _ μ' :=
        congrArg (fun b : PosEdge L k 0 => b.1.terminal) e
      have e3 := add_left_cancel e2
      have e4 : (InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.AmbientSpace) μ =
          (InfiniteLattice.axisStep (meshAt L k 0) μ' : InfiniteLattice.AmbientSpace) μ :=
        congrArg (fun s : InfiniteLattice.LatticePoint (meshAt L k 0) =>
          (s : InfiniteLattice.AmbientSpace) μ) e3
      have e5 : μ = μ' := by
        by_contra hne
        simp only [InfiniteLattice.axisStep, Pi.single_eq_same, Pi.single_eq_of_ne hne] at e4
        exact hη e4
      rw [e5]
    · rintro ⟨b, μ, hμ⟩
      refine ⟨(b.initial, μ), Subtype.ext ?_⟩
      refine InfiniteLattice.Link.ext rfl ?_
      change b.initial + InfiniteLattice.axisStep _ μ = b.terminal
      rw [← hμ]
      abel
  expansion := fun l μ x => hC.expansion l μ x
  wPairing_eq := fun l l' => hC.pairing_eq l l'
theorem faceLayout (hF : FinestFourierSums.FourierFacts L k)
    (hI : IsPeriodic (colourFaces L k 0)) (hC : FaceCoeffFacts L k) :
    PlaceLayout L k (fun n p => shiftFace n p)
      (fun p : FullSpace.Face L k 0 => (p.corner : InfiniteLattice.AmbientSpace))
      (meshAt L k 0 ^ 4)
      (fun x (p : AxisPair) => (⟨x, p.1.1, p.1.2, p.2⟩ : FullSpace.Face L k 0)) where
  isPeriodic := hI
  fourier := hF
  pos_eq := fun _ _ => rfl
  translate_eq := fun _ _ _ => rfl
  bijective := by
    constructor
    · rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ ⟨x', ⟨⟨μ', ν'⟩, h'⟩⟩ e
      simp only [InfiniteLattice.ElementaryPlaquette.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      rfl
    · intro p
      exact ⟨(p.corner, ⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩), rfl⟩
  expansion := fun l p x => hC.expansion l p.1.1 p.1.2 p.2 x
  wPairing_eq := fun l l' => hC.pairing_eq l l'
end Concrete
theorem claim_holds (hS : PlaneWaveCalculus.VertexCoeffsHold)
    (hB : PlaneWaveEdgeCoefficientsHold)
    (hP : PlaneWaveCalculus.FaceCoeffsHold)
    (hFS : FinestFourierSums.Claim)
    (hIx : TowerIndexSets.Claim) (hT : TowerTranslations.Claim) :
    Claim := by
  intro L hL k hk υ _ t ht
  obtain ⟨hIs, hIb, hIp⟩ := hIx L hL k 0 (Nat.zero_le k)
  have hF := hFS L hL k hk
  have hpos : 0 < L := hL.1.pos
  have hη : meshAt L k 0 ≠ 0 := by
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact zpow_ne_zero _ hL0
  refine ⟨?_, ?_, ?_⟩
  · exact ((vertexLayout hF hIs (hS L hL k hk)).coeffRepresentation hpos).multiplierMatrixFacts hL
      (Multiplies := ScalesVertexCoeffs L k t) (M := vertexFourierMultiplier L k t)
      (fun κ A => ⟨fun h l _ m hm => h l m hm, fun h l m hm => h l () m hm⟩) (fun _ => rfl) ht
  · exact ((edgeLayout hF hIb (hB L hL k hk)
      (fun n c b μ => (hT L hL k 0 hk (Nat.zero_le k) n).2.2.2.1 c b μ) hη).coeffRepresentation
        hpos).multiplierMatrixFacts hL
      (Multiplies := ScalesEdgeCoeffs L k t) (M := edgeFourierMultiplier L k t)
      (fun κ A => ⟨fun h l μ m hm => h l μ m hm, fun h l μ m hm => h l μ m hm⟩) (fun _ => rfl) ht
  · exact ((faceLayout hF hIp (hP L hL k hk)).coeffRepresentation hpos).multiplierMatrixFacts hL
      (Multiplies := ScalesFaceCoeffs L k t) (M := faceFourierMultiplier L k t)
      (fun κ A => ⟨fun h l p m hm => h l p.1.1 p.1.2 p.2 m hm,
        fun h l μ ν hμν m hm => h l ⟨(μ, ν), hμν⟩ m hm⟩) (fun _ => rfl) ht
end YangMills.Construction.Tower.PeriodicMultiplierMatrices
end
