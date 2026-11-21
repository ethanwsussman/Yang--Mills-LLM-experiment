import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbolsProof
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FreeResolvents
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open PlaneWaves hiding shiftedFreq
open PlaneWaveCalculus (MultiplierMatrixFacts SymbolFormulas periodShift conjVec meshC integerWave)
open scoped ComplexConjugate
theorem isRightHalfPlaneArg_arg {z : ℂ} (hz : 0 < z.re) : IsRightHalfPlaneArg z (Complex.arg z) := by
  have h := (Complex.abs_arg_lt_pi_div_two_iff (z := z)).2 (Or.inl hz)
  refine ⟨abs_lt.1 h, ?_⟩
  have e := Complex.norm_mul_exp_arg_mul_I z
  rw [mul_comm Complex.I]
  exact e.symm
theorem eq_arg_of_isRightHalfPlaneArg {z : ℂ} (hz : 0 < z.re) {φ : ℝ} (h : IsRightHalfPlaneArg z φ) :
    φ = Complex.arg z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 fun e => by simp [e] at hz
  have hφ : φ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [h.1.1, Real.pi_pos], by linarith [h.1.2, Real.pi_pos]⟩
  have e := Complex.arg_mul_cos_add_sin_mul_I hn hφ
  have e' : (‖z‖ : ℂ) * (Complex.cos φ + Complex.sin φ * Complex.I) = z := by
    rw [← Complex.exp_mul_I, mul_comm (φ : ℂ)]
    exact h.2.symm
  rw [e'] at e
  exact e.symm
theorem rightHalfPlaneArg_eq_arg {z : ℂ} (hz : 0 < z.re) : rightHalfPlaneArg z = Complex.arg z :=
  eq_arg_of_isRightHalfPlaneArg hz
    (Classical.epsilon_spec (p := IsRightHalfPlaneArg z) ⟨_, isRightHalfPlaneArg_arg hz⟩)
theorem principalRpow_eq_cpow (σ : ℝ) {z : ℂ} (hz : 0 < z.re) :
    principalRpow σ z = z ^ (σ : ℂ) := by
  have h0 : z ≠ 0 := fun e => by simp [e] at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
  rw [principalRpow, rightHalfPlaneArg_eq_arg hz, Complex.cpow_def_of_ne_zero h0, Complex.log,
    Real.rpow_def_of_pos hn, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem norm_principalRpow (σ : ℝ) (z : ℂ) : ‖principalRpow σ z‖ = ‖z‖ ^ σ := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.norm_principalRpow <;> assumption
theorem conj_principalRpow (σ : ℝ) {z : ℂ} (hz : 0 < z.re) :
    conj (principalRpow σ z) = principalRpow σ (conj z) := by
  have hc : 0 < (conj z).re := by simpa using hz
  have harg : Complex.arg z ≠ Real.pi := by
    have h := (Complex.abs_arg_lt_pi_div_two_iff (z := z)).2 (Or.inl hz)
    have := (abs_lt.1 h).2
    intro e
    linarith [Real.pi_pos]
  rw [principalRpow_eq_cpow σ hz, principalRpow_eq_cpow σ hc, Complex.conj_cpow _ _ harg]
  simp
theorem principalRpow_neg_half_mul_self (z : ℂ) (hz : 0 < z.re) :
    principalRpow (-(1 / 2)) z * principalRpow (-(1 / 2)) z = principalRpow (-1) z := by
  have h0 : z ≠ 0 := fun e => by simp [e] at hz
  rw [principalRpow_eq_cpow _ hz, principalRpow_eq_cpow _ hz, ← Complex.cpow_add _ _ h0]
  congr 1
  push_cast
  ring
theorem principalRpow_half_mul_neg_half (z : ℂ) (hz : 0 < z.re) :
    principalRpow (1 / 2) z * principalRpow (-(1 / 2)) z = 1 := by
  have h0 : z ≠ 0 := fun e => by simp [e] at hz
  rw [principalRpow_eq_cpow _ hz, principalRpow_eq_cpow _ hz, ← Complex.cpow_add _ _ h0]
  simp
theorem principalRpow_neg_one_mul (z : ℂ) (hz : 0 < z.re) :
    principalRpow (-1) z * z = 1 := by
  have h0 : z ≠ 0 := fun e => by simp [e] at hz
  rw [principalRpow_eq_cpow _ hz]
  simp [Complex.cpow_neg, h0]
theorem isHolomorphicIn_of_differentiableOn {O : Set (Fin 4 → ℂ)} (hO : IsOpen O)
    {f : (Fin 4 → ℂ) → ℂ} (hf : DifferentiableOn ℂ f O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x := by
  refine ⟨hO, continuousOn_pi.2 fun _ => hf.continuousOn, fun a ha j => ?_⟩
  have hc : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hpre : (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ⁻¹' O ∈
      nhds (0 : ℂ) :=
    (hO.preimage hc).mem_nhds (by simpa using ha)
  filter_upwards [hpre] with ζ hζ
  refine differentiableAt_pi.2 fun _ => ?_
  have h1 : DifferentiableAt ℂ f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) :=
    (hf _ hζ).differentiableAt (hO.mem_nhds hζ)
  have h2 : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact h1.comp ζ h2
theorem differentiable_symbolSquare (L k : ℕ) : Differentiable ℂ (symbolSquare L k) := by
  unfold symbolSquare forwardSymbol
  simp only [Pi.neg_apply]
  fun_prop
theorem differentiable_shiftedFreq (m : Fin 4 → ℤ) :
    Differentiable ℂ fun κ : Fin 4 → ℂ => PlaneWaves.shiftedFreq κ m := by
  unfold PlaneWaves.shiftedFreq
  fun_prop
section Bounds
variable {L k : ℕ}
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem exists_periodShift_reduced (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hF : SymbolFormulas L k) (q : Fin 4 → ℂ) :
    ∃ q' θ : Fin 4 → ℝ, (∀ ν, |q' ν| ≤ Real.pi / finestMesh L k) ∧
      (∀ ν, θ ν = (q ν).im) ∧
      symbolSquare L k q = symbolSquare L k (PlaneWaveBounds.complexPoint q' θ) := by
  have hη := finestMesh_pos (k := k) hL
  set η := finestMesh L k with hηd
  let x : Fin 4 → ℝ := fun ν => η / (2 * Real.pi) * (q ν).re
  let e : Fin 4 → ℤ := fun ν => round (x ν)
  let q' : Fin 4 → ℝ := fun ν => (q ν).re - 2 * Real.pi / η * (e ν : ℝ)
  refine ⟨q', fun ν => (q ν).im, fun ν => ?_, fun _ => rfl, ?_⟩
  · have h1 : q' ν = 2 * Real.pi / η * (x ν - round (x ν)) := by
      simp only [q', x, e]
      field_simp
    have h2 := abs_sub_round (x ν)
    rw [h1, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / η)]
    calc 2 * Real.pi / η * |x ν - round (x ν)| ≤ 2 * Real.pi / η * (1 / 2) := by gcongr
      _ = Real.pi / η := by ring
  · have hp : periodShift L k q (-e) = PlaneWaveBounds.complexPoint q' fun ν => (q ν).im := by
      funext μ
      simp only [periodShift, PlaneWaveBounds.complexPoint, q', meshC, Pi.neg_apply]
      conv_lhs => rw [← Complex.re_add_im (q μ)]
      push_cast
      rw [← hηd]
      ring
    rw [← hp, hF.symbolSquare_periodic]
theorem symbolSquare_add_one_bounds (hE : PlaneWaveBounds.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hF : SymbolFormulas L k)
    {q : Fin 4 → ℂ} (hq : q ∈ imStrip (1 / 8)) :
    9 / 10 ≤ (symbolSquare L k q + 1).re ∧
      ‖symbolSquare L k q + 1‖ ≤ 3 * (4 * (Real.pi / finestMesh L k) ^ 2 + 1) := by
  obtain ⟨q', θ, h1, h2, h3⟩ := exists_periodShift_reduced hL hF q
  have hθ : ∀ ν, |θ ν| ≤ 1 / 8 := fun ν => by rw [h2]; exact hq ν
  obtain ⟨-, hB, -⟩ := hE.1 L k hL hk q' θ h1 hθ
  obtain ⟨hd, hre, -, hn, -, -⟩ := hB
  have hD0 : 0 ≤ PlaneWaveBounds.realSymbolSquare L k q' :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hD1 : PlaneWaveBounds.realSymbolSquare L k q' ≤ 4 * (Real.pi / finestMesh L k) ^ 2 := by
    have : ∀ ν, ‖forwardSymbol L k (toComplexVec q') ν‖ ^ 2 ≤ (Real.pi / finestMesh L k) ^ 2 :=
      fun ν => by
        have := (hd ν).2.trans (h1 ν)
        gcongr
    simp only [PlaneWaveBounds.realSymbolSquare, Fin.sum_univ_four]
    linarith [this 0, this 1, this 2, this 3]
  rw [h3]
  constructor
  · linarith
  · linarith
theorem rpow_le_rpow_add_rpow {a b x σ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hax : a ≤ x) (hxb : x ≤ b) :
    x ^ σ ≤ a ^ σ + b ^ σ := by
  have h1 : 0 ≤ a ^ σ := Real.rpow_nonneg ha.le σ
  have h2 : 0 ≤ b ^ σ := Real.rpow_nonneg hb σ
  rcases le_total 0 σ with h | h
  · have := Real.rpow_le_rpow (ha.le.trans hax) hxb h
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha hax h
    linarith
end Bounds
section Powers
variable {L k : ℕ}
theorem shiftedSymbolPow_periodShift (hF : SymbolFormulas L k) (σ : ℝ) (q : Fin 4 → ℂ)
    (e : Fin 4 → ℤ) : shiftedSymbolPow L k σ (periodShift L k q e) = shiftedSymbolPow L k σ q := by
  simp only [shiftedSymbolPow, hF.symbolSquare_periodic]
theorem shiftedSymbolPow_neg (hF : SymbolFormulas L k) (σ : ℝ) (q : Fin 4 → ℂ) :
    shiftedSymbolPow L k σ (-q) = shiftedSymbolPow L k σ q := by
  simp only [shiftedSymbolPow, hF.symbolSquare_neg]
theorem shiftedFreq_im (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) (μ : Fin 4) :
    (PlaneWaves.shiftedFreq κ m μ).im = (κ μ).im := by
  simp [PlaneWaves.shiftedFreq]
theorem shiftedFreq_mem_imStrip {κ : Fin 4 → ℂ} {υ : ℝ} (hκ : κ ∈ imStrip υ) (m : Fin 4 → ℤ) :
    PlaneWaves.shiftedFreq κ m ∈ imStrip υ := fun μ => by
  rw [shiftedFreq_im]
  exact hκ μ
theorem openImStrip_subset_imStrip {υ υ' : ℝ} (h : υ ≤ υ') : openImStrip υ ⊆ imStrip υ' :=
  fun _ hκ μ => (hκ μ).le.trans h
theorem imStrip_subset_openImStrip {υ υ' : ℝ} (h : υ < υ') : imStrip υ ⊆ openImStrip υ' :=
  fun _ hκ μ => (hκ μ).trans_lt h
theorem isOpen_openImStrip (υ : ℝ) : IsOpen (openImStrip υ) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
theorem differentiableOn_shiftedSymbolPow
    (hre : ∀ q ∈ imStrip (1 / 8), 9 / 10 ≤ (symbolSquare L k q + 1).re)
    (σ : ℝ) (m : Fin 4 → ℤ) :
    DifferentiableOn ℂ (fun κ => shiftedSymbolPow L k σ (PlaneWaves.shiftedFreq κ m))
      (openImStrip (1 / 8)) := by
  have hz : ∀ κ ∈ openImStrip (1 / 8), 0 < (symbolSquare L k (PlaneWaves.shiftedFreq κ m) + 1).re :=
    fun κ hκ => by
      have := hre _ (shiftedFreq_mem_imStrip (openImStrip_subset_imStrip le_rfl hκ) m)
      linarith
  have hd : Differentiable ℂ fun κ => symbolSquare L k (PlaneWaves.shiftedFreq κ m) + 1 :=
    ((differentiable_symbolSquare L k).comp (differentiable_shiftedFreq m)).add_const 1
  have h : DifferentiableOn ℂ
      (fun κ => (symbolSquare L k (PlaneWaves.shiftedFreq κ m) + 1) ^ (σ : ℂ))
      (openImStrip (1 / 8)) := fun κ hκ =>
    ((hd κ).cpow (differentiableAt_const _) (Or.inl (hz κ hκ))).differentiableWithinAt
  exact h.congr fun κ hκ => principalRpow_eq_cpow σ (hz κ hκ)
end Powers
section Generic
open Classical
theorem pauliFamily_sum_injective {c c' : Fin 3 → ℂ}
    (h : ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a =
      ∑ a, c' a • Matrices.ComplexMatrix2.pauliFamily a) : c = c' := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_sum_injective <;> assumption
variable {P : Type} (f : (Fin 4 → ℤ) → P → P) (pos : P → InfiniteLattice.AmbientSpace) (w : ℝ)
abbrev colourPairData : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × P) (fun n ι => (ι.1, f n ι.2)) (fun ι => pos ι.2) w
def colourPairClass (ι : Fin 3 × P) : (colourPairData f pos w).UnitQuot :=
  (colourPairData f pos w).mkQuot 1 ι
def quotColour : (colourPairData f pos w).UnitQuot → Fin 3 :=
  Quot.lift (fun ι : Fin 3 × P => ι.1) (by rintro ⟨a, y⟩ _ ⟨n, rfl⟩; rfl)
def quotRecolour (b : Fin 3) : (colourPairData f pos w).UnitQuot → (colourPairData f pos w).UnitQuot :=
  Quot.map (fun ι : Fin 3 × P => (b, ι.2)) (by rintro ⟨a, y⟩ _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)
theorem colourPairClass_colour_eq {a a' : Fin 3} {z y : P}
    (h : colourPairClass f pos w (a', z) = colourPairClass f pos w (a, y)) : a' = a :=
  congrArg (quotColour f pos w) h
theorem colourPairClass_recolour (a b : Fin 3) {z y : P}
    (h : colourPairClass f pos w (a, z) = colourPairClass f pos w (a, y)) :
    colourPairClass f pos w (b, z) = colourPairClass f pos w (b, y) :=
  congrArg (quotRecolour f pos w b) h
theorem single_colourPairClass (a a' : Fin 3) (y₀ z : P) :
    (Pi.single (colourPairClass f pos w (a, y₀)) (1 : ℂ) : (colourPairData f pos w).UnitQuot → ℂ)
        (colourPairClass f pos w (a', z)) =
      if a' = a then
        (if colourPairClass f pos w (0, z) = colourPairClass f pos w (0, y₀) then 1 else 0)
      else 0 := by
  by_cases h : a' = a
  · subst h
    rw [if_pos rfl, Pi.single_apply]
    by_cases h' : colourPairClass f pos w (0, z) = colourPairClass f pos w (0, y₀)
    · rw [if_pos h', if_pos (colourPairClass_recolour f pos w 0 a' h')]
    · rw [if_neg h', if_neg fun e => h' (colourPairClass_recolour f pos w a' 0 e)]
  · rw [if_neg h, Pi.single_apply, if_neg fun e => h (colourPairClass_colour_eq f pos w e)]
variable (L k : ℕ) {D : Type} (rd : FullSpace.Vertex L k 0 → D → P)
def labelledCoeff (l : (colourPairData f pos w).UnitQuot → ℂ) (d : D) (m : Fin 4 → ℤ) :
    Matrices.ComplexMatrix2 :=
  fourierCoeff L k
    (fun x => ofPauliCoeffs (fun ι => l ((colourPairData f pos w).mkQuot 1 ι)) (rd x d)) m
def unitCoeff (d : D) (m : Fin 4 → ℤ) (y₀ : P) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ c : VertexClass L k,
    fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
      (if colourPairClass f pos w (0, rd (Quot.out c) d) = colourPairClass f pos w (0, y₀)
        then 1 else 0)
theorem ofPauliCoeffs_single (a : Fin 3) (y₀ z : P) :
    ofPauliCoeffs (fun ι => (Pi.single (colourPairClass f pos w (a, y₀)) (1 : ℂ) :
        (colourPairData f pos w).UnitQuot → ℂ) ((colourPairData f pos w).mkQuot 1 ι)) z =
      (if colourPairClass f pos w (0, z) = colourPairClass f pos w (0, y₀) then (1 : ℂ) else 0) •
        Matrices.ComplexMatrix2.pauliFamily a := by
  simp only [ofPauliCoeffs]
  have h : ∀ a' : Fin 3, (Pi.single (colourPairClass f pos w (a, y₀)) (1 : ℂ) :
        (colourPairData f pos w).UnitQuot → ℂ) ((colourPairData f pos w).mkQuot 1 (a', z)) •
          Matrices.ComplexMatrix2.pauliFamily a' =
      if a' = a then
        (if colourPairClass f pos w (0, z) = colourPairClass f pos w (0, y₀) then (1 : ℂ) else 0) •
          Matrices.ComplexMatrix2.pauliFamily a' else 0 := fun a' => by
    refine (congrArg (fun c : ℂ => c • Matrices.ComplexMatrix2.pauliFamily a')
      (single_colourPairClass f pos w a a' y₀ z)).trans ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp
theorem labelledCoeff_single (a : Fin 3) (y₀ : P) (d : D) (m : Fin 4 → ℤ) :
    labelledCoeff f pos w L k rd (Pi.single (colourPairClass f pos w (a, y₀)) 1) d m =
      unitCoeff f pos w L k rd d m y₀ • Matrices.ComplexMatrix2.pauliFamily a := by
  simp only [labelledCoeff, PlaneWaves.fourierCoeff, unitCoeff, ofPauliCoeffs_single]
  rw [mul_smul, finsum_smul]
  simp only [smul_smul]
variable {f pos w L k rd}
theorem apply_single_colourPairClass
    (hexp : ∀ (l : (colourPairData f pos w).UnitQuot → ℂ) (d : D) (x : FullSpace.Vertex L k 0),
      ofPauliCoeffs (fun ι => l ((colourPairData f pos w).mkQuot 1 ι)) (rd x d) =
        ∑ m ∈ freqBox L k, integerWave m x • labelledCoeff f pos w L k rd l d m)
    (A : QuotHom (colourPairData f pos w) (colourPairData f pos w)) (t : (Fin 4 → ℤ) → ℂ)
    (hA : ∀ l d, ∀ m ∈ freqBox L k, labelledCoeff f pos w L k rd (A l) d m =
      t m • labelledCoeff f pos w L k rd l d m)
    (a a' : Fin 3) (x : FullSpace.Vertex L k 0) (d : D) (y₀ : P) :
    A (Pi.single (colourPairClass f pos w (a, y₀)) 1) (colourPairClass f pos w (a', rd x d)) =
      if a' = a then ∑ m ∈ freqBox L k,
        t m * (integerWave m x * unitCoeff f pos w L k rd d m y₀) else 0 := by
  set S : ℂ := ∑ m ∈ freqBox L k,
    t m * (integerWave m x * unitCoeff f pos w L k rd d m y₀) with hS
  have h := hexp (A (Pi.single (colourPairClass f pos w (a, y₀)) 1)) d x
  have h2 : ∑ m ∈ freqBox L k, integerWave m x • labelledCoeff f pos w L k rd
      (A (Pi.single (colourPairClass f pos w (a, y₀)) 1)) d m =
        S • Matrices.ComplexMatrix2.pauliFamily a := by
    rw [hS, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hA _ _ m hm, labelledCoeff_single, smul_smul, smul_smul]
    congr 1
    ring
  rw [h2] at h
  have h3 : S • Matrices.ComplexMatrix2.pauliFamily a =
      ∑ b, (if b = a then S else 0) • Matrices.ComplexMatrix2.pauliFamily b := by
    simp
  rw [h3] at h
  have := pauliFamily_sum_injective (c := fun b => A (Pi.single (colourPairClass f pos w (a, y₀)) 1)
    ((colourPairData f pos w).mkQuot 1 (b, rd x d))) (c' := fun b => if b = a then S else 0) h
  exact congrFun this a'
def waveEntry (hcover : ∀ y : P, ∃ x : FullSpace.Vertex L k 0, ∃ d : D, y = rd x d) (y y₀ : P)
    (m : Fin 4 → ℤ) : ℂ :=
  integerWave m (hcover y).choose *
    unitCoeff f pos w L k rd (hcover y).choose_spec.choose m y₀
theorem linearMapEntry_colourPairClass
    (hexp : ∀ (l : (colourPairData f pos w).UnitQuot → ℂ) (d : D) (x : FullSpace.Vertex L k 0),
      ofPauliCoeffs (fun ι => l ((colourPairData f pos w).mkQuot 1 ι)) (rd x d) =
        ∑ m ∈ freqBox L k, integerWave m x • labelledCoeff f pos w L k rd l d m)
    (hcover : ∀ y : P, ∃ x : FullSpace.Vertex L k 0, ∃ d : D, y = rd x d)
    (A : QuotHom (colourPairData f pos w) (colourPairData f pos w)) (t : (Fin 4 → ℤ) → ℂ)
    (hA : ∀ l d, ∀ m ∈ freqBox L k, labelledCoeff f pos w L k rd (A l) d m =
      t m • labelledCoeff f pos w L k rd l d m)
    (a a' : Fin 3) (y y₀ : P) :
    linearMapEntry A (colourPairClass f pos w (a', y)) (colourPairClass f pos w (a, y₀)) =
      if a' = a then ∑ m ∈ freqBox L k,
        t m * waveEntry (f := f) (pos := pos) (w := w) hcover y y₀ m else 0 := by
  have hy := (hcover y).choose_spec.choose_spec
  have := apply_single_colourPairClass hexp A t hA a a' (hcover y).choose
    (hcover y).choose_spec.choose y₀
  rw [← hy] at this
  exact this
end Generic
section Abstract
open Classical
open PeriodicOperators.SymbolCalculus
theorem linearMapEntry_ext {J J' : Type} [Finite J] {A B : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry A = linearMapEntry B) : A = B := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
structure MultiplierFamily (L k : ℕ) (I : PeriodicData)
    (Mult : ((Fin 4 → ℂ) → ℂ) → (Fin 4 → ℂ) → QuotHom I I → Prop)
    (mul : ((Fin 4 → ℂ) → ℂ) → (Fin 4 → ℂ) → QuotHom I I) : Prop where
  isPeriodic : IsPeriodic I
  facts : ∀ υ : ℝ, 0 < υ → ∀ t : (Fin 4 → ℂ) → ℂ,
    (∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q) →
      MultiplierMatrixFacts I (Mult t) (mul t) υ t
  comp : ∀ t t' κ A B, Mult t κ A → Mult t' κ B → Mult (fun q => t q * t' q) κ (A.comp B)
  congr : ∀ t t' κ A,
    (∀ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) = t' (PlaneWaves.shiftedFreq κ m)) →
    Mult t κ A → Mult t' κ A
  one : ∀ κ, Mult (fun _ => 1) κ LinearMap.id
  entries : ∃ W : I.UnitQuot → I.UnitQuot → (Fin 4 → ℤ) → ℂ, ∀ t κ A, Mult t κ A → ∀ c' c,
    linearMapEntry A c' c = ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * W c' c m
variable {L k : ℕ} {I : PeriodicData}
  {Mult : ((Fin 4 → ℂ) → ℂ) → (Fin 4 → ℂ) → QuotHom I I → Prop}
  {mul : ((Fin 4 → ℂ) → ℂ) → (Fin 4 → ℂ) → QuotHom I I}
theorem MultiplierFamily.scales (hM : MultiplierFamily L k I Mult mul) {t : (Fin 4 → ℂ) → ℂ}
    (ht : ∀ q (e : Fin 4 → ℤ), t (periodShift L k q e) = t q) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ openImStrip (1 / 4)) : Mult t κ (mul t κ) :=
  ((hM.facts (1 / 4) (by norm_num) t fun q _ e => ht q e).scales_unique κ hκ).1
theorem MultiplierFamily.eq_mul (hM : MultiplierFamily L k I Mult mul) {t : (Fin 4 → ℂ) → ℂ}
    (ht : ∀ q (e : Fin 4 → ℤ), t (periodShift L k q e) = t q) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ openImStrip (1 / 4)) {A : QuotHom I I} (hA : Mult t κ A) : A = mul t κ :=
  ((hM.facts (1 / 4) (by norm_num) t fun q _ e => ht q e).scales_unique κ hκ).2 A hA
theorem MultiplierFamily.eq_id (hM : MultiplierFamily L k I Mult mul) {t : (Fin 4 → ℂ) → ℂ}
    {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip (1 / 4)) {A : QuotHom I I} (hA : Mult t κ A)
    (h1 : ∀ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) = 1) : A = LinearMap.id :=
  (hM.eq_mul (fun _ _ => rfl) hκ (hM.congr t (fun _ => 1) κ A h1 hA)).trans
    (hM.eq_mul (fun _ _ => rfl) hκ (hM.one κ)).symm
theorem MultiplierFamily.differentiableOn_entry (hM : MultiplierFamily L k I Mult mul)
    {t : (Fin 4 → ℂ) → ℂ} {O : Set (Fin 4 → ℂ)} (hO : ∀ κ ∈ O, Mult t κ (mul t κ))
    (ht : ∀ m ∈ freqBox L k, DifferentiableOn ℂ (fun κ => t (PlaneWaves.shiftedFreq κ m)) O)
    (c' c : I.UnitQuot) : DifferentiableOn ℂ (fun κ => linearMapEntry (mul t κ) c' c) O := by
  obtain ⟨W, hW⟩ := hM.entries
  have h : DifferentiableOn ℂ
      (fun κ => ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * W c' c m) O :=
    DifferentiableOn.fun_sum fun m hm => (ht m hm).mul_const _
  exact h.congr fun κ hκ => hW t κ _ (hO κ hκ) c' c
theorem MultiplierFamily.boundedOn_entries (hM : MultiplierFamily L k I Mult mul)
    {t : (Fin 4 → ℂ) → ℂ} {S : Set (Fin 4 → ℂ)} {C : ℝ} (hS : ∀ κ ∈ S, Mult t κ (mul t κ))
    (ht : ∀ κ ∈ S, ∀ m ∈ freqBox L k, ‖t (PlaneWaves.shiftedFreq κ m)‖ ≤ C) :
    QuotHomFamilyBoundedOn S (mul t) := by
  obtain ⟨W, hW⟩ := hM.entries
  intro e
  refine ⟨∑ m ∈ freqBox L k, C * ‖W e.1 e.2 m‖, fun κ hκ => ?_⟩
  change ‖linearMapEntry (mul t κ) e.1 e.2‖ ≤ _
  rw [hW t κ _ (hS κ hκ)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ht κ hκ m hm) (norm_nonneg _)
theorem matFunKernel_congr {I I' : PeriodicData} {M M' : (Fin 4 → ℂ) → QuotHom I I'}
    (h : ∀ κ : InfiniteLattice.AmbientSpace, M (toComplexVec κ) = M' (toComplexVec κ)) :
    matFunKernel I I' M = matFunKernel I I' M' := by
  funext ι' ι
  simp only [matFunKernel]
  congr 1
  funext κ
  simp only [matFunIntegrand, h]
theorem quotHomInverse_eq {A B : QuotHom I I} (h1 : A.comp B = LinearMap.id)
    (h2 : B.comp A = LinearMap.id) : quotHomInverse A = B := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.quotHomInverse_eq_of_comp <;> assumption
theorem realDualPoints_subset_openImStrip {υ : ℝ} (hυ : 0 < υ) : realDualPoints ⊆ openImStrip υ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.realDualPoints_subset_openImStrip <;> assumption
theorem neg_mem_realDualPoints {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) : -κ ∈ realDualPoints :=
  fun j => by
    have : (κ j).im = 0 := hκ j
    simp [this]
theorem powerMatrixFacts_of_multipliers (hM : MultiplierFamily L k I Mult mul) (hF : SymbolFormulas L k)
    (hre : ∀ q ∈ imStrip (1 / 8), 9 / 10 ≤ (symbolSquare L k q + 1).re)
    {C : ℝ} (hbd : ∀ q ∈ imStrip (1 / 8), ‖symbolSquare L k q + 1‖ ≤ C)
    (hS : StripSymbols.Claim) (hCS : SymbolCalculus.Claim)
    (hId : IdKernelFacts.Claim)
    (K : I.Carrier → I.Carrier → ℂ) (hK : IsPeriodicKernel I I K)
    (hKf : SymbolSummableOn I I K Set.univ)
    (hKm : ∀ κ, Mult (symbolSquare L k) κ (symbolHom I I K κ)) :
    PowerMatrixFacts I (fun σ κ A => Mult (shiftedSymbolPow L k σ) κ A)
      (fun σ κ => mul (shiftedSymbolPow L k σ) κ) (fun ι' ι => K ι' ι + idKernel I ι' ι) := by
  have hI := hM.isPeriodic
  have : Finite I.UnitQuot := hI.finite_quot
  obtain ⟨hi1, -, -, -⟩ := hS.1 (1 / 8) (by norm_num)
  have per : ∀ σ q (e : Fin 4 → ℤ),
      shiftedSymbolPow L k σ (periodShift L k q e) = shiftedSymbolPow L k σ q :=
    fun σ q e => shiftedSymbolPow_periodShift hF σ q e
  have s8 : imStrip (1 / 8) ⊆ openImStrip (1 / 4) := imStrip_subset_openImStrip (by norm_num)
  have s9 : imStrip (1 / 9) ⊆ openImStrip (1 / 8) := imStrip_subset_openImStrip (by norm_num)
  have o8 : openImStrip (1 / 8) ⊆ imStrip (1 / 8) := openImStrip_subset_imStrip le_rfl
  have mulS : ∀ σ κ, κ ∈ openImStrip (1 / 4) →
      Mult (shiftedSymbolPow L k σ) κ (mul (shiftedSymbolPow L k σ) κ) :=
    fun σ κ hκ => hM.scales (per σ) hκ
  have zpos : ∀ κ, κ ∈ imStrip (1 / 8) → ∀ m,
      0 < (symbolSquare L k (PlaneWaves.shiftedFreq κ m) + 1).re :=
    fun κ hκ m => by
      have := hre _ (shiftedFreq_mem_imStrip hκ m)
      linarith
  have holE : ∀ σ c' c, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (openImStrip (1 / 8))
      fun κ _ => linearMapEntry (mul (shiftedSymbolPow L k σ) κ) c' c := fun σ c' c =>
    isHolomorphicIn_of_differentiableOn (isOpen_openImStrip _)
      (hM.differentiableOn_entry (fun κ hκ => mulS σ κ (s8 (o8 hκ)))
        (fun m _ => differentiableOn_shiftedSymbolPow hre σ m) c' c)
  have bdd : ∀ σ : ℝ, QuotHomFamilyBoundedOn (imStrip (1 / 8)) (mul (shiftedSymbolPow L k σ)) :=
    fun σ =>
    hM.boundedOn_entries (C := (9 / 10 : ℝ) ^ σ + C ^ σ) (fun κ hκ => mulS σ κ (s8 hκ))
      (fun κ hκ m _ => by
        have hq := shiftedFreq_mem_imStrip hκ m
        rw [shiftedSymbolPow, norm_principalRpow]
        have h1 := (hre _ hq).trans (Complex.re_le_norm _)
        have h2 := hbd _ hq
        exact rpow_le_rpow_add_rpow (by norm_num) (by linarith [h1.trans h2]) h1 h2)
  have quasi : ∀ σ, IsQuasiPeriodic (openImStrip (1 / 4)) (mul (shiftedSymbolPow L k σ)) :=
    fun σ => (hM.facts (1 / 4) (by norm_num) _ fun q _ e => per σ q e).quasiPeriodic
  have matfn : ∀ σ, IsStripSymbol I I (1 / 9) (mul (shiftedSymbolPow L k σ)) := fun σ =>
    ⟨⟨openImStrip (1 / 8), isOpen_openImStrip _, s9, holE σ⟩,
      fun e => let ⟨B, hB⟩ := bdd σ e; ⟨B, fun κ hκ => hB κ (o8 (s9 hκ))⟩,
      fun e κ hκ => quasi σ e κ (s8 (o8 (s9 hκ)))⟩
  obtain ⟨-, -, -, -, -, -, hυ, -, -⟩ := hCS I I hI hI
  obtain ⟨-, hker, -, hconst, -⟩ := hυ (1 / 9) (by norm_num)
  have KT := fun σ => hker _ (matfn σ)
  obtain ⟨hform, hfacts, -, -⟩ := hS.2.1 I I hI hI
  have hpos0 : (0 : Fin 4 → ℂ) ∈ realDualPoints := fun j => by simp
  have own : ∀ σ, kernelTranspose I I (matFunKernel I I (mul (shiftedSymbolPow L k σ))) =
      matFunKernel I I (mul (shiftedSymbolPow L k σ)) := by
    intro σ
    obtain ⟨pT, sT⟩ := (KT σ).isPeriodicKernel
    have key : ∀ κ ∈ realDualPoints,
        IsPeriodicKernel I I (kernelTranspose I I
          (matFunKernel I I (mul (shiftedSymbolPow L k σ)))) ∧
        SymbolSummableAt I I (kernelTranspose I I
          (matFunKernel I I (mul (shiftedSymbolPow L k σ)))) κ ∧
        symbolHom I I (kernelTranspose I I
          (matFunKernel I I (mul (shiftedSymbolPow L k σ)))) κ =
          mul (shiftedSymbolPow L k σ) κ := by
      intro κ hκ
      obtain ⟨p, f, e⟩ := (hfacts _ (-κ) pT (sT.1 (-κ) (neg_mem_realDualPoints hκ))).transpose
      rw [neg_neg] at f e
      refine ⟨p, f, ?_⟩
      have h1 := (hM.facts (1 / 4) (by norm_num) _ fun q _ e => per σ q e).transpose_neg
        (fun q _ => shiftedSymbolPow_neg hF σ q) κ (realDualPoints_subset_openImStrip (by norm_num) hκ)
      rw [← h1]
      change linearMapOfEntries (quotSymbol I I _ κ) =
        linearMapOfEntries (wTranspose _ _ (linearMapEntry _))
      rw [e, ← sT.2 (-κ) (neg_mem_realDualPoints hκ)]
      change _ = linearMapOfEntries (wTranspose _ _ (linearMapEntry (linearMapOfEntries _)))
      rw [linearMapEntry_linearMapOfEntries]
      rfl
    exact (KT σ).unique _ (key 0 hpos0).1
      ⟨fun κ hκ => (key κ hκ).2.1, fun κ hκ => (key κ hκ).2.2⟩
  have prod : ∀ (σ₁ σ₂ : ℝ) (G : (Fin 4 → ℂ) → QuotHom I I),
      MatFunKernelProperties I I (1 / 9) G →
      (∀ κ ∈ realDualPoints,
        (mul (shiftedSymbolPow L k σ₁) κ).comp (mul (shiftedSymbolPow L k σ₂) κ) = G κ) →
      (∀ ι' ι, CompSummableAt (matFunKernel I I (mul (shiftedSymbolPow L k σ₁)))
        (matFunKernel I I (mul (shiftedSymbolPow L k σ₂))) ι' ι) ∧
      compKernel (matFunKernel I I (mul (shiftedSymbolPow L k σ₁)))
        (matFunKernel I I (mul (shiftedSymbolPow L k σ₂))) =
        matFunKernel I I G := by
    intro σ₁ σ₂ G hG h
    obtain ⟨p₁, s₁⟩ := (KT σ₁).isPeriodicKernel
    obtain ⟨p₂, s₂⟩ := (KT σ₂).isPeriodicKernel
    have pr := fun κ (hκ : κ ∈ realDualPoints) =>
      (hfacts _ κ p₁ (s₁.1 κ hκ)).comp I hI _ p₂ (s₂.1 κ hκ)
    refine ⟨(pr 0 hpos0).1, hG.unique _ (pr 0 hpos0).2.1
      ⟨fun κ hκ => (pr κ hκ).2.2.1, fun κ hκ => ?_⟩⟩
    rw [(pr κ hκ).2.2.2, s₁.2 κ hκ, s₂.2 κ hκ, h κ hκ]
  have hId' := hId I hI
  have idper : IsPeriodicKernel I I (idKernel I) := hId'.1
  have idform : SymbolSummableOn I I (idKernel I) Set.univ := hId'.2.2.1
  have idmat : ∀ κ, quotSymbol I I (idKernel I) κ = quotOne I :=
    hId'.2.2.2.2.1
  have unitId : linearMapOfEntries (quotOne I) = LinearMap.id := by
    refine linearMapEntry_ext ?_
    rw [linearMapEntry_linearMapOfEntries]
    funext c' c
    simp [linearMapEntry, quotOne, Pi.single_apply]
  have symId : ∀ κ, symbolHom I I (idKernel I) κ = LinearMap.id := fun κ => by
    change linearMapOfEntries (quotSymbol I I _ κ) = _
    rw [idmat, unitId]
  set P : I.Carrier → I.Carrier → ℂ := fun ι' ι => K ι' ι + idKernel I ι' ι with hPd
  have hcomb : StripSymbols.linCombKernel 1 1 K (idKernel I) = P := by
    funext ι' ι
    simp [StripSymbols.linCombKernel, hPd]
  have comb := fun κ => (hfacts K κ hK (hKf κ trivial)).linComb (idKernel I) idper
    (idform κ trivial) 1 1
  simp only [hcomb] at comb
  have hPper : IsPeriodicKernel I I P := (comb 0).1
  have hPform : ∀ κ, SymbolSummableAt I I P κ := fun κ => (comb κ).2.1
  have per1 : ∀ q (e : Fin 4 → ℤ), symbolSquare L k (periodShift L k q e) + 1 =
      symbolSquare L k q + 1 := fun q e => by rw [hF.symbolSquare_periodic]
  have mul1 : ∀ κ, κ ∈ openImStrip (1 / 4) →
      Mult (fun q => symbolSquare L k q + 1) κ (mul (fun q => symbolSquare L k q + 1) κ) :=
    fun κ hκ => hM.scales per1 hκ
  have symP : ∀ κ, κ ∈ openImStrip (1 / 4) →
      symbolHom I I P κ = mul (fun q => symbolSquare L k q + 1) κ := by
    intro κ hκ
    obtain ⟨W, hW⟩ := hM.entries
    refine linearMapEntry_ext ?_
    funext c' c
    rw [(comb κ).2.2, symId κ, hW _ κ _ (mul1 κ hκ)]
    have e1 := hW _ κ _ (hKm κ) c' c
    have e2 := hW _ κ _ (hM.one κ) c' c
    have e3 : linearMapEntry ((1 : ℂ) • symbolHom I I K κ + (1 : ℂ) • LinearMap.id) c' c =
        linearMapEntry (symbolHom I I K κ) c' c + linearMapEntry (LinearMap.id) c' c := by
      simp [linearMapEntry]
    rw [e3, e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have invL : ∀ κ, κ ∈ imStrip (1 / 8) → (mul (shiftedSymbolPow L k (-1)) κ).comp
      (mul (fun q => symbolSquare L k q + 1) κ) = LinearMap.id := fun κ hκ =>
    hM.eq_id (s8 hκ) (hM.comp _ _ κ _ _ (mulS _ κ (s8 hκ)) (mul1 κ (s8 hκ))) fun m _ =>
      principalRpow_neg_one_mul _ (zpos κ hκ m)
  have invR : ∀ κ, κ ∈ imStrip (1 / 8) → (mul (fun q => symbolSquare L k q + 1) κ).comp
      (mul (shiftedSymbolPow L k (-1)) κ) = LinearMap.id := fun κ hκ =>
    hM.eq_id (s8 hκ) (hM.comp _ _ κ _ _ (mul1 κ (s8 hκ)) (mulS _ κ (s8 hκ))) fun m _ => by
      rw [mul_comm]
      exact principalRpow_neg_one_mul _ (zpos κ hκ m)
  have hinv : ∀ κ ∈ StripSymbols.openStripInterior (1 / 8),
      IsInvertibleQuotHom (symbolHom I I P κ) := by
    intro κ hκ
    rw [hi1] at hκ
    have hκ8 := o8 hκ
    rw [symP κ (s8 hκ8)]
    intro g
    refine ⟨mul (shiftedSymbolPow L k (-1)) κ g, LinearMap.congr_fun (invR κ hκ8) g, fun f hf => ?_⟩
    have := LinearMap.congr_fun (invL κ hκ8) f
    simp only [LinearMap.comp_apply, hf, LinearMap.id_apply] at this
    exact this.symm
  have holP : QuotHomFamilyHolomorphicOn (n := 4) (StripSymbols.openStripInterior (1 / 8))
      (symbolHom I I P) := by
    rw [hi1]
    refine ⟨by norm_num, isOpen_openImStrip _, fun e => ?_⟩
    refine isHolomorphicIn_of_differentiableOn (isOpen_openImStrip _) ?_
    have h := hM.differentiableOn_entry (t := fun q => symbolSquare L k q + 1)
      (O := openImStrip (1 / 8)) (fun κ hκ => mul1 κ (s8 (o8 hκ)))
      (fun m _ => (((differentiable_symbolSquare L k).comp
        (differentiable_shiftedFreq m)).add_const 1).differentiableOn) e.1 e.2
    exact h.congr fun κ hκ => by
      change linearMapEntry (symbolHom I I P κ) e.1 e.2 = _
      rw [symP κ (s8 (o8 hκ))]
  obtain ⟨hinvReal, -, hf1, hf2, he1, he2, -, -⟩ := hS.2.2.2 I hI (1 / 8) (by norm_num) P hPper
    (fun κ _ => hPform κ) holP hinv
  have hInvEq : periodicInverse I P =
      matFunKernel I I (mul (shiftedSymbolPow L k (-1))) := by
    refine matFunKernel_congr fun κ => ?_
    have hκ : toComplexVec κ ∈ imStrip (1 / 8) :=
      o8 (realDualPoints_subset_openImStrip (by norm_num) fun j => by simp [toComplexVec])
    rw [symP _ (s8 hκ)]
    exact quotHomInverse_eq (invR _ hκ) (invL _ hκ)
  have rm8 : realDualPoints ⊆ imStrip (1 / 8) :=
    fun κ hκ => o8 (realDualPoints_subset_openImStrip (by norm_num) hκ)
  exact
    { scales_unique := fun σ _ κ hκ =>
        (hM.facts (1 / 4) (by norm_num) _ fun q _ e => per σ q e).scales_unique κ (s8 hκ)
      holomorphicOn := fun σ _ => by
        rw [hi1]
        exact ⟨by norm_num, isOpen_openImStrip _, fun e => holE σ e.1 e.2⟩
      boundedOn := fun σ _ => by
        rw [hi1]
        exact fun e => let ⟨B, hB⟩ := bdd σ e; ⟨B, fun κ hκ => hB κ (o8 hκ)⟩
      quasiPeriodic := fun σ _ e κ hκ => quasi σ e κ (s8 hκ)
      continuousOn := fun σ _ => (KT σ).realDualPoints_subset.2
      periodic := fun σ _ => (KT σ).isPeriodicKernel.1
      im_eq_zero := fun σ _ => (KT σ).im_eq_zero fun κ hκ =>
        (hM.facts (1 / 8) (by norm_num) _ fun q _ e => per σ q e).conj_entries
          (fun q _ => shiftedSymbolPow_neg hF σ q)
          (fun q hq => by
            have h := zpos q (o8 hq) 0
            have e0 : PlaneWaves.shiftedFreq q 0 = q := by
              funext μ
              simp [PlaneWaves.shiftedFreq]
            rw [e0] at h
            simp only [shiftedSymbolPow]
            rw [conj_principalRpow σ h, map_add, map_one, hF.conj_symbolSquare])
          κ (s9 hκ)
      transpose_eq := fun σ _ => own σ
      symbol_invertible := ⟨hPper, fun κ _ => hPform κ, hinvReal⟩
      inverse_eq := hInvEq
      inv_comp := by
        rw [← hInvEq]
        exact ⟨hf1, he1⟩
      comp_inv := by
        rw [← hInvEq]
        exact ⟨hf2, he2⟩
      invSqrt_comp_invSqrt := prod _ _ _ (KT (-1)) fun κ hκ =>
        hM.eq_mul (per _) (s8 (rm8 hκ))
          (hM.congr _ _ κ _ (fun m _ => principalRpow_neg_half_mul_self _ (zpos κ (rm8 hκ) m))
            (hM.comp _ _ κ _ _ (mulS _ κ (s8 (rm8 hκ))) (mulS _ κ (s8 (rm8 hκ)))))
      sqrt_comp_invSqrt := by
        have hG := hker _ hconst
        have h := prod (1 / 2) (-(1 / 2)) _ hG fun κ hκ => by
          rw [unitId]
          exact hM.eq_id (s8 (rm8 hκ))
            (hM.comp _ _ κ _ _ (mulS _ κ (s8 (rm8 hκ))) (mulS _ κ (s8 (rm8 hκ))))
            fun m _ => principalRpow_half_mul_neg_half _ (zpos κ (rm8 hκ) m)
        have h1 : idKernel I = matFunKernel I I (fun _ => linearMapOfEntries (quotOne I)) :=
          hG.unique _ idper ⟨fun κ _ => idform κ trivial, fun κ _ => by rw [symId, unitId]⟩
        rw [h1]
        exact h }
end Abstract
section Concrete
open Classical
variable {L k : ℕ}
theorem exists_entry_weights {P : Type} {f : (Fin 4 → ℤ) → P → P}
    {pos : P → InfiniteLattice.AmbientSpace} {w : ℝ}
    {Mult : ((Fin 4 → ℂ) → ℂ) → (Fin 4 → ℂ) →
      QuotHom (colourPairData f pos w) (colourPairData f pos w) → Prop}
    (E : P → P → (Fin 4 → ℤ) → ℂ)
    (h : ∀ t κ A, Mult t κ A → ∀ (a a' : Fin 3) (y y₀ : P),
      linearMapEntry A (colourPairClass f pos w (a', y)) (colourPairClass f pos w (a, y₀)) =
        if a' = a then ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * E y y₀ m else 0) :
    ∃ W : (colourPairData f pos w).UnitQuot → (colourPairData f pos w).UnitQuot → (Fin 4 → ℤ) → ℂ,
      ∀ t κ A, Mult t κ A → ∀ c' c,
        linearMapEntry A c' c = ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * W c' c m := by
  have hrep : ∀ c : (colourPairData f pos w).UnitQuot, ∃ ι : Fin 3 × P, colourPairClass f pos w ι = c :=
    fun c => Quot.exists_rep c
  choose rep hrep using hrep
  refine ⟨fun c' c m => if (rep c').1 = (rep c).1 then E (rep c').2 (rep c).2 m else 0,
    fun t κ A hA c' c => ?_⟩
  have e := h t κ A hA (rep c).1 (rep c').1 (rep c').2 (rep c).2
  have e1 : ((rep c').1, (rep c').2) = rep c' := rfl
  have e2 : ((rep c).1, (rep c).2) = rep c := rfl
  rw [e1, e2, hrep, hrep] at e
  rw [e]
  by_cases hc : (rep c').1 = (rep c).1
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [if_pos hc]
  · rw [if_neg hc]
    simp [hc]
theorem isColourTrivial_matFunKernel {P : Type} {f : (Fin 4 → ℤ) → P → P}
    {pos : P → InfiniteLattice.AmbientSpace} {w : ℝ}
    (M : (Fin 4 → ℂ) → QuotHom (colourPairData f pos w) (colourPairData f pos w))
    (S : InfiniteLattice.AmbientSpace → P → P → ℂ)
    (h : ∀ (κ : InfiniteLattice.AmbientSpace) (a a' : Fin 3) (y y₀ : P),
      linearMapEntry (M (toComplexVec κ)) (colourPairClass f pos w (a', y))
        (colourPairClass f pos w (a, y₀)) = if a' = a then S κ y y₀ else 0) :
    IsColourTrivial (σ := P) (σ' := P)
      (matFunKernel (colourPairData f pos w) (colourPairData f pos w) M) := by
  refine ⟨fun a a' y x hne => ?_, fun a a' y x => ?_⟩
  · have e : matFunIntegrand (colourPairData f pos w) (colourPairData f pos w) M (a', y) (a, x) =
        fun _ => 0 := by
      funext κ
      have e' := h κ a a' y x
      rw [if_neg hne] at e'
      simp only [matFunIntegrand, carrierEntry]
      refine (congrArg (· * _) e').trans ?_
      simp
    change torusAverage _ = 0
    rw [e]
    simp [torusAverage]
  · change torusAverage _ = torusAverage _
    congr 1
    funext κ
    have e₁ := h κ a a y x
    have e₂ := h κ a' a' y x
    rw [if_pos rfl] at e₁ e₂
    simp only [matFunIntegrand, carrierEntry]
    refine (congrArg (· * _) e₁).trans ?_
    exact (congrArg (· * _) e₂).symm
abbrev vertexShift (L k : ℕ) : (Fin 4 → ℤ) → FullSpace.Vertex L k 0 → FullSpace.Vertex L k 0 :=
  fun n x => FullSpace.vertexImage (intShift n) x
abbrev vertexPosition (L k : ℕ) : FullSpace.Vertex L k 0 → InfiniteLattice.AmbientSpace := fun x => x
abbrev edgeShift (L k : ℕ) : (Fin 4 → ℤ) → PeriodicOperators.PosEdge L k 0 →
    PeriodicOperators.PosEdge L k 0 :=
  fun n b => shiftEdge n b
abbrev edgePosition (L k : ℕ) : PeriodicOperators.PosEdge L k 0 → InfiniteLattice.AmbientSpace :=
  fun b => b.1.initial
abbrev vertexCoordinate (L k : ℕ) : FullSpace.Vertex L k 0 → Unit → FullSpace.Vertex L k 0 :=
  fun x _ => x
theorem vertexCover (L k : ℕ) (y : FullSpace.Vertex L k 0) :
    ∃ x : FullSpace.Vertex L k 0, ∃ d : Unit, y = vertexCoordinate L k x d := ⟨y, (), rfl⟩
theorem edgeCover (L k : ℕ) (y : PeriodicOperators.PosEdge L k 0) :
    ∃ x : FullSpace.Vertex L k 0, ∃ μ : Fin 4, y = edgeAt L k x μ := by
  obtain ⟨b, μ, hμ⟩ := y
  refine ⟨b.initial, μ, Subtype.ext ?_⟩
  refine InfiniteLattice.Link.ext rfl ?_
  change b.terminal = b.initial + InfiniteLattice.axisStep _ μ
  rw [← hμ]
  abel
def vertexWave (L k : ℕ) (y y₀ : FullSpace.Vertex L k 0) (m : Fin 4 → ℤ) : ℂ :=
  waveEntry (f := vertexShift L k) (pos := vertexPosition L k) (w := meshAt L k 0 ^ 4)
    (vertexCover L k) y y₀ m
def edgeWave (L k : ℕ) (y y₀ : PeriodicOperators.PosEdge L k 0) (m : Fin 4 → ℤ) : ℂ :=
  waveEntry (f := edgeShift L k) (pos := edgePosition L k) (w := meshAt L k 0 ^ 4)
    (edgeCover L k) y y₀ m
theorem vertex_entry (hC : PlaneWaveCalculus.VertexCoeffFacts L k)
    {t : (Fin 4 → ℂ) → ℂ} {κ : Fin 4 → ℂ}
    {A : QuotHom (colourVertices L k 0) (colourVertices L k 0)}
    (hA : ScalesVertexCoeffs L k t κ A) (a a' : Fin 3) (y y₀ : FullSpace.Vertex L k 0) :
    linearMapEntry A
        (colourPairClass (vertexShift L k) (vertexPosition L k) (meshAt L k 0 ^ 4) (a', y))
        (colourPairClass (vertexShift L k) (vertexPosition L k) (meshAt L k 0 ^ 4) (a, y₀)) =
      if a' = a then
        ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * vertexWave L k y y₀ m else 0 :=
  linearMapEntry_colourPairClass (f := vertexShift L k) (pos := vertexPosition L k)
    (w := meshAt L k 0 ^ 4) (rd := vertexCoordinate L k) (fun l _ x => hC.expansion l x)
    (vertexCover L k) A (fun m => t (PlaneWaves.shiftedFreq κ m)) (fun l _ m hm => hA l m hm)
    a a' y y₀
theorem edge_entry (hC : PlaneWaveCalculus.EdgeCoeffFacts L k)
    {t : (Fin 4 → ℂ) → ℂ} {κ : Fin 4 → ℂ}
    {A : QuotHom (colourEdges L k 0) (colourEdges L k 0)}
    (hA : ScalesEdgeCoeffs L k t κ A) (a a' : Fin 3) (y y₀ : PeriodicOperators.PosEdge L k 0) :
    linearMapEntry A
        (colourPairClass (edgeShift L k) (edgePosition L k) (meshAt L k 0 ^ 4) (a', y))
        (colourPairClass (edgeShift L k) (edgePosition L k) (meshAt L k 0 ^ 4) (a, y₀)) =
      if a' = a then
        ∑ m ∈ freqBox L k, t (PlaneWaves.shiftedFreq κ m) * edgeWave L k y y₀ m else 0 :=
  linearMapEntry_colourPairClass (f := edgeShift L k) (pos := edgePosition L k)
    (w := meshAt L k 0 ^ 4) (rd := edgeAt L k) (fun l μ x => hC.expansion l μ x)
    (edgeCover L k) A (fun m => t (PlaneWaves.shiftedFreq κ m)) (fun l μ m hm => hA l μ m hm)
    a a' y y₀
theorem vertexMultiplierFamily (hI : IsPeriodic (colourVertices L k 0))
    (hC : PlaneWaveCalculus.VertexCoeffFacts L k)
    (hF : ∀ υ : ℝ, 0 < υ → ∀ t : (Fin 4 → ℂ) → ℂ,
      (∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q) →
        MultiplierMatrixFacts (colourVertices L k 0) (ScalesVertexCoeffs L k t)
          (vertexFourierMultiplier L k t) υ t) :
    MultiplierFamily L k (colourVertices L k 0) (ScalesVertexCoeffs L k)
      (vertexFourierMultiplier L k) where
  isPeriodic := hI
  facts := hF
  comp := fun t t' κ A B hA hB l m hm => by
    change vertexFourierCoeff L k (A (B l)) m = _
    rw [hA _ m hm, hB _ m hm, smul_smul]
  congr := fun t t' κ A h hA l m hm => by
    rw [← h m hm]
    exact hA l m hm
  one := fun κ l m hm => by simp
  entries := exists_entry_weights (f := vertexShift L k) (pos := vertexPosition L k)
    (w := meshAt L k 0 ^ 4) (vertexWave L k) fun _ _ _ hA a a' y y₀ =>
      vertex_entry hC hA a a' y y₀
theorem edgeMultiplierFamily (hI : IsPeriodic (colourEdges L k 0))
    (hC : PlaneWaveCalculus.EdgeCoeffFacts L k)
    (hF : ∀ υ : ℝ, 0 < υ → ∀ t : (Fin 4 → ℂ) → ℂ,
      (∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q) →
        MultiplierMatrixFacts (colourEdges L k 0) (ScalesEdgeCoeffs L k t)
          (edgeFourierMultiplier L k t) υ t) :
    MultiplierFamily L k (colourEdges L k 0) (ScalesEdgeCoeffs L k) (edgeFourierMultiplier L k) where
  isPeriodic := hI
  facts := hF
  comp := fun t t' κ A B hA hB l μ m hm => by
    change edgeFourierCoeff L k (A (B l)) μ m = _
    rw [hA _ μ m hm, hB _ μ m hm, smul_smul]
  congr := fun t t' κ A h hA l μ m hm => by
    rw [← h m hm]
    exact hA l μ m hm
  one := fun κ l μ m hm => by simp
  entries := exists_entry_weights (f := edgeShift L k) (pos := edgePosition L k)
    (w := meshAt L k 0 ^ 4) (edgeWave L k) fun _ _ _ hA a a' y y₀ =>
      edge_entry hC hA a a' y y₀
end Concrete
theorem freeResolventRoots_holds (hPW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hE : PlaneWaves.PlaneWaveBounds.Claim)
    (hS : StripSymbols.Claim) (hCS : SymbolCalculus.Claim)
    (hId : IdKernelFacts.Claim) (hIx : TowerIndexSets.Claim)
    (hFO : FreeOperators.FreeOperatorsArePeriodic) : FreeResolventRoots := by
  intro L hL k hk
  obtain ⟨-, hSi, hBo, -, hF, hAct, -, -, -, hMt⟩ := hPW L hL k hk
  obtain ⟨hIs, hIb, -⟩ := hIx L hL k 0 (Nat.zero_le k)
  have hb := fun q (hq : q ∈ imStrip (1 / 8)) => symbolSquare_add_one_bounds hE hL hk hF hq
  have hre := fun q (hq : q ∈ imStrip (1 / 8)) => (hb q hq).1
  have hbd := fun q (hq : q ∈ imStrip (1 / 8)) => (hb q hq).2
  have mS := vertexMultiplierFamily hIs hSi fun υ hυ t ht => (hMt υ hυ t ht).1
  have mB := edgeMultiplierFamily hIb hBo fun υ hυ t ht => (hMt υ hυ t ht).2.1
  have hOp := (hFO.2 L hL k hk).2
  obtain ⟨hi1, -, -, -⟩ := hS.1 (1 / 8) (by norm_num)
  have fS := powerMatrixFacts_of_multipliers mS hF hre hbd hS hCS hId _ hOp.Delta.1
    (fun κ _ => ((hS.2.1 _ _ hIs hIs).1.finiteRange _ hOp.Delta.1 hOp.Delta.2.1) κ trivial)
    hAct.Delta
  have fB := powerMatrixFacts_of_multipliers mB hF hre hbd hS hCS hId _ hOp.K.1
    (fun κ _ => ((hS.2.1 _ _ hIb hIb).1.finiteRange _ hOp.K.1 hOp.K.2.1) κ trivial)
    hAct.K
  have real8 : ∀ κ : InfiniteLattice.AmbientSpace, toComplexVec κ ∈ imStrip (1 / 8) :=
    fun κ μ => by simp [toComplexVec]
  refine ⟨fun κ hκ m _ => hre _ (shiftedFreq_mem_imStrip hκ m),
    fun z hz => ⟨_, isRightHalfPlaneArg_arg hz, fun φ h => eq_arg_of_isRightHalfPlaneArg hz h⟩,
    ⟨openImStrip (1 / 8), isOpen_openImStrip _, imStrip_subset_openImStrip (by norm_num),
      by rw [hi1]⟩, fB, fS, fun σ hσ => ?_, fun σ hσ => ?_⟩
  · exact isColourTrivial_matFunKernel (f := edgeShift L k) (pos := edgePosition L k)
      (w := meshAt L k 0 ^ 4) (edgePowMatrix L k σ) _ fun κ a a' y y₀ =>
        edge_entry hBo ((fB.scales_unique σ hσ _ (real8 κ)).1) a a' y y₀
  · exact isColourTrivial_matFunKernel (f := vertexShift L k) (pos := vertexPosition L k)
      (w := meshAt L k 0 ^ 4) (vertexPowMatrix L k σ) _ fun κ a a' y y₀ =>
        vertex_entry hSi ((fS.scales_unique σ hσ _ (real8 κ)).1) a a' y y₀
end YangMills.Construction.Tower.FreeResolvents
end
