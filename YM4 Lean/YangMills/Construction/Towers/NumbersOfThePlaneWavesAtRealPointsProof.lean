import YangMills.Construction.Towers.ElementaryBoundsOfThePlaneWaveFunctionsProof
import YangMills.Construction.Towers.FormulasOfThePlaneWaveFunctions
import YangMills.Construction.Towers.NumbersOfThePlaneWavesAtRealPoints
import YangMills.Construction.Towers.RelationsOfThePlaneWaveFunctions
import YangMills.Construction.Towers.SumsOverThePointsOfThePlaneWaves
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.Tower.RealFrequencyFamily
open YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
open YangMills.Construction.PeriodicOperators (toComplexVec realDualPoints)
open YangMills.Construction.Tower.PlaneWaves
open YangMills.Construction.Coercivity (IsAdmissibleFamily)
open YangMills.Construction.Tower.PlaneWaveCalculus (periodShift meshC SymbolFormulas WeightRelations)
open YangMills.Construction.Tower.PlaneWaves.PlaneWaveBounds (complexPoint realSymbolSquare)
theorem exists_oddHalfWidth {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (k : ℕ) :
    ∃ N : ℕ, (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1 ∧
      freqWindow L k = Finset.Icc (-(N : ℤ)) N := by apply _root_.YangMills.Construction.Tower.PlaneWaves.PlaneWaveBounds.exists_halfWidth <;> assumption
theorem mem_freqBox_iff {L k N : ℕ} (hr : freqWindow L k = Finset.Icc (-(N : ℤ)) N)
    (m : Fin 4 → ℤ) : m ∈ freqBox L k ↔ ∀ ν, |m ν| ≤ (N : ℤ) := by
  simp only [freqBox, Fintype.mem_piFinset, hr, Finset.mem_Icc, abs_le]
theorem exists_symmetric_residue (N : ℕ) (a : ℤ) :
    ∃ r q : ℤ, a = r + (2 * (N : ℤ) + 1) * q ∧ |r| ≤ (N : ℤ) := by
  have hpos : (0 : ℤ) < 2 * (N : ℤ) + 1 := by positivity
  refine ⟨(a + N) % (2 * (N : ℤ) + 1) - N, (a + N) / (2 * (N : ℤ) + 1), ?_, ?_⟩
  · have := Int.emod_add_mul_ediv (a + N) (2 * (N : ℤ) + 1)
    linarith
  · have h1 := Int.emod_nonneg (a + N) hpos.ne'
    have h2 := Int.emod_lt_of_pos (a + N) hpos
    rw [abs_le]
    constructor <;> linarith
theorem exists_reduced_point {L k N : ℕ} (hinv : (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1)
    (hr : freqWindow L k = Finset.Icc (-(N : ℤ)) N) (x : Fin 4 → ℝ) :
    ∃ (c : Fin 4 → ℝ) (z : Fin 4 → ℤ), z ∈ freqBox L k ∧ (∀ ν, |c ν| ≤ Real.pi) ∧
      (∃ E : Fin 4 → ℤ, shiftedFreq (toComplexVec x) z = periodShift L k (toComplexVec c) E) ∧
      ∀ m ∈ freqBox L k, ∃ (P : Fin 4 → ℝ) (E : Fin 4 → ℤ),
        shiftedFreq (toComplexVec x) m = periodShift L k (toComplexVec P) E ∧
        (∀ ν, |P ν| ≤ Real.pi / finestMesh L k) ∧ (m ≠ z → ∃ ν, Real.pi ≤ |P ν|) := by
  have hpi := Real.pi_pos
  have hspc : (meshC L k)⁻¹ = 2 * (N : ℂ) + 1 := by
    have : (((finestMesh L k)⁻¹ : ℝ) : ℂ) = ((2 * (N : ℝ) + 1 : ℝ) : ℂ) := by rw [hinv]
    push_cast at this
    exact this
  have key : ∀ (y P : ℝ) (w E : ℤ),
      y + 2 * Real.pi * (w : ℝ) = P + 2 * Real.pi * (2 * (N : ℝ) + 1) * (E : ℝ) →
      (y : ℂ) + 2 * (Real.pi : ℂ) * (w : ℂ) =
        (P : ℂ) + 2 * (Real.pi : ℂ) / meshC L k * (E : ℂ) := by
    intro y P w E h
    have h' : ((y + 2 * Real.pi * (w : ℝ) : ℝ) : ℂ) =
        ((P + 2 * Real.pi * (2 * (N : ℝ) + 1) * (E : ℝ) : ℝ) : ℂ) := by rw [h]
    push_cast at h'
    rw [div_eq_mul_inv, hspc, h']
  set e : Fin 4 → ℤ := fun ν => round (x ν / (2 * Real.pi)) with he
  set c : Fin 4 → ℝ := fun ν => x ν - 2 * Real.pi * (e ν : ℝ) with hc
  have hcb : ∀ ν, |c ν| ≤ Real.pi := by
    intro ν
    have h1 := abs_sub_round (x ν / (2 * Real.pi))
    have h2 : c ν = 2 * Real.pi * (x ν / (2 * Real.pi) - (e ν : ℝ)) := by
      simp only [hc]
      field_simp
    rw [h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  choose z n hz hzb using fun ν => exists_symmetric_residue N (-e ν)
  have hzr : ∀ ν, ((e ν : ℝ) + (z ν : ℝ)) = -((2 * (N : ℝ) + 1) * (n ν : ℝ)) := by
    intro ν
    have h := hz ν
    have h' : ((-e ν : ℤ) : ℝ) = ((z ν + (2 * (N : ℤ) + 1) * n ν : ℤ) : ℝ) := by rw [← h]
    push_cast at h'
    linarith
  refine ⟨c, z, (mem_freqBox_iff hr z).2 hzb, hcb, ⟨fun ν => -n ν, ?_⟩, ?_⟩
  · funext ν
    simp only [shiftedFreq, periodShift, toComplexVec]
    have := key (x ν) (c ν) (z ν) (-n ν) (by
      have h := hzr ν
      simp only [hc]
      push_cast
      linear_combination 2 * Real.pi * h)
    exact this
  · intro m hm
    have hmb := (mem_freqBox_iff hr m).1 hm
    choose r n' hmr hrb using fun ν => exists_symmetric_residue N (m ν - z ν)
    have hmr' : ∀ ν, (m ν : ℝ) - (z ν : ℝ) = (r ν : ℝ) + (2 * (N : ℝ) + 1) * (n' ν : ℝ) := by
      intro ν
      have h := hmr ν
      have h' : ((m ν - z ν : ℤ) : ℝ) = ((r ν + (2 * (N : ℤ) + 1) * n' ν : ℤ) : ℝ) := by rw [← h]
      push_cast at h'
      linarith
    refine ⟨fun ν => c ν + 2 * Real.pi * (r ν : ℝ), fun ν => n' ν - n ν, ?_, ?_, ?_⟩
    · funext ν
      simp only [shiftedFreq, periodShift, toComplexVec]
      have := key (x ν) (c ν + 2 * Real.pi * (r ν : ℝ)) (m ν) (n' ν - n ν) (by
        have h := hzr ν
        have h2 := hmr' ν
        simp only [hc]
        push_cast
        linear_combination 2 * Real.pi * h + 2 * Real.pi * h2)
      exact this
    · intro ν
      have hrν : |(r ν : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hrb ν
      have h1 : |c ν + 2 * Real.pi * (r ν : ℝ)| ≤ Real.pi + 2 * Real.pi * (N : ℝ) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        have := hcb ν
        nlinarith
      have h2 : Real.pi / finestMesh L k = Real.pi + 2 * Real.pi * (N : ℝ) := by
        rw [div_eq_mul_inv, hinv]; ring
      rw [h2]
      exact h1
    · intro hne
      obtain ⟨ν, hν⟩ := Function.ne_iff.1 hne
      refine ⟨ν, ?_⟩
      have hr0 : r ν ≠ 0 := by
        intro h0
        have hd : (2 * (N : ℤ) + 1) ∣ (m ν - z ν) := ⟨n' ν, by rw [hmr ν, h0, zero_add]⟩
        have hlt : |m ν - z ν| < 2 * (N : ℤ) + 1 := by
          have h1 := abs_sub (m ν) (z ν)
          have h2 := hmb ν
          have h3 := hzb ν
          linarith
        have := Int.eq_zero_of_abs_lt_dvd hd hlt
        exact hν (by linarith)
      have hcν := abs_le.1 (hcb ν)
      rcases lt_or_gt_of_ne hr0 with h | h
      · have h1 : (r ν : ℝ) ≤ -1 := by exact_mod_cast (by omega : r ν ≤ -1)
        have h2 := neg_le_abs (c ν + 2 * Real.pi * (r ν : ℝ))
        nlinarith
      · have h1 : (1 : ℝ) ≤ (r ν : ℝ) := by exact_mod_cast (by omega : 1 ≤ r ν)
        have h2 := le_abs_self (c ν + 2 * Real.pi * (r ν : ℝ))
        nlinarith
theorem dirichletSum_add_period {L k : ℕ} (hη : meshC L k ≠ 0) (τ : ℂ) (n : ℤ) :
    dirichletSum L k (τ + 2 * (Real.pi : ℂ) / meshC L k * (n : ℂ)) = dirichletSum L k τ := by
  unfold dirichletSum
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) *
        (τ + 2 * (Real.pi : ℂ) / meshC L k * (n : ℂ)) =
      Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * τ +
        ((j * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hη' : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := hη
    simp only [meshC]
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem vertexWeight_periodShift {L k : ℕ} (hη : meshC L k ≠ 0) (q : Fin 4 → ℂ) (E : Fin 4 → ℤ) :
    PlaneWaves.vertexWeight L k (periodShift L k q E) = PlaneWaves.vertexWeight L k q := by
  unfold PlaneWaves.vertexWeight
  exact Finset.prod_congr rfl fun ν _ => dirichletSum_add_period hη (q ν) (E ν)
theorem norm_dirichletSum_ofReal_le_one {L k N : ℕ} (hinv : (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1)
    (hr : freqWindow L k = Finset.Icc (-(N : ℤ)) N) (τ : ℝ) :
    ‖dirichletSum L k (τ : ℂ)‖ ≤ 1 := by
  have hη : 0 < finestMesh L k := by
    have : 0 < (finestMesh L k)⁻¹ := by rw [hinv]; positivity
    exact inv_pos.mp this
  have h1 : ∀ j ∈ freqWindow L k,
      ‖Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * (τ : ℂ))‖ = 1 := by
    intro j _
    have : Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * (τ : ℂ) =
        ((finestMesh L k * (j : ℝ) * τ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcard : ((freqWindow L k).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [hr, Int.card_Icc]
    have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    rw [this]
    push_cast
    ring
  have h2 : ‖∑ j ∈ freqWindow L k,
      Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * (τ : ℂ))‖ ≤
        2 * (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_congr rfl h1]
    simp [hcard]
  unfold dirichletSum
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
  calc finestMesh L k * _ ≤ finestMesh L k * (2 * (N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left h2 hη.le
    _ = 1 := by rw [← hinv]; exact mul_inv_cancel₀ hη.ne'
theorem one_sub_mul_four_le {a b c d : ℝ} (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd1 : d ≤ 1) :
    1 - a * b * c * d ≤ (1 - a) + (1 - b) + (1 - c) + (1 - d) := by
  have two : ∀ {u w : ℝ}, u ≤ 1 → w ≤ 1 → 1 - u * w ≤ (1 - u) + (1 - w) := by
    intro u w hu hw
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hw)]
  have hab1 : a * b ≤ 1 := mul_le_one₀ ha1 hb hb1
  have habc1 : a * b * c ≤ 1 := mul_le_one₀ hab1 hc hc1
  have h1 := two ha1 hb1
  have h2 := two hab1 hc1
  have h3 := two habc1 hd1
  linarith
theorem isAdmissibleFamily_ofReal (hEB : PlaneWaveBounds.Claim)
    {L k : ℕ} (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hF : SymbolFormulas L k) (hR : WeightRelations L k)
    (hS : PlaneWaveSums.Claim) (x : Fin 4 → ℝ) :
    ∃ z : Fin 4 → ℤ, IsAdmissibleFamily ((2 / Real.pi) ^ 4) ((2 / Real.pi) ^ 5) (4 * Real.pi ^ 2)
      (Real.pi ^ 2 / 48) (freqBox L k) z (symbolSquares L k (toComplexVec x))
      (symbols L k (toComplexVec x)) (vertexWeights L k (toComplexVec x))
      (edgeWeights L k (toComplexVec x)) (unitSymbol (toComplexVec x)) := by
  have hpi := Real.pi_pos
  obtain ⟨N, hinv, hr⟩ := exists_oddHalfWidth hL k
  have hη : 0 < finestMesh L k := by
    have : 0 < (finestMesh L k)⁻¹ := by rw [hinv]; positivity
    exact inv_pos.mp this
  have hη1 : finestMesh L k ≤ 1 := by
    have h1 : finestMesh L k * (2 * (N : ℝ) + 1) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hη.ne'
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hηc : meshC L k ≠ 0 := by
    simp only [meshC]
    exact_mod_cast hη.ne'
  have hpoint : ∀ P : Fin 4 → ℝ, complexPoint P 0 = toComplexVec P := by
    intro P
    funext ν
    simp [complexPoint, toComplexVec]
  have hEB' := fun (P : Fin 4 → ℝ) (hP : ∀ ν, |P ν| ≤ Real.pi / finestMesh L k) =>
    hEB.1 L k hL hk P 0 hP (fun ν => by norm_num)
  have hreal : ∀ m : Fin 4 → ℤ, shiftedFreq (toComplexVec x) m =
      toComplexVec (fun ν => x ν + 2 * Real.pi * (m ν : ℝ)) := by
    intro m
    funext ν
    simp [shiftedFreq, toComplexVec]
  have hv : ∀ m : Fin 4 → ℤ, PlaneWaves.vertexWeight L k (shiftedFreq (toComplexVec x) m) =
      ((vertexWeights L k (toComplexVec x) m : ℝ) : ℂ) := by
    intro m
    apply Complex.ext
    · simp [vertexWeights]
    · rw [hreal]
      simpa using hR.vertexWeight_im _
  have hsq : ∀ (m : Fin 4 → ℤ) (P : Fin 4 → ℝ) (E : Fin 4 → ℤ),
      shiftedFreq (toComplexVec x) m = periodShift L k (toComplexVec P) E →
      (∀ ν, |P ν| ≤ Real.pi / finestMesh L k) →
      symbolSquares L k (toComplexVec x) m = realSymbolSquare L k P := by
    intro m P E hq hP
    unfold symbolSquares
    rw [hq, hF.symbolSquare_periodic, (hEB' P hP).1, Complex.ofReal_re]
  obtain ⟨c, z, hz, hc, ⟨E, hE⟩, hall⟩ := exists_reduced_point hinv hr x
  have hcbox : ∀ ν, |c ν| ≤ Real.pi / finestMesh L k := by
    intro ν
    refine (hc ν).trans ?_
    rw [le_div_iff₀ hη]
    nlinarith
  obtain ⟨-, hB1, hB2⟩ := hEB' c hcbox
  set t : Fin 4 → ℝ := fun ν => (dirichletSum L k (c ν : ℂ)).re with ht
  have hside : ∀ ν, (dirichletSum L k (c ν : ℂ)).im = 0 ∧ 2 / Real.pi ≤ t ν ∧
      1 - t ν ^ 2 ≤ 1 / 12 * c ν ^ 2 := by
    intro ν
    have := (hB2 ν).2.1 (hc ν) rfl
    have hp : complexPoint c 0 ν = (c ν : ℂ) := by rw [hpoint]; rfl
    rwa [hp] at this
  have htc : ∀ ν, dirichletSum L k (c ν : ℂ) = (t ν : ℂ) := fun ν =>
    Complex.ext (by simp [ht]) (by simpa using (hside ν).1)
  have ht0 : ∀ ν, 0 < t ν := fun ν => lt_of_lt_of_le (by positivity) (hside ν).2.1
  have ht1 : ∀ ν, t ν ^ 2 ≤ 1 := by
    intro ν
    have h1 := norm_dirichletSum_ofReal_le_one hinv hr (c ν)
    rw [htc, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 := ht0 ν
    rw [abs_of_pos h2] at h1
    nlinarith
  have hvz : vertexWeights L k (toComplexVec x) z = ∏ ν, t ν := by
    have h1 : PlaneWaves.vertexWeight L k (shiftedFreq (toComplexVec x) z) =
        ((∏ ν, t ν : ℝ) : ℂ) := by
      rw [hE, vertexWeight_periodShift hηc]
      unfold PlaneWaves.vertexWeight
      push_cast
      exact Finset.prod_congr rfl fun ν _ => htc ν
    unfold vertexWeights
    rw [h1, Complex.ofReal_re]
  have hprod : (2 / Real.pi) ^ 4 ≤ ∏ ν, t ν := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
      (f := fun _ => 2 / Real.pi) (g := t) (fun _ _ => by positivity)
      (fun ν _ => (hside ν).2.1)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hDz : symbolSquares L k (toComplexVec x) z = realSymbolSquare L k c :=
    hsq z c E hE hcbox
  have hd1 := hB1.1
  refine ⟨z,
    { mem := hz
      eq_normSq := ?_
      four_le := ?_
      le_bound := ?_
      site_lower := by rw [hvz]; exact hprod
      bond_lower := ?_
      site_sum_sq := ?_
      bond_sum_sq_le := fun μ => (hS L hL k hk x).1 μ
      deficit_le := ?_
      mul_eq := ?_ }⟩
  · intro m _
    have h1 := hF.symbolSquare_ofReal (fun ν => x ν + 2 * Real.pi * (m ν : ℝ))
    unfold symbolSquares symbols
    rw [hreal, h1, ← Complex.ofReal_sum, Complex.ofReal_re]
  · intro m hm hne
    obtain ⟨P, E', hq, hP, hgap⟩ := hall m hm
    obtain ⟨ν, hν⟩ := hgap hne
    rw [hsq m P E' hq hP]
    obtain ⟨-, hBP, -⟩ := hEB' P hP
    have h1 := (hBP.1 ν).1
    have h2 : 2 ≤ ‖forwardSymbol L k (toComplexVec P) ν‖ := by
      refine le_trans ?_ h1
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      nlinarith
    have h3 : ‖forwardSymbol L k (toComplexVec P) ν‖ ^ 2 ≤ realSymbolSquare L k P :=
      Finset.single_le_sum (f := fun ν => ‖forwardSymbol L k (toComplexVec P) ν‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ ν)
    nlinarith
  · rw [hDz]
    have h1 : ∀ ν ∈ (Finset.univ : Finset (Fin 4)),
        ‖forwardSymbol L k (toComplexVec c) ν‖ ^ 2 ≤ Real.pi ^ 2 := by
      intro ν _
      have h2 := (hd1 ν).2.trans (hc ν)
      have h3 := norm_nonneg (forwardSymbol L k (toComplexVec c) ν)
      nlinarith
    have := Finset.sum_le_sum h1
    simpa [realSymbolSquare] using this
  · intro μ
    have hq : shiftedFreq (toComplexVec x) z μ =
        ((x μ + 2 * Real.pi * (z μ : ℝ) : ℝ) : ℂ) := by
      rw [hreal]; rfl
    have hs : dirichletSum L k (shiftedFreq (toComplexVec x) z μ) = (t μ : ℂ) := by
      rw [hE, ← htc μ]
      exact dirichletSum_add_period hηc _ _
    have hexp : ‖Complex.exp (Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) *
        shiftedFreq (toComplexVec x) z μ / 2)‖ = 1 := by
      have : Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) *
          shiftedFreq (toComplexVec x) z μ / 2 =
          (((1 - finestMesh L k) * (x μ + 2 * Real.pi * (z μ : ℝ)) / 2 : ℝ) : ℂ) *
            Complex.I := by
        rw [hq]; push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hnorm : ‖edgeWeights L k (toComplexVec x) z μ‖ = t μ * ∏ ν, t ν := by
      unfold edgeWeights edgeWeight
      rw [hv z, hs, norm_mul, norm_mul, hexp, one_mul, Complex.norm_real, Complex.norm_real, hvz,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (ht0 μ),
        abs_of_pos (lt_of_lt_of_le (by positivity) hprod)]
    rw [hnorm, pow_succ, mul_comm]
    exact mul_le_mul (hside μ).2.1 hprod (by positivity) (ht0 μ).le
  · have h1 := (hS L hL k hk x).2
    have h2 : ((∑ m ∈ freqBox L k, vertexWeights L k (toComplexVec x) m ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      push_cast
      exact Finset.sum_congr rfl fun m _ => by rw [← hv m]; rfl
    exact_mod_cast h2
  · rw [hvz, hDz]
    have h1 : (∏ ν, t ν) ^ 2 = t 0 ^ 2 * t 1 ^ 2 * t 2 ^ 2 * t 3 ^ 2 := by
      rw [Fin.prod_univ_four]; ring
    have h2 := one_sub_mul_four_le (ht1 0) (sq_nonneg (t 1)) (ht1 1) (sq_nonneg (t 2)) (ht1 2)
      (ht1 3)
    have h3 : 4 / Real.pi ^ 2 * c 0 ^ 2 + 4 / Real.pi ^ 2 * c 1 ^ 2 + 4 / Real.pi ^ 2 * c 2 ^ 2 +
        4 / Real.pi ^ 2 * c 3 ^ 2 ≤ realSymbolSquare L k c := by
      have h4 : ∀ ν, 4 / Real.pi ^ 2 * c ν ^ 2 ≤ ‖forwardSymbol L k (toComplexVec c) ν‖ ^ 2 := by
        intro ν
        have h5 := (hd1 ν).1
        have h6 : (2 / Real.pi * |c ν|) ^ 2 ≤ ‖forwardSymbol L k (toComplexVec c) ν‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) h5 2
        rw [mul_pow, sq_abs, div_pow] at h6
        norm_num at h6
        exact h6
      unfold realSymbolSquare
      rw [Fin.sum_univ_four]
      linarith [h4 0, h4 1, h4 2, h4 3]
    have h7 : Real.pi ^ 2 / 48 * (4 / Real.pi ^ 2 * c 0 ^ 2 + 4 / Real.pi ^ 2 * c 1 ^ 2 +
        4 / Real.pi ^ 2 * c 2 ^ 2 + 4 / Real.pi ^ 2 * c 3 ^ 2) =
        1 / 12 * c 0 ^ 2 + 1 / 12 * c 1 ^ 2 + 1 / 12 * c 2 ^ 2 + 1 / 12 * c 3 ^ 2 := by
      field_simp
      ring
    have h8 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 48)
    rw [h7] at h8
    rw [h1]
    linarith [(hside 0).2.2, (hside 1).2.2, (hside 2).2.2, (hside 3).2.2]
  · intro m hm μ
    have h1 := hR.edgeWeight_mul_forwardSymbol (shiftedFreq (toComplexVec x) m) μ
    rw [hR.unitSymbol_shiftedFreq _ m hm, hv m] at h1
    exact h1
theorem familyBoundsHold_of_claims (hEB : PlaneWaveBounds.Claim)
    (hF : PlaneWaveSymbolFormulas.Holds)
    (hR : PlaneWaveCalculus.WeightRelationsHold)
    (hS : PlaneWaveSums.Claim) : FamilyBoundsHold := by
  intro L hL k hk κ hκ
  obtain ⟨x, rfl⟩ : ∃ x : Fin 4 → ℝ, κ = toComplexVec x := by
    refine ⟨fun ν => (κ ν).re, ?_⟩
    funext ν
    exact Complex.ext (by simp [toComplexVec]) (by simpa [toComplexVec] using hκ ν)
  exact isAdmissibleFamily_ofReal hEB hL hk (hF L hL k hk) (hR L hL k hk) hS x
end YangMills.Construction.Tower.RealFrequencyFamily
end
