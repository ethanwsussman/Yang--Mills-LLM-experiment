import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.RunningCouplingSlope.LogarithmsOfThePlainIterates
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfAnExponential
import YangMills.Construction.RunningCouplingSlope.PlainLengthAtAReversedBond
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanIterateLogs
open Tower
open Tower.TwoLevelMaps
open Matrices
variable {L n k j : ℕ} {ρ₁ C₁ : ℝ}
theorem bondFormSumAlong_add (A B : Edge L n k j → ComplexMatrix2) (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong (A + B) Γ =
      PeriodicLattice.bondFormSumAlong A Γ + PeriodicLattice.bondFormSumAlong B Γ := by
  induction Γ with
  | nil => simp [PeriodicLattice.bondFormSumAlong]
  | cons e l ih =>
    simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih]
    abel
theorem contourFormAverage_add {i : ℤ} (A B : Edge L n k j → ComplexMatrix2)
    (y : PeriodicLattice.Site L n i) (x : Vertex L n k j) :
    PeriodicLattice.contourFormAverage (A + B) y x =
      PeriodicLattice.contourFormAverage A y x + PeriodicLattice.contourFormAverage B y x := by
  simp only [PeriodicLattice.contourFormAverage, bondFormSumAlong_add, Finset.sum_add_distrib,
    smul_add]
theorem linearSmoothing_add (hfin : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite)
    (A B : Edge L n k j → ComplexMatrix2) :
    linearSmoothing L n k j (A + B) = linearSmoothing L n k j A + linearSmoothing L n k j B := by
  funext c
  change PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum (A + B) c =
    PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A c +
      PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c
  rw [← smul_add, PeriodicLattice.linearBlockSum, PeriodicLattice.linearBlockSum,
    PeriodicLattice.linearBlockSum, ← finsum_mem_add_distrib (hfin _) ]
  congr 1
  refine finsum_mem_congr rfl fun x _ => ?_
  simp only [contourFormAverage_add, bondFormSumAlong_add]
  abel
theorem norm_linearSmoothingBetween_le (hb : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n) {i l : ℕ}
    (h : i ≤ l) (hl : l ≤ k) (h1 : 1 ≤ l) (B : Edge L n k i → ComplexMatrix2)
    (hB : B ∈ complexEdgeForms L n k i)
    (β : ℝ) (hβ : 0 ≤ β) (hBβ : ∀ e, ‖B e‖ ≤ β) (e : Edge L n k l) :
    ‖linearSmoothingBetween L n k h B e‖ ≤ 5 * (L : ℝ) ^ (l - i) * β := by
  have R := ((hb L hL k hk).1 n hn).2.1 (l - i) l h1 (Nat.sub_le _ _) hl
  have aux : ∀ (i' : ℕ) (_ : i' = i) (hi' : i' ≤ l),
      (∀ B' ∈ complexEdgeForms L n k i', maxOperatorNorm (linearSmoothingBetween L n k hi' B') ≤
        5 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B') →
      maxOperatorNorm (linearSmoothingBetween L n k h B) ≤
        5 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
    intro i' hii hi' hp
    subst hii
    exact hp B hB
  have hs := aux (l - (l - i)) (by omega) (Nat.sub_le _ _) R.linearSmoothing_norm_le
  have hB2 : maxOperatorNorm B ≤ ENNReal.ofReal β :=
    iSup_le fun e => ENNReal.ofReal_le_ofReal (hBβ e)
  have h3 : ENNReal.ofReal ‖linearSmoothingBetween L n k h B e‖ ≤
      maxOperatorNorm (linearSmoothingBetween L n k h B) :=
    le_iSup (fun e => ENNReal.ofReal
      (ComplexMatrix2.operatorNorm (linearSmoothingBetween L n k h B e))) e
  have h4 : 5 * (L : ℝ≥0∞) ^ (l - i) * ENNReal.ofReal β =
      ENNReal.ofReal (5 * (L : ℝ) ^ (l - i) * β) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow (by positivity)]
    simp
  have h5 := h3.trans (hs.trans
    (by gcongr : _ ≤ 5 * (L : ℝ≥0∞) ^ (l - i) * ENNReal.ofReal β))
  rw [h4] at h5
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5
theorem xor_isPositivelyOriented_opposite
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (hj : j ≤ k)
    (e : Edge L n k j) :
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented ∧ e.opposite.opposite = e := by
  have h := (ho ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 e
  exact ⟨h.2.2.2.2.2, h.2.2.2.1⟩
theorem extendOddly_mem_complexEdgeForms
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2)
    (hf : ∀ e : Edge L n k j, e.IsPositivelyOriented → f e ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · simp only [extendOddly, if_pos he]
    exact hf e he
  · obtain ⟨hx, hr⟩ := xor_isPositivelyOriented_opposite ho hL hn hk hj e
    by_cases he : e.IsPositivelyOriented
    · have hnot : ¬ e.opposite.IsPositivelyOriented := by
        rcases hx with h | h
        · exact h.2
        · exact absurd he h.2
      simp only [extendOddly, if_pos he, if_neg hnot, hr]
    · have hp : e.opposite.IsPositivelyOriented := by
        rcases hx with h | h
        · exact absurd h.1 he
        · exact h.1
      simp only [extendOddly, if_neg he, if_pos hp, neg_neg]
def nextLog (A : Edge L n k j → ComplexMatrix2) : Edge L n k (j + 1) → ComplexMatrix2 :=
  extendOddly fun c => Complex.I⁻¹ •
    ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c)
theorem nextLog_spec (hE : ∀ n k j : ℕ, 0 < n → j < k →
      ∀ A ∈ complexEdgeForms L n k j, ∀ a : ℝ, 0 ≤ a → a ≤ ρ₁ →
      (∀ e, ComplexMatrix2.operatorNorm (A e) ≤ a) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ‖meanRadius (PeriodicLattice.expTwist A fun _ => 1) c - 1‖ ≤ C₁ * a ^ 2 ∧
        ∃ N ∈ ComplexMatrix2.traceless, ComplexMatrix2.operatorNorm N ≤ C₁ * a ^ 2 ∧
          normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c =
            ComplexMatrix2.matExp (Complex.I • (linearSmoothing L n k j A c + N)))
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlm : TwoLevelMaps.Statement)
    (hcf : PeriodicCoarseningStep.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (A : Edge L n k j → ComplexMatrix2) (hA : A ∈ complexEdgeForms L n k j) (a : ℝ) (ha : 0 ≤ a)
    (haρ : a ≤ ρ₁) (hAa : ∀ e, ‖A e‖ ≤ a) (hsmall : 5 * (L : ℝ) * a + C₁ * a ^ 2 < 1 / 2) :
    nextLog A ∈ complexEdgeForms L n k (j + 1) ∧
    (∀ e, ‖nextLog A e - linearSmoothing L n k j A e‖ ≤ C₁ * a ^ 2) ∧
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c =
        ComplexMatrix2.matExp (Complex.I • nextLog A c) := by
  have hk : 0 < k := by omega
  have hfacts := hcf L hL n k j hn hj
  have hQm := hfacts.linearSmoothing_mapsTo hA
  have hQb : ∀ e, ‖linearSmoothing L n k j A e‖ ≤ 5 * (L : ℝ) * a := by
    intro e
    have h1 := norm_linearSmoothingBetween_le hlm hL (by omega) hn (Nat.le_succ j) hj (by omega)
      A hA a ha hAa e
    have he : linearSmoothingBetween L n k (Nat.le_succ j) A = linearSmoothing L n k j A := by
      simp only [linearSmoothingBetween]
      rw [levelwiseComposition_succ _ (le_refl j), levelwiseComposition_self]
      rfl
    rw [he] at h1
    simpa using h1
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∃ N ∈ ComplexMatrix2.traceless, ‖N‖ ≤ C₁ * a ^ 2 ∧
      Complex.I⁻¹ • ComplexMatrix2.logSeries
          (normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c) =
        linearSmoothing L n k j A c + N ∧
      normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c =
        ComplexMatrix2.matExp (Complex.I • (linearSmoothing L n k j A c + N)) := by
    intro c hc
    obtain ⟨-, N, hNs, hNn, hNe⟩ := hE n k j hn hj A hA a ha haρ hAa c hc
    have hZ : ComplexMatrix2.operatorNorm (Complex.I • (linearSmoothing L n k j A c + N)) <
        Real.log 2 := by
      have h1 : ComplexMatrix2.operatorNorm (Complex.I • (linearSmoothing L n k j A c + N)) =
          ‖linearSmoothing L n k j A c + N‖ := by
        change ‖Complex.I • (linearSmoothing L n k j A c + N)‖ = _
        rw [norm_smul, Complex.norm_I, one_mul]
      rw [h1]
      have h2 : ‖linearSmoothing L n k j A c + N‖ ≤ 5 * (L : ℝ) * a + C₁ * a ^ 2 :=
        (norm_add_le _ _).trans (add_le_add (hQb c) hNn)
      linarith
    have hl := (hel.2.2.2.2.1 _ hZ).2
    refine ⟨N, hNs, hNn, ?_, hNe⟩
    rw [hNe, hl, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hval : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → nextLog A c =
      Complex.I⁻¹ • ComplexMatrix2.logSeries
        (normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c) := by
    intro c hc
    simp only [nextLog, extendOddly, if_pos hc]
  refine ⟨?_, ?_, ?_⟩
  · refine extendOddly_mem_complexEdgeForms ho hL hn hk (by omega) _ fun c hc => ?_
    obtain ⟨N, hNs, -, he, -⟩ := hpos c hc
    rw [he]
    exact Submodule.add_mem _ (hQm.1 c hc) hNs
  · intro e
    by_cases he : e.IsPositivelyOriented
    · obtain ⟨N, -, hNn, hq, -⟩ := hpos e he
      rw [hval e he, hq, add_sub_cancel_left]
      exact hNn
    · have hp := (xor_isPositivelyOriented_opposite ho hL hn hk (by omega) e).1
      have hp' : e.opposite.IsPositivelyOriented := by
        rcases hp with h | h
        · exact absurd h.1 he
        · exact h.1
      obtain ⟨N, -, hNn, hq, -⟩ := hpos _ hp'
      have e1 : nextLog A e = -(linearSmoothing L n k j A e.opposite + N) := by
        simp only [nextLog, extendOddly, if_neg he]
        rw [hq]
      have e2 : linearSmoothing L n k j A e.opposite = -linearSmoothing L n k j A e := hQm.2 e
      rw [e1, e2]
      have e3 : -(-linearSmoothing L n k j A e + N) - linearSmoothing L n k j A e = -N := by abel
      rw [e3, norm_neg]
      exact hNn
  · intro c hc
    obtain ⟨N, -, -, hq, hq'⟩ := hpos c hc
    rw [hval c hc, hq]
    exact hq'
def logSequence (A₀ : Edge L n k 0 → ComplexMatrix2) : (j : ℕ) → Edge L n k j → ComplexMatrix2
  | 0 => A₀
  | j + 1 => nextLog (logSequence A₀ j)
def quadraticRemainder (A₀ : Edge L n k 0 → ComplexMatrix2) (j : ℕ) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  logSequence A₀ (j + 1) - linearSmoothing L n k j (logSequence A₀ j)
theorem linearSmoothingBetween_succ {i l : ℕ} (h : i ≤ l) (h' : i ≤ l + 1)
    (B : Edge L n k i → ComplexMatrix2) :
    linearSmoothingBetween L n k h' B =
      linearSmoothing L n k l (linearSmoothingBetween L n k h B) := by
  simp only [linearSmoothingBetween]
  rw [levelwiseComposition_succ _ h h']
  rfl
theorem linearSmoothingBetween_self (i : ℕ) (B : Edge L n k i → ComplexMatrix2) :
    linearSmoothingBetween L n k (le_refl i) B = B := by
  simp only [linearSmoothingBetween]
  rw [levelwiseComposition_self]
  rfl
theorem logSequence_eq_sum (hfin : ∀ i < k, ∀ y : Vertex L n k (i + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
        Set (Vertex L n k i)).Finite)
    (A₀ : Edge L n k 0 → ComplexMatrix2) : ∀ j ≤ k, logSequence A₀ j =
      linearSmoothingBetween L n k (Nat.zero_le j) A₀ +
        ∑ i : Fin j, linearSmoothingBetween L n k (Nat.succ_le_of_lt i.2)
          (quadraticRemainder A₀ i) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact (linearSmoothingBetween_self 0 A₀).symm
  | succ j ih =>
    intro hj
    have hjk : j < k := by omega
    let Q : (Edge L n k j → ComplexMatrix2) →+ (Edge L n k (j + 1) → ComplexMatrix2) :=
      AddMonoidHom.mk' (linearSmoothing L n k j) (linearSmoothing_add (hfin j hjk))
    have e1 : logSequence A₀ (j + 1) =
        linearSmoothing L n k j (logSequence A₀ j) + quadraticRemainder A₀ j := by
      simp only [quadraticRemainder]
      abel
    have e2 : linearSmoothing L n k j (logSequence A₀ j) = Q (logSequence A₀ j) := rfl
    rw [e1, e2, ih (by omega), map_add, map_sum, Fin.sum_univ_castSucc]
    have e3 : Q (linearSmoothingBetween L n k (Nat.zero_le j) A₀) =
        linearSmoothingBetween L n k (Nat.zero_le (j + 1)) A₀ :=
      (linearSmoothingBetween_succ _ _ _).symm
    have e4 : ∀ i : Fin j,
        Q (linearSmoothingBetween L n k (Nat.succ_le_of_lt i.2) (quadraticRemainder A₀ i)) =
        linearSmoothingBetween L n k (Nat.succ_le_of_lt (Fin.castSucc i).2)
          (quadraticRemainder A₀ (Fin.castSucc i)) :=
      fun i => (linearSmoothingBetween_succ _ _ _).symm
    have e5 : linearSmoothingBetween L n k (Nat.succ_le_of_lt (Fin.last j).2)
        (quadraticRemainder A₀ (Fin.last j)) = quadraticRemainder A₀ j :=
      linearSmoothingBetween_self (j + 1) _
    rw [e3, e5]
    simp only [e4]
    abel
section MeshBounds
theorem meshAt_pos (hL : 0 < L) (i : ℕ) : 0 < meshAt L k i := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  exact zpow_pos this _
theorem meshAt_succ (hL : 0 < L) (i : ℕ) :
    meshAt L k (i + 1) = L * meshAt L k i := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshAt]
  push_cast
  have e : (i : ℤ) + 1 - (k : ℤ) = 1 + ((i : ℤ) - (k : ℤ)) := by ring
  rw [e, zpow_add₀ h, zpow_one]
theorem pow_mul_meshAt (hL : 0 < L) (i m : ℕ) :
    (L : ℝ) ^ m * meshAt L k i = meshAt L k (i + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, meshAt_succ hL, ← ih, pow_succ]
    ring
theorem meshAt_le_one (hL : 0 < L) {i : ℕ} (hi : i ≤ k) : meshAt L k i ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact zpow_le_one_of_nonpos₀ h1 (by omega)
theorem sum_meshAt_le (hL : 2 ≤ L) (j : ℕ) :
    ∑ i : Fin (j + 1), meshAt L k i ≤ 2 * meshAt L k j := by
  have hL0 : 0 < L := by omega
  induction j with
  | zero =>
    simp
    linarith [meshAt_pos (k := k) hL0 0]
  | succ j ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 := meshAt_succ (k := k) hL0 j
    have h2 := meshAt_pos (k := k) hL0 j
    have h3 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
end MeshBounds
theorem logSequence_bounds (hE : ∀ n k j : ℕ, 0 < n → j < k →
      ∀ A ∈ complexEdgeForms L n k j, ∀ a : ℝ, 0 ≤ a → a ≤ ρ₁ →
      (∀ e, ComplexMatrix2.operatorNorm (A e) ≤ a) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ‖meanRadius (PeriodicLattice.expTwist A fun _ => 1) c - 1‖ ≤ C₁ * a ^ 2 ∧
        ∃ N ∈ ComplexMatrix2.traceless, ComplexMatrix2.operatorNorm N ≤ C₁ * a ^ 2 ∧
          normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c =
            ComplexMatrix2.matExp (Complex.I • (linearSmoothing L n k j A c + N)))
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlm : TwoLevelMaps.Statement)
    (hcf : PeriodicCoarseningStep.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (hfin : ∀ i < k, ∀ y : Vertex L n k (i + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
        Set (Vertex L n k i)).Finite)
    (hC₁ : 0 ≤ C₁) (A₀ : Edge L n k 0 → ComplexMatrix2) (hA₀ : A₀ ∈ complexEdgeForms L n k 0)
    (t : ℝ) (ht : 0 ≤ t) (hA₀t : ∀ e, ‖A₀ e‖ ≤ meshAt L k 0 * t) (h1 : 10 * t ≤ ρ₁)
    (h2 : 50 * (L : ℝ) * t + 100 * C₁ * t ^ 2 < 1 / 2) (h3 : 200 * C₁ * t ≤ 1) :
    ∀ j ≤ k, logSequence A₀ j ∈ complexEdgeForms L n k j ∧
      ∀ e, ‖logSequence A₀ j e‖ ≤ 10 * meshAt L k j * t := by
  have hLpos : 0 < L := by have := hL.2; omega
  have hL2 : 2 ≤ L := by have := hL.2; omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨hA₀, fun e => (hA₀t e).trans ?_⟩
      have := meshAt_pos (k := k) hLpos 0
      nlinarith
    · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hst : ∀ i ≤ j, nextLog (logSequence A₀ i) ∈ complexEdgeForms L n k (i + 1) ∧
          (∀ e, ‖nextLog (logSequence A₀ i) e -
              linearSmoothing L n k i (logSequence A₀ i) e‖ ≤
            C₁ * (10 * meshAt L k i * t) ^ 2) := by
        intro i hi
        obtain ⟨hm, hb⟩ := ih i (by omega) (by omega)
        have hℓ := meshAt_le_one (k := k) hLpos (i := i) (by omega)
        have hℓ0 := meshAt_pos (k := k) hLpos i
        have ha0 : 0 ≤ 10 * meshAt L k i * t := by positivity
        have hale : 10 * meshAt L k i * t ≤ 10 * t := by nlinarith
        have hs : 5 * (L : ℝ) * (10 * meshAt L k i * t) +
            C₁ * (10 * meshAt L k i * t) ^ 2 < 1 / 2 := by
          have e1 : 5 * (L : ℝ) * (10 * meshAt L k i * t) ≤ 50 * (L : ℝ) * t := by
            nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ L) ht]
          have e2 : (10 * meshAt L k i * t) ^ 2 ≤ (10 * t) ^ 2 := by gcongr
          have e3 : C₁ * (10 * meshAt L k i * t) ^ 2 ≤ 100 * C₁ * t ^ 2 := by nlinarith
          linarith
        obtain ⟨s1, s2, -⟩ := nextLog_spec hE ho hel hlm hcf hL hn (by omega : i < k) _ hm _ ha0
          (hale.trans h1) hb hs
        exact ⟨s1, s2⟩
      have hrest : ∀ i ≤ j, quadraticRemainder A₀ i ∈ complexEdgeForms L n k (i + 1) ∧
          ∀ e, ‖quadraticRemainder A₀ i e‖ ≤ C₁ * (10 * meshAt L k i * t) ^ 2 := by
        intro i hi
        obtain ⟨hm, -⟩ := ih i (by omega) (by omega)
        have hfacts := hcf L hL n k i hn (by omega)
        exact ⟨Submodule.sub_mem _ (hst i hi).1 (hfacts.linearSmoothing_mapsTo hm), (hst i hi).2⟩
      refine ⟨(hst j (le_refl j)).1, fun e => ?_⟩
      rw [logSequence_eq_sum hfin A₀ (j + 1) hj]
      simp only [Pi.add_apply, Finset.sum_apply]
      set ℓ := meshAt L k with hℓdef
      have hℓj : 0 < ℓ j := meshAt_pos hLpos j
      have hℓs : ℓ (j + 1) = L * ℓ j := meshAt_succ hLpos j
      have hfirst : ‖linearSmoothingBetween L n k (Nat.zero_le (j + 1)) A₀ e‖ ≤
          5 * ℓ (j + 1) * t := by
        have h4 := norm_linearSmoothingBetween_le hlm hL hk hn (Nat.zero_le (j + 1)) hj (by omega)
          A₀ hA₀ (ℓ 0 * t) (by have := meshAt_pos (k := k) hLpos 0; positivity) hA₀t e
        have h5 := pow_mul_meshAt (k := k) hLpos 0 (j + 1)
        simp only [Nat.sub_zero, zero_add] at h4 h5
        rw [← hℓdef] at h5
        calc _ ≤ 5 * (L : ℝ) ^ (j + 1) * (ℓ 0 * t) := h4
          _ = 5 * ((L : ℝ) ^ (j + 1) * ℓ 0) * t := by ring
          _ = 5 * ℓ (j + 1) * t := by rw [h5]
      have hterm : ∀ i : Fin (j + 1),
          ‖linearSmoothingBetween L n k (Nat.succ_le_of_lt i.2) (quadraticRemainder A₀ i) e‖ ≤
            500 * C₁ * t ^ 2 * ℓ j * ℓ i := by
        intro i
        have hi : (i : ℕ) ≤ j := by have := i.2; omega
        obtain ⟨hm, hbn⟩ := hrest i hi
        have hℓi : 0 < ℓ i := meshAt_pos hLpos i
        have h4 := norm_linearSmoothingBetween_le hlm hL hk hn (Nat.succ_le_of_lt i.2) hj
          (by omega) _ hm (C₁ * (10 * ℓ i * t) ^ 2) (by positivity) hbn e
        have h5 := pow_mul_meshAt (k := k) hLpos i (j - i)
        have hij : (i : ℕ) + (j - i) = j := by omega
        rw [hij, ← hℓdef] at h5
        have e2 : j + 1 - ((i : ℕ) + 1) = j - i := by omega
        rw [e2] at h4
        calc _ ≤ 5 * (L : ℝ) ^ (j - (i : ℕ)) * (C₁ * (10 * ℓ i * t) ^ 2) := h4
          _ = 500 * C₁ * t ^ 2 * ((L : ℝ) ^ (j - (i : ℕ)) * ℓ i) * ℓ i := by ring
          _ = 500 * C₁ * t ^ 2 * ℓ j * ℓ i := by rw [h5]
      have hsum : ‖∑ i : Fin (j + 1),
          linearSmoothingBetween L n k (Nat.succ_le_of_lt i.2) (quadraticRemainder A₀ i) e‖ ≤
          1000 * C₁ * t ^ 2 * ℓ j * ℓ j := by
        have h4 := sum_meshAt_le (k := k) hL2 j
        calc _ ≤ ∑ i : Fin (j + 1), 500 * C₁ * t ^ 2 * ℓ j * ℓ i :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
          _ = 500 * C₁ * t ^ 2 * ℓ j * ∑ i : Fin (j + 1), ℓ i := by rw [Finset.mul_sum]
          _ ≤ 500 * C₁ * t ^ 2 * ℓ j * (2 * ℓ j) := by gcongr
          _ = 1000 * C₁ * t ^ 2 * ℓ j * ℓ j := by ring
      have hone : ℓ j ≤ 1 := meshAt_le_one hLpos (by omega)
      have hle : ℓ j ≤ ℓ (j + 1) := by rw [hℓs]; nlinarith
      have hmain : 1000 * C₁ * t ^ 2 * ℓ j * ℓ j ≤ 5 * ℓ (j + 1) * t := by
        have a1 : 1000 * C₁ * t ^ 2 = 5 * t * (200 * C₁ * t) := by ring
        have a2 : ℓ j * ℓ j ≤ ℓ (j + 1) := by nlinarith
        have a3 : 0 ≤ 5 * t * (200 * C₁ * t) := by positivity
        calc 1000 * C₁ * t ^ 2 * ℓ j * ℓ j = 5 * t * (200 * C₁ * t) * (ℓ j * ℓ j) := by
              rw [a1]; ring
          _ ≤ 5 * t * 1 * ℓ (j + 1) := by
              have : 0 ≤ ℓ j * ℓ j := by positivity
              gcongr
          _ = 5 * ℓ (j + 1) * t := by ring
      calc _ ≤ ‖linearSmoothingBetween L n k (Nat.zero_le (j + 1)) A₀ e‖ + ‖∑ i : Fin (j + 1),
            linearSmoothingBetween L n k (Nat.succ_le_of_lt i.2) (quadraticRemainder A₀ i) e‖ :=
              norm_add_le _ _
        _ ≤ 5 * ℓ (j + 1) * t + 5 * ℓ (j + 1) * t := add_le_add hfirst (hsum.trans hmain)
        _ = 10 * ℓ (j + 1) * t := by ring
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem expTwist_of_complexEdgeForm (hel : ComplexMatrix2.ExpLogEstimates)
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (hj : j ≤ k)
    (A : Edge L n k j → ComplexMatrix2) (hA : A ∈ complexEdgeForms L n k j) :
    (∀ e, PeriodicLattice.expTwist A (fun _ => 1) e =
        ComplexMatrix2.matExp (Complex.I • A e)) ∧
      PeriodicLattice.expTwist A (fun _ => 1) ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hform : ∀ e, A e.opposite = -A e := hA.2
  have hV : ∀ e, PeriodicLattice.expTwist A (fun _ => 1) e =
      ComplexMatrix2.matExp (Complex.I • A e) := by
    intro e
    simp only [PeriodicLattice.expTwist, mul_one]
    split_ifs with h
    · rfl
    · rw [matExp_inv, hform]
      congr 1
      simp
  refine ⟨hV, fun e _ => ?_, fun e _ => ?_⟩
  · rw [hV]
    change Matrix.det _ = 1
    rw [hel.2.2.2.2.2.1]
    have htr : ComplexMatrix2.fullTrace (A e) = 0 := by
      by_cases he : e.IsPositivelyOriented
      · exact hA.1 e he
      · have hp := (xor_isPositivelyOriented_opposite ho hL hn hk hj e).1
        have hp' : e.opposite.IsPositivelyOriented := by
          rcases hp with h | h
          · exact absurd h.1 he
          · exact h.1
        have h1 : ComplexMatrix2.fullTrace (A e.opposite) = 0 := hA.1 _ hp'
        rw [hform, ComplexMatrix2.fullTrace, Matrix.trace_neg, neg_eq_zero] at h1
        exact h1
    have : ComplexMatrix2.fullTrace (Complex.I • A e) = 0 := by
      simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at htr ⊢
      simp [htr]
    rw [this]
    simp
  · rw [hV, hV, matExp_inv, hform]
    congr 1
    simp
theorem meanIterateLogarithms_holds (hexp : NormalizedMeanOfExp)
    (hrev : MeanRadiusOpposite)
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlm : TwoLevelMaps.Statement)
    (hcf : PeriodicCoarseningStep.Holds)
    (hR : SmoothingNearIdentity)
    (hcross : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    MeanIterateLogarithms := by
  intro L hL
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hE⟩ := hexp L hL
  have hLpos : 0 < L := by have := hL.2; omega
  have hLR0 : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hρL : 0 < polydiscRadius L := (hR.1 L hL).2.2.pos
  set τ : ℝ := 1 / (400 * C₁ + 400 * L + 400) with hτ
  have hτ0 : 0 < τ := by positivity
  set ρ : ℝ := min (ρ₁ / 10) (min (polydiscRadius L / 40) τ) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) hτ0)
  refine ⟨ρ, hρ0, ?_⟩
  intro n k hn hk v hv
  obtain ⟨hvm, hvs⟩ := hv
  set t := (maxOperatorNorm v).toReal with htdef
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have htρ : t ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ0.le hvs
  have htop : maxOperatorNorm v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvs
  have hvb : ∀ e, ‖v e‖ ≤ t := by
    intro e
    have h1 : ENNReal.ofReal ‖v e‖ ≤ maxOperatorNorm v :=
      le_iSup (fun e => ENNReal.ofReal (ComplexMatrix2.operatorNorm (v e))) e
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
  have ht1 : 10 * t ≤ ρ₁ := by
    have := htρ.trans (min_le_left _ _)
    linarith
  have ht2 : 40 * t ≤ polydiscRadius L := by
    have := htρ.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have ht3 : (400 * C₁ + 400 * L + 400) * t ≤ 1 := by
    have h := htρ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hpos : 0 < 400 * C₁ + 400 * L + 400 := by positivity
    calc (400 * C₁ + 400 * L + 400) * t ≤ (400 * C₁ + 400 * L + 400) * τ := by gcongr
      _ = 1 := by rw [hτ]; field_simp
  have hCt : 0 ≤ C₁ * t := by positivity
  have hLt : 0 ≤ (L : ℝ) * t := by positivity
  have ha1 : 400 * (C₁ * t) ≤ 1 := by nlinarith
  have ha2 : 400 * ((L : ℝ) * t) ≤ 1 := by nlinarith
  have ha3 : 400 * t ≤ 1 := by nlinarith
  have h2 : 50 * (L : ℝ) * t + 100 * C₁ * t ^ 2 < 1 / 2 := by nlinarith
  have h3 : 200 * C₁ * t ≤ 1 := by nlinarith
  have hfwd : ∀ {i : ℕ} (y : Vertex L n k i) (μ : Fin 4),
      (PeriodicLattice.Bond.forwardFrom y μ).IsPositivelyOriented :=
    fun y μ => ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  have hfin : ∀ i < k, ∀ y : Vertex L n k (i + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
        Set (Vertex L n k i)).Finite := by
    intro i hi y
    have hcard := ((hcross L hL n k hn).1 i hi (PeriodicLattice.Bond.forwardFrom y 0)
      (hfwd y 0)).1
    change Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
      Set (Vertex L n k i)) = L ^ 4 at hcard
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
        Set (Vertex L n k i)) ≠ 0 := by
      rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  set A₀ := scaledRemainderForm v with hA₀
  have hηpos : 0 < meshAt L k 0 := meshAt_pos hLpos 0
  have hA₀m : A₀ ∈ complexEdgeForms L n k 0 := Submodule.smul_of_tower_mem _ _ hvm
  have hA₀t : ∀ e, ‖A₀ e‖ ≤ meshAt L k 0 * t := by
    intro e
    have he : A₀ e = meshAt L k 0 • v e := rfl
    rw [he, norm_smul, Real.norm_of_nonneg hηpos.le]
    exact mul_le_mul_of_nonneg_left (hvb e) hηpos.le
  have hB := logSequence_bounds hE ho hel hlm hcf hL hn hk hfin hC₁ A₀ hA₀m t ht0 hA₀t ht1 h2 h3
  have hℓ1 : ∀ j ≤ k, meshAt L k j ≤ 1 := fun j hj => meshAt_le_one hLpos hj
  have hale : ∀ j ≤ k, 10 * meshAt L k j * t ≤ 10 * t := by
    intro j hj
    have := hℓ1 j hj
    nlinarith
  have ha0 : ∀ j, 0 ≤ 10 * meshAt L k j * t := fun j => by
    have := meshAt_pos (k := k) hLpos j
    positivity
  have hsm : ∀ j ≤ k, 5 * (L : ℝ) * (10 * meshAt L k j * t) +
      C₁ * (10 * meshAt L k j * t) ^ 2 < 1 / 2 := by
    intro j hj
    have h0 := ha0 j
    have h1 := hale j hj
    have e1 : 5 * (L : ℝ) * (10 * meshAt L k j * t) ≤ 50 * (L : ℝ) * t := by nlinarith
    have e2 : (10 * meshAt L k j * t) ^ 2 ≤ (10 * t) ^ 2 := by gcongr
    have e3 : C₁ * (10 * meshAt L k j * t) ^ 2 ≤ 100 * C₁ * t ^ 2 := by nlinarith
    linarith
  have hstep : ∀ j (hj : j < k), ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      normalizedMean (PeriodicLattice.expTwist (logSequence A₀ j) fun _ => 1) c =
        ComplexMatrix2.matExp (Complex.I • nextLog (logSequence A₀ j) c) := fun j hj =>
    (nextLog_spec hE ho hel hlm hcf hL hn hj _ (hB j hj.le).1 _ (ha0 j)
      ((hale j hj.le).trans ht1) (hB j hj.le).2 (hsm j hj.le)).2.2
  set U := remainderGaugeField v with hU
  have hW : ∀ j ≤ k, meanIterate U j =
      PeriodicLattice.expTwist (logSequence A₀ j) fun _ => 1 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hk0 : 0 < k := by omega
      have he : meanIterate U (j + 1) =
          fieldOfPositiveValues fun c =>
            (1 : ComplexMatrix2) * normalizedMean (meanIterate U j) c.1 := by
        simp only [meanIterate]
        rw [levelField, dif_pos hjk]
        rfl
      rw [he, ih (by omega)]
      funext e
      by_cases hpe : e.IsPositivelyOriented
      · simp only [fieldOfPositiveValues, dif_pos hpe, one_mul, PeriodicLattice.expTwist,
          if_pos hpe, mul_one]
        rw [hstep j hjk e hpe]
        rfl
      · have hp := (xor_isPositivelyOriented_opposite ho hL hn hk0 hj e).1
        have hp' : e.opposite.IsPositivelyOriented := by
          rcases hp with h | h
          · exact absurd h.1 hpe
          · exact h.1
        simp only [fieldOfPositiveValues, dif_neg hpe, dif_pos hp', one_mul,
          PeriodicLattice.expTwist, if_neg hpe, mul_one]
        rw [hstep j hjk _ hp']
        rfl
  refine ⟨fun j hj => ⟨logSequence A₀ j, (hB j hj).1, hW j hj, ?_⟩, fun j hj => ?_,
    fun j hj c => ?_⟩
  · exact iSup_le fun e => ENNReal.ofReal_le_ofReal ((hB j hj).2 e)
  · have hk0 : 0 < k := by omega
    rw [hW j hj.le]
    obtain ⟨hV, hcfg⟩ := expTwist_of_complexEdgeForm hel ho hL hn hk0 hj.le _ (hB j hj.le).1
    refine ⟨hcfg, fun e => ?_⟩
    rw [hV]
    have h1 := (hel.1 (Complex.I • logSequence A₀ j e)).2
    have hn1 : ComplexMatrix2.operatorNorm (Complex.I • logSequence A₀ j e) =
        ‖logSequence A₀ j e‖ := by
      change ‖Complex.I • logSequence A₀ j e‖ = _
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [hn1] at h1
    have h2' := (hB j hj.le).2 e
    have h3' := hale j hj.le
    have h4 : ‖logSequence A₀ j e‖ ≤ 10 * t := h2'.trans h3'
    have h5 : |‖logSequence A₀ j e‖| ≤ 1 := by
      rw [abs_of_nonneg (norm_nonneg _)]
      linarith
    have h6 := Real.abs_exp_sub_one_le h5
    rw [abs_of_nonneg (norm_nonneg _)] at h6
    have h7 := (abs_le.mp h6).2
    have h8 : ComplexMatrix2.operatorNorm
        (ComplexMatrix2.matExp (Complex.I • logSequence A₀ j e) - 1) ≤ 20 * t := by
      linarith
    linarith
  · have hk0 : 0 < k := by omega
    rw [hW j hj.le]
    have hcfg := (expTwist_of_complexEdgeForm hel ho hL hn hk0 hj.le _ (hB j hj.le).1).2
    have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius (PeriodicLattice.expTwist (logSequence A₀ j) fun _ => 1) c ≠ 0 ∧
        ‖(meanRadius (PeriodicLattice.expTwist (logSequence A₀ j) fun _ => 1) c)⁻¹‖ ≤ 2 := by
      intro c hc
      have h1 := (hE n k j hn hj _ (hB j hj.le).1 _ (ha0 j) ((hale j hj.le).trans ht1)
        (hB j hj.le).2 c hc).1
      set r := meanRadius (PeriodicLattice.expTwist (logSequence A₀ j) fun _ => 1) c
      have h2' : C₁ * (10 * meshAt L k j * t) ^ 2 < 1 / 2 := by
        have := hsm j hj.le
        have h5 : 0 ≤ 5 * (L : ℝ) * (10 * meshAt L k j * t) := by
          have := ha0 j
          positivity
        linarith
      have h3' : ‖r - 1‖ < 1 / 2 := lt_of_le_of_lt h1 h2'
      have h4 : 1 / 2 ≤ ‖r‖ := by
        have h5 : ‖(1 : ℂ)‖ ≤ ‖r‖ + ‖r - 1‖ := by
          have := norm_sub_le r (r - 1)
          simpa using this
        simp only [norm_one] at h5
        linarith
      have hr0 : r ≠ 0 := fun h => by
        rw [h, norm_zero] at h4
        norm_num at h4
      refine ⟨hr0, ?_⟩
      rw [norm_inv]
      exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · have hp := (xor_isPositivelyOriented_opposite ho hL hn hk0 (by omega : j + 1 ≤ k) c)
      have hp' : c.opposite.IsPositivelyOriented := by
        rcases hp.1 with h | h
        · exact absurd h.1 hc
        · exact h.1
      have he := hrev L hL n k j hn hj _ hcfg _ hp'
      rw [hp.2] at he
      rw [he]
      exact hpos _ hp'
end YangMills.Construction.RunningCouplingSlope.MeanIterateLogs
end
