import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
theorem euclidNormVec_sub_comm (u v : AmbientSpace) :
    euclidNormVec (u - v) = euclidNormVec (v - u) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem bilinDot_add_right (κ u v : Fin 4 → ℂ) :
    bilinDot κ (u + v) = bilinDot κ u + bilinDot κ v := by
  simp [bilinDot, mul_add, Finset.sum_add_distrib]
theorem bilinDot_add_left (κ q y : Fin 4 → ℂ) :
    bilinDot (κ + q) y = bilinDot κ y + bilinDot q y := by
  simp [bilinDot, add_mul, Finset.sum_add_distrib]
theorem toComplexVec_add (u v : AmbientSpace) :
    toComplexVec (u + v) = toComplexVec u + toComplexVec v := by
  funext μ
  simp [toComplexVec]
theorem nearIndices_finite (hsum : ExponentialSums.Bounds) {P : PeriodicData}
    (hP : IsPeriodic P) (y : AmbientSpace) (r : ℝ) : (nearIndices P y r).Finite := by
  obtain ⟨hs, -⟩ := (hsum 1 one_pos).2.2 P hP y
  have ht := hs.tendsto_cofinite_zero
  have hpos : 0 < Real.exp (-r) := Real.exp_pos _
  have hfin := Filter.mem_cofinite.mp (ht (Iio_mem_nhds hpos))
  refine hfin.subset fun i hi => ?_
  have hle : euclidNormVec (P.pos i - y) ≤ r := hi
  simp only [mem_compl_iff, mem_preimage, mem_Iio, not_lt]
  exact Real.exp_le_exp.mpr (by linarith)
theorem translate_injective {P : PeriodicData} (hP : IsPeriodic P) (i : P.Carrier) :
    Function.Injective fun n : Fin 4 → ℤ => P.translate n i := by
  intro m n h
  have h' : P.translate (n - m) (P.translate m i) = P.translate m i := by
    rw [← hP.translate_add, show m + (n - m) = n by abel]
    exact h.symm
  exact (sub_eq_zero.mp (hP.free _ _ h')).symm
theorem translate_neg_translate {P : PeriodicData} (hP : IsPeriodic P) (n : Fin 4 → ℤ)
    (i : P.Carrier) : P.translate (-n) (P.translate n i) = i := by
  rw [← hP.translate_add, add_neg_cancel, hP.translate_zero]
theorem translate_translate_neg {P : PeriodicData} (hP : IsPeriodic P) (n : Fin 4 → ℤ)
    (i : P.Carrier) : P.translate n (P.translate (-n) i) = i := by
  rw [← hP.translate_add, neg_add_cancel, hP.translate_zero]
section Kernels
variable {P Q : PeriodicData}
theorem bounded_of_shiftInvariant (hsum : ExponentialSums.Bounds)
    (horb : QuotOrbits.Claim) (hP : IsPeriodic P)
    (hQ : IsPeriodic Q) {K : Q.Carrier → P.Carrier → ℂ} (hK : IsShiftInvariant P Q K) {R : ℝ}
    (hfar : ∀ j i, ¬ euclidNormVec (Q.pos j - P.pos i) ≤ R → K j i = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ j i, ‖K j i‖ ≤ C := by
  classical
  have hfq : Finite Q.UnitQuot := hQ.finite_quot
  choose rep hrep using fun c : Q.UnitQuot => Quot.exists_rep c
  let S : Set (Q.Carrier × P.Carrier) :=
    ⋃ c : Q.UnitQuot, (fun i => (rep c, i)) '' nearIndices P (Q.pos (rep c)) R
  have hS : S.Finite :=
    Set.finite_iUnion fun c => (nearIndices_finite hsum hP _ R).image _
  have hnn : ∀ p ∈ hS.toFinset, 0 ≤ ‖K p.1 p.2‖ := fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ p ∈ hS.toFinset, ‖K p.1 p.2‖, ?_, fun j i => ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  by_cases hd : euclidNormVec (Q.pos j - P.pos i) ≤ R
  · have hcl : Q.mkQuot 1 (rep (Q.mkQuot 1 j)) = Q.mkQuot 1 j := hrep _
    obtain ⟨n, hn⟩ := ((horb Q hQ).1 1 _ _).mp hcl
    rw [one_smul] at hn
    set a := rep (Q.mkQuot 1 j) with ha
    set b := P.translate (-n) i with hb
    have hi : i = P.translate n b := (translate_translate_neg hP n i).symm
    have hval : K j i = K a b := by
      rw [hn, hi]
      exact hK n a b
    have hdist : euclidNormVec (P.pos b - Q.pos a) ≤ R := by
      rw [euclidNormVec_sub_comm]
      have : Q.pos j - P.pos i = Q.pos a - P.pos b := by
        rw [hn, hi, hQ.pos_translate, hP.pos_translate]
        abel
      rwa [this] at hd
    have hmem : (a, b) ∈ hS.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_iUnion.mpr ⟨Q.mkQuot 1 j, b, hdist, rfl⟩
    have := Finset.single_le_sum hnn hmem
    rw [hval]
    simp only at this
    linarith
  · rw [hfar j i hd, norm_zero]
    have := Finset.sum_nonneg hnn
    linarith
theorem kernel_support_finite (hsum : ExponentialSums.Bounds) (hP : IsPeriodic P)
    {K : Q.Carrier → P.Carrier → ℂ} {R : ℝ}
    (hfar : ∀ j i, ¬ euclidNormVec (Q.pos j - P.pos i) ≤ R → K j i = 0)
    (j : Q.Carrier) (i : P.Carrier) :
    (Function.support fun n : Fin 4 → ℤ => K j (P.translate n i)).Finite := by
  have hpre := (nearIndices_finite hsum hP (Q.pos j) R).preimage
    ((translate_injective hP i).injOn)
  refine hpre.subset fun n hn => ?_
  by_contra hout
  apply hn
  refine hfar _ _ fun hle => hout ?_
  change euclidNormVec (P.pos (P.translate n i) - Q.pos j) ≤ R
  rwa [euclidNormVec_sub_comm]
theorem fourierSymbol_eq_finset_sum {K : Q.Carrier → P.Carrier → ℂ} (F : Finset (Fin 4 → ℤ))
    (j : Q.Carrier) (i : P.Carrier) (hF : ∀ n, n ∉ F → K j (P.translate n i) = 0)
    (κ : Fin 4 → ℂ) :
    fourierSymbol P Q K κ j i = ∑ n ∈ F, symbolSummand P Q K κ j i n := by
  refine tsum_eq_sum fun n hn => ?_
  simp [symbolSummand, hF n hn]
theorem kernel_properties (hsum : ExponentialSums.Bounds)
    (horb : QuotOrbits.Claim) (hP : IsPeriodic P)
    (hQ : IsPeriodic Q) {K : Q.Carrier → P.Carrier → ℂ} (hK : IsShiftInvariant P Q K) {R : ℝ}
    (hfar : ∀ j i, ¬ euclidNormVec (Q.pos j - P.pos i) ≤ R → K j i = 0) :
    IsFiniteRangeAllRates P Q K ∧ SymbolIsExponentialSum P Q K ∧
      SymbolIsEntire P Q K := by
  obtain ⟨C, hC, hb⟩ := bounded_of_shiftInvariant hsum horb hP hQ hK hfar
  have hrate : ∀ δ : ℝ, 0 < δ → IsDecayRate P Q K δ := by
    intro δ hδ
    refine ⟨hδ, C * Real.exp (δ * |R|), by positivity, fun j i => ?_⟩
    by_cases hd : euclidNormVec (Q.pos j - P.pos i) ≤ R
    · rw [mul_assoc, ← Real.exp_add]
      have h0 : 0 ≤ δ * |R| + -δ * euclidNormVec (Q.pos j - P.pos i) := by
        have : euclidNormVec (Q.pos j - P.pos i) ≤ |R| := hd.trans (le_abs_self R)
        nlinarith
      have h1 := Real.one_le_exp h0
      calc ‖K j i‖ ≤ C := hb j i
        _ = C * 1 := (mul_one C).symm
        _ ≤ _ := by gcongr
    · rw [hfar j i hd, norm_zero]
      positivity
  have hfin := fun j i => kernel_support_finite hsum hP hfar j i
  have hzero : ∀ j i n, n ∉ (hfin j i).toFinset → K j (P.translate n i) = 0 := by
    intro j i n hn
    by_contra hne
    exact hn ((Set.Finite.mem_toFinset _).mpr hne)
  have hexp : SymbolIsExponentialSum P Q K := by
    intro j i
    let F := (hfin j i).toFinset
    let e := F.equivFin
    refine ⟨F.card, fun k => K j (P.translate (e.symm k) i),
      fun k => P.pos (P.translate (e.symm k) i) - Q.pos j, fun κ => ?_⟩
    rw [fourierSymbol_eq_finset_sum F j i (hzero j i) κ, ← Finset.sum_coe_sort F,
      ← Equiv.sum_comp e.symm]
    rfl
  obtain ⟨-, C₁, hC₁, hb₁⟩ := hrate 1 one_pos
  refine ⟨⟨⟨hK, C₁, 1, hC₁, one_pos, hb₁⟩, ⟨R, hfar⟩, hrate, ?_⟩, hexp, ?_⟩
  · intro κ _ j i
    refine (hasSum_sum_of_ne_finset_zero (s := (hfin j i).toFinset) fun n hn => ?_).summable
    simp [symbolSummand, hzero j i n hn]
  · intro j i
    obtain ⟨m, a, y, hsum'⟩ := hexp j i
    have hfun : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) => fourierSymbol P Q K κ j i) =
        fun κ _ => ∑ k, a k * Complex.exp (Complex.I * bilinDot κ (toComplexVec (y k))) := by
      funext κ _
      exact hsum' κ
    have hd : Differentiable ℂ (fun κ : Fin 4 → ℂ =>
        ∑ k, a k * Complex.exp (Complex.I * bilinDot κ (toComplexVec (y k)))) := by
      unfold bilinDot
      fun_prop
    unfold YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn
    rw [hfun]
    refine ⟨isOpen_univ, ?_, fun p _ k => Filter.Eventually.of_forall fun ζ => ?_⟩
    · exact (continuous_pi fun _ => hd.continuous).continuousOn
    · have hl : Differentiable ℂ
          (fun ζ : ℂ => p + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector k) := by
        fun_prop
      exact differentiableAt_pi.mpr fun _ => (hd _).comp ζ (hl ζ)
end Kernels
theorem dephasedKernel_shiftInvariant {P Q : PeriodicData} (hQ : IsPeriodic Q) {q : Fin 4 → ℂ}
    {Y : Q.Carrier → P.Carrier → ℂ} (hY : IsPhaseCovariant P Q q Y) :
    IsShiftInvariant P Q (dephasedKernel P Q q Y) := by
  intro n j i
  simp only [dephasedKernel]
  rw [hY n j i, hQ.pos_translate, toComplexVec_add, bilinDot_add_right, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring
theorem applyKernel_blochWave_of_vanishes (hsum : ExponentialSums.Bounds)
    (hsym : SymbolOnQuotients.Claim) {P Q : PeriodicData}
    (hP : IsPeriodic P) (hQ : IsPeriodic Q) {q : Fin 4 → ℂ} {R : ℝ}
    {Y : Q.Carrier → P.Carrier → ℂ} (hv : VanishesOutsideRadius P Q R Y)
    (hop : IsFiniteRangeAllRates P Q (dephasedKernel P Q q Y)) :
    ActsOnBlochWaves P Q q Y := by
  intro κ φ j
  refine ⟨?_, ?_⟩
  · refine (nearIndices_finite hsum hP (Q.pos j) R).subset fun i hi => ?_
    by_contra hn
    apply hi
    have h0 : Y j i = 0 := hv j i fun hle => hn (by
      change euclidNormVec (P.pos i - Q.pos j) ≤ R
      rwa [euclidNormVec_sub_comm])
    simp [h0]
  · have hact := ((hsym P Q hP hQ _ hop.periodic).applyKernel_blochWave κ
      (hop.summable κ (mem_univ κ)) φ j).2
    have hYK : applyKernel Y (blochWave P κ φ) j =
        Complex.exp (Complex.I * bilinDot q (toComplexVec (Q.pos j))) *
          applyKernel (dephasedKernel P Q q Y) (blochWave P κ φ) j := by
      simp only [applyKernel, dephasedKernel]
      rw [← tsum_mul_left]
      refine tsum_congr fun i => ?_
      rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add]
      simp
    rw [hYK, hact]
    simp only [blochWave]
    rw [bilinDot_add_left, mul_add, Complex.exp_add]
    ring
theorem quotSymbol_idKernel (horb : QuotOrbits.Claim)
    (hsym : SymbolOnQuotients.Claim) {P : PeriodicData} (hP : IsPeriodic P)
    (hop : IsPeriodicKernel P P (idKernel P))
    (hsumm : SymbolSummableOn P P (idKernel P) univ) (κ : Fin 4 → ℂ) :
    quotSymbol P P (idKernel P) κ = quotOne P := by
  classical
  funext c' c
  induction c' using Quot.ind with
  | mk j =>
  induction c using Quot.ind with
  | mk i =>
  change quotSymbol P P (idKernel P) κ (P.mkQuot 1 j) (P.mkQuot 1 i) =
    quotOne P (P.mkQuot 1 j) (P.mkQuot 1 i)
  rw [(hsym P P hP hP _ hop).quotSymbol_mkQuot κ (hsumm κ (mem_univ κ))]
  by_cases hcl : P.mkQuot 1 j = P.mkQuot 1 i
  · obtain ⟨n, hn⟩ := ((horb P hP).1 1 i j).mp hcl.symm
    rw [one_smul] at hn
    have hterm : ∀ m, m ≠ n → symbolSummand P P (idKernel P) κ j i m = 0 := by
      intro m hm
      have hne : j ≠ P.translate m i := fun h =>
        hm (translate_injective hP i (h.symm.trans hn))
      simp [symbolSummand, idKernel, hne]
    have hself : symbolSummand P P (idKernel P) κ j i n = 1 := by
      have h0 : bilinDot κ (toComplexVec (0 : AmbientSpace)) = 0 := by
        simp [bilinDot, toComplexVec]
      simp only [symbolSummand, idKernel]
      rw [← hn, sub_self, h0]
      simp
    rw [fourierSymbol, tsum_eq_single n hterm, hself]
    simp [quotOne, hcl]
  · have hterm : ∀ m, symbolSummand P P (idKernel P) κ j i m = 0 := by
      intro m
      have hne : j ≠ P.translate m i := by
        intro h
        apply hcl
        exact (((horb P hP).1 1 i j).mpr ⟨m, by rw [one_smul]; exact h⟩).symm
      simp [symbolSummand, idKernel, hne]
    simp only [fourierSymbol, hterm, tsum_zero]
    simp [quotOne, hcl]
theorem claim_holds (hsum : ExponentialSums.Bounds) (horb : QuotOrbits.Claim)
    (hsym : SymbolOnQuotients.Claim) : CovariantFiniteRange.Claim := by
  refine ⟨fun P hP => ?_, fun P Q hP hQ q R Y hY hv => ?_⟩
  · have hcov : IsShiftInvariant P P (idKernel P) := by
      intro n j i
      have hiff : P.translate n j = P.translate n i ↔ j = i := by
        refine ⟨fun h => ?_, fun h => by rw [h]⟩
        rw [← translate_neg_translate hP n j, h, translate_neg_translate hP n i]
      by_cases h : j = i
      · simp [idKernel, h]
      · have h' : P.translate n j ≠ P.translate n i := fun e => h (hiff.mp e)
        simp [idKernel, h, h']
    have hfar : ∀ j i, ¬ euclidNormVec (P.pos j - P.pos i) ≤ 0 →
        idKernel P j i = 0 := by
      intro j i hn
      have hne : j ≠ i := by
        rintro rfl
        apply hn
        simp [euclidNormVec]
      simp [idKernel, hne]
    obtain ⟨hop, -, -⟩ := kernel_properties hsum horb hP hP hcov hfar
    exact ⟨fun y r => nearIndices_finite hsum hP y r, hop.periodic, hop.finiteRange,
      fun κ => quotSymbol_idKernel horb hsym hP hop.periodic hop.summable κ⟩
  · have hfar : ∀ j i, ¬ euclidNormVec (Q.pos j - P.pos i) ≤ R →
        dephasedKernel P Q q Y j i = 0 := by
      intro j i hn
      simp [dephasedKernel, hv j i hn]
    obtain ⟨hop, hexp, hent⟩ :=
      kernel_properties hsum horb hP hQ (dephasedKernel_shiftInvariant hQ hY) hfar
    exact ⟨hop, hexp, hent, applyKernel_blochWave_of_vanishes hsum hsym hP hQ hv hop⟩
end YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof
end
