import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.FourierSeriesOfATestFunctionConverges
import YangMills.Construction.TorusOrFourSpace.PartialSumsUnderATestFunction
import YangMills.Construction.TorusOrFourSpace.PartialsOfSumsAndProducts
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell.TruncationsUnderCutoff
open Kind.Tuple (partialDeriv proj cNorm IsSmoothT IsClassC)
open Coords (iterPartial partialAlong HasSmoothPartials ContPartialsUpTo)
variable {p : ℕ+}
theorem pairing_add_smul_single (k : IntCoords p) (x : Coords p)
    (i : Fin (4 * (p : ℕ))) (r : ℝ) :
    k.pairing (x + r • Pi.single i (1 : ℝ)) = k.pairing x + r * (k i : ℝ) := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.pairing_add_smul_single <;> assumption
theorem continuous_fourierChar (L : ℝ) (k : IntCoords p) : Continuous (fourierChar L k) := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.continuous_fourierChar <;> assumption
def charFreq (L : ℝ) (k : IntCoords p) (i : Fin (4 * (p : ℕ))) : ℂ :=
  2 * Real.pi * Complex.I * (k i : ℂ) / (L : ℂ)
theorem hasDerivAt_fourierChar_line (L : ℝ) (k : IntCoords p) (x : Coords p)
    (i : Fin (4 * (p : ℕ))) :
    HasDerivAt (fun r : ℝ => fourierChar L k (x + r • Pi.single i (1 : ℝ)))
      (charFreq L k i * fourierChar L k x) 0 := by
  have h0 : HasDerivAt (fun r : ℝ => k.pairing x + r * (k i : ℝ)) ((k i : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (k i : ℝ)).const_add (k.pairing x)
  have h1 : HasDerivAt (fun r : ℝ => ((k.pairing x + r * (k i : ℝ) : ℝ) : ℂ)) (((k i : ℝ)) : ℂ) 0 :=
    h0.ofReal_comp
  have h2 := ((h1.const_mul (2 * (Real.pi : ℂ) * Complex.I)).div_const (L : ℂ)).cexp
  have e : (fun r : ℝ => fourierChar L k (x + r • Pi.single i (1 : ℝ))) =
      fun r : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((k.pairing x + r * (k i : ℝ) : ℝ) : ℂ) / (L : ℂ)) := by
    funext r
    rw [fourierChar, pairing_add_smul_single]
  rw [e]
  convert h2 using 1
  simp only [charFreq, fourierChar, zero_mul, add_zero]
  push_cast
  ring
theorem contPartialsUpTo_const_mul_fourierChar (L : ℝ) (k : IntCoords p) (n : ℕ) :
    ∀ a : ℂ, ContPartialsUpTo n (fun x => a * fourierChar L k x) := by
  induction n with
  | zero =>
    intro a
    exact continuous_const.mul (continuous_fourierChar L k)
  | succ n ih =>
    intro a
    have hline : ∀ (i : Fin (4 * (p : ℕ))) (z : Coords p),
        HasLineDerivAt ℝ (fun x => a * fourierChar L k x)
          (a * (charFreq L k i * fourierChar L k z)) z (Pi.single i (1 : ℝ)) := fun i z =>
      HasDerivAt.const_mul a (hasDerivAt_fourierChar_line L k z i)
    refine ⟨continuous_const.mul (continuous_fourierChar L k), fun i =>
      ⟨fun z => (hline i z).lineDifferentiableAt, ?_⟩⟩
    have e : partialAlong i (fun x => a * fourierChar L k x) =
        fun x => (a * charFreq L k i) * fourierChar L k x := by
      funext z
      rw [partialAlong, (hline i z).lineDeriv, mul_assoc]
    rw [e]
    exact ih _
theorem hasSmoothPartials_fourierChar (L : ℝ) (k : IntCoords p) :
    HasSmoothPartials (fourierChar L k) := by
  intro n
  have h := contPartialsUpTo_const_mul_fourierChar L k n 1
  simpa only [one_mul] using h
theorem hasSmoothPartials_sum_fourierChar (hlr : SumsProductsPartials.LeibnizRules) (L : ℝ)
    (a : IntCoords p → ℂ) (S : Finset (IntCoords p)) :
    HasSmoothPartials (fun x => ∑ k ∈ S, a k * fourierChar L k x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 := hasSmoothPartials_fourierChar (p := p) L 0
    have h := (hlr p _ _ h0 h0).1 0 0
    convert h using 1
    funext x
    simp
  | insert k S hk ih =>
    have h := (hlr p _ _ (hasSmoothPartials_fourierChar L k) ih).1 (a k) 1
    convert h using 1
    funext x
    simp [Finset.sum_insert hk]
theorem mem_coordCube_of_proj_mem_cellPow (D : Params) (L : ℝ) (x : Coords p)
    (h : proj D Kind.euclidean x ∈ cellPow D p L) : x ∈ coordCube p L := by
  intro i
  have hi := i.2
  have hq : (i : ℕ) / 4 < (p : ℕ) := by omega
  have hr : (i : ℕ) % 4 < 4 := by omega
  have h2 := h ⟨(i : ℕ) / 4, hq⟩ ⟨(i : ℕ) % 4, hr⟩
  have e : (⟨4 * ((i : ℕ) / 4) + (i : ℕ) % 4, by omega⟩ : Fin (4 * (p : ℕ))) = i :=
    Fin.ext (by simp only; omega)
  change x ⟨4 * ((i : ℕ) / 4) + (i : ℕ) % 4, _⟩ ∈ _ at h2
  rwa [e] at h2
def cellGap (D : Params) (L : ℝ) (f : Kind.euclidean.Tuple D p → ℂ)
    (β : CoordIndex p) (N : ℕ+) : ℝ≥0∞ :=
  ⨆ x ∈ coordCube p L, ENNReal.ofReal
    ‖(∑ k ∈ IntCoords.cubeUpTo N,
        fourierCoeff D L f k * iterPartial β (fourierChar L k) x) -
      partialDeriv D Kind.euclidean β f (proj D Kind.euclidean x)‖
def cellGapSum (D : Params) (L : ℝ) (f : Kind.euclidean.Tuple D p → ℂ) (n : ℕ) (N : ℕ+) :
    ℝ≥0∞ :=
  ∑ β ∈ Fintype.piFinset fun _ : Fin (4 * (p : ℕ)) => Finset.range (n + 1),
    cellGap D L f β N
theorem cellGap_le_cellGapSum (D : Params) (L : ℝ) (f : Kind.euclidean.Tuple D p → ℂ) (n : ℕ)
    (N : ℕ+) (β : CoordIndex p) (hβ : β.degree ≤ n) :
    cellGap D L f β N ≤ cellGapSum D L f n N := by
  refine Finset.single_le_sum (f := fun β => cellGap D L f β N)
    (fun _ _ => zero_le) ?_
  refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
  have : β i ≤ β.degree :=
    Finset.single_le_sum (f := fun i => β i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
theorem fourierTruncationsConverge_holds
    (hser : FourierSeriesConvergence.TestFnFourierSeriesConverges)
    (hcoef : FourierCoeffBounds)
    (hlr : SumsProductsPartials.LeibnizRules)
    (htup : TupleFacts.AllFacts) : FourierTruncationsConverge := by
  intro D p L hL χ hχ f hf g hg
  obtain ⟨-, -, hchar, hderiv, hpsum, -, -, -, -, -, -⟩ := hcoef D p L hL
  obtain ⟨hfib, -, hmetric, -, -, -, -, -, -, -, -, -, -, -, hderivs, hfin, -, hsupp, hclass, -,
    -, -, -, -⟩ := htup D Kind.euclidean p
  have hS : ∀ N : ℕ+, HasSmoothPartials (fourierPartialSum D L f N) := fun N =>
    hasSmoothPartials_sum_fourierChar hlr L (fourierCoeff D L f) (IntCoords.cubeUpTo N)
  have hgs : ∀ N, IsSmoothT D Kind.euclidean (g N) := fun N n => by
    change ContPartialsUpTo n (g N ∘ proj D Kind.euclidean)
    rw [hg N]
    exact hS N n
  refine ⟨hgs, fun n => ?_⟩
  have hKs : ∀ (N : ℕ+) (m : ℕ), IsClassC D Kind.euclidean m (g N - f) := fun N m => by
    have h := ((hclass m (g N) f (hgs N m) (hf.1 m)).1 1 (-1))
    have e : (1 : ℂ) • g N + (-1 : ℂ) • f = g N - f := by
      funext y
      simp [sub_eq_add_neg]
    rwa [e] at h
  have hHs : ∀ (N : ℕ+) (m : ℕ), IsClassC D Kind.euclidean m (χ * (g N - f)) := fun N m =>
    (hclass m χ _ (hχ.1 m) (hKs N m)).2.1
  have hχall : HasSmoothPartials (χ ∘ proj D Kind.euclidean (p := p)) := hχ.1
  have hfall : HasSmoothPartials (f ∘ proj D Kind.euclidean (p := p)) := hf.1
  have hKall : ∀ N : ℕ+, HasSmoothPartials
      ((g N - f) ∘ proj D Kind.euclidean (p := p)) := fun N m => hKs N m
  have hA : cNorm D Kind.euclidean n χ ≠ ∞ := (hfin n χ (hχ.1 n) hχ.2.1).ne
  have hgap : ∀ (N : ℕ+) (β : CoordIndex p) (x : Coords p),
      iterPartial β ((g N - f) ∘ proj D Kind.euclidean) x =
        (∑ k ∈ IntCoords.cubeUpTo N,
          fourierCoeff D L f k * iterPartial β (fourierChar L k) x) -
        partialDeriv D Kind.euclidean β f (proj D Kind.euclidean x) := by
    intro N β x
    have e : (g N - f) ∘ proj D Kind.euclidean (p := p) =
        (1 : ℂ) • fourierPartialSum D L f N + (-1 : ℂ) • (f ∘ proj D Kind.euclidean) := by
      rw [← hg N]
      funext z
      simp [sub_eq_add_neg]
    have hlin := (hlr p _ _ (hS N) hfall).2.2.2.2.1 1 (-1) β
    have hdf : partialDeriv D Kind.euclidean β f ∘ proj D Kind.euclidean (p := p) =
        iterPartial β (f ∘ proj D Kind.euclidean) :=
      (hderivs β.degree f (hf.1 _) β le_rfl).2.1
    have hsum : iterPartial β (fourierPartialSum D L f N) x =
        ∑ k ∈ IntCoords.cubeUpTo N,
          fourierCoeff D L f k * iterPartial β (fourierChar L k) x := by
      rw [hpsum f hf β N]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hderiv f hf β k, hchar β k]
      ring
    rw [e, hlin, ← hdf]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, Function.comp_apply, hsum]
    ring
  have hbound : ∀ N : ℕ+, cellGapSum D L f n N ≠ ∞ →
      cNorm D Kind.euclidean n (χ * (g N - f)) ≤
        (2 : ℝ≥0∞) ^ n * cNorm D Kind.euclidean n χ * cellGapSum D L f n N := by
    intro N hC
    set a : ℝ := (cNorm D Kind.euclidean n χ).toReal with ha_def
    set b : ℝ := (cellGapSum D L f n N).toReal with hb_def
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hnorm : ∀ α : CoordIndex p, α.degree ≤ n →
        ∀ y, ‖partialDeriv D Kind.euclidean α (χ * (g N - f)) y‖ ≤ 2 ^ n * a * b := by
      intro α hα y
      by_cases hy : y ∈ cellPow D p L
      · obtain ⟨x, rfl⟩ := hfib.1 y
        have hx := mem_coordCube_of_proj_mem_cellPow D L x hy
        have hd : partialDeriv D Kind.euclidean α (χ * (g N - f)) ∘
            proj D Kind.euclidean (p := p) =
            iterPartial α ((χ * (g N - f)) ∘ proj D Kind.euclidean) :=
          (hderivs α.degree _ (hHs N _) α le_rfl).2.1
        have e1 : partialDeriv D Kind.euclidean α (χ * (g N - f))
            (proj D Kind.euclidean x) =
            iterPartial α ((χ * (g N - f)) ∘ proj D Kind.euclidean) x :=
          congrFun hd x
        rw [e1]
        have hleib := (hlr p _ _ hχall (hKall N)).2.2.2.2.2.2.2 n a b x ?_ ?_ α hα
        · exact hleib
        · intro β hβ
          have hdχ : partialDeriv D Kind.euclidean β χ ∘ proj D Kind.euclidean (p := p) =
              iterPartial β (χ ∘ proj D Kind.euclidean) :=
            (hderivs β.degree χ (hχ.1 _) β le_rfl).2.1
          have e2 : iterPartial β (χ ∘ proj D Kind.euclidean) x =
              partialDeriv D Kind.euclidean β χ (proj D Kind.euclidean x) :=
            (congrFun hdχ x).symm
          rw [e2]
          refine (ENNReal.ofReal_le_iff_le_toReal hA).1 ?_
          calc ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ (proj D Kind.euclidean x)‖
              ≤ ⨆ y, ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ y‖ :=
                le_iSup (fun y => ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ y‖) _
            _ ≤ ⨆ _ : β.degree ≤ n, ⨆ y, ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ y‖ :=
                le_iSup (fun _ : β.degree ≤ n =>
                  ⨆ y, ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ y‖) hβ
            _ ≤ cNorm D Kind.euclidean n χ :=
                le_iSup (fun β : CoordIndex p => ⨆ _ : β.degree ≤ n,
                  ⨆ y, ENNReal.ofReal ‖partialDeriv D Kind.euclidean β χ y‖) β
        · intro β hβ
          rw [hgap N β x]
          refine (ENNReal.ofReal_le_iff_le_toReal hC).1 ?_
          refine le_trans ?_ (cellGap_le_cellGapSum D L f n N β hβ)
          exact le_iSup₂ (f := fun x (_ : x ∈ coordCube p L) => ENNReal.ofReal
            ‖(∑ k ∈ IntCoords.cubeUpTo N,
                fourierCoeff D L f k * iterPartial β (fourierChar L k) x) -
              partialDeriv D Kind.euclidean β f (proj D Kind.euclidean x)‖) x hx
      · have hzero : partialDeriv D Kind.euclidean α (χ * (g N - f)) y = 0 := by
          by_contra hne
          have hmem : y ∈ Kind.Tuple.supportT D Kind.euclidean
              (partialDeriv D Kind.euclidean α (χ * (g N - f))) := fun r hr => ⟨y, hne, by
            rw [(hmetric.2.1 y y).2 rfl]
            exact hr⟩
          have h1 := (hderivs α.degree _ (hHs N _) α le_rfl).2.2.2.2.2 hmem
          exact hy (hχ.2.2 ((hsupp χ (g N - f) 0 0).2 h1).1)
        rw [hzero, norm_zero]
        positivity
    refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
    refine (ENNReal.ofReal_le_ofReal (hnorm α hα y)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal hA, ENNReal.ofReal_toReal hC, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hC : Tendsto (cellGapSum D L f n) atTop (𝓝 0) := by
    have h := tendsto_finsetSum
      (Fintype.piFinset fun _ : Fin (4 * (p : ℕ)) => Finset.range (n + 1))
      (fun β _ => hser D p L hL f hf β)
    rw [Finset.sum_const_zero] at h
    exact h
  have hlim : Tendsto (fun N => (2 : ℝ≥0∞) ^ n * cNorm D Kind.euclidean n χ *
      cellGapSum D L f n N) atTop (𝓝 0) := by
    have hne : (2 : ℝ≥0∞) ^ n * cNorm D Kind.euclidean n χ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hA
    have h := ENNReal.Tendsto.const_mul hC (Or.inr hne)
    simpa only [mul_zero] using h
  have hfinite : ∀ᶠ N in atTop, cellGapSum D L f n N ≠ ∞ :=
    (hC.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).mono fun N hN =>
      (hN.trans ENNReal.one_lt_top).ne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (hfinite.mono hbound)
end YangMills.Construction.PeriodicSpace.PeriodCell.TruncationsUnderCutoff
