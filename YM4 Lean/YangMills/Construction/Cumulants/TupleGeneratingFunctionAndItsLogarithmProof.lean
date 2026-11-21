import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Cumulants.ExponentialMomentSeries
import YangMills.Construction.Cumulants.MixedCumulantAsIteratedPartial
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import YangMills.Construction.Probability.ExpectationBasicProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.TupleLogMGF
open YangMills.Construction.Probability (IsBoundedRealRV IsBoundedComplexRV complexExpectation)
open YangMills.Construction.ComplexVariables (IsHolomorphicScalar IsEntireFun HasPartialDeriv
  partialDeriv iteratedPartials partialOverFinset diffQuot absMonomial indicatorIndex
  multiIndexSteps partialOfIndex logPrincipal)
open YangMills.Construction.ComplexVariables.HolomorphicFacts (PartialDerivProperties powerSeriesSum)
open YangMills.Construction.Coordinates (ComplexCoordinates)
private theorem norm_monomial {n : ℕ} (z : ComplexCoordinates n)
    (α : YangMills.Construction.PowerSeries.MultiIndex n) :
    ‖YangMills.Construction.PowerSeries.MultiIndex.monomial z α‖ = absMonomial z α := by
  simp [YangMills.Construction.PowerSeries.MultiIndex.monomial, absMonomial, norm_prod, norm_pow]
private theorem multiIndexSteps_indicatorIndex_perm {n : ℕ} (J : Finset (Fin n)) :
    (multiIndexSteps (indicatorIndex J)).Perm J.sort := by
  have h : ∀ l : List (Fin n),
      l.flatMap (fun i => List.replicate (indicatorIndex J i) i) = l.filter (· ∈ J) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : a ∈ J
      · simp [List.flatMap_cons, indicatorIndex, ha] at ih ⊢
        exact ih
      · simp [List.flatMap_cons, indicatorIndex, ha] at ih ⊢
        exact ih
  have hs : multiIndexSteps (indicatorIndex J) = (List.finRange n).filter (· ∈ J) := h _
  rw [hs]
  refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).filter _) (Finset.sort_nodup J _)).2
    fun a => ?_
  simp
private theorem perm_finsetSort_of_nodup {n : ℕ} {J : Finset (Fin n)} {l : List (Fin n)}
    (hl : l.Nodup) (hm : ∀ a, a ∈ l ↔ a ∈ J) : l.Perm J.sort :=
  (List.perm_ext_iff_of_nodup hl (Finset.sort_nodup J _)).2 fun a => by simp [hm a]
private theorem monomial_indicatorIndex {Ω : Type} {n : ℕ} (x : Fin n → Ω → ℝ)
    (J : Finset (Fin n)) (ω : Ω) :
    YangMills.Construction.PowerSeries.MultiIndex.monomial x (indicatorIndex J) ω =
      ∏ l ∈ J, x l ω := by
  have h : ∀ i, x i ω ^ indicatorIndex J i = if i ∈ J then x i ω else 1 := by
    intro i
    by_cases hi : i ∈ J <;> simp [indicatorIndex, hi]
  simp only [YangMills.Construction.PowerSeries.MultiIndex.monomial, Finset.prod_apply,
    Pi.pow_apply, h]
  simp [Finset.prod_ite_mem]
private theorem mgfEntireWithMoments_of
    (hSeries : ExponentialMomentSeriesExpansion)
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i)) :
    MGFEntireWithMoments μ X := by
  obtain ⟨-, -, -, hser, hEnt, hF0, -⟩ := hSeries Ω μ n X hn hX
  have hEnt' : IsEntireFun (tupleMomentGeneratingFunction μ X) := hEnt
  obtain ⟨hPD, -, -, hTerm, -⟩ := hTools n hn univ isOpen_univ
  obtain ⟨-, -, hJ, -, -, hAlpha, -, -⟩ := hPD _ hEnt'
  refine ⟨hEnt', hF0, fun J => (hJ J).1, fun J => ?_⟩
  let mom : YangMills.Construction.PowerSeries.MultiIndex n → ℂ := fun α =>
    complexExpectation μ fun ω =>
      ((YangMills.Construction.PowerSeries.MultiIndex.monomial X α ω : ℝ) : ℂ)
  let coeff : YangMills.Construction.PowerSeries.MultiIndex n → ℂ := fun α =>
    mom α / (YangMills.Construction.PowerSeries.MultiIndex.factorial α : ℂ)
  have hterm : ∀ (z : ComplexCoordinates n) (α : YangMills.Construction.PowerSeries.MultiIndex n),
      YangMills.Construction.PowerSeries.MultiIndex.monomial z α /
          (YangMills.Construction.PowerSeries.MultiIndex.factorial α : ℂ) * mom α =
        coeff α * YangMills.Construction.PowerSeries.MultiIndex.monomial z α := fun z α => by
    simp only [coeff]
    ring
  have hFa : tupleMomentGeneratingFunction μ X = powerSeriesSum coeff := by
    funext z
    have h := (hser z).2.1
    refine h.trans ?_
    simp only [powerSeriesSum, YangMills.Construction.ComplexVariables.indexSum]
    exact tsum_congr (hterm z)
  have hsum : ∀ z : ComplexCoordinates n, Summable fun α => ‖coeff α‖ * absMonomial z α := by
    intro z
    have h : Summable fun α : YangMills.Construction.PowerSeries.MultiIndex n =>
        ‖YangMills.Construction.PowerSeries.MultiIndex.monomial z α /
          (YangMills.Construction.PowerSeries.MultiIndex.factorial α : ℂ) * mom α‖ := (hser z).1
    refine h.congr fun α => ?_
    rw [hterm, norm_mul, norm_monomial]
  have hval := (hTerm coeff hsum).2.2 (indicatorIndex J)
  rw [← hFa] at hval
  have hfac : (YangMills.Construction.PowerSeries.MultiIndex.factorial (indicatorIndex J) : ℂ) ≠ 0 := by
    have : YangMills.Construction.PowerSeries.MultiIndex.factorial (indicatorIndex J) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _
    exact_mod_cast this
  have hm : partialOverFinset J (tupleMomentGeneratingFunction μ X) 0 = mom (indicatorIndex J) := by
    have h := (hAlpha (indicatorIndex J) J.sort (multiIndexSteps_indicatorIndex_perm J).symm).2
      (mem_univ 0)
    refine h.trans (hval.trans ?_)
    simp only [coeff]
    field_simp
  refine hm.trans ?_
  simp only [mom, finsetMoment, monomial_indicatorIndex]
  split_ifs with hJ0
  · subst hJ0
    simp [complexExpectation]
  · rfl
private theorem logMGFOnDomain_of
    (hSeries : ExponentialMomentSeriesExpansion)
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    (hJoint : CumulantAsPartial.MixedCumulantEqPartialOfLog)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i)) :
    LogMGFOnDomain μ X := by
  obtain ⟨-, -, -, -, hEnt, hF0, hUo, h0U, -, -⟩ := hSeries Ω μ n X hn hX
  have hEnt' : IsEntireFun (tupleMomentGeneratingFunction μ X) := hEnt
  have hO : IsOpen (logDomain μ X) := hUo
  obtain ⟨hPD, -, hChain, -, hLog, -⟩ := hTools n hn (logDomain μ X) hO
  obtain ⟨hPDuniv, -⟩ := hTools n hn univ isOpen_univ
  obtain ⟨hSlit, hLogDiff, hLogDeriv, hExpLog, hLog1, -, hDisc, -, -, -⟩ := hLog
  have hFU : IsHolomorphicScalar (logDomain μ X) (tupleMomentGeneratingFunction μ X) :=
    ((hPDuniv _ hEnt').2.2.2.2.2.2.2 _ hO (subset_univ _) _ (fun _ _ => rfl)).1
  have hmaps : MapsTo (tupleMomentGeneratingFunction μ X) (logDomain μ X)
      YangMills.Construction.ComplexVariables.nonpositiveRayComplement := fun z hz => hDisc hz
  obtain ⟨hL, hLpart⟩ := hChain _ _ logPrincipal hSlit hFU hmaps hLogDiff
  have hL' : IsHolomorphicScalar (logDomain μ X) (logMomentGeneratingFunction μ X) := hL
  obtain ⟨hmixed, hcum⟩ := hJoint Ω μ n X hn hX
  refine
    { isOpen := hO
      zero_mem := h0U
      holomorphic := hL'
      mgf_ne_zero := fun z hz h0 => ?_
      exp_log := fun z hz => hExpLog _ (hDisc hz)
      hasPartial := fun j => ((hPD _ hL').1 j).1
      partialDeriv_eq := fun j z hz => ?_
      hasMixedPartial := hmixed
      mixedCumulant_eq := hcum
      apply_zero := ?_ }
  · have h : ‖tupleMomentGeneratingFunction μ X z - 1‖ < 1 := hz
    rw [h0] at h
    simp at h
  · have h : partialDeriv j (logMomentGeneratingFunction μ X) z =
        deriv logPrincipal (tupleMomentGeneratingFunction μ X z) *
          partialDeriv j (tupleMomentGeneratingFunction μ X) z := hLpart j hz
    rw [h, hLogDeriv _ (hDisc hz)]
    ring
  · have h : tupleMomentGeneratingFunction μ X 0 = 1 := hF0
    change logPrincipal (tupleMomentGeneratingFunction μ X 0) = 0
    rw [h, hLog1]
private theorem tendsto_diffQuot_real {n : ℕ} {U : Set (ComplexCoordinates n)}
    {F g : ComplexCoordinates n → ℂ} {j : Fin n} (hF : HasPartialDeriv U F j)
    (hg : EqOn g F (U ∩ ComplexCoordinates.realLocus n)) {t : ComplexCoordinates n}
    (ht : t ∈ U ∩ ComplexCoordinates.realLocus n) :
    Tendsto (fun s : ℝ => diffQuot g t j s) (𝓝[≠] 0)
      (𝓝 (partialDeriv j F t)) := by
  obtain ⟨L, hL⟩ := hF.2 t ht.1
  have hlim : partialDeriv j F t = L := hL.limUnder_eq
  rw [hlim]
  have hcast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hcont : Tendsto (fun s : ℝ => t + (s : ℂ) • ComplexCoordinates.stdBasisVector j) (𝓝 0)
      (𝓝 t) := by
    have hc : Continuous fun s : ℝ => t + (s : ℂ) • ComplexCoordinates.stdBasisVector j := by
      fun_prop
    simpa using hc.tendsto 0
  have hnear : ∀ᶠ s : ℝ in 𝓝[≠] 0, t + (s : ℂ) • ComplexCoordinates.stdBasisVector j ∈ U :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually (hF.1.mem_nhds ht.1)
  refine (hL.comp hcast).congr' ?_
  filter_upwards [hnear] with s hs
  have hreal : t + (s : ℂ) • ComplexCoordinates.stdBasisVector j ∈
      ComplexCoordinates.realLocus n := by
    intro i
    have hi := ht.2 i
    by_cases h : i = j
    · subst h
      simp [ComplexCoordinates.stdBasisVector, hi]
    · simp [ComplexCoordinates.stdBasisVector, hi, h]
  simp only [Function.comp, diffQuot]
  rw [hg ⟨hs, hreal⟩, hg ht]
private theorem iteratedRealPartial_eq_iteratedPartials {n : ℕ} {U : Set (ComplexCoordinates n)}
    (hPD : ∀ F : ComplexCoordinates n → ℂ, IsHolomorphicScalar U F → PartialDerivProperties U F)
    (hOpenIn : YangMills.Construction.Matrices.ComplexMatrix2.IsRelativelyOpen
      (ComplexCoordinates.realLocus n) (U ∩ ComplexCoordinates.realLocus n))
    {F g : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar U F)
    (hg : EqOn g F (U ∩ ComplexCoordinates.realLocus n)) (l : List (Fin n)) :
    HasIteratedRealPartial (U ∩ ComplexCoordinates.realLocus n) l g ∧
      EqOn (iteratedRealPartial l g) (iteratedPartials l F) (U ∩ ComplexCoordinates.realLocus n) ∧
      IsHolomorphicScalar U (iteratedPartials l F) := by
  induction l with
  | nil => exact ⟨hOpenIn, hg, hF⟩
  | cons j l ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    obtain ⟨hj, hjh⟩ := (hPD _ h₃).1 j
    refine ⟨⟨h₁, hOpenIn, fun t ht => ⟨_, tendsto_diffQuot_real hj h₂ ht⟩⟩, fun t ht => ?_, hjh⟩
    exact (tendsto_diffQuot_real hj h₂ ht).limUnder_eq
private theorem cumulantViaRealLog_of
    (hSeries : ExponentialMomentSeriesExpansion)
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    (hExpect : YangMills.Construction.Probability.ExpectationBasicProperties)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i))
    (hLog : LogMGFOnDomain μ X) :
    CumulantViaRealLog μ X := by
  obtain ⟨-, hbd, hreal, -⟩ := hSeries Ω μ n X hn hX
  obtain ⟨-, ⟨-, hre, -, -⟩, hlow, -⟩ := hExpect Ω μ
  obtain ⟨hPD, -, -, -, hFacts, -⟩ := hTools n hn (logDomain μ X) hLog.isOpen
  have hLogReal := hFacts.2.2.2.2.2.1
  have hpos : ∀ t ∈ ComplexCoordinates.realLocus n,
      (tupleMomentGeneratingFunction μ X t).im = 0 ∧
        0 < (tupleMomentGeneratingFunction μ X t).re := by
    intro t ht
    have hct : t = fun i => (((t i).re : ℝ) : ℂ) :=
      funext fun i => Complex.ext (by simp) (by simpa using ht i)
    have hb : IsBoundedComplexRV
        (YangMills.Construction.ComplexVariables.expComp fun ω => ∑ i, t i * (X i ω : ℂ)) :=
      (hbd t).1
    have him : ∀ ω, (YangMills.Construction.ComplexVariables.expComp
        (fun ω => ∑ i, t i * (X i ω : ℂ)) ω).im = 0 := by
      intro ω
      have h := (hreal (fun i => (t i).re) ω).1
      rw [← hct] at h
      exact h
    have hlb : ∀ ω, Real.exp (-∑ i, |(t i).re| *
        YangMills.Construction.Probability.supModulus (fun ω => (X i ω : ℂ))) ≤
        (YangMills.Construction.ComplexVariables.expComp
          (fun ω => ∑ i, t i * (X i ω : ℂ)) ω).re := by
      intro ω
      have h := (hreal (fun i => (t i).re) ω).2
      rw [← hct] at h
      exact h
    have hu : IsBoundedRealRV fun ω => (YangMills.Construction.ComplexVariables.expComp
        (fun ω => ∑ i, t i * (X i ω : ℂ)) ω).re := by
      refine ⟨hb.measurable_re, ?_⟩
      obtain ⟨C, hC⟩ := hb.bounded
      exact ⟨C, fun ω => (Complex.abs_re_le_norm _).trans (hC ω)⟩
    have heq : (fun ω => (((YangMills.Construction.ComplexVariables.expComp
        (fun ω => ∑ i, t i * (X i ω : ℂ)) ω).re : ℝ) : ℂ))
        = YangMills.Construction.ComplexVariables.expComp fun ω => ∑ i, t i * (X i ω : ℂ) :=
      funext fun ω => Complex.ext (by simp) (by simpa using (him ω).symm)
    have h := hlow _ _ hu hlb
    rw [heq] at h
    exact ⟨hre _ hb him, lt_of_lt_of_le (Real.exp_pos _) h⟩
  have hOpenIn : YangMills.Construction.Matrices.ComplexMatrix2.IsRelativelyOpen
      (ComplexCoordinates.realLocus n) (logDomain μ X ∩ ComplexCoordinates.realLocus n) :=
    ⟨_, hLog.isOpen, rfl⟩
  have h0R : (0 : ComplexCoordinates n) ∈ ComplexCoordinates.realLocus n := fun j => by simp
  have hg : EqOn (realLogTupleMGF μ X) (logMomentGeneratingFunction μ X)
      (logDomain μ X ∩ ComplexCoordinates.realLocus n) := by
    intro t ht
    obtain ⟨h₁, h₂⟩ := hpos t ht.2
    have h := hLogReal _ h₂
    have hc : (((tupleMomentGeneratingFunction μ X t).re : ℝ) : ℂ) =
        tupleMomentGeneratingFunction μ X t :=
      Complex.ext (by simp) (by simpa using h₁.symm)
    rw [hc] at h
    exact h.symm
  have hturn := iteratedRealPartial_eq_iteratedPartials hPD hOpenIn hLog.holomorphic hg
    (List.finRange n)
  have hperm : (List.finRange n).Perm (Finset.univ : Finset (Fin n)).sort :=
    perm_finsetSort_of_nodup (List.nodup_finRange n) (by simp)
  have hsame := ((hPD _ hLog.holomorphic).2.2.2.2.1 Finset.univ _ hperm).2 hLog.zero_mem
  refine
    { pos := hpos
      isRelativelyOpen := hOpenIn
      zero_mem := ⟨hLog.zero_mem, h0R⟩
      hasPartials := hturn.1
      mixedCumulant_eq := ?_ }
  rw [hLog.mixedCumulant_eq, hturn.2.1 ⟨hLog.zero_mem, h0R⟩, hsame]
private theorem partialDeriv_comp_of_step {k n : ℕ} {p : Fin k → Fin n}
    {ι : ComplexCoordinates k → ComplexCoordinates n}
    (hι : ∀ (v : ComplexCoordinates k) (a : Fin k) (w : ℂ),
      ι (v + w • ComplexCoordinates.stdBasisVector a) =
        ι v + w • ComplexCoordinates.stdBasisVector (p a))
    {V : Set (ComplexCoordinates k)} (hV : IsOpen V) {G : ComplexCoordinates k → ℂ}
    {F : ComplexCoordinates n → ℂ} (hG : EqOn G (F ∘ ι) V) (a : Fin k) :
    EqOn (partialDeriv a G) (partialDeriv (p a) F ∘ ι) V := by
  intro v hv
  have hcont : Tendsto (fun w : ℂ => v + w • ComplexCoordinates.stdBasisVector a) (𝓝 0)
      (𝓝 v) := by
    have hc : Continuous fun w : ℂ => v + w • ComplexCoordinates.stdBasisVector a := by fun_prop
    simpa using hc.tendsto 0
  have hnear : ∀ᶠ w : ℂ in 𝓝[≠] 0, v + w • ComplexCoordinates.stdBasisVector a ∈ V :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually (hV.mem_nhds hv)
  have hq : diffQuot G v a =ᶠ[𝓝[≠] 0] diffQuot F (ι v) (p a) := by
    filter_upwards [hnear] with w hw
    simp only [diffQuot]
    rw [hG hw, hG hv, Function.comp, Function.comp, hι]
  simp only [partialDeriv, Function.comp, limUnder]
  rw [Filter.map_congr hq]
private theorem iteratedPartials_comp_of_step {k n : ℕ} {p : Fin k → Fin n}
    {ι : ComplexCoordinates k → ComplexCoordinates n}
    (hι : ∀ (v : ComplexCoordinates k) (a : Fin k) (w : ℂ),
      ι (v + w • ComplexCoordinates.stdBasisVector a) =
        ι v + w • ComplexCoordinates.stdBasisVector (p a))
    {V : Set (ComplexCoordinates k)} (hV : IsOpen V) {G : ComplexCoordinates k → ℂ}
    {F : ComplexCoordinates n → ℂ} (hG : EqOn G (F ∘ ι) V) (l : List (Fin k)) :
    EqOn (iteratedPartials l G) (iteratedPartials (l.map p) F ∘ ι) V := by
  induction l with
  | nil => exact hG
  | cons a l ih => exact partialDeriv_comp_of_step hι hV ih a
private def pushCoords {k n : ℕ} (p : Fin k → Fin n) (v : ComplexCoordinates k) :
    ComplexCoordinates n :=
  fun l => ∑ a, if p a = l then v a else 0
private theorem pushCoords_add_smul_basis {k n : ℕ} (p : Fin k → Fin n) (v : ComplexCoordinates k)
    (a : Fin k) (w : ℂ) :
    pushCoords p (v + w • ComplexCoordinates.stdBasisVector a) =
      pushCoords p v + w • ComplexCoordinates.stdBasisVector (p a) := by
  funext l
  have h : ∀ b, (if p b = l then (v + w • ComplexCoordinates.stdBasisVector a) b else 0) =
      (if p b = l then v b else 0) + w * (if b = a then (if p a = l then 1 else 0) else 0) := by
    intro b
    by_cases hb : b = a
    · subst hb
      by_cases hp : p b = l <;> simp [hp, ComplexCoordinates.stdBasisVector]
    · by_cases hp : p b = l <;> simp [hp, hb, ComplexCoordinates.stdBasisVector]
  have hs : pushCoords p (v + w • ComplexCoordinates.stdBasisVector a) l = pushCoords p v l +
      w * ∑ b, if b = a then (if p a = l then (1 : ℂ) else 0) else 0 := by
    simp only [pushCoords]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => h b
  rw [hs, Finset.sum_ite_eq']
  by_cases hp : p a = l
  · subst hp
    simp [ComplexCoordinates.stdBasisVector]
  · simp [ComplexCoordinates.stdBasisVector, hp, Ne.symm hp]
private theorem tupleMGF_reindex_eq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {k n : ℕ}
    (p : Fin k → Fin n) (X : Fin n → Ω → ℝ) :
    tupleMomentGeneratingFunction μ (fun a => X (p a)) =
      tupleMomentGeneratingFunction μ X ∘ pushCoords p := by
  funext v
  have h : ∀ ω, ∑ i, pushCoords p v i * (X i ω : ℂ) = ∑ a, v a * (X (p a) ω : ℂ) := by
    intro ω
    simp only [pushCoords, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ite_mul]
  simp only [tupleMomentGeneratingFunction, Function.comp, h]
private theorem finsetCumulantsAsPartials_of
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    (hJoint : CumulantAsPartial.MixedCumulantEqPartialOfLog)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hn : 1 ≤ n) (hX : ∀ i, IsBoundedRealRV (X i))
    (hLog : LogMGFOnDomain μ X)
    (hOpenOf : ∀ (k : ℕ) (Y : Fin k → Ω → ℝ), 1 ≤ k → (∀ i, IsBoundedRealRV (Y i)) →
      IsOpen (logDomain μ Y)) :
    FinsetCumulantsAsPartials μ X := by
  obtain ⟨hPD, -⟩ := hTools n hn (logDomain μ X) hLog.isOpen
  obtain ⟨-, -, hJ, -, hPerm, -, -, -⟩ := hPD _ hLog.holomorphic
  refine ⟨fun J _ => (hJ J).1, fun J hJ0 => ?_⟩
  have hk : 1 ≤ J.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ0)
  let p : Fin J.card → Fin n := J.orderEmbOfFin rfl
  have hY : ∀ a, IsBoundedRealRV (restrictTuple X J a) := fun a => hX _
  have hOpen : IsOpen (logDomain μ (restrictTuple X J)) := hOpenOf _ _ hk hY
  have hGam : tupleMomentGeneratingFunction μ (restrictTuple X J) =
      tupleMomentGeneratingFunction μ X ∘ pushCoords p := tupleMGF_reindex_eq μ p X
  have hG : EqOn (logMomentGeneratingFunction μ (restrictTuple X J))
      (logMomentGeneratingFunction μ X ∘ pushCoords p) (logDomain μ (restrictTuple X J)) := by
    intro v _
    simp only [logMomentGeneratingFunction, hGam, Function.comp]
  have hz : pushCoords p (0 : ComplexCoordinates J.card) = 0 := by
    funext l
    simp [pushCoords]
  have h0 : (0 : ComplexCoordinates J.card) ∈ logDomain μ (restrictTuple X J) := by
    simp only [logDomain, hGam, mem_ofPred_eq, Function.comp]
    rw [hz]
    exact hLog.zero_mem
  have hcum := (hJoint Ω μ J.card (restrictTuple X J) hk hY).2
  have hturn := iteratedPartials_comp_of_step (pushCoords_add_smul_basis p) hOpen hG
    (Finset.univ : Finset (Fin J.card)).sort h0
  have hperm : ((Finset.univ : Finset (Fin J.card)).sort.map p).Perm J.sort := by
    refine perm_finsetSort_of_nodup
      ((Finset.sort_nodup _ _).map (J.orderEmbOfFin rfl).injective) fun a => ?_
    rw [List.mem_map]
    refine ⟨fun ⟨b, _, hb⟩ => by subst hb; exact Finset.orderEmbOfFin_mem J rfl b, fun h => ?_⟩
    obtain ⟨b, hb⟩ : a ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact h
    exact ⟨b, by simp, hb⟩
  have hsame := (hPerm J _ hperm).2 hLog.zero_mem
  change mixedCumulant μ (restrictTuple X J) = _
  rw [hcum]
  change iteratedPartials _ _ 0 = _
  rw [hturn, Function.comp, hz, hsame]
private theorem tupleMGF_shiftTuple {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (c : Fin n → ℝ) (z : ComplexCoordinates n) :
    tupleMomentGeneratingFunction μ (shiftTuple X c) z =
      Complex.exp (realComplexPairing c z) * tupleMomentGeneratingFunction μ X z := by
  simp only [tupleMomentGeneratingFunction, complexExpectation,
    YangMills.Construction.ComplexVariables.expComp]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [← Complex.exp_add]
  congr 1
  simp only [shiftTuple, realComplexPairing, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
private theorem partialDeriv_realComplexPairing {n : ℕ} (c : Fin n → ℝ) (j : Fin n)
    (z : ComplexCoordinates n) :
    partialDeriv j (realComplexPairing c) z = c j := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w ≠ 0 := hw
  have h : realComplexPairing c (z + w • ComplexCoordinates.stdBasisVector j) =
      realComplexPairing c z + w * c j := by
    simp only [realComplexPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, ComplexCoordinates.stdBasisVector]
    congr 1
    simp [Pi.single_apply, mul_comm]
  simp only [diffQuot]
  rw [h]
  field_simp
  ring
private theorem shiftFormulas_of
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (c : Fin n → ℝ) (hn : 1 ≤ n)
    (hEnt : IsEntireFun (tupleMomentGeneratingFunction μ X))
    (hLog : LogMGFOnDomain μ X) (hLogS : LogMGFOnDomain μ (shiftTuple X c)) :
    ShiftFormulas μ X c := by
  have hO : IsOpen (logDomain μ X ∩ logDomain μ (shiftTuple X c)) :=
    hLog.isOpen.inter hLogS.isOpen
  obtain ⟨-, hSums, hChain, -, hFacts, -⟩ := hTools n hn univ isOpen_univ
  obtain ⟨hSlit, -, -, -, -, -, -, hExpDiff, hExpDeriv, hExpNe⟩ := hFacts
  have hdotEnt : IsEntireFun (realComplexPairing c) := by
    have h := hSums.2.2.2.2.2.2
      (∑ i, MvPolynomial.C (c i : ℂ) * MvPolynomial.X i)
    have he : (fun z : ComplexCoordinates n =>
        MvPolynomial.eval z (∑ i, MvPolynomial.C (c i : ℂ) * MvPolynomial.X i)) =
        realComplexPairing c := by
      funext z
      simp [realComplexPairing, map_sum]
    rwa [he] at h
  obtain ⟨hE, hEpart⟩ := hChain univ (realComplexPairing c) Complex.exp isOpen_univ hdotEnt
    (mapsTo_univ _ _) hExpDiff.differentiableOn
  have hprod := (hSums.2.2.2.2.1 _ _ hE hEnt 0 0).2.2
  refine
    { mgf_shift := tupleMGF_shiftTuple μ X c
      isOpen := hO
      zero_mem := ⟨hLog.zero_mem, hLogS.zero_mem⟩
      hasPartial_shift := fun j => ⟨hO, fun z hz => (hLogS.hasPartial j).2 z hz.2⟩
      hasPartial := fun j => ⟨hO, fun z hz => (hLog.hasPartial j).2 z hz.1⟩
      partialDeriv_shift := fun j z hz => ?_ }
  have hΓ : tupleMomentGeneratingFunction μ (shiftTuple X c) =
      fun z => (Complex.exp ∘ realComplexPairing c) z * tupleMomentGeneratingFunction μ X z :=
    funext (tupleMGF_shiftTuple μ X c)
  have hne := hLog.mgf_ne_zero z hz.1
  have hEne : Complex.exp (realComplexPairing c z) ≠ 0 := hExpNe _
  have hpart : partialDeriv j (tupleMomentGeneratingFunction μ (shiftTuple X c)) z =
      Complex.exp (realComplexPairing c z) * (c j : ℂ) * tupleMomentGeneratingFunction μ X z +
        Complex.exp (realComplexPairing c z) *
          partialDeriv j (tupleMomentGeneratingFunction μ X) z := by
    rw [hΓ]
    have h₁ : partialDeriv j
        (fun z => (Complex.exp ∘ realComplexPairing c) z * tupleMomentGeneratingFunction μ X z) z =
        partialDeriv j (Complex.exp ∘ realComplexPairing c) z *
            tupleMomentGeneratingFunction μ X z +
          Complex.exp (realComplexPairing c z) *
            partialDeriv j (tupleMomentGeneratingFunction μ X) z :=
      (hprod j).2 (mem_univ z)
    have h₂ : partialDeriv j (Complex.exp ∘ realComplexPairing c) z =
        deriv Complex.exp (realComplexPairing c z) * partialDeriv j (realComplexPairing c) z :=
      hEpart j (mem_univ z)
    rw [h₁, h₂, hExpDeriv, partialDeriv_realComplexPairing]
  rw [hLogS.partialDeriv_eq j z hz.2, hLog.partialDeriv_eq j z hz.1, hpart,
    tupleMGF_shiftTuple μ X c z]
  field_simp
private theorem shiftTuple_isBounded {Ω : Type} [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → ℝ)
    (c : Fin n → ℝ) (hX : ∀ i, IsBoundedRealRV (X i)) (i : Fin n) :
    IsBoundedRealRV (shiftTuple X c i) := by
  refine ⟨(hX i).measurable.add_const (c i), ?_⟩
  obtain ⟨C, hC⟩ := (hX i).bounded
  exact ⟨C + |c i|, fun ω => (abs_add_le _ _).trans (add_le_add_left (hC ω) _)⟩
theorem tupleMGFAndLogTheorem_holds (hSeries : ExponentialMomentSeriesExpansion)
    (hTools : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts)
    (hExpect : YangMills.Construction.Probability.ExpectationBasicProperties)
    (hJoint : CumulantAsPartial.MixedCumulantEqPartialOfLog) : TupleMGFAndLogTheorem := by
  intro Ω _ μ _ n X hn hX
  have h₁ := mgfEntireWithMoments_of hSeries hTools μ X hn hX
  have h₂ := logMGFOnDomain_of hSeries hTools hJoint μ X hn hX
  refine ⟨h₁, h₂, cumulantViaRealLog_of hSeries hTools hExpect μ X hn hX h₂,
    finsetCumulantsAsPartials_of hTools hJoint μ X hn hX h₂ (fun k Y hk hY => ?_), fun c => ?_⟩
  · exact (logMGFOnDomain_of hSeries hTools hJoint μ Y hk hY).isOpen
  · exact shiftFormulas_of hTools μ X c hn h₁.entire h₂
      (logMGFOnDomain_of hSeries hTools hJoint μ _ hn (shiftTuple_isBounded X c hX))
end YangMills.Construction.Cumulants.TupleLogMGF
