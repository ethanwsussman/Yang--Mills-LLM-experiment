import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.KernelsOfAFieldAreRealAtRealFieldsProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.StepKernelsNearOneOnASideProof
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheResponseOperators
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.Tower.ResponseOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.EntriesDets
open YangMills.Construction.PeriodicOperators.HomNorm
open YangMills.Construction.PeriodicOperators.SymbolCalculus
open YangMills.Construction.PeriodicOperators.StripSymbols
open YangMills.Construction.TorusMetric (l1NormVec)
open YangMills.Construction.Coordinates (ComplexCoordinates)
section Maps
variable {I I' I'' : PeriodicData}
theorem isUnit_of_isInvertibleQuotHom {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isUnit_of_isInvertibleQuotHom <;> assumption
theorem comp_quotHomInverse {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    M.comp (quotHomInverse M) = LinearMap.id :=
  Ring.mul_inverse_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) (isUnit_of_isInvertibleQuotHom h)
theorem quotHomInverse_conj {E X : QuotHom I I} (hE : IsInvertibleQuotHom E)
    (hX : IsInvertibleQuotHom X) :
    quotHomInverse ((quotHomInverse E).comp (X.comp E)) =
      (quotHomInverse E).comp ((quotHomInverse X).comp E) := by
  obtain ⟨u, hu⟩ := isUnit_of_isInvertibleQuotHom hE
  obtain ⟨v, hv⟩ := isUnit_of_isInvertibleQuotHom hX
  have e1 : quotHomInverse E = ((u⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ _) := by
    unfold quotHomInverse
    rw [← hu, Ring.inverse_unit]
  have e2 : quotHomInverse X = ((v⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ _) := by
    unfold quotHomInverse
    rw [← hv, Ring.inverse_unit]
  have e3 : (quotHomInverse E).comp (X.comp E) =
      (((u⁻¹ * (v * u)) : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ _) := by
    rw [e1, ← hv, ← hu]
    rfl
  rw [e3]
  unfold quotHomInverse
  rw [Ring.inverse_unit]
  have e4 : (quotHomInverse E).comp ((Ring.inverse (X : Module.End ℂ _)).comp E) =
      (((u⁻¹ * (v⁻¹ * u)) : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ _) := by
    have e2' : Ring.inverse (X : Module.End ℂ (I.UnitQuot → ℂ)) =
        ((v⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ _) := e2
    rw [e2', e1, ← hu]
    rfl
  have e5 : (u⁻¹ * (v * u))⁻¹ = u⁻¹ * (v⁻¹ * u) := by group
  rw [e5]
  exact e4.symm
theorem comp_conj {A A' : QuotHom I I'} {B B' : QuotHom I'' I} {E : QuotHom I I}
    {F : QuotHom I' I'} {G : QuotHom I'' I''} (hE : IsInvertibleQuotHom E)
    (hA : A' = F.comp (A.comp E)) (hB : B' = (quotHomInverse E).comp (B.comp G)) :
    A'.comp B' = F.comp ((A.comp B).comp G) := by
  rw [hA, hB]
  have e := comp_quotHomInverse hE
  apply LinearMap.ext
  intro f
  have := LinearMap.congr_fun e (B (G f))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this ⊢
  rw [this]
end Maps
section Symbols
variable {I I' : PeriodicData}
theorem mem_openImStrip_of_real {υ : ℝ} (hυ : 0 < υ) {κ : Fin 4 → ℂ} (h : κ ∈ realDualPoints) :
    κ ∈ openImStrip υ := by
  intro μ
  have : (κ μ).im = 0 := h μ
  simpa [this] using hυ
theorem isHolomorphicIn_mono {N N' : ℕ} {O O' : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (h : ComplexCoordinates.IsHolomorphicIn O f)
    (hO' : IsOpen O') (hs : O' ⊆ O) : ComplexCoordinates.IsHolomorphicIn O' f :=
  ⟨hO', h.2.1.mono hs, fun a ha => h.2.2 a (hs ha)⟩
theorem quotHomFamilyHolomorphicOn_mono {O O' : Set (ComplexCoordinates 4)}
    {M : ComplexCoordinates 4 → QuotHom I I'}
    (h : QuotHomFamilyHolomorphicOn O M) (hO' : IsOpen O') (hs : O' ⊆ O) :
    QuotHomFamilyHolomorphicOn O' M :=
  ⟨h.1, hO', fun e => isHolomorphicIn_mono (h.2.2 e) hO' hs⟩
theorem quotHomFamilyHolomorphicOn_congr {O : Set (ComplexCoordinates 4)}
    {M M' : ComplexCoordinates 4 → QuotHom I I'}
    (h : QuotHomFamilyHolomorphicOn O M) (e : ∀ κ ∈ O, M' κ = M κ) :
    QuotHomFamilyHolomorphicOn O M' := by
  refine ⟨h.1, h.2.1, fun c => ?_⟩
  obtain ⟨ho, hc, hd⟩ := h.2.2 c
  refine ⟨ho, hc.congr fun κ hκ => ?_, fun a ha j => ?_⟩
  · funext _
    simp only [e κ hκ]
  · have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O := by
      have hcont : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by
        fun_prop
      have : (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) 0 ∈ O := by simpa using ha
      exact hcont.continuousAt.eventually_mem (ho.mem_nhds this)
    have hnear2 : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ᶠ ζ' in 𝓝 ζ,
        a + ζ' • ComplexCoordinates.stdBasisVector j ∈ O := hnear.eventually_nhds
    filter_upwards [hd a ha j, hnear2] with ζ h1 h2
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [h2] with ζ' h3
    funext _
    simp only [e _ h3]
end Symbols
section Calculus
variable (hS : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
  (hE : EntriesDets.Claim)
  (hN : HomNorm.Claim)
variable {I I' I'' : PeriodicData}
include hS in
theorem symbolHom_holomorphic (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (he : FourierSymbolIsEntire I I' T) :
    QuotHomFamilyHolomorphicOn (univ : Set (ComplexCoordinates 4)) (symbolHom I I' T) := by
  refine ⟨by norm_num, isOpen_univ, ?_⟩
  rintro ⟨c', c⟩
  induction c' using Quot.ind with
  | mk ι' =>
    induction c using Quot.ind with
    | mk ι =>
      have e : (fun (κ : ComplexCoordinates 4) (_ : Fin 1) =>
            quotHomEntries (symbolHom I I' T κ) (Quot.mk _ ι', Quot.mk _ ι)) =
          fun κ _ => fourierSymbol I I' T κ ι' ι := by
        funext κ _
        exact ((hS.2.1 I I' hI hI').2.1 T κ hT (he.1 κ trivial)).carrierEntry_symbolHom ι' ι
      rw [e]
      exact (he.2 ι' ι).2
include hE in
theorem continuousOn_of_holomorphicOn (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {O : Set (ComplexCoordinates 4)} {M : ComplexCoordinates 4 → QuotHom I I'}
    (h : QuotHomFamilyHolomorphicOn O M) : QuotHomFamilyContinuousOn O M := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hE
  exact (h7 4 O (by norm_num) h.2.1).2.1 I I' hI hI' M h
include hC hN in
theorem symbolHom_boundedOn_imStrip (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (he : FourierSymbolIsEntire I I' T)
    (hcont : QuotHomFamilyContinuousOn (univ : Set (ComplexCoordinates 4)) (symbolHom I I' T))
    (υ : ℝ) :
    QuotHomFamilyBoundedOn (imStrip υ) (symbolHom I I' T) := by
  obtain ⟨-, -, -, -, hNP, -⟩ := hC I I' hI hI'
  obtain ⟨-, -, hcn, -, hbd, -⟩ := hN I I' hI hI'
  have hc : ContinuousOn (fun κ => (quotHomNorm (symbolHom I I' T κ)).toReal) univ :=
    hcn univ _ hcont
  let K : Set (Fin 4 → ℂ) := {κ | ∀ μ, |(κ μ).im| ≤ υ ∧ |(κ μ).re| ≤ Real.pi}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have e : K = ⋂ μ, {κ : Fin 4 → ℂ | |(κ μ).im| ≤ υ ∧ |(κ μ).re| ≤ Real.pi} := by
        ext κ
        simp [K]
      rw [e]
      refine isClosed_iInter fun μ => ?_
      have h1 : IsClosed {κ : Fin 4 → ℂ | |(κ μ).im| ≤ υ} :=
        isClosed_le (Complex.continuous_im.comp (continuous_apply μ)).abs continuous_const
      have h2 : IsClosed {κ : Fin 4 → ℂ | |(κ μ).re| ≤ Real.pi} :=
        isClosed_le (Complex.continuous_re.comp (continuous_apply μ)).abs continuous_const
      exact h1.inter h2
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨|υ| + Real.pi, fun κ hκ => ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
      intro μ
      obtain ⟨h1, h2⟩ := hκ μ
      calc ‖κ μ‖ ≤ |(κ μ).re| + |(κ μ).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ _ := by linarith [le_abs_self υ]
  obtain ⟨C, hCb⟩ := hKc.exists_bound_of_continuousOn (hc.mono (subset_univ K))
  refine (hbd _ (imStrip υ) (symbolHom I I' T)).1 ⟨C, fun κ hκ => ?_⟩
  let e : Fin 4 → ℤ := fun μ => round ((κ μ).re / (2 * Real.pi))
  let κ₀ : Fin 4 → ℂ := fun μ => κ μ - 2 * Real.pi * (e μ : ℂ)
  have hk : addTwoPiInt κ₀ e = κ := by
    funext μ
    simp [addTwoPiInt, κ₀]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hK0 : κ₀ ∈ K := by
    intro μ
    have hre : (κ₀ μ).re = (κ μ).re - 2 * Real.pi * (e μ : ℝ) := by
      simp [κ₀]
    have him : (κ₀ μ).im = (κ μ).im := by
      simp [κ₀]
    refine ⟨by rw [him]; exact hκ μ, ?_⟩
    rw [hre]
    have hr := abs_sub_round ((κ μ).re / (2 * Real.pi))
    have e1 : (κ μ).re - 2 * Real.pi * (e μ : ℝ) =
        2 * Real.pi * ((κ μ).re / (2 * Real.pi) - (e μ : ℝ)) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos hpi]
    have : |(κ μ).re / (2 * Real.pi) - (e μ : ℝ)| ≤ 1 / 2 := hr
    nlinarith
  have h1 := (hNP T hT κ₀ e (he.1 κ₀ trivial)).2
  rw [hk] at h1
  have h2 := hCb κ₀ hK0
  rw [h1]
  simpa using h2
include hC in
theorem norm_le_of_stripSymbol (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {υ : ℝ} (hυ : 0 < υ) {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {M : (Fin 4 → ℂ) → QuotHom I I'} (hM : IsStripSymbol I I' υ M)
    (hsym : ∀ κ ∈ openImStrip υ, SymbolSummableAt I I' T κ ∧ symbolHom I I' T κ = M κ) :
    ∃ c : ℝ, ∀ ι' ι,
      ‖T ι' ι‖ ≤ c * Real.exp (-υ * l1NormVec (I.pos ι - I'.pos ι')) := by
  obtain ⟨-, -, -, -, -, -, hStrip, -⟩ := hC I I' hI hI'
  have K := (hStrip υ hυ).2.1 M hM
  have hTM : T = matFunKernel I I' M :=
    K.unique T hT ⟨fun κ hκ => (hsym κ (mem_openImStrip_of_real hυ hκ)).1,
      fun κ hκ => (hsym κ (mem_openImStrip_of_real hυ hκ)).2⟩
  have hfin : Finite (I'.UnitQuot × I.UnitQuot) := by
    have := hI.finite_quot
    have := hI'.finite_quot
    infer_instance
  choose C hCb using hM.2.1
  obtain ⟨B, hB⟩ := Finite.bddAbove_range C
  have hall : ∀ κ ∈ imStrip υ, ∀ (ι' : I'.Carrier) (ι : I.Carrier),
      ‖carrierEntry (M κ) ι' ι‖ ≤ B := fun κ hκ ι' ι =>
    (hCb (I'.mkQuot 1 ι', I.mkQuot 1 ι) κ hκ).trans (hB ⟨_, rfl⟩)
  refine ⟨B, fun ι' ι => ?_⟩
  rw [hTM]
  refine (K.norm_le ι' ι).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  refine csSup_le ⟨_, ⟨0, ?_, rfl⟩⟩ ?_
  · intro μ
    simpa using hυ.le
  · rintro _ ⟨κ, hκ, rfl⟩
    exact hall κ hκ ι' ι
include hE in
theorem linearMapEntry_comp (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') [Fintype I.UnitQuot] (M : QuotHom I I') (M' : QuotHom I'' I)
    (c' : I'.UnitQuot) (c'' : I''.UnitQuot) :
    linearMapEntry (M.comp M') c' c'' = ∑ c, linearMapEntry M c' c * linearMapEntry M' c c'' := by
  rw [(hE.1 I I' I'' hI hI' hI'').2.2 M M' c' c'', finsum_eq_sum_of_fintype]
include hE in
theorem polynomialHolomorphic_of_isOpen {O : Set (ComplexCoordinates 4)} (hO : IsOpen O) :
    PolynomialHolomorphic 4 O := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hE
  exact (h7 4 O (by norm_num) hO).2.2.2.2.2.1
include hE in
theorem holomorphicOn_comp (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') {O : Set (ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → QuotHom I I'} {B : ComplexCoordinates 4 → QuotHom I'' I}
    (hA : QuotHomFamilyHolomorphicOn O A) (hB : QuotHomFamilyHolomorphicOn O B) :
    QuotHomFamilyHolomorphicOn O fun κ => (A κ).comp (B κ) := by
  have hO : IsOpen O := hA.2.1
  have P := polynomialHolomorphic_of_isOpen hE hO
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  refine ⟨by norm_num, hO, ?_⟩
  rintro ⟨c', c''⟩
  let e := Fintype.equivFin I.UnitQuot
  let u : Fin (Fintype.card I.UnitQuot) → ComplexCoordinates 4 → ℂ := fun i κ =>
    linearMapEntry (A κ) c' (e.symm i) * linearMapEntry (B κ) (e.symm i) c''
  have hu : ∀ i, HolomorphicFnOn O (u i) := by
    intro i
    have h2 := (P.2.2.1 2 ![fun κ => linearMapEntry (A κ) c' (e.symm i),
      fun κ => linearMapEntry (B κ) (e.symm i) c''] (by
        intro j
        fin_cases j
        · exact hA.2.2 (c', e.symm i)
        · exact hB.2.2 (e.symm i, c''))).2
    simpa [Fin.prod_univ_two, u] using h2
  have h3 := (P.2.2.1 _ u hu).1
  have e3 : (fun (κ : ComplexCoordinates 4) (_ : Fin 1) =>
        quotHomEntries ((A κ).comp (B κ)) (c', c'')) = fun κ _ => ∑ i, u i κ := by
    funext κ _
    show linearMapEntry ((A κ).comp (B κ)) c' c'' = _
    rw [linearMapEntry_comp hE hI hI' hI'']
    exact (Equiv.sum_comp e.symm (fun c => linearMapEntry (A κ) c' c * linearMapEntry (B κ) c c'')).symm
  rw [e3]
  exact h3
include hE in
theorem boundedOn_comp (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') {X : Type} {S : Set X}
    {A : X → QuotHom I I'} {B : X → QuotHom I'' I}
    (hA : QuotHomFamilyBoundedOn S A) (hB : QuotHomFamilyBoundedOn S B) :
    QuotHomFamilyBoundedOn S fun κ => (A κ).comp (B κ) := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  rintro ⟨c', c''⟩
  choose Ca hCa using fun c => hA (c', c)
  choose Cb hCb using fun c => hB (c, c'')
  refine ⟨∑ c, |Ca c| * |Cb c|, fun κ hκ => ?_⟩
  show ‖linearMapEntry ((A κ).comp (B κ)) c' c''‖ ≤ _
  rw [linearMapEntry_comp hE hI hI' hI'']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul]
  exact mul_le_mul ((hCa c κ hκ).trans (le_abs_self _)) ((hCb c κ hκ).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)
theorem linearMapEntry_sub (M M' : QuotHom I I') (c' : I'.UnitQuot) (c : I.UnitQuot) :
    linearMapEntry (M - M') c' c = linearMapEntry M c' c - linearMapEntry M' c' c := rfl
include hE in
theorem holomorphicOn_sub_const {O : Set (ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → QuotHom I I'}
    (B : QuotHom I I') (hA : QuotHomFamilyHolomorphicOn O A) :
    QuotHomFamilyHolomorphicOn O fun κ => A κ - B := by
  have hO : IsOpen O := hA.2.1
  have P := polynomialHolomorphic_of_isOpen hE hO
  refine ⟨by norm_num, hO, ?_⟩
  rintro ⟨c', c⟩
  have h2 := (P.2.2.1 2 ![fun κ => linearMapEntry (A κ) c' c, fun _ => -linearMapEntry B c' c] (by
      intro j
      fin_cases j
      · exact hA.2.2 (c', c)
      · exact P.2.1 _)).1
  have e3 : (fun (κ : ComplexCoordinates 4) (_ : Fin 1) => quotHomEntries (A κ - B) (c', c)) =
      fun κ _ => ∑ i : Fin 2, (![fun κ => linearMapEntry (A κ) c' c,
        fun _ => -linearMapEntry B c' c] : Fin 2 → ComplexCoordinates 4 → ℂ) i κ := by
    funext κ _
    show linearMapEntry (A κ - B) c' c = _
    rw [linearMapEntry_sub]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [e3]
  exact h2
theorem boundedOn_sub_const {X : Type} {S : Set X} {A : X → QuotHom I I'} (B : QuotHom I I')
    (hA : QuotHomFamilyBoundedOn S A) : QuotHomFamilyBoundedOn S fun κ => A κ - B := by
  rintro ⟨c', c⟩
  obtain ⟨C, hC⟩ := hA (c', c)
  refine ⟨C + ‖linearMapEntry B c' c‖, fun κ hκ => ?_⟩
  show ‖linearMapEntry (A κ - B) c' c‖ ≤ _
  rw [linearMapEntry_sub]
  have h : ‖linearMapEntry (A κ) c' c‖ ≤ C := hC κ hκ
  exact (norm_sub_le _ _).trans (by linarith)
end Calculus
section StripInverses
variable {I₀ I₁ : PeriodicData} (Ξ : I₀.Carrier → I₀.Carrier → ℂ) (Q : I₁.Carrier → I₀.Carrier → ℂ)
  (Qt : I₀.Carrier → I₁.Carrier → ℂ)
def covSymbolOf (κ : Fin 4 → ℂ) : QuotHom I₁ I₁ :=
  (symbolHom I₀ I₁ Q κ).comp
    ((quotHomInverse (symbolHom I₀ I₀ Ξ κ)).comp (symbolHom I₁ I₀ Qt κ))
def respSymbolOf (κ : Fin 4 → ℂ) : QuotHom I₁ I₀ :=
  (quotHomInverse (symbolHom I₀ I₀ Ξ κ)).comp
    ((symbolHom I₁ I₀ Qt κ).comp (quotHomInverse (covSymbolOf Ξ Q Qt κ)))
def defectSymbolOf (κ : Fin 4 → ℂ) : QuotHom I₁ I₁ :=
  quotHomInverse (covSymbolOf Ξ Q Qt κ) - LinearMap.id
def xiInvKernel : I₀.Carrier → I₀.Carrier → ℂ := periodicInverse I₀ Ξ
def covKernel : I₁.Carrier → I₁.Carrier → ℂ := compKernel (compKernel Q (xiInvKernel Ξ)) Qt
def covInvKernel : I₁.Carrier → I₁.Carrier → ℂ := periodicInverse I₁ (covKernel Ξ Q Qt)
def respKernel : I₀.Carrier → I₁.Carrier → ℂ :=
  compKernel (compKernel (xiInvKernel Ξ) Qt) (covInvKernel Ξ Q Qt)
def defectKernel : I₁.Carrier → I₁.Carrier → ℂ :=
  fun ι' ι => covInvKernel Ξ Q Qt ι' ι - idKernel I₁ ι' ι
structure StripInverseData (υ : ℝ) (O : Set (Fin 4 → ℂ)) : Prop where
  per₀ : IsPeriodic I₀
  per₁ : IsPeriodic I₁
  perXi : IsPeriodicKernel I₀ I₀ Ξ
  perQ : IsPeriodicKernel I₀ I₁ Q
  perQt : IsPeriodicKernel I₁ I₀ Qt
  entXi : FourierSymbolIsEntire I₀ I₀ Ξ
  entQ : FourierSymbolIsEntire I₀ I₁ Q
  entQt : FourierSymbolIsEntire I₁ I₀ Qt
  pos : 0 < υ
  isOpen_set : IsOpen O
  imStrip_sub : imStrip υ ⊆ O
  xi_inv : ∀ κ ∈ O, IsInvertibleQuotHom (symbolHom I₀ I₀ Ξ κ)
  cov_inv : ∀ κ ∈ O, IsInvertibleQuotHom (covSymbolOf Ξ Q Qt κ)
  xi_holo : QuotHomFamilyHolomorphicOn (O : Set (ComplexCoordinates 4))
    fun κ => quotHomInverse (symbolHom I₀ I₀ Ξ κ)
  cov_holo : QuotHomFamilyHolomorphicOn (O : Set (ComplexCoordinates 4))
    fun κ => quotHomInverse (covSymbolOf Ξ Q Qt κ)
  xi_bdd : QuotHomFamilyBoundedOn (imStrip υ) fun κ => quotHomInverse (symbolHom I₀ I₀ Ξ κ)
  cov_bdd : QuotHomFamilyBoundedOn (imStrip υ) fun κ => quotHomInverse (covSymbolOf Ξ Q Qt κ)
variable {Ξ Q Qt} {υ : ℝ} {O : Set (Fin 4 → ℂ)}
variable (hS : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
  (hE : EntriesDets.Claim)
  (hN : HomNorm.Claim)
theorem StripInverseData.openImStrip_sub (s : StripInverseData Ξ Q Qt υ O) : openImStrip υ ⊆ O :=
  fun _ hκ => s.imStrip_sub fun μ => (hκ μ).le
include hS in
theorem StripInverseData.interior_eq (s : StripInverseData Ξ Q Qt υ O) :
    openStripInterior υ = openImStrip υ := (hS.1 υ s.pos).1
include hS in
theorem StripInverseData.isOpen_openImStrip (s : StripInverseData Ξ Q Qt υ O) :
    IsOpen (openImStrip υ) :=
  (hS.1 υ s.pos).2.1
include hS hE in
theorem StripInverseData.cov_holomorphic (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyHolomorphicOn (O : Set (ComplexCoordinates 4)) (covSymbolOf Ξ Q Qt) := by
  have hQ := quotHomFamilyHolomorphicOn_mono (symbolHom_holomorphic hS s.per₀ s.per₁ s.perQ s.entQ)
    s.isOpen_set (subset_univ O)
  have hQt := quotHomFamilyHolomorphicOn_mono
    (symbolHom_holomorphic hS s.per₁ s.per₀ s.perQt s.entQt) s.isOpen_set (subset_univ O)
  exact holomorphicOn_comp hE s.per₀ s.per₁ s.per₁ hQ
    (holomorphicOn_comp hE s.per₀ s.per₀ s.per₁ s.xi_holo hQt)
include hS hE in
theorem StripInverseData.resp_holomorphic (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyHolomorphicOn (O : Set (ComplexCoordinates 4)) (respSymbolOf Ξ Q Qt) := by
  have hQt := quotHomFamilyHolomorphicOn_mono
    (symbolHom_holomorphic hS s.per₁ s.per₀ s.perQt s.entQt) s.isOpen_set (subset_univ O)
  exact holomorphicOn_comp hE s.per₀ s.per₀ s.per₁ s.xi_holo
    (holomorphicOn_comp hE s.per₁ s.per₀ s.per₁ hQt s.cov_holo)
include hE in
theorem StripInverseData.defect_holomorphic (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyHolomorphicOn (O : Set (ComplexCoordinates 4)) (defectSymbolOf Ξ Q Qt) :=
  holomorphicOn_sub_const hE _ s.cov_holo
include hS hC hE hN in
theorem StripInverseData.entire_bounded {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (he : FourierSymbolIsEntire I I' T) (υ : ℝ) :
    QuotHomFamilyBoundedOn (imStrip υ) (symbolHom I I' T) :=
  symbolHom_boundedOn_imStrip hC hN hI hI' hT he
    (continuousOn_of_holomorphicOn hE hI hI' (symbolHom_holomorphic hS hI hI' hT he)) υ
include hS hC hE hN in
theorem StripInverseData.cov_bounded (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyBoundedOn (imStrip υ) (covSymbolOf Ξ Q Qt) := by
  have hQ := StripInverseData.entire_bounded hS hC hE hN s.per₀ s.per₁ s.perQ s.entQ υ
  have hQt := StripInverseData.entire_bounded hS hC hE hN s.per₁ s.per₀ s.perQt s.entQt υ
  exact boundedOn_comp hE s.per₀ s.per₁ s.per₁ hQ (boundedOn_comp hE s.per₀ s.per₀ s.per₁ s.xi_bdd hQt)
include hS hC hE hN in
theorem StripInverseData.resp_bounded (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyBoundedOn (imStrip υ) (respSymbolOf Ξ Q Qt) := by
  have hQt := StripInverseData.entire_bounded hS hC hE hN s.per₁ s.per₀ s.perQt s.entQt υ
  exact boundedOn_comp hE s.per₀ s.per₀ s.per₁ s.xi_bdd
    (boundedOn_comp hE s.per₁ s.per₀ s.per₁ hQt s.cov_bdd)
theorem StripInverseData.defect_bounded (s : StripInverseData Ξ Q Qt υ O) :
    QuotHomFamilyBoundedOn (imStrip υ) (defectSymbolOf Ξ Q Qt) :=
  boundedOn_sub_const _ s.cov_bdd
include hS in
theorem StripInverseData.symbolHom_addTwoPiInt {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (he : FourierSymbolIsEntire I I' T) (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    symbolHom I I' T (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I' e)).comp
        ((symbolHom I I' T κ).comp (phaseMul I e)) :=
  ((hS.2.1 I I' hI hI').2.1 T κ hT (he.1 κ trivial)).symbolHom_addTwoPiInt e
include hC in
theorem StripInverseData.phaseMul_invertible {I : PeriodicData} (hI : IsPeriodic I) {υ : ℝ}
    (hυ : 0 < υ) (e : Fin 4 → ℤ) : IsInvertibleQuotHom (phaseMul I e : QuotHom I I) := by
  obtain ⟨-, -, -, -, -, -, hStrip, -⟩ := hC I I hI hI
  exact (hStrip υ hυ).1 e
include hS hC in
theorem StripInverseData.inner_addTwoPiInt (s : StripInverseData Ξ Q Qt υ O) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ imStrip υ) (e : Fin 4 → ℤ) :
    (quotHomInverse (symbolHom I₀ I₀ Ξ (addTwoPiInt κ e))).comp
        (symbolHom I₁ I₀ Qt (addTwoPiInt κ e)) =
      (quotHomInverse (phaseMul I₀ e)).comp
        (((quotHomInverse (symbolHom I₀ I₀ Ξ κ)).comp (symbolHom I₁ I₀ Qt κ)).comp
          (phaseMul I₁ e)) := by
  have hE₀ := StripInverseData.phaseMul_invertible hC s.per₀ s.pos e
  have hX := StripInverseData.symbolHom_addTwoPiInt hS s.per₀ s.per₀ s.perXi s.entXi κ e
  have hXi : quotHomInverse (symbolHom I₀ I₀ Ξ (addTwoPiInt κ e)) =
      (quotHomInverse (phaseMul I₀ e)).comp
        ((quotHomInverse (symbolHom I₀ I₀ Ξ κ)).comp (phaseMul I₀ e)) := by
    rw [hX]
    exact quotHomInverse_conj hE₀ (s.xi_inv κ (s.imStrip_sub hκ))
  exact comp_conj hE₀ hXi
    (StripInverseData.symbolHom_addTwoPiInt hS s.per₁ s.per₀ s.perQt s.entQt κ e)
include hS hC in
theorem StripInverseData.cov_addTwoPiInt (s : StripInverseData Ξ Q Qt υ O) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ imStrip υ) (e : Fin 4 → ℤ) :
    covSymbolOf Ξ Q Qt (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I₁ e)).comp
        ((covSymbolOf Ξ Q Qt κ).comp (phaseMul I₁ e)) :=
  comp_conj (StripInverseData.phaseMul_invertible hC s.per₀ s.pos e)
    (StripInverseData.symbolHom_addTwoPiInt hS s.per₀ s.per₁ s.perQ s.entQ κ e)
    (StripInverseData.inner_addTwoPiInt hS hC s hκ e)
include hS hC in
theorem StripInverseData.covInv_addTwoPiInt (s : StripInverseData Ξ Q Qt υ O) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ imStrip υ) (e : Fin 4 → ℤ) :
    quotHomInverse (covSymbolOf Ξ Q Qt (addTwoPiInt κ e)) =
      (quotHomInverse (phaseMul I₁ e)).comp
        ((quotHomInverse (covSymbolOf Ξ Q Qt κ)).comp (phaseMul I₁ e)) := by
  rw [StripInverseData.cov_addTwoPiInt hS hC s hκ e]
  exact quotHomInverse_conj (StripInverseData.phaseMul_invertible hC s.per₁ s.pos e)
    (s.cov_inv κ (s.imStrip_sub hκ))
include hS hC in
theorem StripInverseData.cov_quasi (s : StripInverseData Ξ Q Qt υ O) :
    IsQuasiPeriodic (imStrip υ) (covSymbolOf Ξ Q Qt) :=
  fun e _ hκ => StripInverseData.cov_addTwoPiInt hS hC s hκ e
include hS hC in
theorem StripInverseData.resp_quasi (s : StripInverseData Ξ Q Qt υ O) :
    IsQuasiPeriodic (imStrip υ) (respSymbolOf Ξ Q Qt) := by
  intro e κ hκ
  have hE₀ := StripInverseData.phaseMul_invertible hC s.per₀ s.pos e
  have hE₁ := StripInverseData.phaseMul_invertible hC s.per₁ s.pos e
  have hX := StripInverseData.symbolHom_addTwoPiInt hS s.per₀ s.per₀ s.perXi s.entXi κ e
  have hXi : quotHomInverse (symbolHom I₀ I₀ Ξ (addTwoPiInt κ e)) =
      (quotHomInverse (phaseMul I₀ e)).comp
        ((quotHomInverse (symbolHom I₀ I₀ Ξ κ)).comp (phaseMul I₀ e)) := by
    rw [hX]
    exact quotHomInverse_conj hE₀ (s.xi_inv κ (s.imStrip_sub hκ))
  have hQtC := comp_conj hE₁
    (StripInverseData.symbolHom_addTwoPiInt hS s.per₁ s.per₀ s.perQt s.entQt κ e)
    (StripInverseData.covInv_addTwoPiInt hS hC s hκ e)
  exact comp_conj hE₀ hXi hQtC
include hS hC in
theorem StripInverseData.defect_quasi (s : StripInverseData Ξ Q Qt υ O) :
    IsQuasiPeriodic (imStrip υ) (defectSymbolOf Ξ Q Qt) := by
  intro e κ hκ
  have hE₁ := StripInverseData.phaseMul_invertible hC s.per₁ s.pos e
  have hleft : (quotHomInverse (phaseMul I₁ e)).comp (phaseMul I₁ e) =
      LinearMap.id :=
    Ring.inverse_mul_cancel (phaseMul I₁ e : Module.End ℂ (I₁.UnitQuot → ℂ))
      (isUnit_of_isInvertibleQuotHom hE₁)
  show quotHomInverse (covSymbolOf Ξ Q Qt (addTwoPiInt κ e)) - LinearMap.id = _
  rw [StripInverseData.covInv_addTwoPiInt hS hC s hκ e]
  apply LinearMap.ext
  intro f
  have h1 := LinearMap.congr_fun hleft f
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  simp only [defectSymbolOf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, h1]
include hS hC hE hN in
theorem StripInverseData.cov_isStripSymbol (s : StripInverseData Ξ Q Qt υ O) :
    IsStripSymbol I₁ I₁ υ (covSymbolOf Ξ Q Qt) :=
  ⟨⟨O, s.isOpen_set, s.imStrip_sub,
      fun c' c => (StripInverseData.cov_holomorphic hS hE s).2.2 (c', c)⟩,
    StripInverseData.cov_bounded hS hC hE hN s, StripInverseData.cov_quasi hS hC s⟩
include hS hC hE hN in
theorem StripInverseData.resp_isStripSymbol (s : StripInverseData Ξ Q Qt υ O) :
    IsStripSymbol I₁ I₀ υ (respSymbolOf Ξ Q Qt) :=
  ⟨⟨O, s.isOpen_set, s.imStrip_sub,
      fun c' c => (StripInverseData.resp_holomorphic hS hE s).2.2 (c', c)⟩,
    StripInverseData.resp_bounded hS hC hE hN s, StripInverseData.resp_quasi hS hC s⟩
include hS hC hE in
theorem StripInverseData.defect_isStripSymbol (s : StripInverseData Ξ Q Qt υ O) :
    IsStripSymbol I₁ I₁ υ (defectSymbolOf Ξ Q Qt) :=
  ⟨⟨O, s.isOpen_set, s.imStrip_sub,
      fun c' c => (StripInverseData.defect_holomorphic hE s).2.2 (c', c)⟩,
    s.defect_bounded, StripInverseData.defect_quasi hS hC s⟩
end StripInverses
section Kernels
variable {I₀ I₁ : PeriodicData} {Ξ : I₀.Carrier → I₀.Carrier → ℂ} {Q : I₁.Carrier → I₀.Carrier → ℂ}
  {Qt : I₀.Carrier → I₁.Carrier → ℂ} {υ : ℝ} {O : Set (Fin 4 → ℂ)}
variable (hS : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
  (hE : EntriesDets.Claim)
  (hN : HomNorm.Claim)
theorem zero_mem_openImStrip (hυ : 0 < υ) : (0 : Fin 4 → ℂ) ∈ openImStrip υ := by
  intro μ
  simpa using hυ
include hS in
theorem StripInverseData.xiInvKernel_facts (s : StripInverseData Ξ Q Qt υ O) :
    IsPeriodicKernel I₀ I₀ (xiInvKernel Ξ) ∧ ∀ κ ∈ openImStrip υ,
      SymbolSummableAt I₀ I₀ (xiInvKernel Ξ) κ ∧
        symbolHom I₀ I₀ (xiInvKernel Ξ) κ = quotHomInverse (symbolHom I₀ I₀ Ξ κ) := by
  have hint := s.interior_eq hS
  have hholo : QuotHomFamilyHolomorphicOn (openStripInterior υ : Set (ComplexCoordinates 4))
      (symbolHom I₀ I₀ Ξ) :=
    quotHomFamilyHolomorphicOn_mono (symbolHom_holomorphic hS s.per₀ s.per₀ s.perXi s.entXi)
      (by rw [hint]; exact s.isOpen_openImStrip hS) (subset_univ _)
  obtain ⟨-, hp, -, -, -, -, hf, hv⟩ := hS.2.2.2 I₀ s.per₀ υ s.pos Ξ s.perXi
    (fun κ _ => s.entXi.1 κ trivial) hholo
    (fun κ hκ => s.xi_inv κ (s.openImStrip_sub (by rw [← hint]; exact hκ)))
  exact ⟨hp, fun κ hκ => ⟨hf κ (by rw [hint]; exact hκ), hv κ (by rw [hint]; exact hκ)⟩⟩
include hS in
theorem StripInverseData.covKernel_facts (s : StripInverseData Ξ Q Qt υ O) :
    IsPeriodicKernel I₁ I₁ (covKernel Ξ Q Qt) ∧ ∀ κ ∈ openImStrip υ,
      SymbolSummableAt I₁ I₁ (covKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₁ (covKernel Ξ Q Qt) κ = covSymbolOf Ξ Q Qt κ := by
  obtain ⟨hxp, hxf⟩ := StripInverseData.xiInvKernel_facts hS s
  have key : ∀ κ ∈ openImStrip υ,
      (∀ ι' ι, CompSummableAt (compKernel Q (xiInvKernel Ξ)) Qt ι' ι) ∧
      IsPeriodicKernel I₁ I₁ (covKernel Ξ Q Qt) ∧ SymbolSummableAt I₁ I₁ (covKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₁ (covKernel Ξ Q Qt) κ = covSymbolOf Ξ Q Qt κ := by
    intro κ hκ
    obtain ⟨-, hAp, hAf, hAe⟩ :=
      ((hS.2.1 I₀ I₁ s.per₀ s.per₁).2.1 Q κ s.perQ (s.entQ.1 κ trivial)).comp
        I₀ s.per₀ (xiInvKernel Ξ) hxp (hxf κ hκ).1
    obtain ⟨h1, hBp, hBf, hBe⟩ := ((hS.2.1 I₀ I₁ s.per₀ s.per₁).2.1 _ κ hAp hAf).comp
      I₁ s.per₁ Qt s.perQt (s.entQt.1 κ trivial)
    refine ⟨h1, hBp, hBf, ?_⟩
    refine hBe.trans ?_
    rw [hAe, (hxf κ hκ).2]
    rfl
  exact ⟨(key 0 (zero_mem_openImStrip s.pos)).2.1, fun κ hκ => (key κ hκ).2.2⟩
include hS hE in
theorem StripInverseData.covInvKernel_facts (s : StripInverseData Ξ Q Qt υ O) :
    IsPeriodicKernel I₁ I₁ (covInvKernel Ξ Q Qt) ∧ ∀ κ ∈ openImStrip υ,
      SymbolSummableAt I₁ I₁ (covInvKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₁ (covInvKernel Ξ Q Qt) κ = quotHomInverse (covSymbolOf Ξ Q Qt κ) := by
  have hint := s.interior_eq hS
  obtain ⟨hcp, hcf⟩ := StripInverseData.covKernel_facts hS s
  have hholo : QuotHomFamilyHolomorphicOn (openStripInterior υ : Set (ComplexCoordinates 4))
      (symbolHom I₁ I₁ (covKernel Ξ Q Qt)) := by
    rw [hint]
    exact quotHomFamilyHolomorphicOn_congr
      (quotHomFamilyHolomorphicOn_mono (StripInverseData.cov_holomorphic hS hE s)
        (s.isOpen_openImStrip hS) s.openImStrip_sub)
      fun κ hκ => (hcf κ hκ).2
  obtain ⟨-, hp, -, -, -, -, hf, hv⟩ := hS.2.2.2 I₁ s.per₁ υ s.pos (covKernel Ξ Q Qt) hcp
    (fun κ hκ => (hcf κ (by rw [← hint]; exact hκ)).1) hholo
    (fun κ hκ => by
      have hκ' : κ ∈ openImStrip υ := by rw [← hint]; exact hκ
      rw [(hcf κ hκ').2]
      exact s.cov_inv κ (s.openImStrip_sub hκ'))
  refine ⟨hp, fun κ hκ => ⟨hf κ (by rw [hint]; exact hκ), ?_⟩⟩
  rw [← (hcf κ hκ).2]
  exact hv κ (by rw [hint]; exact hκ)
include hS hE in
theorem StripInverseData.respKernel_facts (s : StripInverseData Ξ Q Qt υ O) :
    IsPeriodicKernel I₁ I₀ (respKernel Ξ Q Qt) ∧ ∀ κ ∈ openImStrip υ,
      SymbolSummableAt I₁ I₀ (respKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₀ (respKernel Ξ Q Qt) κ = respSymbolOf Ξ Q Qt κ := by
  obtain ⟨hxp, hxf⟩ := StripInverseData.xiInvKernel_facts hS s
  obtain ⟨hcp, hcf⟩ := StripInverseData.covInvKernel_facts hS hE s
  have key : ∀ κ ∈ openImStrip υ,
      IsPeriodicKernel I₁ I₀ (respKernel Ξ Q Qt) ∧ SymbolSummableAt I₁ I₀ (respKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₀ (respKernel Ξ Q Qt) κ = respSymbolOf Ξ Q Qt κ := by
    intro κ hκ
    obtain ⟨-, hAp, hAf, hAe⟩ :=
      ((hS.2.1 I₀ I₀ s.per₀ s.per₀).2.1 (xiInvKernel Ξ) κ hxp (hxf κ hκ).1).comp
        I₁ s.per₁ Qt s.perQt (s.entQt.1 κ trivial)
    obtain ⟨-, hBp, hBf, hBe⟩ := ((hS.2.1 I₁ I₀ s.per₁ s.per₀).2.1 _ κ hAp hAf).comp
      I₁ s.per₁ (covInvKernel Ξ Q Qt) hcp (hcf κ hκ).1
    refine ⟨hBp, hBf, hBe.trans ?_⟩
    rw [hAe, (hcf κ hκ).2, (hxf κ hκ).2]
    rfl
  exact ⟨(key 0 (zero_mem_openImStrip s.pos)).1, fun κ hκ => (key κ hκ).2⟩
include hS hC hE hN in
theorem StripInverseData.defectKernel_facts (s : StripInverseData Ξ Q Qt υ O) :
    IsPeriodicKernel I₁ I₁ (defectKernel Ξ Q Qt) ∧ ∀ κ ∈ openImStrip υ,
      SymbolSummableAt I₁ I₁ (defectKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₁ (defectKernel Ξ Q Qt) κ = defectSymbolOf Ξ Q Qt κ := by
  obtain ⟨hcp, hcf⟩ := StripInverseData.covInvKernel_facts hS hE s
  obtain ⟨-, -, -, -, -, -, -, hUnit, -⟩ := hC I₁ I₁ s.per₁ s.per₁
  have hid : IsPeriodicKernel I₁ I₁ (idKernel I₁) := (hUnit _ hcp).1
  have hform := (hS.2.1 I₁ I₁ s.per₁ s.per₁).1.identity
  have hone : linearMapOfEntries (quotOne I₁) = (LinearMap.id : QuotHom I₁ I₁) :=
    (hN I₁ I₁ s.per₁ s.per₁).2.2.2.2.2.2.2.1.1
  have hk : defectKernel Ξ Q Qt =
      StripSymbols.linCombKernel 1 (-1) (covInvKernel Ξ Q Qt) (idKernel I₁) := by
    funext ι' ι
    simp [defectKernel, StripSymbols.linCombKernel, sub_eq_add_neg]
  have key : ∀ κ ∈ openImStrip υ,
      IsPeriodicKernel I₁ I₁ (defectKernel Ξ Q Qt) ∧ SymbolSummableAt I₁ I₁ (defectKernel Ξ Q Qt) κ ∧
        symbolHom I₁ I₁ (defectKernel Ξ Q Qt) κ = defectSymbolOf Ξ Q Qt κ := by
    intro κ hκ
    obtain ⟨h1, h2, h3⟩ := ((hS.2.1 I₁ I₁ s.per₁ s.per₁).2.1 _ κ hcp (hcf κ hκ).1).linComb
      (idKernel I₁) hid (hform κ).1 1 (-1)
    rw [← hk] at h1 h2 h3
    refine ⟨h1, h2, h3.trans ?_⟩
    have e1 : symbolHom I₁ I₁ (idKernel I₁) κ = LinearMap.id := by
      have : symbolHom I₁ I₁ (idKernel I₁) κ =
          linearMapOfEntries (quotSymbol I₁ I₁ (idKernel I₁) κ) := rfl
      rw [this, (hform κ).2, hone]
    rw [e1, (hcf κ hκ).2, one_smul]
    apply LinearMap.ext
    intro f
    funext c
    simp [defectSymbolOf, sub_eq_add_neg]
  exact ⟨(key 0 (zero_mem_openImStrip s.pos)).1, fun κ hκ => (key κ hκ).2⟩
end Kernels
section Rate
variable {I I' : PeriodicData}
theorem hasDecayRate_of_stripSymbol (hC : SymbolCalculus.Claim) (hF : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {υ : ℝ} (hυ : 0 < υ) {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) {M : (Fin 4 → ℂ) → QuotHom I I'}
    (hM : IsStripSymbol I I' υ M)
    (hsym : ∀ κ ∈ openImStrip υ, SymbolSummableAt I I' T κ ∧ symbolHom I I' T κ = M κ) :
    HasDecayRate I I' T υ := by
  refine ⟨norm_le_of_stripSymbol hC hI hI' hυ hT hM hsym, fun κ hκ => (hsym κ hκ).1,
    fun κ hκ φ ι' => ?_⟩
  have hst := (hId I hI).2.2.2.2.2.1 I' hI' T hT
  obtain ⟨δ, hδ⟩ := hst.exists_rate
  have a := hst.withRate δ hδ
  have F := hF.1 I I' I hI hI' hI T (idKernel I) δ a.left_kernel a.left_rate
    a.right_kernel a.right_rate
  exact F.applyKernel_blochWave κ (hsym κ hκ).1 φ ι'
end Rate
section Colour
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.PlaneWaveCalculus (IsRealColourTrivial)
variable {σ σ' σ'' : Type}
theorem isRealColourTrivial_comp {T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    {S : KernelMatrix (Fin 3 × σ'') (Fin 3 × σ)}
    (hT : IsRealColourTrivial T)
    (hS : IsRealColourTrivial S)
    (hf : ∀ ι' ι'', CompSummableAt T S ι' ι'') :
    IsRealColourTrivial (compKernel T S) := by
  refine ⟨fun ι' ι'' => ?_, fun a a' y x hne => ?_, fun a a' y x => ?_⟩
  · have hs : Summable fun ι => T ι' ι * S ι ι'' := (hf ι' ι'').of_norm
    show (∑' ι, T ι' ι * S ι ι'').im = 0
    rw [Complex.im_tsum hs]
    simp [Complex.mul_im, hT.1, hS.1]
  · show ∑' ι, T (a', y) ι * S ι (a, x) = 0
    refine (tsum_congr fun ι => ?_).trans tsum_zero
    obtain ⟨b, z⟩ := ι
    by_cases hb : a' = b
    · subst hb
      rw [hS.2.1 a a' z x hne, mul_zero]
    · rw [hT.2.1 b a' y z hb, zero_mul]
  · show ∑' ι, T (a, y) ι * S ι (a, x) = ∑' ι, T (a', y) ι * S ι (a', x)
    rw [← (Equiv.prodCongr (Equiv.swap a a') (Equiv.refl σ)).tsum_eq
      (fun ι => T (a', y) ι * S ι (a', x))]
    refine tsum_congr fun ι => ?_
    obtain ⟨b, z⟩ := ι
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    by_cases hb : b = a
    · subst hb
      rw [Equiv.swap_apply_left, hT.2.2 b a' y z, hS.2.2 b a' z x]
    · have h1 : a' ≠ Equiv.swap a a' b := by
        intro h
        apply hb
        have := congrArg (Equiv.swap a a') h
        simpa using this.symm
      rw [hT.2.1 b a y z (Ne.symm hb), hT.2.1 _ a' y z h1, zero_mul, zero_mul]
theorem isRealColourTrivial_sub {T U : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    (hT : IsRealColourTrivial T)
    (hU : IsRealColourTrivial U) :
    IsRealColourTrivial fun ι' ι => T ι' ι - U ι' ι := by
  refine ⟨fun ι' ι => ?_, fun a a' y x hne => ?_, fun a a' y x => ?_⟩
  · simp [hT.1, hU.1]
  · simp [hT.2.1 a a' y x hne, hU.2.1 a a' y x hne]
  · simp only [hT.2.2 a a' y x, hU.2.2 a a' y x]
theorem isRealColourTrivial_id (L k j : ℕ) :
    IsRealColourTrivial (idKernel (colourEdges L k j) :
      KernelMatrix (Fin 3 × PosEdge L k j) (Fin 3 × PosEdge L k j)) := by
  refine ⟨fun ι' ι => ?_, fun a a' y x hne => ?_, fun a a' y x => ?_⟩
  · by_cases h : ι' = ι
    · have e : idKernel (colourEdges L k j) ι' ι = 1 := if_pos h
      rw [e]
      simp
    · have e : idKernel (colourEdges L k j) ι' ι = 0 := if_neg h
      rw [e]
      simp
  · exact if_neg fun e => hne (congrArg Prod.fst e)
  · by_cases h : y = x
    · have e1 : idKernel (colourEdges L k j) (a, y) (a, x) = 1 := if_pos (by rw [h])
      have e2 : idKernel (colourEdges L k j) (a', y) (a', x) = 1 := if_pos (by rw [h])
      exact e1.trans e2.symm
    · have e1 : idKernel (colourEdges L k j) (a, y) (a, x) = 0 :=
        if_neg fun e => h (congrArg Prod.snd e)
      have e2 : idKernel (colourEdges L k j) (a', y) (a', x) = 0 :=
        if_neg fun e => h (congrArg Prod.snd e)
      exact e1.trans e2.symm
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem eq_sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
theorem sum_smul_pauliFamily_mem_traceless (c : Fin 3 → ℂ) :
    ∑ a, c a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_smul_pauliFamily_mem_hermitianTraceless (c : Fin 3 → ℂ) (hc : ∀ a, (c a).im = 0) :
    ∑ a, c a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by
  refine Submodule.sum_mem _ fun a _ => ?_
  have e : c a • ComplexMatrix2.pauliFamily a = (c a).re • ComplexMatrix2.pauliFamily a := by
    ext i j
    have : c a = ((c a).re : ℂ) := by
      apply Complex.ext <;> simp [hc a]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    rw [← this]
  rw [e]
  exact Submodule.smul_mem _ _ (pauliFamily_mem_hermitianTraceless a)
theorem applyKernel_im_eq_zero {J J' : Type} {T : J' → J → ℂ} {f : J → ℂ} {ι' : J'}
    (hT : ∀ ι, (T ι' ι).im = 0) (hf : ∀ ι, (f ι).im = 0) (h : ApplySummableAt T f ι') :
    (applyKernel T f ι').im = 0 := by
  have hs : Summable fun ι => T ι' ι * f ι := h.of_norm
  show (∑' ι, T ι' ι * f ι).im = 0
  rw [Complex.im_tsum hs]
  simp [Complex.mul_im, hT, hf]
theorem mapsLieFormsToLieForms_of_isRealColourTrivial
    {T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    (hT : IsRealColourTrivial T) :
    MapsLieFormsToLieForms T := by
  intro f hf hform
  have hf' : ∀ b, f b ∈ ComplexMatrix2.hermitianTraceless := by
    simpa [GroupLieProduct.hermitianTracelessFunctions] using hf
  have hreal : ∀ ι, (toPauliCoeffs f ι).im = 0 := fun ι => pauliCoeff_im_eq_zero (hf' ι.2) ι.1
  simp only [GroupLieProduct.hermitianTracelessFunctions]
  rw [Submodule.mem_pi]
  intro b _
  exact sum_smul_pauliFamily_mem_hermitianTraceless _
    fun a => applyKernel_im_eq_zero (fun ι => hT.1 _ ι) hreal (hform (a, b))
end Colour
section Torus
open YangMills.Construction.Matrices
open YangMills.Construction.LocalKernels (projPositiveEdge)
open YangMills.Construction.LocalKernels.Periodisation (periodSide)
variable (hY : LocalKernels.Periodisation.PeriodisationHolds)
include hY in
theorem classFnsAreForms {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {n k j : ℕ}
    (hn : 0 < n) (hj : j ≤ k) : ClassFnsAreForms L n k j := by
  have hb := ((hY L hL k n hn).1 j hj).1 LocalKernels.CellType.edge
  have hsurj : Function.Surjective (projPositiveEdge L n k j) := hb.1
  have hiff : ∀ x y : PosEdge L k j,
      projPositiveEdge L n k j x = projPositiveEdge L n k j y ↔
        ∃ m : Fin 4 → ℤ, y = shiftEdge (periodSide L n • m) x := hb.2
  choose lift hlift using hsurj
  intro g
  let c : PositiveEdge L n k j → Fin 3 → ℂ := fun b a =>
    g ((colourEdges L k j).mkQuot (periodSide L n) (a, lift b))
  let f : PositiveEdge L n k j → ComplexMatrix2 := fun b => ∑ a, c b a • ComplexMatrix2.pauliFamily a
  have hclass : ∀ (a : Fin 3) (b : PosEdge L k j),
      (colourEdges L k j).mkQuot (periodSide L n)
          (a, lift (projPositiveEdge L n k j b)) =
        (colourEdges L k j).mkQuot (periodSide L n) (a, b) := by
    intro a b
    obtain ⟨m, hm⟩ := (hiff (lift (projPositiveEdge L n k j b)) b).1 (hlift _)
    exact Quot.sound ⟨m, congrArg (Prod.mk a) hm⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · simp only [GroupLieProduct.tracelessFunctions]
    rw [Submodule.mem_pi]
    intro b _
    exact sum_smul_pauliFamily_mem_traceless _
  · intro ι
    have h1 : toPauliCoeffs f (ι.1, projPositiveEdge L n k j ι.2) =
        c (projPositiveEdge L n k j ι.2) ι.1 := pauliCoeff_sum_smul _ _
    rw [h1]
    exact congrArg g (hclass ι.1 ι.2).symm
  · rintro f' ⟨hf'c, hf'⟩
    funext b
    have hmem : f' b ∈ ComplexMatrix2.traceless := by
      simp only [GroupLieProduct.tracelessFunctions] at hf'c
      rw [Submodule.mem_pi] at hf'c
      exact hf'c b trivial
    refine (eq_sum_pauliCoeff_smul hmem).trans (Finset.sum_congr rfl fun a _ => ?_)
    have h3 : g ((colourEdges L k j).mkQuot (periodSide L n) (a, lift b)) =
        pauliCoeff a (f' (projPositiveEdge L n k j (lift b))) := hf' (a, lift b)
    rw [hlift b] at h3
    rw [← h3]
include hY in
theorem periodicMatrix_preservesLieForms (hC : SymbolCalculus.Claim)
    (hQ : Quotients.QuotientTransposeNorm) {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {n k i j : ℕ} (hn : 0 < n) (hj : j ≤ k) (hIi : IsPeriodic (colourEdges L k i))
    (hIj : IsPeriodic (colourEdges L k j))
    {T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ}
    (hT : IsPeriodicKernel (colourEdges L k i) (colourEdges L k j) T)
    (hreal : ∀ ι' ι, (T ι' ι).im = 0) : PeriodicMatrixPreservesLieForms L n k i j T := by
  have hs : 0 < periodSide L n := by
    have hL0 : 0 < L := by
      have := hL.2
      omega
    exact Nat.mul_pos (by norm_num) (pow_pos hL0 n)
  obtain ⟨-, -, -, -, -, hTor, -⟩ := hC _ _ hIi hIj
  have hOT := (hTor _ hs).2 T hT
  refine ⟨hOT.summable, hOT.eq_of_mkQuot_eq, ?_⟩
  intro f hf g hg
  have hf' : ∀ b, f b ∈ ComplexMatrix2.hermitianTraceless := fun b => by
    simp only [GroupLieProduct.hermitianTracelessFunctions] at hf
    rw [Submodule.mem_pi] at hf
    exact hf b trivial
  have hfin : Finite ((colourEdges L k i).QuotMod (periodSide L n)) :=
    (hQ _ _ hIi hIj _ hs).1.2.1
  let F : (colourEdges L k i).Carrier → ℂ :=
    fun ι => g ((colourEdges L k i).mkQuot (periodSide L n) ι)
  have hbd : ∃ C : ℝ, ∀ ι, ‖F ι‖ ≤ C := by
    obtain ⟨C, hC'⟩ := Finite.bddAbove_range (fun c => ‖g c‖)
    exact ⟨C, fun ι => hC' ⟨_, rfl⟩⟩
  have hinv : IsSidePeriodic (colourEdges L k i) (periodSide L n) F :=
    fun m ι => congrArg g (Eq.symm (Quot.sound ⟨m, rfl⟩))
  have hFreal : ∀ ι, (F ι).im = 0 := fun ι => by
    have e : F ι = toPauliCoeffs f (ι.1, projPositiveEdge L n k i ι.2) := hg ι
    rw [e]
    exact pauliCoeff_im_eq_zero (hf' _) _
  obtain ⟨f', ⟨hf'c, hf'G⟩, -⟩ := classFnsAreForms hY hL hn hj
    (applyKernel (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n)) g)
  refine ⟨f', ?_, hf'G⟩
  simp only [GroupLieProduct.hermitianTracelessFunctions]
  rw [Submodule.mem_pi]
  intro b _
  have hmem : f' b ∈ ComplexMatrix2.traceless := by
    simp only [GroupLieProduct.tracelessFunctions] at hf'c
    rw [Submodule.mem_pi] at hf'c
    exact hf'c b trivial
  obtain ⟨bt, rfl⟩ := (((hY L hL k n hn).1 j hj).1 LocalKernels.CellType.edge).1 b
  rw [eq_sum_pauliCoeff_smul hmem]
  refine sum_smul_pauliFamily_mem_hermitianTraceless _ fun a => ?_
  have h4 : applyKernel (periodicMatrix (colourEdges L k i) (colourEdges L k j) T
        (periodSide L n)) g ((colourEdges L k j).mkQuot (periodSide L n) (a, bt)) =
      pauliCoeff a (f' (projPositiveEdge L n k j bt)) := hf'G (a, bt)
  have h5 := hOT.periodicMatrix_apply F hbd hinv g (fun ι => rfl) (a, bt)
  have h6 : pauliCoeff a (f' (projPositiveEdge L n k j bt)) =
      applyKernel T F (a, bt) := h4.symm.trans h5
  show (pauliCoeff a (f' (projPositiveEdge L n k j bt))).im = 0
  rw [h6]
  exact applyKernel_im_eq_zero (fun ι => hreal _ ι) hFreal (hOT.apply_summable F hbd hinv _)
end Torus
section Assembly
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.FreeStrip (edges topEdges)
open YangMills.Construction.Tower.BackgroundFieldResponse (xiInv blockCovariance blockCovarianceInv
  responseKernel responseDefect)
open YangMills.Construction.Tower.ResponseInverses (IsInverseRadius)
open YangMills.Construction.Tower.PlaneWaveCalculus (IsRealColourTrivial)
theorem quotHomFamilyBoundedOn_congr {I I' : PeriodicData} {S S' : Set (Fin 4 → ℂ)}
    {M M' : (Fin 4 → ℂ) → QuotHom I I'} (h : QuotHomFamilyBoundedOn S M) (hs : S' ⊆ S)
    (e : ∀ κ ∈ S', M' κ = M κ) : QuotHomFamilyBoundedOn S' M' := by
  intro c
  obtain ⟨C, hC⟩ := h c
  refine ⟨C, fun κ hκ => ?_⟩
  rw [e κ hκ]
  exact hC κ (hs hκ)
theorem exists_stripInverseData (hC : SymbolCalculus.Claim) (hT3 : TowerIndexSets.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {k : ℕ}
    (hk : 1 ≤ k) {δ₀ υ : ℝ} (hδ : 0 < δ₀) (hυ : IsInverseRadius δ₀ L k υ) :
    ∃ O, StripInverseData (I₀ := colourEdges L k 0) (I₁ := colourEdges L k k)
      (trivialRescaledOperators L k).Xi (trivialRescaledOperators L k).Q
      (trivialRescaledOperators L k).Qt υ O := by
  have i₀ := (hT3 L hL k 0 (Nat.zero_le k)).2.1
  have i₁ := (hT3 L hL k k le_rfl).2.1
  obtain ⟨hMaps, hFin⟩ := hFree.2 L hL k hk
  obtain ⟨O, hOo, hsO, hO⟩ := hυ.2.near
  have hQ := hMaps.edgeAverage.finite_range
  have hQt := hFin.edgeAverage_transpose
  have hXi := hFin.Xi
  exact ⟨O, i₀, i₁, hXi.1, hQ.1, hQt.1, (hC _ _ i₀ i₀).1 _ hXi.1 hXi.2.1,
    (hC _ _ i₀ i₁).1 _ hQ.1 hQ.2.1, (hC _ _ i₁ i₀).1 _ hQt.1 hQt.2.1,
    by linarith [hυ.1.1], hOo, hsO, hO.xi_isInvertible, hO.cov_isInvertible,
    hO.xi_holomorphic, hO.cov_holomorphic, hυ.2.xi_bounded, hυ.2.cov_bounded⟩
theorem claim_holds (hInv : ResponseInverses.Claim)
    (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hS : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
    (hF : Symbols.Claim) (hId : IdKernelFacts.Claim)
    (hE : EntriesDets.Claim)
    (hN : HomNorm.Claim) (hQ : Quotients.QuotientTransposeNorm)
    (hT3 : TowerIndexSets.Claim) (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hPW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hY : LocalKernels.Periodisation.PeriodisationHolds) :
    YangMills.Construction.Tower.ResponseOperators.Claim := by
  obtain ⟨δ₀, hδ, hall⟩ := hInv
  obtain ⟨-, -, δ₁, hδ₁, _, _, hIoc, -⟩ := hNum
  have hpos : 0 < δ₀ := by
    rw [Part.mem_unique hδ hδ₁]
    exact hIoc.1
  refine ⟨δ₀, hδ, fun L hL k hk => ?_⟩
  obtain ⟨hSF, ⟨υ₀, hυ₀⟩, hOps⟩ := hall L hL k hk
  have i₀ := (hT3 L hL k 0 (Nat.zero_le k)).2.1
  have i₁ := (hT3 L hL k k le_rfl).2.1
  obtain ⟨O₀, s₀⟩ := exists_stripInverseData hC hT3 hFree hL hk hpos hυ₀
  have hc := StripInverseData.covKernel_facts hS s₀
  have hr := StripInverseData.respKernel_facts hS hE s₀
  have hv := StripInverseData.defectKernel_facts hS hC hE hN s₀
  have hnum : ∀ υ, IsInverseRadius δ₀ L k υ → IsResponseRate δ₀ L k υ := by
    intro υ hυ
    obtain ⟨O, s⟩ := exists_stripInverseData hC hT3 hFree hL hk hpos hυ
    have hc' := StripInverseData.covKernel_facts hS s
    have hr' := StripInverseData.respKernel_facts hS hE s
    have hv' := StripInverseData.defectKernel_facts hS hC hE hN s
    exact ⟨hυ.1.1,
      hasDecayRate_of_stripSymbol hC hF hId i₁ i₁ s.pos hc'.1
        (StripInverseData.cov_isStripSymbol hS hC hE hN s) hc'.2,
      hasDecayRate_of_stripSymbol hC hF hId i₁ i₀ s.pos hr'.1
        (StripInverseData.resp_isStripSymbol hS hC hE hN s) hr'.2,
      hasDecayRate_of_stripSymbol hC hF hId i₁ i₁ s.pos hv'.1
        (StripInverseData.defect_isStripSymbol hS hC hE s) hv'.2⟩
  have hFR := (hPW L hL k hk).2.2.2.2.2.2.2.2.1
  have rQ : IsRealColourTrivial (trivialRescaledOperators L k).Q := hFR.Q.2
  have rQt : IsRealColourTrivial (trivialRescaledOperators L k).Qt := hFR.Qt.2
  have hcf := hOps.cov_formed
  have rC : IsRealColourTrivial (blockCovariance L k) :=
    isRealColourTrivial_comp (isRealColourTrivial_comp rQ hOps.xi_real hcf.left_pair) rQt
      hcf.left_assoc
  have hpq : ∀ ι' ι, CompSummableAt
      (compKernel (xiInv L k) (trivialRescaledOperators L k).Qt) (blockCovarianceInv L k) ι' ι := by
    have hcp := (StripInverseData.covInvKernel_facts hS hE s₀).1
    have hxp := (StripInverseData.xiInvKernel_facts hS s₀).1
    have h9 := (hC _ _ i₀ i₀).2.2.2.2.2.2.2.2 _ i₁
    have h10 := (hC _ _ i₁ i₀).2.2.2.2.2.2.2.2 _ i₁
    have hB := h9.1 _ _ hxp s₀.perQt
    exact (h10.1 _ _ hB.2 hcp).1
  have rH : IsRealColourTrivial (responseKernel L k) :=
    isRealColourTrivial_comp (isRealColourTrivial_comp hOps.xi_real rQt hcf.right_pair)
      hOps.cov_real hpq
  have rV : IsRealColourTrivial (responseDefect L k) :=
    isRealColourTrivial_sub hOps.cov_real (isRealColourTrivial_id L k k)
  have hopen := s₀.isOpen_openImStrip hS
  have hnear : ResponseSymbolsOn L k (openImStrip υ₀) := by
    have ecov : ∀ κ ∈ openImStrip υ₀, covSymbol L k κ =
        covSymbolOf (I₀ := colourEdges L k 0) (I₁ := colourEdges L k k)
          (trivialRescaledOperators L k).Xi (trivialRescaledOperators L k).Q
          (trivialRescaledOperators L k).Qt κ :=
      fun κ hκ => (hc.2 κ hκ).2
    have estrip : openImStrip υ₀ ⊆ imStrip υ₀ := fun κ hκ μ => (hκ μ).le
    exact
      { cov_summable := fun κ hκ => (hc.2 κ hκ).1
        resp_summable := fun κ hκ => (hr.2 κ hκ).1
        defect_summable := fun κ hκ => (hv.2 κ hκ).1
        xi_isInvertible := fun κ hκ => s₀.xi_inv κ (s₀.openImStrip_sub hκ)
        cov_isInvertible := fun κ hκ => by
          rw [ecov κ hκ]
          exact s₀.cov_inv κ (s₀.openImStrip_sub hκ)
        cov_eq := fun κ hκ => ecov κ hκ
        resp_eq := fun κ hκ => by
          rw [ecov κ hκ]
          exact (hr.2 κ hκ).2
        defect_eq := fun κ hκ => by
          rw [ecov κ hκ]
          exact (hv.2 κ hκ).2
        cov_holomorphic := quotHomFamilyHolomorphicOn_congr
          (quotHomFamilyHolomorphicOn_mono (StripInverseData.cov_holomorphic hS hE s₀) hopen
            s₀.openImStrip_sub) ecov
        resp_holomorphic := quotHomFamilyHolomorphicOn_congr
          (quotHomFamilyHolomorphicOn_mono (StripInverseData.resp_holomorphic hS hE s₀) hopen
            s₀.openImStrip_sub)
          fun κ hκ => (hr.2 κ hκ).2
        defect_holomorphic := quotHomFamilyHolomorphicOn_congr
          (quotHomFamilyHolomorphicOn_mono (StripInverseData.defect_holomorphic hE s₀) hopen
            s₀.openImStrip_sub)
          fun κ hκ => (hv.2 κ hκ).2
        cov_bounded := quotHomFamilyBoundedOn_congr
          (StripInverseData.cov_bounded hS hC hE hN s₀) estrip ecov
        resp_bounded := quotHomFamilyBoundedOn_congr
          (StripInverseData.resp_bounded hS hC hE hN s₀) estrip
          fun κ hκ => (hr.2 κ hκ).2
        defect_bounded := quotHomFamilyBoundedOn_congr s₀.defect_bounded estrip
          fun κ hκ => (hv.2 κ hκ).2 }
  exact
    { cov_periodic := hc.1
      resp_periodic := hr.1
      defect_periodic := hv.1
      free_summable := hSF
      near := ⟨openImStrip υ₀, hopen, fun κ hκ μ => (hκ μ).trans_lt hυ₀.1.1, hnear⟩
      exists_rate := ⟨υ₀, hnum υ₀ hυ₀⟩
      rate_of_inverseRadius := hnum
      cov_real := rC
      resp_real := rH
      defect_real := rV
      cov_lie := mapsLieFormsToLieForms_of_isRealColourTrivial rC
      resp_lie := mapsLieFormsToLieForms_of_isRealColourTrivial rH
      defect_lie := mapsLieFormsToLieForms_of_isRealColourTrivial rV
      torus_sides := fun n hn =>
        { forms_top := classFnsAreForms hY hL hn le_rfl
          forms_bottom := classFnsAreForms hY hL hn (Nat.zero_le k)
          cov := periodicMatrix_preservesLieForms hY hC hQ hL hn le_rfl i₁ i₁ hc.1 rC.1
          resp := periodicMatrix_preservesLieForms hY hC hQ hL hn (Nat.zero_le k) i₁ i₀ hr.1 rH.1
          defect := periodicMatrix_preservesLieForms hY hC hQ hL hn le_rfl i₁ i₁ hv.1 rV.1 } }
end Assembly
end YangMills.Construction.Tower.ResponseOperators
end
