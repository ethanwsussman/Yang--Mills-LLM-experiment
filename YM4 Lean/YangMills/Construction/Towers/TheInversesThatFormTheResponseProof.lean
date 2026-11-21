import YangMills.Construction.PeriodicOperators.CompositesAndInversesOfElementsOfHom
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZeroProof
import YangMills.Construction.PeriodicOperators.SandwichesOfARootedPairProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStripProof
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.TheInversesThatFormTheResponse
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseInverses
open PeriodicOperators
open PeriodicOperators.EntriesDets (HolomorphicFnOn)
def cubeSlab (s : ℝ) : Set (Fin 4 → ℂ) :=
  Set.pi univ fun _ => Complex.reProdIm (Icc (-Real.pi) Real.pi) (Icc (-s) s)
theorem isCompact_cubeSlab (s : ℝ) : IsCompact (cubeSlab s) :=
  isCompact_univ_pi fun _ => isCompact_Icc.reProdIm isCompact_Icc
theorem cubeSlab_subset_imStrip (s : ℝ) : cubeSlab s ⊆ imStrip s := by
  intro z hz ν
  have h := hz ν (mem_univ ν)
  rw [Complex.mem_reProdIm] at h
  exact abs_le.2 h.2
theorem addTwoPiInt_im (z : Fin 4 → ℂ) (n : Fin 4 → ℤ) (ν : Fin 4) :
    (addTwoPiInt z n ν).im = (z ν).im := by
  simp [addTwoPiInt]
theorem addTwoPiInt_addTwoPiInt_neg (z : Fin 4 → ℂ) (n : Fin 4 → ℤ) :
    addTwoPiInt (addTwoPiInt z n) (-n) = z := by
  funext ν
  simp [addTwoPiInt]
theorem addTwoPiInt_mem_imStrip {s : ℝ} {z : Fin 4 → ℂ} (h : z ∈ imStrip s) (n : Fin 4 → ℤ) :
    addTwoPiInt z n ∈ imStrip s := by apply _root_.YangMills.SharedProofs.p29809 <;> assumption
theorem addTwoPiInt_mem_openImStrip {s : ℝ} {z : Fin 4 → ℂ} (h : z ∈ openImStrip s)
    (n : Fin 4 → ℤ) : addTwoPiInt z n ∈ openImStrip s := fun ν => by
  rw [addTwoPiInt_im]
  exact h ν
theorem exists_addTwoPiInt_re_le_pi (z : Fin 4 → ℂ) :
    ∃ n : Fin 4 → ℤ, ∀ ν, |(addTwoPiInt z n ν).re| ≤ Real.pi := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.exists_abs_re_addTwoPiInt_le <;> assumption
theorem isOpen_openImStrip (s : ℝ) : IsOpen (openImStrip s) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
theorem imStrip_subset_openImStrip {a b : ℝ} (h : a < b) : imStrip a ⊆ openImStrip b :=
  fun _ hz ν => lt_of_le_of_lt (hz ν) h
theorem openImStrip_subset_imStrip (a : ℝ) : openImStrip a ⊆ imStrip a :=
  fun _ hz ν => (hz ν).le
theorem imStrip_mono {a b : ℝ} (h : a ≤ b) : imStrip a ⊆ imStrip b :=
  fun _ hz ν => (hz ν).trans h
theorem openImStrip_mono {a b : ℝ} (h : a ≤ b) : openImStrip a ⊆ openImStrip b :=
  fun _ hz ν => (hz ν).trans_le h
theorem exists_abs_le_abs_sub_le {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : |x| ≤ b) :
    ∃ y, |y| ≤ a ∧ |x - y| ≤ b - a := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  rcases le_total x (-a) with h | h
  · exact ⟨-a, by rw [abs_neg, abs_of_nonneg ha], by rw [abs_le]; constructor <;> linarith⟩
  · rcases le_total x a with h' | h'
    · exact ⟨x, abs_le.2 ⟨h, h'⟩, by simp; linarith⟩
    · exact ⟨a, by rw [abs_of_nonneg ha], by rw [abs_le]; constructor <;> linarith⟩
theorem exists_wider_imStrip_subset {U : Set (Fin 4 → ℂ)} (hU : IsOpen U) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hsub : imStrip a ⊆ U) (hinv : ∀ z ∈ U, ∀ n, addTwoPiInt z n ∈ U) :
    ∃ c, a < c ∧ c < b ∧ imStrip c ⊆ U := by
  obtain ⟨R, hR, hthick⟩ := (isCompact_cubeSlab a).exists_thickening_subset_open hU
    ((cubeSlab_subset_imStrip a).trans hsub)
  set m := min (b - a) R with hm
  have hm0 : 0 < m := lt_min (by linarith) hR
  have hmb : m ≤ b - a := min_le_left _ _
  have hmR : m ≤ R := min_le_right _ _
  refine ⟨a + m / 2, by linarith, by linarith, fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := exists_addTwoPiInt_re_le_pi z
  have hy : ∀ ν, ∃ y, |y| ≤ a ∧ |(z ν).im - y| ≤ a + m / 2 - a := fun ν =>
    exists_abs_le_abs_sub_le ha.le (by linarith) (hz ν)
  choose y hy1 hy2 using hy
  set p : Fin 4 → ℂ := fun ν => ⟨(addTwoPiInt z n ν).re, y ν⟩ with hp
  have hpK : p ∈ cubeSlab a := by
    intro ν _
    rw [Complex.mem_reProdIm]
    exact ⟨abs_le.1 (hn ν), abs_le.1 (hy1 ν)⟩
  have hnear : addTwoPiInt z n ∈ Metric.thickening R (cubeSlab a) := by
    refine Metric.mem_thickening_iff.2 ⟨p, hpK, ?_⟩
    refine (dist_pi_lt_iff hR).2 fun ν => ?_
    rw [Complex.dist_eq]
    have hw : addTwoPiInt z n ν - p ν = ⟨0, (z ν).im - y ν⟩ := by
      apply Complex.ext
      · simp [hp]
      · simp [hp, addTwoPiInt_im]
    rw [hw]
    have hnorm : ‖(⟨0, (z ν).im - y ν⟩ : ℂ)‖ = |(z ν).im - y ν| := by
      have : (⟨0, (z ν).im - y ν⟩ : ℂ) = (((z ν).im - y ν : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have := hy2 ν
    linarith
  have hzn := hinv _ (hthick hnear) (-n)
  rwa [addTwoPiInt_addTwoPiInt_neg] at hzn
section Hom
variable {I I' I'' : PeriodicData}
theorem quotHom_ext_linearMapEntry (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {A B : QuotHom I I'}
    (h : linearMapEntry A = linearMapEntry B) : A = B := by
  have h1 := (hE.1 I I' I hI hI' hI).1
  refine LinearMap.ext fun f => funext fun c' => ?_
  rw [h1 A f c', h1 B f c', h]
theorem linearMapOfEntries_linearMapEntry (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (A : QuotHom I I') :
    linearMapOfEntries (linearMapEntry A) = A := by
  refine quotHom_ext_linearMapEntry hE hI hI' ?_
  funext c' c
  exact ((hE.2.1 I I' hI hI').1 (linearMapEntry A)).2 c' c
theorem linearMapEntry_conjQuotHom (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (A : QuotHom I I') :
    linearMapEntry (conjQuotHom A) = Quotients.conjKernel (linearMapEntry A) := by
  funext c' c
  exact ((hE.2.1 I I' hI hI').1 _).2 c' c
theorem negConjPoint_eq_neg_star (z : Fin 4 → ℂ) : negConjPoint z = -star z := by
  funext ν
  simp [negConjPoint]
theorem quotHomNorm_phaseMul_le_one (hS : SymbolCalculus.Claim) (hI : IsPeriodic I)
    (n : Fin 4 → ℤ) : quotHomNorm (phaseMul I n : QuotHom I I) ≤ 1 := by
  have hu := (hS I I hI hI).2.2.2.1 n
  refine iSup₂_le fun f hf => ?_
  have hf' : wNorm (I.quotWeight 1) (phaseMul I n f) = wNorm (I.quotWeight 1) f := hu.2.2.2 f
  rw [hf']
  exact ENNReal.ofReal_le_one.2 hf.2.2
theorem quotHomNorm_phaseMul_inverse_le_one (hS : SymbolCalculus.Claim)
    (hC : CompInv.Claim) (hI : IsPeriodic I) (n : Fin 4 → ℤ) :
    quotHomNorm (quotHomInverse (phaseMul I n : QuotHom I I)) ≤ 1 := by
  have hu := (hS I I hI hI).2.2.2.1 n
  have hinv : IsInvertibleQuotHom (phaseMul I n : QuotHom I I) :=
    ((hC.1 I I I hI hI hI).2.1 n).1
  refine iSup₂_le fun f hf => ?_
  have hf' := hu.2.2.2 (quotHomInverse (phaseMul I n : QuotHom I I) f)
  rw [hinv.apply_quotHomInverse f] at hf'
  rw [← hf']
  exact ENNReal.ofReal_le_one.2 hf.2.2
theorem quotHomNorm_phaseConj_le (hS : SymbolCalculus.Claim) (hC : CompInv.Claim)
    (hN : HomNorm.Claim) (hI : IsPeriodic I) (hI' : IsPeriodic I') (n : Fin 4 → ℤ)
    (A : QuotHom I I') : quotHomNorm (phaseConj n A) ≤ quotHomNorm A := by
  have h1 := ((hN I' I' hI' hI').2.2.2.2.2.2.1 I hI).2
    (quotHomInverse (phaseMul I' n : QuotHom I' I'))
    (A.comp (phaseMul I n : QuotHom I I))
  have h2 := ((hN I I' hI hI').2.2.2.2.2.2.1 I hI).2 A (phaseMul I n : QuotHom I I)
  calc quotHomNorm (phaseConj n A)
      ≤ quotHomNorm (quotHomInverse (phaseMul I' n : QuotHom I' I')) *
          quotHomNorm (A.comp (phaseMul I n : QuotHom I I)) := h1
    _ ≤ 1 * (quotHomNorm A * 1) := by
        gcongr
        · exact quotHomNorm_phaseMul_inverse_le_one hS hC hI' n
        · exact h2.trans (by gcongr; exact quotHomNorm_phaseMul_le_one hS hI n)
    _ = quotHomNorm A := by simp
theorem boundedOn_imStrip_of_quasiPeriodic (hS : SymbolCalculus.Claim) (hC : CompInv.Claim)
    (hN : HomNorm.Claim) (hI : IsPeriodic I) (hI' : IsPeriodic I') {s : ℝ}
    {M : (Fin 4 → ℂ) → QuotHom I I'}
    (hc : QuotHomFamilyContinuousOn (n := 4) (imStrip s) M)
    (hq : ∀ z ∈ imStrip s, ∀ n, M (addTwoPiInt z n) = phaseConj n (M z)) :
    QuotHomFamilyBoundedOn (imStrip s) M := by
  have hNI := hN I I' hI hI'
  have hcn := hNI.2.2.1 (imStrip s) M hc
  obtain ⟨B, hB⟩ := (isCompact_cubeSlab s).exists_bound_of_continuousOn
    (hcn.mono (cubeSlab_subset_imStrip s))
  refine (hNI.2.2.2.2.1 _ (imStrip s) M).1 ⟨B, fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := exists_addTwoPiInt_re_le_pi z
  have hp : addTwoPiInt z n ∈ cubeSlab s := by
    intro ν _
    rw [Complex.mem_reProdIm]
    refine ⟨abs_le.1 (hn ν), ?_⟩
    rw [addTwoPiInt_im]
    exact abs_le.1 (hz ν)
  have hback := hq _ (addTwoPiInt_mem_imStrip hz n) (-n)
  rw [addTwoPiInt_addTwoPiInt_neg] at hback
  have hle : quotHomNorm (M z) ≤ quotHomNorm (M (addTwoPiInt z n)) := by
    rw [hback]
    exact quotHomNorm_phaseConj_le hS hC hN hI hI' _ _
  have hfin : quotHomNorm (M (addTwoPiInt z n)) ≠ ⊤ :=
    (hNI.1 (M (addTwoPiInt z n))).2.ne
  have h3 := hB _ hp
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h3
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono hfin hle).trans h3
theorem isOpen_setOf_isInvertible (hE : EntriesDets.Claim) (hI : IsPeriodic I)
    {S : Set (Fin 4 → ℂ)} (hSo : IsOpen S) {M : (Fin 4 → ℂ) → QuotHom I I}
    (hc : QuotHomFamilyContinuousOn (n := 4) S M) :
    IsOpen {z | z ∈ S ∧ IsInvertibleQuotHom (M z)} := by
  have hdet := (hE.2.2.1 I hI).2.1
  have := hI.finite_quot
  let q : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot := (Finite.equivFin I.UnitQuot).symm
  have hcont : ContinuousOn (fun z => (matrixOfEnum (M z) q).det) S := by
    have h1 : ContinuousOn (fun z => matrixOfEnum (M z) q) S := by
      refine continuousOn_pi.2 fun α => continuousOn_pi.2 fun β => ?_
      exact hc.2 (q α, q β)
    exact (continuous_id.matrix_det).comp_continuousOn h1
  have hset : {z | z ∈ S ∧ IsInvertibleQuotHom (M z)} =
      S ∩ (fun z => (matrixOfEnum (M z) q).det) ⁻¹' {0}ᶜ := by
    ext z
    have h1 := (hdet (M z)).1 q
    have h2 := (hdet (M z)).2.2.2
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
    rw [h1, h2]
  rw [hset]
  exact hcont.isOpen_inter_preimage hSo isOpen_compl_singleton
theorem holomorphicOn_mono {O O' : Set (Fin 4 → ℂ)} (hO' : IsOpen O') (hsub : O' ⊆ O)
    {M : (Fin 4 → ℂ) → QuotHom I I'} (h : QuotHomFamilyHolomorphicOn (n := 4) O M) :
    QuotHomFamilyHolomorphicOn (n := 4) O' M :=
  ⟨h.1, hO', fun p => ⟨hO', (h.2.2 p).2.1.mono hsub, fun a ha => (h.2.2 p).2.2 a (hsub ha)⟩⟩
theorem continuousOn_of_holomorphicOn (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {O : Set (Fin 4 → ℂ)}
    {M : (Fin 4 → ℂ) → QuotHom I I'} (h : QuotHomFamilyHolomorphicOn (n := 4) O M) :
    QuotHomFamilyContinuousOn (n := 4) O M :=
  ((hE.2.2.2.2.2.2.1 4 O (by norm_num) h.2.1).2.1 I I' hI hI') M h
theorem holomorphicOn_comp (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {O : Set (Fin 4 → ℂ)} {A : (Fin 4 → ℂ) → QuotHom I I'} {B : (Fin 4 → ℂ) → QuotHom I'' I}
    (hA : QuotHomFamilyHolomorphicOn (n := 4) O A) (hB : QuotHomFamilyHolomorphicOn (n := 4) O B) :
    QuotHomFamilyHolomorphicOn (n := 4) O fun z => (A z).comp (B z) := by apply _root_.YangMills.Construction.PeriodicOperators.RootedSandwiches.familyHolomorphicOn_comp <;> assumption
theorem exists_wider_imStrip_inverse (hE : EntriesDets.Claim) (hS : SymbolCalculus.Claim)
    (hC : CompInv.Claim) (hN : HomNorm.Claim) (hI : IsPeriodic I) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {M : (Fin 4 → ℂ) → QuotHom I I}
    (hh : QuotHomFamilyHolomorphicOn (n := 4) (openImStrip b) M)
    (hq : ∀ z ∈ openImStrip b, ∀ n, M (addTwoPiInt z n) = phaseConj n (M z))
    (hi : ∀ z ∈ imStrip a, IsInvertibleQuotHom (M z)) :
    ∃ c, a < c ∧ c < b ∧ (∀ z ∈ imStrip c, IsInvertibleQuotHom (M z)) ∧
      QuotHomFamilyBoundedOn (imStrip c) (fun z => quotHomInverse (M z)) ∧
      QuotHomFamilyHolomorphicOn (n := 4) (openImStrip c) fun z => quotHomInverse (M z) := by
  have hcont := continuousOn_of_holomorphicOn hE hI hI hh
  have hphase := (hC.1 I I I hI hI hI).2.1
  have hU := isOpen_setOf_isInvertible hE hI (isOpen_openImStrip b) hcont
  obtain ⟨c, hac, hcb, hsub⟩ := exists_wider_imStrip_subset hU ha hab
    (fun z hz => ⟨imStrip_subset_openImStrip hab hz, hi z hz⟩)
    (fun z hz n => ⟨addTwoPiInt_mem_openImStrip hz.1 n, by
      rw [hq z hz.1 n]
      exact ((hphase n).2.2.2.2 _ hz.2).1⟩)
  have hinv : ∀ z ∈ imStrip c, IsInvertibleQuotHom (M z) := fun z hz => (hsub hz).2
  have hcb' : imStrip c ⊆ openImStrip b := fun z hz => (hsub hz).1
  have hmaps := (hE.2.2.1 I hI).2.2.1 (imStrip c) M hinv
  have hcont' : QuotHomFamilyContinuousOn (n := 4) (imStrip c) M :=
    ⟨hcont.1, fun p => (hcont.2 p).mono hcb'⟩
  refine ⟨c, hac, hcb, hinv, ?_, ?_⟩
  · refine boundedOn_imStrip_of_quasiPeriodic hS hC hN hI hI (hmaps.1 hcont') fun z hz n => ?_
    rw [hq z (hcb' hz) n]
    exact ((hphase n).2.2.2.2 _ (hinv z hz)).2
  · have hsubo : openImStrip c ⊆ openImStrip b :=
      (openImStrip_subset_imStrip c).trans hcb'
    have hinvo : ∀ w ∈ openImStrip c, IsInvertibleQuotHom (M w) :=
      fun w hw => hinv w (openImStrip_subset_imStrip c hw)
    exact ((hE.2.2.1 I hI).2.2.1 (openImStrip c) M hinvo).2
      (isOpen_openImStrip c) (holomorphicOn_mono (isOpen_openImStrip c) hsubo hh)
end Hom
section Colour
variable {L k j j' : ℕ}
theorem fourierSymbol_isColourTrivial
    {T : (colourEdges L k j').Carrier → (colourEdges L k j).Carrier → ℂ}
    (hT : Tower.IsColourTrivial (σ := PeriodicOperators.PosEdge L k j)
      (σ' := PeriodicOperators.PosEdge L k j') T)
    (z : Fin 4 → ℂ) :
    Tower.IsColourTrivial (σ := PeriodicOperators.PosEdge L k j)
      (σ' := PeriodicOperators.PosEdge L k j')
      (fourierSymbol (colourEdges L k j) (colourEdges L k j') T z) := by
  refine ⟨fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · have hz : ∀ n, symbolSummand (colourEdges L k j) (colourEdges L k j') T z (a', y) (a, x) n = 0 :=
      fun n => by
        have h0 : T (a', y) (a, shiftEdge n x) = 0 := hT.1 a a' y _ h
        exact mul_eq_zero_of_left h0 _
    exact (tsum_congr hz).trans tsum_zero
  · refine tsum_congr fun n => ?_
    have h0 : T (a, y) (a, shiftEdge n x) = T (a', y) (a', shiftEdge n x) :=
      hT.2 a a' y _
    exact congrArg₂ (· * ·) h0 rfl
theorem isColourTrivial_of_carrierEntry {M : QuotHom (colourEdges L k j) (colourEdges L k j')}
    {F : (colourEdges L k j').Carrier → (colourEdges L k j).Carrier → ℂ}
    (hM : ∀ ι' ι, carrierEntry M ι' ι = F ι' ι)
    (hF : Tower.IsColourTrivial (σ := PeriodicOperators.PosEdge L k j)
      (σ' := PeriodicOperators.PosEdge L k j') F) :
    PeriodicOperators.IsColourTrivial (L := L) (k := k) (j := j) (j' := j') (t := .edge)
      (t' := .edge) M :=
  ⟨fun a a' y x h => (hM (a', y) (a, x)).trans (hF.1 a a' y x h),
    fun a a' y x => ((hM (a, y) (a, x)).trans (hF.2 a a' y x)).trans (hM (a', y) (a', x)).symm⟩
theorem matFunKernel_isColourTrivial
    {M : (Fin 4 → ℂ) → QuotHom (colourEdges L k j) (colourEdges L k j')}
    (hM : ∀ z ∈ realDualPoints, PeriodicOperators.IsColourTrivial (L := L) (k := k) (j := j)
      (j' := j') (t := .edge) (t' := .edge) (M z)) :
    Tower.IsColourTrivial (σ := PeriodicOperators.PosEdge L k j)
      (σ' := PeriodicOperators.PosEdge L k j')
      (matFunKernel (colourEdges L k j) (colourEdges L k j') M) := by
  have hreal : ∀ θ : InfiniteLattice.AmbientSpace, toComplexVec θ ∈ realDualPoints :=
    fun θ ν => by simp [toComplexVec]
  refine ⟨fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · have hz : matFunIntegrand (colourEdges L k j) (colourEdges L k j') M (a', y) (a, x) =
        fun _ => 0 := by
      funext θ
      have h0 : carrierEntry (M (toComplexVec θ)) ((a', y) : (colourEdges L k j').Carrier)
          ((a, x) : (colourEdges L k j).Carrier) = 0 := (hM _ (hreal θ)).1 a a' y x h
      exact mul_eq_zero_of_left h0 _
    change torusAverage (matFunIntegrand (colourEdges L k j) (colourEdges L k j') M
      (a', y) (a, x)) = 0
    rw [hz]
    simp [torusAverage]
  · have he : matFunIntegrand (colourEdges L k j) (colourEdges L k j') M (a, y) (a, x) =
        matFunIntegrand (colourEdges L k j) (colourEdges L k j') M (a', y) (a', x) := by
      funext θ
      have h0 : carrierEntry (M (toComplexVec θ)) ((a, y) : (colourEdges L k j').Carrier)
          ((a, x) : (colourEdges L k j).Carrier) =
          carrierEntry (M (toComplexVec θ)) ((a', y) : (colourEdges L k j').Carrier)
            ((a', x) : (colourEdges L k j).Carrier) := (hM _ (hreal θ)).2 a a' y x
      exact congrArg₂ (· * ·) h0 rfl
    change torusAverage (matFunIntegrand (colourEdges L k j) (colourEdges L k j') M
      (a, y) (a, x)) = torusAverage (matFunIntegrand (colourEdges L k j)
        (colourEdges L k j') M (a', y) (a', x))
    rw [he]
end Colour
section Symbols
variable {I I' : PeriodicData}
theorem symbolHom_holomorphicOn (hO : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hent : FourierSymbolIsEntire I I' T) :
    QuotHomFamilyHolomorphicOn (n := 4) univ (symbolHom I I' T) := by apply _root_.YangMills.Construction.PeriodicOperators.RootedSandwiches.symbolHom_holomorphicOn_univ <;> assumption
theorem symbolHom_isSymmetricFamilyOn (hE : EntriesDets.Claim) (hS : SymbolCalculus.Claim)
    (hO : StripSymbols.Claim) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hent : FourierSymbolIsEntire I I' T) (hreal : ∀ ι' ι, (T ι' ι).im = 0) :
    IsSymmetricFamilyOn univ (symbolHom I I' T) := by
  intro z _
  have hf := hent.1 z (mem_univ z)
  refine ⟨?_, fun n => ((hO.2.1 I I' hI hI').2.1 T z hT hf).symbolHom_addTwoPiInt n⟩
  have h := ((hS I I' hI hI').2.2.1 T hT hreal z hf).2.2.2
  rw [negConjPoint_eq_neg_star, conjQuotHom, h, linearMapOfEntries_linearMapEntry hE hI hI']
end Symbols
open FreeStrip (edges topEdges addScalar symbolAddScalar)
open FreeResolvents (trivialRescaledOperators)
open BackgroundFieldResponse (xiInv blockCovariance blockCovarianceInv)
theorem addScalar_zero (I : PeriodicData) (A : I.Carrier → I.Carrier → ℂ) : addScalar I 0 A = A := by
  funext ι' ι
  simp [addScalar]
theorem symbolAddScalar_zero (I : PeriodicData) (A : I.Carrier → I.Carrier → ℂ) (z : Fin 4 → ℂ) :
    symbolAddScalar I 0 A z = symbolHom I I A z := by
  simp [symbolAddScalar]
theorem claim_at_height (hIdx : TowerIndexSets.Claim) (hS : SymbolCalculus.Claim)
    (hO : StripSymbols.Claim) (hF : FreeOperators.FreeOperatorsArePeriodic)
    (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hE : EntriesDets.Claim)
    (hN : HomNorm.Claim) (hC : CompInv.Claim)
    {δ₀ C₀ : ℝ} (hδ : δ₀ ∈ Ioc (0 : ℝ) (1 / 64)) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hA : FreeStrip.StripBounds L k δ₀ C₀) :
    SymbolsSummable L k ∧ (∃ υ, IsInverseRadius δ₀ L k υ) ∧ OperatorInverses L k := by
  have hI : IsPeriodic (edges L k) := (hIdx L hL k 0 (Nat.zero_le k)).2.1
  have hI' : IsPeriodic (topEdges L k) := (hIdx L hL k k le_rfl).2.1
  have hFree := hF.2 L hL k hk
  have hXi : FreeOperators.HasFiniteRangeEveryRate (edges L k) (edges L k)
      (trivialRescaledOperators L k).Xi := hFree.2.Xi
  have hQ : FreeOperators.HasFiniteRangeEveryRate (edges L k) (topEdges L k)
      (trivialRescaledOperators L k).Q := hFree.1.edgeAverage.finite_range
  have hQt : FreeOperators.HasFiniteRangeEveryRate (topEdges L k) (edges L k)
      (trivialRescaledOperators L k).Qt := hFree.2.edgeAverage_transpose
  have hReal := (hW L hL k hk).2.2.2.2.2.2.2.2.1
  have rXi := hReal.Xi.2
  have rQ := hReal.Q.2
  have rQt := hReal.Qt.2
  have eXi : FourierSymbolIsEntire (edges L k) (edges L k) (trivialRescaledOperators L k).Xi :=
    (hS _ _ hI hI).1 _ hXi.1 hXi.2.1
  have eQ : FourierSymbolIsEntire (edges L k) (topEdges L k) (trivialRescaledOperators L k).Q :=
    (hS _ _ hI hI').1 _ hQ.1 hQ.2.1
  have eQt : FourierSymbolIsEntire (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt :=
    (hS _ _ hI' hI).1 _ hQt.1 hQt.2.1
  have holXi : QuotHomFamilyHolomorphicOn (n := 4) univ (xiHat L k) :=
    symbolHom_holomorphicOn hO hI hI hXi.1 eXi
  have holQ := symbolHom_holomorphicOn hO hI hI' hQ.1 eQ
  have holQt := symbolHom_holomorphicOn hO hI' hI hQt.1 eQt
  have famXi : IsSymmetricFamilyOn univ (xiHat L k) :=
    symbolHom_isSymmetricFamilyOn hE hS hO hI hI hXi.1 eXi rXi.1
  have famQ := symbolHom_isSymmetricFamilyOn hE hS hO hI hI' hQ.1 eQ rQ.1
  have famQt := symbolHom_isSymmetricFamilyOn hE hS hO hI' hI hQt.1 eQt rQt.1
  have hinv0 := hA.2 0 (left_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
  have hbi := hinv0.edge_inverse
  have hba := hinv0.edge_avg
  have hzero : addScalar (edges L k) 0 (FreeStrip.edgeOpXi L k) =
      (trivialRescaledOperators L k).Xi := addScalar_zero _ _
  have hXiInvPeriodic : IsPeriodicKernel (edges L k) (edges L k) (xiInv L k) := by
    have h := hbi.inverse_periodic
    rw [hzero] at h
    exact h
  have hXiInvSummable : SymbolSummableOn (edges L k) (edges L k) (xiInv L k)
      (imStrip (2 * δ₀)) := by
    have h := hbi.inverse_summable
    rw [hzero] at h
    exact h
  have hXiInvSymbol : ∀ z ∈ imStrip (2 * δ₀), symbolHom (edges L k) (edges L k) (xiInv L k) z =
      quotHomInverse (xiHat L k z) := by
    intro z hz
    have h := hbi.inverse_symbol z hz
    rw [hzero, symbolAddScalar_zero] at h
    exact h
  have hXiInvertibleA : ∀ z ∈ imStrip (2 * δ₀), IsInvertibleQuotHom (xiHat L k z) := by
    intro z hz
    have h := hbi.matrix_invertible z hz
    rw [symbolAddScalar_zero] at h
    exact h
  have hCov : FreeStrip.SymbolInvertibleOn (topEdges L k) (blockCovariance L k)
      (imStrip (2 * δ₀)) C₀ := by
    have h := hba.2.2
    rw [hzero] at h
    exact h
  have hSymbolCov : ∀ z ∈ imStrip (2 * δ₀),
      symbolHom (topEdges L k) (topEdges L k) (blockCovariance L k) z = blockCovarianceHat L k z := by
    intro z hz
    have f1 := ((hO.2.1 _ _ hI hI').2.1 _ z hQ.1 (eQ.1 z (mem_univ z))).comp (edges L k) hI
      (xiInv L k) hXiInvPeriodic (hXiInvSummable z hz)
    have f2 := ((hO.2.1 _ _ hI hI').2.1 _ z f1.2.1 f1.2.2.1).comp (topEdges L k) hI'
      (trivialRescaledOperators L k).Qt hQt.1 (eQt.1 z (mem_univ z))
    have e2 := f2.2.2.2
    rw [f1.2.2.2, hXiInvSymbol z hz] at e2
    exact e2
  have ha : 0 < 2 * δ₀ := by linarith [hδ.1]
  have ha9 : 2 * δ₀ < 1 / 9 := by linarith [hδ.2]
  obtain ⟨υ₁, h1a, h1b, hXinv, hXbdd, hXhol⟩ := exists_wider_imStrip_inverse hE hS hC hN hI ha ha9
    (M := xiHat L k) (holomorphicOn_mono (isOpen_openImStrip _) (subset_univ _) holXi)
    (fun z _ n => (famXi z (mem_univ z)).2 n) hXiInvertibleA
  have hSym : IsSymmetricSet (univ : Set (Fin 4 → ℂ)) :=
    fun _ _ => ⟨mem_univ _, fun _ => mem_univ _⟩
  have hIF := (hC.1 _ _ _ hI hI hI).2.2.1 univ (xiHat L k) hSym famXi
  set D₁ := unitPoints univ (xiHat L k) with hD₁
  have hD₁sym : IsSymmetricSet D₁ := hIF.1
  have famXinv : IsSymmetricFamilyOn D₁ fun z => quotHomInverse (xiHat L k z) := hIF.2
  have hstripD₁ : imStrip υ₁ ⊆ D₁ := fun z hz => ⟨mem_univ z, hXinv z hz⟩
  have famQ₁ : IsSymmetricFamilyOn D₁
      (symbolHom (edges L k) (topEdges L k) (trivialRescaledOperators L k).Q) :=
    fun z _ => famQ z (mem_univ z)
  have famQt₁ : IsSymmetricFamilyOn D₁
      (symbolHom (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt) :=
    fun z _ => famQt z (mem_univ z)
  have famRight : IsSymmetricFamilyOn D₁ fun z => (quotHomInverse (xiHat L k z)).comp
      (symbolHom (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt z) :=
    (hC.1 _ _ _ hI hI hI').2.2.2 D₁ _ _ hD₁sym famXinv famQt₁
  have famCov : IsSymmetricFamilyOn D₁ (blockCovarianceHat L k) :=
    (hC.1 _ _ _ hI hI' hI').2.2.2 D₁ _ _ hD₁sym famQ₁ famRight
  have hCovHol : QuotHomFamilyHolomorphicOn (n := 4) (openImStrip υ₁) (blockCovarianceHat L k) := by
    have hos := isOpen_openImStrip υ₁
    exact holomorphicOn_comp hE hI hI' hI' (holomorphicOn_mono hos (subset_univ _) holQ)
      (holomorphicOn_comp hE hI hI hI' hXhol (holomorphicOn_mono hos (subset_univ _) holQt))
  have hCovInvertibleA : ∀ z ∈ imStrip (2 * δ₀), IsInvertibleQuotHom (blockCovarianceHat L k z) := by
    intro z hz
    rw [← hSymbolCov z hz]
    exact (hCov.2 z hz).1
  obtain ⟨υ₂, h2a, h2b, hCinv, hCbdd, hChol⟩ := exists_wider_imStrip_inverse hE hS hC hN hI' ha h1a
    (M := blockCovarianceHat L k) hCovHol
    (fun z hz n => (famCov z (hstripD₁ (openImStrip_subset_imStrip _ hz))).2 n) hCovInvertibleA
  have hIC := (hC.1 _ _ _ hI' hI' hI').2.2.1 D₁ (blockCovarianceHat L k) hD₁sym famCov
  set υ := (2 * δ₀ + υ₂) / 2 with hυdef
  have hυa : 2 * δ₀ < υ := by rw [hυdef]; linarith
  have hυb : υ < υ₂ := by rw [hυdef]; linarith
  have hυ0 : 0 < υ := ha.trans hυa
  have hsub₂₁ : openImStrip υ₂ ⊆ imStrip υ₁ :=
    (openImStrip_subset_imStrip υ₂).trans (imStrip_mono h2b.le)
  have hsubυ₂ : imStrip υ ⊆ openImStrip υ₂ := imStrip_subset_openImStrip hυb
  have hsubυ₁ : imStrip υ ⊆ imStrip υ₁ := imStrip_mono (hυb.trans h2b).le
  have hos₂ := isOpen_openImStrip υ₂
  have hXholυ₂ : QuotHomFamilyHolomorphicOn (n := 4) (openImStrip υ₂)
      fun z => quotHomInverse (xiHat L k z) :=
    holomorphicOn_mono hos₂ (openImStrip_mono h2b.le) hXhol
  have hXbddυ : QuotHomFamilyBoundedOn (imStrip υ) fun z => quotHomInverse (xiHat L k z) :=
    fun p => let ⟨B, hB⟩ := hXbdd p; ⟨B, fun x hx => hB x (hsubυ₁ hx)⟩
  have hCbddυ : QuotHomFamilyBoundedOn (imStrip υ)
      fun z => quotHomInverse (blockCovarianceHat L k z) :=
    fun p => let ⟨B, hB⟩ := hCbdd p; ⟨B, fun x hx => hB x (imStrip_mono hυb.le hx)⟩
  have hFirst : IsInverseRadius δ₀ L k υ := by
    refine ⟨⟨hυa, hυb.trans (h2b.trans h1b)⟩, ⟨openImStrip υ₂, hos₂, hsubυ₂, ?_⟩, hXbddυ,
      hCbddυ⟩
    exact ⟨fun z hz => hXinv z (hsub₂₁ hz),
      fun z hz => hCinv z (openImStrip_subset_imStrip _ hz), hXholυ₂, hChol⟩
  have hassoc := (hO.2.1 _ _ hI hI').2.2.2 (edges L k) (topEdges L k) hI hI'
    (trivialRescaledOperators L k).Q (xiInv L k) (trivialRescaledOperators L k).Qt hQ.1
    hXiInvPeriodic hQt.1
  have hCovPeriodic : IsPeriodicKernel (topEdges L k) (topEdges L k) (blockCovariance L k) :=
    hassoc.2.2.2.2.2.1
  have hFormed : BlockCovarianceWellFormed L k :=
    { left_pair := hassoc.1
      left_assoc := hassoc.2.2.2.2.1
      right_pair := hassoc.2.2.1
      right_assoc := hassoc.2.2.2.2.2.2.1
      assoc_eq := hassoc.2.2.2.2.2.2.2.2
      periodic := hassoc.2.2.2.2.2.1 }
  have hcalc := (hS _ _ hI hI).2.2.2.2.2.2.1 υ hυ0
  have hcalc' := (hS _ _ hI' hI').2.2.2.2.2.2.1 υ hυ0
  have hContXi : QuotHomFamilyContinuousOn (n := 4) (imStrip υ) (xiHat L k) :=
    have h := continuousOn_of_holomorphicOn hE hI hI holXi
    ⟨h.1, fun p => (h.2 p).mono (subset_univ _)⟩
  have mfXi : SymbolCalculus.IsStripSymbol (edges L k) (edges L k) υ (xiHat L k) :=
    ⟨⟨univ, isOpen_univ, subset_univ _, fun c' c => holXi.2.2 (c', c)⟩,
      boundedOn_imStrip_of_quasiPeriodic hS hC hN hI hI hContXi
        fun z _ n => (famXi z (mem_univ z)).2 n,
      fun n z _ => (famXi z (mem_univ z)).2 n⟩
  have hContCov : QuotHomFamilyContinuousOn (n := 4) (imStrip υ) (blockCovarianceHat L k) :=
    have h := continuousOn_of_holomorphicOn hE hI' hI' hCovHol
    ⟨h.1, fun p => (h.2 p).mono (hsubυ₂.trans (openImStrip_mono h2b.le))⟩
  have mfCov : SymbolCalculus.IsStripSymbol (topEdges L k) (topEdges L k) υ
      (blockCovarianceHat L k) :=
    ⟨⟨openImStrip υ₁, hCovHol.2.1, hsubυ₂.trans (openImStrip_mono h2b.le),
        fun c' c => hCovHol.2.2 (c', c)⟩,
      boundedOn_imStrip_of_quasiPeriodic hS hC hN hI' hI' hContCov
        (fun z hz n => (famCov z (hstripD₁ (hsubυ₁ hz))).2 n),
      fun n z hz => (famCov z (hstripD₁ (hsubυ₁ hz))).2 n⟩
  have hrealSub : realDualPoints ⊆ imStrip (2 * δ₀) := by
    intro z hz ν
    rw [hz ν, abs_zero]
    exact ha.le
  have resXi := hcalc.2.2.2.2 _ mfXi (trivialRescaledOperators L k).Xi hXi.1
    ⟨fun z _ => eXi.1 z (mem_univ z), fun _ _ => rfl⟩
    ⟨openImStrip υ₂, hos₂, hsubυ₂, fun z hz => hXinv z (hsub₂₁ hz)⟩ hXbddυ
  have resCov := hcalc'.2.2.2.2 _ mfCov (blockCovariance L k) hCovPeriodic
    ⟨fun z hz => hCov.1 z (hrealSub hz), fun z hz => hSymbolCov z (hrealSub hz)⟩
    ⟨openImStrip υ₂, hos₂, hsubυ₂, fun z hz => hCinv z (openImStrip_subset_imStrip _ hz)⟩
    hCbddυ
  have mfXinv : SymbolCalculus.IsStripSymbol (edges L k) (edges L k) υ
      fun z => quotHomInverse (xiHat L k z) :=
    ⟨⟨openImStrip υ₂, hos₂, hsubυ₂, fun c' c => hXholυ₂.2.2 (c', c)⟩, hXbddυ,
      fun n z hz => (famXinv z (hstripD₁ (hsubυ₁ hz))).2 n⟩
  have hD₂ : ∀ z ∈ imStrip υ, z ∈ unitPoints D₁ (blockCovarianceHat L k) :=
    fun z hz => ⟨hstripD₁ (hsubυ₁ hz), hCinv z (imStrip_mono hυb.le hz)⟩
  have mfCinv : SymbolCalculus.IsStripSymbol (topEdges L k) (topEdges L k) υ
      fun z => quotHomInverse (blockCovarianceHat L k z) :=
    ⟨⟨openImStrip υ₂, hos₂, hsubυ₂, fun c' c => hChol.2.2 (c', c)⟩, hCbddυ,
      fun n z hz => (hIC.2 z (hD₂ z hz)).2 n⟩
  have kerXinv := hcalc.2.1 _ mfXinv
  have kerCinv := hcalc'.2.1 _ mfCinv
  have realXinv : ∀ ι' ι, (xiInv L k ι' ι).im = 0 := by
    refine kerXinv.im_eq_zero fun z hz => ?_
    have h := (famXinv z (hstripD₁ (hsubυ₁ hz))).1
    rw [← negConjPoint_eq_neg_star, ← linearMapEntry_conjQuotHom hE hI hI]
    exact congrArg linearMapEntry h
  have hCinvKernel : blockCovarianceInv L k = matFunKernel (topEdges L k)
      (topEdges L k) fun z => quotHomInverse (blockCovarianceHat L k z) := resCov.2.2.1
  have realCinv : ∀ ι' ι, (blockCovarianceInv L k ι' ι).im = 0 := by
    rw [hCinvKernel]
    refine kerCinv.im_eq_zero fun z hz => ?_
    have h := (hIC.2 z (hD₂ z hz)).1
    rw [← negConjPoint_eq_neg_star, ← linearMapEntry_conjQuotHom hE hI' hI']
    exact congrArg linearMapEntry h
  have formOf : ∀ {j j' : ℕ} {T : (colourEdges L k j').Carrier → (colourEdges L k j).Carrier → ℂ},
      j ≤ k → j' ≤ k → IsPeriodicKernel (colourEdges L k j) (colourEdges L k j') T →
      FourierSymbolIsEntire (colourEdges L k j) (colourEdges L k j') T →
      Tower.IsColourTrivial (σ := PeriodicOperators.PosEdge L k j)
        (σ' := PeriodicOperators.PosEdge L k j') T → ∀ z,
      PeriodicOperators.IsColourTrivial (L := L) (k := k) (j := j) (j' := j') (t := .edge)
        (t' := .edge) (symbolHom (colourEdges L k j) (colourEdges L k j') T z) := by
    intro j j' T hj hj' hT hent htriv z
    have hPj := (hIdx L hL k j hj).2.1
    have hPj' := (hIdx L hL k j' hj').2.1
    exact isColourTrivial_of_carrierEntry
      ((hO.2.1 _ _ hPj hPj').2.1 T z hT (hent.1 z (mem_univ z))).carrierEntry_symbolHom
      (fourierSymbol_isColourTrivial htriv z)
  have hk0 : (0 : ℕ) ≤ k := Nat.zero_le k
  have formXi := formOf hk0 hk0 hXi.1 eXi rXi.2
  have formQ := formOf hk0 le_rfl hQ.1 eQ rQ.2
  have formQt := formOf le_rfl hk0 hQt.1 eQt rQt.2
  have col₀ := (hC.2.1 L hL k hk 0 0 k hk0 hk0 le_rfl .edge .edge .edge).1
  have col₁ := (hC.2.1 L hL k hk 0 k k hk0 le_rfl le_rfl .edge .edge .edge).1
  have colInvXi : ∀ z ∈ imStrip υ₁, PeriodicOperators.IsColourTrivial (L := L) (k := k) (j := 0)
      (j' := 0) (t := .edge) (t' := .edge) (quotHomInverse (xiHat L k z)) := fun z hz =>
    (hC.2.1 L hL k hk 0 0 0 hk0 hk0 hk0 .edge .edge .edge).1.2 _ (hXinv z hz) (formXi z)
  have colCov : ∀ z ∈ imStrip υ₁, PeriodicOperators.IsColourTrivial (L := L) (k := k) (j := k)
      (j' := k) (t := .edge) (t' := .edge) (blockCovarianceHat L k z) := fun z hz =>
    col₁.1 _ _ (formQ z) (col₀.1 _ _ (colInvXi z hz) (formQt z))
  have hreal₁ : ∀ z ∈ realDualPoints, z ∈ imStrip υ₁ := fun z hz => imStrip_mono h1a.le (hrealSub hz)
  refine ⟨⟨eXi.1, eQ.1, eQt.1⟩, ⟨υ, hFirst⟩, ?_⟩
  exact
    { xi := ⟨resXi.1, resXi.2.2.2.1, resXi.2.2.2.2.1, resXi.2.2.2.2.2.1, resXi.2.2.2.2.2.2.1,
        resXi.2.2.2.2.2.2.2⟩
      cov_formed := hFormed
      cov := ⟨resCov.1, resCov.2.2.2.1, resCov.2.2.2.2.1, resCov.2.2.2.2.2.1,
        resCov.2.2.2.2.2.2.1, resCov.2.2.2.2.2.2.2⟩
      xi_real := ⟨realXinv, matFunKernel_isColourTrivial (j := 0) (j' := 0)
        (M := fun z => quotHomInverse (xiHat L k z))
        fun z hz => colInvXi z (hreal₁ z hz)⟩
      cov_real := ⟨realCinv, by
        rw [hCinvKernel]
        exact matFunKernel_isColourTrivial (j := k) (j' := k)
          (M := fun z => quotHomInverse (blockCovarianceHat L k z))
          fun z hz => (hC.2.1 L hL k hk k k k le_rfl le_rfl le_rfl .edge .edge .edge).1.2 _
            (hCinv z (imStrip_mono h2a.le (hrealSub hz))) (colCov z (hreal₁ z hz))⟩ }
theorem claim_holds (hAdm : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hIdx : TowerIndexSets.Claim) (hS : SymbolCalculus.Claim)
    (hO : StripSymbols.Claim) (hF : FreeOperators.FreeOperatorsArePeriodic)
    (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hE : EntriesDets.Claim)
    (hN : HomNorm.Claim) (hC : CompInv.Claim) : Claim := by
  obtain ⟨_, _, δ₀, hδ₀, C₀, _, hδ, _, hPair⟩ := hAdm
  exact ⟨δ₀, hδ₀, fun L hL k hk =>
    claim_at_height hIdx hS hO hF hW hE hN hC hδ hL hk (hPair.2.2 L hL k hk)⟩
end YangMills.Construction.Tower.ResponseInverses
end
