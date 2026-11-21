import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbolProof
import YangMills.Construction.PeriodicOperators.SymbolOfAProduct
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolComp
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
variable {I I' I'' : PeriodicData}
theorem euclidNormVec_sub_comm (a b : AmbientSpace) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_eq_norm (v : AmbientSpace) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_add_le (u v : AmbientSpace) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem norm_exp_I_bilinDot_le (κ : Fin 4 → ℂ) (y : AmbientSpace) :
    ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec y))‖ ≤
      Real.exp (euclidNormVec (imVec κ) * euclidNormVec y) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolSeriesProof.norm_cexp_I_mul_bilinDot_le <;> assumption
theorem exp_I_bilinDot_sub_split (κ : Fin 4 → ℂ) (a b c : AmbientSpace) :
    Complex.exp (Complex.I * bilinDot κ (toComplexVec (a - b))) =
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (c - b))) *
        Complex.exp (Complex.I * bilinDot κ (toComplexVec (a - c))) := by
  have h : bilinDot κ (toComplexVec (a - b)) =
      bilinDot κ (toComplexVec (c - b)) + bilinDot κ (toComplexVec (a - c)) := by
    simp only [bilinDot, toComplexVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.sub_apply]
    push_cast
    ring
  rw [h, mul_add, Complex.exp_add]
def pairSummand (T : I'.Carrier → I.Carrier → ℂ) (S : I.Carrier → I''.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (i' : I'.Carrier) (i'' : I''.Carrier) (p : I.Carrier × (Fin 4 → ℤ)) : ℂ :=
  T i' p.1 * S p.1 (I''.translate p.2 i'') *
    Complex.exp (Complex.I * bilinDot κ
      (toComplexVec (I''.pos (I''.translate p.2 i'') - I'.pos i')))
theorem summable_pairBound (hSums : ExponentialSums.Bounds) (hI : IsPeriodic I) {ε : ℝ}
    (hε : 0 < ε) (x' x'' : AmbientSpace) :
    Summable fun p : I.Carrier × (Fin 4 → ℤ) =>
      Real.exp (-ε * euclidNormVec (I.pos p.1 - x')) *
        Real.exp (-ε * euclidNormVec ((x'' - I.pos p.1) + castVec p.2)) := by
  have h := hSums ε hε
  have h2 := h.2.1
  have h3 := (h.2.2 I hI x').1
  have hnn : 0 ≤ fun p : I.Carrier × (Fin 4 → ℤ) =>
      Real.exp (-ε * euclidNormVec (I.pos p.1 - x')) *
        Real.exp (-ε * euclidNormVec ((x'' - I.pos p.1) + castVec p.2)) :=
    fun p => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  refine (summable_prod_of_nonneg hnn).mpr ?_
  constructor
  · intro i
    simp only
    exact (h2 (x'' - I.pos i)).1.mul_left (Real.exp (-ε * euclidNormVec (I.pos i - x')))
  · have hb : ∀ i : I.Carrier,
        ∑' k : Fin 4 → ℤ, Real.exp (-ε * euclidNormVec (I.pos i - x')) *
            Real.exp (-ε * euclidNormVec ((x'' - I.pos i) + castVec k)) ≤
          Real.exp (-ε * euclidNormVec (I.pos i - x')) *
            (Real.exp (2 * ε) * expHalfSum ε ^ 4) := by
      intro i
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (h2 _).2 (Real.exp_nonneg _)
    have hk : ∀ i : I.Carrier,
        0 ≤ ∑' k : Fin 4 → ℤ, Real.exp (-ε * euclidNormVec (I.pos i - x')) *
          Real.exp (-ε * euclidNormVec ((x'' - I.pos i) + castVec k)) :=
      fun i => tsum_nonneg fun k => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    exact Summable.of_nonneg_of_le hk hb (h3.mul_right _)
theorem norm_pairSummand_le (hI'' : IsPeriodic I'') {T : I'.Carrier → I.Carrier → ℂ}
    {S : I.Carrier → I''.Carrier → ℂ} {C C' δ : ℝ} (hC : 0 < C) (hC' : 0 < C')
    (hT : ExpDecay I I' T C δ) (hS : ExpDecay I'' I S C' δ) (κ : Fin 4 → ℂ)
    (i' : I'.Carrier) (i'' : I''.Carrier) (p : I.Carrier × (Fin 4 → ℤ)) :
    ‖pairSummand T S κ i' i'' p‖ ≤
      C * C' * (Real.exp (-(δ - euclidNormVec (imVec κ)) *
          euclidNormVec (I.pos p.1 - I'.pos i')) *
        Real.exp (-(δ - euclidNormVec (imVec κ)) *
          euclidNormVec ((I''.pos i'' - I.pos p.1) + castVec p.2))) := by
  obtain ⟨i, k⟩ := p
  set ρ := euclidNormVec (imVec κ) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set y := I''.pos (I''.translate k i'') with hy
  have hyeq : y - I.pos i = (I''.pos i'' - I.pos i) + castVec k := by
    rw [hy, hI''.pos_translate]
    abel
  simp only
  rw [← hyeq]
  set a := euclidNormVec (I.pos i - I'.pos i') with ha
  set b := euclidNormVec (y - I.pos i) with hb
  have h1 : ‖T i' i‖ ≤ C * Real.exp (-δ * a) := by
    have := hT i' i
    rwa [euclidNormVec_sub_comm] at this
  have h2 : ‖S i (I''.translate k i'')‖ ≤ C' * Real.exp (-δ * b) := by
    have := hS i (I''.translate k i'')
    rwa [euclidNormVec_sub_comm] at this
  have hd : euclidNormVec (y - I'.pos i') ≤ b + a := by
    have := euclidNormVec_add_le (y - I.pos i) (I.pos i - I'.pos i')
    simpa using this
  have h3 : ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec (y - I'.pos i')))‖ ≤
      Real.exp (ρ * (b + a)) :=
    (norm_exp_I_bilinDot_le κ _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hρ0))
  unfold pairSummand
  simp only
  rw [norm_mul, norm_mul]
  calc ‖T i' i‖ * ‖S i (I''.translate k i'')‖ *
        ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec (y - I'.pos i')))‖
      ≤ (C * Real.exp (-δ * a)) * (C' * Real.exp (-δ * b)) * Real.exp (ρ * (b + a)) := by
        gcongr
    _ = C * C' * (Real.exp (-(δ - ρ) * a) * Real.exp (-(δ - ρ) * b)) := by
        have e : Real.exp (-(δ - ρ) * a) * Real.exp (-(δ - ρ) * b) =
            Real.exp (-δ * a) * Real.exp (-δ * b) * Real.exp (ρ * (b + a)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [e]
        ring
theorem summable_pairSummand (hSums : ExponentialSums.Bounds) (hI : IsPeriodic I)
    (hI'' : IsPeriodic I'') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {δ : ℝ} (hT : IsDecayRate I I' T δ) (hS : IsDecayRate I'' I S δ) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ strictImStrip δ) (i' : I'.Carrier) (i'' : I''.Carrier) :
    Summable (pairSummand T S κ i' i'') := by
  obtain ⟨-, C, hC, hTC⟩ := hT
  obtain ⟨-, C', hC', hSC⟩ := hS
  have hε : 0 < δ - euclidNormVec (imVec κ) := sub_pos.mpr hκ
  exact Summable.of_norm_bounded
    ((summable_pairBound hSums hI hε (I'.pos i') (I''.pos i'')).mul_left (C * C'))
    (norm_pairSummand_le hI'' hC hC' hTC hSC κ i' i'')
theorem symbolSummand_compKernel_eq_tsum (T : I'.Carrier → I.Carrier → ℂ)
    (S : I.Carrier → I''.Carrier → ℂ) (κ : Fin 4 → ℂ) (i' : I'.Carrier) (i'' : I''.Carrier)
    (k : Fin 4 → ℤ) :
    symbolSummand I'' I' (compKernel T S) κ i' i'' k =
      ∑' i, pairSummand T S κ i' i'' (i, k) := by
  unfold symbolSummand compKernel pairSummand
  simp only
  rw [tsum_mul_right]
theorem summable_norm_symbolSummand_of_summable {T : I'.Carrier → I.Carrier → ℂ}
    {S : I.Carrier → I''.Carrier → ℂ} {κ : Fin 4 → ℂ} {i' : I'.Carrier} {i'' : I''.Carrier}
    (hG : Summable (pairSummand T S κ i' i'')) :
    Summable fun k => ‖symbolSummand I'' I' (compKernel T S) κ i' i'' k‖ := by
  have hsw : Summable fun p : (Fin 4 → ℤ) × I.Carrier => ‖pairSummand T S κ i' i'' p.swap‖ :=
    hG.norm.prod_symm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hsw.prod
  rw [symbolSummand_compKernel_eq_tsum]
  exact norm_tsum_le_tsum_norm (hsw.prod_factor k)
theorem tsum_pairSummand_snd (T : I'.Carrier → I.Carrier → ℂ) (S : I.Carrier → I''.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (i' : I'.Carrier) (i'' : I''.Carrier) (i : I.Carrier) :
    ∑' k, pairSummand T S κ i' i'' (i, k) =
      T i' i * Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos i - I'.pos i'))) *
        fourierSymbol I'' I S κ i i'' := by
  unfold fourierSymbol
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  unfold pairSummand symbolSummand
  simp only
  rw [exp_I_bilinDot_sub_split κ _ (I'.pos i') (I.pos i)]
  ring
theorem fourierSymbol_compKernel_eq_tsum_quot (hOrbits : QuotOrbits.Claim)
    (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {κ : Fin 4 → ℂ} {i' : I'.Carrier} {i'' : I''.Carrier}
    (hG : Summable (pairSummand T S κ i' i''))
    (hquot : ∀ i₁ i₂, I.mkQuot 1 i₁ = I.mkQuot 1 i₂ →
      fourierSymbol I'' I S κ i₁ i'' = fourierSymbol I'' I S κ i₂ i'')
    (r : I.UnitQuot → I.Carrier) (hr : ∀ c, I.mkQuot 1 (r c) = c) :
    fourierSymbol I'' I' (compKernel T S) κ i' i'' =
      ∑' c, fourierSymbol I I' T κ i' (r c) * fourierSymbol I'' I S κ (r c) i'' := by
  set H : I.Carrier → ℂ := fun i =>
    T i' i * Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos i - I'.pos i'))) *
      fourierSymbol I'' I S κ i i'' with hH
  have hcomm : fourierSymbol I'' I' (compKernel T S) κ i' i'' = ∑' i, H i := by
    unfold fourierSymbol
    simp only [symbolSummand_compKernel_eq_tsum]
    have hu : Summable (Function.uncurry fun i k => pairSummand T S κ i' i'' (i, k)) := hG
    rw [hu.tsum_comm]
    exact tsum_congr fun i => tsum_pairSummand_snd T S κ i' i'' i
  have hHsum : Summable H := by
    have := hG.prod
    refine this.congr fun i => ?_
    exact tsum_pairSummand_snd T S κ i' i'' i
  have hbij := (hOrbits I hI).2 1 one_pos r hr
  set e := Equiv.ofBijective _ hbij with he
  have hHe : Summable fun p : I.UnitQuot × (Fin 4 → ℤ) => H (e p) := e.summable_iff.mpr hHsum
  rw [hcomm, ← e.tsum_eq H, hHe.tsum_prod]
  refine tsum_congr fun c => ?_
  have hTsum : fourierSymbol I I' T κ i' (r c) = ∑' m, symbolSummand I I' T κ i' (r c) m := rfl
  rw [hTsum, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  have hep : e (c, m) = I.translate m (r c) := by
    simp [he, Equiv.ofBijective_apply]
  have hcl : I.mkQuot 1 (I.translate m (r c)) = I.mkQuot 1 (r c) :=
    (Quot.sound ⟨m, by simp⟩ : I.mkQuot 1 (r c) = I.mkQuot 1 (I.translate m (r c))).symm
  rw [hep, hH]
  simp only
  rw [hquot _ _ hcl]
  rfl
theorem symbolCompClaim_holds (hSums : ExponentialSums.Bounds) (hSeries : SymbolSeriesClaim)
    (hQuot : SymbolOnQuotients.Claim)
    (hOrbits : QuotOrbits.Claim)
    (hComp : CompClaim) : SymbolCompClaim := by
  intro I I' I'' hI hI' hI'' T S δ hT hδT hS hδS κ hκ
  have hsum : SymbolSummableAt I'' I' (compKernel T S) κ := fun i' i'' =>
    summable_norm_symbolSummand_of_summable (summable_pairSummand hSums hI hI'' hδT hδS hκ i' i'')
  refine ⟨hsum, ?_⟩
  have hTS := (hComp I I' I'' hI hI' hI'' T S δ hT hδT hS hδS).comp_periodic.2
  have qTS := hQuot I'' I' hI'' hI' _ hTS
  have qT := hQuot I I' hI hI' T hT
  have qS := hQuot I'' I hI'' hI S hS
  have sT : SymbolSummableAt I I' T κ := (hSeries I I' hI hI' T δ hδT).summableOn_strip κ hκ
  have sS : SymbolSummableAt I'' I S κ := (hSeries I'' I hI'' hI S δ hδS).summableOn_strip κ hκ
  have hrep : ∀ c : I.UnitQuot, ∃ i, I.mkQuot 1 i = c := fun c => Quot.exists_rep c
  choose r hr using hrep
  funext c' c''
  obtain ⟨i', rfl⟩ : ∃ i', I'.mkQuot 1 i' = c' := Quot.exists_rep c'
  obtain ⟨i'', rfl⟩ : ∃ i'', I''.mkQuot 1 i'' = c'' := Quot.exists_rep c''
  rw [qTS.quotSymbol_mkQuot κ hsum i' i'',
    fourierSymbol_compKernel_eq_tsum_quot hOrbits hI
      (summable_pairSummand hSums hI hI'' hδT hδS hκ i' i'')
      (fun i₁ i₂ h => qS.fourierSymbol_congr_mkQuot κ sS i₁ i₂ i'' i'' h rfl) r hr]
  unfold compKernel
  refine tsum_congr fun c => ?_
  have e1 := qT.quotSymbol_mkQuot κ sT i' (r c)
  have e2 := qS.quotSymbol_mkQuot κ sS (r c) i''
  rw [hr c] at e1 e2
  rw [e1, e2]
end YangMills.Construction.PeriodicOperators.SymbolComp
end
