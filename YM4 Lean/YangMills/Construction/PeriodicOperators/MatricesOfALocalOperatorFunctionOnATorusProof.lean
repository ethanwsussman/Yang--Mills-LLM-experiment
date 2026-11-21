import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSetProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
open Set Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalTorusMatrices
open TorusMetric (euclidNormVec)
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
section Quotients
variable {I : PeriodicData}
theorem mkQuot_eq_iff (h : IsPeriodic I) (s : ℕ) (ι ι' : I.Carrier) :
    I.mkQuot s ι = I.mkQuot s ι' ↔ ∃ n : Fin 4 → ℤ, ι' = I.translate (s • n) ι := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
theorem translate_nsmul_injective (h : IsPeriodic I) (s : ℕ) (hs : 0 < s) (ι : I.Carrier) :
    Function.Injective fun n : Fin 4 → ℤ => I.translate (s • n) ι := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.translate_nsmul_injective <;> assumption
theorem finite_nearTranslates (h : IsPeriodic I)
    (hfin : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite) (s : ℕ)
    (hs : 0 < s) (y : InfiniteLattice.AmbientSpace) (R : ℝ) (ι : I.Carrier) :
    {n : Fin 4 → ℤ | euclidNormVec (I.pos (I.translate (s • n) ι) - y) ≤ R}.Finite :=
  (hfin y R).preimage (f := fun n : Fin 4 → ℤ => I.translate (s • n) ι)
    (translate_nsmul_injective h s hs ι).injOn
end Quotients
section Kernels
variable {I I' : PeriodicData}
structure IsRangedPeriodicKernel (I I' : PeriodicData) (Y : I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (s : ℕ) : Prop where
  vanish : ∀ ι' ι, ¬ euclidNormVec (I.pos ι - I'.pos ι') ≤ R → Y ι' ι = 0
  periodic : ∀ (m : Fin 4 → ℤ) ι' ι, Y (I'.translate (s • m) ι') (I.translate (s • m) ι) = Y ι' ι
theorem periodSumFiniteOnQuot_of_ranged (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hfin : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    {Y : I'.Carrier → I.Carrier → ℂ} {R : ℝ} {s : ℕ} (hs : 0 < s)
    (hY : IsRangedPeriodicKernel I I' Y R s) : PeriodSumFiniteOnQuot I I' Y s := by
  refine ⟨fun ι' ι => ?_, fun a a₂ b b₂ ea eb => ?_⟩
  · refine (finite_nearTranslates hI hfin s hs (I'.pos ι') R ι).subset fun n hn => ?_
    by_contra hc
    exact hn (hY.vanish _ _ hc)
  · obtain ⟨m', rfl⟩ := (mkQuot_eq_iff hI' s _ _).1 ea
    obtain ⟨m, rfl⟩ := (mkQuot_eq_iff hI s _ _).1 eb
    have key : ∀ n : Fin 4 → ℤ,
        Y (I'.translate (s • m') a) (I.translate (s • n) (I.translate (s • m) b)) =
        Y a (I.translate (s • (n + (m - m'))) b) := by
      intro n
      have hn : I.translate (s • n) (I.translate (s • m) b) =
          I.translate (s • m') (I.translate (s • (n + (m - m'))) b) := by
        rw [← hI.translate_add, ← hI.translate_add]
        congr 1
        simp only [smul_add, smul_sub]
        abel
      rw [hn, hY.periodic]
    simp only [periodization, key]
    exact ((Equiv.addRight (m - m')).tsum_eq fun n => Y a (I.translate (s • n) b)).symm
theorem descendMatrix_mkQuot {s : ℕ} {G : I'.Carrier → I.Carrier → ℂ}
    (hG : ∀ ι₁' ι₂' ι₁ ι₂, I'.mkQuot s ι₁' = I'.mkQuot s ι₂' →
      I.mkQuot s ι₁ = I.mkQuot s ι₂ → G ι₁' ι₁ = G ι₂' ι₂) (ι' : I'.Carrier) (ι : I.Carrier) :
    descendMatrix I I' s G (I'.mkQuot s ι') (I.mkQuot s ι) = G ι' ι := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.descendMatrix_mkQuot <;> assumption
theorem actsViaPeriodization_of_ranged (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hfin : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    {Y : I'.Carrier → I.Carrier → ℂ} {R : ℝ} {s : ℕ} (hs : 0 < s)
    (hY : IsRangedPeriodicKernel I I' Y R s) : ActsViaPeriodization I I' Y s := by
  intro f
  have hsupp : ∀ ι', {ι | Y ι' ι * liftQuotField I s f ι ≠ 0}.Finite := by
    intro ι'
    refine (hfin (I'.pos ι') R).subset fun ι hι => ?_
    by_contra hc
    exact hι (by rw [hY.vanish ι' ι hc, zero_mul])
  have main : ∀ ι', applyKernel Y (liftQuotField I s f) ι' =
      applyKernel (descendMatrix I I' s (periodization I I' Y s)) f (I'.mkQuot s ι') := by
    intro ι'
    have hcl := (periodSumFiniteOnQuot_of_ranged hI hI' hfin hs hY).2
    let Φ : I.QuotMod s × (Fin 4 → ℤ) → I.Carrier := fun p => I.translate (s • p.2) (Quot.out p.1)
    have hquot : ∀ (c : I.QuotMod s) (n : Fin 4 → ℤ), I.mkQuot s (Φ (c, n)) = c := by
      intro c n
      have h1 : I.mkQuot s (Quot.out c) = I.mkQuot s (Φ (c, n)) :=
        (mkQuot_eq_iff hI s _ _).2 ⟨n, rfl⟩
      rw [← h1]
      exact Quot.out_eq c
    have hΦ : Function.Bijective Φ := by
      constructor
      · rintro ⟨c, n⟩ ⟨c', n'⟩ hcn
        have hc : c = c' := by rw [← hquot c n, ← hquot c' n', hcn]
        subst hc
        have hn : n = n' := translate_nsmul_injective hI s hs (Quot.out c) hcn
        rw [hn]
      · intro ι
        have h1 : I.mkQuot s ι = I.mkQuot s (Quot.out (I.mkQuot s ι)) :=
          (Quot.out_eq (I.mkQuot s ι)).symm
        obtain ⟨n, hn⟩ := (mkQuot_eq_iff hI s _ _).1 h1.symm
        exact ⟨(I.mkQuot s ι, n), hn.symm⟩
    let g : I.Carrier → ℂ := fun ι => Y ι' ι * liftQuotField I s f ι
    have hg : Summable g := summable_of_finite_support (hsupp ι')
    have hgΦ : Summable (g ∘ Φ) := ((Equiv.ofBijective Φ hΦ).summable_iff).2 hg
    have e1 : applyKernel Y (liftQuotField I s f) ι' = ∑' p, g (Φ p) :=
      ((Equiv.ofBijective Φ hΦ).tsum_eq g).symm
    rw [e1]
    refine (hgΦ.tsum_prod' fun c => hgΦ.prod_factor c).trans ?_
    show _ = ∑' c, descendMatrix I I' s (periodization I I' Y s) (I'.mkQuot s ι') c * f c
    refine tsum_congr fun c => ?_
    have e2 : descendMatrix I I' s (periodization I I' Y s) (I'.mkQuot s ι') c =
        periodization I I' Y s ι' (Quot.out c) := by
      conv_lhs => rw [← Quot.out_eq c]
      exact descendMatrix_mkQuot hcl ι' (Quot.out c)
    rw [e2, periodization, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    show Y ι' (Φ (c, n)) * f (I.mkQuot s (Φ (c, n))) = _
    rw [hquot]
  refine ⟨hsupp, fun a b hab => ?_, main⟩
  rw [main, main, hab]
end Kernels
section Entries
variable {F I I' : PeriodicData}
theorem equiv_val_injective {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) :
    Function.Injective fun j => ((e j : S) : F.Carrier) :=
  Subtype.val_injective.comp e.injective
theorem norm_fieldExtend_le {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
    (z : Coordinates.ComplexCoordinates l) (κ : F.Carrier) : ‖fieldExtend e z κ‖ ≤ ‖z‖ := by
  unfold fieldExtend
  by_cases h : ∃ j, ((e j : S) : F.Carrier) = κ
  · obtain ⟨j, rfl⟩ := h
    rw [(equiv_val_injective e).extend_apply]
    exact norm_le_pi_norm z j
  · rw [Function.extend_apply' _ _ _ h]
    simp
theorem fieldValues_fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
    (z : Coordinates.ComplexCoordinates l) : fieldValues e (fieldExtend e z) = z := by
  funext j
  exact (equiv_val_injective e).extend_apply _ _ j
theorem exists_quadratic_forms (hNumbers : ParameterIndependence.Claim)
    (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) (ι' : I'.Carrier) (ι : I.Carrier) :
    ∃ (l : ℕ) (e : Fin l ≃ nearIndices F (I'.pos ι') R) (h : Coordinates.ComplexCoordinates l → ℂ)
      (φ : Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ)
      (β : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion h φ β ∧
      (∀ ζ, IsSupBelow F ζ ρ → T ζ ι' ι = h (fieldValues e ζ)) ∧
      (∀ ζ, coeffOne F I I' T ζ ι' ι = φ (fieldValues e ζ)) ∧
      ∀ ζ ζ', coeffTwo F I I' T ζ ζ' ι' ι = β (fieldValues e ζ) (fieldValues e ζ') := by
  obtain ⟨l, e, h, hh, hTh⟩ := hT.holo_entry ι' ι
  obtain ⟨⟨φ, β⟩, hp, -⟩ := hTaylor l ρ hT.radius_pos h hh
  have hnear : entryFun T ι' ι e =ᶠ[𝓝 0] h := by
    filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates l) hT.radius_pos]
      with z hz
    have hb : IsSupBelow F (fieldExtend e z) ρ :=
      ⟨‖z‖, by simpa using hz, norm_fieldExtend_le e z⟩
    show T (fieldExtend e z) ι' ι = h z
    rw [hTh _ hb, fieldValues_fieldExtend]
  have h0 : entryFun T ι' ι e 0 = h 0 := hnear.self_of_nhds
  have hexp : IsSecondOrderExpansion (entryFun T ι' ι e) φ β := by
    refine ⟨hp.1, hp.2.congr' ?_ EventuallyEq.rfl⟩
    filter_upwards [hnear] with z hz
    rw [hz, h0]
  have hb := fun ζ ζ' => (hNumbers F I I' hF hI hI' T ρ R ρ R hT hT).2.1.1 ζ ζ' ι' ι
  exact ⟨l, e, h, φ, β, hp, hTh,
    fun ζ => ((hb ζ ζ).1.2.2 ρ R hT l e φ β hexp).symm,
    fun ζ ζ' => ((hb ζ ζ').2.2.2 ρ R hT l e φ β hexp).symm⟩
end Entries
section Coefficients
variable {F I I' : PeriodicData}
theorem shiftField_liftQuotField (hF : IsPeriodic F) (s : ℕ) (ζ : F.QuotMod s → ℂ)
    (m : Fin 4 → ℤ) : shiftField F (s • m) (liftQuotField F s ζ) = liftQuotField F s ζ := by
  funext κ
  show ζ (F.mkQuot s (F.translate (-(s • m)) κ)) = ζ (F.mkQuot s κ)
  rw [← smul_neg]
  exact congrArg ζ ((mkQuot_eq_iff hF s _ _).2 ⟨-m, rfl⟩).symm
theorem le_supModulus {s : ℕ} (hfin : Finite (F.QuotMod s)) (ζ : F.QuotMod s → ℂ)
    (c : F.QuotMod s) : ‖ζ c‖ ≤ supModulus F s ζ :=
  le_ciSup (Set.finite_range fun c => ‖ζ c‖).bddAbove c
theorem periodicCoeffsAreTaylor_of_local {s : ℕ} (hNumbers : ParameterIndependence.Claim)
    (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion)
    (hCoeff : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hfin : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    (hquot : Finite (F.QuotMod s))
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) (hs : 0 < s) :
    PeriodicCoeffsAreTaylor F I I' T ρ s := by
  intro ι' ι
  have hNfin := finite_nearTranslates hI hfin s hs (I'.pos ι') R ι
  let N : Finset (Fin 4 → ℤ) := hNfin.toFinset
  have hN : ∀ n, n ∉ N → ¬ euclidNormVec (I.pos (I.translate (s • n) ι) - I'.pos ι') ≤ R := by
    intro n hn
    simpa [N] using hn
  choose l e h φ β hexp hval hfirst hsecond using
    fun n : Fin 4 → ℤ => exists_quadratic_forms hNumbers hTaylor hF hI hI' hT ι' (I.translate (s • n) ι)
  let v : ∀ n, (F.QuotMod s → ℂ) →ₗ[ℂ] Coordinates.ComplexCoordinates (l n) := fun n =>
    { toFun := fun ζ => fieldValues (e n) (liftQuotField F s ζ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have first_sum : ∀ ζ : F.QuotMod s → ℂ, periodicCoeffOne F I I' T s ζ ι' ι =
      ∑ n ∈ N, φ n (v n ζ) := by
    intro ζ
    unfold periodicCoeffOne periodization
    rw [tsum_eq_sum (s := N) fun n hn =>
      ((hCoeff F I I' hF hI hI' T ρ R hT (liftQuotField F s ζ) (liftQuotField F s ζ) ι'
        (I.translate (s • n) ι) 0).2.1.2 (hN n hn)).2.1]
    exact Finset.sum_congr rfl fun n _ => hfirst n _
  have second_sum : ∀ ζ ζ' : F.QuotMod s → ℂ, periodicCoeffTwo F I I' T s ζ ζ' ι' ι =
      ∑ n ∈ N, β n (v n ζ) (v n ζ') := by
    intro ζ ζ'
    unfold periodicCoeffTwo periodization
    rw [tsum_eq_sum (s := N) fun n hn =>
      ((hCoeff F I I' hF hI hI' T ρ R hT (liftQuotField F s ζ) (liftQuotField F s ζ') ι'
        (I.translate (s • n) ι) 0).2.1.2 (hN n hn)).2.2]
    exact Finset.sum_congr rfl fun n _ => hsecond n _ _
  let L : (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ := ∑ n ∈ N, (φ n).comp (v n)
  let B : (F.QuotMod s → ℂ) →ₗ[ℂ] (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ :=
    ∑ n ∈ N, (β n).compl₁₂ (v n) (v n)
  have hL : ∀ ζ, periodicCoeffOne F I I' T s ζ ι' ι = L ζ := by
    intro ζ
    simp [L, first_sum, LinearMap.sum_apply]
  have hB : ∀ ζ ζ', periodicCoeffTwo F I I' T s ζ ζ' ι' ι = B ζ ζ' := by
    intro ζ ζ'
    simp [B, second_sum, LinearMap.sum_apply]
  refine ⟨?_, fun ζ' => ?_, fun ζ => ?_, fun ζ ζ' => ?_, ?_⟩
  · simp only [hL]
    exact L.isLinear
  · simp only [hB]
    exact (B.flip ζ').isLinear
  · simp only [hB]
    exact (B ζ).isLinear
  · rw [second_sum, second_sum]
    exact Finset.sum_congr rfl fun n _ => (hexp n).1 _ _
  · have hmod0 : ∀ ζ : F.QuotMod s → ℂ, 0 ≤ supModulus F s ζ := fun ζ =>
      Real.iSup_nonneg fun _ => norm_nonneg _
    have hvle : ∀ n (ζ : F.QuotMod s → ℂ), ‖v n ζ‖ ≤ supModulus F s ζ := fun n ζ =>
      (pi_norm_le_iff_of_nonneg (hmod0 ζ)).2 fun j => le_supModulus hquot ζ _
    let S : Set (F.QuotMod s → ℂ) := {ζ | IsSupBelow F (liftQuotField F s ζ) ρ}
    have hterm : ∀ n ∈ N, (fun ζ : F.QuotMod s → ℂ =>
        h n (v n ζ) - (h n 0 + φ n (v n ζ) + (1 / 2 : ℂ) * β n (v n ζ) (v n ζ)))
          =O[𝓝[S] 0] fun ζ => supModulus F s ζ ^ 3 := by
      intro n _
      have hcont : Continuous (v n) :=
        continuous_pi fun j => continuous_apply (F.mkQuot s ((e n j : _) : F.Carrier))
      have htend : Tendsto (v n) (𝓝[S] 0) (𝓝 0) := by
        have h1 := hcont.tendsto (0 : F.QuotMod s → ℂ)
        rw [map_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      refine ((hexp n).2.comp_tendsto htend).trans (IsBigO.of_bound 1 (Eventually.of_forall ?_))
      intro ζ
      simp only [Function.comp, one_mul, norm_pow, Real.norm_eq_abs, abs_norm,
        abs_of_nonneg (hmod0 ζ)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hvle n ζ) 3
    refine (IsBigO.sum hterm).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have below0 : IsSupBelow F (0 : F.Carrier → ℂ) ρ := ⟨0, hT.radius_pos, fun _ => by simp⟩
    have value_sum : periodicValue F I I' T s ζ ι' ι = ∑ n ∈ N, h n (v n ζ) := by
      unfold periodicValue periodization
      rw [tsum_eq_sum (s := N) fun n hn => hT.vanish_far _ hζ _ _ (hN n hn)]
      exact Finset.sum_congr rfl fun n _ => hval n _ hζ
    have zeroth_sum : periodicCoeffZero F I I' T s ι' ι = ∑ n ∈ N, h n 0 := by
      unfold periodicCoeffZero periodization coeffZero
      rw [tsum_eq_sum (s := N) fun n hn => hT.vanish_far _ below0 _ _ (hN n hn)]
      exact Finset.sum_congr rfl fun n _ => hval n _ below0
    rw [value_sum, zeroth_sum, first_sum, second_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_apply _ _ _
end Coefficients
theorem localTorusMatricesClaim_holds (hFinite : CovariantFiniteRange.Claim)
    (hNumbers : ParameterIndependence.Claim)
    (hQuotients : Quotients.QuotientTransposeNorm)
    (hCoeff : LocalOpFunTaylor.Claim)
    (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion) : LocalTorusMatricesClaim := by
  intro F I I' hF hI hI' T ρ R hT s hs _
  have hfin := (hFinite.1 I hI).1
  have hquot : Finite (F.QuotMod s) := (hQuotients F F hF hF s hs).1.2.1
  refine ⟨fun ζ ζ' Y hY => ?_,
    periodicCoeffsAreTaylor_of_local hNumbers hTaylor hCoeff hF hI hI' hfin hquot hT hs⟩
  have hK : IsRangedPeriodicKernel I I' Y R s := by
    have hc := fun (a b : F.Carrier → ℂ) ι' ι n => hCoeff F I I' hF hI hI' T ρ R hT a b ι' ι n
    have htr := shiftField_liftQuotField hF s
    rcases hY with ⟨hb, rfl⟩ | rfl | rfl | rfl
    · refine ⟨fun ι' ι hr => hT.vanish_far _ hb _ _ hr, fun m ι' ι => ?_⟩
      have h1 := hT.shift_covariant _ hb (s • m) ι' ι
      rwa [htr] at h1
    · exact ⟨fun ι' ι hr => ((hc 0 0 ι' ι 0).2.1.2 hr).1,
        fun m ι' ι => (hc 0 0 ι' ι (s • m)).2.2.1.1⟩
    · refine ⟨fun ι' ι hr => ((hc (liftQuotField F s ζ) 0 ι' ι 0).2.1.2 hr).2.1,
        fun m ι' ι => ?_⟩
      have h1 := (hc (liftQuotField F s ζ) 0 ι' ι (s • m)).2.2.1.2.2.2.1
      rwa [htr] at h1
    · refine ⟨fun ι' ι hr =>
        ((hc (liftQuotField F s ζ) (liftQuotField F s ζ') ι' ι 0).2.1.2 hr).2.2,
        fun m ι' ι => ?_⟩
      have h1 := (hc (liftQuotField F s ζ) (liftQuotField F s ζ') ι' ι (s • m)).2.2.1.2.2.2.2
      rwa [htr, htr] at h1
  exact ⟨periodSumFiniteOnQuot_of_ranged hI hI' hfin hs hK,
    actsViaPeriodization_of_ranged hI hI' hfin hs hK⟩
end YangMills.Construction.PeriodicOperators.LocalTorusMatrices
end
