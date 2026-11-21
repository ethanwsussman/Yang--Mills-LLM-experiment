import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorusProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import YangMills.Construction.PeriodicOperators.TheSecondDifferentialOnATorusByTraces
import YangMills.Construction.PeriodicOperators.TheTracesOnTheToriAtUnitFieldsConverge
import YangMills.Construction.Towers.DecayOfTheResolventOfAKernelOfRangeAtMostTwoProof
import YangMills.Construction.Towers.GaugeTransformationsKeepTheDensityProof
import YangMills.Construction.Towers.SecondDifferentialsOnTheToriOfALocalSetting
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2 Tower.AbelianFieldDensity
open Tower.ResolventDecay Tower.LocalFamilies OneLoopNotation
open PeriodicOperators PeriodicOperators.UnitFieldTraces
open PeriodicOperators.LogDetSecondDerivs
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
noncomputable section
namespace Tower.LocalFamilies.HessianLimitProof
theorem deriv_zero_of_isBigO_cube {k k' : ℝ → ℂ} {c : ℂ} (hk : ∀ t, HasDerivAt k (k' t) t)
    (hk' : HasDerivAt k' c 0) (hO : k =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 3) : k' 0 = 0 ∧ c = 0 := by
  have hO' : k =O[𝓝 0] fun t : ℝ => ‖t - 0‖ ^ 3 := by simpa using hO
  have hz : HasFDerivAt k (0 : ℝ →L[ℝ] ℂ) 0 := hO'.hasFDerivAt (by norm_num)
  have h0 : k' 0 = 0 := by
    have := (hk 0).unique hz.hasDerivAt
    simpa using this
  refine ⟨h0, ?_⟩
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => k t - c / 2 * (t : ℂ) ^ 2) (k' t - c * t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.pow 2).const_mul (c / 2)
    refine ((hk t).sub h2).congr_deriv ?_
    push_cast
    ring
  have hgo : (fun t : ℝ => k' t - c * t) =o[𝓝[Set.univ] 0] fun t : ℝ => (t - 0) ^ 1 := by
    have := hasDerivAt_iff_isLittleO.1 hk'
    simp only [nhdsWithin_univ, pow_one]
    refine this.congr_left fun t => ?_
    simp [h0, mul_comm]
  have hlit := Convex.isLittleO_pow_succ_real convex_univ (Set.mem_univ (0 : ℝ))
    (fun x _ => (hg x).hasDerivWithinAt) hgo
  simp only [nhdsWithin_univ, sub_zero] at hlit
  have hk0 : k 0 = 0 := hO'.eq_zero_of_norm_pow (by norm_num)
  have hko : k =o[𝓝 0] fun t : ℝ => t ^ (1 + 1) := by
    refine hO.trans_isLittleO ?_
    have := (isLittleO_pow_pow (𝕜 := ℝ) (m := 2) (n := 3) (by norm_num))
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)).trans_isLittleO this
    simp
  have hc : (fun t : ℝ => c / 2 * (t : ℂ) ^ 2) =o[𝓝 0] fun t : ℝ => t ^ (1 + 1) := by
    refine (hko.sub hlit).congr_left fun t => ?_
    simp [hk0]
  by_contra hne
  have hpos : 0 < ‖c‖ / 4 := by
    have := norm_pos_iff.2 hne
    positivity
  have hev := (hc.def hpos).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : t ≠ 0 := ht0
  have hsq : 0 < t ^ 2 := by positivity
  have hn : ‖c / 2 * (t : ℂ) ^ 2‖ = ‖c‖ / 2 * t ^ 2 := by
    simp [norm_pow, Complex.norm_real]
  have hn' : ‖t ^ (1 + 1)‖ = t ^ 2 := by simp
  rw [hn, hn'] at ht
  nlinarith
theorem derivs_of_quadratic_expansion {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : ℝ × ℝ → V) (hG : ContDiff ℝ 2 G) (lam : V →L[ℝ] ℂ) (c p q A M D : ℂ)
    (hexp : (fun w : ℝ × ℝ => lam (G w) - (c + ((w.1 : ℂ) * p + (w.2 : ℂ) * q) +
        1 / 2 * ((w.1 : ℂ) ^ 2 * A + 2 * (w.1 : ℂ) * (w.2 : ℂ) * M + (w.2 : ℂ) ^ 2 * D)))
      =O[𝓝 0] fun w : ℝ × ℝ => ‖w‖ ^ 3) :
    lam (deriv (fun s : ℝ => G (s, 0)) 0) = p ∧ lam (deriv (fun t : ℝ => G (0, t)) 0) = q ∧
      lam (deriv (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) 0) = M := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hD1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
  have hD1d : Differentiable ℝ (fderiv ℝ G) := hD1.differentiable (by norm_num)
  set L := fderiv ℝ (fderiv ℝ G) 0 with hL
  have key : ∀ α β : ℝ, lam (fderiv ℝ G 0 (α, β)) = (α : ℂ) * p + (β : ℂ) * q ∧
      lam (L (α, β) (α, β)) =
        (α : ℂ) ^ 2 * A + 2 * (α : ℂ) * (β : ℂ) * M + (β : ℂ) ^ 2 * D := by
    intro α β
    set u : ℝ × ℝ := (α, β) with hu
    set P : ℂ := (α : ℂ) * p + (β : ℂ) * q with hP
    set Q : ℂ := (α : ℂ) ^ 2 * A + 2 * (α : ℂ) * (β : ℂ) * M + (β : ℂ) ^ 2 * D with hQ
    have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • u) u t := by
      intro t
      simpa using (hasDerivAt_id t).smul_const u
    have hGl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => lam (G (t • u))) (lam (fderiv ℝ G (t • u) u)) t := by
      intro t
      have h1 := ((hGd (t • u)).hasFDerivAt).comp_hasDerivAt t (hline t)
      exact lam.hasFDerivAt.comp_hasDerivAt t h1
    have hDl : HasDerivAt (fun t : ℝ => lam (fderiv ℝ G (t • u) u)) (lam (L u u)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ G (t • u)) (L u) 0 := by
        have h0 : HasFDerivAt (fderiv ℝ G) L ((0 : ℝ) • u) := by
          rw [zero_smul]
          exact (hD1d 0).hasFDerivAt
        exact h0.comp_hasDerivAt 0 (hline 0)
      have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) u)
      have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ G (t • u) u) (L u u) 0 := by
        simpa using h2
      exact lam.hasFDerivAt.comp_hasDerivAt 0 h3
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have hk : ∀ t : ℝ, HasDerivAt
        (fun t : ℝ => lam (G (t • u)) - (c + (t : ℂ) * P + 1 / 2 * ((t : ℂ) ^ 2 * Q)))
        (lam (fderiv ℝ G (t • u) u) - (P + (t : ℂ) * Q)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := ((h1.mul_const P).const_add c).add
        (((h1.pow 2).mul_const Q).const_mul (1 / 2 : ℂ))
      refine ((hGl t).sub h2).congr_deriv ?_
      push_cast
      ring
    have hk' : HasDerivAt (fun t : ℝ => lam (fderiv ℝ G (t • u) u) - (P + (t : ℂ) * Q))
        (lam (L u u) - Q) 0 := by
      have h2 := (hcast.mul_const Q).const_add P
      refine (hDl.sub h2).congr_deriv ?_
      ring
    have hO : (fun t : ℝ => lam (G (t • u)) - (c + (t : ℂ) * P + 1 / 2 * ((t : ℂ) ^ 2 * Q)))
        =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 3 := by
      have htend : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 0) := by
        have := (hline 0).continuousAt.tendsto
        simpa using this
      have h1 := hexp.comp_tendsto htend
      have h2 : ((fun w : ℝ × ℝ => ‖w‖ ^ 3) ∘ fun t : ℝ => t • u) =O[𝓝 0]
          fun t : ℝ => ‖t‖ ^ 3 := by
        refine IsBigO.of_bound (‖u‖ ^ 3) (Eventually.of_forall fun t => ?_)
        simp only [Function.comp, norm_smul, mul_pow, norm_pow, norm_mul, norm_norm]
        rw [mul_comm]
      refine (h1.trans h2).congr_left fun t => ?_
      simp only [Function.comp, hu, Prod.smul_mk, smul_eq_mul, hP, hQ]
      push_cast
      ring
    obtain ⟨e1, e2⟩ := deriv_zero_of_isBigO_cube hk hk' hO
    constructor
    · simpa [sub_eq_zero] using e1
    · exact sub_eq_zero.1 e2
  have hsym : L (1, 0) (0, 1) = L (0, 1) (1, 0) :=
    (hG.contDiffAt.isSymmSndFDerivAt (by simp)) (1, 0) (0, 1)
  have hsplit : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by simp
  have h10 := (key 1 0).2
  have h01 := (key 0 1).2
  have h11 := (key 1 1).2
  have hmix : lam (L (1, 0) (0, 1)) = M := by
    rw [hsplit] at h11
    simp only [map_add, add_apply, hsym] at h11
    rw [h10, h01, ← hsym] at h11
    push_cast at h11
    simp only [one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_mul, zero_mul,
      mul_zero, mul_one, add_zero, zero_add] at h11
    linear_combination (1 / 2 : ℂ) * h11
  have hrow : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (1, 0) s := fun s =>
    (hasDerivAt_id s).prodMk (hasDerivAt_const s (0 : ℝ))
  have hcol : ∀ (s t : ℝ), HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) t := fun s t =>
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun s : ℝ => G (s, 0)) (fderiv ℝ G 0 (1, 0)) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ)
        (hGd ((0 : ℝ), (0 : ℝ))).hasFDerivAt (hrow 0)
    rw [h1.deriv]
    simpa using (key 1 0).1
  · have h1 : HasDerivAt (fun t : ℝ => G (0, t)) (fderiv ℝ G 0 (0, 1)) 0 :=
      (show HasFDerivAt G (fderiv ℝ G ((0 : ℝ), (0 : ℝ))) ((0 : ℝ), (0 : ℝ)) from
        (hGd _).hasFDerivAt).comp_hasDerivAt 0 (hcol 0 0)
    rw [h1.deriv]
    simpa using (key 0 1).1
  · have hin : ∀ s : ℝ, deriv (fun t : ℝ => G (s, t)) 0 = fderiv ℝ G (s, 0) (0, 1) := fun s =>
      ((hGd (s, 0)).hasFDerivAt.comp_hasDerivAt 0 (hcol s 0)).deriv
    have hfun : (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) =
        fun s : ℝ => fderiv ℝ G (s, 0) (0, 1) := funext hin
    have hout : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, 0) (0, 1)) (L (1, 0) (0, 1)) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, 0)) (L (1, 0)) 0 :=
        HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ)
          (hD1d ((0 : ℝ), (0 : ℝ))).hasFDerivAt (hrow 0)
      have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) ((0, 1) : ℝ × ℝ))
      simpa using h2
    rw [hfun, hout.deriv]
    exact hmix
section Kernels
variable {J : Type}
theorem matrixEntry_comp (hE : MatrixEntryProperties J) (X Y : BddOp (IndexL2 J)) :
    matrixEntry (X.comp Y) = compKernel (matrixEntry X) (matrixEntry Y) := by
  funext ι' ι
  exact ((hE X).2 (Y (basisVec ι)) ι').2
open Classical in
theorem basisVec_apply (ι j : J) :
    (basisVec ι : IndexL2 J) j = if j = ι then 1 else 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.GaugeConjugation.basisVec_apply <;> assumption
def entryCLM (ι' ι : J) : BddOp (IndexL2 J) →L[ℝ] ℂ :=
  ((lp.evalCLM ℂ (fun _ : J => ℂ) 2 ι').comp
    (ContinuousLinearMap.apply ℂ (IndexL2 J) (basisVec ι))).restrictScalars ℝ
end Kernels
theorem matrixEntry_one (I : PeriodicData) :
    matrixEntry (1 : BddOp (IndexL2 I.Carrier)) = idKernel I := by
  classical
  funext ι' ι
  show (basisVec ι : IndexL2 I.Carrier) ι' = _
  rw [basisVec_apply]
  simp only [idKernel]
section Resolvent
variable {J B : Type} {pos : J → InfiniteLattice.AmbientSpace} {tail : B → InfiniteLattice.AmbientSpace}
  {m m' : ℕ} {z C : ℝ} {T : (B → ℝ) → BddOp (IndexL2 J)}
theorem shifted_bounded_below (hset : IsLocalExpansionSetting pos tail m m' z C T) :
    IsBoundedBelowBy (addScalar (T fun _ => 0) z) (z / 2) := by
  obtain ⟨r, hr, hlow⟩ := hset.lower_bound
  exact hlow (fun _ => 0) fun _ => by simpa using hr.le
theorem baseResolvent_inverse (hset : IsLocalExpansionSetting pos tail m m' z C T) :
    addScalar (T fun _ => 0) z * baseResolvent T z 0 = 1 ∧
      baseResolvent T z 0 * addScalar (T fun _ => 0) z = 1 := by
  have h := ((hset.space.logShifted (T fun _ => 0)
    ⟨hset.family.selfAdjoint _, shifted_bounded_below hset⟩).1 0 le_rfl).1
  have h0 : addScalar (addScalar (T fun _ => 0) z) 0 = addScalar (T fun _ => 0) z := by
    simp [addScalar, scalarOp]
  unfold baseResolvent
  rw [h0] at h ⊢
  exact h
theorem matrixEntry_base_le (hset : IsLocalExpansionSetting pos tail m m' z C T) (ι' ι : J) :
    ‖matrixEntry (T fun _ => 0) ι' ι‖ ≤ C := by
  obtain ⟨E, Q, -, -, hQ, heq⟩ := hset.family.entry_smooth ι' ι
  rw [heq]
  simpa using hQ 0 (by norm_num) fun b => (0 : ℝ)
theorem baseResolvent_decay (hset : IsLocalExpansionSetting pos tail m m' z C T) (ι' ι : J) :
    ‖matrixEntry (baseResolvent T z 0) ι' ι‖ ≤
      (z / 4)⁻¹ * Real.exp (-resolventDecayRate z C * TorusMetric.euclidNormVec (pos ι' - pos ι)) := by
  have h := hset.space.resolventDecay (T fun _ => 0) (hset.family.selfAdjoint _) (shifted_bounded_below hset)
    (matrixEntry_base_le hset) (hset.family.finite_range _) 0 le_rfl ι' ι
  simpa [baseResolvent] using h
end Resolvent
theorem resolventDecayRate_pos {z C : ℝ} (hz : 0 < z) (hC : 0 < C) : 0 < resolventDecayRate z C := by apply _root_.YangMills.Construction.Tower.ResolventDecay.resolventDecayRate_pos <;> assumption
theorem inverse_shiftInvariant {I : PeriodicData} (hI : IsPeriodic I)
    (hE : MatrixEntryProperties I.Carrier) (A R : BddOp (IndexL2 I.Carrier))
    (hAR : A * R = 1) (hRA : R * A = 1)
    (hcov : ∀ (n : Fin 4 → ℤ) ι' ι, matrixEntry A (I.translate n ι') (I.translate n ι) = matrixEntry A ι' ι) :
    IsShiftInvariant I I (matrixEntry R) := by
  classical
  intro n ι' ι
  let σ : I.Carrier ≃ I.Carrier :=
    { toFun := I.translate n
      invFun := I.translate (-n)
      left_inv := fun x => by rw [← hI.translate_add]; simp [hI.translate_zero]
      right_inv := fun x => by rw [← hI.translate_add]; simp [hI.translate_zero] }
  set f : IndexL2 I.Carrier := R (basisVec (σ ι)) with hf
  have hmem : Memℓp (fun κ => f (σ κ)) 2 := by
    have h := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num)] at h ⊢
    exact (σ.summable_iff (f := fun κ => ‖f κ‖ ^ (2 : ENNReal).toReal)).2 h
  let v : IndexL2 I.Carrier := ⟨fun κ => f (σ κ), hmem⟩
  have hAf : A f = basisVec (σ ι) := DFunLike.congr_fun hAR (basisVec (σ ι))
  have hAv : A v = basisVec ι := by
    apply lp.ext
    funext j
    have h1 := ((hE A).2 v j).2
    have h2 := ((hE A).2 f (σ j)).2
    have h4 : ∑' κ, matrixEntry A j κ * v κ = ∑' κ, matrixEntry A (σ j) κ * f κ := by
      rw [← σ.tsum_eq (fun κ => matrixEntry A (σ j) κ * f κ)]
      refine tsum_congr fun κ => ?_
      show matrixEntry A j κ * f (σ κ) = matrixEntry A (I.translate n j) (I.translate n κ) * f (σ κ)
      rw [hcov n j κ]
    rw [h1, h4, ← h2, hAf, basisVec_apply, basisVec_apply]
    simp [σ.injective.eq_iff]
  have hv : v = R (basisVec ι) := by
    have h : R (A v) = v := DFunLike.congr_fun hRA v
    rw [hAv] at h
    exact h.symm
  have h := congrArg (fun w : IndexL2 I.Carrier => w ι') hv
  exact h
section Coefficients
variable {F : PeriodicData}
theorem fieldValues_fieldExtend {A : Set F.Carrier} {l : ℕ} (e : Fin l ≃ A)
    (w : Coordinates.ComplexCoordinates l) : fieldValues e (fieldExtend e w) = w := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.fieldValues_fieldExtend <;> assumption
theorem norm_fieldExtend_le {A : Set F.Carrier} {l : ℕ} (e : Fin l ≃ A)
    (w : Coordinates.ComplexCoordinates l) (κ : F.Carrier) : ‖fieldExtend e w κ‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.norm_fieldExtend_le <;> assumption
theorem norm_siteIndicator_le (κ κ' : F.Carrier) : ‖siteIndicator F κ κ'‖ ≤ 1 := by
  unfold siteIndicator
  split_ifs <;> simp
end Coefficients
theorem variation_entries_eq_coeffs
    (hTay : PeriodicOperators.CoeffsOnSuperset.Claim)
    {F I : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I) {B : Type}
    (Φ : B → F.Carrier) {z : ℝ} {T : (B → ℝ) → BddOp (IndexL2 I.Carrier)}
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hm : IsLocalWith F I I S ρ R) (b b' : B)
    (hC2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => T (twoBondField b b' p.1 p.2)))
    (hread : ∀ (s t : ℝ) (ι' ι : I.Carrier),
      S ((s : ℂ) • siteIndicator F (Φ b) + (t : ℂ) • siteIndicator F (Φ b')) ι' ι =
        matrixEntry (addScalar (T (twoBondField b b' s t)) z) ι' ι)
    (ι' ι : I.Carrier) :
    matrixEntry (firstVar T b) ι' ι = coeffOne F I I S (siteIndicator F (Φ b)) ι' ι ∧
      matrixEntry (firstVar T b') ι' ι = coeffOne F I I S (siteIndicator F (Φ b')) ι' ι ∧
      matrixEntry (secondVar T b b') ι' ι =
        coeffTwo F I I S (siteIndicator F (Φ b)) (siteIndicator F (Φ b')) ι' ι := by
  obtain ⟨l, e, h, -, hh⟩ := hm.holo_entry ι' ι
  obtain ⟨φ, β, ⟨hsymm, hexp⟩, hφ, hβ⟩ := hTay F I I hF hI hI S ρ R hm ι' ι _ l e subset_rfl
  set u := siteIndicator F (Φ b) with hu
  set u' := siteIndicator F (Φ b') with hu'
  set a := fieldValues e u with ha
  set a' := fieldValues e u' with ha'
  set Eh := entryFun S ι' ι e with hEh
  set κ : ℂ := matrixEntry (scalarOp ((z : ℝ) : ℂ) :
    BddOp (IndexL2 I.Carrier)) ι' ι with hκ
  let w : ℝ × ℝ → Coordinates.ComplexCoordinates l := fun p => (p.1 : ℂ) • a + (p.2 : ℂ) • a'
  let ζ : ℝ × ℝ → F.Carrier → ℂ := fun p => (p.1 : ℂ) • u + (p.2 : ℂ) • u'
  have hwv : ∀ p, fieldValues e (ζ p) = w p := fun p => rfl
  have hbound : ∀ (p : ℝ × ℝ) (κ' : F.Carrier), ‖ζ p κ'‖ ≤ 2 * ‖p‖ := by
    intro p κ'
    have h1 : ‖u κ'‖ ≤ 1 := norm_siteIndicator_le (Φ b) κ'
    have h2 : ‖u' κ'‖ ≤ 1 := norm_siteIndicator_le (Φ b') κ'
    have h3 : ‖(p.1 : ℂ)‖ ≤ ‖p‖ := by simpa using norm_fst_le p
    have h4 : ‖(p.2 : ℂ)‖ ≤ ‖p‖ := by simpa using norm_snd_le p
    calc ‖ζ p κ'‖ ≤ ‖(p.1 : ℂ) * u κ'‖ + ‖(p.2 : ℂ) * u' κ'‖ := norm_add_le _ _
      _ = ‖(p.1 : ℂ)‖ * ‖u κ'‖ + ‖(p.2 : ℂ)‖ * ‖u' κ'‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖p‖ * 1 + ‖p‖ * 1 := by gcongr
      _ = 2 * ‖p‖ := by ring
  have hw : ∀ p, ‖w p‖ ≤ 2 * ‖p‖ := fun p =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
      rw [← hwv]
      exact hbound p _
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 0, 2 * ‖p‖ < ρ := by
    have hc : Continuous fun p : ℝ × ℝ => 2 * ‖p‖ := by fun_prop
    exact (hc.tendsto 0).eventually_lt_const (by simpa using hm.radius_pos)
  have hEq : ∀ᶠ p : ℝ × ℝ in 𝓝 0,
      matrixEntry (addScalar (T (twoBondField b b' p.1 p.2)) z) ι' ι = Eh (w p) := by
    filter_upwards [hnear] with p hp
    have hζ : IsSupBelow F (ζ p) ρ := ⟨2 * ‖p‖, hp, hbound p⟩
    have hfv : IsSupBelow F (fieldExtend e (w p)) ρ :=
      ⟨2 * ‖p‖, hp, fun κ' => (norm_fieldExtend_le e (w p) κ').trans (hw p)⟩
    rw [← hread p.1 p.2 ι' ι]
    show S (ζ p) ι' ι = S (fieldExtend e (w p)) ι' ι
    rw [hh _ hζ, hh _ hfv, fieldValues_fieldExtend, hwv]
  have hwt : Tendsto w (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => hw p) ?_
    have hc : Continuous fun p : ℝ × ℝ => 2 * ‖p‖ := by fun_prop
    simpa using hc.tendsto 0
  have hE1 := hexp.comp_tendsto hwt
  have hE2 : ((fun x : Coordinates.ComplexCoordinates l => ‖x‖ ^ 3) ∘ w) =O[𝓝 0]
      fun p : ℝ × ℝ => ‖p‖ ^ 3 := by
    refine IsBigO.of_bound (2 ^ 3) (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, norm_pow, norm_norm]
    calc ‖w p‖ ^ 3 ≤ (2 * ‖p‖) ^ 3 := by
          gcongr
          exact hw p
      _ = 2 ^ 3 * ‖p‖ ^ 3 := by ring
  have hexp' : (fun p : ℝ × ℝ => entryCLM ι' ι (T (twoBondField b b' p.1 p.2)) -
      ((Eh 0 - κ) + ((p.1 : ℂ) * φ a + (p.2 : ℂ) * φ a') +
        1 / 2 * ((p.1 : ℂ) ^ 2 * β a a + 2 * (p.1 : ℂ) * (p.2 : ℂ) * β a a' +
          (p.2 : ℂ) ^ 2 * β a' a'))) =O[𝓝 0] fun p : ℝ × ℝ => ‖p‖ ^ 3 := by
    refine (hE1.trans hE2).congr' ?_ EventuallyEq.rfl
    filter_upwards [hEq] with p hp
    have hsplit : matrixEntry (addScalar (T (twoBondField b b' p.1 p.2)) z) ι' ι =
        entryCLM ι' ι (T (twoBondField b b' p.1 p.2)) + κ := rfl
    rw [hsplit] at hp
    have hφw : φ (w p) = (p.1 : ℂ) * φ a + (p.2 : ℂ) * φ a' := by
      simp [w, map_add]
    have hβw : β (w p) (w p) = (p.1 : ℂ) ^ 2 * β a a + 2 * (p.1 : ℂ) * (p.2 : ℂ) * β a a' +
        (p.2 : ℂ) ^ 2 * β a' a' := by
      simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hsymm a' a]
      ring
    simp only [Function.comp, hφw, hβw, ← hp]
    ring
  obtain ⟨r1, r2, r3⟩ := derivs_of_quadratic_expansion _ hC2 (entryCLM ι' ι) _ _ _ _ _ _ hexp'
  have e1 : (fun s : ℝ => T (twoBondField b b' s 0)) = fun s : ℝ => T fun c => s * bondIndicator b c := by
    funext s
    congr 1
    funext c
    simp [twoBondField]
  have e2 : (fun t : ℝ => T (twoBondField b b' 0 t)) = fun t : ℝ => T fun c => t * bondIndicator b' c := by
    funext t
    congr 1
    funext c
    simp [twoBondField]
  have r1' : matrixEntry (deriv (fun s : ℝ => T (twoBondField b b' s 0)) 0) ι' ι = φ a := r1
  have r2' : matrixEntry (deriv (fun t : ℝ => T (twoBondField b b' 0 t)) 0) ι' ι = φ a' := r2
  have r3' : matrixEntry (secondVar T b b') ι' ι = β a a' := r3
  refine ⟨?_, ?_, ?_⟩
  · unfold firstVar
    rw [← e1]
    exact r1'.trans (hφ u)
  · unfold firstVar
    rw [← e2]
    exact r2'.trans (hφ u')
  · exact r3'.trans (hβ u u')
theorem periodicHessianLimit_holds (hBy : PeriodicOperators.LogDetTraces.Claim)
    (hConv : PeriodicOperators.QuotTraceLimits.UnitFieldTracesConverge)
    (hVar : Tower.LocalFamilies.LocalFamilyVariations)
    (hTay : PeriodicOperators.CoeffsOnSuperset.Claim) :
    Tower.LocalFamilies.PeriodicHessianLimit := by
  intro F I B Φ tail m m' z C T S hF hI hz hC hS hset hread b b' ε hε
  obtain ⟨ρ, R, hm⟩ := hS
  have hE := hset.space.entryFacts
  obtain ⟨hAR, hRA⟩ := baseResolvent_inverse hset
  have hzero : coeffZero F I I S = matrixEntry (addScalar (T fun _ => 0) z) := by
    funext ι' ι
    have h := hread b b' 0 0 ι' ι
    have h0 : twoBondField b b' 0 0 = fun _ => (0 : ℝ) := by
      funext c
      simp [twoBondField]
    rw [h0] at h
    simpa [coeffZero] using h
  have hcov : ∀ (n : Fin 4 → ℤ) ι' ι,
      matrixEntry (addScalar (T fun _ => 0) z) (I.translate n ι') (I.translate n ι) =
        matrixEntry (addScalar (T fun _ => 0) z) ι' ι := by
    intro n ι' ι
    have hb : IsSupBelow F (0 : F.Carrier → ℂ) ρ := ⟨0, hm.radius_pos, fun _ => by simp⟩
    have h := hm.shift_covariant 0 hb n ι' ι
    have ht : shiftField F n (0 : F.Carrier → ℂ) = 0 := rfl
    rw [ht] at h
    have hz' := fun x y => congrFun (congrFun hzero x) y
    simp only [coeffZero] at hz'
    rw [← hz', ← hz']
    exact h
  have hper : IsPeriodicKernel I I (matrixEntry (baseResolvent T z 0)) :=
    ⟨inverse_shiftInvariant hI hE _ _ hAR hRA hcov, (z / 4)⁻¹, resolventDecayRate z C, by positivity,
      resolventDecayRate_pos hz hC, fun ι' ι => baseResolvent_decay hset ι' ι⟩
  have h1 : compKernel (coeffZero F I I S) (matrixEntry (baseResolvent T z 0)) =
      idKernel I := by
    rw [hzero, ← matrixEntry_comp hE, ← matrixEntry_one I]
    exact congrArg matrixEntry hAR
  have h2 : compKernel (matrixEntry (baseResolvent T z 0)) (coeffZero F I I S) =
      idKernel I := by
    rw [hzero, ← matrixEntry_comp hE, ← matrixEntry_one I]
    exact congrArg matrixEntry hRA
  have hC2 := (hVar I.Carrier B I.pos tail m m' z C T hz hC hset b b').1
  have hent := variation_entries_eq_coeffs hTay hF hI Φ hm b b' hC2 (hread b b')
  have c1 : matrixEntry (firstVar T b) = coeffOne F I I S (siteIndicator F (Φ b)) :=
    funext fun ι' => funext fun ι => (hent ι' ι).1
  have c2 : matrixEntry (firstVar T b') = coeffOne F I I S (siteIndicator F (Φ b')) :=
    funext fun ι' => funext fun ι => (hent ι' ι).2.1
  have c3 : matrixEntry (secondVar T b b') =
      coeffTwo F I I S (siteIndicator F (Φ b)) (siteIndicator F (Φ b')) :=
    funext fun ι' => funext fun ι => (hent ι' ι).2.2
  have hnum : kernelTraceDefect F I S (matrixEntry (baseResolvent T z 0)) (siteIndicator F (Φ b))
      (siteIndicator F (Φ b')) = variationTrace T z b b' := by
    unfold kernelTraceDefect variationTrace diagTrace diagSum
    rw [← c1, ← c2, ← c3, ← matrixEntry_comp hE, ← matrixEntry_comp hE, ← matrixEntry_comp hE,
      ← matrixEntry_comp hE, ContinuousLinearMap.comp_assoc]
  obtain ⟨hunit, hlim⟩ := hConv F I hF hI S ρ R hm _ hper h1 h2
  have hl := hlim (Φ b) (Φ b')
  rw [hnum] at hl
  obtain ⟨s₁, hs₁⟩ := Metric.tendsto_atTop.1 hl ε hε
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 hunit
  obtain ⟨s₃, hs₃⟩ := exists_nat_gt (4 * R)
  refine ⟨max (max s₁ s₂) (max s₃ 1), fun s hs N e => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2 : s₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs3 : s₃ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs4 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hlt : 4 * R < s := lt_of_lt_of_le hs₃ (by exact_mod_cast hs3)
  rw [hBy F I hF hI S ρ R hm s hs4 hlt (hs₂ s hs2) N e, ← dist_eq_norm]
  exact hs₁ s hs1
end Tower.LocalFamilies.HessianLimitProof
end
end YangMills.Construction
