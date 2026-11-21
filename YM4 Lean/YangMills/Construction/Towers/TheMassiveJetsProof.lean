import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJetProof
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.NormsOfJetsAndAffineFamiliesOfInvertibleJets
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.TheMassiveJets
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets
open PeriodicOperators PeriodicOperators.JetQuad
section Generic
variable {I : PeriodicData}
theorem quotWeight_one_pos (hQ : Quotients.QuotientTransposeNorm) (hI : IsPeriodic I)
    (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotWeight_pos <;> assumption
theorem norm_trace_le_card_mul (hQ : Quotients.QuotientTransposeNorm)
    (hH : HomNorm.Claim) (hI : IsPeriodic I) (M : QuotHom I I) :
    ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) M‖ ≤
      (Nat.card I.UnitQuot : ℝ) * (quotHomNorm M).toReal := by
  classical
  have : Finite I.UnitQuot := hI.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite I.UnitQuot
  have hent : ∀ c : I.UnitQuot, ‖linearMapEntry M c c‖ ≤ (quotHomNorm M).toReal := by
    intro c
    have h := (hH I I hI hI).2.2.2.1 M c c
    have hw := quotWeight_one_pos hQ hI c
    rw [div_self hw.ne'] at h
    simpa [RealPower.sqrtOf, RealPower.rpowPos] using h
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I.UnitQuot) M, Matrix.trace]
  calc ‖∑ c, (LinearMap.toMatrix (Pi.basisFun ℂ I.UnitQuot) (Pi.basisFun ℂ I.UnitQuot) M).diag c‖
      ≤ ∑ c, ‖(LinearMap.toMatrix (Pi.basisFun ℂ I.UnitQuot) (Pi.basisFun ℂ I.UnitQuot) M).diag c‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : I.UnitQuot, (quotHomNorm M).toReal := by
        refine Finset.sum_le_sum fun c _ => ?_
        have : (LinearMap.toMatrix (Pi.basisFun ℂ I.UnitQuot) (Pi.basisFun ℂ I.UnitQuot) M).diag c =
            linearMapEntry M c c := by
          simp [Matrix.diag, linearMapEntry]
        rw [this]
        exact hent c
    _ = (Nat.card I.UnitQuot : ℝ) * (quotHomNorm M).toReal := by
        simp [Nat.card_eq_fintype_card]
theorem norm_traceNumber_le_card_mul (hQ : Quotients.QuotientTransposeNorm)
    (hH : HomNorm.Claim) (hI : IsPeriodic I) {δ : ℝ} {p : Fin 4 → ℂ}
    (X : JetQuad I I) (hX : jetNorm δ p X < ∞) :
    ‖traceNumber X‖ ≤ (Nat.card I.UnitQuot : ℝ) * (jetNorm δ p X).toReal := by
  have hb : ∀ κ : InfiniteLattice.AmbientSpace,
      ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) (X.f11 (toComplexVec κ))‖ ≤
        (Nat.card I.UnitQuot : ℝ) * (jetNorm δ p X).toReal := by
    intro κ
    refine (norm_trace_le_card_mul hQ hH hI _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine ENNReal.toReal_mono hX.ne ?_
    have hmem : toComplexVec κ ∈ realDualPoints := fun μ => by simp [toComplexVec]
    refine le_trans ?_ (le_add_self (a := _) (b := _))
    exact le_iSup₂ (f := fun κ (_ : κ ∈ realDualPoints) => quotHomNorm (X.f11 κ)) _ hmem
  have hvol : MeasureTheory.volume.real
      (Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) = (2 * Real.pi) ^ 4 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_neg_eq_add, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hint := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume)
    (s := Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi))
    (f := fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) (X.f11 (toComplexVec κ)))
    (C := (Nat.card I.UnitQuot : ℝ) * (jetNorm δ p X).toReal)
    (by rw [Real.volume_Icc_pi]; exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top) (fun κ _ => hb κ)
  rw [traceNumber, torusAverage, norm_mul]
  rw [hvol] at hint
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 4 := by positivity
  have hn : ‖((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ)‖ = ((2 * Real.pi) ^ 4)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpi.le)]
  rw [hn]
  calc ((2 * Real.pi) ^ 4)⁻¹ * _ ≤ ((2 * Real.pi) ^ 4)⁻¹ *
        ((Nat.card I.UnitQuot : ℝ) * (jetNorm δ p X).toReal * (2 * Real.pi) ^ 4) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi.le)
    _ = _ := by field_simp
theorem eqAsJet_trans {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} {A B C : JetQuad I I'}
    (h : EqAsJet δ p A B) (h' : EqAsJet δ p B C) : EqAsJet δ p A C := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
theorem eqAsJet_symm {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} {A B : JetQuad I I'}
    (h : EqAsJet δ p A B) : EqAsJet δ p B A :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem addScalarJet_eq_add_smul_one {I : PeriodicData} (T : JetQuad I I) (z z' : ℝ) :
    addScalarJet T z' =
      add (addScalarJet T z) (smul (((z' - z : ℝ)) : ℂ) (one I)) := by
  simp only [addScalarJet, add, smul, one]
  ext1
  · funext κ
    apply LinearMap.ext
    intro f
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Complex.ofReal_sub]
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  all_goals simp
theorem invJet_addScalarJet_resolvent (hL : JetDomains.OpFunJetTheory)
    (hC : JetCalculus.Claim) (hA : QuadAlgebra.Claim)
    (hE : JetArgumentsAndEqualJets) {I : PeriodicData} {δ : ℝ}
    {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hI : IsPeriodic I)
    (T : JetQuad I I) (z z' : ℝ) (h : IsInvertibleJet δ p (addScalarJet T z))
    (h' : IsInvertibleJet δ p (addScalarJet T z')) :
    EqAsJet δ p (invJet p (addScalarJet T z))
      (add (invJet p (addScalarJet T z'))
        (smul (((z' - z : ℝ)) : ℂ)
          (mul p (invJet p (addScalarJet T z')) (invJet p (addScalarJet T z))))) := by
  have hF := hL.2.2 I I I hI hI hI δ p hδ hp
  have hCalc := hC δ p hδ hp
  have hinv := hCalc.2.2.2.2.1 I hI
  have hprod := hCalc.1 I I I I hI hI hI hI
  obtain ⟨hR, hRT, -, -, -⟩ := hinv _ h'
  obtain ⟨hC', -, hTC, -, -⟩ := hinv _ h
  have hBil := (hA.1 p I I I)
  set R := invJet p (addScalarJet T z') with hRdef
  set C := invJet p (addScalarJet T z) with hCdef
  have hTz := h.isJet
  have hTz' := h'.isJet
  have hone := hF.one_isJet
  have hcongr := fun (X X' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (e : EqAsJet δ p X X') (Y Y' : JetQuad I I) (hY : IsJet δ p Y) (hY' : IsJet δ p Y')
      (e' : EqAsJet δ p Y Y') =>
    (hE.2.1 δ p I I hI hI X X' hX hX' e).2.2.2.2 I hI Y Y' hY hY' e'
  have hrefl : ∀ X : JetQuad I I, EqAsJet δ p X X := fun X =>
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have e1 : EqAsJet δ p C (mul p R (mul p (addScalarJet T z') C)) := by
    have a1 : EqAsJet δ p (mul p (mul p R (addScalarJet T z')) C) (mul p (one I) C) :=
      hcongr _ _ (hF.mul_isJet _ _ hR hTz') hone hRT C C hC' hC' (hrefl C)
    rw [(hBil.2.2.2.2 C).1] at a1
    exact eqAsJet_trans (eqAsJet_symm a1) (hprod _ _ _ hR hTz' hC').1
  have e2 : mul p (addScalarJet T z') C =
      add (mul p (addScalarJet T z) C) (smul (((z' - z : ℝ)) : ℂ) C) := by
    rw [addScalarJet_eq_add_smul_one T z z', hBil.1, hBil.2.2.1, (hBil.2.2.2.2 C).1]
  rw [e2, hBil.2.1, hBil.2.2.2.1] at e1
  have e3 : EqAsJet δ p (mul p R (mul p (addScalarJet T z) C)) R := by
    have a3 := hcongr R R hR hR (hrefl R) _ _ (hF.mul_isJet _ _ hTz hC') hone hTC
    rwa [(hBil.2.2.2.2 R).2] at a3
  have hRC := hF.mul_isJet _ _ hR hC'
  have hs := hF.smul_isJet (((z' - z : ℝ)) : ℂ) _ hRC
  exact eqAsJet_trans e1 ((hE.2.1 δ p I I hI hI _ _ (hF.mul_isJet _ _ hR
    (hF.mul_isJet _ _ hTz hC')) hR e3).2.2.2.1 _ _ hs hs (hrefl _))
theorem logNumber_addScalarJet_deriv (hL : JetDomains.OpFunJetTheory)
    (hC : JetCalculus.Claim) (hA : QuadAlgebra.Claim)
    (hE : JetArgumentsAndEqualJets)
    (hN : JetNormsAffine.Claim)
    (hQ : Quotients.QuotientTransposeNorm) (hH : HomNorm.Claim)
    {I : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    (hI : IsPeriodic I) (T : JetQuad I I) (hT : IsJet δ p T) (a : ℝ) (ha : 0 < a)
    (hinv : ∀ z, a < z → IsInvertibleJet δ p (addScalarJet T z))
    (hbd : ∀ z, a < z → ∀ κ ∈ imStrip (2 * δ),
      quotHomNorm (quotHomInverse ((addScalarJet T z).f00 κ)) ≤ ENNReal.ofReal (3 / z)) :
    ContDiffOn ℝ 2 (fun z : ℝ => logNumber p (addScalarJet T z)) (Ioi a) ∧
      ∀ z ∈ Ioi a,
        deriv (fun y : ℝ => logNumber p (addScalarJet T y)) z =
            traceNumber (invJet p (addScalarJet T z)) ∧
          deriv (deriv fun y : ℝ => logNumber p (addScalarJet T y)) z =
            -traceNumber (invJetSq p (addScalarJet T z)) := by
  have hF := hL.2.2 I I I hI hI hI δ p hδ hp
  have hCalc := hC δ p hδ hp
  have hAlg := hA.2 δ p hδ hp I I hI hI
  have hBil := hA.1 p I I I
  have hone := hF.one_isJet
  have hR : ∀ z, a < z → IsJet δ p (invJet p (addScalarJet T z)) := fun z hz =>
    (hCalc.2.2.2.2.1 I hI _ (hinv z hz)).1
  set ℓ : ℝ → ℂ := fun z => logNumber p (addScalarJet T z) with hℓ
  set g : ℝ → ℂ := fun z => traceNumber (invJet p (addScalarJet T z)) with hg
  set h : ℝ → ℂ := fun z => traceNumber (invJetSq p (addScalarJet T z)) with hh
  have key : ∀ z, a < z → HasDerivAt ℓ (g z) z ∧ HasDerivAt g (-h z) z ∧ ContinuousAt h z := by
    intro z hz
    have hmid : a < (a + z) / 2 := by linarith
    have hmid' : (a + z) / 2 < z := by linarith
    set J : Set ℝ := Icc ((a + z) / 2) (z + 1) with hJ
    have hJa : ∀ t ∈ J, a < t := fun t ht => lt_of_lt_of_le hmid ht.1
    have hzJ : z ∈ J := ⟨hmid'.le, by linarith⟩
    have hJn : J ∈ 𝓝 z := Icc_mem_nhds hmid' (by linarith)
    obtain ⟨hsup, ⟨Lip, hLip⟩, hcontC, -, hder, -⟩ :=
      (hN δ p hδ hp I I hI hI).2 T (one I) hT hone J isCompact_Icc ordConnected_Icc
        ⟨(a + z) / 2, ⟨le_rfl, by linarith⟩, z + 1, ⟨by linarith, le_rfl⟩, by linarith [hmid'.ne]⟩ (fun t ht => hinv t (hJa t ht))
        ⟨ENNReal.ofReal (3 / ((a + z) / 2)), ENNReal.ofReal_lt_top, fun t ht =>
          iSup₂_le fun κ hκ => (hbd t (hJa t ht) κ hκ).trans
            (ENNReal.ofReal_le_ofReal
              (div_le_div_of_nonneg_left (by norm_num) (by linarith) ht.1))⟩
    have aff : ∀ t, JetNormsAffine.affinePath T (one I) t =
        addScalarJet T t := fun _ => rfl
    simp only [aff] at hsup hLip hcontC hder
    set C := invJet p (addScalarJet T z) with hCdef
    have hCj : IsJet δ p C := hR z hz
    refine ⟨?_, ?_, ?_⟩
    · have h1 := hder z hzJ
      rw [(hBil.2.2.2.2 _).2] at h1
      exact h1.hasDerivAt hJn
    · have hdiff : ∀ t ∈ J, g t - g z =
          -(((t - z : ℝ)) : ℂ) * traceNumber (mul p C (invJet p (addScalarJet T t))) := by
        intro t ht
        have e := invJet_addScalarJet_resolvent hL hC hA hE hδ hp hI T z t (hinv z hz) (hinv t (hJa t ht))
        have et := ((hE.2.2 δ p I hI _ _ hCj (hF.add_isJet _ _ (hR t (hJa t ht))
          (hF.smul_isJet _ _ (hF.mul_isJet _ _ (hR t (hJa t ht)) hCj))) e).1)
        rw [hAlg.2.2.2.1 _ _ (hR t (hJa t ht))
            (hF.smul_isJet _ _ (hF.mul_isJet _ _ (hR t (hJa t ht)) hCj)),
          hAlg.2.2.2.2 _ _ (hF.mul_isJet _ _ (hR t (hJa t ht)) hCj),
          ((hCalc.2.2.2.2.2.1 I I hI hI).1 _ _ (hR t (hJa t ht)) hCj)] at et
        simp only [hg]
        rw [← hCdef, et]
        ring
      have hcont : ContinuousAt (fun t => traceNumber (mul p C (invJet p (addScalarJet T t)))) z :=
        (hcontC C hCj z hzJ).continuousAt hJn
      rw [hasDerivAt_iff_tendsto_slope]
      have hlim : Tendsto (fun t => -traceNumber (mul p C (invJet p (addScalarJet T t))))
          (𝓝[≠] z) (𝓝 (-h z)) := (hcont.tendsto.neg).mono_left nhdsWithin_le_nhds
      refine hlim.congr' ?_
      have hev : ∀ᶠ t in 𝓝[≠] z, t ∈ J ∧ t ≠ z :=
        (eventually_nhdsWithin_of_eventually_nhds hJn).and self_mem_nhdsWithin
      filter_upwards [hev] with t ht
      have hne : (((t - z : ℝ)) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr ht.2
      rw [slope_def_module, hdiff t ht.1]
      rw [Complex.real_smul]
      push_cast at hne ⊢
      field_simp
    · set B := ⨆ t ∈ J, jetNorm δ p (invJet p (addScalarJet T t)) with hB
      have hRB : ∀ t ∈ J, jetNorm δ p (invJet p (addScalarJet T t)) ≤ B := fun t ht =>
        le_iSup₂ (f := fun t (_ : t ∈ J) => jetNorm δ p (invJet p (addScalarJet T t))) t ht
      have hprod : ∀ X Y : JetQuad I I, IsJet δ p X → IsJet δ p Y → ∀ u v : ℝ≥0∞,
          jetNorm δ p X ≤ u → jetNorm δ p Y ≤ v → u * v < ∞ →
          ‖traceNumber (mul p X Y)‖ ≤ (Nat.card I.UnitQuot : ℝ) * (u * v).toReal := by
        intro X Y hX hY u v hu hv huv
        have hXY : jetNorm δ p (mul p X Y) ≤ u * v :=
          ((hCalc.1 I I I I hI hI hI hI X Y (one I) hX hY hone).2).trans (mul_le_mul' hu hv)
        refine (norm_traceNumber_le_card_mul hQ hH hI _ (lt_of_le_of_lt hXY huv)).trans ?_
        exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono huv.ne hXY) (Nat.cast_nonneg _)
      have hbound : ∀ t ∈ J, ‖h t - h z‖ ≤
          ((Nat.card I.UnitQuot : ℝ) * (2 * (Lip : ℝ) * B.toReal)) * |t - z| := by
        intro t ht
        have hRt := hR t (hJa t ht)
        set R := invJet p (addScalarJet T t) with hRdef
        set D := add R (smul (-1) C) with hDdef
        have hDj : IsJet δ p D := hF.add_isJet _ _ hRt (hF.smul_isJet _ _ hCj)
        have hD : jetNorm δ p D ≤ (Lip : ℝ≥0∞) * ENNReal.ofReal |t - z| := hLip z hzJ t ht
        have hRR := hF.mul_isJet _ _ hRt hRt
        have hCR := hF.mul_isJet _ _ hCj hRt
        have hCC := hF.mul_isJet _ _ hCj hCj
        have e : h t - h z = traceNumber (mul p D R) + traceNumber (mul p C D) := by
          have e1 : mul p D R = add (mul p R R) (smul (-1) (mul p C R)) := by
            rw [hDdef, hBil.1, hBil.2.2.1]
          have e2 : mul p C D = add (mul p C R) (smul (-1) (mul p C C)) := by
            rw [hDdef, hBil.2.1, hBil.2.2.2.1]
          rw [e1, e2, hAlg.2.2.2.1 _ _ hRR (hF.smul_isJet _ _ hCR),
            hAlg.2.2.2.1 _ _ hCR (hF.smul_isJet _ _ hCC), hAlg.2.2.2.2 _ _ hCR,
            hAlg.2.2.2.2 _ _ hCC]
          simp only [hh, invJetSq]
          rw [← hRdef, ← hCdef]
          ring
        have hu : (Lip : ℝ≥0∞) * ENNReal.ofReal |t - z| < ∞ :=
          ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top
        have hval : ((Lip : ℝ≥0∞) * ENNReal.ofReal |t - z| * B).toReal =
            (Lip : ℝ) * |t - z| * B.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
            ENNReal.coe_toReal]
        have b1 := hprod D R hDj hRt _ B hD (hRB t ht) (ENNReal.mul_lt_top hu hsup)
        have b2 := hprod C D hCj hDj B _ (hRB z hzJ) hD (ENNReal.mul_lt_top hsup hu)
        rw [mul_comm B, hval] at b2
        rw [hval] at b1
        rw [e]
        refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
        ring
      have hlim : Tendsto (fun t =>
          ((Nat.card I.UnitQuot : ℝ) * (2 * (Lip : ℝ) * B.toReal)) * |t - z|) (𝓝 z) (𝓝 0) := by
        have hc : Continuous fun t : ℝ =>
            ((Nat.card I.UnitQuot : ℝ) * (2 * (Lip : ℝ) * B.toReal)) * |t - z| := by
          fun_prop
        simpa using hc.tendsto z
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
      filter_upwards [hJn] with t ht using hbound t ht
  have hopen : IsOpen (Ioi a) := isOpen_Ioi
  have hderiv : ∀ z ∈ Ioi a, deriv ℓ z = g z := fun z hz => (key z hz).1.deriv
  have hev : ∀ z ∈ Ioi a, deriv ℓ =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [hopen.mem_nhds hz] with t ht using hderiv t ht
  have hderiv1 : ∀ z ∈ Ioi a, HasDerivAt (deriv ℓ) (-h z) z := fun z hz =>
    (key z hz).2.1.congr_of_eventuallyEq (hev z hz)
  have hderiv2 : ∀ z ∈ Ioi a, deriv (deriv ℓ) z = -h z := fun z hz => (hderiv1 z hz).deriv
  refine ⟨?_, fun z hz => ⟨hderiv z hz, hderiv2 z hz⟩⟩
  have two : (2 : WithTop ℕ∞) = 1 + 1 := one_add_one_eq_two.symm
  rw [two, contDiffOn_succ_iff_deriv_of_isOpen hopen]
  refine ⟨fun z hz => (key z hz).1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_deriv_of_isOpen hopen]
  refine ⟨fun z hz => (hderiv1 z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  intro z hz
  have hc : ContinuousAt (fun t => -h t) z := (key z hz).2.2.neg
  have he : deriv (deriv ℓ) =ᶠ[𝓝 z] fun t => -h t := by
    filter_upwards [hopen.mem_nhds hz] with t ht using hderiv2 t ht
  exact (hc.congr he.symm).continuousWithinAt
end Generic
section Numbers
theorem finestMesh_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    0 < finestMesh L k := by
  have h : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  exact zpow_pos h _
theorem finestMesh_le_one {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    finestMesh L k ≤ 1 := by
  have h : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  exact zpow_le_one_of_nonpos₀ h (by omega)
theorem stripHalfWidth_pos_and_le (h : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    0 < stripHalfWidth ∧ stripHalfWidth ≤ 1 / 64 := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hI, -, -⟩ := h
  have hdom : FreeStrip.halfSupRate.Dom := Part.dom_iff_mem.mpr ⟨δ₀, hδ₀⟩
  rw [Part.mem_unique (stripHalfWidth_mem hdom) hδ₀]
  exact hI
theorem massWidth_pos (hW : 0 < stripHalfWidth) {z : ℝ} (hz : 0 < z) : 0 < massWidth z :=
  lt_min hW (by have := Real.sqrt_pos.mpr hz; positivity)
theorem massWidth_le_stripHalfWidth : ∀ z : ℝ, massWidth z ≤ stripHalfWidth := fun _ => min_le_left _ _
theorem twentyFive_mul_massWidth_sq_le (hW : 0 < stripHalfWidth) {z : ℝ} (hz : 0 < z) :
    25 * massWidth z ^ 2 ≤ z := by
  have h0 := massWidth_pos hW hz
  have h1 : massWidth z ≤ 1 / 5 * Real.sqrt z := min_le_right _ _
  have h2 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  nlinarith
theorem massWidth_eq_of_le (hW : 0 < stripHalfWidth) {z : ℝ} (hz : 25 * stripHalfWidth ^ 2 ≤ z) :
    massWidth z = stripHalfWidth := by
  refine min_eq_left ?_
  have h : 5 * stripHalfWidth ≤ Real.sqrt z := by
    refine (Real.le_sqrt' (by positivity)).mpr ?_
    nlinarith
  linarith
theorem re_cos_term_ge {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) (w : ℂ) (hw : |w.im| ≤ 1 / 8) :
    -(129 / 128 * w.im ^ 2) ≤ (2 * ((η : ℂ))⁻¹ ^ 2 * (1 - Complex.cos ((η : ℂ) * w))).re := by
  have hcos : (Complex.cos ((η : ℂ) * w)).re =
      Real.cos (η * w.re) * Real.cosh (η * w.im) := by
    have hu : (η : ℂ) * w = ((η * w.re : ℝ) : ℂ) + ((η * w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have aux : ∀ a b : ℝ, (Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)).re =
        Real.cos a * Real.cosh b := by
      intro a b
      rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
        ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
      simp [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re]
    rw [hu, aux]
  have hcast : 2 * ((η : ℂ))⁻¹ ^ 2 = ((2 * η⁻¹ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hcos]
  set y := η * w.im with hy
  set x := η * w.re
  have hyabs : |y| ≤ 1 / 8 := by
    rw [hy, abs_mul, abs_of_pos h0]
    calc η * |w.im| ≤ 1 * (1 / 8) := mul_le_mul h1 hw (abs_nonneg _) zero_le_one
      _ = 1 / 8 := one_mul _
  have hy2 : y ^ 2 ≤ 1 / 64 := by
    have := abs_le.mp hyabs
    nlinarith
  set u := y ^ 2 / 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have e1 : Real.cosh y ≤ Real.exp u := Real.cosh_le_exp_half_sq y
  have e2 := Real.abs_exp_sub_one_sub_id_le (x := u) (by rw [abs_of_nonneg hu0]; linarith)
  have e3 : Real.exp u ≤ 1 + u + u ^ 2 := by
    have := (abs_le.mp e2).2
    linarith
  have e4 : Real.cosh y - 1 ≤ 129 / 128 * u := by nlinarith
  have e5 : Real.cos x * Real.cosh y ≤ Real.cosh y :=
    mul_le_of_le_one_left (Real.cosh_pos y).le (Real.cos_le_one x)
  have e6 : -(129 / 128 * u) ≤ 1 - Real.cos x * Real.cosh y := by linarith
  have hA : 0 ≤ 2 * η⁻¹ ^ 2 := by positivity
  have e7 := mul_le_mul_of_nonneg_left e6 hA
  have hid : 2 * η⁻¹ ^ 2 * (-(129 / 128 * u)) = -(129 / 128 * w.im ^ 2) := by
    rw [hu, hy]
    field_simp
  linarith
theorem denominatorReBound_of_formula {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ)
    (hs : ∀ q : Fin 4 → ℂ, PlaneWaves.symbolSquare L k q =
      ∑ μ, 2 * (((finestMesh L k : ℝ) : ℂ))⁻¹ ^ 2 *
        (1 - Complex.cos (((finestMesh L k : ℝ) : ℂ) * q μ)))
    (hW : 0 < stripHalfWidth ∧ stripHalfWidth ≤ 1 / 64) {z : ℝ} (hz : 0 < z) :
    DenominatorReBound L k z := by
  intro κ hκ m _
  have hd1 := massWidth_le_stripHalfWidth z
  have hd2 := twentyFive_mul_massWidth_sq_le hW.1 hz
  set δ := massWidth z
  have hterm : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), -(129 / 128 * (2 * δ) ^ 2) ≤
      (2 * (((finestMesh L k : ℝ) : ℂ))⁻¹ ^ 2 *
        (1 - Complex.cos (((finestMesh L k : ℝ) : ℂ) * PlaneWaves.shiftedFreq κ m μ))).re := by
    intro μ _
    have him : (PlaneWaves.shiftedFreq κ m μ).im = (κ μ).im := by
      simp [PlaneWaves.shiftedFreq]
    have hb : |(κ μ).im| ≤ 2 * δ := hκ μ
    have hw : |(PlaneWaves.shiftedFreq κ m μ).im| ≤ 1 / 8 := by
      rw [him]
      linarith [hW.2]
    have h := re_cos_term_ge (finestMesh_pos hL k) (finestMesh_le_one hL k) _ hw
    refine le_trans ?_ h
    rw [him]
    have : (κ μ).im ^ 2 ≤ (2 * δ) ^ 2 := by
      have := abs_le.mp hb
      nlinarith
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Complex.add_re, Complex.ofReal_re, hs, Complex.re_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  nlinarith
end Numbers
section Coefficients
open PlaneWaves
variable {L k : ℕ}
theorem finite_vertexClass (hS : IsPeriodic (colourVertices L k 0)) :
    Finite (VertexClass L k) := by
  have := hS.finite_quot
  refine Finite.of_surjective (fun c : (colourVertices L k 0).UnitQuot =>
    Quot.lift (fun ι => (Quot.mk _ ι.2 : VertexClass L k)) ?_ c) ?_
  · rintro ι _ ⟨m, rfl⟩
    exact Quot.sound ⟨_, rfl⟩
  · intro c
    induction c using Quot.ind with
    | mk x => exact ⟨Quot.mk _ ((0 : Fin 3), x), rfl⟩
theorem fourierCoeff_add (hf : Finite (VertexClass L k)) (g g' : Vertex L k 0 → Matrices.ComplexMatrix2)
    (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => g x + g' x) m = fourierCoeff L k g m + fourierCoeff L k g' m := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.fourierCoeff_add <;> assumption
theorem fourierCoeff_smul (hf : Finite (VertexClass L k)) (c : ℂ) (g : Vertex L k 0 → Matrices.ComplexMatrix2)
    (m : Fin 4 → ℤ) :
    fourierCoeff L k (fun x => c • g x) m = c • fourierCoeff L k g m := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.fourierCoeff_smul <;> assumption
theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (fun ι => c ι + c' ι) x = ofPauliCoeffs c x + ofPauliCoeffs c' x := by
  simp only [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
theorem ofPauliCoeffs_smul {σ : Type} (a : ℂ) (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (fun ι => a * c ι) x = a • ofPauliCoeffs c x := by
  simp only [ofPauliCoeffs, Finset.smul_sum, mul_smul]
theorem vertexFourierCoeff_add (hf : Finite (VertexClass L k))
    (l l' : (colourVertices L k 0).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    vertexFourierCoeff L k (l + l') m =
      vertexFourierCoeff L k l m + vertexFourierCoeff L k l' m := by
  have h : vertexFieldOfClasses L k (l + l') =
      fun x => vertexFieldOfClasses L k l x + vertexFieldOfClasses L k l' x := by
    funext x
    exact ofPauliCoeffs_add _ _ x
  rw [vertexFourierCoeff, h]
  exact fourierCoeff_add hf _ _ m
theorem vertexFourierCoeff_smul (hf : Finite (VertexClass L k)) (a : ℂ)
    (l : (colourVertices L k 0).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    vertexFourierCoeff L k (a • l) m = a • vertexFourierCoeff L k l m := by
  have h : vertexFieldOfClasses L k (a • l) = fun x => a • vertexFieldOfClasses L k l x := by
    funext x
    exact ofPauliCoeffs_smul a _ x
  rw [vertexFourierCoeff, h]
  exact fourierCoeff_smul hf _ _ m
theorem edgeFourierCoeff_add (hf : Finite (VertexClass L k))
    (b b' : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (b + b') μ m =
      edgeFourierCoeff L k b μ m + edgeFourierCoeff L k b' μ m := by
  have h : (fun x => edgeFieldOfClasses L k (b + b') (edgeAt L k x μ)) =
      fun x => edgeFieldOfClasses L k b (edgeAt L k x μ) + edgeFieldOfClasses L k b' (edgeAt L k x μ) := by
    funext x
    exact ofPauliCoeffs_add _ _ _
  rw [edgeFourierCoeff, h]
  exact fourierCoeff_add hf _ _ m
theorem edgeFourierCoeff_smul (hf : Finite (VertexClass L k)) (a : ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (a • b) μ m = a • edgeFourierCoeff L k b μ m := by
  have h : (fun x => edgeFieldOfClasses L k (a • b) (edgeAt L k x μ)) =
      fun x => a • edgeFieldOfClasses L k b (edgeAt L k x μ) := by
    funext x
    exact ofPauliCoeffs_smul a _ _
  rw [edgeFourierCoeff, h]
  exact fourierCoeff_smul hf _ _ m
theorem pauliNorm_smul (c : ℂ) (X : Matrices.ComplexMatrix2) : pauliNorm (c • X) = ‖c‖ * pauliNorm X := by
  by_cases hc : c = 0
  · subst hc
    have h0 : ∀ a, pauliCoeff a (0 : Matrices.ComplexMatrix2) = 0 := fun a => by
      have h := map_zero (OneLoop.pauliCoordinateEquiv)
      have hm : (0 : Matrices.ComplexMatrix2) ∈ Matrices.ComplexMatrix2.traceless := Submodule.zero_mem _
      simp only [pauliCoeff, dif_pos hm]
      exact congrFun h a
    simp [pauliNorm, h0]
  have hcoef : ∀ a, pauliCoeff a (c • X) = c * pauliCoeff a X := by
    intro a
    by_cases hX : X ∈ Matrices.ComplexMatrix2.traceless
    · have hcX : c • X ∈ Matrices.ComplexMatrix2.traceless := Submodule.smul_mem _ _ hX
      simp only [pauliCoeff, dif_pos hX, dif_pos hcX]
      have : (⟨c • X, hcX⟩ : Matrices.ComplexMatrix2.traceless) = c • (⟨X, hX⟩ : Matrices.ComplexMatrix2.traceless) := rfl
      rw [this, map_smul]
      rfl
    · have hcX : c • X ∉ Matrices.ComplexMatrix2.traceless := fun h => hX (by
        have := Submodule.smul_mem _ c⁻¹ h
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this)
      simp only [pauliCoeff, dif_neg hX, dif_neg hcX, mul_zero]
  simp only [pauliNorm, hcoef, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
theorem mul_wNorm_le_of_edge_scaling (hB : PlaneWaveCalculus.EdgeCoeffFacts L k)
    (M : QuotHom (colourEdges L k 0) (colourEdges L k 0)) (c : (Fin 4 → ℤ) → ℂ) {r : ℝ}
    (hr : 0 ≤ r)
    (hM : ∀ b μ, ∀ m ∈ freqBox L k,
      edgeFourierCoeff L k (M b) μ m = c m • edgeFourierCoeff L k b μ m)
    (hc : ∀ m ∈ freqBox L k, r ≤ ‖c m‖) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    r * wNorm ((colourEdges L k 0).quotWeight 1) b ≤
      wNorm ((colourEdges L k 0).quotWeight 1) (M b) := by
  have hsq : (r * wNorm ((colourEdges L k 0).quotWeight 1) b) ^ 2 ≤
      wNorm ((colourEdges L k 0).quotWeight 1) (M b) ^ 2 := by
    rw [mul_pow, hB.norm_sq b, hB.norm_sq (M b), Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [hM b μ m hm, pauliNorm_smul, mul_pow]
    have := hc m hm
    gcongr
  exact (pow_le_pow_iff_left₀ (mul_nonneg hr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    two_ne_zero).mp hsq
theorem mul_wNorm_le_of_vertex_scaling (hS : PlaneWaveCalculus.VertexCoeffFacts L k)
    (M : QuotHom (colourVertices L k 0) (colourVertices L k 0)) (c : (Fin 4 → ℤ) → ℂ) {r : ℝ}
    (hr : 0 ≤ r)
    (hM : ∀ l, ∀ m ∈ freqBox L k,
      vertexFourierCoeff L k (M l) m = c m • vertexFourierCoeff L k l m)
    (hc : ∀ m ∈ freqBox L k, r ≤ ‖c m‖) (l : (colourVertices L k 0).UnitQuot → ℂ) :
    r * wNorm ((colourVertices L k 0).quotWeight 1) l ≤
      wNorm ((colourVertices L k 0).quotWeight 1) (M l) := by
  have hsq : (r * wNorm ((colourVertices L k 0).quotWeight 1) l) ^ 2 ≤
      wNorm ((colourVertices L k 0).quotWeight 1) (M l) ^ 2 := by
    rw [mul_pow, hS.norm_sq l, hS.norm_sq (M l), Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [hM l m hm, pauliNorm_smul, mul_pow]
    have := hc m hm
    gcongr
  exact (pow_le_pow_iff_left₀ (mul_nonneg hr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    two_ne_zero).mp hsq
end Coefficients
section Inverses
theorem isUnit_and_norm_inv_le_of_lower_bound (hQ : Quotients.QuotientTransposeNorm) {I : PeriodicData}
    (hI : IsPeriodic I) (M : QuotHom I I) {r : ℝ} (hr : 0 < r)
    (hb : ∀ f, r * wNorm (I.quotWeight 1) f ≤ wNorm (I.quotWeight 1) (M f)) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse M) ≤ ENNReal.ofReal r⁻¹ := by
  classical
  have hfin : Finite I.UnitQuot := hI.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite I.UnitQuot
  have hw := fun c => quotWeight_one_pos hQ hI c
  have hzero : ∀ f : I.UnitQuot → ℂ, wNorm (I.quotWeight 1) f = 0 → f = 0 := by
    intro f hf
    rw [wNorm, tsum_fintype, Real.sqrt_eq_zero
      (Finset.sum_nonneg fun c _ => mul_nonneg (hw c).le (by positivity)),
      Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => mul_nonneg (hw c).le (by positivity))] at hf
    funext c
    have h := hf c (Finset.mem_univ c)
    have h2 : ‖f c‖ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (hw c).ne'
    simpa using h2
  have hnorm0 : wNorm (I.quotWeight 1) (0 : I.UnitQuot → ℂ) = 0 := by
    simp [wNorm]
  have hnn : ∀ f : I.UnitQuot → ℂ, 0 ≤ wNorm (I.quotWeight 1) f := fun _ =>
    Real.sqrt_nonneg _
  have hker : LinearMap.ker M = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun f hf => hzero f ?_
    have h := hb f
    rw [hf, hnorm0] at h
    have h' := hnn f
    nlinarith
  have hU : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mpr hker
  refine ⟨hU, ?_⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have hMf : M (quotHomInverse M f) = f :=
    LinearMap.congr_fun (Ring.mul_inverse_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) hU) f
  have h := hb (quotHomInverse M f)
  rw [hMf] at h
  have h1 : wNorm (I.quotWeight 1) f ≤ 1 := hf.2.2
  rw [inv_eq_one_div, le_div_iff₀ hr]
  linarith
end Inverses
section Jets
open PlaneWaves
variable {L k : ℕ}
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = fun _ => 1 := by
  have hc : ∀ x, ofPauliCoeffs (0 : (remainderIndex L k).Carrier → ℂ) x = 0 := fun x =>
    Finset.sum_eq_zero fun a _ => zero_smul ℂ _
  have hA : (edgePauliCoordinates L k 0).ofCoeffs (0 : (remainderIndex L k).Carrier → ℂ) = 0 := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [edgePauliCoordinates, extendOddly, hb, hc]
    · simp [edgePauliCoordinates, extendOddly, hb, hc]
  have hU : ∀ B : Edge L k 0 → Matrices.ComplexMatrix2, (∀ b, B b = 0) → expForm B = fun _ => 1 := by
    intro B hB
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [expForm, expTwist, hb, hB]
    · simp [expForm, expTwist, hb, hB]
  exact hU _ fun b => congrFun hA b
theorem edgeOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (edgeOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (PlaneWaveCalculus.freeOps L k).K := by
  simp only [edgeOperatorJet, jetAlongResponse, jetAlong, coeffZero,
    gaugeFieldOfForm_zero, PlaneWaveCalculus.freeOps]
theorem vertexOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (PlaneWaveCalculus.freeOps L k).Delta := by
  simp only [vertexOperatorJet, jetAlongResponse, jetAlong, coeffZero,
    gaugeFieldOfForm_zero, PlaneWaveCalculus.freeOps]
theorem addScalarJet_f00 {I : PeriodicData} (T : JetQuad I I) (z : ℝ) (κ : Fin 4 → ℂ) :
    (addScalarJet T z).f00 κ = T.f00 κ + (z : ℂ) • LinearMap.id := rfl
theorem div_three_le_norm_of_re {w : ℂ} {z : ℝ} (h : 1 / 3 * z ≤ w.re) : z / 3 ≤ ‖w‖ := by
  have := Complex.re_le_norm w
  linarith
theorem shiftInvertibleBounded_of_lower_bound {I : PeriodicData} {z : ℝ} {p : Fin 4 → ℂ} {T : JetQuad I I}
    (hz : 0 < z) (hQ : Quotients.QuotientTransposeNorm) (hI : IsPeriodic I)
    (hjet : IsJet (massWidth z) p (addScalarJet T z))
    (hb : ∀ κ ∈ imStrip (2 * massWidth z), ∀ f, z / 3 * wNorm (I.quotWeight 1) f ≤
      wNorm (I.quotWeight 1) ((addScalarJet T z).f00 κ f)) :
    ShiftInvertibleBounded z p T := by
  have hr : 0 < z / 3 := by positivity
  have hU : ∀ κ ∈ imStrip (2 * massWidth z),
      IsUnit ((addScalarJet T z).f00 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse ((addScalarJet T z).f00 κ)) ≤ ENNReal.ofReal (3 / z) := by
    intro κ hκ
    have h := isUnit_and_norm_inv_le_of_lower_bound hQ hI ((addScalarJet T z).f00 κ) hr (hb κ hκ)
    rwa [inv_div] at h
  exact ⟨⟨hjet, fun κ hκ => (hU κ hκ).1,
    lt_of_le_of_lt (iSup₂_le fun κ hκ => (hU κ hκ).2) ENNReal.ofReal_lt_top⟩,
    fun κ hκ => (hU κ hκ).2⟩
end Jets
theorem massJetsClaim_holds (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hPW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hL : JetDomains.OpFunJetTheory)
    (hC : JetCalculus.Claim) (hA : QuadAlgebra.Claim)
    (hE : JetArgumentsAndEqualJets)
    (hN : JetNormsAffine.Claim)
    (hQ : Quotients.QuotientTransposeNorm) (hH : HomNorm.Claim) :
    MassJetsClaim := by
  intro L hLb k hk
  have hW := stripHalfWidth_pos_and_le hNum
  obtain ⟨-, hSites, hBonds, -, hForm, hAct, -⟩ := hPW L hLb k hk
  have hOps := (hOp.1 L hLb k hk).1
  obtain ⟨hSi, hBo, -⟩ := hOps.periodic
  have hFin := finite_vertexClass hSi
  have hden : ∀ z : ℝ, 0 < z → DenominatorReBound L k z := fun z hz =>
    denominatorReBound_of_formula hLb k hForm.symbolSquare_eq hW hz
  have hstrip : ∀ {δ : ℝ} {p : Fin 4 → ℂ}, p ∈ momentumPolydisc δ → p ∈ imStrip δ := fun hp μ =>
    (Complex.abs_im_le_norm _).trans (hp μ)
  have hjetK : ∀ (δ : ℝ), 0 < δ → ∀ p ∈ imStrip δ, ∀ μPlus μMinus : Fin 4,
      IsJet δ p (edgeOperatorJet L k p μPlus μMinus) := fun δ hδ p hp _ _ =>
    (hL.2.1 _ _ _ hBo hBo hBo _ hOps.K_local.1).isJet δ hδ p hp _ _
  have hjetD : ∀ (δ : ℝ), 0 < δ → ∀ p ∈ imStrip δ, ∀ μPlus μMinus : Fin 4,
      IsJet δ p (vertexOperatorJet L k p μPlus μMinus) := fun δ hδ p hp _ _ =>
    (hL.2.1 _ _ _ hBo hSi hSi _ hOps.Delta_local.1).isJet δ hδ p hp _ _
  have hinvK : ∀ z : ℝ, 0 < z → ∀ p ∈ momentumPolydisc (massWidth z), ∀ μPlus μMinus : Fin 4,
      ShiftInvertibleBounded z p (edgeOperatorJet L k p μPlus μMinus) := by
    intro z hz p hp μPlus μMinus
    have hδ := massWidth_pos hW.1 hz
    have hF := hL.2.2 _ _ _ hBo hBo hBo _ p hδ (hstrip hp)
    refine shiftInvertibleBounded_of_lower_bound hz hQ hBo
      (hF.add_isJet _ _ (hjetK _ hδ p (hstrip hp) μPlus μMinus)
        (hF.smul_isJet _ _ hF.one_isJet)) ?_
    intro κ hκ f
    refine mul_wNorm_le_of_edge_scaling hBonds _
      (fun m => PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) + (z : ℂ))
      (by positivity) ?_ (fun m hm => div_three_le_norm_of_re (hden z hz κ hκ m hm)) f
    intro b μ m hm
    rw [addScalarJet_f00, edgeOperatorJet_f00, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, edgeFourierCoeff_add hFin, edgeFourierCoeff_smul hFin,
      hAct.K κ b μ m hm, add_smul]
  have hinvD : ∀ z : ℝ, 0 < z → ∀ p ∈ momentumPolydisc (massWidth z), ∀ μPlus μMinus : Fin 4,
      ShiftInvertibleBounded z p (vertexOperatorJet L k p μPlus μMinus) := by
    intro z hz p hp μPlus μMinus
    have hδ := massWidth_pos hW.1 hz
    have hF := hL.2.2 _ _ _ hSi hSi hSi _ p hδ (hstrip hp)
    refine shiftInvertibleBounded_of_lower_bound hz hQ hSi
      (hF.add_isJet _ _ (hjetD _ hδ p (hstrip hp) μPlus μMinus)
        (hF.smul_isJet _ _ hF.one_isJet)) ?_
    intro κ hκ f
    refine mul_wNorm_le_of_vertex_scaling hSites _
      (fun m => PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) + (z : ℂ))
      (by positivity) ?_ (fun m hm => div_three_le_norm_of_re (hden z hz κ hκ m hm)) f
    intro l m hm
    rw [addScalarJet_f00, vertexOperatorJet_f00, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, vertexFourierCoeff_add hFin, vertexFourierCoeff_smul hFin,
      hAct.Delta κ l m hm, add_smul]
  have hwidth : ∀ z : ℝ, 25 * stripHalfWidth ^ 2 ≤ z → massWidth z = stripHalfWidth := fun z hz =>
    massWidth_eq_of_le hW.1 hz
  have hapos : 0 < 25 * stripHalfWidth ^ 2 := by have := hW.1; positivity
  refine ⟨fun z hz => ⟨hden z hz, fun p hp μPlus μMinus =>
      ⟨hinvD z hz p hp μPlus μMinus, hinvK z hz p hp μPlus μMinus⟩⟩,
    fun z _ hz => hwidth z hz, fun z hz => hwidth z ?_, ?_⟩
  · have := hW.1
    have := hW.2
    nlinarith
  · intro p hp μPlus μMinus
    have hps := hstrip hp
    have hat : ∀ z, 25 * stripHalfWidth ^ 2 < z → 0 < z ∧ p ∈ momentumPolydisc (massWidth z) ∧
        massWidth z = stripHalfWidth := fun z hz =>
      ⟨hapos.trans hz, by rw [hwidth z hz.le]; exact hp, hwidth z hz.le⟩
    refine ⟨?_, ?_⟩
    · refine logNumber_addScalarJet_deriv hL hC hA hE hN hQ hH hW.1 hps hBo _
        (hjetK _ hW.1 p hps μPlus μMinus) _ hapos (fun z hz => ?_) (fun z hz κ hκ => ?_)
      · obtain ⟨h0, h1, h2⟩ := hat z hz
        have h := (hinvK z h0 p h1 μPlus μMinus).1
        rwa [h2] at h
      · obtain ⟨h0, h1, h2⟩ := hat z hz
        have h := (hinvK z h0 p h1 μPlus μMinus).2
        rw [h2] at h
        exact h κ hκ
    · refine logNumber_addScalarJet_deriv hL hC hA hE hN hQ hH hW.1 hps hSi _
        (hjetD _ hW.1 p hps μPlus μMinus) _ hapos (fun z hz => ?_) (fun z hz κ hκ => ?_)
      · obtain ⟨h0, h1, h2⟩ := hat z hz
        have h := (hinvD z h0 p h1 μPlus μMinus).1
        rwa [h2] at h
      · obtain ⟨h0, h1, h2⟩ := hat z hz
        have h := (hinvD z h0 p h1 μPlus μMinus).2
        rw [h2] at h
        exact h κ hκ
end YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets
end
