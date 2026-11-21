import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import YangMills.Construction.PeriodicOperators.NormsOfJetsAndAffineFamiliesOfInvertibleJets
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetNormsAffine
open JetQuad
variable {I : PeriodicData} {ε : ℝ} {z : Fin 4 → ℂ}
private theorem eqAsJet_refl (T : JetQuad I I) : EqAsJet ε z T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem eqAsJet_trans {T S R : JetQuad I I} (e : EqAsJet ε z T S) (f : EqAsJet ε z S R) :
    EqAsJet ε z T R :=
  ⟨e.1.trans f.1, e.2.1.trans f.2.1, e.2.2.1.trans f.2.2.1, e.2.2.2.trans f.2.2.2⟩
private theorem eqAsJet_add {T T' S S' : JetQuad I I} (e : EqAsJet ε z T T') (f : EqAsJet ε z S S') :
    EqAsJet ε z (add T S) (add T' S') := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · simp only [add, Pi.add_apply, e.1 hw, f.1 hw]
  · simp only [add, Pi.add_apply, e.2.1 hw, f.2.1 hw]
  · simp only [add, Pi.add_apply, e.2.2.1 hw, f.2.2.1 hw]
  · simp only [add, Pi.add_apply, e.2.2.2 hw, f.2.2.2 hw]
private theorem eqAsJet_smul (c : ℂ) {T T' : JetQuad I I} (e : EqAsJet ε z T T') :
    EqAsJet ε z (smul c T) (smul c T') := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · simp only [smul, Pi.smul_apply, e.1 hw]
  · simp only [smul, Pi.smul_apply, e.2.1 hw]
  · simp only [smul, Pi.smul_apply, e.2.2.1 hw]
  · simp only [smul, Pi.smul_apply, e.2.2.2 hw]
private theorem affinePath_sub (A B : JetQuad I I) (a b : ℝ) :
    add (affinePath A B a) (smul (-1) (affinePath A B b)) = smul ((a : ℂ) - b) B := by
  apply JetQuad.ext <;> funext w <;>
    simp only [affinePath, add, smul, Pi.add_apply, Pi.smul_apply] <;> module
private theorem smul_smul_add_neg (B : JetQuad I I) {c d : ℂ} (h : c * d = 1) :
    add (smul c (smul d B)) (smul (-1) B) = zeroJet I I := by
  apply JetQuad.ext <;> funext w <;>
    simp only [zeroJet, add, smul, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_smul, h, one_smul] <;>
    module
private theorem add_smul_neg_one_self (B : JetQuad I I) : add B (smul (-1) B) = zeroJet I I := by
  apply JetQuad.ext <;> funext w <;>
    simp only [zeroJet, add, smul, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] <;> module
private theorem jetNorm_zeroJet (h0 : quotHomNorm (0 : QuotHom I I) = 0) :
    jetNorm ε z (zeroJet I I) = 0 := by
  simp [jetNorm, zeroJet, h0]
private theorem norm_traceNumber_le {Ct : ℝ} (hCt : 0 ≤ Ct)
    (htr : ∀ M : QuotHom I I, ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) M‖ ≤ Ct * (quotHomNorm M).toReal) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : JetQuad I I, jetNorm ε z T < ∞ →
      ‖traceNumber T‖ ≤ K * (jetNorm ε z T).toReal := by
  set s : Set (Fin 4 → ℝ) := Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) with hs
  have hfin : volume s < ∞ := isCompact_Icc.measure_lt_top
  refine ⟨‖(((((2 * Real.pi) ^ 4)⁻¹ : ℝ)) : ℂ)‖ * (Ct * volume.real s), by positivity,
    fun T hT => ?_⟩
  have hb : ∀ θ ∈ s, ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec θ))‖ ≤
      Ct * (jetNorm ε z T).toReal := by
    intro θ _
    have hreal : toComplexVec θ ∈ realDualPoints := fun μ => by simp [toComplexVec]
    have h1 : quotHomNorm (T.f11 (toComplexVec θ)) ≤ jetNorm ε z T :=
      le_trans (le_iSup₂ (f := fun w (_ : w ∈ realDualPoints) => quotHomNorm (T.f11 w))
        (toComplexVec θ) hreal) le_add_self
    exact (htr _).trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hT.ne h1) hCt)
  have hi := norm_setIntegral_le_of_norm_le_const hfin hb
  unfold traceNumber torusAverage
  rw [norm_mul]
  calc _ ≤ ‖(((((2 * Real.pi) ^ 4)⁻¹ : ℝ)) : ℂ)‖ * (Ct * (jetNorm ε z T).toReal * volume.real s) :=
        mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by ring
private theorem affinePath_props
    (h₁ : JetCalculus.Claim)
    (h₂ : JetDomains.OpFunJetTheory)
    (h₃ : JetArgumentsAndEqualJets)
    (h₄ : QuadAlgebra.Claim)
    (h₅ : QuotMatrixNorms.Claim)
    (hε : 0 < ε) (hz : z ∈ imStrip ε) (hI : IsPeriodic I)
    (hfin : ∀ T : JetQuad I I, IsJet ε z T → jetNorm ε z T < ∞)
    (A B : JetQuad I I) (hA : IsJet ε z A) (hB : IsJet ε z B)
    (J : Set ℝ) (hJc : IsCompact J) (hJo : J.OrdConnected) (hJn : J.Nontrivial)
    (hinv : ∀ t ∈ J, IsInvertibleJet ε z (affinePath A B t))
    (hbd : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ J,
      (⨆ w ∈ imStrip (2 * ε), quotHomNorm (quotHomInverse ((affinePath A B t).f00 w))) ≤ C) :
    (⨆ t ∈ J, jetNorm ε z (invJet z (affinePath A B t))) < ∞ ∧
    (∃ L : ℝ≥0, ∀ t ∈ J, ∀ t' ∈ J,
      jetNorm ε z
          (add (invJet z (affinePath A B t'))
            (smul (-1) (invJet z (affinePath A B t)))) ≤
        L * ENNReal.ofReal |t' - t|) ∧
    (∀ C : JetQuad I I, IsJet ε z C →
      ContinuousOn (fun t => traceNumber (mul z C (invJet z (affinePath A B t)))) J) ∧
    ContinuousOn (fun t => traceNumber (mul z (invJet z (affinePath A B t)) B)) J ∧
    (∀ t ∈ J, HasDerivWithinAt (fun s => logNumber z (affinePath A B s))
      (traceNumber (mul z (invJet z (affinePath A B t)) B)) J t) ∧
    ∀ t₀ ∈ J, ∀ t₁ ∈ J,
      logNumber z (affinePath A B t₁) - logNumber z (affinePath A B t₀) =
        ∫ t in t₀..t₁, traceNumber (mul z (invJet z (affinePath A B t)) B) := by
  have F := h₂.2.2 I I I hI hI hI ε z hε hz
  obtain ⟨hP, -, -, -, hInv, hTr, -, -, hDer⟩ := h₁ ε z hε hz
  obtain ⟨mul_add_l, mul_add_r, smul_l, smul_r, unit⟩ := h₄.1 z I I I
  obtain ⟨n_add, n_smul, -, t_add, t_smul⟩ := h₄.2 ε z hε hz I I hI hI
  have cong := h₃.2.1 ε z I I hI hI
  obtain ⟨hnorm, -, htrace⟩ := h₅ I I I hI hI hI
  have n0 : quotHomNorm (0 : QuotHom I I) = 0 := hnorm.2.2.2.1
  obtain ⟨Ct, hCt, htr⟩ := htrace.2
  obtain ⟨K, hK, hKt⟩ := norm_traceNumber_le (ε := ε) (z := z) hCt htr
  have assoc := fun (T S R : JetQuad I I) (hT : IsJet ε z T) (hS : IsJet ε z S)
    (hR : IsJet ε z R) => (hP I I I I hI hI hI hI T S R hT hS hR).1
  have n_mul := fun (T S : JetQuad I I) (hT : IsJet ε z T) (hS : IsJet ε z S) =>
    (hP I I I I hI hI hI hI T S (one I) hT hS F.one_isJet).2
  have mulj := F.mul_isJet
  obtain ⟨C, hCfin, hC⟩ := hbd
  obtain ⟨r, hr⟩ := hJc.isBounded.exists_norm_le
  set m : ℝ≥0∞ := jetNorm ε z A + ENNReal.ofReal r * jetNorm ε z B with hm
  have hmfin : m < ∞ :=
    ENNReal.add_lt_top.2 ⟨hfin A hA, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin B hB)⟩
  have hTm : ∀ t ∈ J, jetNorm ε z (affinePath A B t) ≤ m := by
    intro t ht
    refine (n_add A _ hA (F.smul_isJet _ B hB)).trans (add_le_add_right ?_ _)
    refine (n_smul _ B hB).trans (mul_le_mul_left ?_ _)
    apply ENNReal.ofReal_le_ofReal
    simpa using hr t ht
  set m' : ℝ≥0∞ := C * (1 + C * m) ^ 2 with hm'
  have hm'fin : m' < ∞ :=
    ENNReal.mul_lt_top hCfin
      (ENNReal.pow_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top hCfin hmfin⟩))
  have hRj : ∀ t ∈ J, IsJet ε z (invJet z (affinePath A B t)) :=
    fun t ht => (hInv I hI _ (hinv t ht)).1
  have hRm : ∀ t ∈ J, jetNorm ε z (invJet z (affinePath A B t)) ≤ m' := by
    intro t ht
    obtain ⟨-, -, -, hle, heq⟩ := hInv I hI _ (hinv t ht)
    have hc : jetNorm ε z (zeroPartInv (affinePath A B t)) ≤ C := heq.le.trans (hC t ht)
    refine hle.trans ?_
    have := hTm t ht
    rw [hm']
    gcongr
  have hdiff : ∀ t ∈ J, ∀ t' ∈ J,
      EqAsJet ε z (smul ((t : ℂ) - t') (mul z (mul z (invJet z (affinePath A B t')) B)
          (invJet z (affinePath A B t))))
        (add (invJet z (affinePath A B t')) (smul (-1) (invJet z (affinePath A B t)))) := by
    intro t ht t' ht'
    obtain ⟨hYj, -, hSY, -⟩ := hInv I hI _ (hinv t ht)
    obtain ⟨hXj, hXS', -, -⟩ := hInv I hI _ (hinv t' ht')
    have hSj := (hinv t ht).isJet
    have hS'j := (hinv t' ht').isJet
    set X := invJet z (affinePath A B t')
    set Y := invJet z (affinePath A B t)
    set S := affinePath A B t
    set S' := affinePath A B t'
    have e1 : EqAsJet ε z (mul z X (mul z S Y)) X := by
      have := (cong X X hXj hXj (eqAsJet_refl X)).2.2.2.2 I hI (mul z S Y) (one I)
        (mulj S Y hSj hYj) F.one_isJet hSY
      rwa [(unit X).2] at this
    have e2 : EqAsJet ε z (mul z (mul z X S') Y) Y := by
      have := (cong (mul z X S') (one I) (mulj X S' hXj hS'j) F.one_isJet hXS').2.2.2.2 I hI Y Y
        hYj hYj (eqAsJet_refl Y)
      rwa [(unit Y).1] at this
    have e3 := eqAsJet_add (eqAsJet_trans (assoc X S Y hXj hSj hYj) e1) (eqAsJet_smul (-1) e2)
    have e4 : add (mul z (mul z X S) Y) (smul (-1) (mul z (mul z X S') Y)) =
        smul ((t : ℂ) - t') (mul z (mul z X B) Y) := by
      rw [← smul_l, ← mul_add_l, ← smul_r, ← mul_add_r, affinePath_sub, smul_r, smul_l]
    rwa [e4] at e3
  set b : ℝ≥0∞ := m' * jetNorm ε z B * m' with hb
  have hbfin : b < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hm'fin (hfin B hB)) hm'fin
  have hDj : ∀ t ∈ J, ∀ t' ∈ J, IsJet ε z
      (add (invJet z (affinePath A B t')) (smul (-1) (invJet z (affinePath A B t)))) :=
    fun t ht t' ht' => F.add_isJet _ _ (hRj t' ht') (F.smul_isJet _ _ (hRj t ht))
  have hLip : ∀ t ∈ J, ∀ t' ∈ J,
      jetNorm ε z (add (invJet z (affinePath A B t'))
        (smul (-1) (invJet z (affinePath A B t)))) ≤ b * ENNReal.ofReal |t' - t| := by
    intro t ht t' ht'
    have hWj := mulj _ _ (mulj _ _ (hRj t' ht') hB) (hRj t ht)
    have hsj := F.smul_isJet ((t : ℂ) - t') _ hWj
    rw [← (cong _ _ hsj (hDj t ht t' ht') (hdiff t ht t' ht')).1]
    refine (n_smul _ _ hWj).trans ?_
    have hnorm' : ‖(t : ℂ) - t'‖ = |t' - t| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [hnorm', mul_comm]
    refine mul_le_mul_left ?_ _
    calc _ ≤ jetNorm ε z (mul z (invJet z (affinePath A B t')) B) *
            jetNorm ε z (invJet z (affinePath A B t)) := n_mul _ _ (mulj _ _ (hRj t' ht') hB) (hRj t ht)
      _ ≤ (jetNorm ε z (invJet z (affinePath A B t')) * jetNorm ε z B) *
            jetNorm ε z (invJet z (affinePath A B t)) := by
          gcongr
          exact n_mul _ _ (hRj t' ht') hB
      _ ≤ b := by
          have h1 := hRm t ht
          have h2 := hRm t' ht'
          rw [hb]
          gcongr
  have hcont : ∀ D : JetQuad I I, IsJet ε z D →
      ContinuousOn (fun t => traceNumber (mul z D (invJet z (affinePath A B t)))) J := by
    intro D hD
    have hDfin := hfin D hD
    have hnn : 0 ≤ K * ((jetNorm ε z D).toReal * b.toReal) := by positivity
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (K * ((jetNorm ε z D).toReal * b.toReal)))
      ?_).continuousOn
    intro t' ht' t ht
    rw [Real.coe_toNNReal _ hnn, dist_eq_norm, Real.dist_eq]
    have hsplit : mul z D (add (invJet z (affinePath A B t'))
        (smul (-1) (invJet z (affinePath A B t)))) =
        add (mul z D (invJet z (affinePath A B t')))
          (smul (-1) (mul z D (invJet z (affinePath A B t)))) := by
      rw [mul_add_r, smul_r]
    have hmj := mulj _ _ hD (hDj t ht t' ht')
    have htn : traceNumber (mul z D (invJet z (affinePath A B t'))) -
        traceNumber (mul z D (invJet z (affinePath A B t))) =
        traceNumber (mul z D (add (invJet z (affinePath A B t'))
          (smul (-1) (invJet z (affinePath A B t))))) := by
      rw [hsplit, t_add _ _ (mulj _ _ hD (hRj t' ht'))
        (F.smul_isJet _ _ (mulj _ _ hD (hRj t ht))),
        t_smul _ _ (mulj _ _ hD (hRj t ht))]
      ring
    rw [htn]
    refine (hKt _ (hfin _ hmj)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hle := (n_mul _ _ hD (hDj t ht t' ht')).trans
      (mul_le_mul_right (hLip t ht t' ht') (jetNorm ε z D))
    have hrhs : jetNorm ε z D * (b * ENNReal.ofReal |t' - t|) < ∞ :=
      ENNReal.mul_lt_top hDfin (ENNReal.mul_lt_top hbfin ENNReal.ofReal_lt_top)
    refine (ENNReal.toReal_mono hrhs.ne hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    ring
  have hcontB : ContinuousOn (fun t => traceNumber (mul z (invJet z (affinePath A B t)) B)) J :=
    (hcont B hB).congr fun t ht => ((hTr I I hI hI).1 _ _ (hRj t ht) hB)
  have hfam : HasC1FamilyDeriv ε z J (affinePath A B) fun _ => B := by
    intro t _
    constructor
    · have hev : (fun _ : ℝ => (0 : ℝ≥0∞)) =ᶠ[𝓝[{h : ℝ | h ≠ 0 ∧ t + h ∈ J}] 0]
          fun h => jetNorm ε z (add (smul ((h⁻¹ : ℝ) : ℂ)
            (add (affinePath A B (t + h)) (smul (-1) (affinePath A B t)))) (smul (-1) B)) := by
        filter_upwards [self_mem_nhdsWithin] with h hh
        have hne : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.1
        have hone : ((h⁻¹ : ℝ) : ℂ) * (((t + h : ℝ) : ℂ) - t) = 1 := by
          push_cast
          field_simp
          ring
        rw [affinePath_sub, smul_smul_add_neg B hone, jetNorm_zeroJet n0]
      exact tendsto_const_nhds.congr' hev
    · have hfun : (fun h : ℝ => jetNorm ε z (add B (smul (-1) B))) = fun _ => 0 := by
        funext h
        rw [add_smul_neg_one_self, jetNorm_zeroJet n0]
      simp only [hfun]
      exact tendsto_const_nhds
  have hd : ∀ t ∈ J, HasDerivWithinAt (fun s => logNumber z (affinePath A B s))
      (traceNumber (mul z (invJet z (affinePath A B t)) B)) J t :=
    fun t ht => hDer I hI J hJo hJn _ (fun _ => B) hinv (fun _ _ => hB) hfam ⟨C, hCfin, hC⟩ t ht
  refine ⟨lt_of_le_of_lt (iSup₂_le hRm) hm'fin,
    ⟨b.toNNReal, fun t ht t' ht' => ?_⟩, hcont, hcontB, hd, fun t₀ h₀ t₁ h₁' => ?_⟩
  · rw [ENNReal.coe_toNNReal hbfin.ne]
    exact hLip t ht t' ht'
  · have hsub : uIcc t₀ t₁ ⊆ J := hJo.uIcc_subset h₀ h₁'
    refine (intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (fun x hx => (hd x (hsub hx)).continuousWithinAt.mono hsub)
      (fun x hx => ?_) (hcontB.mono hsub).intervalIntegrable).symm
    have hnh : J ∈ 𝓝 x := mem_of_superset (Icc_mem_nhds hx.1 hx.2) hsub
    exact ((hd x (hsub (Ioo_subset_Icc_self hx))).hasDerivAt hnh).hasDerivWithinAt
theorem claim_holds
    (h₁ : JetCalculus.Claim)
    (h₂ : JetDomains.OpFunJetTheory)
    (h₃ : JetArgumentsAndEqualJets)
    (h₄ : QuadAlgebra.Claim)
    (h₅ : QuotMatrixNorms.Claim) :
    Claim := by
  have finite : ∀ (ε : ℝ) (z : Fin 4 → ℂ), 0 < ε → z ∈ imStrip ε → ∀ I I' : PeriodicData,
      IsPeriodic I → IsPeriodic I' → ∀ T : JetQuad I I', IsJet ε z T →
      jetNorm ε z T < ∞ := by
    intro ε z hε hz I I' hI hI' T hT
    obtain ⟨a, b, c, d⟩ := (h₂.2.2 I I' I' hI hI' hI' ε z hε hz).sups_finite T hT
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨a, b⟩, c⟩, d⟩
  intro ε z hε hz I I' hI hI'
  refine ⟨finite ε z hε hz I I' hI hI', ?_⟩
  intro A B hA hB J hJc hJo hJn hinv hbd
  exact affinePath_props h₁ h₂ h₃ h₄ h₅ hε hz hI (finite ε z hε hz I I hI hI) A B hA hB J hJc hJo hJn hinv hbd
end YangMills.Construction.PeriodicOperators.JetNormsAffine
end
