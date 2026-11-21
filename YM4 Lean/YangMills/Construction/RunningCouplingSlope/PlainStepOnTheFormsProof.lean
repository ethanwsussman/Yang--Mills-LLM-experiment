import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.OrbitUnderThePlainAverage
import YangMills.Construction.RunningCouplingSlope.OtherConstraintAtNoNoiseProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfARealField
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialAtOneOnComplexFormsProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesHasRealAnalyticEntriesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanDerivOnForms
open Matrices Tower
private theorem matExp_neg_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_matExp_I_smul (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof.hasDerivAt_matExp_I_smul <;> assumption
private theorem hasDerivAt_ofReal_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : ℂ → F} {Y : F} (h : HasDerivAt G Y 0) : HasDerivAt (fun t : ℝ => G (t : ℂ)) Y 0 := by apply _root_.YangMills.SharedProofs.p1580 <;> assumption
variable {L n k j : ℕ}
private def tangentAt (V B : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if b.IsPositivelyOriented then (Complex.I • B b) * V b
    else V b * (-(Complex.I • B b.opposite))
private theorem tangentAt_add_smul (V B B' : Edge L n k j → ComplexMatrix2) (z : ℂ) :
    tangentAt V (z • B + B') = z • tangentAt V B + tangentAt V B' := by
  classical
  funext b
  simp only [tangentAt, Pi.add_apply, Pi.smul_apply]
  split_ifs
  · simp only [smul_add, add_mul, smul_comm Complex.I z, Matrix.smul_mul]
  · simp only [smul_add, neg_add, Matrix.mul_add, smul_comm Complex.I z, Matrix.mul_smul,
      smul_neg, Matrix.mul_neg]
abbrev _root_.YangMills.DeltaSharedProofs.p502068 := @tangentAt_add_smul
theorem hasDerivAt_expTwist_apply (V B : Edge L n k j → ComplexMatrix2)
    (hinv : ∀ b, (V b.opposite)⁻¹ = V b)
    (hneg : ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
    (b : Edge L n k j) :
    HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) (tangentAt V B b) 0 := by
  classical
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) =
        fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e]
    refine HasDerivAt.congr_deriv ((hasDerivAt_matExp_I_smul _).mul_const (V b)) ?_
    simp only [tangentAt, if_pos hb]
  · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) =
        fun t : ℂ => V b * ComplexMatrix2.matExp (Complex.I • (t • (-B b.opposite))) := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, Matrix.mul_inv_rev, hinv,
        matExp_neg_inv]
      congr 2
      simp
    rw [e]
    refine HasDerivAt.congr_deriv ((hasDerivAt_matExp_I_smul _).const_mul (V b)) ?_
    simp only [tangentAt, if_neg hb, smul_neg]
private theorem extendOddly_opposite
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.extendOddly_opposite <;> assumption
private theorem expTwist_mem_fieldsIn_complex
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j) (t : ℂ) :
    PeriodicLattice.expTwist (t • B) V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  classical
  have hdetV : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Matrix.det (ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b) = 1 := by
    intro b hb
    have htr : ComplexMatrix2.fullTrace (Complex.I • (t • B) b) = 0 := by
      have h0 : ComplexMatrix2.fullTrace (B b) = 0 := hB.1 b hb
      simp only [ComplexMatrix2.fullTrace, Pi.smul_apply, Matrix.trace_smul] at h0 ⊢
      simp [h0]
    rw [Matrix.det_mul, SpinHarmonics.det_matExp_of_trace_eq_zero htr, hdetV, one_mul]
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · change Matrix.det (PeriodicLattice.expTwist (t • B) V b) = 1
    by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · have hp : b.opposite.IsPositivelyOriented := by
        rcases hX b with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hb
        · exact h
      simp only [PeriodicLattice.expTwist, if_neg hb]
      rw [Matrix.det_nonsing_inv, hpos _ hp]
      simp
  · rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · simp only [PeriodicLattice.expTwist, if_neg hn, if_pos hp,
        show b.opposite.opposite = b from rfl]
    · simp only [PeriodicLattice.expTwist, if_pos hp, if_neg hn]
      refine (Matrix.nonsing_inv_nonsing_inv _ ?_).symm
      rw [hpos _ hp]
      exact isUnit_one
private theorem matExp_mem_compactGaugeGroup {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem inv_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem expTwist_mem_fieldSpace
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {V B : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) (t : ℝ) :
    PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ fieldSpace L n k j := by
  classical
  have hVs : ∀ b, V b ∈ ComplexMatrix2.specialUnitary := fun b => hV.1 b (Set.mem_univ b)
  have hdet : ∀ g : ComplexMatrix2, g ∈ ComplexMatrix2.specialUnitary → Matrix.det g = 1 :=
    fun g hg => (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B) b) * V b ∈
        ComplexMatrix2.specialUnitary := by
    intro b hb
    refine ComplexMatrix2.specialUnitary.mul_mem ?_ (hVs b)
    have : ((t : ℂ) • B) b ∈ ComplexMatrix2.hermitianTraceless := by
      have := ComplexMatrix2.hermitianTraceless.smul_mem t (hB.1 b hb)
      simpa [Complex.coe_smul] using this
    exact matExp_mem_compactGaugeGroup this
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · have hp : b.opposite.IsPositivelyOriented := by
        rcases hX b with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hb
        · exact h
      simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_specialUnitary (hpos _ hp)
  · rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · simp only [PeriodicLattice.expTwist, if_neg hn, if_pos hp,
        show b.opposite.opposite = b from rfl]
    · simp only [PeriodicLattice.expTwist, if_pos hp, if_neg hn]
      refine (Matrix.nonsing_inv_nonsing_inv _ ?_).symm
      rw [hdet _ (hpos _ hp)]
      exact isUnit_one
private theorem expTwist_zero_smul {V : Edge L n k j → ComplexMatrix2}
    (hinv : ∀ b, (V b.opposite)⁻¹ = V b) (B : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [PeriodicLattice.expTwist, if_pos hb, NormedSpace.exp_zero, ComplexMatrix2.matExp]
  · simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, zero_smul, Pi.zero_apply,
      smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
    exact hinv b
abbrev _root_.YangMills.SharedProofs.p63404 := @expTwist_zero_smul
private theorem eq_of_eq_on_positive {i : ℕ}
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f g : Edge L n k i → ComplexMatrix2} (hf : ∀ b, f b.opposite = -f b)
    (hg : ∀ b, g b.opposite = -g b)
    (h : ∀ c, c.IsPositivelyOriented → f c = g c) : f = g := by apply _root_.YangMills.SharedProofs.p26709 <;> assumption
section AtAnEdge
variable [Fintype (Edge L n k j)]
private theorem exists_linear_deriv_at_edge
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (V : Edge L n k j → ComplexMatrix2) (hinv : ∀ b, (V b.opposite)⁻¹ = V b)
    (hneg : ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented)
    (hΦ : AnalyticAt ℂ (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' c) V)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
      ∀ B : Edge L n k j → ComplexMatrix2,
      HasDerivAt (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c *
        (normalizedMean V c)⁻¹) (D B) 0 ∧
      normalizedMean (PeriodicLattice.expTwist ((0 : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹ = 1 ∧
      holLeftDifferential normalizedMean V B c = Complex.I⁻¹ • D B ∧
      leftDifferential normalizedMean V B c = Complex.I⁻¹ • D B := by
  classical
  set u := normalizedMean V c with hudef
  have huu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [hu]; exact isUnit_one)
  have hF := hΦ.differentiableAt.hasFDerivAt
  set Df := fderiv ℂ (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' c) V with hDf
  let vel : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] (Edge L n k j → ComplexMatrix2) :=
    { toFun := tangentAt V
      map_add' := fun B B' => by simpa using tangentAt_add_smul V B B' 1
      map_smul' := fun z B => by
        have h0 : tangentAt V (0 : Edge L n k j → ComplexMatrix2) = 0 := by
          funext b
          simp only [tangentAt, Pi.zero_apply, smul_zero, neg_zero, Matrix.zero_mul,
            Matrix.mul_zero, ite_self]
        simpa [h0] using tangentAt_add_smul V B 0 z }
  refine ⟨LinearMap.mulRight ℂ u⁻¹ ∘ₗ Df.toLinearMap ∘ₗ vel, fun B => ?_⟩
  have hγ0 : PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := expTwist_zero_smul hinv B
  have hγ : HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) V) (tangentAt V B) 0 :=
    hasDerivAt_pi.2 fun b => hasDerivAt_expTwist_apply V B hinv hneg b
  have hcomp : HasDerivAt (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c)
      (Df (tangentAt V B)) 0 := by
    have hF' : HasFDerivAt (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' c) Df
        ((fun t : ℂ => PeriodicLattice.expTwist (t • B) V) 0) := by
      simp only [hγ0]
      exact hF
    exact hF'.comp_hasDerivAt (0 : ℂ) hγ
  have hX := hcomp.mul_const u⁻¹
  have hX0 : (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c * u⁻¹) 0 = 1 := by
    simp only [hγ0]
    exact huu
  have hlog := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.2.1
  have hlogR := hasDerivAt_ofReal_comp hlog
  refine ⟨hX, hX0, ?_, ?_⟩
  · have e : holLeftDifferential normalizedMean V B c = Complex.I⁻¹ • deriv (fun t : ℂ =>
        ComplexMatrix2.logSeries
          (normalizedMean (PeriodicLattice.expTwist (t • B) V) c * u⁻¹)) 0 := by
      unfold holLeftDifferential extendOddly
      rw [if_pos hc]
      rfl
    rw [e, hlog.deriv]
    rfl
  · have e : leftDifferential normalizedMean V B c = Complex.I⁻¹ • deriv (fun t : ℝ =>
        ComplexMatrix2.logSeries
          (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c * u⁻¹)) 0 := by
      unfold leftDifferential extendOddly
      rw [if_pos hc]
      rfl
    rw [e, hlogR.deriv]
    rfl
end AtAnEdge
theorem claim_holds (hA : NormalizedMeanAnalytic)
    (hN : NormalizedMeanNearOne) (hR : NormalizedMeanOfCompactField)
    (hO : ContourMeanGaugeOrbit)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hP : SmoothingNearIdentity) :
    Claim := by
  intro L hL n k j hn hj
  classical
  obtain ⟨ρA, hρA, HA⟩ := hA L hL
  obtain ⟨ρN, hρN, HN⟩ := hN L hL
  obtain ⟨ρR, hρR, HR⟩ := hR L hL
  obtain ⟨ρO, hρO, HO⟩ := hO L hL
  have hρL := (hP.1 L hL).2.2.pos
  set ρ := min (min ρA ρN) (min ρR (min ρO (polydiscRadius L))) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρA hρN) (lt_min hρR (lt_min hρO hρL))
  have hρ1 : ρ ≤ ρA := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρN := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ ρR := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ ρO := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ5 : ρ ≤ polydiscRadius L :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hX' : ∀ b : Edge L n k (j + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hneg : ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented := by
    intro b hb
    rcases hX b with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hb
    · exact h
  have hfin : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
  let _ : Fintype (Edge L n k j) := Fintype.ofFinite _
  unfold EventuallyNearIdentity
  have hnear : ∀ᶠ V : Edge L n k j → ComplexMatrix2 in
      𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)),
      ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ := by
    rw [Filter.eventually_all]
    intro b
    have h1 : Tendsto (fun V : Edge L n k j → ComplexMatrix2 => V b)
        (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2)) (𝓝 1) :=
      ((continuous_apply b).tendsto _).mono_left nhdsWithin_le_nhds
    have := Metric.tendsto_nhds.1 h1 ρ hρ0
    filter_upwards [this] with V hV
    simpa [dist_eq_norm] using hV
  filter_upwards [hnear, self_mem_nhdsWithin] with V hVρ hVr
  have hVs : ∀ b, V b ∈ ComplexMatrix2.specialUnitary := fun b => hVr.1 b (Set.mem_univ b)
  have hVc : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.1 (hVs b)).2, hVr.2⟩
  have hinv : ∀ b, (V b.opposite)⁻¹ = V b := by
    intro b
    rw [hVr.2 b (Set.mem_univ b)]
    exact Matrix.nonsing_inv_nonsing_inv _ (by
      rw [(Matrix.mem_specialUnitaryGroup_iff.1 (hVs b)).2]
      exact isUnit_one)
  have lt : ∀ {ρ' : ℝ}, ρ ≤ ρ' → ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ' :=
    fun h b => (hVρ b).trans_le h
  have hRV := fun c hc => HR n k j hn hj V hVr (lt hρ3) c hc
  have hdetu : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Matrix.det (normalizedMean V c) = 1 := fun c hc =>
    (Matrix.mem_specialUnitaryGroup_iff.1 (hRV c hc).2.2).2
  have key := fun (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) =>
    exists_linear_deriv_at_edge hd V hinv hneg c hc
      (HA n k j hn hj V hVc (lt hρ1) c hc).2 (hdetu c hc)
  have hodd : ∀ B b, holLeftDifferential normalizedMean V B b.opposite =
      -holLeftDifferential normalizedMean V B b := fun B b => extendOddly_opposite hX' _ b
  have hcurve : ∀ B : Edge L n k j → ComplexMatrix2, ∀ᶠ t : ℂ in 𝓝 0,
      ∀ b, ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist (t • B) V b - 1) < ρ := by
    intro B
    rw [Filter.eventually_all]
    intro b
    have h1 := (hasDerivAt_expTwist_apply V B hinv hneg b).continuousAt
    have h2 : ContinuousAt (fun t : ℂ => ‖PeriodicLattice.expTwist (t • B) V b - 1‖) 0 :=
      (h1.sub continuousAt_const).norm
    have h3 : ‖PeriodicLattice.expTwist ((0 : ℂ) • B) V b - 1‖ < ρ := by
      rw [expTwist_zero_smul hinv B]
      exact hVρ b
    exact h2.eventually_lt continuousAt_const h3
  have hsl : ∀ B ∈ complexEdgeForms L n k j, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless := by
    intro B hB c hc
    obtain ⟨D, hD⟩ := key c hc
    obtain ⟨hF, hF0, hv, -⟩ := hD B
    rw [hv]
    refine ComplexMatrix2.traceless.smul_mem _ ?_
    have hI : {t : ℂ | Matrix.det (normalizedMean (PeriodicLattice.expTwist (t • B) V) c *
        (normalizedMean V c)⁻¹) = 1} ∈ 𝓝 (0 : ℂ) := by
      filter_upwards [hcurve B] with t ht
      have h1 := (HN n k j hn hj _ (expTwist_mem_fieldsIn_complex hX hVc hB t)
        (fun b => (ht b).trans_le hρ2) c hc).2.2.2.1
      have h2 : Matrix.det (normalizedMean (PeriodicLattice.expTwist (t • B) V) c) = 1 := h1
      rw [Matrix.det_mul, h2, Matrix.det_nonsing_inv, hdetu c hc]
      simp
    exact ((hd.2 _ _ _ _ _ _ _ hI hF hF hF).2.1 hF0).2.2.2 (fun t ht => ht) |>.2
  refine ⟨⟨hVc, fun b => lt hρ5 b⟩, hRV, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    exact ⟨fun c hc => hsl B hB c hc, hodd B⟩
  · intro B _ B' _ z
    refine eq_of_eq_on_positive hX' (hodd _) (fun b => ?_) fun c hc => ?_
    · simp only [Pi.add_apply, Pi.smul_apply, hodd]
      rw [smul_neg]
      abel
    · obtain ⟨D, hD⟩ := key c hc
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [(hD _).2.2.1, (hD B).2.2.1, (hD B').2.2.1, map_add, map_smul, smul_add, smul_comm]
  · intro B hB
    have hBc : B ∈ complexEdgeForms L n k j := ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
    refine ⟨fun c hc => ?_, hodd B⟩
    have htr := hsl B hBc c hc
    obtain ⟨D, hD⟩ := key c hc
    obtain ⟨hF, hF0, hv, -⟩ := hD B
    refine ⟨?_, htr⟩
    rw [hv]
    have hr := hasDerivAt_ofReal_comp hF
    have hst := (hr.star).mul hr
    have hunit : ∀ᶠ t : ℝ in 𝓝 0,
        star (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹) * (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹) = 1 := by
      have hc0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
      filter_upwards [hc0.eventually (hcurve B)] with t ht
      have h1 := (HR n k j hn hj _ (expTwist_mem_fieldSpace hX hVr hB t)
        (fun b => (ht b).trans_le hρ3) c hc).2.2
      have h2 : normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c *
          (normalizedMean V c)⁻¹ ∈ ComplexMatrix2.specialUnitary :=
        ComplexMatrix2.specialUnitary.mul_mem h1 (inv_mem_specialUnitary (hRV c hc).2.2)
      exact (Matrix.mem_unitaryGroup_iff').1 (Matrix.mem_specialUnitaryGroup_iff.1 h2).1
    have hF0' : normalizedMean (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹ = 1 := by
      simpa using hF0
    simp only [hF0', star_one, mul_one, one_mul] at hst
    have hc1 : HasDerivAt (fun t : ℝ =>
        star (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹) * (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c *
        (normalizedMean V c)⁻¹)) (0 : ComplexMatrix2) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ComplexMatrix2)).congr_of_eventuallyEq hunit
    have hY := hst.unique hc1
    have hsy : star (D B) = -D B := eq_neg_of_add_eq_zero_left hY
    rw [Matrix.conjTranspose_smul, ← Matrix.star_eq_conjTranspose, hsy]
    have hI : star (Complex.I⁻¹) = Complex.I := by
      simp [Complex.inv_I]
    rw [hI, Complex.inv_I]
    simp
  · intro B c hc
    obtain ⟨D, hD⟩ := key c hc
    exact (hD B).2.2.2.trans (hD B).2.2.1.symm
  · intro l hl
    have hodd2 : ∀ (W : Edge L n k (j + 1) → ComplexMatrix2)
        (g : Vertex L n k (j + 1) → ComplexMatrix2) b,
        covDiff W g b.opposite = -covDiff W g b := fun W g b =>
      extendOddly_opposite hX' _ b
    refine eq_of_eq_on_positive hX' (hodd _) (hodd2 _ _) fun c hc => ?_
    obtain ⟨D, hD⟩ := key c hc
    rw [← (hD _).2.2.2.trans (hD _).2.2.1.symm]
    exact HO n k j hn hj V hVc (lt hρ4) l hl c hc
end YangMills.Construction.RunningCouplingSlope.MeanDerivOnForms
end
