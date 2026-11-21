import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheCoarseCase
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequality
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantOfVariablesWithBoundedCentredMoments
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open TestFunctions
private theorem uniformNorm_nonneg' {X : Type*} (f : X → ℝ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem sharpNormR4_nonneg' (M : ℝ) (f : InfiniteLattice.AmbientSpace → ℝ) :
    0 ≤ sharpNormR4 M f :=
  le_max_of_le_left (uniformNorm_nonneg' f)
private theorem sharpNormTorus_nonneg' {S : ℝ} (M : ℝ) (f : TorusMetric.Torus4 S → ℝ) :
    0 ≤ sharpNormTorus M f :=
  le_max_of_le_left (uniformNorm_nonneg' f)
private theorem mixedCumulant_le_of_centred_moments (hC : CumulantBoundByCentredMoments)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (hn : 2 ≤ n)
    (Z : Fin n → Ω → ℝ) (s : Fin n → ℝ) (g c : ℝ) (hg : 0 ≤ g) (hgc : 2 * g ≤ c)
    (hs : ∀ i, 0 ≤ s i) (hZ : ∀ i, Measurable (Z i)) (hb : ∀ i, ∃ C : ℝ, ∀ᵐ ω ∂ν, |Z i ω| ≤ C)
    (hm : ∀ J : Finset (Fin n), J.Nonempty →
      |∫ ω, ∏ i ∈ J, (Z i ω - ∫ ω', Z i ω' ∂ν) ∂ν| ≤ ∏ i ∈ J, g * s i) :
    ‖Cumulants.mixedCumulant ν Z‖ ≤ (n.factorial : ℝ) * c ^ n * ∏ i, s i := by
  have h := hC Ω ν n Z (fun i => g * s i) hn hZ hb (fun i => mul_nonneg hg (hs i)) hm
  refine h.trans ?_
  have hp : 0 ≤ ∏ i, s i := Finset.prod_nonneg fun i _ => hs i
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (2 : ℝ) ^ n * g ^ n ≤ c ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hgc n
  calc (2 : ℝ) ^ n * (n.factorial : ℝ) * (g ^ n * ∏ i, s i)
      = (n.factorial : ℝ) * ((2 : ℝ) ^ n * g ^ n) * ∏ i, s i := by ring
    _ ≤ (n.factorial : ℝ) * c ^ n * ∏ i, s i := by gcongr
private theorem exists_centred_moment_constant (hF : SeparatedMoments.FineCaseMomentBound)
    (hK : SeparatedMoments.CoarseCaseMomentBound) (D : ChessboardTori.ChessboardSetup) (A b M R d : ℝ) (n : ℕ)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M) (hR : 0 < R) (hd : 0 < d) (hd1 : d ≤ 1) (hn : 2 ≤ n)
    (hI : 2 ≤ (D.K : ℕ) → ReflectedCopies.CopyInequality D A b) :
    ∃ g : ℝ, 0 ≤ g ∧ 2 * g ≤ cumulantConstant D.L A b * (1 + R) ^ 4 * ((n : ℝ) / d) ^ 5 ∧
      SeparatedMoments.CentredMomentBound D M R d g n := by
  have hL13 : (13 : ℝ) ≤ (D.L : ℝ) := by exact_mod_cast D.isAdmissible.2
  have hL1 : (1 : ℝ) < (D.L : ℝ) := by linarith
  have hL0 : (0 : ℝ) < (D.L : ℝ) := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (show 0 < d / 8 by positivity) hL1
  have hscale : SeparatedMoments.IsMaximalScalePower D.L d ((D.L : ℝ) ^ k) := by
    refine ⟨⟨k, rfl⟩, hk1, ?_⟩
    rw [zpow_add_one₀ hL0.ne'] at hk2
    linarith
  have ht : 1 ≤ (n : ℝ) / d := by
    rw [one_le_div hd]
    linarith
  have hP : 0 ≤ (1 + R) ^ 4 * ((n : ℝ) / d) ^ 5 := by positivity
  by_cases hcase : max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) ≤ (D.L : ℝ) ^ k / D.mesh
  · have hK2 : 2 ≤ (D.K : ℕ) := by
      by_contra hlt
      have hK1 : (D.K : ℕ) = 1 := by
        have := D.K.pos
        omega
      have hmesh : D.mesh = (D.L : ℝ)⁻¹ := by
        unfold ChessboardTori.ChessboardSetup.mesh PeriodicLattice.meshSize
        rw [hK1]
        simp
      have hsq : (D.L : ℝ) ^ 2 ≤ (D.L : ℝ) ^ k / D.mesh := (le_max_right _ _).trans hcase
      rw [hmesh, div_inv_eq_mul] at hsq
      nlinarith
    refine ⟨SeparatedMoments.fineConstant D.L A b R n d, ?_, ?_,
      hF D A b M R d _ n hA hb hM hR hd hd1 hn (hI hK2) hscale hcase⟩
    · unfold SeparatedMoments.fineConstant
      positivity
    · unfold SeparatedMoments.fineConstant cumulantConstant
      have hmx := le_max_left (10 * 2 ^ 53 * (D.L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19)))
        (24 * 2 ^ 40 * (D.L : ℝ) ^ 12)
      have := mul_le_mul_of_nonneg_right hmx hP
      linarith
  · refine ⟨SeparatedMoments.coarseConstant D.L R n d, ?_, ?_,
      hK D M R d _ n hM hR hd hd1 hn hscale (not_le.mp hcase)⟩
    · unfold SeparatedMoments.coarseConstant
      positivity
    · unfold SeparatedMoments.coarseConstant cumulantConstant
      have hmx := le_max_right (10 * 2 ^ 53 * (D.L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19)))
        (24 * 2 ^ 40 * (D.L : ℝ) ^ 12)
      have h45 : ((n : ℝ) / d) ^ 4 ≤ ((n : ℝ) / d) ^ 5 := pow_le_pow_right₀ ht (by norm_num)
      have h1 := mul_le_mul_of_nonneg_right hmx hP
      have hY : (0 : ℝ) ≤ 24 * 2 ^ 40 * (D.L : ℝ) ^ 12 * (1 + R) ^ 4 := by positivity
      have h2 := mul_le_mul_of_nonneg_left h45 hY
      linarith
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem isBoundedBorelCompactlySupported_of_lipschitz {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) {x : InfiniteLattice.AmbientSpace}
    {R : ℝ} (hR : 0 < R) (hx : tsupport f ⊆ closedBallR4 x R) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨?_, ⟨C * R + |f x|, fun y => ?_⟩, ?_⟩
  · have hl : LipschitzWith (Real.toNNReal (C * 2)) f := by
      refine LipschitzWith.of_dist_le_mul fun y z => ?_
      rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      have h1 := hC y z
      have h2 := euclidNormVec_le_two_mul_norm (y - z)
      rw [Real.norm_eq_abs] at h1
      unfold euclidDistR4 at h1
      rw [dist_eq_norm]
      nlinarith
    exact hl.continuous.measurable
  · by_cases hy : y ∈ tsupport f
    · have h1 := hC y x
      have h2 : TorusMetric.euclidNormVec (y - x) ≤ R := hx hy
      unfold euclidDistR4 at h1
      rw [Real.norm_eq_abs] at h1 ⊢
      have h3 : |f y| ≤ |f y - f x| + |f x| := by
        simpa using abs_add_le (f y - f x) (f x)
      nlinarith
    · have : f y = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [this, norm_zero]
      positivity
  · refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f) ?_
    refine (Metric.isBounded_closedBall (x := x) (r := R)).subset fun y hy => ?_
    rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
    intro μ
    have h2 : TorusMetric.euclidNormVec (y - x) ≤ R := hx hy
    rw [Real.dist_eq]
    simpa using (abs_apply_le_euclidNormVec (y - x) μ).trans h2
private theorem meshSize_pos' (L : ℕ) (k : ℤ) (hL : 0 < L) : 0 < PeriodicLattice.meshSize L k := by
  unfold PeriodicLattice.meshSize
  exact zpow_pos (by exact_mod_cast hL) _
abbrev _root_.YangMills.SharedProofs.p16883 := @meshSize_pos'
private theorem torusEuclidNorm_le {S : ℝ} (hS : 0 < S) (x : TorusMetric.Torus4 S) :
    TorusMetric.torusEuclidNorm x ≤ S := by
  choose v hv hv' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (x μ)
  have hbdd : BddBelow (TorusMetric.euclidNormVec '' (TorusMetric.torusProj S ⁻¹' {x})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, rfl⟩
    exact Real.sqrt_nonneg _
  refine (csInf_le hbdd ⟨v, funext hv, rfl⟩).trans ?_
  unfold TorusMetric.euclidNormVec
  refine Real.sqrt_le_iff.mpr ⟨hS.le, ?_⟩
  have h : ∀ μ, v μ ^ 2 ≤ (S / 2) ^ 2 := fun μ => by
    have h1 : ‖x μ‖ ≤ |S| / 2 := AddCircle.norm_le_half_period S hS.ne'
    rw [abs_of_pos hS, ← hv' μ] at h1
    rw [← sq_abs (v μ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [Fin.sum_univ_four]
  nlinarith [h 0, h 1, h 2, h 3]
abbrev _root_.YangMills.SharedProofs.p53575 := @torusEuclidNorm_le
private theorem torusSide_pos' (L m : ℕ) (hL : 0 < L) : 0 < PeriodicLattice.torusSide L m := by
  unfold PeriodicLattice.torusSide
  have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  positivity
abbrev _root_.YangMills.SharedProofs.p16249 := @torusSide_pos'
private theorem isBoundedFun_of_lipschitz {S : ℝ} (hS : 0 < S) {f : TorusMetric.Torus4 S → ℝ}
    (hf : IsLipschitzFor euclidDistTorus f) : TestFunctions.IsBoundedFun f := by apply _root_.YangMills.SharedProofs.p4953 <;> assumption
private theorem measurable_pathHolonomy {L m : ℕ} {k : ℤ} (Γ : List (PeriodicLattice.Bond L m k)) :
    Measurable fun U : PeriodicLattice.Bond L m k → Matrices.ComplexMatrix2 =>
      PeriodicLattice.pathHolonomy U Γ := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  induction Γ with
  | nil =>
    simp [PeriodicLattice.pathHolonomy]
  | cons e Γ ih =>
    have : (fun U : PeriodicLattice.Bond L m k → Matrices.ComplexMatrix2 =>
        PeriodicLattice.pathHolonomy U (e :: Γ)) =
        fun U => U e * PeriodicLattice.pathHolonomy U Γ := by
      funext U
      simp [PeriodicLattice.pathHolonomy]
    rw [this]
    exact (measurable_pi_apply e).mul ih
abbrev _root_.YangMills.SharedProofs.p124 := @measurable_pathHolonomy
private theorem measurable_plaquetteCost {L m : ℕ} {k : ℤ} (p : PeriodicLattice.Plaquette L m k) :
    Measurable fun U : PeriodicLattice.Bond L m k → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by
  have htr : Continuous fun X : Matrices.ComplexMatrix2 => (Matrices.ComplexMatrix2.fullTrace X).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace continuous_id)
  have h := htr.measurable.comp (measurable_pathHolonomy p.boundaryBonds)
  unfold PeriodicLattice.plaquetteCost PeriodicLattice.plaquetteHolonomy
  exact (h.const_mul (1 / 2)).const_sub 1
private theorem measurable_smearedObservable
    (hW : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (L m K : ℕ) (hL : 1 < L) (hm : 0 < m) (f : PeriodicLattice.FourTorus L m → ℝ) :
    Measurable fun U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
      PeriodicLattice.smearedObservable f U := by
  have : Finite (PeriodicLattice.Plaquette L m (K : ℤ)) := (hW L m (K : ℤ) hL hm (by positivity)).2.1
  have := Fintype.ofFinite (PeriodicLattice.Plaquette L m (K : ℤ))
  have : (fun U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
      PeriodicLattice.smearedObservable f U) =
      fun U => ∑ p, PeriodicLattice.plaquetteCost U p • f p.barycenter := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [this]
  refine Finset.measurable_sum _ fun p _ => ?_
  simpa [smul_eq_mul] using (measurable_plaquetteCost p).mul_const (f p.barycenter)
private theorem ballClusterBoundInStates_of_inequality
    (hF : SeparatedMoments.FineCaseMomentBound) (hK : SeparatedMoments.CoarseCaseMomentBound)
    (hC : CumulantBoundByCentredMoments)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) (β A b M : ℝ) (hβ : 0 < β)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M)
    (hI : 2 ≤ (K : ℕ) → ReflectedCopies.CopyInequality ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b) :
    BallClusterBoundInStates L M K β A b := by
  intro ν hν n hn R d hR hd f hfL hfB hfS
  have hd₁ : 0 < truncatedDist d := lt_min hd one_pos
  have hd₁1 : truncatedDist d ≤ 1 := min_le_right _ _
  have hd₁d : truncatedDist d ≤ d := min_le_left _ _
  obtain ⟨g, hg, hgc, hmom⟩ := exists_centred_moment_constant hF hK ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b M R
    (truncatedDist d) n hA hb hM hR hd₁ hd₁1 hn hI
  have hsep : HasSeparatedSupportsR4 f (truncatedDist d) :=
    ⟨hd₁, fun i k hik => (ENNReal.ofReal_le_ofReal hd₁d).trans (hfS.2 i k hik)⟩
  have : IsProbabilityMeasure ν := hν.1.1
  have ha : 0 < PeriodicLattice.meshSize L ((K : ℕ) : ℤ) := meshSize_pos' L _ (by have := hL.2; omega)
  have hobs : ∀ i, Measurable (fun U => InfiniteLattice.smearedEnergy
        (a := PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) (f i) U) ∧
      ∃ C : ℝ, ∀ U, |InfiniteLattice.smearedEnergy
        (a := PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) (f i) U| ≤ C := by
    intro i
    obtain ⟨x, hx⟩ := hfB i
    obtain ⟨-, -, hO, -⟩ :=
      (hS _ ha).1.2 (f i) (isBoundedBorelCompactlySupported_of_lipschitz (hfL i) hR hx)
    refine ⟨by simpa [Function.comp_def] using Complex.measurable_re.comp hO.1, ?_⟩
    obtain ⟨C, hC'⟩ := hO.2
    exact ⟨C, fun U => by simpa [Complex.norm_real] using hC' U⟩
  exact mixedCumulant_le_of_centred_moments hC ν n hn
    (fun i U => InfiniteLattice.smearedEnergy (f i) U)
    (fun i => sharpNormR4 M (f i)) g _ hg hgc (fun i => sharpNormR4_nonneg' M (f i))
    (fun i => (hobs i).1)
    (fun i => by
      obtain ⟨C, hC'⟩ := (hobs i).2
      exact ⟨C, Filter.Eventually.of_forall hC'⟩)
    (fun J hJ => hmom.gibbs_bound ν hν f hfL hfB hsep J hJ)
private theorem ballClusterBoundOnTori_of_inequality
    (hF : SeparatedMoments.FineCaseMomentBound) (hK : SeparatedMoments.CoarseCaseMomentBound)
    (hC : CumulantBoundByCentredMoments)
    (hZ : SmearedObservableBound)
    (hP : PeriodicLattice.WilsonCumulantWellPosedness.statement)
    (hW : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) (β A b M : ℝ) (hβ : 0 < β)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M)
    (hI : 2 ≤ (K : ℕ) → ReflectedCopies.CopyInequality ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b) :
    BallClusterBoundOnTori L M K β A b := by
  intro m n hn R d hR hd f hfL hfB hfS
  have hL1 : 1 < L := by have := hL.2; omega
  have hd₁ : 0 < truncatedDist d := lt_min hd one_pos
  have hd₁1 : truncatedDist d ≤ 1 := min_le_right _ _
  have hd₁d : truncatedDist d ≤ d := min_le_left _ _
  obtain ⟨g, hg, hgc, hmom⟩ := exists_centred_moment_constant hF hK ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b M R
    (truncatedDist d) n hA hb hM hR hd₁ hd₁1 hn hI
  have hsep : HasSeparatedSupportsTorus f (truncatedDist d) :=
    ⟨hd₁, fun i k hik => (ENNReal.ofReal_le_ofReal hd₁d).trans (hfS.2 i k hik)⟩
  have : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure L m K β) :=
    (hP.1 L m K β hL1 m.pos K.pos).2.2.2
  have hside : 0 < PeriodicLattice.torusSide L m := torusSide_pos' L m (by omega)
  exact mixedCumulant_le_of_centred_moments hC (PeriodicLattice.wilsonGibbsMeasure L m K β) n hn
    (fun i U => PeriodicLattice.smearedObservable (f i) U)
    (fun i => sharpNormTorus M (f i)) g _ hg hgc (fun i => sharpNormTorus_nonneg' M (f i))
    (fun i => measurable_smearedObservable hW L m K hL1 m.pos (f i))
    (fun i => ⟨_, hZ.2 L m K β R hL.2 hβ hR (f i) (isBoundedFun_of_lipschitz hside (hfL i)) (hfB i)⟩)
    (fun J hJ => hmom.torus_bound m f hfL hfB hsep J hJ)
theorem cumulantBoundsOfInequality_holds
    (hF : SeparatedMoments.FineCaseMomentBound) (hK : SeparatedMoments.CoarseCaseMomentBound)
    (hC : CumulantBoundByCentredMoments)
    (hZ : SmearedObservableBound)
    (hP : PeriodicLattice.WilsonCumulantWellPosedness.statement)
    (hW : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) :
    CumulantConditionsOfInequality := by
  intro L IsDatum A b M hL hpos hA hb hM hI
  have tori : ∀ K β, IsDatum K β → BallClusterBoundOnTori L M K β A b := fun K β h =>
    ballClusterBoundOnTori_of_inequality hF hK hC hZ hP hW L hL K β A b M (hpos K β h) hA hb hM
      (fun hK2 => hI _ rfl hK2 h)
  refine ⟨fun K β h => ?_, tori, fun K β h =>
    ballClusterBoundInStates_of_inequality hF hK hC hS L hL K β A b M (hpos K β h) hA hb hM
      (fun hK2 => hI _ rfl hK2 h)⟩
  intro m n hn d hd f hfL hfS
  have hside : 0 < PeriodicLattice.torusSide L m := torusSide_pos' L m (by have := hL.2; omega)
  exact tori K β h m n hn _ d hside hd f hfL
    (fun i => ⟨0, fun y _ => torusEuclidNorm_le hside _⟩) hfS
end YangMills.Construction.AdmissibleConstants
end
