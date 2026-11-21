import YangMills.Construction.Continuum.MultilinearFunctionalsCoordinatewise
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsUsedOfALimitAlongStates
import YangMills.Construction.SystemsWithFiveBounds.GrowthOfALimitAtNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter AmbientPoints CumulantLimits
open TestSpaces (SepTupleOfCard)
open SeparatedBound SeparatedPowerBound
open LimitGrowthFromCutoffBound (restrictToTestTuples)
open TestSpaces.UnifiedSeparatedTuples
namespace SystemsWithFiveBounds.LimitGrowthAtConstantsProof
open BoundsOnEverySide (SideFamily GibbsStateSequence)
variable {s : Conventions.StandingParameters}
private theorem isLipschitzFor_of_contDiff {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.isLipschitzFor_of_contDiff <;> assumption
private theorem agreeOnTuples_restrict (S : TupleMapFamily s .euclidean) (n : ℕ) (hn : 2 ≤ n) :
    AgreeOnComponents (S n hn) (restrictToTestTuples S n hn) := by
  intro f X he
  exact congrArg (S n hn) (Subtype.ext he)
private theorem restrictToR4_moments (S : TupleMapFamily s .euclidean) :
    FourSpaceGrowth.restrictToR4 (moments S) =
      TestSpaces.centredOfCumulants (restrictToTestTuples S) := by
  funext X
  obtain ⟨n, Y⟩ := X
  exact centredOfMaps_r4 S (restrictToTestTuples S) (fun _ _ _ => rfl)
    (⟨Y.1, (mem_separatedTuples_r4_iff Y.1).2 Y.2⟩ : separatedTuples s .euclidean n)
private theorem growthBound_mono {k : ℕ} {c c' C C' κ κ' : ℝ}
    {σ : TestSpaces.SepTuple → ℝ} (h : TestSpaces.GrowthBound k c C κ σ)
    (hc : c ≤ c') (hC : C ≤ C') (hκ : κ ≤ κ') :
    TestSpaces.GrowthBound k c' C' κ' σ := by
  obtain ⟨hk, hc0, hC0, hκ0, T, hT, hb⟩ := h
  refine ⟨hk, hc0.trans hc, hC0.trans hC, hκ0.trans hκ, T, hT, fun n hn φ => (hb n hn φ).trans ?_⟩
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 n.factorial_ne_zero
  have h₁ : (n.factorial : ℝ) ^ κ ≤ (n.factorial : ℝ) ^ κ' := Real.rpow_le_rpow_of_exponent_le hf hκ
  have h₂ : C ^ n ≤ C' ^ n := pow_le_pow_left₀ hC0 hC n
  have h₃ : 0 ≤ (n.factorial : ℝ) ^ κ := by positivity
  have h₄ : 0 ≤ C ^ n := by positivity
  have hc' : 0 ≤ c' := hc0.trans hc
  have h₅ : 0 ≤ C' ^ n := pow_nonneg (hC0.trans hC) n
  exact mul_le_mul (mul_le_mul hc h₂ h₄ hc') h₁ h₃ (mul_nonneg hc' h₅)
theorem cumulant_separated_le {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N)
    {K : ℕ+} {β : ℝ} (hd : F.IsFirstPassage K β) {ν} (hν : ν ∈ F.stateSet F.L K β)
    {n : ℕ} (hn : 2 ≤ n) {R d : ℝ} (hR : 0 < R) (hd' : 0 < d) (X : SepTupleOfCard n)
    (hX : SupportedSeparated R d X) :
    ‖InfiniteLattice.smearedEnergyCumulant ν X.1‖ ≤ N.cumulantBound n d R * sharpNormProd F.M X := by
  refine B.cumulant_le K β hd ν hν n hn R d hR hd' X.1
    (fun i => isLipschitzFor_of_contDiff
      (X.2.1 i).1 (X.2.1 i).2.1) hX.1 ⟨hd', fun i k hik => ?_⟩
  exact hX.2.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
theorem cumulantBound_one (N : BoundConstants) (n : ℕ) (d : ℝ) :
    N.cumulantBound n d 1 = (powerConst N * max 1 (d ^ (-(N.sepExponent : ℤ)))) ^ n *
      (n.factorial : ℝ) ^ N.factorialExponent := by
  have e : N.aStar * max 1 (d ^ (-(N.sepExponent : ℤ))) * N.ballConst 1 =
      powerConst N * max 1 (d ^ (-(N.sepExponent : ℤ))) := by
    unfold powerConst
    ring
  unfold BoundConstants.cumulantBound
  rw [e]
theorem powerSepBound_of_limit {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N)
    (S : TupleMapFamily s .euclidean) (Q : GibbsStateSequence F.L)
    (hd : ∀ j, F.IsFirstPassage (Q.K j) (Q.β j)) (hst : ∀ j, Q.gibbs j ∈ F.stateSet F.L (Q.K j) (Q.β j))
    (hQ : Q.TendsToFamily S) :
    PowerSepBound F.M N.sepExponent (powerConst N) N.factorialExponent (restrictToTestTuples S) := by
  intro n hn d hd' X hX
  have ht := (hQ n hn ⟨X.1, (mem_separatedTuples_r4_iff X.1).2 X.2⟩).norm
  have hev : ∀ j, ‖InfiniteLattice.smearedEnergyCumulant (Q.gibbs j)
      (⟨X.1, (mem_separatedTuples_r4_iff X.1).2 X.2⟩ :
        separatedTuples s .euclidean n).1‖ ≤
      N.cumulantBound n d 1 * sharpNormProd F.M X := fun j =>
    cumulant_separated_le B (hd j) (hst j) hn one_pos hd' X hX
  have hle := le_of_tendsto ht (Eventually.of_forall hev)
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  rw [cumulantBound_one] at hle
  exact hle
theorem isConnectedFamily_of_limit (hU : BoundsOnEverySide.SeparatedLimitsExist) {F : StatedSideFamily}
    {N : BoundConstants} (B : BoundsHoldAt F N) {S : TupleMapFamily s .euclidean}
    (Q : GibbsStateSequence F.L) (hd : ∀ j, F.IsFirstPassage (Q.K j) (Q.β j))
    (hst : ∀ j, Q.gibbs j ∈ F.stateSet F.L (Q.K j) (Q.β j)) (hQ : Q.TendsToFamily S) :
    IsConnectedFamily S := by
  obtain ⟨φ, S', h⟩ := hU F.L F.admissible F.M F.one_le_M Q N.cumulantBound
    (fun j n hn R d hR hd' X hX =>
      cumulant_separated_le B (hd j) (hst j) hn hR hd' X hX) s
  have hφ : Tendsto φ atTop atTop :=
    tendsto_atTop_mono (fun i => h.strictMono.le_apply) tendsto_id
  have hEq : S' = S := by
    funext n hn f
    exact Complex.ofReal_injective (tendsto_nhds_unique (h.tendsto n hn f) ((hQ n hn f).comp hφ))
  exact hEq ▸ h.isConnected
theorem of_connectedFamilyMomentsAreFunctional
    (hU : BoundsOnEverySide.SeparatedLimitsExist)
    (hG : SeparatedPowerBound.GrowthFromPowerSepBound)
    (hC : ConnectedFamilyMomentsAreFunctional)
    (hE : EntrywiseMultilinearity.Statement) :
    LimitGrowthAtConstants := by
  intro Fr N B s S Q hd hst hQ
  have hP := powerSepBound_of_limit B S Q hd hst hQ
  have hC₀ : 0 ≤ powerConst N :=
    (mul_pos B.admissible_constants.aStar_pos (B.admissible_constants.ballConst_pos 1 one_pos)).le
  have hM : 1 ≤ Fr.M := Fr.one_le_M
  obtain ⟨hml, F, hF⟩ := isConnectedFamily_of_limit hU B Q hd hst hQ
  have hone : ∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnComponents (F.fn n hn) (restrictToTestTuples S n hn) := by
    intro n hn
    rw [hF]
    exact agreeOnTuples_restrict S n hn
  have hmult : ∀ (n : ℕ) (hn : 2 ≤ n), TestSpaces.IsMultilinearOnSep (restrictToTestTuples S n hn) :=
    fun n hn =>
    (((hE s).1 n (by omega)).2.2 _ _
      (agreeOnTuples_restrict S n hn)).1 (hml n hn)
  obtain ⟨-, hFun, -, hCen⟩ := (hE s).2
  have hfun : TestSpaces.IsSepFunctional (TestSpaces.centredOfCumulants (restrictToTestTuples S)) :=
    (hFun.2.2 _ _ (hCen F _ hone)).1 (hC s F).2
  have hκ : 0 ≤ N.factorialExponent := B.admissible_constants.factorialExponent_nonneg
  have hcon := hG _ N.sepExponent (powerConst N) N.factorialExponent (restrictToTestTuples S) hM hC₀ hκ
    hmult hfun hP
  have hgrow : ∀ κ' : ℝ, 20 + N.factorialExponent ≤ κ' →
      FourSpaceGrowth.GrowthBoundOf
        (growthOrder N) (2 * extFactorAbs) (growthBase Fr.M N) κ' (moments S) := by
    intro κ' hκ'
    unfold FourSpaceGrowth.GrowthBoundOf
    rw [restrictToR4_moments]
    exact hcon.growthBound κ' hκ'
  refine ⟨hP, hcon, hgrow, fun cBar hcBar => ?_⟩
  refine growthBound_mono
    (hgrow (20 + N.factorialExponent) le_rfl) ?_ ?_ le_rfl
  · linarith
  · unfold growthConst TestSpaces.onePointConst
    have := mul_nonneg hcBar
      (ENNReal.toReal_nonneg (a := TestSpaces.weightIntegral (growthOrder N)))
    linarith
theorem limitGrowthAtConstants_holds (hU : BoundsOnEverySide.SeparatedLimitsExist)
    (hG : SeparatedPowerBound.GrowthFromPowerSepBound)
    (hC : CumulantLimits.CentredMomentsAndTheirLimits)
    (hE : EntrywiseMultilinearity.Statement) :
    LimitGrowthAtConstants :=
  of_connectedFamilyMomentsAreFunctional hU hG (connectedFamilyMomentsAreFunctional_of hC) hE
end SystemsWithFiveBounds.LimitGrowthAtConstantsProof
end YangMills.Construction
end
