import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunction
import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZero
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinates
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.RealLogarithmOfTheDeterminantOfLinearMaps
import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.PeriodicOperators.TracesOfTheCoefficientsOnPlaneWaves
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (scalarSecondDeriv IsHolomorphicScalarIn)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open JetDomains (IsLiftOf)
open RiemannSums (periodLattice classSum stripSup)
open JetQuad (IsInvertibleJet logNumber logDensity)
theorem riemann_factor_bound {δ : ℝ} {n : ℕ} (hδ : 0 < δ) (hn : 2 / δ ≤ n) :
    (1 + 2 * (Real.exp (δ * n) - 1)⁻¹) ^ 4 - 1 ≤ 45 * Real.exp (-δ * n) := by
  have hx : 2 ≤ δ * n := by
    rw [div_le_iff₀ hδ] at hn
    linarith
  have hE : 3 ≤ Real.exp (δ * n) := by
    have := Real.add_one_le_exp (δ * n)
    linarith
  set E := Real.exp (δ * n) with hEdef
  have hneg : Real.exp (-δ * n) = E⁻¹ := by
    rw [hEdef, ← Real.exp_neg]
    ring_nf
  have hE1 : 0 < E - 1 := by linarith
  set y := 2 * (E - 1)⁻¹ with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, ← div_eq_mul_inv, div_le_one hE1]
    linarith
  have hy3 : y ≤ 3 * E⁻¹ := by
    rw [hy, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hE1 (by linarith)]
    linarith
  have hpoly : (1 + y) ^ 4 - 1 ≤ 15 * y := by
    have h2 : y ^ 2 ≤ y := by nlinarith
    have h3 : y ^ 3 ≤ y := by nlinarith
    have h4 : y ^ 4 ≤ y := by nlinarith [pow_le_one₀ hy0.le hy1 (n := 3)]
    nlinarith
  rw [hneg]
  linarith
theorem isLiftOf_descendField (P : PeriodicData) (n : ℕ) (f : P.Carrier → ℂ)
    (h : ∃ g, IsLiftOf P n g f) : IsLiftOf P n (descendField P n f) f := by
  obtain ⟨g, hg⟩ := h
  intro i
  have hex : ∃ w, ∀ k, P.mkQuot n k = P.mkQuot n i → f k = w :=
    ⟨g (P.mkQuot n i), fun k hk => by rw [← hk, hg]⟩
  exact (Classical.epsilon_spec hex i rfl).symm
variable {F I : PeriodicData}
theorem ofCoords_toCoords {n N : ℕ} (e : Fin N ≃ F.QuotMod n) (ζ : F.QuotMod n → ℂ) :
    ofCoords e (toCoords e ζ) = ζ := by
  funext c
  simp [ofCoords, toCoords]
theorem isOpen_openPolydisk_and_zero_mem {N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) ∧
      (0 : Coordinates.ComplexCoordinates N) ∈ openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ := by
  constructor
  · simp only [openPolydisk, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro j
    simpa using hρ
theorem logDet_holomorphic_and_secondDeriv
    (hLog : LogDetOfMaps.Claim)
    (hCoord : TorusMatrixCoordinates.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hLoc : IsLocalWith F I I T ρ R) {n : ℕ} (hn : 0 < n) (h4 : 4 * R < n)
    (hu : IsUnit (quotOperator F I T n 0)) {N : ℕ} (e : Fin N ≃ F.QuotMod n) :
    (∃ W : Set (Coordinates.ComplexCoordinates N), IsOpen W ∧ 0 ∈ W ∧
      (∀ z ∈ W, ‖normalizedDet F I T n (ofCoords e z) - 1‖ < 1) ∧
      IsHolomorphicScalarIn W (logDetInCoords F I T e)) ∧
    ∀ ζ ζ' : F.QuotMod n → ℂ,
      logDetSecondDeriv F I T e ζ ζ' =
        LinearMap.trace ℂ (I.QuotMod n → ℂ)
            (Ring.inverse (quotOperator F I T n 0) * periodicCoeffTwoMatrix F I T n ζ ζ') -
          LinearMap.trace ℂ (I.QuotMod n → ℂ)
            (Ring.inverse (quotOperator F I T n 0) * periodicCoeffOneMatrix F I T n ζ *
              Ring.inverse (quotOperator F I T n 0) * periodicCoeffOneMatrix F I T n ζ') := by
  obtain ⟨hl1, hl2, hl3, hsym, hcoord⟩ := hCoord F I hF hI T ρ R hLoc n hn h4
  obtain ⟨hHol, hExp, -⟩ := hcoord N e
  have : Finite (I.QuotMod n) := (hQuot I I hI hI n hn).1.2.1
  obtain ⟨hO, h0⟩ := isOpen_openPolydisk_and_zero_mem (N := N) hLoc.radius_pos
  have main := hLog (I.QuotMod n) N (openPolydisk 0 ρ)
    (fun z => quotOperator F I T n (ofCoords e z))
    (fun k => periodicCoeffOneMatrix F I T n (ofCoords e k))
    (fun k h => periodicCoeffTwoMatrix F I T n (ofCoords e k) (ofCoords e h))
    hO h0 hHol hu
    ⟨fun x y => hl1.map_add _ _, fun c x => hl1.map_smul c _⟩
    (fun h => ⟨fun x y => (hl2 _).map_add _ _, fun c x => (hl2 _).map_smul c _⟩)
    (fun k => ⟨fun x y => (hl3 _).map_add _ _, fun c x => (hl3 _).map_smul c _⟩)
    (fun k h => hsym _ _) hExp
  obtain ⟨⟨W, hW, hW0, -, hdist, hhol⟩, hform⟩ := main
  refine ⟨⟨W, hW, hW0, hdist, hhol⟩, fun ζ ζ' => ?_⟩
  have key := hform (toCoords e ζ) (toCoords e ζ')
  simp only [ofCoords_toCoords] at key
  exact key
theorem realLogAbsDet_secondDeriv_eq
    (hRealLog : RealLogDet.Claim)
    (hCoord : TorusMatrixCoordinates.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hLoc : IsLocalWith F I I T ρ R) {n : ℕ} (hn : 0 < n) (h4 : 4 * R < n)
    (hu : IsUnit (quotOperator F I T n 0)) {N : ℕ} (e : Fin N ≃ F.QuotMod n)
    (hReal : IsRealOnRealFields F I T) {W : Set (Coordinates.ComplexCoordinates N)} (hW : IsOpen W)
    (hW0 : 0 ∈ W)
    (hdist : ∀ z ∈ W, ‖normalizedDet F I T n (ofCoords e z) - 1‖ < 1)
    (hhol : IsHolomorphicScalarIn W (logDetInCoords F I T e)) :
    (∀ᶠ v in 𝓝 (0 : Fin N → ℝ),
      LinearMap.det (quotOperator F I T n fun c =>
        (ofRealCoords e v c : ℂ)) ≠ 0) ∧
    HasSecondFDerivAtZero (realLogAbsDetDiffInCoords F I T e) ∧
    ∀ ζ ζ' : F.QuotMod n → ℂ,
      realLogAbsDetSecondDeriv F I T e ζ ζ' =
        logDetSecondDeriv F I T e ζ ζ' := by
  obtain ⟨-, -, -, -, hcoord⟩ := hCoord F I hF hI T ρ R hLoc n hn h4
  have hEntry := (hcoord N e).2.2 hReal
  have : Finite (I.QuotMod n) := (hQuot I I hI hI n hn).1.2.1
  have hev : ∀ᶠ v : Fin N → ℝ in 𝓝 0, ∀ j, |v j| < ρ := by
    refine eventually_all.2 fun j => ?_
    have hlim : Tendsto (fun v : Fin N → ℝ => |v j|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_apply j).abs.tendsto (0 : Fin N → ℝ)
    exact hlim.eventually_lt_const hLoc.radius_pos
  obtain ⟨r1, r2, r3, r4⟩ := hRealLog (I.QuotMod n) N W
    (fun z => quotOperator F I T n (ofCoords e z)) hW hW0 hu hdist hhol
    (hev.mono fun v hv c' c => hEntry v hv c' c)
  exact ⟨r1, ⟨r2, r3⟩, fun ζ ζ' => r4 _ _⟩
theorem claim_of_ingredients (hLog : LogDetOfMaps.Claim)
    (hRealLog : RealLogDet.Claim)
    (hCoord : TorusMatrixCoordinates.Claim)
    (hInv : ZeroFieldInvertibility.Claim)
    (hTraces : PlaneWaveTraces.Claim)
    (hIntegrand : LogDensityBounds.Claim)
    (hRiemann : RiemannSums.Claim)
    (hJets : JetCalculus.Claim)
    (hFacts : JetDomains.OpFunJetTheory)
    (hQuot : Quotients.QuotientTransposeNorm) : Claim := by
  intro F I hF hI T hT hSym
  obtain ⟨ρ, R, hLoc⟩ := id hT
  obtain ⟨⟨δ, hδ, hInvJets⟩, hUnit⟩ := hInv F I hF hI T hT hSym
  obtain ⟨⟨C₀, hC₀, hBound⟩, hCoeff⟩ := hIntegrand F I hF hI T hT δ hδ hInvJets
  have hTr := hTraces F I hF hI T ρ R hLoc hSym
  have hJ := hFacts.2.1 F I I hF hI hI T hT
  obtain ⟨n₀, hn₀, hR₀, hδ₀⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ 4 * R < n₀ ∧ 2 / δ ≤ n₀ := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max (4 * R) (2 / δ))
    refine ⟨m + 1, Nat.succ_pos m, ?_, ?_⟩
    · have := (le_max_left (4 * R) (2 / δ)).trans_lt hm
      push_cast
      linarith
    · have := (le_max_right (4 * R) (2 / δ)).trans_lt hm
      push_cast
      linarith
  have hsizes : ∀ n : ℕ, n₀ ≤ n → 0 < n ∧ 4 * R < n ∧ 2 / δ ≤ n := fun n hn => by
    have hle : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨hn₀.trans_le hn, by linarith, by linarith⟩
  have hvanish : ∀ (n N : ℕ) (e : Fin N ≃ F.QuotMod n), n₀ ≤ n →
      VanishesOffAntipodal F n (logDetSecondDeriv F I T e) := by
    intro n N e hn p hp p' hp' u v hnot
    obtain ⟨h0, h4, -⟩ := hsizes n hn
    have hform := (logDet_holomorphic_and_secondDeriv hLog hCoord hQuot hF hI hLoc h0 h4
      (hUnit ρ R hLoc n h0 h4) e).2
    have r1 := isLiftOf_descendField F n _
      (hJ.descends ρ R hLoc n h0 h4 0 (dualLattice n).zero_mem p hp u u 0).1.1
    have r2 := isLiftOf_descendField F n _
      (hJ.descends ρ R hLoc n h0 h4 0 (dualLattice n).zero_mem p' hp' v v 0).1.1
    obtain ⟨t1, t2⟩ := (hTr n h0 h4).1 p hp p' hp' hnot u v _ _ r1 r2
    rw [hform]
    exact sub_eq_zero.2 (t1.trans t2.symm)
  have hclose : ∀ (n N : ℕ) (e : Fin N ≃ F.QuotMod n), n₀ ≤ n →
      IsCloseToLogNumber F I T n (logDetSecondDeriv F I T e) (45 * C₀) δ := by
    intro n N e hn p hp u v
    obtain ⟨h0, h4, h2⟩ := hsizes n hn
    have hform := (logDet_holomorphic_and_secondDeriv hLog hCoord hQuot hF hI hLoc h0 h4
      (hUnit ρ R hLoc n h0 h4) e).2
    have w := hJ.descends ρ R hLoc n h0 h4 0 (dualLattice n).zero_mem p hp u v 0
    have r1 := isLiftOf_descendField F n _ w.1.1
    have r2 := isLiftOf_descendField F n _ w.1.2.1
    have hsum := (hTr n h0 h4).2 p hp u v _ _ r1 r2
    obtain ⟨hol, per, bd⟩ := hBound p u v
    have hR := (hRiemann n δ _ h0 hδ hol per ⟨_, bd⟩).1
    have hpS : toComplexVec p ∈ imStrip δ := fun μ => by
      simpa [toComplexVec] using hδ.le
    have hℓ := ((hJets δ (toComplexVec p) hδ hpS).2.2.2.2.2.2.1 I hI).2 _
      (hInvJets _ hpS u v)
    rw [(hform _ _).trans hsum, hℓ]
    refine hR.trans ?_
    have hsup : stripSup δ (logDensity (toComplexVec p)
          (jetAlong F I I T (toComplexVec p) u v)) ≤
        C₀ * wNorm (F.quotWeight 1) u * wNorm (F.quotWeight 1) v := by
      have : Nonempty (imStrip δ) := ⟨⟨0, fun μ => by simpa using hδ.le⟩⟩
      exact ciSup_le fun κ => bd κ κ.2
    have hfac := riemann_factor_bound hδ h2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h0
    have hE : 1 < Real.exp (δ * n) := Real.one_lt_exp_iff.2 (by positivity)
    have hfac0 : 0 ≤ (1 + 2 * (Real.exp (δ * n) - 1)⁻¹) ^ 4 - 1 := by
      have hy : 0 ≤ 2 * (Real.exp (δ * n) - 1)⁻¹ := by
        have : 0 < Real.exp (δ * n) - 1 := by linarith
        positivity
      have := one_le_pow₀ (n := 4) (a := 1 + 2 * (Real.exp (δ * n) - 1)⁻¹) (by linarith)
      linarith
    have hB0 : 0 ≤ C₀ * wNorm (F.quotWeight 1) u *
        wNorm (F.quotWeight 1) v := by
      unfold wNorm
      positivity
    refine (mul_le_mul hsup hfac hfac0 hB0).trans (le_of_eq ?_)
    ring
  refine ⟨δ, hδ, hInvJets, ⟨n₀, 45 * C₀, δ, by positivity, hδ, fun n hn => ?_⟩, hCoeff,
    fun hReal => ⟨n₀, 45 * C₀, δ, by positivity, hδ, fun n hn N e => ?_⟩⟩
  · obtain ⟨h0, h4, -⟩ := hsizes n hn
    refine ⟨hUnit ρ R hLoc n h0 h4, fun N e => ⟨?_, hvanish n N e hn, hclose n N e hn⟩⟩
    exact (logDet_holomorphic_and_secondDeriv hLog hCoord hQuot hF hI hLoc h0 h4
      (hUnit ρ R hLoc n h0 h4) e).1
  · obtain ⟨h0, h4, -⟩ := hsizes n hn
    obtain ⟨⟨W, hW, hW0, hdist, hhol⟩, -⟩ :=
      logDet_holomorphic_and_secondDeriv hLog hCoord hQuot hF hI hLoc h0 h4
        (hUnit ρ R hLoc n h0 h4) e
    obtain ⟨r1, r2, r3⟩ := realLogAbsDet_secondDeriv_eq hRealLog hCoord hQuot hF hI hLoc h0 h4
      (hUnit ρ R hLoc n h0 h4) e hReal hW hW0 hdist hhol
    have hDeq : realLogAbsDetSecondDeriv F I T e =
        logDetSecondDeriv F I T e := by
      funext ζ ζ'
      exact r3 ζ ζ'
    refine ⟨r1, r2, ?_, ?_⟩
    · rw [hDeq]
      exact hvanish n N e hn
    · rw [hDeq]
      exact hclose n N e hn
end YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
