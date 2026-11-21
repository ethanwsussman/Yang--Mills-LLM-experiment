import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainKernelsOfAFieldOnTheWhole
import YangMills.Construction.RunningCouplingSlope.ThePlainSaddlesAreLocal
import YangMills.Construction.Towers.FreeOperatorsAreRealOfFiniteRangeAndTrivialOnTheColourProof
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheEntriesOfTheBackgroundKernelAreRealAtRealData
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheBonds
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheSites
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbolProof
import YangMills.Construction.Towers.TheThreeKernelsAreRealAtRealConfigurations
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreLocalProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace SaddleLocality
open Tower Tower.FullSpace PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (IsRealOnRealFields)
open Tower.FullSpace.BackgroundJets (rescaledEdgeSaddle rescaledVertexSaddle gaugeFieldOfForm)
open FullLattice
section Generic
variable {F I J : PeriodicData}
private theorem isSupBelow_mono {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ} (h : IsSupBelow F ζ ρ')
    (hle : ρ' ≤ ρ) : IsSupBelow F ζ ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_mono <;> assumption
private theorem isSupBelow_shiftField {ζ : F.Carrier → ℂ} {ρ : ℝ} (h : IsSupBelow F ζ ρ)
    (n : Fin 4 → ℤ) : IsSupBelow F (shiftField F n ζ) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_shiftField <;> assumption
private theorem isLocalWith_congr {I' : PeriodicData}
    {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hT : IsLocalWith F I I' T ρ R) (hc : ∀ ζ, IsSupBelow F ζ ρ → T' ζ = T ζ) :
    IsLocalWith F I I' T' ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rw [hc ζ hζ]
    exact hT.vanish_far ζ hζ ι' ι hn
  holo_entry := fun ι' ι => by
    obtain ⟨l, e, h, hh, he⟩ := hT.holo_entry ι' ι
    exact ⟨l, e, h, hh, fun ζ hζ => by rw [hc ζ hζ]; exact he ζ hζ⟩
  shift_covariant := fun ζ hζ n ι' ι => by
    rw [hc _ (isSupBelow_shiftField hζ n), hc ζ hζ]
    exact hT.shift_covariant ζ hζ n ι' ι
private theorem isLocalOpFun_smul (hMult : OpFunMultiples.Claim)
    {I' : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hS : IsLocalOpFun F I I' S) (c : ℂ) :
    IsLocalOpFun F I I' (fun ζ => c • S ζ) :=
  (hMult F hF 1 0 one_pos (fun μ => by simp) 0 0 I I' hI hI' S hS c).1
private theorem isLocalWith_leftBlock {T : (F.Carrier → ℂ) → (I.disjSum J).Carrier →
    (I.disjSum J).Carrier → ℂ} {ρ R : ℝ}
    (hT : IsLocalWith F (I.disjSum J) (I.disjSum J) T ρ R) :
    IsLocalWith F I I (fun ζ i' i => T ζ (Sum.inl i') (Sum.inl i)) ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => hT.vanish_far ζ hζ (Sum.inl ι') (Sum.inl ι) hn
  holo_entry := fun ι' ι => hT.holo_entry (Sum.inl ι') (Sum.inl ι)
  shift_covariant := fun ζ hζ n ι' ι => hT.shift_covariant ζ hζ n (Sum.inl ι') (Sum.inl ι)
private theorem isLocalWith_offBlock {T : (F.Carrier → ℂ) → (I.disjSum J).Carrier →
    (I.disjSum J).Carrier → ℂ} {ρ R : ℝ}
    (hT : IsLocalWith F (I.disjSum J) (I.disjSum J) T ρ R) :
    IsLocalWith F J I (fun ζ i' c => T ζ (Sum.inl i') (Sum.inr c)) ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => hT.vanish_far ζ hζ (Sum.inl ι') (Sum.inr ι) hn
  holo_entry := fun ι' ι => hT.holo_entry (Sum.inl ι') (Sum.inr ι)
  shift_covariant := fun ζ hζ n ι' ι => hT.shift_covariant ζ hζ n (Sum.inl ι') (Sum.inr ι)
private def fourBlock (X : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (Mt : (F.Carrier → ℂ) → I.Carrier → J.Carrier → ℂ)
    (M : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ)
    (C : (F.Carrier → ℂ) → J.Carrier → J.Carrier → ℂ) :
    (F.Carrier → ℂ) → (I.disjSum J).Carrier → (I.disjSum J).Carrier → ℂ :=
  fun ζ ι' ι => match ι', ι with
    | .inl a, .inl b => X ζ a b
    | .inl a, .inr b => Mt ζ a b
    | .inr a, .inl b => M ζ a b
    | .inr a, .inr b => C ζ a b
private theorem isLocalWith_fourBlock {X : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {Mt : (F.Carrier → ℂ) → I.Carrier → J.Carrier → ℂ}
    {M : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ}
    {C : (F.Carrier → ℂ) → J.Carrier → J.Carrier → ℂ}
    {ρ R : ℝ} (hX : IsLocalWith F I I X ρ R) (hMt : IsLocalWith F J I Mt ρ R)
    (hM : IsLocalWith F I J M ρ R) (hC : IsLocalWith F J J C ρ R) :
    IsLocalWith F (I.disjSum J) (I.disjSum J) (fourBlock X Mt M C) ρ R where
  radius_pos := hX.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.vanish_far ζ hζ a b hn
    · exact hMt.vanish_far ζ hζ a b hn
    · exact hM.vanish_far ζ hζ a b hn
    · exact hC.vanish_far ζ hζ a b hn
  holo_entry := fun ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.holo_entry a b
    · exact hMt.holo_entry a b
    · exact hM.holo_entry a b
    · exact hC.holo_entry a b
  shift_covariant := fun ζ hζ n ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.shift_covariant ζ hζ n a b
    · exact hMt.shift_covariant ζ hζ n a b
    · exact hM.shift_covariant ζ hζ n a b
    · exact hC.shift_covariant ζ hζ n a b
private theorem isHolomorphicIn_zero (l : ℕ) (ρ : ℝ) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates l) ρ)
      (fun w _ => (fun _ : Coordinates.ComplexCoordinates l => (0 : ℂ)) w) := by apply _root_.YangMills.Construction.Tower.FullSpace.OperatorLocality.isHolomorphicIn_zero <;> assumption
private theorem isLocalWith_saddleMatrix [Nonempty I.Carrier]
    {X : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {Mt : (F.Carrier → ℂ) → I.Carrier → J.Carrier → ℂ}
    {M : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hX : IsLocalWith F I I X ρ R) (hMt : IsLocalWith F J I Mt ρ R)
    (hM : IsLocalWith F I J M ρ R) :
    IsLocalWith F (I.disjSum J) (I.disjSum J)
      (fun ζ => saddleMatrix (X ζ) (Mt ζ) (M ζ)) ρ R where
  radius_pos := hX.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.vanish_far ζ hζ a b hn
    · exact hMt.vanish_far ζ hζ a b hn
    · exact hM.vanish_far ζ hζ a b hn
    · rfl
  holo_entry := fun ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.holo_entry a b
    · exact hMt.holo_entry a b
    · exact hM.holo_entry a b
    · obtain ⟨l, e, -, -, -⟩ := hM.holo_entry a (Classical.arbitrary I.Carrier)
      exact ⟨l, e, fun _ => 0, isHolomorphicIn_zero l ρ, fun ζ _ => rfl⟩
  shift_covariant := fun ζ hζ n ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.shift_covariant ζ hζ n a b
    · exact hMt.shift_covariant ζ hζ n a b
    · exact hM.shift_covariant ζ hζ n a b
    · rfl
end Generic
section Real
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
private theorem isRealOnRealFields_of_near
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hnear : ∀ f : F.Carrier → ℂ, (∀ κ, (f κ).im = 0) → IsSupBelow F f ρ₀ →
      ∀ ι' ι, (T f ι' ι).im = 0) :
    IsRealOnRealFields F I T := by apply _root_.YangMills.Construction.Tower.SecondDerivNearSymbol.isRealOnRealFields_of_eventually <;> assumption
end Real
section RealKernels
variable {L k : ℕ}
private theorem im_tsum_eq_zero {ι : Type} {g : ι → ℂ} (h : ∀ i, (g i).im = 0) :
    (∑' i, g i).im = 0 := by apply _root_.YangMills.Construction.Tower.FreeOperatorsRealLocal.im_tsum_eq_zero <;> assumption
private theorem eta_ne_zero (hL : Conventions.IsAdmissibleBlockingFactor L)
    (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    (rescaledOperators L k U).eta ≠ 0 := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have h : 0 < meshAt L k 0 := zpow_pos (Nat.cast_pos.2 hL0) _
  exact h.ne'
private theorem im_eq_zero_of_ofReal_mul {r : ℝ} (hr : r ≠ 0) {w v : ℂ} (h : (r : ℂ) * w = v)
    (hv : v.im = 0) : w.im = 0 := by
  have h1 := congrArg Complex.im h
  rw [Complex.im_ofReal_mul, hv] at h1
  exact (mul_eq_zero.1 h1).resolve_left hr
private theorem backgroundKernel_im (hZero : KernelAtZeroSources.ZeroSourceKernel)
    (hFormed : HessianLaplacian.HessianKernelAndLaplacianExist)
    (hEnt : RealBackgroundKernel.RawHessianKernelReal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.smallIterateFields L k) (hc : U ∈ FullSpace.fieldSpace L k 0)
    (ι' ι) : (backgroundKernel L k U ι' ι).im = 0 := by
  have hA := hZero L hL k hk U hU
  have hF := (hFormed L hL k hk U hU).1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have e := hA.2.2.2.2.2.2.1 _ hF.2.2.1
  have hY := hEnt L hL k hk U hU hc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  rw [← e]
  simp only [HessianLaplacian.symmHessianKernel,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, swapKernel, Complex.mul_im, Complex.add_im,
    hY ι' ι, hY ι ι']
  simp
private theorem X_im (hZero : KernelAtZeroSources.ZeroSourceKernel)
    (hFormed : HessianLaplacian.HessianKernelAndLaplacianExist)
    (hEnt : RealBackgroundKernel.RawHessianKernelReal)
    (hSad : RescaledSaddleScaling)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.smallIterateFields L k) (hc : U ∈ FullSpace.fieldSpace L k 0)
    (ι' ι) : ((rescaledOperators L k U).X ι' ι).im = 0 := by
  have h1 := congrFun (congrFun (hSad L hL k hk U hU).1 (Sum.inl ι')) (Sum.inl ι)
  have h2 : backgroundKernel L k U ι' ι = ((rescaledOperators L k U).eta : ℂ) ^ 2 *
      (rescaledOperators L k U).X ι' ι * 1 := h1
  refine im_eq_zero_of_ofReal_mul (r := (rescaledOperators L k U).eta ^ 2)
    (pow_ne_zero 2 (eta_ne_zero hL U))
    ?_ (backgroundKernel_im hZero hFormed hEnt hL hk hU hc ι' ι)
  rw [h2]
  push_cast
  ring
private theorem Delta_im (hThree : KernelsRealAtGroupFields)
    (hSad : RescaledSaddleScaling)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.smallIterateFields L k) (hc : U ∈ FullSpace.fieldSpace L k 0)
    (ι' ι) : ((rescaledOperators L k U).Delta ι' ι).im = 0 := by
  have h1 := congrFun (congrFun (hSad L hL k hk U hU).2 (Sum.inl ι')) (Sum.inl ι)
  have h2 : compKernel (swapKernel (covDiffKernel L k 0 U))
      (covDiffKernel L k 0 U) ι' ι = ((rescaledOperators L k U).eta : ℂ) ^ 2 *
      (rescaledOperators L k U).Delta ι' ι * 1 := h1
  have hD := (hThree L hL k hk U hU hc).1
  refine im_eq_zero_of_ofReal_mul (r := (rescaledOperators L k U).eta ^ 2)
    (pow_ne_zero 2 (eta_ne_zero hL U))
    ?_ (v := compKernel (swapKernel (covDiffKernel L k 0 U))
      (covDiffKernel L k 0 U) ι' ι)
    (im_tsum_eq_zero fun i => by simp [Complex.mul_im, swapKernel, hD])
  rw [h2]
  push_cast
  ring
private theorem Rt_im (hThree : KernelsRealAtGroupFields)
    (hSad : RescaledSaddleScaling)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.smallIterateFields L k) (hc : U ∈ FullSpace.fieldSpace L k 0)
    (ι' ι) : ((rescaledOperators L k U).Rt ι' ι).im = 0 := by
  have h1 := congrFun (congrFun (hSad L hL k hk U hU).2 (Sum.inl ι')) (Sum.inr ι)
  have h2 : swapKernel (iterAverageKernel L k U) ι' ι =
      ((rescaledOperators L k U).eta : ℂ) ^ 2 * (rescaledOperators L k U).Rt ι' ι *
        ((rescaledOperators L k U).eta : ℂ) ^ 2 := h1
  have hR := (hThree L hL k hk U hU hc).2.1
  refine im_eq_zero_of_ofReal_mul (r := (rescaledOperators L k U).eta ^ 4)
    (pow_ne_zero 4 (eta_ne_zero hL U))
    ?_ (v := swapKernel (iterAverageKernel L k U) ι' ι) (hR ι ι')
  rw [h2]
  push_cast
  ring
end RealKernels
end SaddleLocality
open SaddleLocality Tower Tower.FullSpace PeriodicOperators FullLattice in
open Tower.FullSpace.BackgroundJets (rescaledEdgeSaddle rescaledVertexSaddle) in
theorem SaddleKernelsAreLocal.holds (hKer : MeanKernelsAreLocal)
    (hI : FieldIteratesNearIdentity)
    (hJB : BackgroundJets.RescaledEdgeSaddleJet)
    (hJS : BackgroundJets.VertexSaddleJet.LocalWithBlockJet)
    (hJ : DisjSumJets.Claim)
    (hZero : KernelAtZeroSources.ZeroSourceKernel)
    (hFormed : HessianLaplacian.HessianKernelAndLaplacianExist)
    (hEnt : RealBackgroundKernel.RawHessianKernelReal)
    (hSad : RescaledSaddleScaling)
    (hThree : KernelsRealAtGroupFields)
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hSets : TowerIndexSets.Claim)
    (hMult : OpFunMultiples.Claim)
    (hNumbers : ParameterIndependence.Claim)
    (hTrn : OpFunTransposeLocal.Claim) :
    SaddleKernelsAreLocal := by
  intro a ha L hL k hk
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨hS0, hB0, -⟩ := hSets L hL k 0 (Nat.zero_le k)
  obtain ⟨hSk, hBk, -⟩ := hSets L hL k k le_rfl
  obtain ⟨hQ, hR, hΓ, ρ₀, hρ₀, hreal⟩ := hKer L hL k hk
  have shrink : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : ((colourEdges L k 0).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R ρ'' R'' : ℝ},
        IsLocalWith (colourEdges L k 0) I I' T ρ R → 0 < ρ'' → ρ'' ≤ ρ → R ≤ R'' →
          IsLocalWith (colourEdges L k 0) I I' T ρ'' R'' :=
    fun hI hI' _ _ _ _ _ h h₁ h₂ h₃ =>
      (hNumbers _ _ _ hB0 hI hI' _ _ _ _ _ h h).1.1 _ _ h₁ h₂ h₃
  obtain ⟨ρ₁, R₁, hM₁⟩ := ((hJ _ _ _ hB0 hB0 hBk).2 _ (hJB L hL k hk).1).1
  obtain ⟨ρ₂, R₂, hM₂⟩ := ((hJ _ _ _ hB0 hS0 hSk).2 _ (hJS L hL k hk).1).1
  obtain ⟨ρq, Rq, hMq⟩ := hQ
  obtain ⟨ρt, Rt, hMt⟩ := hTrn _ _ _ hB0 hB0 hBk _ ⟨ρq, Rq, hMq⟩
  obtain ⟨ρg, Rg, hMg⟩ := isLocalOpFun_smul hMult hB0 hBk hBk (hΓ a) (-1)
  obtain ⟨ρr, Rr, hMr⟩ := hR
  have p₁ := hM₁.radius_pos
  have p₂ := hM₂.radius_pos
  have pq := hMq.radius_pos
  have pt := hMt.radius_pos
  have pg := hMg.radius_pos
  have pr := hMr.radius_pos
  obtain ⟨⟨υ, hυ, -, -, hW⟩, -⟩ := hSmall L hL0 hL k hk
  obtain ⟨δ₀, hδ₀, HI⟩ := hI L hL
  obtain ⟨ρ₃, hρ₃, I⟩ := HI (min δ₀ (υ 0)) (lt_min hδ₀ (hυ 0 (by omega))) (min_le_left _ _) k hk
  have hnear : ∀ f : (colourEdges L k 0).Carrier → ℂ, (∀ κ, (f κ).im = 0) →
      IsSupBelow (colourEdges L k 0) f (min ρ₀ ρ₃) →
      BackgroundJets.gaugeFieldOfForm L k f ∈ FullSpace.smallIterateFields L k ∧
        BackgroundJets.gaugeFieldOfForm L k f ∈ FullSpace.fieldSpace L k 0 := by
    intro f hr hf
    have hf₃ := isSupBelow_mono hf (min_le_right _ _)
    have h0 := I.mem_nearIdentity 0 (Nat.zero_le _) f hf₃
    exact ⟨(hW _ h0.1 fun b => (h0.2 b).trans_le (min_le_right _ _)).1,
      fun b => I.mem_compact f hf₃ hr 0 (Nat.zero_le _) b, h0.1.2⟩
  have : Nonempty (colourVertices L k 0).Carrier :=
    ⟨((0 : Fin 3), (Classical.arbitrary (PeriodicOperators.PosEdge L k 0)).1.initial)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · set ρ := min (min ρ₁ ρq) (min ρt ρg) with hρ
    set R := max (max R₁ Rq) (max Rt Rg) with hR'
    have hρp : 0 < ρ := lt_min (lt_min p₁ pq) (lt_min pt pg)
    refine ⟨ρ, R, isLocalWith_congr (isLocalWith_fourBlock
      (shrink hB0 hB0 (isLocalWith_leftBlock hM₁) hρp ((min_le_left _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_left _ _)))
      (shrink hBk hB0 hMt hρp ((min_le_right _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _)))
      (shrink hB0 hBk hMq hρp ((min_le_left _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_left _ _)))
      (shrink hBk hBk hMg hρp ((min_le_right _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)))) fun f _ => ?_⟩
    funext ι' ι
    rcases ι' with i' | c' <;> rcases ι with i | c
    · rfl
    · rfl
    · rfl
    · show -FullLattice.noiseCovariance a L k (BackgroundJets.gaugeFieldOfForm L k f) k c' c =
        (-1 : ℂ) * FullLattice.noiseCovariance a L k (BackgroundJets.gaugeFieldOfForm L k f) k c' c
      ring
  · set ρ := min (min ρ₂ ρ₂) ρr with hρ
    set R := max (max R₂ R₂) Rr with hR'
    have hρp : 0 < ρ := lt_min (lt_min p₂ p₂) pr
    refine ⟨ρ, R, isLocalWith_congr (isLocalWith_saddleMatrix
      (shrink hS0 hS0 (isLocalWith_leftBlock hM₂) hρp ((min_le_left _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_left _ _)))
      (shrink hSk hS0 (isLocalWith_offBlock hM₂) hρp ((min_le_left _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_left _ _)))
      (shrink hS0 hSk hMr hρp (min_le_right _ _) (le_max_right _ _))) fun f _ => ?_⟩
    funext ι' ι
    rcases ι' with i' | c' <;> rcases ι with i | c <;> rfl
  · refine isRealOnRealFields_of_near hHol (lt_min hρ₀ hρ₃) fun f hr hf ι' ι => ?_
    obtain ⟨hU, hc⟩ := hnear f hr hf
    obtain ⟨hq, -, hg⟩ := hreal f hr (isSupBelow_mono hf (min_le_left _ _))
    rcases ι' with i' | c' <;> rcases ι with i | c
    · exact X_im hZero hFormed hEnt hSad hL hk hU hc i' i
    · show (((meshWeight (meshAt L k k) c / meshWeight (finestMesh L k) i' : ℝ) : ℂ) *
        FullLattice.meanKernelQ L k (BackgroundJets.gaugeFieldOfForm L k f) c i').im = 0
      rw [Complex.im_ofReal_mul, hq c i', mul_zero]
    · exact hq c' i
    · show (-FullLattice.noiseCovariance a L k (BackgroundJets.gaugeFieldOfForm L k f) k c' c).im = 0
      rw [Complex.neg_im, hg a c' c, neg_zero]
  · refine isRealOnRealFields_of_near hHol (lt_min hρ₀ hρ₃) fun f hr hf ι' ι => ?_
    obtain ⟨hU, hc⟩ := hnear f hr hf
    obtain ⟨-, hq, -⟩ := hreal f hr (isSupBelow_mono hf (min_le_left _ _))
    rcases ι' with i' | c' <;> rcases ι with i | c
    · exact Delta_im hThree hSad hL hk hU hc i' i
    · exact Rt_im hThree hSad hL hk hU hc i' c
    · exact hq c' i
    · rfl
end YangMills.Construction.RunningCouplingSlope
end
