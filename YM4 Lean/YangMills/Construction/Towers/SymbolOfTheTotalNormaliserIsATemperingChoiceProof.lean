import YangMills.Construction.Matrices.ConjugationInvariantForms
import YangMills.Construction.Towers.CoefficientsOfTheSymbolOfTheSecondDifferential
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsAFunctional
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.PolarisationAtTheResponseField
import YangMills.Construction.Towers.ResponseFieldOfAPlaneWave
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoice
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.TheMassiveFunctionAsASumOfSymbolsProof
import YangMills.Construction.Towers.TheResponseSymbolNearTheStrip
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbol
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.NormaliserSymbol
open PeriodicOperators
open InfiniteLattice (AmbientSpace)
open PeriodicOperators.Tempered
open FullSpace (IsJointInvertibilityWidth axisPauliElement fieldPeriodicData responseSymbol
  secondVariationSymbol)
section Functions
structure IsBoundedHolomorphicOn (O : Set (Fin 4 → ℂ)) (g : (Fin 4 → ℂ) → ℂ) : Prop where
  isOpen : IsOpen O
  continuousOn : ContinuousOn g O
  differentiable : ∀ a ∈ O, ∀ j : Fin 4, ∀ᶠ ζ in 𝓝 (0 : ℂ),
    DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ
  bounded : ∃ C : ℝ, ∀ κ ∈ O, ‖g κ‖ ≤ C
variable {O : Set (Fin 4 → ℂ)} {g g' : (Fin 4 → ℂ) → ℂ}
theorem IsBoundedHolomorphicOn.of_isHolomorphicIn
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun κ _ => g κ)
    (hb : ∃ C : ℝ, ∀ κ ∈ O, ‖g κ‖ ≤ C) : IsBoundedHolomorphicOn O g := by
  obtain ⟨hO, hc, hd⟩ := h
  refine ⟨hO, (continuous_apply (0 : Fin 1)).comp_continuousOn hc, fun a ha j => ?_, hb⟩
  filter_upwards [hd a ha j] with ζ hζ
  exact (differentiableAt_pi.1 hζ) 0
theorem IsBoundedHolomorphicOn.isHolomorphicIn (h : IsBoundedHolomorphicOn O g) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun κ _ => g κ := by
  refine ⟨h.isOpen, continuousOn_pi.2 fun _ => h.continuousOn, fun a ha j => ?_⟩
  filter_upwards [h.differentiable a ha j] with ζ hζ
  exact differentiableAt_pi.2 fun _ => hζ
theorem IsBoundedHolomorphicOn.mono {O' : Set (Fin 4 → ℂ)} (h : IsBoundedHolomorphicOn O g)
    (hO' : IsOpen O') (hs : O' ⊆ O) : IsBoundedHolomorphicOn O' g := by
  obtain ⟨C, hC⟩ := h.bounded
  exact ⟨hO', h.continuousOn.mono hs, fun a ha j => h.differentiable a (hs ha) j,
    C, fun κ hκ => hC κ (hs hκ)⟩
theorem IsBoundedHolomorphicOn.zero (hO : IsOpen O) :
    IsBoundedHolomorphicOn O fun _ => 0 :=
  ⟨hO, continuousOn_const, fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _,
    0, fun _ _ => by simp⟩
theorem IsBoundedHolomorphicOn.add (h : IsBoundedHolomorphicOn O g)
    (h' : IsBoundedHolomorphicOn O g') : IsBoundedHolomorphicOn O fun κ => g κ + g' κ := by
  obtain ⟨C, hC⟩ := h.bounded
  obtain ⟨C', hC'⟩ := h'.bounded
  refine ⟨h.isOpen, h.continuousOn.add h'.continuousOn, fun a ha j => ?_, C + C', fun κ hκ => ?_⟩
  · filter_upwards [h.differentiable a ha j, h'.differentiable a ha j] with ζ d d'
    exact d.add d'
  · exact (norm_add_le _ _).trans (add_le_add (hC κ hκ) (hC' κ hκ))
theorem IsBoundedHolomorphicOn.sub (h : IsBoundedHolomorphicOn O g)
    (h' : IsBoundedHolomorphicOn O g') : IsBoundedHolomorphicOn O fun κ => g κ - g' κ := by
  obtain ⟨C, hC⟩ := h.bounded
  obtain ⟨C', hC'⟩ := h'.bounded
  refine ⟨h.isOpen, h.continuousOn.sub h'.continuousOn, fun a ha j => ?_, C + C', fun κ hκ => ?_⟩
  · filter_upwards [h.differentiable a ha j, h'.differentiable a ha j] with ζ d d'
    exact d.sub d'
  · exact (norm_sub_le _ _).trans (add_le_add (hC κ hκ) (hC' κ hκ))
theorem IsBoundedHolomorphicOn.mul (h : IsBoundedHolomorphicOn O g)
    (h' : IsBoundedHolomorphicOn O g') : IsBoundedHolomorphicOn O fun κ => g κ * g' κ := by
  obtain ⟨C, hC⟩ := h.bounded
  obtain ⟨C', hC'⟩ := h'.bounded
  refine ⟨h.isOpen, h.continuousOn.mul h'.continuousOn, fun a ha j => ?_, |C| * |C'|,
    fun κ hκ => ?_⟩
  · filter_upwards [h.differentiable a ha j, h'.differentiable a ha j] with ζ d d'
    exact d.mul d'
  · rw [norm_mul]
    exact mul_le_mul ((hC κ hκ).trans (le_abs_self C)) ((hC' κ hκ).trans (le_abs_self C'))
      (norm_nonneg _) (abs_nonneg C)
theorem IsBoundedHolomorphicOn.sum {ι : Type} (s : Finset ι) {f : ι → (Fin 4 → ℂ) → ℂ}
    (hO : IsOpen O) (h : ∀ i ∈ s, IsBoundedHolomorphicOn O (f i)) :
    IsBoundedHolomorphicOn O fun κ => ∑ i ∈ s, f i κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsBoundedHolomorphicOn.zero hO
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem IsBoundedHolomorphicOn.comp_neg (h : IsBoundedHolomorphicOn O g) :
    IsBoundedHolomorphicOn (Neg.neg ⁻¹' O) fun κ => g (-κ) := by
  obtain ⟨C, hC⟩ := h.bounded
  refine ⟨h.isOpen.preimage continuous_neg,
    h.continuousOn.comp continuous_neg.continuousOn fun _ hκ => hκ, fun a ha j => ?_,
    C, fun κ hκ => hC _ hκ⟩
  have ht : Tendsto (fun ζ : ℂ => -ζ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℂ)).tendsto 0
  filter_upwards [ht.eventually (h.differentiable (-a) ha j)] with ζ hζ
  have d := DifferentiableAt.comp (𝕜 := ℂ) ζ hζ (differentiableAt_id.neg)
  refine d.congr_of_eventuallyEq (Eventually.of_forall fun ζ' => ?_)
  simp only [Function.comp_def]
  congr 1
  rw [neg_add, neg_smul]
theorem IsBoundedHolomorphicOn.bilinear {C : Type} [Fintype C] (hO : IsOpen O)
    {a : C → C → (Fin 4 → ℂ) → ℂ} {u v : (Fin 4 → ℂ) → C → ℂ}
    (ha : ∀ c c', IsBoundedHolomorphicOn O (a c c'))
    (hu : ∀ c, IsBoundedHolomorphicOn O fun κ => u κ c)
    (hv : ∀ c, IsBoundedHolomorphicOn O fun κ => v κ c) :
    IsBoundedHolomorphicOn O fun κ => ∑ c, ∑ c', a c c' κ * u κ c * v κ c' :=
  IsBoundedHolomorphicOn.sum _ hO fun c _ => IsBoundedHolomorphicOn.sum _ hO fun c' _ =>
    ((ha c c').mul (hu c)).mul (hv c')
end Functions
section Large
variable {L n : ℕ}
theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 ≤ δ) (y : AmbientSpace) :
    toComplexVec y ∈ imStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_mem_imStrip <;> assumption
theorem imStrip_mono {δ δ' : ℝ} (h : δ ≤ δ') : imStrip δ ⊆ imStrip δ' :=
  fun _ hκ μ => (hκ μ).trans h
theorem neg_mem_imStrip {δ : ℝ} {κ : Fin 4 → ℂ} (h : κ ∈ imStrip δ) : -κ ∈ imStrip δ :=
  fun μ => by simpa using h μ
theorem toComplexVec_neg (y : AmbientSpace) : toComplexVec (-y) = -toComplexVec y := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.SymbolExpansion.toComplexVec_neg_eq <;> assumption
theorem isOpen_setOf_abs_im_lt (δ : ℝ) : IsOpen {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δ} := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.isOpen_openStrip <;> assumption
theorem exists_forall_ge_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) : ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem eventuallyForSides_of_forall_ge (hL : 2 ≤ L) {P : ℕ → Prop} {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → P n) : EventuallyForSides L P := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.eventuallyForSides_of_forall_ge <;> assumption
theorem tendsto_mul_exp_neg_side (hL : 2 ≤ L) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ))) atTop (𝓝 0) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.tendsto_mul_exp_neg <;> assumption
theorem fourierModeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (a : Fin 3) (p : AmbientSpace)
    (μ : Fin 4) : Tempered.fourierModeForm L n a p μ ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.fourierModeForm_mem <;> assumption
end Large
section Assembly
open ResponseSymbolNearStrip (IsTracelessTuple)
theorem axisPauliElement_isTracelessTuple (μ : Fin 4) (a : Fin 3) :
    IsTracelessTuple (axisPauliElement μ a) := by
  intro ρ
  by_cases h : ρ = μ
  · subst h
    simpa [axisPauliElement] using Matrices.ConjugationInvariants.pauliFamily_mem_traceless a
  · simp [axisPauliElement, Pi.single_eq_of_ne h]
theorem pos_of_mem_halfSupRate {δ₀ : ℝ} (h : δ₀ ∈ FreeStrip.halfSupRate) : 0 < δ₀ := by
  obtain ⟨hne, hval⟩ := h
  have hne' : FreeStrip.admissibleRates.Nonempty := hne
  have hval' : 1 / 2 * sSup FreeStrip.admissibleRates = δ₀ := hval
  obtain ⟨d, hd⟩ := hne'
  have hbdd : BddAbove FreeStrip.admissibleRates :=
    ⟨1 / 32, fun x hx => by
      obtain ⟨C, hC⟩ := hx
      exact hC.1.2⟩
  have h1 := le_csSup hbdd hd
  obtain ⟨C, hC⟩ := hd
  have h2 : 0 < d := hC.1.1
  linarith
theorem exists_wNorm_le {C X : Type} [Fintype C] (w : C → ℝ) {S : Set X} {f : X → C → ℂ}
    (h : ∀ c, ∃ M : ℝ, ∀ x ∈ S, ‖f x c‖ ≤ M) : ∃ B : ℝ, ∀ x ∈ S, wNorm w (f x) ≤ B := by
  choose M hM using h
  refine ⟨Real.sqrt (∑ c, |w c| * |M c| ^ 2), fun x hx => ?_⟩
  unfold wNorm
  rw [tsum_fintype]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
  have h1 : ‖f x c‖ ^ 2 ≤ |M c| ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((hM c x hx).trans (le_abs_self _)) 2
  calc w c * ‖f x c‖ ^ 2 ≤ |w c| * ‖f x c‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |w c| * |M c| ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
theorem norm_sub_le_two_mul {x u v : ℂ} {e : ℝ} (h₁ : ‖x - u‖ ≤ e) (h₂ : ‖x - v‖ ≤ e) :
    ‖u - v‖ ≤ 2 * e := by
  have h : u - v = (x - v) - (x - u) := by ring
  rw [h]
  have := norm_sub_le (x - v) (x - u)
  linarith
theorem isTemperedWitnessClaim (hPol : HessianAtResponseField.Claim)
    (hWave : ResponseOfFourierMode.Claim)
    (hClose : SecondDerivNearSymbol.SecondDerivCloseToSymbol)
    (hResp : ResponseSymbolNearStrip.ResponseSymbolHolomorphicNearStrip)
    (hCoef : FullSpace.SymbolCoefficients.SymbolCoefficientsExist)
    (hFun : LogNormaliserIsFunctional.Claim)
    (hGauge : OneLoopLaw.GaugeColourMomenta.GaugeColourMomentumClaim)
    (hMom : DualLatticeDensity.Claim)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement) : IsTemperedWitnessClaim := by
  intro δ₀ hδ₀ L hL hs k hk δ hδ
  have hL2 : 2 ≤ L := by
    have := hs.2
    omega
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hPer L hs k).2 (LocalKernels.fieldIndices L k hL)).1
  have := hF.finite_quot
  let := Fintype.ofFinite (fieldPeriodicData L k hL).UnitQuot
  obtain ⟨δ', hδ', hnear⟩ := hResp
  obtain rfl : δ' = δ₀ := Part.mem_unique hδ' hδ₀
  obtain ⟨O₁, hO₁, hsub₁, hOn⟩ := hnear L hL hs k hk
  obtain ⟨δP, hlt, -, coef, hcoef, hgive⟩ := hCoef L hL hs k hk δ hδ
  have hδpos : 0 < δ := hδ.1.1
  have hδ₀pos := pos_of_mem_halfSupRate hδ₀
  have hδ₁pos : 0 < min δ (2 * δ') := lt_min hδpos (by linarith)
  have hU : IsOpen {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δP} := isOpen_setOf_abs_im_lt δP
  have hUint : {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δP} ⊆ interior (imStrip δP) :=
    interior_maximal (fun κ h μ => (h μ).le) hU
  have hO₁n : IsOpen (Neg.neg ⁻¹' O₁ : Set (Fin 4 → ℂ)) := hO₁.preimage continuous_neg
  obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin 4 → ℂ),
      O = {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δP} ∩ (O₁ ∩ Neg.neg ⁻¹' O₁) := ⟨_, rfl⟩
  have hO : IsOpen O := hOdef ▸ hU.inter (hO₁.inter hO₁n)
  have hOU : O ⊆ interior (imStrip δP) := fun κ hκ => hUint (by rw [hOdef] at hκ; exact hκ.1)
  have hOO₁ : O ⊆ O₁ := fun κ hκ => by rw [hOdef] at hκ; exact hκ.2.1
  have hOn₁ : O ⊆ Neg.neg ⁻¹' O₁ := fun κ hκ => by rw [hOdef] at hκ; exact hκ.2.2
  have hsubO : imStrip (min δ (2 * δ')) ⊆ O := fun κ hκ => by
    have h2 := imStrip_mono (min_le_right δ (2 * δ')) hκ
    rw [hOdef]
    exact ⟨fun μ => ((hκ μ).trans (min_le_left _ _)).trans_lt hlt, hsub₁ h2,
      hsub₁ (neg_mem_imStrip h2)⟩
  obtain ⟨hat, hhat⟩ : ∃ hat : Fin 3 → Fin 4 → (Fin 4 → ℂ) → (fieldPeriodicData L k hL).UnitQuot → ℂ,
      hat = fun a μ p => responseSymbol L k hL p (axisPauliElement μ a) := ⟨_, rfl⟩
  have hatHB : ∀ a μ c, IsBoundedHolomorphicOn O₁ fun κ => hat a μ κ c := fun a μ c => by
    subst hhat
    have h := hOn.symbol_entries _ (axisPauliElement_isTracelessTuple μ a)
    exact .of_isHolomorphicIn (h.1.2.2 c) (h.2 c)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Fin 3 → Fin 3 → Fin 4 → Fin 4 → (Fin 4 → ℂ) → ℂ,
      Φ = fun a a' μ ν p => ∑ c, ∑ c', coef c c' p * hat a μ p c * hat a' ν (-p) c' := ⟨_, rfl⟩
  have hΦ : ∀ a a' μ ν, IsBoundedHolomorphicOn O (Φ a a' μ ν) := fun a a' μ ν => by
    subst hΦdef
    refine IsBoundedHolomorphicOn.bilinear (a := coef) (u := fun κ => hat a μ κ)
      (v := fun κ => hat a' ν (-κ)) hO (fun c c' => ?_) (fun c => ?_) (fun c => ?_)
    · obtain ⟨h₁, M, hM⟩ := hcoef c c'
      exact (IsBoundedHolomorphicOn.of_isHolomorphicIn h₁
        ⟨M, fun κ hκ => hM κ (interior_subset hκ)⟩).mono hO hOU
    · exact (hatHB a μ c).mono hO hOO₁
    · exact (hatHB a' ν c).comp_neg.mono hO hOn₁
  have hsym : ∀ a a' μ ν, ∀ p ∈ imStrip δ,
      secondVariationSymbol L k hL p (hat a μ p) (hat a' ν (-p)) = Φ a a' μ ν p := by
    intro a a' μ ν p hp
    rw [hgive p hp, hΦdef]
    simp only [finsum_eq_sum_of_fintype]
  obtain ⟨Cn, hCn⟩ : ∃ B : ℝ, ∀ (a : Fin 3) (μ : Fin 4), ∀ κ ∈ O₁,
      wNorm ((fieldPeriodicData L k hL).quotWeight 1) (hat a μ κ) ≤ B := by
    have h : ∀ (a : Fin 3) (μ : Fin 4), ∃ B : ℝ, ∀ κ ∈ O₁,
        wNorm ((fieldPeriodicData L k hL).quotWeight 1) (hat a μ κ) ≤ B := fun a μ =>
      exists_wNorm_le _ fun c => (hatHB a μ c).bounded
    choose B hB using h
    refine ⟨∑ a, ∑ μ, |B a μ|, fun a μ κ hκ => (hB a μ κ hκ).trans ?_⟩
    calc B a μ ≤ |B a μ| := le_abs_self _
      _ ≤ ∑ μ', |B a μ'| := Finset.single_le_sum (f := fun μ' => |B a μ'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
      _ ≤ ∑ a', ∑ μ', |B a' μ'| := Finset.single_le_sum (f := fun a' => ∑ μ', |B a' μ'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hreal : ∀ y : AmbientSpace, toComplexVec y ∈ O₁ := fun y =>
    hsub₁ (toComplexVec_mem_imStrip (by linarith) y)
  have hrealn : ∀ y : AmbientSpace, -toComplexVec y ∈ O₁ := fun y =>
    hsub₁ (neg_mem_imStrip (toComplexVec_mem_imStrip (by linarith) y))
  have hCn0 : 0 ≤ Cn := (Real.sqrt_nonneg _).trans (hCn 0 0 _ (hreal 0))
  obtain ⟨C, c, hC, hc, hclose⟩ := hClose L hL hs k hk
  obtain ⟨n₁, h1₁, hn₁⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hPol L hs k hk)
  obtain ⟨n₂, -, hn₂⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hWave L hL hs k hk)
  obtain ⟨n₃, -, hn₃⟩ := exists_forall_ge_of_eventuallyForSides hL2 hclose
  obtain ⟨n₄, -, hn₄⟩ :=
    exists_forall_ge_of_eventuallyForSides hL2 ((hGauge L hL hs).1 _ (hFun L hs k hk))
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max (max n₁ n₂) (max n₃ n₄) := ⟨_, rfl⟩
  have hN₁ : n₁ ≤ N := by omega
  have hN₂ : n₂ ≤ N := by omega
  have hN₃ : n₃ ≤ N := by omega
  have hN₄ : n₄ ≤ N := by omega
  have hN1 : 1 ≤ N := h1₁.trans hN₁
  obtain ⟨e, hedef⟩ : ∃ e : ℕ → ℝ,
      e = fun n => (C * Cn ^ 2) * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) := ⟨_, rfl⟩
  have heo : ∀ n, 0 ≤ e n := fun n => by
    rw [hedef]
    positivity
  have het : Tendsto e atTop (𝓝 0) := by
    rw [hedef]
    exact tendsto_mul_exp_neg_side hL2 hc _
  have hkey : ∀ n, N ≤ n → ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a a' : Fin 3) (μ ν : Fin 4),
      ‖(((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
          complexHessian (logNormaliserFamily L k) n (Tempered.fourierModeForm L n a p μ)
            (Tempered.fourierModeForm L n a' (-p) ν) - Φ a a' μ ν (toComplexVec p)‖ ≤ e n := by
    intro n hn p hp a a' μ ν
    have hn0 : 0 < n := by omega
    have hnp : -p ∈ dualLattice (2 * L ^ n) := neg_mem hp
    have hsc : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) = (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ := by
      simp only [PeriodicLattice.torusSide]
      push_cast
      ring
    rw [hn₁ n (hN₁.trans hn) _ (fourierModeForm_mem hL2 hn0 a p μ) _
        (fourierModeForm_mem hL2 hn0 a' (-p) ν),
      hn₂ n (hN₂.trans hn) p hp a μ, hn₂ n (hN₂.trans hn) (-p) hnp a' ν, toComplexVec_neg, hsc,
      ← hsym a a' μ ν _ (toComplexVec_mem_imStrip hδpos.le p)]
    have hb := hn₃ n (hN₃.trans hn) p hp (hat a μ (toComplexVec p))
      (hat a' ν (-toComplexVec p))
    have fp := hCn a μ _ (hreal p)
    have fm := hCn a' ν _ (hrealn p)
    have hCE : 0 ≤ C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) := by positivity
    subst hhat
    refine hb.trans ?_
    calc _ ≤ C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * Cn * Cn :=
          mul_le_mul (mul_le_mul_of_nonneg_left fp hCE) fm (Real.sqrt_nonneg _)
            (mul_nonneg hCE hCn0)
      _ = e n := by
          rw [hedef]
          ring
  have hvanish : ∀ G : (Fin 4 → ℂ) → ℂ, IsBoundedHolomorphicOn O G →
      (∀ n, N ≤ n → ∀ p ∈ dualLattice (2 * L ^ n), ‖G (toComplexVec p)‖ ≤ 2 * e n) →
      ∀ κ ∈ imStrip (min δ (2 * δ')), G κ = 0 := by
    intro G hG hb
    have hcont : Continuous fun y : AmbientSpace => G (toComplexVec y) := by
      have h2 : Continuous toComplexVec := by
        unfold toComplexVec
        fun_prop
      exact hG.continuousOn.comp_continuous h2 fun y =>
        hsubO (toComplexVec_mem_imStrip hδ₁pos.le y)
    exact ((hMom L hs).2.2 (fun y => G (toComplexVec y)) N (fun n => 2 * e n) hcont hN1
      (fun n _ => mul_nonneg (by norm_num) (heo n)) (by simpa using het.const_mul 2) hb).2
      _ G hδ₁pos ⟨O, hsubO, hG.isHolomorphicIn⟩ fun _ => rfl
  have hdiag : ∀ (μ ν : Fin 4) (a a' : Fin 3), ∀ κ ∈ imStrip (min δ (2 * δ')),
      (if a = a' then Φ 2 2 μ ν κ else 0) = Φ a a' μ ν κ := by
    intro μ ν a a' κ hκ
    by_cases haa : a = a'
    · subst haa
      rw [if_pos rfl]
      refine (sub_eq_zero.1 (hvanish (fun κ => Φ a a μ ν κ - Φ 2 2 μ ν κ)
        ((hΦ a a μ ν).sub (hΦ 2 2 μ ν)) (fun n hn p hp => ?_) κ hκ)).symm
      obtain ⟨c', hc'⟩ := (hn₄ n (hN₄.trans hn)).2.2.2.1 p hp μ ν
      have k₁ := hkey n hn p hp a a μ ν
      have k₂ := hkey n hn p hp 2 2 μ ν
      rw [hc' a a, if_pos rfl] at k₁
      rw [hc' 2 2, if_pos rfl] at k₂
      exact norm_sub_le_two_mul k₁ k₂
    · rw [if_neg haa]
      refine (hvanish (Φ a a' μ ν) (hΦ a a' μ ν) (fun n hn p hp => ?_) κ hκ).symm
      obtain ⟨c', hc'⟩ := (hn₄ n (hN₄.trans hn)).2.2.2.1 p hp μ ν
      have k₁ := hkey n hn p hp a a' μ ν
      rw [hc' a a', if_neg haa, mul_zero, zero_sub, norm_neg] at k₁
      linarith [heo n]
  refine ⟨fun μ ν => Φ 2 2 μ ν, e, ⟨hδ₁pos, ⟨O, hsubO, fun μ ν =>
      ⟨(hΦ 2 2 μ ν).isHolomorphicIn, (hΦ 2 2 μ ν).bounded⟩⟩,
    eventuallyForSides_of_forall_ge hL2 (n₀ := 0) fun n _ => heo n, het,
    eventuallyForSides_of_forall_ge hL2 (n₀ := N) fun n hn p hp a a' μ ν => ?_⟩,
    fun p hp a a' μ ν => ?_⟩
  · show ‖_ - (if a = a' then Φ 2 2 μ ν (toComplexVec p) else 0)‖ ≤ e n
    rw [hdiag μ ν a a' _ (toComplexVec_mem_imStrip hδ₁pos.le p)]
    exact hkey n hn p hp a a' μ ν
  · have hp₁ : p ∈ imStrip (min δ (2 * δ')) := fun μ' => le_min (hp.1 μ') (hp.2 μ')
    have h := (hdiag μ ν a a' p hp₁).trans (hsym a a' μ ν p hp.1).symm
    subst hhat
    exact h
end Assembly
end YangMills.Construction.Tower.NormaliserSymbol
end
