import YangMills.Construction.ColdChainAtEveryLevel.ComplexCriticalFamilies
import YangMills.Construction.ColdChainAtEveryLevel.RealPointsOfAComplexFamily
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsAtATurnedTop
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsOfTheTotal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Matrix Filter Topology
namespace YangMills.Construction.ComplexCriticalFamilies
open BlockAverages CoordinateSeminorms SpanVariations Analytic GaugeMap
open BlockAverages.ChartCoordinates BlockAverages.ComplexChartCoordinates
variable {F : BlockFrame}
theorem exists_finite_spanning_family {W E : Type} [AddCommGroup W] [Module ℝ W] [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ W) (π : W →ₗ[ℝ] E) :
    ∃ (m : ℕ) (e : Fin m → W), (∀ i, e i ∈ P) ∧
      (∀ v ∈ P, ∃ α : Fin m → ℝ, π v = π (∑ i, α i • e i)) ∧
      ∀ x : Fin m → ℝ, π (∑ i, x i • e i) = 0 → x = 0 := by
  set Q := P.map π with hQ
  set bs := Module.finBasis ℝ Q with hb
  have hlift : ∀ i, ∃ v ∈ P, π v = (bs i : E) := fun i => by
    obtain ⟨v, hv, h⟩ := Submodule.mem_map.1 (bs i).2
    exact ⟨v, hv, h⟩
  choose e he hπ using hlift
  have hsum : ∀ x : Fin _ → ℝ, π (∑ i, x i • e i) = ((∑ i, x i • bs i : Q) : E) := by
    intro x
    simp [map_sum, hπ]
  refine ⟨_, e, he, fun v hv => ?_, fun x hx => ?_⟩
  · set y : Q := ⟨π v, Submodule.mem_map_of_mem hv⟩ with hy
    refine ⟨fun i => bs.repr y i, ?_⟩
    rw [hsum, bs.sum_repr y]
  · have h0 : (∑ i, x i • bs i : Q) = 0 := Subtype.ext (by rw [← hsum, hx]; rfl)
    funext i
    exact Fintype.linearIndependent_iff.1 bs.linearIndependent x h0 i
theorem abs_sub_neg_mul_cellSupDist_le (δ : ℝ) (hδ : 0 ≤ δ) (y₀ y y' : F.Cell) :
    |(-δ * (cellSupDist y y₀ : ℝ)) - (-δ * (cellSupDist y' y₀ : ℝ))| ≤ δ * cellSupDist y y' := by apply _root_.YangMills.Construction.ComplexFamilies.abs_neg_mul_cellSupDist_sub_le <;> assumption
section Pair
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {k m : ℕ} {b : Fin k → F.Site F.top × Fin 4}
  {X : Fin k → imaginaryQuaternions}
theorem isRealCoordSeminorm_weightedNorm (e : Fin m → ChartVector F) (R : F.FieldChain) (w : F.SiteWeights)
    (hw : ∀ j x, 0 ≤ w j x) :
    IsRealCoordSeminorm (fun x : Fin m → ℝ => weightedNorm S R (toChart (realCombination e x)) w) where
  nonneg x := weightedNorm_nonneg _ _ _ _
  triangle x x' := by
    have h := weightedNorm_chartMove_le S R (toChart (realCombination e x)) (toChart (realCombination e x')) 1 w hw
    simp only [abs_one, one_mul] at h
    rw [realCombination_add, toChart_add]
    exact h
  smul_real c x := by
    rw [realCombination_smul, toChart_smul, weightedNorm_smul S R _ c w hw]
theorem isRealCoordSeminorm_supWeightedNorm (hL : 0 < F.blockSide) (e : Fin m → ChartVector F) (R : F.FieldChain)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    IsRealCoordSeminorm (fun x : Fin m → ℝ => supWeightedNorm S δ R (toChart (realCombination e x))) where
  nonneg x := supWeightedNorm_nonneg _ _ _ _
  triangle x x' := by
    have h := supWeightedNorm_chartMove_le S hL δ hδ R (toChart (realCombination e x))
      (toChart (realCombination e x')) 1
    simp only [abs_one, one_mul] at h
    rw [realCombination_add, toChart_add]
    exact h
  smul_real c x := by
    rw [realCombination_smul, toChart_smul, supWeightedNorm_smul S hL δ R _ c]
theorem referenceSecondDeriv_congr_right (hodd : Odd F.blockSide) {a : ℝ} {R : F.FieldChain}
    {U A A' : ChainChart F} (h : ChartEqOnBonds S A A') :
    referenceSecondDeriv a S R V U A = referenceSecondDeriv a S R V U A' := by
  unfold referenceSecondDeriv
  have e : ∀ τ σ : ℝ, chartAction a S R (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ U τ) A σ) V =
      chartAction a S R (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ U τ) A' σ) V := by
    intro τ σ
    refine chartAction_congr hodd a R V ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
    · simp only [chartMove]
      rw [h.1 x hx]
    · simp only [chartMove]
      rw [h.2 j hj x hx]
  simp only [e]
variable {a θ δ Ct cT CT s : ℝ}
theorem referenceSecondDeriv_zeroChart_left (hT : ActionTaylorBounds a θ δ Ct cT CT s S V) (B : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V (zeroChart F) B = 0 := by
  have h := hT.hessian_smul_left 0 (zeroChart F) B
  have e : chartSmul 0 (zeroChart F) = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
    · funext j p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
  rw [e] at h
  simpa using h
theorem referenceSecondDeriv_zeroChart_right (hT : ActionTaylorBounds a θ δ Ct cT CT s S V) (B : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V B (zeroChart F) = 0 := by
  have h := hT.hessian_smul_right 0 B (zeroChart F)
  have e : chartSmul 0 (zeroChart F) = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
    · funext j p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
  rw [e] at h
  simpa using h
theorem referenceSecondDeriv_realCombination_left (hT : ActionTaylorBounds a θ δ Ct cT CT s S V)
    (e : Fin m → ChartVector F) (x : Fin m → ℝ) (B : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (realCombination e x)) B =
      ∑ i, x i * referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (e i)) B := by
  classical
  have key : ∀ u : Finset (Fin m),
      referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (∑ i ∈ u, x i • e i)) B =
      ∑ i ∈ u, x i * referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (e i)) B := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, toChart_zero]
      exact referenceSecondDeriv_zeroChart_left hT B
    | insert i u hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, toChart_add, hT.hessian_add_left, ih, toChart_smul]
      congr 1
      exact hT.hessian_smul_left _ _ _
  exact key Finset.univ
theorem referenceSecondDeriv_realCombination_right (hT : ActionTaylorBounds a θ δ Ct cT CT s S V)
    (e : Fin m → ChartVector F) (x : Fin m → ℝ) (B : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V B (toChart (realCombination e x)) =
      ∑ i, x i * referenceSecondDeriv a S (referenceFieldChain S V) V B (toChart (e i)) := by
  classical
  have key : ∀ u : Finset (Fin m),
      referenceSecondDeriv a S (referenceFieldChain S V) V B (toChart (∑ i ∈ u, x i • e i)) =
      ∑ i ∈ u, x i * referenceSecondDeriv a S (referenceFieldChain S V) V B (toChart (e i)) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, toChart_zero]
      exact referenceSecondDeriv_zeroChart_right hT B
    | insert i u hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, toChart_add, hT.hessian_add_right, ih, toChart_smul]
      congr 1
      exact hT.hessian_smul_right _ _ _
  exact key Finset.univ
def secondDerivMatrix (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (e : Fin m → ChartVector F) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (e i)) (toChart (e j))
theorem dotProduct_secondDerivMatrix_mulVec (hT : ActionTaylorBounds a θ δ Ct cT CT s S V)
    (e : Fin m → ChartVector F) (x α : Fin m → ℝ) :
    x ⬝ᵥ (secondDerivMatrix a S V e *ᵥ α) =
      referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (realCombination e x))
        (toChart (realCombination e α)) := by
  rw [referenceSecondDeriv_realCombination_left hT]
  simp only [dotProduct, Matrix.mulVec, secondDerivMatrix, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [referenceSecondDeriv_realCombination_right hT]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
theorem matrixFormPairing_eq_re_add_im (M : Matrix (Fin m) (Fin m) ℝ) (D : Fin m → ℂ) (α : Fin m → ℝ) :
    matrixFormPairing M D α =
      ((realParts D ⬝ᵥ (M *ᵥ α) : ℝ) : ℂ) + Complex.I * ((imagParts D ⬝ᵥ (M *ᵥ α) : ℝ) : ℂ) := by
  simp only [matrixFormPairing, dotProduct, realParts, imagParts]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← Complex.re_add_im (D i)]
  ring
theorem matrixFormPairing_secondDerivMatrix_eq (hT : ActionTaylorBounds a θ δ Ct cT CT s S V)
    (e : Fin m → ChartVector F) (D : Fin m → ℂ) (α : Fin m → ℝ) :
    matrixFormPairing (secondDerivMatrix a S V e) D α =
      complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexSpan (fun i => toChart (e i)) D)
        (toChart (realCombination e α)) := by
  rw [matrixFormPairing_eq_re_add_im, dotProduct_secondDerivMatrix_mulVec hT,
    dotProduct_secondDerivMatrix_mulVec hT, complexSpan_eq]
  rfl
theorem directionPairing_sub (v v' : Fin m → ℂ) (α : Fin m → ℝ) :
    directionPairing (v - v') α = directionPairing v α - directionPairing v' α := by
  simp only [directionPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem directionPairing_zero (α : Fin m → ℝ) : directionPairing (0 : Fin m → ℂ) α = 0 := by
  simp [directionPairing]
theorem localNorm_le_weightedNorm_invertedDecay (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) (R : F.FieldChain)
    (A : ChainChart F) (y z : F.Cell) :
    localNorm S R A (constOneWeights F) z ≤ weightedNorm S R A (invertedWeights (decayWeights F δ 0 0 y)) := by
  refine le_trans ?_ (localNorm_le_weightedNorm S R A _ z)
  unfold localNorm
  refine Real.sqrt_le_sqrt (localNormSq_mono_weights S _ R A _ _ (fun _ _ => zero_le_one) fun j x => ?_)
  have h1 := decayWeights_pos hL δ 0 0 y j x
  have h2 := decayWeights_le_one δ hδ 0 y j x
  show (1 : ℝ) ≤ (decayWeights F δ 0 0 y j x)⁻¹
  exact (one_le_inv₀ h1).2 h2
theorem eventually_chartIsRegular_chartMove (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) {R : F.FieldChain} {c₁ : ℝ}
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ R U ≤ c₁ → ChartIsRegular S R U)
    {U : ChainChart F} (A : ChainChart F) (hU : supWeightedNorm S δ R U < c₁) :
    ∀ᶠ τ : ℝ in 𝓝 0, ChartIsRegular S R (chartMove U A τ) := by apply _root_.YangMills.Construction.ComplexFamilies.eventually_chartIsRegular_chartMove <;> assumption
variable {Ca c C c₁ : ℝ}
theorem norm_complexFirstVariation_zero_le (hL : Odd F.blockSide) (hδ : 0 ≤ δ) (hc₁ : 0 < c₁)
    (hT : ActionTaylorBounds a θ δ Ct cT CT s S V) (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hc : 0 ≤ c)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U)
    (A : ChainChart F) (y : F.Cell) :
    ‖complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexTwistedTop b X 0 V) A‖ ≤
      (Ct * s + CT * s ^ 2) * weightedNorm S (referenceFieldChain S V) A
        (invertedWeights (decayWeights F δ 0 0 y)) := by
  have hzero : supWeightedNorm S δ (referenceFieldChain S V) (zeroChart F) = 0 := by
    have h := supWeightedNorm_smul S hL.pos δ (referenceFieldChain S V) (zeroChart F) 0
    have e : chartMove (zeroChart F) (zeroChart F) 0 = zeroChart F := by
      apply chainChart_ext
      · funext p i
        simp [chartMove, zeroChart]
      · funext j p i
        simp [chartMove, zeroChart]
    rw [e] at h
    simpa using h
  have hsup : complexSupWeightedNorm S δ (referenceFieldChain S V) (realChart (zeroChart F)) ≤ c := by
    simp only [complexSupWeightedNorm, realChart]
    have : supWeightedNorm S δ (referenceFieldChain S V) ⟨fun _ _ => 0, fun _ _ _ => 0⟩ = 0 := hzero
    rw [this, hzero]
    simpa using hc
  have hd := differentiableAt_complexChartMove_line hB (ζ := 0) hsup (by simpa using hc) A
  rw [complexTwistedTop_zero] at hd ⊢
  have hr := complexFirstVariation_real a (referenceFieldChain S V) (zeroChart F) A V hd
    (eventually_chartIsRegular_chartMove hL.pos hδ hreg A (by rw [hzero]; exact hc₁))
  obtain ⟨ℓ₀, -, -, hl⟩ := hT.linear_source
  obtain ⟨h1, h2⟩ := hl A 0 y 0 (Or.inr rfl)
  have hfv : chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A =
      (complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexifyField V) A).re :=
    hr.1.deriv
  have hnorm : ‖complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexifyField V) A‖ =
      |chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A| := by
    rw [hfv]
    have e : complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexifyField V) A =
        (((complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
          (complexifyField V) A).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using hr.2)
    exact (congrArg norm e).trans ((Complex.norm_real _).trans (Real.norm_eq_abs _))
  rw [hnorm]
  have h3 := abs_sub_abs_le_abs_sub (chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A) (ℓ₀ A)
  have e : (Ct * s + CT * s ^ 2) * weightedNorm S (referenceFieldChain S V) A
      (invertedWeights (decayWeights F δ 0 0 y)) =
      Ct * s * weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ 0 0 y)) +
        CT * s ^ 2 * weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ 0 0 y)) := by
    ring
  rw [e]
  linarith
theorem norm_complexFirstVariation_twist_sub_le (hL : 0 < F.blockSide) (hδ : 0 ≤ δ)
    (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hC : 0 ≤ C) {W : ComplexChainChart F} (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c)
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ ≤ c) (hc : 0 ≤ c) (A : ChainChart F) (y : F.Cell) :
    ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
        complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X 0 V) A‖ ≤
      (C * ∑ l, ‖ζ l‖) * weightedNorm S (referenceFieldChain S V) A
        (invertedWeights (decayWeights F δ 0 0 y)) := by
  classical
  set q := weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ 0 0 y)) with hq
  set G : (Fin k → ℂ) → ℂ := fun ζ' =>
    complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ' V) A with hG
  set part : Finset (Fin k) → Fin k → ℂ := fun u l => if l ∈ u then ζ l else 0 with hpart
  have hsz : ∀ u, ∑ l, ‖part u l‖ ≤ c := by
    intro u
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) hζ
    simp only [hpart]
    split_ifs
    · exact le_rfl
    · simp
  have key : ∀ u : Finset (Fin k), ‖G (part u) - G 0‖ ≤ (C * ∑ l ∈ u, ‖ζ l‖) * q := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      have : part ∅ = 0 := by
        funext l
        simp [hpart]
      simp [this]
    | insert i u hi ih =>
      have h1 := hB.localTwist W (part (insert i u)) (part u) i hW (hsz _) (hsz _) (fun l hl => by
        simp only [hpart, Finset.mem_insert, hl, false_or]) A
      have e1 : part (insert i u) i - part u i = ζ i := by
        simp [hpart, hi]
      rw [e1] at h1
      have h2 := localNorm_le_weightedNorm_invertedDecay (S := S) hL hδ (referenceFieldChain S V) A y (b i).1
      have h3 : ‖G (part (insert i u)) - G (part u)‖ ≤ C * ‖ζ i‖ * q :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      have h4 : ‖G (part (insert i u)) - G 0‖ ≤ ‖G (part (insert i u)) - G (part u)‖ + ‖G (part u) - G 0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [Finset.sum_insert hi]
      nlinarith
  have e : part Finset.univ = ζ := by
    funext l
    simp [hpart]
  have := key Finset.univ
  rw [e] at this
  exact this
theorem complexWeightedNorm_sub_le_of_variation (hE : ReferenceFormWeightedEstimate a θ δ Ca S V) (hCa : 0 < Ca)
    {Ca' : ℝ} (hB : TwistedTotalBounds a θ δ Ca' c C s S V b X) (hC : 0 ≤ C)
    (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0) (hθ' : θ' = θ ∨ θ' = 0 ∨ θ' = -θ)
    (hφ : ∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y')
    (ζ : Fin k → ℂ) (W W' : ComplexChainChart F) (β : ℝ) (hβ : 0 ≤ β)
    (h1 : InGaugeSlice S V (referenceFieldChain S V 0) W.re.fine)
    (h2 : InGaugeSlice S V (referenceFieldChain S V 0) W.im.fine)
    (h3 : InGaugeSlice S V (referenceFieldChain S V 0) W'.re.fine)
    (h4 : InGaugeSlice S V (referenceFieldChain S V 0) W'.im.fine)
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c)
    (hW' : complexSupWeightedNorm S δ (referenceFieldChain S V) W' ≤ c)
    (hζ : ∑ l, ‖ζ l‖ ≤ c)
    (hκ : 4 * Ca * C * (complexSupWeightedNorm S δ (referenceFieldChain S V) W +
      complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖) ≤ 1)
    (hnn : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W +
      complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖)
    (hf : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
          complexFirstVariation a S (referenceFieldChain S V) W' (complexTwistedTop b X ζ V) A‖ ≤
        β * weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))) :
    complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W W') (classWeight F φ θ' p) ≤ 4 * Ca * β := by
  set D := complexChartSub W W' with hD
  set N := complexWeightedNorm S (referenceFieldChain S V) D (classWeight F φ θ' p) with hN
  set Kf := C * (complexSupWeightedNorm S δ (referenceFieldChain S V) W +
      complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖) with hKf
  have hN0 : 0 ≤ N := add_nonneg (weightedNorm_nonneg _ _ _ _) (weightedNorm_nonneg _ _ _ _)
  have hbound : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      ‖complexReferenceSecondDeriv a S (referenceFieldChain S V) V D A‖ ≤
        (β + Kf * N) * weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)) := by
    intro A hA
    have l1 := hB.lipschitz W W' ζ hW hW' hζ φ θ' p hθ' hφ A
    have l2 := hf A hA
    have e : complexReferenceSecondDeriv a S (referenceFieldChain S V) V D A =
        (complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
          complexFirstVariation a S (referenceFieldChain S V) W' (complexTwistedTop b X ζ V) A) -
        (complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
          complexFirstVariation a S (referenceFieldChain S V) W' (complexTwistedTop b X ζ V) A -
          complexReferenceSecondDeriv a S (referenceFieldChain S V) V D A) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add l2 l1
  have hsl : ∀ U U' : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
      InGaugeSlice S V (referenceFieldChain S V 0) U'.fine →
      InGaugeSlice S V (referenceFieldChain S V 0) (chartMove U U' (-1)).fine := by
    intro U U' hU hU'
    have hv : ofChart U + (-1 : ℝ) • ofChart U' ∈ gaugeSliceSubmodule S V (referenceFieldChain S V 0) :=
      Submodule.add_mem _ (mem_gaugeSliceSubmodule.2 hU)
        (Submodule.smul_mem _ _ (mem_gaugeSliceSubmodule.2 hU'))
    have e : chartMove U U' (-1) = toChart (ofChart U + (-1 : ℝ) • ofChart U') :=
      chartMove_toChart (ofChart U) (ofChart U') (-1)
    rw [e]
    exact mem_gaugeSliceSubmodule.1 hv
  have hre := hE φ p θ' hθ' hφ D.re (fun A => referenceSecondDeriv a S (referenceFieldChain S V) V D.re A)
    (β + Kf * N) (by positivity) (hsl _ _ h1 h3) (fun _ _ => rfl) (fun A hA => by
      refine le_trans ?_ (hbound A hA)
      have := Complex.abs_re_le_norm (complexReferenceSecondDeriv a S (referenceFieldChain S V) V D A)
      simpa [complexReferenceSecondDeriv] using this)
  have him := hE φ p θ' hθ' hφ D.im (fun A => referenceSecondDeriv a S (referenceFieldChain S V) V D.im A)
    (β + Kf * N) (by positivity) (hsl _ _ h2 h4) (fun _ _ => rfl) (fun A hA => by
      refine le_trans ?_ (hbound A hA)
      have := Complex.abs_im_le_norm (complexReferenceSecondDeriv a S (referenceFieldChain S V) V D A)
      simpa [complexReferenceSecondDeriv] using this)
  have hsum : N ≤ 2 * Ca * (β + Kf * N) := by
    have hNe : N = weightedNorm S (referenceFieldChain S V) D.re (classWeight F φ θ' p) +
        weightedNorm S (referenceFieldChain S V) D.im (classWeight F φ θ' p) := rfl
    calc N = weightedNorm S (referenceFieldChain S V) D.re (classWeight F φ θ' p) +
        weightedNorm S (referenceFieldChain S V) D.im (classWeight F φ θ' p) := hNe
      _ ≤ Ca * (β + Kf * N) + Ca * (β + Kf * N) := add_le_add hre him
      _ = 2 * Ca * (β + Kf * N) := by ring
  have h5 : 2 * Ca * Kf ≤ 1 / 2 := by
    have : 4 * Ca * Kf ≤ 1 := by
      rw [hKf]
      linarith [hκ]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right h5 hN0]
theorem twistedTotalBounds_mono {c' C' : ℝ} (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hc : c' ≤ c) (hC : C ≤ C') (hC0 : 0 ≤ C) (hs : 0 ≤ s) : TwistedTotalBounds a θ δ Ca c' C' s S V b X where
  analytic m A t ζ h1 h2 := hB.analytic m A t ζ (h1.trans hc) (h2.trans hc)
  lipschitz W W' ζ h1 h2 h3 φ θ' p h4 h5 A := by
    refine (hB.lipschitz W W' ζ (h1.trans hc) (h2.trans hc) (h3.trans hc) φ θ' p h4 h5 A).trans ?_
    have n1 : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W :=
      add_nonneg (supWeightedNorm_nonneg _ _ _ _) (supWeightedNorm_nonneg _ _ _ _)
    have n2 : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W' :=
      add_nonneg (supWeightedNorm_nonneg _ _ _ _) (supWeightedNorm_nonneg _ _ _ _)
    have n4 : 0 ≤ complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W W') (classWeight F φ θ' p) :=
      add_nonneg (weightedNorm_nonneg _ _ _ _) (weightedNorm_nonneg _ _ _ _)
    have n5 := weightedNorm_nonneg S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
    gcongr
  localTwist W ζ ζ' l h1 h2 h3 h4 A := by
    refine (hB.localTwist W ζ ζ' l (h1.trans hc) (h2.trans hc) (h3.trans hc) h4 A).trans ?_
    have n1 : 0 ≤ localNorm S (referenceFieldChain S V) A (constOneWeights F) (b l).1 := Real.sqrt_nonneg _
    gcongr
  twistSource ζ h := by
    obtain ⟨l1, e1, e2, e3⟩ := hB.twistSource ζ (h.trans hc)
    refine ⟨l1, e1, e2, fun A p y₀ θ' hθ' => ⟨(e3 A p y₀ θ' hθ').1, (e3 A p y₀ θ' hθ').2.trans ?_⟩⟩
    have n1 := weightedNorm_nonneg S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ θ' p y₀))
    have n2 : 0 ≤ s + ∑ l, |ζ l| := add_nonneg hs (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    gcongr
theorem exists_isComplexCriticalFamily (hZ : HolomorphicZeroOfCoerciveFamilyProperty) (hL : Odd F.blockSide)
    {Ca₄ r r' C₀ : ℝ}
    (hδ : 0 < δ) (hCa₄ : 0 < Ca₄) (hCt : 0 ≤ Ct) (hCT : 0 ≤ CT) (hC : 0 ≤ C)
    (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r) (hr' : 0 < r') (hr'r : r' ≤ r) (hrc : r ≤ c) (hrc₁ : r < c₁)
    (hC₀ : 4 * Ca₄ * (Ct + CT + C + 1) ≤ C₀)
    (hE : ReferenceFormWeightedEstimate a θ δ Ca₄ S V) (hT : ActionTaylorBounds a θ δ Ct cT CT s S V)
    (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U)
    (hs1' : 16 * Ca₄ * C * r ≤ 1) (hs2 : 16 * Ca₄ * (Ct + CT) * s ≤ r) (hs3 : 16 * Ca₄ * C * r' ≤ r) :
    ∃ Wf : (Fin k → ℂ) → ComplexChainChart F, IsComplexCriticalFamily a θ δ C₀ r r' s S V b X Wf := by
  classical
  have hc0 : 0 ≤ c := hr.le.trans hrc
  have hc₁ : 0 < c₁ := hr.trans hrc₁
  obtain ⟨m, e, he, hspan, hind⟩ :=
    exists_finite_spanning_family (gaugeSliceSubmodule S V (referenceFieldChain S V 0)) (bondValues S)
  have hlin : ∀ x, realCombination e x ∈ gaugeSliceSubmodule S V (referenceFieldChain S V 0) := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  have hrep : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      ∃ α : Fin m → ℝ, ChartEqOnBonds S A (toChart (realCombination e α)) := by
    intro A hA
    obtain ⟨α, hα⟩ := hspan (ofChart A) (mem_gaugeSliceSubmodule.2 hA)
    exact ⟨α, (bondValues_eq_iff S _ _).1 hα⟩
  have hYn : IsRealCoordSeminorm
      (fun x : Fin m → ℝ => supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) :=
    isRealCoordSeminorm_supWeightedNorm hL.pos e _ δ hδ.le
  have hYdef : ∀ x : Fin m → ℝ,
      supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x)) = 0 → x = 0 := by
    intro x h0
    apply hind
    have h1 : weightedNorm S (referenceFieldChain S V) (toChart (realCombination e x)) (decayWeights F δ 0 0 0) = 0 :=
      le_antisymm ((weightedNorm_decay_le_supWeightedNorm S hL.pos δ hδ.le _ _ 0).trans h0.le)
        (weightedNorm_nonneg _ _ _ _)
    have h2 := chartEq_zero_of_weightedNorm_eq_zero S hL _ _ _ (fun j x => decayWeights_pos hL.pos δ 0 0 0 j x) h1
    exact (bondValues_eq_iff S (realCombination e x) 0).2 h2
  have hYc : ∀ t : Fin m → ℂ,
      complexSupWeightedNorm S δ (referenceFieldChain S V) (complexSpan (fun i => toChart (e i)) t) =
      complexifiedSeminorm
        (fun x : Fin m → ℝ => supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t := by
    intro t
    rw [complexSpan_eq]
    rfl
  have hpc : ∀ (y : F.Cell) (t : Fin m → ℂ),
      complexWeightedNorm S (referenceFieldChain S V) (complexSpan (fun i => toChart (e i)) t)
        (decayWeights F δ 0 0 y) =
      complexifiedSeminorm (fun x : Fin m → ℝ =>
        weightedNorm S (referenceFieldChain S V) (toChart (realCombination e x)) (decayWeights F δ 0 0 y)) t := by
    intro y t
    rw [complexSpan_eq]
    rfl
  set Ω : Set (Fin k → ℂ) := {ζ | ∑ l, ‖ζ l‖ < r'} with hΩd
  have hΩ : IsOpen Ω := isOpen_lt (by fun_prop) continuous_const
  have hζc : ∀ ζ ∈ Ω, ∑ l, ‖ζ l‖ ≤ c := fun ζ hζ => (le_of_lt hζ).trans (hr'r.trans hrc)
  have hsup0 : complexSupWeightedNorm S δ (referenceFieldChain S V) (realChart (zeroChart F)) ≤ c := by
    have h := hYc 0
    rw [complexSpan_zero] at h
    rw [h]
    have e1 : realParts (0 : Fin m → ℂ) = 0 := by
      funext i
      simp [realParts]
    have e2 : imagParts (0 : Fin m → ℂ) = 0 := by
      funext i
      simp [imagParts]
    have e3 : supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e 0)) = 0 := by
      have := hYn.smul_real 0 0
      simpa using this
    simp only [complexifiedSeminorm, e1, e2, e3]
    simpa using hc0
  have hco : ∀ (y : F.Cell) (x : Fin m → ℝ) (β : ℝ), 0 ≤ β →
      (∀ α, |x ⬝ᵥ (secondDerivMatrix a S V e *ᵥ α)| ≤
        β * weightedNorm S (referenceFieldChain S V) (toChart (realCombination e α))
          (invertedWeights (decayWeights F δ 0 0 y))) →
      weightedNorm S (referenceFieldChain S V) (toChart (realCombination e x)) (decayWeights F δ 0 0 y) ≤
        Ca₄ * β := by
    intro y x β hβ hb
    have hb' : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        |referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (realCombination e x)) A| ≤
          β * weightedNorm S (referenceFieldChain S V) A (invertedWeights
            (classWeight F (fun z => -δ * (cellSupDist z y : ℝ)) 0 0)) := by
      intro A hA
      obtain ⟨α, hα⟩ := hrep A hA
      rw [referenceSecondDeriv_congr_right hL hα, weightedNorm_congr S _ A _ _ hα,
        ← dotProduct_secondDerivMatrix_mulVec hT]
      exact hb α
    exact hE (fun z => -δ * (cellSupDist z y : ℝ)) 0 0 (Or.inr (Or.inl rfl))
      (fun z z' => abs_sub_neg_mul_cellSupDist_le δ hδ.le y z z') (toChart (realCombination e x))
      (fun A => referenceSecondDeriv a S (referenceFieldChain S V) V (toChart (realCombination e x)) A) β hβ
      (mem_gaugeSliceSubmodule.1 (hlin x)) (fun _ _ => rfl) hb'
  have han : ∀ ζ ∈ Ω, ∀ t, complexifiedSeminorm (fun x : Fin m → ℝ =>
      supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t ≤ r →
      AnalyticAt ℂ (spanTotal a S V e b X) (t, ζ) := by
    intro ζ hζ t ht
    exact hB.analytic m _ t ζ (by rw [hYc]; exact ht.trans hrc) (hζc ζ hζ)
  have hk0 : ∀ ζ : Fin k → ℂ, 0 ≤ ∑ l, ‖ζ l‖ := fun ζ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsq : s ^ 2 ≤ s := by nlinarith
  have hεr : ∀ ζ ∈ Ω, 8 * Ca₄ * ((Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖) ≤ r := by
    intro ζ hζ
    have h1 : Ct * s + CT * s ^ 2 ≤ (Ct + CT) * s := by nlinarith
    have h2 : C * ∑ l, ‖ζ l‖ ≤ C * r' := mul_le_mul_of_nonneg_left (le_of_lt hζ) hC
    have h3 : 8 * Ca₄ * ((Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖) ≤ 8 * Ca₄ * ((Ct + CT) * s + C * r') :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    nlinarith
  have hκ : ∀ ζ ∈ Ω, 4 * Ca₄ * C * (2 * r + ∑ l, ‖ζ l‖) ≤ 1 := by
    intro ζ hζ
    have h1 : 2 * r + ∑ l, ‖ζ l‖ ≤ 3 * r := by
      have := (le_of_lt hζ).trans hr'r
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 * Ca₄ * C)
    nlinarith
  have hsz : ∀ ζ ∈ Ω, 0 ≤ ∑ l, ‖ζ l‖ ∧ 0 ≤ (Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖ ∧
      8 * Ca₄ * ((Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖) ≤ r ∧
      4 * Ca₄ * C * (2 * r + ∑ l, ‖ζ l‖) ≤ 1 := fun ζ hζ =>
    ⟨hk0 ζ, add_nonneg (by positivity) (mul_nonneg hC (hk0 ζ)), hεr ζ hζ, hκ ζ hζ⟩
  have hsrc : ∀ ζ ∈ Ω, ∀ (y : F.Cell) (α : Fin m → ℝ),
      ‖directionPairing (spanGradient a S V e b X (0, ζ)) α‖ ≤ ((Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖) *
        weightedNorm S (referenceFieldChain S V) (toChart (realCombination e α))
          (invertedWeights (decayWeights F δ 0 0 y)) := by
    intro ζ hζ y α
    have hd : DifferentiableAt ℂ (spanTotal a S V e b X) (0, ζ) :=
      (hB.analytic m _ 0 ζ (by rw [complexSpan_zero]; exact hsup0) (hζc ζ hζ)).differentiableAt
    rw [← complexFirstVariation_complexSpan_eq_pairing hd, complexSpan_zero]
    have h1 := norm_complexFirstVariation_zero_le (b := b) (X := X) hL hδ.le hc₁ hT hB hc0 hreg
      (toChart (realCombination e α)) y
    have h2 := norm_complexFirstVariation_twist_sub_le hL.pos hδ.le hB hC hsup0 (hζc ζ hζ) hc0
      (toChart (realCombination e α)) y
    have h3 := norm_add_le
      (complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexTwistedTop b X ζ V)
          (toChart (realCombination e α)) -
        complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexTwistedTop b X 0 V)
          (toChart (realCombination e α)))
      (complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexTwistedTop b X 0 V)
        (toChart (realCombination e α)))
    rw [sub_add_cancel] at h3
    rw [add_mul]
    linarith
  have hlip : ∀ ζ ∈ Ω, ∀ t t', complexifiedSeminorm (fun x : Fin m → ℝ =>
        supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t ≤ r →
      complexifiedSeminorm (fun x : Fin m → ℝ =>
        supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t' ≤ r →
      ∀ (y : F.Cell) (α : Fin m → ℝ),
      ‖directionPairing (spanGradient a S V e b X (t, ζ) - spanGradient a S V e b X (t', ζ)) α -
          matrixFormPairing (secondDerivMatrix a S V e) (t - t') α‖ ≤
        C * (complexifiedSeminorm (fun x : Fin m → ℝ =>
              supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t +
            complexifiedSeminorm (fun x : Fin m → ℝ =>
              supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t' +
            ∑ l, ‖ζ l‖) *
          complexifiedSeminorm (fun x : Fin m → ℝ =>
            weightedNorm S (referenceFieldChain S V) (toChart (realCombination e x)) (decayWeights F δ 0 0 y))
            (t - t') *
          weightedNorm S (referenceFieldChain S V) (toChart (realCombination e α))
            (invertedWeights (decayWeights F δ 0 0 y)) := by
    intro ζ hζ t t' ht ht' y α
    have hd := (han ζ hζ t ht).differentiableAt
    have hd' := (han ζ hζ t' ht').differentiableAt
    rw [directionPairing_sub, ← complexFirstVariation_complexSpan_eq_pairing hd,
      ← complexFirstVariation_complexSpan_eq_pairing hd', matrixFormPairing_secondDerivMatrix_eq hT,
      ← complexChartSub_complexSpan, ← hYc, ← hYc, ← hpc, ← complexChartSub_complexSpan]
    exact hB.lipschitz _ _ ζ (by rw [hYc]; exact ht.trans hrc) (by rw [hYc]; exact ht'.trans hrc) (hζc ζ hζ)
      (fun z => -δ * (cellSupDist z y : ℝ)) 0 0 (Or.inr (Or.inl rfl))
      (fun z z' => abs_sub_neg_mul_cellSupDist_le δ hδ.le y z z') _
  obtain ⟨w, hw⟩ := hZ m k F.Cell
    (fun y x => weightedNorm S (referenceFieldChain S V) (toChart (realCombination e x)) (decayWeights F δ 0 0 y))
    (fun y α => weightedNorm S (referenceFieldChain S V) (toChart (realCombination e α))
      (invertedWeights (decayWeights F δ 0 0 y)))
    (fun x => supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x)))
    (secondDerivMatrix a S V e)
    (spanGradient a S V e b X) Ω (fun ζ => ∑ l, ‖ζ l‖) (fun ζ => (Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖)
    Ca₄ C r ⟨0⟩ hYn hYdef
    (fun y => isRealCoordSeminorm_weightedNorm e _ _ (fun j x => (decayWeights_pos hL.pos δ 0 0 y j x).le))
    (fun y α => weightedNorm_nonneg _ _ _ _)
    (fun y x => weightedNorm_decay_le_supWeightedNorm S hL.pos δ hδ.le _ _ y)
    (fun x β _ h => supWeightedNorm_le S δ _ _ β h) hCa₄ hC hr hΩ hco
    (fun ζ hζ t ht => analyticAt_spanGradient (han ζ hζ t ht)) hsz hsrc hlip
  have hread : ∀ x : Fin m → ℝ,
      chartValues S (toChart (realCombination e x)) = ∑ i, x i • chartValues S (toChart (e i)) := by
    intro x
    refine Prod.ext ?_ ?_
    · funext c'
      simp [chartValues, toChart, realCombination, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    · funext j c'
      simp [chartValues, toChart, realCombination, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  have hwR : ∀ ζ ∈ Ω,
      complexSupWeightedNorm S δ (referenceFieldChain S V) (complexSpan (fun i => toChart (e i)) (w ζ)) ≤ r := by
    intro ζ hζ
    rw [hYc]
    have h1 := (hw ζ hζ).2.2.1
    have h2 := hεr ζ hζ
    have h3 : 0 ≤ (Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖ := (hsz ζ hζ).2.1
    nlinarith
  have hdet : IsUnit (secondDerivMatrix a S V e).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    apply hYdef
    refine le_antisymm (supWeightedNorm_le S δ _ _ 0 fun y => ?_) (supWeightedNorm_nonneg _ _ _ _)
    have := hco y v 0 le_rfl (fun α => by
      rw [Matrix.dotProduct_mulVec, hvM]
      simp)
    simpa using this
  refine ⟨fun ζ => complexSpan (fun i => toChart (e i)) (w ζ), ?_⟩
  exact {
    solve := fun l hadd hsm hsame => by
      have hl0 : l (zeroChart F) = 0 := by
        have h1 := hsm 0 (zeroChart F)
        have h2 : l (chartMove (zeroChart F) (zeroChart F) 0) = l (zeroChart F) :=
          hsame _ _ ⟨fun x _ => by simp [chartMove, zeroChart], fun j _ x _ => by simp [chartMove, zeroChart]⟩
        rw [h2] at h1
        simpa using h1
      have hll : ∀ α : Fin m → ℝ, l (toChart (realCombination e α)) = ∑ i, α i * l (toChart (e i)) := by
        intro α
        have key : ∀ u : Finset (Fin m),
            l (toChart (∑ i ∈ u, α i • e i)) = ∑ i ∈ u, α i * l (toChart (e i)) := by
          intro u
          induction u using Finset.induction_on with
          | empty =>
            simp only [Finset.sum_empty, toChart_zero]
            exact hl0
          | insert i u hi ih =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi, toChart_add]
            have e' : l (chartSum (toChart (α i • e i)) (toChart (∑ i ∈ u, α i • e i))) =
                l (toChart (α i • e i)) + l (toChart (∑ i ∈ u, α i • e i)) := hadd _ _
            rw [e', ih, toChart_smul, hsm]
        exact key Finset.univ
      set y : Fin m → ℝ := fun j => l (toChart (e j)) with hy
      set x : Fin m → ℝ := y ᵥ* (secondDerivMatrix a S V e)⁻¹ with hx
      have hxM : x ᵥ* secondDerivMatrix a S V e = y := by
        rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      refine ⟨toChart (realCombination e x), mem_gaugeSliceSubmodule.1 (hlin x), fun A hA => ?_⟩
      obtain ⟨α, hα⟩ := hrep A hA
      rw [referenceSecondDeriv_congr_right hL hα, hsame _ _ hα, ← dotProduct_secondDerivMatrix_mulVec hT,
        Matrix.dotProduct_mulVec, hxM, hll]
      simp only [dotProduct, hy]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    mem_slice := fun ζ _ => by
      rw [complexSpan_eq]
      exact ⟨mem_gaugeSliceSubmodule.1 (hlin _), mem_gaugeSliceSubmodule.1 (hlin _)⟩
    norm_le := fun ζ hζ => by
      rw [hYc]
      refine (hw ζ hζ).2.2.1.trans ?_
      have h1 : Ct * s + CT * s ^ 2 ≤ (Ct + CT) * s := by nlinarith
      have hk := hk0 ζ
      have h2 : 4 * Ca₄ * ((Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖) ≤
          4 * Ca₄ * (Ct + CT + C + 1) * (s + ∑ l, ‖ζ l‖) := by
        have h3 : (Ct * s + CT * s ^ 2) + C * ∑ l, ‖ζ l‖ ≤ (Ct + CT + C + 1) * (s + ∑ l, ‖ζ l‖) := by
          nlinarith [mul_nonneg hCt hk, mul_nonneg hCT hk, mul_nonneg hC hs.le]
        have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * Ca₄)
        linarith
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right hC₀ (by positivity)
    small := hwR
    critical := fun ζ hζ A hA => by
      obtain ⟨α, hα⟩ := hrep A hA
      have hd := (han ζ hζ (w ζ) (by rw [← hYc]; exact hwR ζ hζ)).differentiableAt
      rw [complexFirstVariation_congr_direction hL _ _ _ hα, complexFirstVariation_complexSpan_eq_pairing hd,
        (hw ζ hζ).2.1, directionPairing_zero]
    analytic := fun ζ hζ ℓ => by
      have hwa := (hw ζ hζ).1
      have e' : (fun ζ' => (ℓ (chartValues S (complexSpan (fun i => toChart (e i)) (w ζ')).re) : ℂ) +
          Complex.I * (ℓ (chartValues S (complexSpan (fun i => toChart (e i)) (w ζ')).im) : ℂ)) =
          fun ζ' => ∑ i, w ζ' i * ((ℓ (chartValues S (toChart (e i))) : ℝ) : ℂ) := by
        funext ζ'
        rw [complexSpan_eq]
        simp only [hread, map_sum, map_smul, smul_eq_mul]
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_rhs => rw [← Complex.re_add_im (w ζ' i)]
        simp only [realParts, imagParts]
        ring
      rw [e']
      refine Finset.analyticAt_fun_sum _ fun i _ => ?_
      exact ((analyticAt_pi_iff.1 hwa) i).mul analyticAt_const
    real := fun ζ hζ => by
      have hζΩ : (fun l => (ζ l : ℂ)) ∈ Ω := by
        show ∑ l, ‖((ζ l : ℝ) : ℂ)‖ < r'
        simpa [Complex.norm_real] using hζ
      have him := (hw _ hζΩ).2.2.2 (by
        intro t ht htr
        funext j
        have hd := (han _ hζΩ t htr).differentiableAt
        have hW : complexSupWeightedNorm S δ (referenceFieldChain S V)
            (complexSpan (fun i => toChart (e i)) t) ≤ c := by
          rw [hYc]
          exact htr.trans hrc
        have e1 := complexFirstVariation_complexSpan_eq_pairing hd (Pi.single j 1)
        have e2 : directionPairing (spanGradient a S V e b X (t, fun l => (ζ l : ℂ))) (Pi.single j 1) =
            spanGradient a S V e b X (t, fun l => (ζ l : ℂ)) j := by
          simp only [directionPairing, Pi.single_apply]
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hi
            simp [hi]
          · simp
        have hl := differentiableAt_complexChartMove_line hB (ζ := fun l => (ζ l : ℂ)) hW (hζc _ hζΩ)
          (toChart (realCombination e (Pi.single j 1)))
        rw [complexTwistedTop_ofReal] at hl e1
        rw [complexSpan_of_imagParts_eq_zero e t ht] at hl e1 hW
        have hU : supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e (realParts t))) < c₁ := by
          have h1 : supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e (realParts t))) ≤
              complexifiedSeminorm (fun x : Fin m → ℝ =>
                supWeightedNorm S δ (referenceFieldChain S V) (toChart (realCombination e x))) t :=
            le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _)
          exact lt_of_le_of_lt (h1.trans htr) hrc₁
        have hr2 := complexFirstVariation_real a (referenceFieldChain S V)
          (toChart (realCombination e (realParts t)))
          (toChart (realCombination e (Pi.single j 1))) (rotatedField (bondSpread b X ζ) V) hl
          (eventually_chartIsRegular_chartMove hL.pos hδ.le hreg _ hU)
        have e3 := hr2.2
        rw [e1, e2] at e3
        exact e3)
      have e' : (complexSpan (fun i => toChart (e i)) (w fun l => (ζ l : ℂ))).im = zeroChart F := by
        rw [complexSpan_eq]
        show toChart (realCombination e (imagParts (w fun l => (ζ l : ℂ)))) = zeroChart F
        rw [him, realCombination_zero]
        rfl
      rw [e']
      exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    stable := fun φ θ' p hθ' hφ ζ W W' β hζ hβ h1 h2 h3 h4 hW hW' hf => by
      have hnn : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W +
          complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖ :=
        add_nonneg (add_nonneg (add_nonneg (supWeightedNorm_nonneg _ _ _ _) (supWeightedNorm_nonneg _ _ _ _))
          (add_nonneg (supWeightedNorm_nonneg _ _ _ _) (supWeightedNorm_nonneg _ _ _ _))) (hk0 ζ)
      have hk : 4 * Ca₄ * C * (complexSupWeightedNorm S δ (referenceFieldChain S V) W +
          complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖) ≤ 1 := by
        have h5 := hκ ζ hζ
        have h6 : complexSupWeightedNorm S δ (referenceFieldChain S V) W +
            complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖ ≤ 2 * r + ∑ l, ‖ζ l‖ := by
          linarith
        exact (mul_le_mul_of_nonneg_left h6 (by positivity)).trans h5
      refine (complexWeightedNorm_sub_le_of_variation hE hCa₄ hB hC φ θ' p hθ' hφ ζ W W' β hβ h1 h2 h3 h4
        (hW.trans hrc) (hW'.trans hrc) (hζc ζ hζ) hk hnn hf).trans ?_
      have h7 : 4 * Ca₄ ≤ C₀ := by
        have : 4 * Ca₄ * 1 ≤ 4 * Ca₄ * (Ct + CT + C + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_right h7 hβ }
end Pair
theorem complexCriticalFamiliesStatement_holds (hZ : HolomorphicZeroOfCoerciveFamilyProperty)
    (hT : actionTaylorBoundStatement) (hB : rotatedTopTaylorBoundsStatement)
    (hR : smallChartIsRegularStatement) :
    complexCriticalFamiliesStatement := by
  intro a θ δ Ca₄ ha hθ hθ8 hδ hδ8 hCa₄ hE
  obtain ⟨L₁, hE⟩ := hE
  obtain ⟨Ct, L₄, hCt, hT'⟩ := hT a θ δ ha hθ.le hθ8 hδ hδ8
  obtain ⟨Ca, hCa, L₂, hB'⟩ := hB a θ δ ha hθ.le hθ8 hδ hδ8
  obtain ⟨L₃, hR'⟩ := hR
  refine ⟨Ca, hCa, max (max L₁ L₂) (max L₃ L₄), fun L hL hLge => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLge)
  have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hLge)
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLge)
  have hL4 : L₄ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLge)
  obtain ⟨cE, hcE, hE'⟩ := hE L hL hL1
  obtain ⟨cT, CT, hcT, hCT, hTL⟩ := hT' L hL hL4
  obtain ⟨cB, CB, hcB, hCB, hBL⟩ := hB' L hL hL2
  obtain ⟨c₁, hc₁, hRL⟩ := hR' L hL hL3 δ hδ hδ8
  set c₀ : ℝ := min (min cB (c₁ / 2)) (1 / (16 * Ca₄ * CB)) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (lt_min hcB (by positivity)) (by positivity)
  set C₀ : ℝ := 4 * Ca₄ * (Ct + CT + CB + 1) + CB with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  refine ⟨c₀, C₀, hc₀0, hC₀0, fun r hr hrc => ?_⟩
  have hrB : r ≤ cB := hrc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ : r ≤ c₁ / 2 := hrc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr16 : r ≤ 1 / (16 * Ca₄ * CB) := hrc.trans (min_le_right _ _)
  set r' : ℝ := min r (r / (16 * Ca₄ * CB)) with hr'd
  have hr'0 : 0 < r' := lt_min hr (by positivity)
  set s₀ : ℝ := min (min cE cT) (min (min cB c₁) (min 1 (r / (16 * Ca₄ * (Ct + CT))))) with hs₀
  have hs₀0 : 0 < s₀ := lt_min (lt_min hcE hcT) (lt_min (lt_min hcB hc₁) (lt_min one_pos (by positivity)))
  refine ⟨r', s₀, hr'0, min_le_left _ _, hs₀0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsle hcold k b X hX
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hsE : s ≤ cE := hsle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsT : s ≤ cT := hsle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsB : s ≤ cB := hsle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs₁ : s ≤ c₁ := hsle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hs1 : s ≤ 1 := hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsr : s ≤ r / (16 * Ca₄ * (Ct + CT)) :=
    hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hBp := hBL F m S hFL hamb hm hreg s V hs hsB hcold k b X hX
  have hTp := hTL F m S hFL hamb hm hreg s V hs hsT hcold
  have hEp := hE' F m S hFL hamb hm hreg s V hs hsE hcold
  refine ⟨twistedTotalBounds_mono hBp ((min_le_left _ _).trans (min_le_left _ _))
    (by rw [hC₀]; have : 0 < 4 * Ca₄ * (Ct + CT + CB + 1) := by positivity
        linarith) hCB.le hs.le, ?_⟩
  refine exists_isComplexCriticalFamily (c₁ := c₁) (c := cB) hZ hLF hδ hCa₄ hCt.le hCT.le hCB.le hs hs1 hr hr'0
    (min_le_left _ _) hrB (by linarith) (by rw [hC₀]; linarith) hEp hTp hBp
    (fun U hU => (hRL F m S hFL hamb hm hreg s V hs hs₁ hcold U hU).1) ?_ ?_ ?_
  · have h0 : 0 < 16 * Ca₄ * CB := by positivity
    have := mul_le_mul_of_nonneg_left hr16 h0.le
    rwa [mul_one_div_cancel h0.ne'] at this
  · have h0 : 0 < 16 * Ca₄ * (Ct + CT) := by positivity
    rw [le_div_iff₀ h0] at hsr
    linarith
  · have h0 : 0 < 16 * Ca₄ * CB := by positivity
    have h1 : r' ≤ r / (16 * Ca₄ * CB) := min_le_right _ _
    rw [le_div_iff₀ h0] at h1
    linarith
end YangMills.Construction.ComplexCriticalFamilies
end
