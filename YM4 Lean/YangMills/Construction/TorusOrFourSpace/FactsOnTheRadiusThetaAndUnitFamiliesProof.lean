import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.TorusOrFourSpace.FactsOnTheRadiusThetaAndUnitFamilies
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open YangMills.Construction.PeriodicSpace.Kind YangMills.Construction.TorusMetric
namespace RadiusThetaFacts
private theorem one_le_side (D : Params) : (1 : ℝ) ≤ D.side := by
  have hL : (1 : ℝ) ≤ (D.L : ℝ) := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  have h1 : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := one_le_pow₀ hL
  show (1 : ℝ) ≤ 2 * (D.L : ℝ) ^ (D.m : ℕ)
  linarith
private theorem side_pos (D : Params) : 0 < D.side := lt_of_lt_of_le one_pos (one_le_side D)
private theorem lipConstQ_nonneg (D : Params) (u : Pt D torus → ℝ) :
    0 ≤ lipConstQ D torus u :=
  Real.sInf_nonneg fun _ h => h.1
private theorem euclidNormVec_smul {c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
private theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (μ : Fin 4) (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.partialDerivR4_eq_fderiv <;> assumption
private theorem continuous_partialDerivR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (μ : Fin 4) : Continuous (TestFunctions.partialDerivR4 μ f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h : TestFunctions.partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ (1 : ℝ)) :=
    funext (partialDerivR4_eq_fderiv hd μ)
  rw [h]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
private theorem partialDerivR4_periodic {f : (Fin 4 → ℝ) → ℝ}
    (hp : ∀ x, ∀ k : Fin 4 → ℤ, f (x + fun μ => (k μ : ℝ)) = f x) (μ : Fin 4) (x : Fin 4 → ℝ)
    (k : Fin 4 → ℤ) :
    TestFunctions.partialDerivR4 μ f (x + fun ν => (k ν : ℝ)) =
      TestFunctions.partialDerivR4 μ f x := by
  unfold TestFunctions.partialDerivR4
  congr 1
  funext t
  rw [show x + (fun ν => (k ν : ℝ)) + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) =
    (x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) + fun ν => (k ν : ℝ) by abel]
  exact hp _ k
private theorem exists_grad_bound {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x, ∀ k : Fin 4 → ℤ, f (x + fun μ => (k μ : ℝ)) = f x) :
    ∃ K : ℝ, ∀ x, euclidNormVec (fun μ => TestFunctions.partialDerivR4 μ f x) ≤ K := by
  have hg : Continuous fun x => euclidNormVec fun μ => TestFunctions.partialDerivR4 μ f x := by
    have h1 : Continuous fun x => ∑ μ, (TestFunctions.partialDerivR4 μ f x) ^ 2 :=
      continuous_finsetSum _ fun μ _ => (continuous_partialDerivR4 hf μ).pow 2
    exact h1.sqrt
  have hc : IsCompact (Set.Icc (0 : Fin 4 → ℝ) 1) := isCompact_Icc
  obtain ⟨K, hK⟩ := hc.bddAbove_image hg.continuousOn
  refine ⟨K, fun x => ?_⟩
  have hx : x = (fun μ => Int.fract (x μ)) + fun μ => ((⌊x μ⌋ : ℤ) : ℝ) := by
    funext μ
    simp [Int.fract_add_floor]
  have hmem : (fun μ => Int.fract (x μ)) ∈ Set.Icc (0 : Fin 4 → ℝ) 1 :=
    ⟨fun μ => Int.fract_nonneg _, fun μ => (Int.fract_lt_one _).le⟩
  have hval : (fun μ => TestFunctions.partialDerivR4 μ f x) =
      fun μ => TestFunctions.partialDerivR4 μ f (fun ν => Int.fract (x ν)) := by
    funext μ
    conv_lhs => rw [hx]
    exact partialDerivR4_periodic hp μ _ fun ν => ⌊x ν⌋
  rw [hval]
  exact hK ⟨_, hmem, rfl⟩
private theorem gradSupBound_ne_top {B : Type} [Fintype B] {θ : RadiusRatio}
    {X : B → (Fin 4 → ℝ) → ℝ} (hX : IsPeriodicPartition θ X) : gradSupBound X ≠ ⊤ := by
  choose K hK using fun b => exists_grad_bound (hX.contDiff b) (hX.periodic b)
  obtain ⟨K', hK'⟩ := (Set.finite_range K).bddAbove
  have h : gradSupBound X ≤ ENNReal.ofReal K' :=
    iSup₂_le fun b x => ENNReal.ofReal_le_ofReal ((hK b x).trans (hK' ⟨b, rfl⟩))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
private theorem partitionConstant_ne_top {B : Type} [Fintype B] (M : ℝ)
    {X : B → (Fin 4 → ℝ) → ℝ} (h : gradSupBound X ≠ ⊤) : partitionConstant M X ≠ ⊤ := by
  unfold partitionConstant
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) h⟩)
private theorem ofReal_sum_le {B : Type} [Fintype B] {M : ℝ} (hM : 0 ≤ M) {c : B → ℝ}
    (hc : ∀ b, 0 ≤ c b) {C : ℝ≥0∞} (h : ∀ b, ENNReal.ofReal (c b) ≤ C) :
    ENNReal.ofReal (∑ b, (1 + 40 * M * c b)) ≤
      (Fintype.card B : ℝ≥0∞) * (1 + 40 * ENNReal.ofReal M * C) := by
  have hn : ∀ b, 0 ≤ 40 * M * c b := fun b => mul_nonneg (mul_nonneg (by norm_num) hM) (hc b)
  rw [ENNReal.ofReal_sum_of_nonneg fun b _ => add_nonneg zero_le_one (hn b)]
  have hterm : ∀ b, ENNReal.ofReal (1 + 40 * M * c b) ≤ 1 + 40 * ENNReal.ofReal M * C := by
    intro b
    rw [ENNReal.ofReal_add zero_le_one (hn b), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hM), ENNReal.ofReal_mul (by norm_num)]
    have h40 : ENNReal.ofReal 40 = 40 := by simp
    rw [h40]
    gcongr
    exact h b
  calc ∑ b, ENNReal.ofReal (1 + 40 * M * c b)
      ≤ ∑ _b : B, (1 + 40 * ENNReal.ofReal M * C) := Finset.sum_le_sum fun b _ => hterm b
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
private theorem mem_periodGroup_iff (D : Params) (x : Fin 4 → ℝ) :
    x ∈ periodGroup D torus ↔ ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (n μ : ℝ) * D.side :=
  Iff.rfl
private theorem side_smul_int_mem (D : Params) (n : Fin 4 → ℤ) :
    D.side • (fun μ => (n μ : ℝ)) ∈ periodGroup D torus :=
  (mem_periodGroup_iff D _).2 ⟨n, fun μ => by simp [mul_comm]⟩
private theorem apply_inv_side_smul_eq (D : Params) {f : (Fin 4 → ℝ) → ℝ}
    (hp : ∀ x, ∀ k : Fin 4 → ℤ, f (x + fun μ => (k μ : ℝ)) = f x) {x x' : Fin 4 → ℝ}
    (h : x - x' ∈ periodGroup D torus) : f (D.side⁻¹ • x) = f (D.side⁻¹ • x') := by
  obtain ⟨n, hn⟩ := (mem_periodGroup_iff D _).1 h
  have hs : D.side ≠ 0 := (side_pos D).ne'
  have hx : D.side⁻¹ • x = D.side⁻¹ • x' + fun μ => (n μ : ℝ) := by
    funext μ
    have h1 : x μ - x' μ = (n μ : ℝ) * D.side := hn μ
    have h2 : x μ = x' μ + (n μ : ℝ) * D.side := by linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2]
    field_simp
  rw [hx, hp]
private theorem existsUnique_torusRescaling (hW : WellPosedness.WellPosed)
    (D : Params) {f : (Fin 4 → ℝ) → ℝ}
    (hp : ∀ x, ∀ k : Fin 4 → ℤ, f (x + fun μ => (k μ : ℝ)) = f x) :
    ∃! χ : Pt D torus → ℝ, IsTorusRescaling D f χ := by
  obtain ⟨⟨-, hsurj, -⟩, -, hdiff, -⟩ := hW D torus
  refine ⟨fun y => f (D.side⁻¹ • Function.surjInv hsurj y), fun x => ?_, fun χ' hχ' => ?_⟩
  · exact apply_inv_side_smul_eq D hp
      ((hdiff _ _).1 ⟨quotMap D torus x, Function.surjInv_eq hsurj _, rfl⟩)
  · funext y
    have hx := hχ' (Function.surjInv hsurj y)
    rw [Function.surjInv_eq hsurj] at hx
    exact hx
private theorem quotDist_le (hW : WellPosedness.WellPosed) (D : Params)
    (x z : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    quotDist D torus (quotMap D torus x) (quotMap D torus (D.side • z)) ≤
      D.side * euclidNormVec (D.side⁻¹ • x - z - fun μ => (k μ : ℝ)) := by
  obtain ⟨-, -, -, -, -, -, hleast, -⟩ := hW D torus
  have hmem : euclidNormVec (x - D.side • z - D.side • fun μ => (k μ : ℝ)) ∈
      WellPosedness.translateNorms D torus x (D.side • z) :=
    ⟨_, side_smul_int_mem D k, rfl⟩
  refine ((hleast x (D.side • z)).2 hmem).trans_eq ?_
  rw [← euclidNormVec_smul (side_pos D).le]
  congr 1
  have hs : D.side ≠ 0 := (side_pos D).ne'
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
private theorem exists_quotDist_eq (hW : WellPosedness.WellPosed) (D : Params)
    (x x' : Fin 4 → ℝ) :
    ∃ n : Fin 4 → ℤ, quotDist D torus (quotMap D torus x) (quotMap D torus x') =
      euclidNormVec (x - x' - D.side • fun μ => (n μ : ℝ)) := by
  obtain ⟨-, -, -, -, -, -, hleast, -⟩ := hW D torus
  obtain ⟨k, hk, heq⟩ := (hleast x x').1
  obtain ⟨n, hn⟩ := (mem_periodGroup_iff D _).1 hk
  refine ⟨n, heq.trans ?_⟩
  congr 2
  funext μ
  simp [hn μ, mul_comm]
private theorem quotDist_le_of_mem_supportQ (hQ : QuotientCompactC1.Claim)
    (D : Params) {u : Pt D torus → ℝ} {c : Pt D torus} {ρ : ℝ}
    (h : ∀ y, u y ≠ 0 → quotDist D torus y c ≤ ρ) :
    ∀ y ∈ supportQ D torus u, quotDist D torus y c ≤ ρ := by
  obtain ⟨⟨-, -, -, htri, -⟩, -⟩ := hQ D torus
  intro p hp
  have hp' : ∀ r : ℝ, 0 < r → ∃ y ∈ {y | u y ≠ 0}, quotDist D torus p y < r := hp
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y, hy, hd⟩ := hp' ε hε
  have h1 := htri p y c
  have h2 := h y hy
  linarith
private theorem partialDerivR4_comp_smul (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 μ (fun v => f (c • v)) x =
      c * TestFunctions.partialDerivR4 μ f (c • x) := by
  unfold TestFunctions.partialDerivR4
  have h : (fun t : ℝ => f (c • (x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)))) =
      fun t => (fun s : ℝ => f (c • x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))) (c * t) := by
    funext t
    simp only [smul_add, smul_smul]
  rw [h]
  have h2 := deriv_comp_mul_left
    (f := fun s : ℝ => f (c • x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))) (c := c) (x := 0)
  simpa using h2
private theorem lipConstQ_le (hW : WellPosedness.WellPosed)
    (hP : TorusBallCoversAndPartitionsOfUnity) (D : Params)
    {f : (Fin 4 → ℝ) → ℝ} {χ : Pt D torus → ℝ} (hsm : χ ∈ smoothSet D torus)
    (hχ : IsTorusRescaling D f χ) :
    ENNReal.ofReal (lipConstQ D torus χ) ≤
      (⨆ x, ENNReal.ofReal (euclidNormVec fun μ => TestFunctions.partialDerivR4 μ f x)) /
        ENNReal.ofReal D.side := by
  obtain ⟨⟨-, hsurj, -⟩, -, -, -, -, -, -, -, -, hpart, -⟩ := hW D torus
  obtain ⟨hC1, -, -, -, hlip⟩ := (hP D 1 one_pos).2.2 χ hsm
  rw [hlip]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have hcomp : χ ∘ quotMap D torus = fun v => f (D.side⁻¹ • v) := funext hχ
  have hgr : gradVec D torus χ (quotMap D torus x) =
      D.side⁻¹ • fun μ => TestFunctions.partialDerivR4 μ f (D.side⁻¹ • x) := by
    funext μ
    have h2 := congrFun ((hpart χ hC1).2 μ).2.2 x
    rw [hcomp, partialDerivR4_comp_smul] at h2
    exact h2
  rw [hgr, euclidNormVec_smul (inv_nonneg.2 (side_pos D).le), inv_mul_eq_div,
    ENNReal.ofReal_div_of_pos (side_pos D)]
  exact ENNReal.div_le_div_right
    (le_iSup (fun x => ENNReal.ofReal (euclidNormVec fun μ => TestFunctions.partialDerivR4 μ f x))
      (D.side⁻¹ • x)) _
private theorem thetaNumber_ge_one : ThetaNumberGeOne := by
  intro D θ P E
  cases E with
  | euclidean => exact le_refl (1 : ℝ)
  | torus =>
    have hne : Nonempty P.Idx := by
      by_contra h
      have h0 := P.subordinate.sum_eq_one 0
      rw [not_nonempty_iff] at h
      simp at h0
    obtain ⟨a⟩ := hne
    have hterm : ∀ b, 1 ≤ 1 + 40 * D.M * lipConstQ D torus (P.bump b) := fun b =>
      le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num)
        (zero_le_one.trans D.one_le_M)) (lipConstQ_nonneg D _))
    show (1 : ℝ) ≤ ∑ a, (1 + 40 * D.M * lipConstQ D torus (P.bump a))
    exact (hterm a).trans (Finset.single_le_sum
      (f := fun a => 1 + 40 * D.M * lipConstQ D torus (P.bump a))
      (fun b _ => zero_le_one.trans (hterm b)) (Finset.mem_univ a))
private theorem ballRadius_pos (D : Params) (θ : RadiusRatio) (E : Kind) :
    0 < ballRadius D θ E := by
  cases E with
  | euclidean => exact one_pos
  | torus => exact mul_pos θ.val_mem.1 (side_pos D)
private theorem effConst_finite : EffConstFinite := by
  refine ⟨fun D θ P E C n hn d R hd hR => ?_, fun D R hR => hR, fun D θ P C n _ d R _ hR => ?_⟩
  · show 0 ≤ effConst P E C n d R
    unfold effConst
    split_ifs with h
    · exact C.nonneg n hn d R hd hR
    · exact mul_nonneg (pow_nonneg (zero_le_one.trans (thetaNumber_ge_one D θ P E)) n)
        (C.nonneg n hn d _ hd (ballRadius_pos D θ E))
  · unfold effConst
    exact if_pos hR
private theorem radiusTheta_dependence : RadiusThetaDependence := by
  refine ⟨fun _ _ _ _ => rfl, fun D D' θ hL hm => ?_, fun _ _ _ _ _ _ => rfl,
    fun D θ θ' P P' e h => ?_⟩
  · show θ.val * PeriodicLattice.torusSide D.L D.m = θ.val * PeriodicLattice.torusSide D'.L D'.m
    rw [hL, hm]
  · show ∑ a, (1 + 40 * D.M * lipConstQ D torus (P.bump a)) =
      ∑ a, (1 + 40 * D.M * lipConstQ D torus (P'.bump a))
    exact Fintype.sum_equiv e _ _ fun a => by rw [h a]
private theorem partition_from_periodic (hW : WellPosedness.WellPosed)
    (hQ : QuotientCompactC1.Claim)
    (hP : TorusBallCoversAndPartitionsOfUnity) :
    PartitionFromUnitFamily := by
  intro D θ B _ X hX z θb hθb hsupp
  obtain ⟨⟨-, hsurj, -⟩, -⟩ := hW D torus
  have hC := gradSupBound_ne_top hX
  refine ⟨hC, partitionConstant_ne_top D.M hC,
    fun b => existsUnique_torusRescaling hW D (hX.periodic b), fun χ hχ => ?_⟩
  have hfar : ∀ b y, χ b y ≠ 0 →
      quotDist D torus y (scaledCenter D (z b)) ≤ θb b * D.side := by
    intro b y hy
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hχ b x] at hy
    obtain ⟨k, hk⟩ := hsupp b _ hy
    calc quotDist D torus (quotMap D torus x) (scaledCenter D (z b))
        ≤ D.side * euclidNormVec (D.side⁻¹ • x - z b - fun μ => (k μ : ℝ)) :=
          quotDist_le hW D x (z b) k
      _ ≤ D.side * θb b := mul_le_mul_of_nonneg_left hk (side_pos D).le
      _ = θb b * D.side := mul_comm _ _
  have hlt : ∀ b, θb b * D.side < ballRadius D θ torus := fun b =>
    mul_lt_mul_of_pos_right (hθb b).2 (side_pos D)
  have hsup : ∀ b, supportQ D torus (χ b) ⊆
      torusBall D (scaledCenter D (z b)) (ballRadius D θ torus) := fun b y hy =>
    lt_of_le_of_lt (quotDist_le_of_mem_supportQ hQ D (hfar b) y hy) (hlt b)
  have hsum : ∀ y, ∑ b, χ b y = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact (Finset.sum_congr rfl fun b _ => hχ b x).trans (hX.sum_eq_one _)
  have hcover : BallsCoverTorus D (fun b => scaledCenter D (z b))
      (ballRadius D θ torus) := by
    intro y
    have hex : ∃ b, χ b y ≠ 0 := by
      by_contra h
      push Not at h
      have h1 := hsum y
      simp [h] at h1
    obtain ⟨b, hb⟩ := hex
    exact ⟨b, lt_of_le_of_lt (hfar b y hb) (hlt b)⟩
  have hsm : ∀ b, χ b ∈ smoothSet D torus := by
    intro b
    have hcomp : χ b ∘ quotMap D torus = X b ∘ fun v => D.side⁻¹ • v := funext (hχ b)
    show ContDiff ℝ ∞ (χ b ∘ quotMap D torus)
    rw [hcomp]
    exact (hX.contDiff b).comp (contDiff_const_smul _)
  have hmem : ∀ b, χ b ∈ smoothUnitIntervalSet D torus := by
    intro b
    refine ⟨hsm b, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hχ b x]
    exact hX.mem_Icc b _
  have hpart : IsSubordinatePartitionOfUnity D (fun b => scaledCenter D (z b))
      (ballRadius D θ torus) χ := ⟨hmem, hsum, fun b => ⟨b, hsup b⟩⟩
  have hlip : ∀ b, ENNReal.ofReal (lipConstQ D torus (χ b)) ≤
      gradSupBound X / ENNReal.ofReal D.side := fun b =>
    (lipConstQ_le hW hP D (hsm b) (hχ b)).trans (ENNReal.div_le_div_right
      (le_iSup (fun b => ⨆ x, ENNReal.ofReal
        (euclidNormVec fun μ => TestFunctions.partialDerivR4 μ (X b) x)) b) _)
  have hdiv : gradSupBound X / ENNReal.ofReal D.side ≤ gradSupBound X := by
    refine ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' ?_)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_side D)
  have hM : 0 ≤ D.M := zero_le_one.trans D.one_le_M
  have hsumle : ENNReal.ofReal (∑ b, (1 + 40 * D.M * lipConstQ D torus (χ b))) ≤
      partitionConstant D.M X :=
    ofReal_sum_le hM (fun b => lipConstQ_nonneg D _) fun b => (hlip b).trans hdiv
  refine ⟨hcover, hpart, hsup, ?_, hlip, hdiv, hsumle, ?_⟩
  · have hcov' : BallsCoverTorus D
        (fun j : Fin (Fintype.card B) => scaledCenter D (z ((Fintype.equivFin B).symm j)))
        (ballRadius D θ torus) := by
      intro y
      obtain ⟨b, hb⟩ := hcover y
      refine ⟨Fintype.equivFin B b, ?_⟩
      simpa using hb
    have hpart' : IsSubordinatePartitionOfUnity D
        (fun j : Fin (Fintype.card B) => scaledCenter D (z ((Fintype.equivFin B).symm j)))
        (ballRadius D θ torus) χ := by
      refine ⟨hmem, hsum, fun b => ⟨Fintype.equivFin B b, ?_⟩⟩
      simpa using hsup b
    exact ⟨{ numBalls := Fintype.card B
             center := _
             cover := hcov'
             Idx := B
             fintypeIdx := inferInstance
             bump := χ
             subordinate := hpart' },
      (Fintype.equivFin B).symm, Equiv.refl B, fun _ => rfl, fun _ => rfl⟩
  · rintro P ⟨e, he⟩
    have heq : thetaNumber P torus =
        ∑ b, (1 + 40 * D.M * lipConstQ D torus (χ b)) :=
      Fintype.sum_equiv e _ _ fun a => by rw [he a]
    rw [heq]
    exact hsumle
private theorem exists_closedBall_of_compact (hQ : QuotientCompactC1.Claim)
    (D : Params) {S : Set (Pt D torus)} (hS : IsCompactQ D torus S) {c : Pt D torus}
    {r : ℝ} (hr : 0 < r) (h : ∀ y ∈ S, quotDist D torus y c < r) :
    ∃ t, 0 < t ∧ t < r ∧ ∀ y ∈ S, quotDist D torus y c ≤ t := by
  obtain ⟨⟨-, -, hsymm, htri, -⟩, -⟩ := hQ D torus
  let U : ℝ → Set (Pt D torus) := fun t => {y | quotDist D torus y c < t}
  have hopen : ∀ t, MetricNotions.IsOpenWrt (quotDist D torus) (U t) := by
    intro t y hy
    have hy' : quotDist D torus y c < t := hy
    refine ⟨t - quotDist D torus y c, sub_pos.2 hy', fun w hw => ?_⟩
    have h1 := htri w y c
    rw [hsymm w y] at h1
    show quotDist D torus w c < t
    linarith
  obtain ⟨𝒱, hsub, hfin, hcov⟩ := hS (U '' Set.Ioo (r / 2) r)
    (by rintro _ ⟨t, -, rfl⟩; exact hopen t)
    (by
      intro y hy
      have hy' := h y hy
      have hm : max (quotDist D torus y c) (r / 2) < r := max_lt hy' (by linarith)
      have hm1 := le_max_left (quotDist D torus y c) (r / 2)
      have hm2 := le_max_right (quotDist D torus y c) (r / 2)
      refine ⟨U ((max (quotDist D torus y c) (r / 2) + r) / 2),
        ⟨_, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
      show quotDist D torus y c < _
      linarith)
  have h1 : ∀ V ∈ 𝒱, ∃ t, t ∈ Set.Ioo (r / 2) r ∧ V = U t := fun V hV => by
    obtain ⟨t, ht, rfl⟩ := hsub hV
    exact ⟨t, ht, rfl⟩
  choose! τ hτ using h1
  rcases 𝒱.eq_empty_or_nonempty with rfl | hne
  · refine ⟨r / 2, by linarith, by linarith, fun y hy => ?_⟩
    simpa using hcov hy
  · obtain ⟨V₀, hV₀, hmax⟩ := Set.exists_max_image 𝒱 τ hfin hne
    have hpos := (hτ V₀ hV₀).1.1
    refine ⟨τ V₀, by linarith, (hτ V₀ hV₀).1.2, fun y hy => ?_⟩
    obtain ⟨V, hV, hyV⟩ := hcov hy
    rw [(hτ V hV).2] at hyV
    have hy' : quotDist D torus y c < τ V := hyV
    exact hy'.le.trans (hmax V hV)
private theorem periodicPartitions_exist (hW : WellPosedness.WellPosed)
    (hQ : QuotientCompactC1.Claim)
    (hP : TorusBallCoversAndPartitionsOfUnity) : PeriodicPartitionsExist := by
  intro θ
  let D : Params := ⟨13, ⟨⟨6, by norm_num⟩, le_refl _⟩, 1, 1, le_refl _⟩
  obtain ⟨⟨hadd, hsurj, hker⟩, -⟩ := hW D torus
  obtain ⟨⟨-, -, -, -, -⟩, -⟩ := hQ D torus
  have hs := side_pos D
  have hr : 0 < θ.val * D.side := mul_pos θ.val_mem.1 hs
  obtain ⟨⟨J, hJ, x, hx⟩, hb, hc⟩ := hP D _ hr
  obtain ⟨A, hA, hne, χ, hχ⟩ := hb J hJ x hx
  refine ⟨A, hA, fun a v => χ a (quotMap D torus (D.side • v)), ?_⟩
  refine ⟨hne, fun a => ?_, fun a v => (hχ.mem_unitInterval a).2 _, fun a v k => ?_,
    fun v => hχ.sum_eq_one _, fun a => ?_⟩
  · have h1 : ContDiff ℝ ∞ (χ a ∘ quotMap D torus) := (hχ.mem_unitInterval a).1
    exact h1.comp (contDiff_const_smul D.side)
  · have h0 : quotMap D torus (D.side • fun μ => (k μ : ℝ)) = 0 :=
      (hker _).2 (side_smul_int_mem D k)
    show χ a (quotMap D torus (D.side • (v + fun μ => (k μ : ℝ)))) = _
    rw [smul_add, hadd, h0, add_zero]
  · obtain ⟨j, hj⟩ := hχ.support_subset a
    obtain ⟨t, ht0, htr, ht⟩ := exists_closedBall_of_compact hQ D
      (hc (χ a) (hχ.mem_unitInterval a).1).2.1 hr (fun y hy => hj hy)
    obtain ⟨xt, hxt⟩ := hsurj (x j)
    have hinv : 0 ≤ D.side⁻¹ := inv_nonneg.2 hs.le
    refine ⟨D.side⁻¹ • xt, D.side⁻¹ * t, ⟨mul_pos (inv_pos.2 hs) ht0, ?_⟩, fun v hv => ?_⟩
    · rw [inv_mul_lt_iff₀ hs, mul_comm]
      exact htr
    · have hin : quotMap D torus (D.side • v) ∈ supportQ D torus (χ a) := by
        intro ρ hρ
        obtain ⟨⟨-, hz, -⟩, -⟩ := hQ D torus
        exact ⟨_, hv, by rw [(hz _ _).2 rfl]; exact hρ⟩
      have hd := ht _ hin
      obtain ⟨n, hn⟩ := exists_quotDist_eq hW D (D.side • v) xt
      rw [hxt] at hn
      rw [hn] at hd
      refine ⟨n, ?_⟩
      have heq : euclidNormVec (v - D.side⁻¹ • xt - fun μ => (n μ : ℝ)) =
          D.side⁻¹ * euclidNormVec (D.side • v - xt - D.side • fun μ => (n μ : ℝ)) := by
        rw [← euclidNormVec_smul hinv]
        congr 1
        funext μ
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hd hinv
theorem claim_holds (hW : WellPosedness.WellPosed)
    (hQ : QuotientCompactC1.Claim)
    (hP : TorusBallCoversAndPartitionsOfUnity) : Claim :=
  ⟨thetaNumber_ge_one, effConst_finite, radiusTheta_dependence,
    partition_from_periodic hW hQ hP, periodicPartitions_exist hW hQ hP⟩
end RadiusThetaFacts
end YangMills.Construction.PeriodicSpace
