import YangMills.Construction.Torus.AveragedSquareExpansion
import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocks
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansion
import YangMills.Construction.Torus.KernelCalculusOnTheLayers
import YangMills.Construction.Torus.LocalInverseOfTheAveragedSquare
import YangMills.Construction.Torus.NeumannExpansionOfAParametrix
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.InverseExpansion
theorem restrict_extendByZero {Y : Type*} (X : Set Y) (v : ↥X → ℝ) :
    LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y)
      (Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) v) = v := by
  funext x
  exact Subtype.val_injective.extend_apply v 0 x
theorem extendByZero_restrict {Y : Type*} (X : Set Y) (w : Y → ℝ) :
    Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y)
      (LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) w) = X.indicator w := by
  funext y
  by_cases hy : y ∈ X
  · rw [indicator_of_mem hy]
    exact Subtype.val_injective.extend_apply (fun x : ↥X => w x) 0 ⟨y, hy⟩
  · rw [indicator_of_notMem hy]
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨x, rfl⟩
    exact hy x.2
theorem isUnit_compression_of_cut_inverse {Y : Type*} (X : Set Y) (χ T E : Module.End ℝ (Y → ℝ))
    (hχ : ∀ w, χ w = X.indicator w) (hE : χ * E * χ = E) (h₁ : χ * T * χ * E = χ)
    (h₂ : E * (χ * T * χ) = χ) :
    IsUnit (LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) ∘ₗ T ∘ₗ
        Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) : Module.End ℝ (↥X → ℝ)) ∧
      (LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) ∘ₗ (χ * T * χ) ∘ₗ
        Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) : Module.End ℝ (↥X → ℝ)) =
      LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) ∘ₗ T ∘ₗ
        Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) ∧
      Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) ∘ₗ
        Ring.inverse (LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) ∘ₗ T ∘ₗ
          Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) : Module.End ℝ (↥X → ℝ)) ∘ₗ
        LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) = E := by
  set res := LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → Y) with hres
  set ex := Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → Y) with hex
  have re : ∀ v, res (ex v) = v := restrict_extendByZero X
  have er : ∀ w, ex (res w) = χ w := fun w => by rw [hχ]; exact extendByZero_restrict X w
  have χe : ∀ v, χ (ex v) = ex v := fun v => by rw [← er, re]
  have rχ : ∀ w, res (χ w) = res w := fun w => by rw [← er, re]
  have a₁ : ∀ w, χ (T (χ (E w))) = χ w := fun w => LinearMap.congr_fun h₁ w
  have a₂ : ∀ w, E (χ (T (χ w))) = χ w := fun w => LinearMap.congr_fun h₂ w
  have a₃ : ∀ w, χ (E (χ w)) = E w := fun w => LinearMap.congr_fun hE w
  let A : Module.End ℝ (↥X → ℝ) := res ∘ₗ T ∘ₗ ex
  let A' : Module.End ℝ (↥X → ℝ) := res ∘ₗ E ∘ₗ ex
  have hAA' : A * A' = 1 := by
    refine LinearMap.ext fun v => ?_
    change res (T (ex (res (E (ex v))))) = v
    rw [er, ← rχ, a₁, χe, re]
  have hA'A : A' * A = 1 := by
    refine LinearMap.ext fun v => ?_
    change res (E (ex (res (T (ex v))))) = v
    have := a₂ (ex v)
    rw [χe] at this
    rw [er, this, re]
  let u : (Module.End ℝ (↥X → ℝ))ˣ := ⟨A, A', hAA', hA'A⟩
  have hinv : Ring.inverse A = A' := Ring.inverse_unit u
  refine ⟨⟨u, rfl⟩, ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    change res (χ (T (χ (ex v)))) = res (T (ex v))
    rw [rχ, χe]
  · change ex ∘ₗ Ring.inverse A ∘ₗ res = E
    rw [hinv]
    refine LinearMap.ext fun w => ?_
    change ex (res (E (ex (res w)))) = E w
    rw [er, er, a₃]
theorem mul_approxInverse_eq_one_sub {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι] (T : A)
    (χ h Tl E : ι → A) (Rb : ι → ι → A) (hχh : ∀ i, χ i * h i = h i) (hhχ : ∀ i, h i * χ i = h i)
    (hinv : ∀ i, χ i * Tl i * χ i * E i = χ i) (hsum : ∑ i, h i ^ 2 = 1)
    (hd : ∀ i, Rb i i = (h i * (χ i * Tl i * χ i) - χ i * Tl i * χ i * h i) +
      χ i * (Tl i - T) * h i)
    (ho : ∀ i i', i ≠ i' → Rb i i' = (χ i' - 1) * h i ^ 2 * T * h i') :
    T * ∑ i, h i * E i * h i = 1 - ∑ i, ∑ i', Rb i i' * E i' * h i' := by
  have key : ∀ j, ∑ i, Rb i j = h j * (χ j * Tl j * χ j) - T * h j := by
    intro j
    have hz : (χ j - 1) * h j ^ 2 = 0 := by
      rw [pow_two, ← mul_assoc, sub_mul, hχh]
      simp
    have hrest : ∑ i ∈ Finset.univ.erase j, h i ^ 2 = 1 - h j ^ 2 := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      abel
    have hsplit : ∑ i ∈ Finset.univ.erase j, Rb i j =
        (χ j - 1) * (1 - h j ^ 2) * T * h j := by
      rw [← hrest, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => ho i j (Finset.ne_of_mem_erase hi)
    have hcut : χ j * Tl j * χ j * h j = χ j * Tl j * h j := by
      rw [mul_assoc, hχh]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hsplit, hd, hcut]
    have e : (χ j - 1) * (1 - h j ^ 2) * T * h j =
        (χ j - 1) * T * h j - ((χ j - 1) * h j ^ 2) * T * h j := by noncomm_ring
    rw [e, hz]
    noncomm_ring
  have term : ∀ j, T * (h j * E j * h j) = h j ^ 2 - ∑ i, Rb i j * E j * h j := by
    intro j
    have h₁ : ∑ i, Rb i j * E j * h j = (∑ i, Rb i j) * E j * h j := by
      rw [Finset.sum_mul, Finset.sum_mul]
    have h₂ : h j * (χ j * Tl j * χ j) * E j = h j * χ j := by
      rw [mul_assoc, hinv]
    rw [h₁, key, sub_mul, sub_mul, h₂, hhχ, pow_two]
    noncomm_ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => term j, Finset.sum_sub_distrib, hsum,
    Finset.sum_comm]
theorem sum_abs_chain_kernel_le {Y ι : Type*} [Fintype Y] [Fintype ι] (r : ι → ι → Y → Y → ℝ)
    (e : ι → Y → Y → ℝ) (g : ι → Y → ℝ) (X : ι → Set Y) (d : Y → Y → ℝ) (A U Cv cc ρ : ℝ)
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hCv : 0 ≤ Cv)
    (hr : ∀ b y z, z ∈ X b → ∑ a, |r a b y z| ≤ A * Real.exp (-(2 * ρ) * d y z))
    (he : ∀ b z y', |e b z y'| ≤ U * Real.exp (-(2 * ρ) * d z y'))
    (he₀ : ∀ b z y', z ∉ X b → e b z y' = 0)
    (hg : ∀ b y, 0 ≤ g b y) (hgs : ∀ y, ∑ b, g b y ≤ cc)
    (hconv : ∀ y y', ∑ z, Real.exp (-(2 * ρ) * d y z) * Real.exp (-(2 * ρ) * d z y') ≤
      Cv * Real.exp (-ρ * d y y')) (y y' : Y) :
    ∑ a, ∑ b, |(∑ z, r a b y z * e b z y') * g b y'| ≤
      cc * A * U * Cv * Real.exp (-ρ * d y y') := by
  rw [Finset.sum_comm]
  have one : ∀ b, ∑ a, |(∑ z, r a b y z * e b z y') * g b y'| ≤
      g b y' * (A * U * (Cv * Real.exp (-ρ * d y y'))) := by
    intro b
    have step : ∀ a, |(∑ z, r a b y z * e b z y') * g b y'| ≤
        g b y' * ∑ z, |r a b y z| * |e b z y'| := by
      intro a
      rw [abs_mul, abs_of_nonneg (hg b y'), mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (hg b y')
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun z _ => abs_mul _ _
    refine (Finset.sum_le_sum fun a _ => step a).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hg b y')
    have each : ∀ z, ∑ a, |r a b y z| * |e b z y'| ≤
        A * U * (Real.exp (-(2 * ρ) * d y z) * Real.exp (-(2 * ρ) * d z y')) := by
      intro z
      rw [← Finset.sum_mul]
      by_cases hz : z ∈ X b
      · calc (∑ a, |r a b y z|) * |e b z y'|
            ≤ (A * Real.exp (-(2 * ρ) * d y z)) * (U * Real.exp (-(2 * ρ) * d z y')) :=
              mul_le_mul (hr b y z hz) (he b z y') (abs_nonneg _)
                (mul_nonneg hA (Real.exp_pos _).le)
          _ = _ := by ring
      · rw [he₀ b z y' hz, abs_zero, mul_zero]
        positivity
    refine (Finset.sum_le_sum fun z _ => each z).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hconv y y') (mul_nonneg hA hU)
  refine (Finset.sum_le_sum fun b _ => one b).trans ?_
  rw [← Finset.sum_mul]
  have hnn : 0 ≤ A * U * (Cv * Real.exp (-ρ * d y y')) := by positivity
  calc (∑ b, g b y') * (A * U * (Cv * Real.exp (-ρ * d y y')))
      ≤ cc * (A * U * (Cv * Real.exp (-ρ * d y y'))) :=
        mul_le_mul_of_nonneg_right (hgs y') hnn
    _ = _ := by ring
section Operators
variable {D : TorusData} {B : SeparatedChain D}
variable {D : TorusData} {B : SeparatedChain D}
theorem kernel_mulOnLayer_mul (g : D.Space → ℝ) (K : Module.End ℝ B.LayerFn) (y y' : ↥B.allSites) :
    B.kernel (B.mulOnLayer g * K) y y' = g y * B.kernel K y y' := rfl
theorem kernel_mul_mulOnLayer (g : D.Space → ℝ) (K : Module.End ℝ B.LayerFn) (y y' : ↥B.allSites) :
    B.kernel (K * B.mulOnLayer g) y y' = B.kernel K y y' * g y' := by
  have h : B.mulOnLayer g (({y'} : Set ↥B.allSites).indicator 1) =
      g y' • ({y'} : Set ↥B.allSites).indicator 1 := by
    funext z
    by_cases hz : z = y'
    · subst hz
      simp [SeparatedChain.mulOnLayer]
    · simp [SeparatedChain.mulOnLayer, hz]
  change K (B.mulOnLayer g _) y = _
  rw [h, map_smul]
  simp [SeparatedChain.kernel, mul_comm]
theorem mulOnLayer_commute (g g' : D.Space → ℝ) :
    B.mulOnLayer g * B.mulOnLayer g' =
      B.mulOnLayer g' * B.mulOnLayer g := by
  refine LinearMap.ext fun w => funext fun y => ?_
  change g y * (g' y * w y) = g' y * (g y * w y)
  ring
theorem scaleOnLayer_sq :
    (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2 =
      B.mulOnLayer fun x => B.siteScale x ^ 2 := by
  refine LinearMap.ext fun w => funext fun y => ?_
  rw [pow_two]
  change B.siteScale y * (B.siteScale y * w y) = B.siteScale y ^ 2 * w y
  ring
theorem kernel_scaled_eq_matrix (K : Module.End ℝ B.LayerFn) (y z : ↥B.allSites)
    (hz : 0 < B.siteScale z)
    (hm : B.matrixOf K y z =
      B.siteScale y ^ 2 * B.kernel K y z * B.siteScale z ^ (-2 : ℤ)) :
    B.kernel ((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2 * K *
        (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2) y z =
      B.matrixOf K y z * B.siteScale z ^ 4 := by
  rw [scaleOnLayer_sq, kernel_mul_mulOnLayer, kernel_mulOnLayer_mul, hm]
  have : B.siteScale z ^ (-2 : ℤ) = (B.siteScale z ^ 2)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [this]
  field_simp
variable {ι : Type} {𝒟 : ι → D.CoverPiece} (δ : B.Localization 𝒟)
theorem errorBlock_eq_scaled (P : Module.End ℝ B.LayerFn)
    (hP : P = B.mulOnLayer fun x => B.siteScale x ^ 2)
    (hT : B.avgGreenSq = P * B.scaledGreenSq * P)
    (hTl : ∀ i, δ.localSqOnLayers i = P * δ.localScaledExt i * P) (a b : ι) :
    δ.errorBlock a b = P * δ.remainderBlock a b * P := by
  have cm : ∀ g : D.Space → ℝ, B.mulOnLayer g * P = P * B.mulOnLayer g :=
    fun g => by rw [hP]; exact mulOnLayer_commute _ _
  have l : ∀ m K : Module.End ℝ B.LayerFn, m * P = P * m →
      P * (m * K) * P = m * (P * K * P) := fun m K h => by
    rw [← mul_assoc, ← h]
    noncomm_ring
  have r : ∀ m K : Module.End ℝ B.LayerFn, m * P = P * m →
      P * (K * m) * P = (P * K * P) * m := fun m K h => by
    rw [mul_assoc P (K * m) P, mul_assoc K m P, h]
    simp only [mul_assoc]
  have hχ : B.pieceIndicatorOp (𝒟 b) * P = P * B.pieceIndicatorOp (𝒟 b) := cm _
  have hh : B.pieceCutoffOp (𝒟 b) * P = P * B.pieceCutoffOp (𝒟 b) := cm _
  have hh' : B.pieceCutoffOp (𝒟 a) * P = P * B.pieceCutoffOp (𝒟 a) := cm _
  have hcut : δ.cutLocalSq b = P * δ.cutScaled b * P := by
    change _ * δ.localSqOnLayers b * _ = P * (_ * δ.localScaledExt b * _) * P
    rw [r _ _ hχ, l _ _ hχ, hTl]
  unfold SeparatedChain.Localization.errorBlock
    SeparatedChain.Localization.remainderBlock
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl, hcut, hTl, hT]
    have e : ∀ (x y z : Module.End ℝ B.LayerFn), P * (x - y + z) * P =
        P * x * P - P * y * P + P * z * P := fun x y z => by
      rw [mul_add, mul_sub, add_mul, sub_mul]
    have e' : ∀ (x y : Module.End ℝ B.LayerFn), P * (x - y) * P =
        P * x * P - P * y * P := fun x y => by rw [mul_sub, sub_mul]
    rw [e, l _ _ hh, r _ _ hh, r _ _ hh, l _ _ hχ, e']
  · rw [if_neg hab, if_neg hab]
    have hχ1 : (B.pieceIndicatorOp (𝒟 b) - 1) * P = P * (B.pieceIndicatorOp (𝒟 b) - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one]
      rw [hχ]
    have hh2 : B.pieceCutoffOp (𝒟 a) ^ 2 * P = P * B.pieceCutoffOp (𝒟 a) ^ 2 :=
      (show Commute (B.pieceCutoffOp (𝒟 a)) P from hh').pow_left 2
    have hprod : (B.pieceIndicatorOp (𝒟 b) - 1) * B.pieceCutoffOp (𝒟 a) ^ 2 * P =
        P * ((B.pieceIndicatorOp (𝒟 b) - 1) * B.pieceCutoffOp (𝒟 a) ^ 2) := by
      rw [mul_assoc, hh2, ← mul_assoc, hχ1, mul_assoc]
    rw [r _ _ hh, l _ _ hprod, hT]
theorem sum_cutoff_le [Fintype ι] {c : ℝ} (hc : B.IsCover c 𝒟) {x : D.Space}
    (hx : x ∈ B.stage 0) : ∑ i, (𝒟 i).cutoff x ≤ c := by
  classical
  set S : Finset ι := Finset.univ.filter fun i => (𝒟 i).cutoff x ≠ 0 with hS
  have hset : {i | (𝒟 i).cutoff x ≠ 0} = (S : Set ι) := by
    ext i
    simp [hS]
  have hcard : ((S.card : ℕ) : ℝ) ≤ c := by
    have := hc.overlap x hx
    rwa [hset, Set.ncard_coe_finset] at this
  have hsum : ∑ i, (𝒟 i).cutoff x = ∑ i ∈ S, (𝒟 i).cutoff x := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (𝒟 i).cutoff x = 0 <;> simp [h]
  rw [hsum]
  refine le_trans ?_ hcard
  calc ∑ i ∈ S, (𝒟 i).cutoff x ≤ ∑ _i ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => ((𝒟 i).cutoff_mem x).2
    _ = (S.card : ℝ) := by simp
end Operators
set_option maxHeartbeats 1600000 in
theorem inverseExpansionHolds (hFl : ExpansionFloors.Statement)
    (hKc : LayerKernelCalculus)
    (hLi : LocalAveragedSquareInverse)
    (hRb : ScaledRemainderBoundStatement)
    (hNe : NeumannParametrixExpansion) (hSu : ChainSiteSumBounds)
    (hCa : DistanceAvgPairMatrixNormFacts)
    (D : TorusData) (B : SeparatedChain D) (hne : (B.stage 0).Nonempty) (ι : Type)
    (𝒟 : ι → D.CoverPiece) (c : ℝ) (hc : B.IsCover c 𝒟) (δ : B.Localization 𝒟)
    (hblock : expansionBlockSizeFloor 4 D.L c ≤ (D.blockNumber : ℝ))
    (hgap : expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ)) :
    δ.InverseExpansionHolds c := by
  obtain ⟨hfin, hmem, hpos, -, hcomp, -, hinvΞ, hext⟩ := hKc D B hne
  obtain ⟨h2δ, -, hδε, hfloor6, -⟩ := hFl.2.1 D.L D.blocking
  obtain ⟨-, -, -, hsumfloor, -, hhalf⟩ := hFl.2.2 D hgap
  obtain ⟨hanti, -, hlayer, -, hsums⟩ := hSu D B
  obtain ⟨-, -, -, -, -, -, -, hmat, -⟩ := hCa D B hne
  have hmatrix := hmat.2.2.2.1
  have h1c : 1 ≤ c := hc.one_le
  have hc0 : 0 < c := by linarith
  have hL3 : (3 : ℝ) ≤ (D.L : ℝ) := by exact_mod_cast D.blocking.three_le_factor
  have hL0 : (0 : ℝ) < (D.L : ℝ) := by linarith
  have h6L : 6 * (D.L : ℝ) ≤ (D.blockNumber : ℝ) := (hfloor6 c h1c).trans hblock
  have hM : (0 : ℝ) < (D.blockNumber : ℝ) := by linarith
  have hδ : 0 < expansionDecayRate 4 D.L := by linarith
  have hε : 0 < greenDecayRate 4 D.L := by
    unfold greenDecayRate
    positivity
  have hγ : 0 < lowerBoundConst 4 := by
    unfold lowerBoundConst lowerBoundBaseConst testLaplacianConst
    positivity
  have hcS : ∀ κ : ℝ, 0 < κ → 0 < latticeSumConst 4 D.L κ := by
    intro κ hκ
    unfold latticeSumConst
    positivity
  have hCS : 0 ≤ upperBoundConst 4 D.L := by
    have := hcS (1 / 4 * greenDecayRate 4 D.L) (by positivity)
    unfold upperBoundConst
    positivity
  have hC5 : 0 ≤ localComparisonConst 4 D.L := by
    have := hcS (1 / 16 * greenDecayRate 4 D.L) (by positivity)
    unfold localComparisonConst
    positivity
  have hC6 : 0 ≤ expansionConstFirst 4 D.L c := by
    unfold expansionConstFirst
    positivity
  have hC7 : 0 ≤ expansionConstSecond 4 D.L c := by
    have := hcS (expansionDecayRate 4 D.L) hδ
    unfold expansionConstSecond
    positivity
  have hB₅ : 4 * c * latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) / lowerBoundConst 4 ≤
      expansionConstBound 4 D.L c :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have := hc.finite
  have := hfin
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ↥B.allSites
  classical
  have hdist : ∀ y y' : ↥B.allSites, 0 ≤ B.weightedDistance y y' := by
    intro y y'
    have layer_of : ∀ x : ↥B.allSites, ∃ n, (x : D.Space) ∈ B.layer n := by
      intro x
      obtain ⟨n, -, hn⟩ := Set.mem_iUnion₂.1 x.2
      exact ⟨n, hn.2⟩
    obtain ⟨n, hn⟩ := layer_of y
    obtain ⟨n', hn'⟩ := layer_of y'
    refine le_trans ?_ (hlayer n n' y hn y' hn')
    positivity
  have hloc := fun i => hLi D B hne hgap ι 𝒟 c hc δ i
  choose E hEχ hE₁ hE₂ hEk using fun i => (hloc i).2
  have hχ : ∀ i (w : B.LayerFn), B.pieceIndicatorOp (𝒟 i) w =
      (B.pieceSiteSet (𝒟 i)).indicator w := by
    intro i w
    funext y
    by_cases hy : (y : D.Space) ∈ B.pieceSites (𝒟 i)
    · rw [indicator_of_mem (show y ∈ B.pieceSiteSet (𝒟 i) from hy)]
      change (B.pieceSites (𝒟 i)).indicator 1 (y : D.Space) * w y = w y
      rw [indicator_of_mem hy]
      simp
    · rw [indicator_of_notMem (show y ∉ B.pieceSiteSet (𝒟 i) from hy)]
      change (B.pieceSites (𝒟 i)).indicator 1 (y : D.Space) * w y = 0
      rw [indicator_of_notMem hy]
      simp
  have hcomp' := fun i => isUnit_compression_of_cut_inverse (B.pieceSiteSet (𝒟 i))
    (B.pieceIndicatorOp (𝒟 i)) (δ.localSqOnLayers i) (E i) (hχ i) (hEχ i) (hE₁ i)
    (hE₂ i)
  have hCE : ∀ i, δ.localInv i = E i := fun i => (hcomp' i).2.2
  have hzero : ∀ i (y : ↥B.allSites), (y : D.Space) ∉ B.pieceSites (𝒟 i) →
      (𝒟 i).cutoff y = 0 := by
    intro i y hy
    refine hc.cutoff_eq_zero i y fun h => hy ⟨y.2, ?_⟩
    have hside : 0 ≤ D.blockSide (𝒟 i).index := by
      have : 0 < D.scale (𝒟 i).index := by
        have := D.bareSpacing_pos
        unfold TorusData.scale
        positivity
      unfold TorusData.blockSide
      positivity
    change TorusMetric.torusSupNorm _ ≤ 1 * _
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) hside
  have hχh : ∀ i, B.pieceIndicatorOp (𝒟 i) * B.pieceCutoffOp (𝒟 i) =
      B.pieceCutoffOp (𝒟 i) := by
    intro i
    refine LinearMap.ext fun w => funext fun y => ?_
    change (B.pieceSites (𝒟 i)).indicator 1 (y : D.Space) * ((𝒟 i).cutoff y * w y) =
      (𝒟 i).cutoff y * w y
    by_cases hy : (y : D.Space) ∈ B.pieceSites (𝒟 i)
    · rw [indicator_of_mem hy]
      simp
    · rw [hzero i y hy]
      simp
  have hhχ : ∀ i, B.pieceCutoffOp (𝒟 i) * B.pieceIndicatorOp (𝒟 i) =
      B.pieceCutoffOp (𝒟 i) := fun i => by
    rw [show B.pieceCutoffOp (𝒟 i) * B.pieceIndicatorOp (𝒟 i) =
      B.pieceIndicatorOp (𝒟 i) * B.pieceCutoffOp (𝒟 i) from
      mulOnLayer_commute _ _, hχh]
  have hsq : ∑ i, B.pieceCutoffOp (𝒟 i) ^ 2 = 1 := by
    refine LinearMap.ext fun w => funext fun y => ?_
    have one : ∀ i, (B.pieceCutoffOp (𝒟 i) ^ 2) w y = (𝒟 i).cutoff y ^ 2 * w y := by
      intro i
      rw [pow_two]
      change (𝒟 i).cutoff y * ((𝒟 i).cutoff y * w y) = _
      ring
    have hs := hc.sum_sq y (hmem y)
    rw [finsum_eq_sum_of_fintype] at hs
    rw [LinearMap.sum_apply, Finset.sum_apply]
    simp only [one]
    rw [← Finset.sum_mul, hs, one_mul]
    rfl
  have hTC : B.avgGreenSq * ∑ᶠ i, B.pieceCutoffOp (𝒟 i) * δ.localInv i *
      B.pieceCutoffOp (𝒟 i) = 1 - ∑ᶠ i, ∑ᶠ i', δ.errorTerm i i' := by
    simp only [finsum_eq_sum_of_fintype]
    refine mul_approxInverse_eq_one_sub B.avgGreenSq (fun i => B.pieceIndicatorOp (𝒟 i))
      (fun i => B.pieceCutoffOp (𝒟 i)) (fun i => δ.localSqOnLayers i)
      (fun i => δ.localInv i) δ.errorBlock hχh hhχ (fun i => ?_) hsq (fun i => ?_)
      (fun i i' hii' => ?_)
    · rw [hCE]
      exact hE₁ i
    · unfold SeparatedChain.Localization.errorBlock
      exact if_pos rfl
    · unfold SeparatedChain.Localization.errorBlock
      exact if_neg hii'
  set P : Module.End ℝ B.LayerFn := (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2
    with hPdef
  set Q : Module.End ℝ B.LayerFn :=
    Ring.inverse (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2 with hQdef
  have hPQ : P * Q = 1 := by
    refine LinearMap.ext fun w => funext fun y => ?_
    rw [hPdef, hQdef, pow_two, pow_two, hinvΞ]
    change B.siteScale y * (B.siteScale y * ((B.siteScale y)⁻¹ *
      ((B.siteScale y)⁻¹ * w y))) = w y
    have := (hpos y).ne'
    field_simp
  have hQP : Q * P = 1 := by
    refine LinearMap.ext fun w => funext fun y => ?_
    rw [hPdef, hQdef, pow_two, pow_two, hinvΞ]
    change (B.siteScale y)⁻¹ * ((B.siteScale y)⁻¹ * (B.siteScale y *
      (B.siteScale y * w y))) = w y
    have := (hpos y).ne'
    field_simp
  have hcancel : ∀ K : Module.End ℝ B.LayerFn, P * (Q * K * Q) * P = K := by
    intro K
    calc P * (Q * K * Q) * P = (P * Q) * K * (Q * P) := by simp only [mul_assoc]
      _ = K := by rw [hPQ, hQP, one_mul, mul_one]
  have hT : B.avgGreenSq = P * B.scaledGreenSq * P := (hcancel _).symm
  have hTl : ∀ i, δ.localSqOnLayers i = P * δ.localScaledExt i * P := by
    intro i
    have : δ.localScaledExt i = Q * δ.localSqOnLayers i * Q := hext _ _
    rw [this, hcancel]
  have hblk := errorBlock_eq_scaled δ P scaleOnLayer_sq hT hTl
  have hterm : ∀ a b (y y' : ↥B.allSites), B.kernel (δ.errorTerm a b) y y' =
      (∑ z, B.matrixOf (δ.remainderBlock a b) y z *
        (B.siteScale z ^ 4 * B.kernel (E b) z y')) * (𝒟 b).cutoff y' := by
    intro a b y y'
    change B.kernel (δ.errorBlock a b * δ.localInv b *
      B.mulOnLayer (𝒟 b).cutoff) y y' = _
    rw [kernel_mul_mulOnLayer, hCE]
    congr 1
    have := hcomp (δ.errorBlock a b) (E b) y y'
    rw [finsum_eq_sum_of_fintype] at this
    refine this.trans (Finset.sum_congr rfl fun z _ => ?_)
    rw [hblk, kernel_scaled_eq_matrix _ y z (hpos z) (hmatrix _ y z)]
    ring
  have hE₀ : ∀ b (z y' : ↥B.allSites), (z : D.Space) ∉ B.pieceSites (𝒟 b) →
      B.kernel (E b) z y' = 0 := by
    intro b z y' hz
    rw [← hEχ b]
    change B.kernel (B.mulOnLayer _ * E b * B.mulOnLayer _) z y' = 0
    rw [kernel_mul_mulOnLayer, kernel_mulOnLayer_mul, indicator_of_notMem hz]
    simp
  have hq : ∀ y y' : ↥B.allSites, ∑ᶠ i, ∑ᶠ i', |B.kernel (δ.errorTerm i i') y y'| ≤
      (expansionConstSecond 4 D.L c * (D.blockNumber : ℝ)⁻¹) *
        Real.exp (-expansionDecayRate 4 D.L * B.weightedDistance y y') := by
    intro y y'
    simp only [finsum_eq_sum_of_fintype, hterm]
    have hchain := sum_abs_chain_kernel_le
      (fun a b (y z : ↥B.allSites) => B.matrixOf (δ.remainderBlock a b) y z)
      (fun b (z y' : ↥B.allSites) => B.siteScale z ^ 4 * B.kernel (E b) z y')
      (fun b (y : ↥B.allSites) => (𝒟 b).cutoff y)
      (fun b => {z : ↥B.allSites | (z : D.Space) ∈ B.pieceSites (𝒟 b)})
      (fun y y' : ↥B.allSites => B.weightedDistance y y')
      (expansionConstFirst 4 D.L c * (D.blockNumber : ℝ)⁻¹) (2 / lowerBoundConst 4)
      (latticeSumConst 4 D.L (expansionDecayRate 4 D.L)) c (expansionDecayRate 4 D.L)
      (by positivity) (by positivity) (hcS _ hδ).le ?_ ?_ ?_ ?_ ?_ ?_ y y'
    · refine hchain.trans (le_of_eq ?_)
      unfold expansionConstSecond
      ring
    · intro b y z hz
      have h := hRb D B hne h6L hgap ι 𝒟 c hc δ b y z hz
      rw [finsum_eq_sum_of_fintype] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (hdist y z))
      linarith
    · intro b z y'
      have h := hEk b z y'
      rw [abs_mul, abs_of_pos (pow_pos (hpos z) 4)]
      calc B.siteScale z ^ 4 * |B.kernel (E b) z y'|
          ≤ B.siteScale z ^ 4 * (2 / lowerBoundConst 4 * B.siteScale z ^ (-4 : ℤ) *
              Real.exp (-(2 * expansionDecayRate 4 D.L) * B.weightedDistance z y')) :=
            mul_le_mul_of_nonneg_left h (pow_pos (hpos z) 4).le
        _ = _ := by
            have hz := (hpos z).ne'
            rw [zpow_neg]
            norm_cast
            field_simp
    · intro b z y' hz
      rw [hE₀ b z y' hz, mul_zero]
    · intro b y
      exact ((𝒟 b).cutoff_mem y).1
    · intro y
      exact sum_cutoff_le hc (hmem y)
    · intro y y'
      have h := (hsums (expansionDecayRate 4 D.L) hδ (hsumfloor _ (by linarith))).2 y y'
      rwa [finsum_eq_sum_of_fintype] at h
  have hp : ∀ y y' : ↥B.allSites, ∑ᶠ i, |B.kernel (B.pieceCutoffOp (𝒟 i) *
      δ.localInv i * B.pieceCutoffOp (𝒟 i)) y y'| ≤
      (c * (2 / lowerBoundConst 4)) * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(2 * expansionDecayRate 4 D.L) * B.weightedDistance y y') := by
    intro y y'
    rw [finsum_eq_sum_of_fintype]
    set W : ℝ := 2 / lowerBoundConst 4 * B.siteScale y ^ (-4 : ℤ) *
      Real.exp (-(2 * expansionDecayRate 4 D.L) * B.weightedDistance y y') with hW
    have hW0 : 0 ≤ W := by
      have := (hpos y).le
      rw [hW]
      positivity
    have one : ∀ i, |B.kernel (B.pieceCutoffOp (𝒟 i) * δ.localInv i *
        B.pieceCutoffOp (𝒟 i)) y y'| ≤ (𝒟 i).cutoff y * W := by
      intro i
      change |B.kernel (B.mulOnLayer _ * δ.localInv i *
        B.mulOnLayer _) y y'| ≤ _
      rw [kernel_mul_mulOnLayer, kernel_mulOnLayer_mul, hCE, abs_mul, abs_mul,
        abs_of_nonneg ((𝒟 i).cutoff_mem y).1, abs_of_nonneg ((𝒟 i).cutoff_mem y').1,
        mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ ((𝒟 i).cutoff_mem y).1
      calc |B.kernel (E i) y y'| * (𝒟 i).cutoff y'
          ≤ W * 1 := mul_le_mul (hEk i y y') ((𝒟 i).cutoff_mem y').2
            ((𝒟 i).cutoff_mem y').1 hW0
        _ = W := mul_one _
    refine (Finset.sum_le_sum fun i _ => one i).trans ?_
    rw [← Finset.sum_mul]
    calc (∑ i, (𝒟 i).cutoff y) * W ≤ c * W :=
          mul_le_mul_of_nonneg_right (sum_cutoff_le hc (hmem y)) hW0
      _ = _ := by rw [hW]; ring
  have hcSδ := hcS (1 / 2 * expansionDecayRate 4 D.L) (by positivity)
  have hsmall : (expansionConstSecond 4 D.L c * (D.blockNumber : ℝ)⁻¹) *
      latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) ≤ 1 / 2 := by
    have h : 2 * expansionConstSecond 4 D.L c *
        latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) ≤ (D.blockNumber : ℝ) :=
      (le_max_right _ _).trans hblock
    rw [mul_right_comm, mul_inv_le_iff₀ hM]
    linarith
  have N := hNe D B hne (expansionDecayRate 4 D.L)
    (expansionConstSecond 4 D.L c * (D.blockNumber : ℝ)⁻¹) (c * (2 / lowerBoundConst 4)) hδ
    (by positivity) (by positivity) hsumfloor hsmall ι inferInstance B.avgGreenSq
    (fun i => B.pieceCutoffOp (𝒟 i) * δ.localInv i * B.pieceCutoffOp (𝒟 i))
    δ.errorTerm hTC hq hp
  have hb : c * (2 / lowerBoundConst 4) * latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) ≤
      1 / 2 * expansionConstBound 4 D.L c := by
    have : c * (2 / lowerBoundConst 4) * latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) =
        1 / 2 * (4 * c * latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) /
          lowerBoundConst 4) := by ring
    rw [this]
    linarith
  refine
    { one_sub_error_isUnit := N.isUnit_one_sub_remainder
      inverse_eq := N.inverse_eq_mul
      hasSum_powers := N.hasSum_kernel_pow
      hasSum_terms := N.hasSum_kernel_words
      sum_terms_kernel_le := fun n y y' => (N.sum_abs_kernel_products_le n y y').trans ?_
      inverse_kernel_le := fun y y' => (N.abs_kernel_inverse_le y y').trans ?_ }
  · have := (hpos y).le
    have hx : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
    have hz : 0 ≤ B.siteScale y ^ (-4 : ℤ) := by positivity
    gcongr
  · have := (hpos y).le
    have hz : 0 ≤ B.siteScale y ^ (-4 : ℤ) := by positivity
    have : 2 * (c * (2 / lowerBoundConst 4)) *
        latticeSumConst 4 D.L (1 / 2 * expansionDecayRate 4 D.L) ≤ expansionConstBound 4 D.L c := by
      linarith
    gcongr
theorem inverseExpansionTheorem_holds (hFl : ExpansionFloors.Statement)
    (hKc : LayerKernelCalculus)
    (hLi : LocalAveragedSquareInverse)
    (hRb : ScaledRemainderBoundStatement)
    (hNe : NeumannParametrixExpansion) (hSu : ChainSiteSumBounds)
    (hCa : DistanceAvgPairMatrixNormFacts) :
    InverseExpansionTheorem := by
  refine ⟨fun L hL => ?_, ⟨fun q : ℕ × ℕ =>
    (expansionConstBound q.1 q.2 (coverConst q.1 q.2),
      expansionBlockSizeFloor q.1 q.2 (coverConst q.1 q.2)), fun _ => rfl⟩, ?_⟩
  · have h := hFl.2.1 L hL
    exact ⟨by linarith [h.1], h.2.2.1⟩
  intro D B hne ι 𝒟 c hc δ hblock hgap
  exact inverseExpansionHolds hFl hKc hLi hRb hNe hSu hCa D B hne ι 𝒟 c hc δ hblock hgap
end YangMills.Construction.Weighted.InverseExpansion
