import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesOnARegion
import YangMills.Construction.ColdChainAtEveryLevel.VariationsAlongAMisfit
import YangMills.Construction.ColdChainAtEveryLevel.ComplexCells
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfTheTopAverageProof
import YangMills.Construction.ColdChainAtEveryLevel.DerivativesOfTheChainTotal
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAtTheReference
import YangMills.Construction.ColdChainAtEveryLevel.FitsInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.LevelNormsOnFewCells
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinatesAreSeminorms
import YangMills.Construction.ColdChainAtEveryLevel.SizeOfABondAlongADirection
import YangMills.Construction.HoleBesideASecondHole.TermsOfSmallCoordinatesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace FirstVariation
open YangMills.Construction.BlockLines YangMills.Construction.WeightedAverages.Sums
open YangMills.Construction.LevelRecursion YangMills.Construction.BlockAverages.ChartNorms
open YangMills.Construction.BlockAverages.ChartFits YangMills.Construction.ComplexRemainders
open YangMills.Construction.ComplexLevels YangMills.Construction.HullBounds
open YangMills.Construction.BondAverageNorms
variable {F : BlockFrame}
abbrev scaleAt (F : BlockFrame) (m : ℕ) : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - m)
abbrev ray (A : ChainChart F) (τ : ℝ) : ChainChart F := chartMove (zeroChart F) A τ
def rayCoordNorm (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (m : ℕ) : F.Site m → Fin 4 → ℝ :=
  fun x i => ‖levelCoordinate R (ray A τ) m x i‖
def rayLinearGap (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (m : ℕ) : F.Site m → Fin 4 → ℍ[ℝ] :=
  fun x i => levelCoordinate R (ray A τ) m x i - τ • linearPart R A m x i
theorem rayCoordNorm_nonneg (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (m : ℕ) (x : F.Site m) (i : Fin 4) :
    0 ≤ rayCoordNorm R A τ m x i := norm_nonneg _
theorem ray_coarse (A : ChainChart F) (τ : ℝ) (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4) :
    (((ray A τ).coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) = τ • ((A.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) := by
  show (((0 : imaginaryQuaternions) + τ • A.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) = _
  simp
theorem ray_fine (A : ChainChart F) (τ : ℝ) (x : F.Site 0) (i : Fin 4) :
    (ray A τ).fine x i = τ • A.fine x i := by
  show (0 : imaginaryQuaternions) + τ • A.fine x i = _
  simp
structure ColdTopHyp (del C Cb cc s : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) : Prop where
  odd : Odd F.blockSide
  two : 2 ≤ F.blockSide
  amb : IsAdmissibleAmbient F
  hC : 1 ≤ C
  hCb : 0 ≤ Cb
  hdel : 0 < del
  s0 : 0 < s
  s1 : s ≤ 1
  cc0 : 0 < cc
  top : R F.top = V
  curv : ∀ p ∈ innerPlaquettes S 0, plaquetteDefect (R 0) p ≤ Cb * s * levelScale F 0 ^ 2
  mis_low : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
    unitDeviation (referenceDefect R j c) ≤ Cb * s * levelScale F (j + 1) ^ 3
  mis_top : ∀ c ∈ innerBonds S F.top, unitDeviation (referenceDefect R F.depth c) ≤ Cb * s
  one_step : ∀ (U : ChainChart F) (j : ℕ) (b : F.Site (j + 1) × Fin 4), j + 1 < F.top → b ∈ innerBonds S (j + 1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ cc → ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ ≤ cc →
      BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) b t →
      ‖levelCoordinate R U (j + 1) b.1 b.2 - ((U.coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) -
          parallelAverage (R j) (levelCoordinate R U j) b‖ ≤
        C * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 + ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ +
          ‖((referenceDefect R j b : UnitQuaternion) : ℍ[ℝ]) - 1‖) * t)
  rearrangedPathCorner : ∀ (U : ChainChart F) (j : ℕ) (b : F.Site (j + 1) × Fin 4), j < F.top → b ∈ innerBonds S (j + 1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ cc → BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) b t →
      ‖bondAngle R U j b - parallelAverage (R j) (levelCoordinate R U j) b‖ ≤
        C * (t ^ 2 + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 * t)
  size : ∀ (j : ℕ) (b : F.Site (j + 1) × Fin 4), j < F.top → b ∈ innerBonds S (j + 1) →
    (∀ U : ChainChart F, ‖gaugedBondAverage R U j b‖ = bondAverageNorm (R j) (levelCoordinateImaginary R U j) b) ∧
    ∀ (f : F.Site j → Fin 4 → imaginaryQuaternions) (t : ℝ), 0 ≤ t → t ≤ cc →
      BoundedOnAdjacentBlocks (fun x i => ‖(f x i : ℍ[ℝ])‖) b t →
      (∀ (k : ℕ) (g : Fin k → F.Site j → Fin 4 → imaginaryQuaternions), AnalyticAt ℝ (fun σ : Fin k → ℝ =>
        bondAverageNorm (R j) (fun x i => f x i + ∑ l, σ l • g l x i) b) 0) ∧
      ∀ (g : F.Site j → Fin 4 → imaginaryQuaternions) (ρ : ℝ), 0 ≤ ρ →
        BoundedOnAdjacentBlocks (fun x i => ‖(g x i : ℍ[ℝ])‖) b ρ →
        |deriv (fun τ : ℝ => bondAverageNorm (R j) (fun x i => f x i + τ • g x i) b) 0| ≤
          C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * ρ
  coords : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ cc → ∀ j, j < F.top → ∀ z ∈ S,
    Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} j, ‖levelCoordinate R U j b.1 b.2‖ ^ 4)) ≤
      C * localNorm S R U (constOneWeights F) z
theorem boundedOnAdjacentBlocks_bondHullSum {j : ℕ} (c : F.Site (j + 1) × Fin 4) {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) : BoundedOnAdjacentBlocks f c (bondHullSum c f) := by
  refine ⟨fun h hh k hk => le_bondHullSum_of_block c hf hh k hk, fun h hh r hr => le_bondHullSum_of_line c hf hh hr⟩
theorem lineBlockAverage_le_bondHullSum {j : ℕ} (hodd : Odd F.blockSide) (c : F.Site (j + 1) × Fin 4)
    {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) : lineBlockAverage f c ≤ bondHullSum c f := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  unfold lineBlockAverage
  have h1 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ≤ bondHullSum c f := by
    rw [bondHullSum]
    have h2 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4, (if h + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h) k + f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k
        else 0) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
        split_ifs
        · exact add_nonneg (hf _ _) (hf _ _)
        · exact le_rfl
    have e : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, f (lineBond c h r).1 (lineBond c h r).2 =
        ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 := rfl
    rw [e]
    linarith
  have h3 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _
  have h4 : 1 / (F.blockSide : ℝ) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ hL
  calc _ ≤ 1 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 :=
        mul_le_mul_of_nonneg_right h4 h3
    _ ≤ _ := by rw [one_mul]; exact h1
theorem norm_parallelAverage_le_lineBlockAverage {j : ℕ} (hodd : Odd F.blockSide) (X : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    ‖parallelAverage X f c‖ ≤ lineBlockAverage (fun x i => ‖f x i‖) c :=
  norm_parallelAverage_le hodd X f c
theorem parallelAverage_sub_smul {j : ℕ} (X : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ]) (τ : ℝ)
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage X (fun x i => f x i - τ • g x i) c =
      parallelAverage X f c - τ • parallelAverage X g c := by
  unfold parallelAverage
  rw [smul_comm τ, ← smul_sub]
  congr 1
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun r _ => ?_
  simp [_root_.YangMills.Construction.BlockAverages.adjointAction, mul_sub, sub_mul]
section Small
variable {del C Cb cc s : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top}
def stepFactor (C s : ℝ) (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (m : ℕ) (y : F.Site (m + 1)) (d : Fin 4) : ℝ :=
  C * (bondHullSum (y, d) (rayCoordNorm R A τ m) + s * scaleAt F (m + 1) ^ 2 + τ * ‖A.coarse m y d‖ +
    ‖((referenceDefect R m (y, d) : UnitQuaternion) : ℍ[ℝ]) - 1‖)
structure IsSmallStep (C cc : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (τ δ : ℝ) : Prop where
  τ0 : 0 < τ
  δ0 : 0 ≤ δ
  δc : δ ≤ cc
  hull : ∀ m, m < F.top → ∀ c ∈ innerBonds S (m + 1), C * bondHullSum c (rayCoordNorm R A τ m) ≤ δ
  mu : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds S (m + 1), C * (τ * ‖A.coarse m c.1 c.2‖) ≤ δ
  base : ∀ b ∈ innerBonds S 0, τ * ‖A.fine b.1 b.2‖ ≤ 1 / 8
theorem stepFactor_nonneg (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) {τ : ℝ} (hτ : 0 ≤ τ) (m : ℕ)
    (y : F.Site (m + 1)) (d : Fin 4) : 0 ≤ stepFactor C s R A τ m y d := by
  have h1 : 0 ≤ bondHullSum (y, d) (rayCoordNorm R A τ m) := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ m)
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast h.odd.pos
  have h2 := h.s0
  have hC : 0 ≤ C := by linarith [h.hC]
  unfold stepFactor
  positivity
theorem le_mul_of_one_le_const {C x : ℝ} (hC : 1 ≤ C) (hx : 0 ≤ x) : x ≤ C * x := by nlinarith
theorem rayStep_bound (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {m : ℕ} (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4}
    (hc : c ∈ innerBonds S (m + 1)) :
    ‖levelCoordinate R (ray A τ) (m + 1) c.1 c.2 - τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) -
        parallelAverage (R m) (levelCoordinate R (ray A τ) m) c‖ ≤
      stepFactor C s R A τ m c.1 c.2 * bondHullSum c (rayCoordNorm R A τ m) := by
  have hτ := hs.τ0.le
  set t := bondHullSum c (rayCoordNorm R A τ m) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ m)
  have htc : t ≤ cc := (le_mul_of_one_le_const h.hC ht0).trans ((hs.hull m (by omega) c hc).trans hs.δc)
  have hmu : ‖(((ray A τ).coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = τ * ‖A.coarse m c.1 c.2‖ := by
    rw [ray_coarse, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    rfl
  have hmc : ‖(((ray A τ).coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ cc := by
    rw [hmu]
    exact (le_mul_of_one_le_const h.hC (by positivity)).trans ((hs.mu m hm c hc).trans hs.δc)
  have h1 := h.one_step (ray A τ) m c hm hc t ht0 htc hmc
    (boundedOnAdjacentBlocks_bondHullSum c (rayCoordNorm_nonneg R A τ m))
  rw [hmu, ray_coarse] at h1
  refine h1.trans (le_of_eq ?_)
  unfold stepFactor
  rw [← ht]
  simp only [scaleAt]
  ring
theorem scaleAt_le_one (hodd : Odd F.blockSide) (m : ℕ) : scaleAt F m ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.levelScale_le_one <;> assumption
theorem scaleAt_nonneg (hodd : Odd F.blockSide) (m : ℕ) : 0 ≤ scaleAt F m := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  positivity
theorem blockCount_mul_scaleAt (hodd : Odd F.blockSide) (m : ℕ) :
    ((F.blockSide ^ (F.top - m) : ℕ) : ℝ) * scaleAt F m = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    exact this.ne'
  push_cast
  rw [scaleAt, ← mul_pow, mul_one_div_cancel hL, one_pow]
theorem blockCount_le (hodd : Odd F.blockSide) (m : ℕ) :
    ((F.blockSide ^ (F.top - m) : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  push_cast
  exact pow_le_pow_right₀ hL (Nat.sub_le _ _)
theorem stepFactor_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {m : ℕ} (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4}
    (hc : c ∈ innerBonds S (m + 1)) :
    stepFactor C s R A τ m c.1 c.2 ≤ 2 * δ + C * (1 + Cb) * s * scaleAt F (m + 1) ^ 2 := by
  have h1 := hs.hull m (by omega) c hc
  have h2 := hs.mu m hm c hc
  have h3 : ‖((referenceDefect R m (c.1, c.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cb * s * scaleAt F (m + 1) ^ 3 :=
    h.mis_low m hm c hc
  have hC : 0 ≤ C := by linarith [h.hC]
  have hl1 := scaleAt_le_one h.odd (m + 1)
  have hb : 0 ≤ Cb * s := mul_nonneg h.hCb h.s0.le
  have h4 : Cb * s * scaleAt F (m + 1) ^ 3 ≤ Cb * s * scaleAt F (m + 1) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hb
    calc scaleAt F (m + 1) ^ 3 = scaleAt F (m + 1) ^ 2 * scaleAt F (m + 1) := by ring
      _ ≤ scaleAt F (m + 1) ^ 2 * 1 := mul_le_mul_of_nonneg_left hl1 (by positivity)
      _ = _ := by ring
  have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) hC
  unfold stepFactor
  nlinarith
theorem finsetLpNorm_four_stepFactor_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {D : Finset F.Cell} (hDS : D ⊆ S) (hD : D.card ≤ 81) {m : ℕ}
    (hm : m + 1 < F.top) :
    finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => stepFactor C s R A τ m c.1 c.2) ≤
      10 * (F.blockSide : ℝ) ^ F.top * δ + 5 * (C * (1 + Cb) * s) := by
  have hτ := hs.τ0.le
  set Q : ℝ := ((F.blockSide ^ (F.top - (m + 1)) : ℕ) : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hκ : 0 ≤ C * (1 + Cb) * s := by
    have := h.hCb
    have := h.s0
    have : 0 ≤ C := by linarith [h.hC]
    positivity
  have hl1 := scaleAt_le_one h.odd (m + 1)
  have hδ := hs.δ0
  have h1 := finsetLpNorm_four_le_of_abs_le (innerBonds D (m + 1)) (fun c => stepFactor C s R A τ m c.1 c.2)
    (x := 2 * δ + C * (1 + Cb) * s * scaleAt F (m + 1) ^ 2) (Q := Q) (by positivity) hQ0
    (fun c hc => by
      rw [abs_of_nonneg (stepFactor_nonneg h A hτ m c.1 c.2)]
      exact stepFactor_le h hs hm (innerBonds_mono hDS _ hc))
    (card_innerBonds_le_of_card_le h.odd hD _)
  refine h1.trans ?_
  have e1 : Q * scaleAt F (m + 1) = 1 := blockCount_mul_scaleAt h.odd (m + 1)
  have e2 : Q ≤ (F.blockSide : ℝ) ^ F.top := blockCount_le h.odd (m + 1)
  have e3 : 5 * Q * (C * (1 + Cb) * s * scaleAt F (m + 1) ^ 2) =
      5 * (C * (1 + Cb) * s) * scaleAt F (m + 1) := by
    calc _ = 5 * (C * (1 + Cb) * s) * (Q * scaleAt F (m + 1)) * scaleAt F (m + 1) := by ring
      _ = _ := by rw [e1]; ring
  have e4 : 5 * (C * (1 + Cb) * s) * scaleAt F (m + 1) ≤ 5 * (C * (1 + Cb) * s) := by
    nlinarith
  have e5 : 5 * Q * (2 * δ) ≤ 10 * (F.blockSide : ℝ) ^ F.top * δ := by nlinarith
  calc 5 * Q * (2 * δ + C * (1 + Cb) * s * scaleAt F (m + 1) ^ 2)
      = 5 * Q * (2 * δ) + 5 * Q * (C * (1 + Cb) * s * scaleAt F (m + 1) ^ 2) := by ring
    _ ≤ _ := by rw [e3]; linarith
theorem levelCoordinate_ray_zero {A : ChainChart F} {τ : ℝ} (hτ : 0 ≤ τ) (R : F.FieldChain) (x : F.Site 0)
    (i : Fin 4) (h8 : τ * ‖A.fine x i‖ ≤ 1 / 8) :
    levelCoordinate R (ray A τ) 0 x i = τ • ((A.fine x i : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold levelCoordinate
  rw [chartGap_zero, ray_fine]
  have e : (((τ • A.fine x i : imaginaryQuaternions)) : ℍ[ℝ]) = τ • ((A.fine x i : imaginaryQuaternions) : ℍ[ℝ]) := rfl
  rw [unitQuaternionLog_expUnit, e]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
  exact h8
theorem weightedScaleNorm_four_ray_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {D : Finset F.Cell} (hDS : D ⊆ S) (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ}
    (hϑ : |ϑ| ≤ 1 / 8) {n2 : ℝ} (hn2 : 0 ≤ n2)
    (hmu : ∀ m, m + 1 < F.top → weightedScaleNorm D p ϑ 2 (m + 1) (fun y d => ‖A.coarse m y d‖) ≤ n2)
    (hsmall : 568 * (10 * (F.blockSide : ℝ) ^ F.top * δ + 5 * (C * (1 + Cb) * s)) * hullFactor F.blockSide ≤ 1)
    {m : ℕ} (hm : m < F.top) :
    weightedScaleNorm D p ϑ 4 m (rayCoordNorm R A τ m) ≤
      τ * (2 * (20000 * weightedScaleNorm D p ϑ 4 0 (fun x i => ‖A.fine x i‖) + 284 * n2)) := by
  have hτ := hs.τ0.le
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast h.odd.pos
  have hκ : 0 ≤ C * (1 + Cb) * s := by
    have := h.hCb
    have := h.s0
    have : 0 ≤ C := by linarith [h.hC]
    positivity
  have hδ := hs.δ0
  have h1 := weightedScaleNorm_four_le_of_small h.odd h.two D p hϑ (rayCoordNorm R A τ)
    (fun m y d => τ * ‖A.coarse m y d‖)
    (fun m y d => stepFactor C s R A τ m y d) (fun m x d => rayCoordNorm_nonneg R A τ m x d)
    (fun m y d => by positivity) (fun m y d => stepFactor_nonneg h A hτ m y d)
    (ε := 10 * (F.blockSide : ℝ) ^ F.top * δ + 5 * (C * (1 + Cb) * s)) (S := τ * n2)
    (fun m hm c hc => by
      have hcS := innerBonds_mono hDS _ hc
      have h2 := rayStep_bound h hs hm hcS
      have h3 := norm_parallelAverage_le_lineBlockAverage h.odd (R m) (levelCoordinate R (ray A τ) m) c
      have e : levelCoordinate R (ray A τ) (m + 1) c.1 c.2 =
          (levelCoordinate R (ray A τ) (m + 1) c.1 c.2 -
            τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) -
            parallelAverage (R m) (levelCoordinate R (ray A τ) m) c) +
          τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) +
          parallelAverage (R m) (levelCoordinate R (ray A τ) m) c := by abel
      have h4 := norm_add₃_le (a := levelCoordinate R (ray A τ) (m + 1) c.1 c.2 -
        τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) -
        parallelAverage (R m) (levelCoordinate R (ray A τ) m) c)
        (b := τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]))
        (c := parallelAverage (R m) (levelCoordinate R (ray A τ) m) c)
      rw [← e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ] at h4
      show ‖levelCoordinate R (ray A τ) (m + 1) c.1 c.2‖ ≤ lineBlockAverage (rayCoordNorm R A τ m) c +
        (τ * ‖A.coarse m c.1 c.2‖ + stepFactor C s R A τ m c.1 c.2 * bondHullSum c (rayCoordNorm R A τ m))
      have h5 : ‖((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖A.coarse m c.1 c.2‖ := rfl
      rw [h5] at h4
      have h6 : lineBlockAverage (fun x i => ‖levelCoordinate R (ray A τ) m x i‖) c =
          lineBlockAverage (rayCoordNorm R A τ m) c := rfl
      rw [h6] at h3
      linarith)
    (by positivity) (mul_nonneg hτ hn2)
    (fun m hm => finsetLpNorm_four_stepFactor_le h hs hDS hD hm)
    (fun m hm => by
      rw [weightedScaleNorm_const_mul (by norm_num) D p ϑ (m + 1) _ hτ]
      exact mul_le_mul_of_nonneg_left (hmu m hm) hτ)
    hsmall m hm
  refine h1.trans ?_
  have h0 : weightedScaleNorm D p ϑ 4 0 (rayCoordNorm R A τ 0) ≤
      τ * weightedScaleNorm D p ϑ 4 0 (fun x i => ‖A.fine x i‖) := by
    rw [← weightedScaleNorm_const_mul (by norm_num) D p ϑ 0 _ hτ]
    refine weightedScaleNorm_mono_of_abs_le (by norm_num) D p ϑ 0 fun b hb => ?_
    have h3 := hs.base b (innerBonds_mono hDS _ hb)
    have : rayCoordNorm R A τ 0 b.1 b.2 = τ * ‖A.fine b.1 b.2‖ := by
      unfold rayCoordNorm
      rw [levelCoordinate_ray_zero hτ R b.1 b.2 h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
      rfl
    rw [this]
  nlinarith
theorem rayLinearGap_zero {A : ChainChart F} {τ : ℝ} (hτ : 0 ≤ τ) (R : F.FieldChain) (x : F.Site 0) (i : Fin 4)
    (h8 : τ * ‖A.fine x i‖ ≤ 1 / 8) : rayLinearGap R A τ 0 x i = 0 := by
  unfold rayLinearGap
  rw [levelCoordinate_ray_zero hτ R x i h8]
  simp [linearPart]
theorem rayLinearGap_succ_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {m : ℕ} (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4}
    (hc : c ∈ innerBonds S (m + 1)) :
    ‖rayLinearGap R A τ (m + 1) c.1 c.2‖ ≤ lineBlockAverage (fun x i => ‖rayLinearGap R A τ m x i‖) c +
      stepFactor C s R A τ m c.1 c.2 * bondHullSum c (rayCoordNorm R A τ m) := by
  have h2 := rayStep_bound h hs hm hc
  have h3 := norm_parallelAverage_le_lineBlockAverage h.odd (R m) (rayLinearGap R A τ m) c
  have e0 : linearPart R A (m + 1) c.1 c.2 = parallelAverage (R m) (linearPart R A m) (c.1, c.2) +
      ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
    show parallelAverage (R m) (linearPart R A m) (c.1, c.2) +
      (if m + 1 < F.top then ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0) = _
    rw [if_pos hm]
  have e1 : parallelAverage (R m) (rayLinearGap R A τ m) c =
      parallelAverage (R m) (levelCoordinate R (ray A τ) m) c - τ • parallelAverage (R m) (linearPart R A m) c :=
    parallelAverage_sub_smul (R m) _ _ τ c
  have e : rayLinearGap R A τ (m + 1) c.1 c.2 =
      parallelAverage (R m) (rayLinearGap R A τ m) c +
      (levelCoordinate R (ray A τ) (m + 1) c.1 c.2 - τ • ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) -
        parallelAverage (R m) (levelCoordinate R (ray A τ) m) c) := by
    rw [e1]
    unfold rayLinearGap
    rw [e0, smul_add]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h3 h2)
theorem weightedScaleNorm_eq_zero_of_forall {D : Finset F.Cell} {p : F.Site 0} {ϑ : ℝ} {P m : ℕ} (hP : 1 ≤ P)
    {f : F.Site m → Fin 4 → ℝ} (hf : ∀ b ∈ innerBonds D m, f b.1 b.2 = 0) : weightedScaleNorm D p ϑ P m f = 0 := by
  have h1 := weightedScaleNorm_const_mul hP D p ϑ m f (le_refl (0 : ℝ))
  have h2 : weightedScaleNorm D p ϑ P m f ≤ weightedScaleNorm D p ϑ P m (fun x i => 0 * f x i) :=
    weightedScaleNorm_mono_of_abs_le hP D p ϑ m fun b hb => by simp [hf b hb]
  rw [h1, zero_mul] at h2
  exact le_antisymm h2 (finsetLpNorm_nonneg _ _ _)
theorem weightedScaleNorm_two_source_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {D : Finset F.Cell} (hDS : D ⊆ S) (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ}
    (hϑ : |ϑ| ≤ 1 / 8) {E : ℝ} (hE : ∀ m, m < F.top → weightedScaleNorm D p ϑ 4 m (rayCoordNorm R A τ m) ≤ E)
    {i : ℕ} (hi : i + 1 < F.top) :
    weightedScaleNorm D p ϑ 2 (i + 1)
        (fun y d => stepFactor C s R A τ i y d * bondHullSum (y, d) (rayCoordNorm R A τ i)) ≤
      hullFactor F.blockSide * (5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide)) * E := by
  have hτ := hs.τ0.le
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast h.odd.pos
  have hκ : 0 ≤ C * (1 + Cb) * s := by
    have := h.hCb
    have := h.s0
    have : 0 ≤ C := by linarith [h.hC]
    positivity
  have hδ := hs.δ0
  set x := 2 * δ + C * (1 + Cb) * s * scaleAt F (i + 1) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : weightedScaleNorm D p ϑ 2 (i + 1)
        (fun y d => stepFactor C s R A τ i y d * bondHullSum (y, d) (rayCoordNorm R A τ i)) ≤
      weightedScaleNorm D p ϑ 2 (i + 1) (fun y d => x * bondHullSum (y, d) (rayCoordNorm R A τ i)) := by
    refine weightedScaleNorm_mono_of_abs_le (by norm_num) D p ϑ (i + 1) fun b hb => ?_
    have h2 : 0 ≤ bondHullSum (b.1, b.2) (rayCoordNorm R A τ i) := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ i)
    rw [abs_of_nonneg (mul_nonneg (stepFactor_nonneg h A hτ i _ _) h2), abs_of_nonneg (mul_nonneg hx0 h2)]
    exact mul_le_mul_of_nonneg_right (stepFactor_le h hs hi (innerBonds_mono hDS _ hb)) h2
  refine h1.trans ?_
  rw [weightedScaleNorm_const_mul (by norm_num) D p ϑ (i + 1) _ hx0]
  have h2 := weightedScaleNorm_bondHullSum_le (D := D) h.odd hϑ (j := i) (by omega) p 2 (by norm_num)
    (rayCoordNorm_nonneg R A τ i)
  have h3 := weightedScaleNorm_two_le_four h.odd hD p ϑ i (rayCoordNorm R A τ i)
  have h4 := hE i (by omega)
  set Qi : ℝ := ((F.blockSide ^ (F.top - i) : ℕ) : ℝ) with hQi
  have hE0 : 0 ≤ E := (finsetLpNorm_nonneg _ _ _).trans (hE 0 (by simp))
  have hF0 : 0 ≤ hullFactor F.blockSide := by
    unfold hullFactor
    have := one_le_hullFactor_parts (F := F) h.odd
    have hh : 0 ≤ hullBondCount F.blockSide := by
      unfold hullBondCount
      positivity
    positivity
  have e1 : Qi * scaleAt F (i + 1) ^ 2 * 1 ≤ F.blockSide := by
    have e2 : Qi = F.blockSide * ((F.blockSide ^ (F.top - (i + 1)) : ℕ) : ℝ) := by
      rw [hQi]
      push_cast
      rw [← pow_succ']
      congr 1
      omega
    have e3 := blockCount_mul_scaleAt h.odd (i + 1)
    have e4 := scaleAt_le_one h.odd (i + 1)
    rw [e2]
    calc _ = (F.blockSide : ℝ) * (((F.blockSide ^ (F.top - (i + 1)) : ℕ) : ℝ) * scaleAt F (i + 1)) *
          scaleAt F (i + 1) := by ring
      _ = F.blockSide * scaleAt F (i + 1) := by rw [e3]; ring
      _ ≤ F.blockSide * 1 := mul_le_mul_of_nonneg_left e4 (by linarith)
      _ = _ := by ring
  have e5 : x * (5 * Qi) ≤ 5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide) := by
    have e6 := blockCount_le h.odd i
    rw [← hQi] at e6
    have e7 : C * (1 + Cb) * s * (Qi * scaleAt F (i + 1) ^ 2) ≤ C * (1 + Cb) * s * F.blockSide :=
      mul_le_mul_of_nonneg_left (by linarith) hκ
    have e8 : 2 * δ * Qi ≤ 2 * (F.blockSide : ℝ) ^ F.top * δ := by nlinarith
    rw [hx]
    nlinarith
  calc x * weightedScaleNorm D p ϑ 2 (i + 1) (fun y d => bondHullSum (y, d) (rayCoordNorm R A τ i))
      ≤ x * (hullFactor F.blockSide * weightedScaleNorm D p ϑ 2 i (rayCoordNorm R A τ i)) :=
        mul_le_mul_of_nonneg_left h2 hx0
    _ ≤ x * (hullFactor F.blockSide * (5 * Qi * E)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h3.trans ?_) hF0) hx0
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = hullFactor F.blockSide * (x * (5 * Qi)) * E := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e5 hF0) hE0
theorem weightedScaleNorm_two_rayLinearGap_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {D : Finset F.Cell} (hDS : D ⊆ S) (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ}
    (hϑ : |ϑ| ≤ 1 / 8) {E : ℝ} (hE : ∀ m, m < F.top → weightedScaleNorm D p ϑ 4 m (rayCoordNorm R A τ m) ≤ E)
    {m : ℕ} (hm : m < F.top) :
    weightedScaleNorm D p ϑ 2 m (fun x i => ‖rayLinearGap R A τ m x i‖) ≤
      284 * (hullFactor F.blockSide *
        (5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide)) * E) := by
  have hτ := hs.τ0.le
  have hB0 : 0 ≤ hullFactor F.blockSide *
      (5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide)) * E := by
    have hκ : 0 ≤ C * (1 + Cb) * s := by
      have := h.hCb
      have := h.s0
      have : 0 ≤ C := by linarith [h.hC]
      positivity
    have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast h.odd.pos
    have hδ := hs.δ0
    have hE0 : 0 ≤ E := (finsetLpNorm_nonneg _ _ _).trans (hE 0 (by simp))
    have hF0 : 0 ≤ hullFactor F.blockSide := by
      have hh : 0 ≤ hullBondCount F.blockSide := by
        unfold hullBondCount
        positivity
      unfold hullFactor
      positivity
    positivity
  have h1 := (weightedScaleNorm_le_of_recursion h.odd h.two D p hϑ (fun m x i => ‖rayLinearGap R A τ m x i‖)
    (fun i y d => stepFactor C s R A τ i y d * bondHullSum (y, d) (rayCoordNorm R A τ i))
    (fun _ _ _ => norm_nonneg _)
    (fun i y d => mul_nonneg (stepFactor_nonneg h A hτ i y d) (bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ i)))
    (fun m hm c hc => rayLinearGap_succ_le h hs hm (innerBonds_mono hDS _ hc)) m
    (fun i hi => weightedScaleNorm_two_source_le h hs hDS hD p hϑ hE (by omega)) hB0 hm).2
  refine h1.trans ?_
  have h0 : weightedScaleNorm D p ϑ 2 0 (fun x i => ‖rayLinearGap R A τ 0 x i‖) = 0 :=
    weightedScaleNorm_eq_zero_of_forall (by norm_num) fun b hb => by
      rw [rayLinearGap_zero hτ R b.1 b.2 (hs.base b (innerBonds_mono hDS _ hb)), norm_zero]
  rw [h0]
  linarith
def topLinearGap (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (y : F.Site (F.depth + 1)) (d : Fin 4) : ℍ[ℝ] :=
  bondAngle R (ray A τ) F.depth (y, d) - τ • linearPart R A (F.depth + 1) y d
theorem scaleAt_top_eq_one : ((1 / (F.blockSide : ℝ)) ^ (F.top - (F.depth + 1))) = 1 := by apply _root_.YangMills.Construction.ReferenceBounds.levelScale_top_eq_one <;> assumption
theorem bondAngle_ray_sub_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ innerBonds S (F.depth + 1)) :
    ‖bondAngle R (ray A τ) F.depth c - parallelAverage (R F.depth) (levelCoordinate R (ray A τ) F.depth) c‖ ≤
      (δ + C * s) * bondHullSum c (rayCoordNorm R A τ F.depth) := by
  set t := bondHullSum c (rayCoordNorm R A τ F.depth) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ F.depth)
  have h1 := hs.hull F.depth (by simp) c hc
  have htc : t ≤ cc := (le_mul_of_one_le_const h.hC ht0).trans (h1.trans hs.δc)
  have h2 := h.rearrangedPathCorner (ray A τ) F.depth c (by simp) hc t ht0 htc
    (boundedOnAdjacentBlocks_bondHullSum c (rayCoordNorm_nonneg R A τ F.depth))
  rw [scaleAt_top_eq_one] at h2
  refine h2.trans ?_
  have e : C * (t ^ 2 + s * 1 ^ 2 * t) = (C * t + C * s) * t := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) ht0
theorem topLinearGap_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ innerBonds S (F.depth + 1)) :
    ‖topLinearGap R A τ c.1 c.2‖ ≤ bondHullSum c (fun x i => ‖rayLinearGap R A τ F.depth x i‖) +
      (δ + C * s) * bondHullSum c (rayCoordNorm R A τ F.depth) := by
  have h2 := bondAngle_ray_sub_le h hs hc
  have h3 := (norm_parallelAverage_le_lineBlockAverage h.odd (R F.depth) (rayLinearGap R A τ F.depth) c).trans
    (lineBlockAverage_le_bondHullSum h.odd c fun _ _ => norm_nonneg _)
  have e0 : linearPart R A (F.depth + 1) c.1 c.2 = parallelAverage (R F.depth) (linearPart R A F.depth) c := by
    show parallelAverage (R F.depth) (linearPart R A F.depth) (c.1, c.2) +
      (if F.depth + 1 < F.top then ((A.coarse F.depth c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0) = _
    rw [if_neg (by simp [BlockFrame.top]), add_zero]
  have e1 : parallelAverage (R F.depth) (rayLinearGap R A τ F.depth) c =
      parallelAverage (R F.depth) (levelCoordinate R (ray A τ) F.depth) c -
        τ • parallelAverage (R F.depth) (linearPart R A F.depth) c :=
    parallelAverage_sub_smul (R F.depth) _ _ τ c
  have e : topLinearGap R A τ c.1 c.2 = parallelAverage (R F.depth) (rayLinearGap R A τ F.depth) c +
      (bondAngle R (ray A τ) F.depth c - parallelAverage (R F.depth) (levelCoordinate R (ray A τ) F.depth) c) := by
    rw [e1]
    unfold topLinearGap
    rw [e0]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h3 h2)
theorem weightedScaleNorm_add_le_add {D : Finset F.Cell} {p : F.Site 0} {ϑ : ℝ} {P m : ℕ} (hP : 1 ≤ P)
    (f g : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p ϑ P m (fun x i => f x i + g x i) ≤
      weightedScaleNorm D p ϑ P m f + weightedScaleNorm D p ϑ P m g := by
  unfold weightedScaleNorm
  refine le_trans (le_of_eq ?_) (finsetLpNorm_add_le hP _ _ _)
  congr 1
  funext b
  ring
theorem zero_le_hullFactor (L : ℕ) : 0 ≤ hullFactor L := by apply _root_.YangMills.Construction.ComplexCells.hullFactor_nonneg <;> assumption
theorem weightedScaleNorm_two_topLinearGap_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {D : Finset F.Cell} (hDS : D ⊆ S) (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ}
    (hϑ : |ϑ| ≤ 1 / 8) {E : ℝ} (hE : ∀ m, m < F.top → weightedScaleNorm D p ϑ 4 m (rayCoordNorm R A τ m) ≤ E) :
    weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖topLinearGap R A τ y d‖) ≤
      hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide)) * E)) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide * E)) := by
  have hδ := hs.δ0
  have hC : 0 ≤ C := by linarith [h.hC]
  have hs0 := h.s0.le
  have hx0 : 0 ≤ δ + C * s := by positivity
  have hF0 := zero_le_hullFactor F.blockSide
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  have h1 : weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖topLinearGap R A τ y d‖) ≤
      weightedScaleNorm D p ϑ 2 (F.depth + 1)
        (fun y d => bondHullSum (y, d) (fun x i => ‖rayLinearGap R A τ F.depth x i‖) +
        (δ + C * s) * bondHullSum (y, d) (rayCoordNorm R A τ F.depth)) := by
    refine weightedScaleNorm_mono_of_abs_le (by norm_num) D p ϑ (F.depth + 1) fun b hb => ?_
    have h2 := topLinearGap_le h hs (innerBonds_mono hDS _ hb)
    rw [abs_of_nonneg (norm_nonneg _)]
    refine h2.trans (le_abs_self _)
  refine h1.trans ((weightedScaleNorm_add_le_add (by norm_num) _ _).trans (add_le_add ?_ ?_))
  · have h2 := weightedScaleNorm_bondHullSum_le (D := D) h.odd hϑ (j := F.depth) hj p 2 (by norm_num)
      (g := fun x i => ‖rayLinearGap R A τ F.depth x i‖) (fun _ _ => norm_nonneg _)
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hF0)
    exact weightedScaleNorm_two_rayLinearGap_le h hs hDS hD p hϑ hE hj
  · rw [weightedScaleNorm_const_mul (by norm_num) D p ϑ (F.depth + 1) _ hx0]
    refine mul_le_mul_of_nonneg_left ?_ hx0
    have h2 := weightedScaleNorm_bondHullSum_le (D := D) h.odd hϑ (j := F.depth) hj p 2 (by norm_num)
      (rayCoordNorm_nonneg R A τ F.depth)
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hF0)
    have h3 := weightedScaleNorm_two_le_four h.odd hD p ϑ F.depth (rayCoordNorm R A τ F.depth)
    have e : ((F.blockSide ^ (F.top - F.depth) : ℕ) : ℝ) = F.blockSide := by
      have : F.top - F.depth = 1 := by simp [BlockFrame.top]
      rw [this]
      simp
    rw [e] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (hE F.depth hj) (by positivity))
theorem boundedOnAdjacentBlocks_const_mul {j : ℕ} {f : F.Site j → Fin 4 → ℝ} {c : F.Site (j + 1) × Fin 4}
    {t σ : ℝ} (hσ : 0 ≤ σ) (h : BoundedOnAdjacentBlocks f c t) :
    BoundedOnAdjacentBlocks (fun x i => σ * f x i) c (σ * t) :=
  ⟨fun g hg k hk => ⟨mul_le_mul_of_nonneg_left (h.1 g hg k hk).1 hσ, mul_le_mul_of_nonneg_left (h.1 g hg k hk).2 hσ⟩,
    fun g hg r hr => mul_le_mul_of_nonneg_left (h.2 g hg r hr) hσ⟩
theorem bondAverageNorm_zero {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    bondAverageNorm X (fun _ _ => 0) c = ‖contourAverage X c‖ := by
  unfold bondAverageNorm expTwistedField
  simp [VariationRates.expUnit_zero]
theorem abs_norm_gaugedBondAverage_sub_le (h : ColdTopHyp del C Cb cc s S R V) {j : ℕ} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) (U : ChainChart F) {t : ℝ} (ht0 : 0 ≤ t)
    (htc : t ≤ cc) (hb : BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) c t) :
    |‖gaugedBondAverage R U j c‖ - ‖contourAverage (R j) c‖| ≤
      C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * t := by
  obtain ⟨hsz1, hsz2⟩ := h.size j c hj hc
  set f0 := levelCoordinateImaginary R U j with hf0
  have hC : 0 ≤ C := by linarith [h.hC]
  set φ : ℝ → ℝ := fun σ => bondAverageNorm (R j) (fun x i => σ • f0 x i) c with hφ
  have hbf : BoundedOnAdjacentBlocks (fun x i => ‖(f0 x i : ℍ[ℝ])‖) c t := hb
  have hder : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∃ d, HasDerivWithinAt φ d (Set.Icc 0 1) σ ∧
      |d| ≤ C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * t := by
    intro σ hσ
    have hbσ : BoundedOnAdjacentBlocks (fun x i => ‖((σ • f0 x i : imaginaryQuaternions) : ℍ[ℝ])‖) c (σ * t) := by
      have h1 := boundedOnAdjacentBlocks_const_mul hσ.1 hbf
      have e : (fun x i => ‖((σ • f0 x i : imaginaryQuaternions) : ℍ[ℝ])‖) = fun x i => σ * ‖(f0 x i : ℍ[ℝ])‖ := by
        funext x i
        show ‖σ • (f0 x i : ℍ[ℝ])‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
      rw [e]
      exact h1
    have hσt : σ * t ≤ t := by nlinarith [hσ.2]
    obtain ⟨han, hbd⟩ := hsz2 (fun x i => σ • f0 x i) (σ * t) (by have := hσ.1; positivity) (hσt.trans htc) hbσ
    have h1 := han 1 ![f0]
    set ψ : ℝ → ℝ := fun q => bondAverageNorm (R j) (fun x i => σ • f0 x i + q • f0 x i) c with hψ
    have hψd : DifferentiableAt ℝ ψ 0 := by
      have h2 := h1.differentiableAt
      have h3 : HasDerivAt (fun q : ℝ => ((fun _ => q) : Fin 1 → ℝ)) (fun _ => (1 : ℝ)) 0 :=
        hasDerivAt_pi.2 fun _ => hasDerivAt_id _
      have h4 := (h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h3 rfl).differentiableAt
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
      simp [ψ]
    have hdb := hbd f0 t ht0 hbf
    refine ⟨deriv ψ 0, ?_, hdb.trans ?_⟩
    · have h2 : HasDerivAt ψ (deriv ψ 0) (σ - σ) := by
        simpa using hψd.hasDerivAt
      have h3 := h2.comp_sub_const σ σ
      refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)).hasDerivWithinAt
      simp only [hψ, hφ]
      congr 1
      funext x i
      rw [← add_smul]
      congr 1
      ring
    · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) ht0
      linarith
  choose! d hd hdb using hder
  have h3 := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := d)
    (C := C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * t)
    (fun σ hσ => hd σ hσ) (fun σ hσ => by simpa using hdb σ hσ)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have e1 : φ 1 = ‖gaugedBondAverage R U j c‖ := by
    rw [hsz1 U]
    simp only [hφ, one_smul]
    rfl
  have e0 : φ 0 = ‖contourAverage (R j) c‖ := by
    simp only [hφ, zero_smul]
    exact bondAverageNorm_zero _ _
  rw [e1, e0] at h3
  simpa using h3
theorem quaternion_abs_re_le (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem abs_re_mul_unit_le (q : ℍ[ℝ]) (g : UnitQuaternion) : |(q * (g : ℍ[ℝ])).re| ≤ ‖q‖ := by
  have h := quaternion_abs_re_le (q * (g : ℍ[ℝ]))
  rwa [norm_mul, norm_coe_unitQuaternion, mul_one] at h
theorem abs_re_mul_unit_le_of_re_eq_zero {Z : ℍ[ℝ]} (hZ : Z.re = 0) (g : UnitQuaternion) :
    |(Z * (g : ℍ[ℝ])).re| ≤ ‖Z‖ * ‖(g : ℍ[ℝ]) - 1‖ := by
  have e : (Z * (g : ℍ[ℝ])).re = (Z * ((g : ℍ[ℝ]) - 1)).re := by
    rw [mul_sub, mul_one, Quaternion.re_sub, hZ, sub_zero]
  rw [e]
  have h := quaternion_abs_re_le (Z * ((g : ℍ[ℝ]) - 1))
  rwa [norm_mul] at h
theorem norm_inv_coe_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem norm_coe_mul_sub_one_le (x y : UnitQuaternion) :
    ‖((x * y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(x : ℍ[ℝ]) - 1‖ + ‖(y : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem norm_one_sub_exp_add_le {w : ℍ[ℝ]} (hw : w.re = 0) (h1 : ‖w‖ ≤ 1) :
    ‖1 - NormedSpace.exp w + w‖ ≤ ‖w‖ ^ 2 := by
  by_cases h0 : w = 0
  · subst h0
    simp
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 h0
  have hs : Real.sin r / r = Real.sinc r := by
    rw [Real.sinc_of_ne_zero hr0.ne']
  have e : 1 - NormedSpace.exp w + w = ((1 - Real.cos r : ℝ) : ℍ[ℝ]) + (1 - Real.sinc r) • w := by
    rw [exp_eq_of_re_eq_zero hw, ← hr, hs, sub_smul, one_smul]
    simp only [Quaternion.coe_sub, Quaternion.coe_one]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Quaternion.norm_coe, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← hr]
  have hc := Real.one_sub_sq_div_two_le_cos (x := r)
  have hc1 := Real.cos_le_one r
  rw [abs_of_nonneg (by linarith)]
  have h2 := abs_sinc_sub_one_le hr0.le h1
  rw [abs_sub_comm] at h2
  have h3 : |1 - Real.sinc r| * r ≤ r ^ 2 / 4 * 1 :=
    mul_le_mul h2 h1 hr0.le (by positivity)
  nlinarith
theorem one_sub_re_coe_eq (g : UnitQuaternion) :
    1 - ((g : UnitQuaternion) : ℍ[ℝ]).re = ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by apply _root_.YangMills.Construction.MisfitVariation.one_sub_re_eq_distFromOne_sq <;> assumption
theorem norm_coe_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
theorem ray_zero (A : ChainChart F) : ray A 0 = zeroChart F := by
  show (⟨_, _⟩ : ChainChart F) = ⟨_, _⟩
  congr 1
  · funext x i
    simp [zeroChart]
  · funext j y i
    simp [zeroChart]
theorem gaugedBondAverage_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) :
    gaugedBondAverage R (zeroChart F) j c = contourAverage (R j) c := by
  unfold gaugedBondAverage
  rw [chartField_zeroChart hodd]
  have e : balancingGauge (R j) (R j) = fun _ => 1 := funext (balancingGauge_self hodd (R j))
  rw [e, gaugedContourAverage_one]
theorem bondAverageGap_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ) (c : F.Site (j + 1) × Fin 4) :
    bondAverageGap R (zeroChart F) j c = 1 := by
  unfold bondAverageGap
  rw [gaugedBondAverage_zeroChart hodd]
  simp
def plaquetteRate (R : F.FieldChain) (A : ChainChart F) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  - (linearizedCurl (R 0) A.fine p * ((plaquetteHolonomy (R 0) p : UnitQuaternion) : ℍ[ℝ])).re
def innerRate (R : F.FieldChain) (A : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  - (‖contourAverage (R j) c‖ * (((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) *
    ((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ])).re)
def topRate (R : F.FieldChain) (A : ChainChart F) (c : F.Site (F.depth + 1) × Fin 4) : ℝ :=
  - (‖contourAverage (R F.depth) c‖ *
    (linearPart R A (F.depth + 1) c.1 c.2 * (((referenceDefect R F.depth c)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re)
def firstVariationFunctional (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, plaquetteRate R A p +
    a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c +
      ∑ c ∈ innerBonds S (F.depth + 1), topRate R A c)
def innerDefect (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  1 - ((expUnit ((ray A τ).coarse j c.1 c.2) * referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]).re
def topDefect (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) (c : F.Site (F.depth + 1) × Fin 4) : ℝ :=
  1 - ((bondAverageGap R (ray A τ) F.depth c * (referenceDefect R F.depth c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re
def smoothPart (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (τ : ℝ) : ℝ :=
  wilsonAction S (chartField R (ray A τ) 0) +
    a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), ‖contourAverage (R j) c‖ * innerDefect R A τ j c
theorem hasDerivAt_smoothPart (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) :
    HasDerivAt (smoothPart a S R A) (∑ p ∈ innerPlaquettes S 0, plaquetteRate R A p +
      a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c) 0 := by
  unfold smoothPart
  refine (hasDerivAt_wilsonAction_chartMove S R A).add (HasDerivAt.const_mul a ?_)
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun c _ => ?_
  unfold innerRate
  have h1 := (VariationRates.hasDerivAt_expUnit_smul (A.coarse j c.1 c.2)).mul_const
    ((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ])
  have hr := (ChartCoordinates.reCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h2 := (hr.const_sub (1 : ℝ)).const_mul ‖contourAverage (R j) c‖
  have h3 : HasDerivAt (fun τ : ℝ => ‖contourAverage (R j) c‖ * innerDefect R A τ j c)
      (‖contourAverage (R j) c‖ * -((((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) *
        ((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ])).re)) 0 := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    have e : (ray A τ).coarse j c.1 c.2 = τ • A.coarse j c.1 c.2 := by
      show (0 : imaginaryQuaternions) + τ • A.coarse j c.1 c.2 = _
      simp
    simp only [innerDefect, e]
    rfl
  rw [mul_neg] at h3
  exact h3
theorem chartAction_ray_sub_eq (h : ColdTopHyp del C Cb cc s S R V) (a : ℝ) (A : ChainChart F) (τ : ℝ) :
    chartAction a S R (ray A τ) V - chartAction a S R (ray A 0) V - τ * firstVariationFunctional a S R A =
      (smoothPart a S R A τ - smoothPart a S R A 0 - τ * (∑ p ∈ innerPlaquettes S 0, plaquetteRate R A p +
        a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c)) +
      a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c +
        ∑ c ∈ innerBonds S (F.depth + 1),
          ((‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
          (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c))) := by
  have hz : ray A 0 = zeroChart F := ray_zero A
  have e1 := chartAction_eq_sum a S R (ray A τ) V h.top
  have e0 := chartAction_eq_sum a S R (ray A 0) V h.top
  rw [e1, e0]
  have l0 : ∀ j (c : F.Site (j + 1) × Fin 4),
      innerFit R (ray A 0) j c = ‖contourAverage (R j) c‖ * innerDefect R A 0 j c := by
    intro j c
    unfold innerFit innerDefect
    rw [hz, gaugedBondAverage_zeroChart h.odd]
  have t0 : ∀ c : F.Site (F.depth + 1) × Fin 4,
      topFit R (ray A 0) c = ‖contourAverage (R F.depth) c‖ * topDefect R A 0 c := by
    intro c
    unfold topFit topDefect
    rw [hz, gaugedBondAverage_zeroChart h.odd]
  have lt : ∀ j (c : F.Site (j + 1) × Fin 4), innerFit R (ray A τ) j c =
      ‖contourAverage (R j) c‖ * innerDefect R A τ j c +
        (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c := by
    intro j c
    have : innerFit R (ray A τ) j c = ‖gaugedBondAverage R (ray A τ) j c‖ * innerDefect R A τ j c := rfl
    rw [this]
    ring
  have tt : ∀ c : F.Site (F.depth + 1) × Fin 4, topFit R (ray A τ) c =
      ‖contourAverage (R F.depth) c‖ * topDefect R A τ c +
        (‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c := by
    intro c
    have : topFit R (ray A τ) c = ‖gaugedBondAverage R (ray A τ) F.depth c‖ * topDefect R A τ c := rfl
    rw [this]
    ring
  have s1 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerFit R (ray A τ) j c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), ‖contourAverage (R j) c‖ * innerDefect R A τ j c +
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
        (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => lt j c
  have s0 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerFit R (ray A 0) j c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), ‖contourAverage (R j) c‖ * innerDefect R A 0 j c :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => l0 j c
  have u1 : ∑ c ∈ innerBonds S (F.depth + 1), topFit R (ray A τ) c =
      ∑ c ∈ innerBonds S (F.depth + 1), ‖contourAverage (R F.depth) c‖ * topDefect R A τ c +
      ∑ c ∈ innerBonds S (F.depth + 1),
        (‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => tt c
  have u0 : ∑ c ∈ innerBonds S (F.depth + 1), topFit R (ray A 0) c =
      ∑ c ∈ innerBonds S (F.depth + 1), ‖contourAverage (R F.depth) c‖ * topDefect R A 0 c :=
    Finset.sum_congr rfl fun c _ => t0 c
  have u2 : ∑ c ∈ innerBonds S (F.depth + 1),
      ((‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
      (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c)) =
      ∑ c ∈ innerBonds S (F.depth + 1),
        (‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
      (∑ c ∈ innerBonds S (F.depth + 1), ‖contourAverage (R F.depth) c‖ * topDefect R A τ c -
        ∑ c ∈ innerBonds S (F.depth + 1), ‖contourAverage (R F.depth) c‖ * topDefect R A 0 c -
        τ * ∑ c ∈ innerBonds S (F.depth + 1), topRate R A c) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [s1, s0, u1, u0, u2]
  unfold smoothPart firstVariationFunctional
  ring
theorem add_sq_div_two_le (x y : ℝ) : (x + y) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
theorem bondHullSum_ray_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) {m : ℕ} (hm : m < F.top) {c : F.Site (m + 1) × Fin 4}
    (hc : c ∈ innerBonds S (m + 1)) :
    bondHullSum c (rayCoordNorm R A τ m) ≤ δ :=
  (le_mul_of_one_le_const h.hC (bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ m))).trans (hs.hull m hm c hc)
theorem abs_inner_remainder_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (hδ : δ ≤ 1 / 2) (hCs : C * s ≤ 1 / 2) {j : ℕ} (hj : j + 1 < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    |(‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c| ≤
      bondHullSum c (rayCoordNorm R A τ j) * (δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2) := by
  have hτ := hs.τ0.le
  set t := bondHullSum c (rayCoordNorm R A τ j) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ j)
  have htδ : C * t ≤ δ := hs.hull j (by omega) c hc
  have hC : 0 ≤ C := by linarith [h.hC]
  have htc : t ≤ cc := (bondHullSum_ray_le h hs (by omega) hc).trans hs.δc
  have h1 := abs_norm_gaugedBondAverage_sub_le h (by omega) hc (ray A τ) ht0 htc
    (boundedOnAdjacentBlocks_bondHullSum c (rayCoordNorm_nonneg R A τ j))
  have hl0 := scaleAt_nonneg h.odd (j + 1)
  have hl1 := scaleAt_le_one h.odd (j + 1)
  have h2 : C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * t ≤ t := by
    have h3 : C * (s * scaleAt F (j + 1) ^ 2) ≤ C * s := by
      have : s * scaleAt F (j + 1) ^ 2 ≤ s * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ h.s0.le
        nlinarith
      nlinarith
    have h4 : C * (t + s * scaleAt F (j + 1) ^ 2) ≤ 1 := by
      have : C * (t + s * scaleAt F (j + 1) ^ 2) = C * t + C * (s * scaleAt F (j + 1) ^ 2) := by ring
      rw [this]
      linarith
    calc _ ≤ 1 * t := mul_le_mul_of_nonneg_right h4 ht0
      _ = t := one_mul t
  have h5 := h1.trans h2
  set g := expUnit ((ray A τ).coarse j c.1 c.2) * referenceDefect R j c with hg
  have he : innerDefect R A τ j c = ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 2 := one_sub_re_coe_eq g
  have he0 : 0 ≤ innerDefect R A τ j c := by
    rw [he]
    positivity
  have h6 : ‖(g : ℍ[ℝ]) - 1‖ ≤ δ + Cb * s * scaleAt F (j + 1) ^ 3 := by
    refine (norm_coe_mul_sub_one_le _ _).trans (add_le_add ?_ (h.mis_low j hj c hc))
    refine (norm_coe_expUnit_sub_one_le _).trans ?_
    rw [ray_coarse, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    exact (le_mul_of_one_le_const h.hC (by positivity)).trans (hs.mu j hj c hc)
  have h7 : innerDefect R A τ j c ≤ δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 := by
    rw [he]
    refine le_trans ?_ (add_sq_div_two_le δ (Cb * s * scaleAt F (j + 1) ^ 3))
    have := pow_le_pow_left₀ (norm_nonneg _) h6 2
    linarith
  rw [abs_mul, abs_of_nonneg he0]
  exact mul_le_mul h5 h7 he0 ht0
theorem norm_bondAngle_ray_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (hδ : δ ≤ 1 / 2) (hCs : C * s ≤ 1 / 2) {c : F.Site (F.depth + 1) × Fin 4}
    (hc : c ∈ innerBonds S (F.depth + 1)) :
    ‖bondAngle R (ray A τ) F.depth c‖ ≤ 2 * bondHullSum c (rayCoordNorm R A τ F.depth) := by
  have h1 := bondAngle_ray_sub_le h hs hc
  set t := bondHullSum c (rayCoordNorm R A τ F.depth) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ F.depth)
  have h2 := (norm_parallelAverage_le_lineBlockAverage h.odd (R F.depth)
    (levelCoordinate R (ray A τ) F.depth) c).trans (lineBlockAverage_le_bondHullSum h.odd c fun _ _ => norm_nonneg _)
  have h3 : (δ + C * s) * t ≤ t := by nlinarith
  have e : bondAngle R (ray A τ) F.depth c =
      (bondAngle R (ray A τ) F.depth c - parallelAverage (R F.depth) (levelCoordinate R (ray A τ) F.depth) c) +
        parallelAverage (R F.depth) (levelCoordinate R (ray A τ) F.depth) c := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h4 : bondHullSum c (fun x i => ‖levelCoordinate R (ray A τ) F.depth x i‖) = t := rfl
  rw [h4] at h2
  linarith
theorem abs_top_remainder_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (hδ : δ ≤ 1 / 2) (hCs : C * s ≤ 1 / 2) {c : F.Site (F.depth + 1) × Fin 4}
    (hc : c ∈ innerBonds S (F.depth + 1)) :
    |(‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c| ≤
      bondHullSum c (rayCoordNorm R A τ F.depth) * (δ * (4 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) := by
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  set t := bondHullSum c (rayCoordNorm R A τ F.depth) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ F.depth)
  have htδ : C * t ≤ δ := hs.hull F.depth hj c hc
  have htδ' : t ≤ δ := bondHullSum_ray_le h hs hj hc
  have hC : 0 ≤ C := by linarith [h.hC]
  have htc : t ≤ cc := htδ'.trans hs.δc
  have h1 := abs_norm_gaugedBondAverage_sub_le h hj hc (ray A τ) ht0 htc
    (boundedOnAdjacentBlocks_bondHullSum c (rayCoordNorm_nonneg R A τ F.depth))
  rw [scaleAt_top_eq_one] at h1
  have hs0 := h.s0
  have hs1 := h.s1
  have h2 : C * (t + s * 1 ^ 2) * t ≤ (δ + C * s) * t := by
    refine mul_le_mul_of_nonneg_right ?_ ht0
    nlinarith
  set g := bondAverageGap R (ray A τ) F.depth c * (referenceDefect R F.depth c)⁻¹ with hg
  have he : topDefect R A τ c = ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 2 := one_sub_re_coe_eq g
  have he0 : 0 ≤ topDefect R A τ c := by
    rw [he]
    positivity
  have h6 : ‖(g : ℍ[ℝ]) - 1‖ ≤ 2 * t + Cb * s := by
    refine (norm_coe_mul_sub_one_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_coe_sub_one_le_norm_unitQuaternionLog _).trans (norm_bondAngle_ray_le h hs hδ hCs hc)
    · rw [norm_inv_coe_sub_one]
      exact h.mis_top c hc
  have h7 : topDefect R A τ c ≤ 4 * δ + (Cb * s) ^ 2 := by
    rw [he]
    have h8 := pow_le_pow_left₀ (norm_nonneg _) h6 2
    have h9 := add_sq_div_two_le (2 * t) (Cb * s)
    have h10 : (2 * t) ^ 2 ≤ 4 * δ := by nlinarith
    linarith
  rw [abs_mul, abs_of_nonneg he0]
  have hδ0 := hs.δ0
  calc _ ≤ ((δ + C * s) * t) * (4 * δ + (Cb * s) ^ 2) := mul_le_mul (h1.trans h2) h7 he0 (by positivity)
    _ = t * ((δ + C * s) * (4 * δ + (Cb * s) ^ 2)) := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ ht0
        have e1 : (δ + C * s) * (4 * δ) ≤ 4 * δ := by nlinarith
        have e2 : δ * (Cb * s) ^ 2 ≤ δ * Cb ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hδ0
          rw [mul_pow]
          exact mul_le_of_le_one_right (sq_nonneg Cb) (pow_le_one₀ hs0.le hs1)
        have e3 : C * s * (Cb * s) ^ 2 ≤ C * Cb ^ 2 * s ^ 2 := by
          have : C * s * (Cb * s) ^ 2 = (C * Cb ^ 2 * s ^ 2) * s := by ring
          rw [this]
          have : 0 ≤ C * Cb ^ 2 * s ^ 2 := by positivity
          nlinarith
        nlinarith
theorem re_linearPart (R : F.FieldChain) (A : ChainChart F) (j : ℕ) (x : F.Site j) (i : Fin 4) :
    (linearPart R A j x i).re = 0 := by apply _root_.YangMills.Construction.TopAverageCurl.re_linearPart <;> assumption
theorem abs_top_main_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (hδ : δ ≤ 1 / 2) (hCs : C * s ≤ 1 / 2) {c : F.Site (F.depth + 1) × Fin 4}
    (hc : c ∈ innerBonds S (F.depth + 1)) :
    |‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c| ≤
      4 * δ * bondHullSum c (rayCoordNorm R A τ F.depth) + Cb * s * ‖topLinearGap R A τ c.1 c.2‖ := by
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  set t := bondHullSum c (rayCoordNorm R A τ F.depth) with ht
  have ht0 : 0 ≤ t := bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ F.depth)
  have htδ' : t ≤ δ := bondHullSum_ray_le h hs hj hc
  set mi := (referenceDefect R F.depth c)⁻¹ with hmi
  set gg := bondAverageGap R (ray A τ) F.depth c with hgg
  set ν := bondAngle R (ray A τ) F.depth c with hν
  set r := ‖contourAverage (R F.depth) c‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := VariationRates.norm_contourAverage_le_one h.odd _ _
  have hν0 : ν.re = 0 := re_unitQuaternionLog _
  have hνe : NormedSpace.exp ν = (gg : ℍ[ℝ]) := exp_unitQuaternionLog _
  have hνn := norm_bondAngle_ray_le h hs hδ hCs hc
  rw [← hν, ← ht] at hνn
  have hν1 : ‖ν‖ ≤ 1 := by linarith
  set Z := topLinearGap R A τ c.1 c.2 with hZ
  have hZe : ν = Z + τ • linearPart R A (F.depth + 1) c.1 c.2 := by
    rw [hZ]
    unfold topLinearGap
    simp
    rfl
  have hZ0 : Z.re = 0 := by
    rw [hZ]
    unfold topLinearGap
    simp only [Quaternion.re_sub, Quaternion.re_smul, re_linearPart]
    have : (bondAngle R (ray A τ) F.depth (c.1, c.2)).re = 0 := re_unitQuaternionLog _
    rw [this]
    simp
  have e0 : topDefect R A 0 c = 1 - ((mi : UnitQuaternion) : ℍ[ℝ]).re := by
    unfold topDefect
    rw [ray_zero, bondAverageGap_zeroChart h.odd, one_mul]
  have e1 : topDefect R A τ c = 1 - (((gg : ℍ[ℝ])) * ((mi : UnitQuaternion) : ℍ[ℝ])).re := rfl
  set q := 1 - NormedSpace.exp ν + ν with hq
  have hqn : ‖q‖ ≤ ‖ν‖ ^ 2 := norm_one_sub_exp_add_le hν0 hν1
  have key : topDefect R A τ c - topDefect R A 0 c =
      (q * ((mi : UnitQuaternion) : ℍ[ℝ])).re - (Z * ((mi : UnitQuaternion) : ℍ[ℝ])).re -
        τ * (linearPart R A (F.depth + 1) c.1 c.2 * ((mi : UnitQuaternion) : ℍ[ℝ])).re := by
    rw [e0, e1, hq, hνe]
    have e2 : (1 - (gg : ℍ[ℝ]) + ν) * ((mi : UnitQuaternion) : ℍ[ℝ]) =
        ((mi : UnitQuaternion) : ℍ[ℝ]) - (gg : ℍ[ℝ]) * ((mi : UnitQuaternion) : ℍ[ℝ]) +
          Z * ((mi : UnitQuaternion) : ℍ[ℝ]) +
          τ • (linearPart R A (F.depth + 1) c.1 c.2 * ((mi : UnitQuaternion) : ℍ[ℝ])) := by
      rw [hZe, add_mul, sub_mul, one_mul, add_mul, smul_mul_assoc]
      abel
    rw [e2]
    simp only [Quaternion.re_add, Quaternion.re_sub, Quaternion.re_smul, smul_eq_mul]
    ring
  have e3 : topRate R A c = - (r * (linearPart R A (F.depth + 1) c.1 c.2 * ((mi : UnitQuaternion) : ℍ[ℝ])).re) := rfl
  have e4 : r * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c =
      r * ((q * ((mi : UnitQuaternion) : ℍ[ℝ])).re - (Z * ((mi : UnitQuaternion) : ℍ[ℝ])).re) := by
    rw [key, e3]
    ring
  rw [e4, abs_mul, abs_of_nonneg hr0]
  have h1 := abs_re_mul_unit_le q mi
  have h2 := abs_re_mul_unit_le_of_re_eq_zero hZ0 mi
  rw [hmi, norm_inv_coe_sub_one, ← hmi] at h2
  have h3 : ‖((referenceDefect R F.depth c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cb * s := h.mis_top c hc
  have h4 : |(q * ((mi : UnitQuaternion) : ℍ[ℝ])).re - (Z * ((mi : UnitQuaternion) : ℍ[ℝ])).re| ≤
      ‖ν‖ ^ 2 + ‖Z‖ * (Cb * s) := by
    refine (abs_sub _ _).trans (add_le_add (h1.trans hqn) (h2.trans ?_))
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  have h5 : ‖ν‖ ^ 2 ≤ 4 * δ * t := by
    have h6 := pow_le_pow_left₀ (norm_nonneg _) hνn 2
    nlinarith
  calc r * _ ≤ 1 * (‖ν‖ ^ 2 + ‖Z‖ * (Cb * s)) := mul_le_mul hr1 h4 (abs_nonneg _) zero_le_one
    _ ≤ _ := by nlinarith
theorem sum_innerBonds_le_sum_cellBall (h : ColdTopHyp del C Cb cc s S R V) {l : ℕ} (hl : l ≤ F.top)
    (G : F.Site l × Fin 4 → ℝ) (hG : ∀ b, 0 ≤ G b) :
    ∑ b ∈ innerBonds S l, G b ≤ ∑ z ∈ S, ∑ b ∈ innerBonds (cellBall S z 1) l, G b := by
  classical
  have hmaps : ∀ b ∈ innerBonds S l, enclosingCell b.1 ∈ S := fun b hb =>
    enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
  intro b hb
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  refine mem_innerBonds_cellBall_of_mem_bondsOver h.amb h.odd S z hl ?_
  unfold bondsOver
  exact Finset.mem_filter.2 ⟨h1, by simp [h2]⟩
theorem sum_bondHullSum_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ : ℝ} (hτ : 0 ≤ τ)
    (p : F.Site 0) {θ : ℝ} (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) {Ez : F.Cell → ℝ}
    (hE : ∀ z ∈ S, ∀ m, m < F.top → weightedScaleNorm (cellBall S z 1) p (-θ) 4 m (rayCoordNorm R A τ m) ≤ τ * Ez z)
    {m : ℕ} (hm : m < F.top) :
    ∑ c ∈ innerBonds S (m + 1), bondHullSum c (rayCoordNorm R A τ m) ≤
      240 * hullFactor F.blockSide * F.blockSide * ((F.blockSide ^ (F.top - (m + 1)) : ℕ) : ℝ) ^ 3 *
        (((F.blockSide : ℝ) ^ F.top) ^ (-θ) * τ * ∑ z ∈ S, Ez z) := by
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast h.odd.pos
  have hϑ : |(-θ)| ≤ 1 / 8 := by
    rw [abs_neg, abs_of_nonneg h0]
    exact h8
  have hF0 := zero_le_hullFactor F.blockSide
  refine (sum_innerBonds_le_sum_cellBall h (by omega) (fun c => bondHullSum c (rayCoordNorm R A τ m))
    (fun c => bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ m))).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  set Q : ℝ := ((F.blockSide ^ (F.top - (m + 1)) : ℕ) : ℝ) with hQ
  set Nθ : ℝ := ((F.blockSide : ℝ) ^ F.top) ^ (-θ) with hNθ
  have hD := card_cellBall_one_le S z
  have h1 := sum_innerBonds_le_weightedScaleNorm h.odd (l := m + 1) (by omega) hD p h0 h8
    (f := fun y d => bondHullSum (y, d) (rayCoordNorm R A τ m))
    (fun _ _ => bondHullSum_nonneg _ (rayCoordNorm_nonneg R A τ m))
  have h2 := weightedScaleNorm_bondHullSum_le (D := cellBall S z 1) h.odd hϑ (j := m) hm p 2 (by norm_num)
    (rayCoordNorm_nonneg R A τ m)
  have h3 := weightedScaleNorm_two_le_four h.odd hD p (-θ) m (rayCoordNorm R A τ m)
  have h4 := hE z hz m hm
  have eQ : ((F.blockSide ^ (F.top - m) : ℕ) : ℝ) = F.blockSide * Q := by
    rw [hQ]
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  rw [eQ] at h3
  have h5 : weightedScaleNorm (cellBall S z 1) p (-θ) 2 m (rayCoordNorm R A τ m) ≤
      5 * (F.blockSide * Q) * (τ * Ez z) :=
    h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  calc ∑ b ∈ innerBonds (cellBall S z 1) (m + 1), bondHullSum b (rayCoordNorm R A τ m) ≤ 48 * Q ^ 2 * Nθ *
        weightedScaleNorm (cellBall S z 1) p (-θ) 2 (m + 1)
          (fun y d => bondHullSum (y, d) (rayCoordNorm R A τ m)) := h1
    _ ≤ 48 * Q ^ 2 * Nθ * (hullFactor F.blockSide * (5 * (F.blockSide * Q) * (τ * Ez z))) := by
        refine mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h5 hF0)) (by positivity)
    _ = _ := by ring
theorem sum_norm_topLinearGap_le (h : ColdTopHyp del C Cb cc s S R V) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (p : F.Site 0) {θ : ℝ} (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) {Ez : F.Cell → ℝ}
    (hE : ∀ z ∈ S, ∀ m, m < F.top → weightedScaleNorm (cellBall S z 1) p (-θ) 4 m (rayCoordNorm R A τ m) ≤ τ * Ez z) :
    ∑ c ∈ innerBonds S (F.depth + 1), ‖topLinearGap R A τ c.1 c.2‖ ≤
      48 * (hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * (F.blockSide : ℝ) ^ F.top * δ + C * (1 + Cb) * s * F.blockSide)))) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide))) *
        (((F.blockSide : ℝ) ^ F.top) ^ (-θ) * τ * ∑ z ∈ S, Ez z) := by
  have hϑ : |(-θ)| ≤ 1 / 8 := by
    rw [abs_neg, abs_of_nonneg h0]
    exact h8
  refine (sum_innerBonds_le_sum_cellBall h (by simp [BlockFrame.top]) (fun c => ‖topLinearGap R A τ c.1 c.2‖)
    (fun _ => norm_nonneg _)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hD := card_cellBall_one_le S z
  have hSub : cellBall S z 1 ⊆ S := cellBall_subset S z 1
  have h1 := sum_innerBonds_le_weightedScaleNorm h.odd (l := F.depth + 1) (by simp [BlockFrame.top]) hD p h0 h8
    (f := fun y d => ‖topLinearGap R A τ y d‖) (fun _ _ => norm_nonneg _)
  have h2 := weightedScaleNorm_two_topLinearGap_le h hs hSub hD p hϑ (hE z hz)
  have eQ : ((F.blockSide ^ (F.top - (F.depth + 1)) : ℕ) : ℝ) = 1 := by
    have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
    rw [this]
    simp
  rw [eQ] at h1
  set Nθ : ℝ := ((F.blockSide : ℝ) ^ F.top) ^ (-θ) with hNθ
  refine h1.trans ?_
  calc 48 * 1 ^ 2 * Nθ * _ ≤ 48 * 1 ^ 2 * Nθ * _ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring
def sqCoefficient (L : ℕ) (C Cb : ℝ) : ℝ :=
  240 * hullFactor L * L * (2 * Cb ^ 2 + C * Cb ^ 2) +
    Cb * 48 * (hullFactor L * 284 * hullFactor L * 5 * (C * (1 + Cb) * L) + C * (hullFactor L * 5 * L))
def stepCoefficient (L t : ℕ) (N C Cb : ℝ) : ℝ :=
  240 * hullFactor L * L * ((t : ℝ) * N ^ 3 + 8 + Cb ^ 2) +
    Cb * 48 * (hullFactor L * 284 * hullFactor L * 5 * (2 * N) + hullFactor L * 5 * L)
theorem sum_scaleAt_le_two (h2 : 2 ≤ F.blockSide) : ∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) ≤ 2 := by
  have hL : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (sum_inv_pow_le_two hL F.depth)
  have hj' := Finset.mem_range.1 hj
  refine pow_le_pow_of_le_one (by positivity) ?_ (by simp only [BlockFrame.top]; omega)
  rw [div_le_one (by linarith)]
  linarith
theorem abs_remainder_le (h : ColdTopHyp del C Cb cc s S R V) {a : ℝ} (ha : 0 ≤ a) {A : ChainChart F} {τ δ : ℝ}
    (hs : IsSmallStep C cc S R A τ δ) (hδ : δ ≤ 1 / 2) (hCs : C * s ≤ 1 / 2) (p : F.Site 0) {θ : ℝ} (h0 : 0 ≤ θ)
    (h8 : θ ≤ 1 / 8) {Ez : F.Cell → ℝ} (hEz : ∀ z ∈ S, 0 ≤ Ez z)
    (hE : ∀ z ∈ S, ∀ m, m < F.top → weightedScaleNorm (cellBall S z 1) p (-θ) 4 m (rayCoordNorm R A τ m) ≤ τ * Ez z) :
    |a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c +
        ∑ c ∈ innerBonds S (F.depth + 1),
          ((‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
          (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c)))| ≤
      τ * (a * ((((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ∑ z ∈ S, Ez z) *
        (sqCoefficient F.blockSide C Cb * s ^ 2 +
          stepCoefficient F.blockSide F.depth ((F.blockSide : ℝ) ^ F.top) C Cb * δ))) := by
  have hτ := hs.τ0.le
  have hδ0 := hs.δ0
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast h.odd.pos
  have hCb := h.hCb
  have hC0 : 0 ≤ C := by linarith [h.hC]
  have hs0 := h.s0
  have hs1 := h.s1
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  set Nθ : ℝ := N ^ (-θ) with hNθ
  set Sz := ∑ z ∈ S, Ez z with hSz
  have hSz0 : 0 ≤ Sz := Finset.sum_nonneg hEz
  set W := Nθ * τ * Sz with hW
  set H : ℝ := 240 * hullFactor F.blockSide * F.blockSide with hH
  have hF0 := zero_le_hullFactor F.blockSide
  have hlow : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      |(‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c| ≤
      H * W * ((F.depth : ℝ) * δ * N ^ 3 + 2 * (Cb ^ 2 * s ^ 2)) := by
    have hj : ∀ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
        |(‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c| ≤
        H * W * (δ * N ^ 3 + Cb ^ 2 * s ^ 2 * scaleAt F (j + 1)) := by
      intro j hjr
      have hj1 : j + 1 < F.top := by
        have := Finset.mem_range.1 hjr
        simp only [BlockFrame.top]
        omega
      have h1 : ∑ c ∈ innerBonds S (j + 1),
          |(‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c| ≤
          ∑ c ∈ innerBonds S (j + 1),
            bondHullSum c (rayCoordNorm R A τ j) * (δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2) :=
        Finset.sum_le_sum fun c hc => abs_inner_remainder_le h hs hδ hCs hj1 hc
      rw [← Finset.sum_mul] at h1
      have h2 := sum_bondHullSum_le h hτ p h0 h8 hE (m := j) (by omega)
      set Q : ℝ := ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) with hQ
      have hQ0 : 0 ≤ Q := by positivity
      have hQl : Q * scaleAt F (j + 1) = 1 := blockCount_mul_scaleAt h.odd (j + 1)
      have hQN : Q ≤ N := blockCount_le h.odd (j + 1)
      have hl0 := scaleAt_nonneg h.odd (j + 1)
      have hl1 := scaleAt_le_one h.odd (j + 1)
      have hx0 : 0 ≤ δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 := by positivity
      refine h1.trans ((mul_le_mul_of_nonneg_right h2 hx0).trans ?_)
      have e1 : Q ^ 3 * (δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2) ≤
          δ * N ^ 3 + Cb ^ 2 * s ^ 2 * scaleAt F (j + 1) := by
        have e2 : Q ^ 3 * (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 = Cb ^ 2 * s ^ 2 * scaleAt F (j + 1) ^ 3 := by
          calc _ = Cb ^ 2 * s ^ 2 * (Q * scaleAt F (j + 1)) ^ 3 * scaleAt F (j + 1) ^ 3 := by ring
            _ = _ := by rw [hQl]; ring
        have e3 : scaleAt F (j + 1) ^ 3 ≤ scaleAt F (j + 1) := by
          calc scaleAt F (j + 1) ^ 3 = scaleAt F (j + 1) * scaleAt F (j + 1) ^ 2 := by ring
            _ ≤ scaleAt F (j + 1) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hl0 hl1) hl0
            _ = _ := by ring
        have e4 : Q ^ 3 * δ ^ 2 ≤ δ * N ^ 3 := by
          have e5 : Q ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hQ0 hQN 3
          have e6 : δ ^ 2 ≤ δ := by nlinarith
          calc Q ^ 3 * δ ^ 2 ≤ N ^ 3 * δ := mul_le_mul e5 e6 (by positivity) (by positivity)
            _ = _ := by ring
        have e7 : Cb ^ 2 * s ^ 2 * scaleAt F (j + 1) ^ 3 ≤ Cb ^ 2 * s ^ 2 * scaleAt F (j + 1) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
        rw [mul_add, e2]
        linarith
      calc 240 * hullFactor F.blockSide * F.blockSide * Q ^ 3 * (Nθ * τ * Sz) *
            (δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2)
          = H * W * (Q ^ 3 * (δ ^ 2 + (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2)) := by
            rw [hH, hW]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left e1 (by positivity)
    refine (Finset.sum_le_sum hj).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := sum_scaleAt_le_two h.two
    have h3 : Cb ^ 2 * s ^ 2 * ∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) ≤ Cb ^ 2 * s ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : ∑ j ∈ Finset.range F.depth, (δ * N ^ 3 + Cb ^ 2 * s ^ 2 * scaleAt F (j + 1)) =
        (F.depth : ℝ) * δ * N ^ 3 + Cb ^ 2 * s ^ 2 * ∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
      ring
    rw [e]
    linarith
  have htop : ∑ c ∈ innerBonds S (F.depth + 1),
      |(‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
        (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c)| ≤
      H * W * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
      Cb * s * (48 * (hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * N * δ + C * (1 + Cb) * s * F.blockSide)))) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide))) * W) := by
    have h1 : ∑ c ∈ innerBonds S (F.depth + 1),
        |(‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
          (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c)| ≤
        ∑ c ∈ innerBonds S (F.depth + 1),
          (bondHullSum c (rayCoordNorm R A τ F.depth) * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
          Cb * s * ‖topLinearGap R A τ c.1 c.2‖) := by
      refine Finset.sum_le_sum fun c hc => ?_
      refine (abs_add_le _ _).trans ?_
      have e1 := abs_top_remainder_le h hs hδ hCs hc
      have e2 := abs_top_main_le h hs hδ hCs hc
      have e3 : bondHullSum c (rayCoordNorm R A τ F.depth) * (δ * (4 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
          (4 * δ * bondHullSum c (rayCoordNorm R A τ F.depth) + Cb * s * ‖topLinearGap R A τ c.1 c.2‖) =
          bondHullSum c (rayCoordNorm R A τ F.depth) * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
          Cb * s * ‖topLinearGap R A τ c.1 c.2‖ := by ring
      rw [← e3]
      exact add_le_add e1 e2
    refine h1.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    have h2 := sum_bondHullSum_le h hτ p h0 h8 hE (m := F.depth) (by simp [BlockFrame.top])
    have eQ : ((F.blockSide ^ (F.top - (F.depth + 1)) : ℕ) : ℝ) = 1 := by
      have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
      rw [this]
      simp
    rw [eQ] at h2
    have h3 := sum_norm_topLinearGap_le h hs p h0 h8 hE
    have hx0 : 0 ≤ δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2 := by positivity
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left h3 (by positivity))
    refine (mul_le_mul_of_nonneg_right h2 hx0).trans (le_of_eq ?_)
    rw [hH, hW]
    ring
  rw [abs_mul, abs_of_nonneg ha]
  have hsum : |∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c +
        ∑ c ∈ innerBonds S (F.depth + 1),
          ((‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
          (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c))| ≤
      H * W * ((F.depth : ℝ) * δ * N ^ 3 + 2 * (Cb ^ 2 * s ^ 2)) +
      (H * W * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
      Cb * s * (48 * (hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * N * δ + C * (1 + Cb) * s * F.blockSide)))) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide))) * W)) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans hlow)
      exact Finset.abs_sum_le_sum_abs _ _
    · exact (Finset.abs_sum_le_sum_abs _ _).trans htop
  have hkey : H * W * ((F.depth : ℝ) * δ * N ^ 3 + 2 * (Cb ^ 2 * s ^ 2)) +
      (H * W * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
      Cb * s * (48 * (hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * N * δ + C * (1 + Cb) * s * F.blockSide)))) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide))) * W)) ≤
      W * (sqCoefficient F.blockSide C Cb * s ^ 2 + stepCoefficient F.blockSide F.depth N C Cb * δ) := by
    have e : W * (sqCoefficient F.blockSide C Cb * s ^ 2 + stepCoefficient F.blockSide F.depth N C Cb * δ) -
        (H * W * ((F.depth : ℝ) * δ * N ^ 3 + 2 * (Cb ^ 2 * s ^ 2)) +
        (H * W * (δ * (8 + Cb ^ 2) + C * Cb ^ 2 * s ^ 2) +
      Cb * s * (48 * (hullFactor F.blockSide * (284 * (hullFactor F.blockSide *
        (5 * (2 * N * δ + C * (1 + Cb) * s * F.blockSide)))) +
        (δ + C * s) * (hullFactor F.blockSide * (5 * F.blockSide))) * W))) =
        W * (Cb * 48 * (hullFactor F.blockSide * 284 * hullFactor F.blockSide * 5 * (2 * N) +
          hullFactor F.blockSide * 5 * F.blockSide)) * δ * (1 - s) := by
      unfold sqCoefficient stepCoefficient
      rw [hH]
      ring
    have h5 : 0 ≤ W * (Cb * 48 * (hullFactor F.blockSide * 284 * hullFactor F.blockSide * 5 * (2 * N) +
        hullFactor F.blockSide * 5 * F.blockSide)) * δ * (1 - s) := by
      have : 0 ≤ 1 - s := by linarith
      positivity
    linarith
  have hfin := hsum.trans hkey
  calc a * _ ≤ a * (W * (sqCoefficient F.blockSide C Cb * s ^ 2 + stepCoefficient F.blockSide F.depth N C Cb * δ)) :=
        mul_le_mul_of_nonneg_left hfin ha
    _ = _ := by
        rw [hW]
        ring
theorem supWeightedNorm_zeroChart (S : Finset F.Cell) (del : ℝ) (hdel : 0 ≤ del) (hL : 0 < F.blockSide)
    (R' : F.FieldChain) : supWeightedNorm S del R' (zeroChart F) = 0 := by
  refine le_antisymm (supWeightedNorm_le _ _ _ _ _ fun y0 => ?_) (supWeightedNorm_nonneg _ _ _ _)
  have hz : ∀ B, localNormSq S B R' (zeroChart F) (decayWeights F del 0 0 y0) = 0 := by
    intro B
    simp [localNormSq, zeroChart, linearizedCurl, _root_.YangMills.Construction.BlockAverages.adjointAction]
  simp [_root_.YangMills.Construction.BlockAverages.weightedNorm, localNorm, hz]
theorem localNorm_zeroChart (S : Finset F.Cell) (R' : F.FieldChain) (w : F.SiteWeights) (z : F.Cell) :
    localNorm S R' (zeroChart F) w z = 0 := by
  simp [localNorm, localNormSq, zeroChart, linearizedCurl, _root_.YangMills.Construction.BlockAverages.adjointAction]
theorem exists_isSmallStep (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ cc) : ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₁ → IsSmallStep C cc S R A τ δ := by
  have hL := h.odd.pos
  have hC0 : 0 ≤ C := by linarith [h.hC]
  have hdel := h.hdel
  set M0 := ∑ z ∈ S, localNorm S R A (constOneWeights F) z with hM0
  have hM00 : 0 ≤ M0 := Finset.sum_nonneg fun _ _ => localNorm_nonneg _ _ _ _ _
  set Nn := supWeightedNorm S del R A with hNn
  have hNn0 : 0 ≤ Nn := supWeightedNorm_nonneg _ _ _ _
  set M1 := ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), ‖A.coarse j c.1 c.2‖ +
    ∑ b ∈ innerBonds S 0, ‖A.fine b.1 b.2‖ with hM1
  have hA0 : 0 ≤ ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), ‖A.coarse j c.1 c.2‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : 0 ≤ ∑ b ∈ innerBonds S 0, ‖A.fine b.1 b.2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hM10 : 0 ≤ M1 := add_nonneg hA0 hB0
  set Hc := hullBondCount F.blockSide with hHc
  have hHc0 : 0 ≤ Hc := by
    rw [hHc]
    unfold hullBondCount
    positivity
  set T := C * (Hc * (C * M0)) + C * M1 with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact add_nonneg (mul_nonneg hC0 (mul_nonneg hHc0 (mul_nonneg hC0 hM00))) (mul_nonneg hC0 hM10)
  clear_value M0 Nn Hc M1 T
  refine ⟨min (cc / (Nn + 1)) (min (δ / (T + 1)) (1 / (8 * (M1 + 1)))), ?_, fun τ hτ hτ1 => ?_⟩
  · have := h.cc0
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have t1 : τ ≤ cc / (Nn + 1) := hτ1.trans (min_le_left _ _)
  have t2 : τ ≤ δ / (T + 1) := hτ1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 : τ ≤ 1 / (8 * (M1 + 1)) := hτ1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have u1 : τ * Nn ≤ cc := by
    have := (le_div_iff₀ (by positivity : 0 < Nn + 1)).1 t1
    nlinarith
  have u2 : τ * T ≤ δ := by
    have := (le_div_iff₀ (by positivity : 0 < T + 1)).1 t2
    nlinarith
  have u3 : τ * M1 ≤ 1 / 8 := by
    have := (le_div_iff₀ (by positivity : 0 < 8 * (M1 + 1))).1 t3
    nlinarith
  have hsup : supWeightedNorm S del R (ray A τ) ≤ cc := by
    have h1 := supWeightedNorm_chartMove_le S hL del hdel.le R (zeroChart F) A τ
    rw [supWeightedNorm_zeroChart S del hdel.le hL, zero_add, abs_of_pos hτ, ← hNn] at h1
    exact h1.trans u1
  have hbond : ∀ m, m < F.top → ∀ b ∈ innerBonds S m, rayCoordNorm R A τ m b.1 b.2 ≤ C * (τ * M0) := by
    intro m hm b hb
    classical
    have hz : enclosingCell b.1 ∈ S :=
      enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    have h1 := h.coords (ray A τ) hsup m hm (enclosingCell b.1) hz
    have hbz : b ∈ bondsOver S {enclosingCell b.1} m := by
      unfold bondsOver
      exact Finset.mem_filter.2 ⟨hb, by simp⟩
    have h2 : rayCoordNorm R A τ m b.1 b.2 ≤
        Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {enclosingCell b.1} m,
          ‖levelCoordinate R (ray A τ) m b.1 b.2‖ ^ 4)) := by
      have h3 : ‖levelCoordinate R (ray A τ) m b.1 b.2‖ ^ 4 ≤
          ∑ b' ∈ bondsOver S {enclosingCell b.1} m, ‖levelCoordinate R (ray A τ) m b'.1 b'.2‖ ^ 4 :=
        Finset.single_le_sum (f := fun b' : F.Site m × Fin 4 => ‖levelCoordinate R (ray A τ) m b'.1 b'.2‖ ^ 4)
          (fun _ _ => by positivity) hbz
      have h4 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h3)
      have h5 : Real.sqrt (Real.sqrt (‖levelCoordinate R (ray A τ) m b.1 b.2‖ ^ 4)) = rayCoordNorm R A τ m b.1 b.2 := by
        rw [show ‖levelCoordinate R (ray A τ) m b.1 b.2‖ ^ 4 =
            (‖levelCoordinate R (ray A τ) m b.1 b.2‖ ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)]
        rfl
      rwa [h5] at h4
    have h6 : localNorm S R (ray A τ) (constOneWeights F) (enclosingCell b.1) ≤ τ * M0 := by
      have h7 := localNorm_chartMove_le S R (zeroChart F) A τ (constOneWeights F)
        (fun _ _ => zero_le_one) (enclosingCell b.1)
      rw [localNorm_zeroChart, zero_add, abs_of_pos hτ] at h7
      refine h7.trans (mul_le_mul_of_nonneg_left ?_ hτ.le)
      rw [hM0]
      exact Finset.single_le_sum (f := fun z => localNorm S R A (constOneWeights F) z)
        (fun _ _ => localNorm_nonneg _ _ _ _ _) hz
    exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left h6 hC0))
  refine ⟨hτ, hδ.le, hδc, fun m hm c hc => ?_, fun m hm c hc => ?_, fun b hb => ?_⟩
  · have h1 : HoldsOnHull c (fun x i => rayCoordNorm R A τ m x i ≤ C * (τ * M0)) :=
      holdsOnHull_of_innerBonds hm h.odd hc fun b hb => hbond m hm b hb
    have h2 := bondHullSum_le h.odd (by positivity) h1
    rw [← hHc] at h2
    have h3 : C * bondHullSum c (rayCoordNorm R A τ m) ≤ C * (Hc * (C * (τ * M0))) :=
      mul_le_mul_of_nonneg_left h2 hC0
    refine h3.trans (le_trans ?_ u2)
    rw [hT]
    have : 0 ≤ τ * (C * M1) := by positivity
    nlinarith
  · have h1 : ‖A.coarse m c.1 c.2‖ ≤ M1 := by
      have h2 : ‖A.coarse m c.1 c.2‖ ≤ ∑ c ∈ innerBonds S (m + 1), ‖A.coarse m c.1 c.2‖ :=
        Finset.single_le_sum (f := fun c : F.Site (m + 1) × Fin 4 => ‖A.coarse m c.1 c.2‖)
          (fun _ _ => norm_nonneg _) hc
      have h3 : ∑ c ∈ innerBonds S (m + 1), ‖A.coarse m c.1 c.2‖ ≤
          ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), ‖A.coarse j c.1 c.2‖ :=
        Finset.single_le_sum (f := fun j => ∑ c ∈ innerBonds S (j + 1), ‖A.coarse j c.1 c.2‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
      linarith
    have h4 : C * (τ * ‖A.coarse m c.1 c.2‖) ≤ C * (τ * M1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hτ.le) hC0
    refine h4.trans (le_trans ?_ u2)
    rw [hT]
    have : 0 ≤ τ * (C * (Hc * (C * M0))) := by positivity
    nlinarith
  · have h1 : ‖A.fine b.1 b.2‖ ≤ M1 := by
      have h2 : ‖A.fine b.1 b.2‖ ≤ ∑ b ∈ innerBonds S 0, ‖A.fine b.1 b.2‖ :=
        Finset.single_le_sum (f := fun b : F.Site 0 × Fin 4 => ‖A.fine b.1 b.2‖) (fun _ _ => norm_nonneg _) hb
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hτ.le).trans u3
theorem abs_deriv_sub_le_of_slope {J G : ℝ → ℝ} {d g' l X : ℝ} (hJ : HasDerivAt J d 0) (hG : HasDerivAt G g' 0)
    (hb : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), |J τ - J 0 - τ * l - (G τ - G 0 - τ * g')| ≤ τ * X) :
    |d - l| ≤ X := by
  have hh := hJ.sub hG
  have h1 := hh.tendsto_slope_zero_right
  have h2 : Filter.Tendsto (fun τ : ℝ => |τ⁻¹ • ((J - G) (0 + τ) - (J - G) 0) - (l - g')|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds |d - g' - (l - g')|) := (h1.sub_const (l - g')).abs
  have h3 : |d - g' - (l - g')| ≤ X := by
    refine le_of_tendsto h2 ?_
    filter_upwards [hb, self_mem_nhdsWithin] with τ h4 h5
    have hτ : 0 < τ := h5
    have e : τ⁻¹ • ((J - G) (0 + τ) - (J - G) 0) - (l - g') =
        τ⁻¹ * (J τ - J 0 - τ * l - (G τ - G 0 - τ * g')) := by
      simp only [Pi.sub_apply, zero_add, smul_eq_mul]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hτ)]
    calc τ⁻¹ * _ ≤ τ⁻¹ * (τ * X) := mul_le_mul_of_nonneg_left h4 (inv_pos.2 hτ).le
      _ = X := by field_simp
  have e : d - g' - (l - g') = d - l := by ring
  rwa [e] at h3
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
def cellFactor (F : BlockFrame) (del θ : ℝ) (y0 z : F.Cell) : ℝ :=
  ((F.blockSide : ℝ) ^ F.top) ^ θ * Real.exp del * Real.exp (-del * cellSupDist z y0)
theorem cellFactor_nonneg (hodd : Odd F.blockSide) (del θ : ℝ) (y0 z : F.Cell) : 0 ≤ cellFactor F del θ y0 z := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold cellFactor
  positivity
theorem scaleWeight_le_cellFactor_mul (hodd : Odd F.blockSide) {del θ : ℝ} (hdel : 0 ≤ del) (p : F.Site 0)
    (y0 z : F.Cell) {j : ℕ} (x : F.Site j) (hx : cellSupDist z (enclosingCell x) ≤ 1) :
    scaleWeight p (-θ) j x ≤ cellFactor F del θ y0 z * invertedWeights (decayWeights F del θ p y0) j x := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hρ := WeightedAverages.Chains.scaleRadius_pos (F := F) hodd.pos j p x
  set ρ := scaleRadius F j p x with hρd
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  have e1 : scaleWeight p (-θ) j x = ρ ^ θ := by
    unfold scaleWeight
    rw [neg_neg]
  have e2 : invertedWeights (decayWeights F del θ p y0) j x =
      Real.exp (del * cellSupDist (enclosingCell x) y0) * (ρ ^ θ / N ^ θ) := by
    unfold invertedWeights decayWeights
    rw [mul_inv, ← Real.exp_neg, ← Real.rpow_neg (by positivity), neg_neg, Real.div_rpow hρ.le hN0.le]
    congr 2
    ring
  rw [e1, e2]
  unfold cellFactor
  have hd : (cellSupDist z y0 : ℝ) ≤ 1 + cellSupDist (enclosingCell x) y0 := by
    have h1 := cellSupDist_triangle z (enclosingCell x) y0
    have h2 : (cellSupDist z y0 : ℝ) ≤ cellSupDist z (enclosingCell x) + cellSupDist (enclosingCell x) y0 := by
      exact_mod_cast h1
    have h3 : (cellSupDist z (enclosingCell x) : ℝ) ≤ 1 := by exact_mod_cast hx
    linarith
  have hρθ : 0 < ρ ^ θ := by positivity
  have h4 : (1 : ℝ) ≤ Real.exp del * Real.exp (-del * cellSupDist z y0) *
      Real.exp (del * cellSupDist (enclosingCell x) y0) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  calc ρ ^ θ ≤ (Real.exp del * Real.exp (-del * cellSupDist z y0) *
        Real.exp (del * cellSupDist (enclosingCell x) y0)) * ρ ^ θ :=
        le_mul_of_one_le_left hρθ.le h4
    _ = _ := by
        field_simp
        rfl
theorem sum_pow_four_le_localNormSq_sq (S B : Finset F.Cell) (R' : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) :
    ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ localNormSq S B R' U w ^ 2 := by
  have h1 : Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤ localNormSq S B R' U w := by
    unfold localNormSq
    have h2 : 0 ≤ ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R' 0) U.fine p‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have h0 : 0 ≤ ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_nonneg fun b _ => by
      have : (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 = ((w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 2) ^ 2 := by ring
      rw [this]
      positivity
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rwa [Real.sq_sqrt h0] at this
theorem sum_curl_sq_le_localNormSq (S B : Finset F.Cell) (R' : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) :
    ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R' 0) U.fine p‖) ^ 2 ≤ localNormSq S B R' U w := by
  unfold localNormSq
  have h2 := Real.sqrt_nonneg (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem sum_coarse_sq_le_localNormSq (S B : Finset F.Cell) (R' : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) :
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      localNormSq S B R' U w := by
  unfold localNormSq
  have h2 := Real.sqrt_nonneg (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R' 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem localNorm_sq_eq (S : Finset F.Cell) (R' : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : localNorm S R' U w z ^ 2 = localNormSq S (cellBall S z 3) R' U w :=
  Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)
theorem cellSupDist_le_of_mem_cellBall {S : Finset F.Cell} {z y : F.Cell} {r : ℕ} (h : y ∈ cellBall S z r) :
    cellSupDist z y ≤ r := by apply _root_.YangMills.Construction.BlockAverages.LevelCoordinates.cellSupDist_le_of_mem_cellBall <;> assumption
theorem weightedScaleNorm_four_fine_le (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) (p : F.Site 0)
    {θ : ℝ} (y0 z : F.Cell) :
    weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖A.fine x i‖) ≤
      cellFactor F del θ y0 z * localNorm S R A (invertedWeights (decayWeights F del θ p y0)) z := by
  set w := invertedWeights (decayWeights F del θ p y0) with hw
  set K := cellFactor F del θ y0 z with hK
  have hK0 : 0 ≤ K := cellFactor_nonneg h.odd _ _ _ _
  unfold weightedScaleNorm
  rw [finsetLpNorm_four_eq_sqrt_sqrt]
  refine sqrt_sqrt_le_of_le_pow_four (mul_nonneg hK0 (localNorm_nonneg _ _ _ _ _)) ?_
  have h1 : ∑ b ∈ innerBonds (cellBall S z 1) 0, (scaleWeight p (-θ) 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ innerBonds (cellBall S z 1) 0, K ^ 4 * (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc : cellSupDist z (enclosingCell b.1) ≤ 1 := cellSupDist_le_of_mem_cellBall
      (enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1)
    have h2 := scaleWeight_le_cellFactor_mul h.odd h.hdel.le p y0 z b.1 hc (θ := θ)
    have h3 : 0 ≤ scaleWeight p (-θ) 0 b.1 * ‖A.fine b.1 b.2‖ :=
      mul_nonneg (scaleWeight_pos h.odd p _ 0 b.1).le (norm_nonneg _)
    have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (A.fine b.1 b.2))
    calc _ ≤ (K * w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 := pow_le_pow_left₀ h3 h4 4
      _ = _ := by ring
  refine h1.trans ?_
  rw [← Finset.mul_sum, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h5 : ∑ b ∈ innerBonds (cellBall S z 1) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall h.odd S z 0 hb)
      fun b _ _ => by
        have : (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 = ((w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 2) ^ 2 := by ring
        rw [this]
        positivity
  refine h5.trans ((sum_pow_four_le_localNormSq_sq S _ R A w).trans (le_of_eq ?_))
  rw [← localNorm_sq_eq]
  ring
theorem weightedScaleNorm_two_coarse_le (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) (p : F.Site 0)
    {θ : ℝ} (y0 z : F.Cell) {m : ℕ} (hm : m + 1 < F.top) :
    weightedScaleNorm (cellBall S z 1) p (-θ) 2 (m + 1) (fun y d => ‖A.coarse m y d‖) ≤
      cellFactor F del θ y0 z * localNorm S R A (invertedWeights (decayWeights F del θ p y0)) z := by
  set w := invertedWeights (decayWeights F del θ p y0) with hw
  set K := cellFactor F del θ y0 z with hK
  have hK0 : 0 ≤ K := cellFactor_nonneg h.odd _ _ _ _
  unfold weightedScaleNorm
  rw [finsetLpNorm_two_eq_sqrt]
  apply Real.sqrt_le_iff.2
  refine ⟨mul_nonneg hK0 (localNorm_nonneg _ _ _ _ _), ?_⟩
  have h1 : ∑ b ∈ innerBonds (cellBall S z 1) (m + 1), (scaleWeight p (-θ) (m + 1) b.1 * ‖A.coarse m b.1 b.2‖) ^ 2 ≤
      ∑ b ∈ innerBonds (cellBall S z 1) (m + 1), K ^ 2 * (w (m + 1) b.1 * ‖A.coarse m b.1 b.2‖) ^ 2 := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc : cellSupDist z (enclosingCell b.1) ≤ 1 := cellSupDist_le_of_mem_cellBall
      (enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1)
    have h2 := scaleWeight_le_cellFactor_mul h.odd h.hdel.le p y0 z b.1 hc (θ := θ)
    have h3 : 0 ≤ scaleWeight p (-θ) (m + 1) b.1 * ‖A.coarse m b.1 b.2‖ :=
      mul_nonneg (scaleWeight_pos h.odd p _ (m + 1) b.1).le (norm_nonneg _)
    have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (A.coarse m b.1 b.2))
    calc _ ≤ (K * w (m + 1) b.1 * ‖A.coarse m b.1 b.2‖) ^ 2 := pow_le_pow_left₀ h3 h4 2
      _ = _ := by ring
  refine h1.trans ?_
  rw [← Finset.mul_sum, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h5 : ∑ b ∈ innerBonds (cellBall S z 1) (m + 1), (w (m + 1) b.1 * ‖A.coarse m b.1 b.2‖) ^ 2 ≤
      ∑ b ∈ bondsOver S (cellBall S z 3) (m + 1), (w (m + 1) b.1 * ‖A.coarse m b.1 b.2‖) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall h.odd S z (m + 1) hb) fun b _ _ => by positivity
  refine h5.trans ?_
  rw [localNorm_sq_eq]
  refine le_trans ?_ (sum_coarse_sq_le_localNormSq S _ R A w)
  exact Finset.single_le_sum (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
    (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_range.2 (by omega))
theorem sum_cellFactor_mul_localNorm_le (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) (w : F.SiteWeights)
    {θ : ℝ} (y0 : F.Cell) :
    ((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z ≤
      Real.exp del * Real.sqrt (expCountSum del) * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast h.odd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  have e1 : N ^ (-θ) * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z =
      Real.exp del * ∑ z ∈ S, Real.exp (-del * cellSupDist z y0) * localNorm S R A w z := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold cellFactor
    have e2 : N ^ (-θ) * N ^ θ = 1 := by
      rw [← Real.rpow_add hN0]
      simp
    calc _ = (N ^ (-θ) * N ^ θ) * Real.exp del * Real.exp (-del * cellSupDist z y0) * localNorm S R A w z := by
          ring
      _ = _ := by rw [e2]; ring
  rw [e1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  refine le_trans (le_of_eq ?_) (sum_exp_cellSupDist_le h.hdel S y0)
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
theorem le_baseTransport_add_sum {D : Finset F.Cell} (hodd : Odd F.blockSide) (a : (m : ℕ) → F.Site m → Fin 4 → ℝ)
    (s' : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (hrec : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + s' m c.1 c.2)
    (m : ℕ) (hm : m ≤ F.top) : ∀ b ∈ innerBonds D m, a m b.1 b.2 ≤
      baseTransport (a 0) m b.1 b.2 + ∑ i ∈ Finset.range m, sourceTransport s' i m b.1 b.2 := by
  induction m with
  | zero => exact fun b _ => by simp [baseTransport]
  | succ m ih =>
    intro c hc
    have h1 := hrec m (by omega) c hc
    have h2 := lineBlockAverage_mono_on (D := D) (f := a m)
      (g := fun x d => baseTransport (a 0) m x d + ∑ i ∈ Finset.range m, sourceTransport s' i m x d)
      (by omega) hodd (ih (by omega)) hc
    rw [lineBlockAverage_add, lineBlockAverage_sum] at h2
    have e0 : sourceTransport s' m (m + 1) c.1 c.2 = s' m c.1 c.2 := by
      simp only [sourceTransport, if_true, sourceTransport_of_le s' m m le_rfl]
      simp [lineBlockAverage]
    have e1 : ∀ i ∈ Finset.range m,
        sourceTransport s' i (m + 1) c.1 c.2 = lineBlockAverage (sourceTransport s' i m) c := by
      intro i hi
      have hne : m ≠ i := by
        have := Finset.mem_range.1 hi
        omega
      simp only [sourceTransport, if_neg hne, add_zero]
    rw [Finset.sum_range_succ, e0, Finset.sum_congr rfl e1]
    have e2 : baseTransport (a 0) (m + 1) c.1 c.2 = lineBlockAverage (baseTransport (a 0) m) c := rfl
    rw [e2]
    linarith
theorem weightedScaleNorm_two_linearPart_top_le (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0) {ϑ : ℝ} (hϑ : |ϑ| ≤ 1 / 8) {n2 : ℝ} (hn2 : 0 ≤ n2)
    (hmu : ∀ m, m + 1 < F.top → weightedScaleNorm D p ϑ 2 (m + 1) (fun y d => ‖A.coarse m y d‖) ≤ n2) :
    weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖linearPart R A (F.depth + 1) y d‖) ≤
      5 * (20000 * weightedScaleNorm D p ϑ 4 0 (fun x i => ‖A.fine x i‖)) + 284 * n2 := by
  classical
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ := fun m x d => ‖linearPart R A m x d‖ with ha
  set sf : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ :=
    fun m y d => if m + 1 < F.top then ‖A.coarse m y d‖ else 0 with hsf
  have hsf0 : ∀ m y d, 0 ≤ sf m y d := fun m y d => by
    simp only [hsf]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hrec : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + sf m c.1 c.2 := by
    intro m _ c _
    have e0 : linearPart R A (m + 1) c.1 c.2 = parallelAverage (R m) (linearPart R A m) (c.1, c.2) +
        (if m + 1 < F.top then ((A.coarse m c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0) := rfl
    have h1 := norm_parallelAverage_le_lineBlockAverage h.odd (R m) (linearPart R A m) c
    show ‖linearPart R A (m + 1) c.1 c.2‖ ≤ _
    rw [e0]
    refine (norm_add_le _ _).trans (add_le_add h1 ?_)
    simp only [hsf]
    split_ifs
    · exact le_rfl
    · simp
  have h1 := le_baseTransport_add_sum (D := D) h.odd a sf hrec (F.depth + 1) (by simp [BlockFrame.top])
  have h2 : weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => ‖linearPart R A (F.depth + 1) y d‖) ≤
      weightedScaleNorm D p ϑ 2 (F.depth + 1) (fun y d => baseTransport (a 0) (F.depth + 1) y d +
        ∑ i ∈ Finset.range (F.depth + 1), sourceTransport sf i (F.depth + 1) y d) := by
    refine weightedScaleNorm_mono_of_abs_le (by norm_num) D p ϑ (F.depth + 1) fun b hb => ?_
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (h1 b hb).trans (le_abs_self _)
  refine h2.trans ((weightedScaleNorm_add_le_add (by norm_num) _ _).trans (add_le_add ?_ ?_))
  · have ha0 : ∀ x d, 0 ≤ a 0 x d := fun _ _ => norm_nonneg _
    have h3 := (baseTransport_norm_le h.odd h.two D p hϑ (a 0) ha0 (F.depth + 1) (by simp [BlockFrame.top])).1
    have h4 := weightedScaleNorm_two_le_four h.odd hD p ϑ (F.depth + 1) (baseTransport (a 0) (F.depth + 1))
    have eQ : ((F.blockSide ^ (F.top - (F.depth + 1)) : ℕ) : ℝ) = 1 := by
      have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
      rw [this]
      simp
    rw [eQ] at h4
    refine h4.trans ?_
    have e1 : weightedScaleNorm D p ϑ 4 0 (a 0) = weightedScaleNorm D p ϑ 4 0 (fun x i => ‖A.fine x i‖) := rfl
    rw [e1] at h3
    linarith
  · have hsum : weightedScaleNorm D p ϑ 2 (F.depth + 1)
          (fun y d => ∑ i ∈ Finset.range (F.depth + 1), sourceTransport sf i (F.depth + 1) y d) ≤
        ∑ i ∈ Finset.range (F.depth + 1), weightedScaleNorm D p ϑ 2 (F.depth + 1) (sourceTransport sf i (F.depth + 1)) := by
      unfold weightedScaleNorm
      refine le_trans (le_of_eq ?_) (finsetLpNorm_sum_le (by norm_num) _ _ _)
      congr 1
      funext b
      rw [Finset.mul_sum]
    refine hsum.trans ?_
    have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h.two
    have hterm : ∀ i ∈ Finset.range (F.depth + 1),
        weightedScaleNorm D p ϑ 2 (F.depth + 1) (sourceTransport sf i (F.depth + 1)) ≤
        142 * (1 / (F.blockSide : ℝ)) ^ (F.depth + 1 - 1 - i) * n2 := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h3 := sourceTransport_norm_le h.odd h.two D p hϑ sf hsf0 i (F.depth + 1) hi' (by simp [BlockFrame.top])
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      by_cases hc : i + 1 < F.top
      · have e : sf i = fun y d => ‖A.coarse i y d‖ := by
          funext y d
          simp only [hsf, if_pos hc]
        rw [e]
        exact hmu i hc
      · have e : sf i = fun _ _ => 0 := by
          funext y d
          simp only [hsf, if_neg hc]
        rw [e, weightedScaleNorm_eq_zero_of_forall (by norm_num) fun _ _ => rfl]
        exact hn2
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have h4 := sum_inv_pow_le_two hL2 (F.depth + 1)
    nlinarith
theorem re_linearizedCurl (X : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4) : (linearizedCurl X u q).re = 0 := by
  unfold linearizedCurl
  have hu : ∀ x i, ((u x i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := fun x i => (u x i).2
  simp only [Quaternion.re_add, Quaternion.re_sub, VariationRates.re_adjointAction, hu]
  simp
theorem sum_plaquette_curl_sq_le (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F) (w : F.SiteWeights) :
    ∑ q ∈ innerPlaquettes S 0, (w 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 ≤ _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w ^ 2 := by
  classical
  have hmaps : ∀ q ∈ innerPlaquettes S 0, enclosingCell q.1 ∈ S := fun q hq =>
    enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
  rw [_root_.YangMills.Construction.BlockAverages.ChartNorms.weightedNorm_sq, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun z hz => le_trans ?_ (sum_curl_sq_le_localNormSq S _ R A w)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro q hq
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
  unfold plaquettesOver
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  rw [h2]
  unfold cellBall
  refine Finset.mem_filter.2 ⟨hz, ?_⟩
  have : cellSupDist z z = 0 := cellSupDist_self z
  omega
theorem sum_coarse_sq_le_weightedNorm_sq (h : ColdTopHyp del C Cb cc s S R V) (A : ChainChart F)
    (w : F.SiteWeights) :
    ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 ≤
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w ^ 2 := by
  classical
  have hmaps : ∀ j, ∀ c ∈ innerBonds S (j + 1), enclosingCell c.1 ∈ S := fun j c hc =>
    enclosingCell_mem h.odd (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  have e : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 =
      ∑ z ∈ S, ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1) with enclosingCell c.1 = z,
        (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_fiberwise_of_maps_to (hmaps j) _).symm
  rw [e, _root_.YangMills.Construction.BlockAverages.ChartNorms.weightedNorm_sq]
  refine Finset.sum_le_sum fun z hz => le_trans ?_ (sum_coarse_sq_le_localNormSq S _ R A w)
  have hn : F.top - 1 = F.depth := by simp [BlockFrame.top]
  rw [hn]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro c hc
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
  unfold bondsOver
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  rw [h2]
  unfold cellBall
  refine Finset.mem_filter.2 ⟨hz, ?_⟩
  have : cellSupDist z z = 0 := cellSupDist_self z
  omega
theorem invertedWeights_mul_decayWeights (hodd : Odd F.blockSide) (del θ : ℝ) (p : F.Site 0) (y0 : F.Cell) {j : ℕ}
    (x : F.Site j) :
    invertedWeights (decayWeights F del θ p y0) j x * decayWeights F del θ p y0 j x = 1 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 : decayWeights F del θ p y0 j x ≠ 0 := by
    unfold decayWeights
    have := WeightedAverages.Chains.scaleRadius_pos (F := F) hodd.pos j p x
    exact mul_ne_zero (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (by positivity) _).ne'
  unfold invertedWeights
  exact inv_mul_cancel₀ h1
theorem sum_mul_le_sqrt_mul_sqrt_of_mul_eq_one {ι : Type} (T : Finset ι) (f b w d : ι → ℝ)
    (hwd : ∀ i ∈ T, w i * d i = 1) :
    ∑ i ∈ T, f i * b i ≤ Real.sqrt (∑ i ∈ T, (w i * f i) ^ 2) * Real.sqrt (∑ i ∈ T, (d i * b i) ^ 2) := by
  refine le_trans (le_of_eq ?_) (Real.sum_mul_le_sqrt_mul_sqrt T _ _)
  refine Finset.sum_congr rfl fun i hi => ?_
  calc f i * b i = (w i * d i) * (f i * b i) := by rw [hwd i hi, one_mul]
    _ = _ := by ring
theorem linearPart_chartMove (R : F.FieldChain) (U A : ChainChart F) (t : ℝ) :
    ∀ (j : ℕ) (x : F.Site j) (i : Fin 4),
      linearPart R (chartMove U A t) j x i = linearPart R U j x i + t • linearPart R A j x i
  | 0, x, i => rfl
  | j + 1, x, i => by
    have e1 : linearPart R (chartMove U A t) j =
        fun y d => linearPart R U j y d - (-t) • linearPart R A j y d := by
      funext y d
      rw [linearPart_chartMove R U A t j y d]
      simp
    show parallelAverage (R j) (linearPart R (chartMove U A t) j) (x, i) +
        (if j + 1 < F.top then (((chartMove U A t).coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0) =
      (parallelAverage (R j) (linearPart R U j) (x, i) +
        (if j + 1 < F.top then ((U.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0)) +
      t • (parallelAverage (R j) (linearPart R A j) (x, i) +
        (if j + 1 < F.top then ((A.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0))
    rw [e1, parallelAverage_sub_smul]
    split_ifs with hc
    · have e2 : (((chartMove U A t).coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) =
          ((U.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) + t • ((A.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) := rfl
      rw [e2, smul_add, neg_smul]
      abel
    · simp
theorem firstVariationFunctional_chartMove (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F)
    (t : ℝ) :
    firstVariationFunctional a S R (chartMove U A t) =
      firstVariationFunctional a S R U + t * firstVariationFunctional a S R A := by
  have hp : ∀ q, plaquetteRate R (chartMove U A t) q = plaquetteRate R U q + t * plaquetteRate R A q := by
    intro q
    unfold plaquetteRate
    have e : (chartMove U A t).fine = fun x i => U.fine x i + t • A.fine x i := rfl
    rw [e, linearizedCurl_add_smul, add_mul, smul_mul_assoc]
    simp only [Quaternion.re_add, Quaternion.re_smul, smul_eq_mul]
    ring
  have hl : ∀ j (c : F.Site (j + 1) × Fin 4),
      innerRate R (chartMove U A t) j c = innerRate R U j c + t * innerRate R A j c := by
    intro j c
    unfold innerRate
    have e : (((chartMove U A t).coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        ((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) +
          t • ((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) := rfl
    rw [e, add_mul, smul_mul_assoc]
    simp only [Quaternion.re_add, Quaternion.re_smul, smul_eq_mul]
    ring
  have ht : ∀ c : F.Site (F.depth + 1) × Fin 4,
      topRate R (chartMove U A t) c = topRate R U c + t * topRate R A c := by
    intro c
    unfold topRate
    rw [linearPart_chartMove, add_mul, smul_mul_assoc]
    simp only [Quaternion.re_add, Quaternion.re_smul, smul_eq_mul]
    ring
  unfold firstVariationFunctional
  simp only [hp, hl, ht, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem chartMove_zeroChart : chartMove (zeroChart F) (zeroChart F) 1 = zeroChart F := by
  show (⟨_, _⟩ : ChainChart F) = ⟨_, _⟩
  congr 1
  · funext x i
    simp [zeroChart]
  · funext j y i
    simp [zeroChart]
theorem firstVariationFunctional_zeroChart (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) :
    firstVariationFunctional a S R (zeroChart F) = 0 := by
  have h1 := firstVariationFunctional_chartMove a S R (zeroChart F) (zeroChart F) 1
  rw [chartMove_zeroChart] at h1
  linarith
theorem abs_firstVariationFunctional_le (h : ColdTopHyp del C Cb cc s S R V) {a : ℝ} (ha : 0 ≤ a)
    (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) {θ : ℝ} (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) :
    |firstVariationFunctional a S R A| ≤ (Cb * (Real.sqrt (6432 * expCountSum del) +
        a * (2 * Real.sqrt (1608 * expCountSum del) +
        48 * 100284 * (Real.exp del * Real.sqrt (expCountSum del))))) * s *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights (decayWeights F del θ p y0)) := by
  have hodd := h.odd
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hCb := h.hCb
  have hs0 := h.s0
  have hdel := h.hdel
  set w := invertedWeights (decayWeights F del θ p y0) with hw
  set dk := decayWeights F del θ p y0 with hdk
  set Nm := _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w with hNm
  have hNm0 : 0 ≤ Nm := _root_.YangMills.Construction.BlockAverages.ChartNorms.weightedNorm_nonneg _ _ _ _
  have hwd : ∀ {j : ℕ} (x : F.Site j), w j x * dk j x = 1 := fun x =>
    invertedWeights_mul_decayWeights hodd del θ p y0 x
  have hexp : 0 ≤ expCountSum del := expCountSum_nonneg
  have hP : |∑ q ∈ innerPlaquettes S 0, plaquetteRate R A q| ≤
      Cb * s * Real.sqrt (6432 * expCountSum del) * Nm := by
    have h1 : |∑ q ∈ innerPlaquettes S 0, plaquetteRate R A q| ≤
        ∑ q ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) A.fine q‖ * (Cb * s * levelScale F 0 ^ 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
      unfold plaquetteRate
      rw [abs_neg]
      refine (abs_re_mul_unit_le_of_re_eq_zero (re_linearizedCurl _ _ _) _).trans ?_
      exact mul_le_mul_of_nonneg_left (h.curv q hq) (norm_nonneg _)
    refine h1.trans ?_
    have h2 := sum_mul_le_sqrt_mul_sqrt_of_mul_eq_one (innerPlaquettes S 0)
      (fun q => ‖linearizedCurl (R 0) A.fine q‖)
      (fun _ => Cb * s * levelScale F 0 ^ 2) (fun q => w 0 q.1) (fun q => dk 0 q.1) (fun q _ => hwd q.1)
    refine h2.trans ?_
    have h3 : Real.sqrt (∑ q ∈ innerPlaquettes S 0, (w 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2) ≤ Nm := by
      apply Real.sqrt_le_iff.2
      exact ⟨hNm0, sum_plaquette_curl_sq_le h A w⟩
    have h4 : Real.sqrt (∑ q ∈ innerPlaquettes S 0, (dk 0 q.1 * (Cb * s * levelScale F 0 ^ 2)) ^ 2) ≤
        Cb * s * Real.sqrt (6432 * expCountSum del) := by
      set Q : ℝ := ((F.blockSide ^ (F.top - 0) : ℕ) : ℝ) with hQ
      have hQl : Q * levelScale F 0 = 1 := blockCount_mul_scaleAt hodd 0
      have e : ∑ q ∈ innerPlaquettes S 0, (dk 0 q.1 * (Cb * s * levelScale F 0 ^ 2)) ^ 2 =
          (Cb * s * levelScale F 0 ^ 2) ^ 2 * ∑ q ∈ innerPlaquettes S 0, dk 0 q.1 ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
      have h5 := sum_innerPlaquettes_le (S := S) (l := 0) (g := fun x => dk 0 x ^ 2) (fun _ => by positivity)
      have h6 := sum_sitesOfCells_decayWeights_sq_le hodd (l := 0) (by omega) S hdel h0 h8 p y0
      rw [← hdk, ← hQ] at h6
      have h7 : ∑ q ∈ innerPlaquettes S 0, dk 0 q.1 ^ 2 ≤ 6432 * expCountSum del * Q ^ 4 := by linarith
      rw [e]
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      have e9 : (Cb * s * Real.sqrt (6432 * expCountSum del)) ^ 2 = (Cb * s) ^ 2 * (6432 * expCountSum del) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [e9]
      calc (Cb * s * levelScale F 0 ^ 2) ^ 2 * ∑ q ∈ innerPlaquettes S 0, dk 0 q.1 ^ 2
          ≤ (Cb * s * levelScale F 0 ^ 2) ^ 2 * (6432 * expCountSum del * Q ^ 4) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = (Cb * s) ^ 2 * (Q * levelScale F 0) ^ 4 * (6432 * expCountSum del) := by ring
        _ = _ := by rw [hQl]; ring
    calc _ ≤ Nm * (Cb * s * Real.sqrt (6432 * expCountSum del)) :=
          mul_le_mul h3 h4 (Real.sqrt_nonneg _) hNm0
      _ = _ := by ring
  have hLow : |∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c| ≤
      Cb * s * Real.sqrt (1608 * expCountSum del) * (2 * Nm) := by
    set P : ℕ → ℝ := fun j =>
      Real.sqrt (∑ c ∈ innerBonds S (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2) with hPd
    have hj : ∀ j ∈ Finset.range F.depth, |∑ c ∈ innerBonds S (j + 1), innerRate R A j c| ≤
        Cb * s * Real.sqrt (1608 * expCountSum del) * (scaleAt F (j + 1) * P j) := by
      intro j hjr
      have hj1 : j + 1 < F.top := by
        have := Finset.mem_range.1 hjr
        simp only [BlockFrame.top]
        omega
      have h1 : |∑ c ∈ innerBonds S (j + 1), innerRate R A j c| ≤
          ∑ c ∈ innerBonds S (j + 1), ‖A.coarse j c.1 c.2‖ * (Cb * s * scaleAt F (j + 1) ^ 3) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c hc => ?_)
        unfold innerRate
        rw [abs_neg, abs_mul, abs_of_nonneg (norm_nonneg _)]
        have h2 := abs_re_mul_unit_le_of_re_eq_zero (Z := ((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]))
          (A.coarse j c.1 c.2).2 (referenceDefect R j c)
        have h3 := VariationRates.norm_contourAverage_le_one hodd (R j) c
        have h4 : ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cb * s * scaleAt F (j + 1) ^ 3 :=
          h.mis_low j hj1 c hc
        calc _ ≤ 1 * (‖((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ *
              ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) :=
              mul_le_mul h3 h2 (abs_nonneg _) zero_le_one
          _ ≤ _ := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      refine h1.trans ?_
      have h2 := sum_mul_le_sqrt_mul_sqrt_of_mul_eq_one (innerBonds S (j + 1)) (fun c => ‖A.coarse j c.1 c.2‖)
        (fun _ => Cb * s * scaleAt F (j + 1) ^ 3) (fun c => w (j + 1) c.1) (fun c => dk (j + 1) c.1)
        (fun c _ => hwd c.1)
      refine h2.trans ?_
      have h4 : Real.sqrt (∑ c ∈ innerBonds S (j + 1), (dk (j + 1) c.1 * (Cb * s * scaleAt F (j + 1) ^ 3)) ^ 2) ≤
          Cb * s * Real.sqrt (1608 * expCountSum del) * scaleAt F (j + 1) := by
        set Q : ℝ := ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) with hQ
        have hQl : Q * scaleAt F (j + 1) = 1 := blockCount_mul_scaleAt hodd (j + 1)
        have e : ∑ c ∈ innerBonds S (j + 1), (dk (j + 1) c.1 * (Cb * s * scaleAt F (j + 1) ^ 3)) ^ 2 =
            (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 * ∑ c ∈ innerBonds S (j + 1), dk (j + 1) c.1 ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
        have h5 := sum_innerBonds_le (S := S) (l := j + 1) (g := fun x => dk (j + 1) x ^ 2) (fun _ => by positivity)
        have h6 := sum_sitesOfCells_decayWeights_sq_le hodd (l := j + 1) (by omega) S hdel h0 h8 p y0
        rw [← hdk, ← hQ] at h6
        have h7 : ∑ c ∈ innerBonds S (j + 1), dk (j + 1) c.1 ^ 2 ≤ 1608 * expCountSum del * Q ^ 4 := by linarith
        rw [e]
        apply Real.sqrt_le_iff.2
        refine ⟨by positivity, ?_⟩
        have e9 : (Cb * s * Real.sqrt (1608 * expCountSum del) * scaleAt F (j + 1)) ^ 2 =
            (Cb * s) ^ 2 * (1608 * expCountSum del) * scaleAt F (j + 1) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        rw [e9]
        calc (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 * ∑ c ∈ innerBonds S (j + 1), dk (j + 1) c.1 ^ 2
            ≤ (Cb * s * scaleAt F (j + 1) ^ 3) ^ 2 * (1608 * expCountSum del * Q ^ 4) :=
              mul_le_mul_of_nonneg_left h7 (by positivity)
          _ = (Cb * s) ^ 2 * (Q * scaleAt F (j + 1)) ^ 4 * (1608 * expCountSum del) * scaleAt F (j + 1) ^ 2 := by
              ring
          _ = _ := by rw [hQl]; ring
      calc _ ≤ P j * (Cb * s * Real.sqrt (1608 * expCountSum del) * scaleAt F (j + 1)) :=
            mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
        _ = _ := by ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hj).trans ?_)
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    have h1 : Real.sqrt (∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) ^ 2) ≤ 2 := by
      apply Real.sqrt_le_iff.2
      refine ⟨by norm_num, ?_⟩
      have h2 := sum_scaleAt_le_two h.two
      have h3 : ∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) ^ 2 ≤ ∑ j ∈ Finset.range F.depth, scaleAt F (j + 1) :=
        Finset.sum_le_sum fun j _ => by
          have h4 := scaleAt_nonneg hodd (j + 1)
          have h5 := scaleAt_le_one hodd (j + 1)
          nlinarith
      linarith
    have h2 : Real.sqrt (∑ j ∈ Finset.range F.depth, P j ^ 2) ≤ Nm := by
      apply Real.sqrt_le_iff.2
      refine ⟨hNm0, le_trans (le_of_eq ?_) (sum_coarse_sq_le_weightedNorm_sq h A w)⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by norm_num)
  have hTop : |∑ c ∈ innerBonds S (F.depth + 1), topRate R A c| ≤
      Cb * s * (48 * 100284 * (Real.exp del * Real.sqrt (expCountSum del) * Nm)) := by
    have h1 : |∑ c ∈ innerBonds S (F.depth + 1), topRate R A c| ≤
        Cb * s * ∑ c ∈ innerBonds S (F.depth + 1), ‖linearPart R A (F.depth + 1) c.1 c.2‖ := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c hc => ?_)
      unfold topRate
      rw [abs_neg, abs_mul, abs_of_nonneg (norm_nonneg _)]
      have h2 := abs_re_mul_unit_le_of_re_eq_zero (Z := linearPart R A (F.depth + 1) c.1 c.2)
        (re_linearPart R A _ _ _) ((referenceDefect R F.depth c)⁻¹)
      rw [norm_inv_coe_sub_one] at h2
      have h3 := VariationRates.norm_contourAverage_le_one hodd (R F.depth) c
      have h4 : ‖((referenceDefect R F.depth c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cb * s := h.mis_top c hc
      calc _ ≤ 1 * (‖linearPart R A (F.depth + 1) c.1 c.2‖ *
            ‖((referenceDefect R F.depth c : UnitQuaternion) : ℍ[ℝ]) - 1‖) :=
            mul_le_mul h3 h2 (abs_nonneg _) zero_le_one
        _ ≤ _ := by
            rw [one_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hϑ : |(-θ)| ≤ 1 / 8 := by
      rw [abs_neg, abs_of_nonneg h0]
      exact h8
    set Nθ : ℝ := ((F.blockSide : ℝ) ^ F.top) ^ (-θ) with hNθ
    have h2 := sum_innerBonds_le_sum_cellBall h (l := F.depth + 1) (by simp [BlockFrame.top])
      (fun c => ‖linearPart R A (F.depth + 1) c.1 c.2‖) (fun _ => norm_nonneg _)
    refine h2.trans ?_
    have h3 : ∀ z ∈ S, ∑ b ∈ innerBonds (cellBall S z 1) (F.depth + 1), ‖linearPart R A (F.depth + 1) b.1 b.2‖ ≤
        48 * Nθ * (100284 * (cellFactor F del θ y0 z * localNorm S R A w z)) := by
      intro z _
      have hD := card_cellBall_one_le S z
      have hX0 : 0 ≤ cellFactor F del θ y0 z * localNorm S R A w z :=
        mul_nonneg (cellFactor_nonneg hodd _ _ _ _) (localNorm_nonneg _ _ _ _ _)
      have h4 := sum_innerBonds_le_weightedScaleNorm hodd (l := F.depth + 1) (by simp [BlockFrame.top]) hD p h0 h8
        (f := fun y d => ‖linearPart R A (F.depth + 1) y d‖) (fun _ _ => norm_nonneg _)
      have eQ : ((F.blockSide ^ (F.top - (F.depth + 1)) : ℕ) : ℝ) = 1 := by
        have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
        rw [this]
        simp
      rw [eQ] at h4
      have h5 := weightedScaleNorm_two_linearPart_top_le h A hD p hϑ hX0
        (fun m hm => weightedScaleNorm_two_coarse_le h A p y0 z hm)
      have h6 := weightedScaleNorm_four_fine_le h A p (θ := θ) y0 z
      refine h4.trans ?_
      have h7 : weightedScaleNorm (cellBall S z 1) p (-θ) 2 (F.depth + 1)
            (fun y d => ‖linearPart R A (F.depth + 1) y d‖) ≤
          100284 * (cellFactor F del θ y0 z * localNorm S R A w z) := by
        linarith
      calc 48 * 1 ^ 2 * Nθ * _ ≤ 48 * 1 ^ 2 * Nθ * (100284 * (cellFactor F del θ y0 z * localNorm S R A w z)) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum h3).trans ?_
    have h4 := sum_cellFactor_mul_localNorm_le h A w (θ := θ) y0
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc 48 * Nθ * (100284 * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z)
        = 48 * 100284 * (Nθ * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  unfold firstVariationFunctional
  have hsum := (abs_add_le (∑ p ∈ innerPlaquettes S 0, plaquetteRate R A p) (a * (∑ j ∈ Finset.range F.depth,
    ∑ c ∈ innerBonds S (j + 1), innerRate R A j c + ∑ c ∈ innerBonds S (F.depth + 1), topRate R A c)))
  refine hsum.trans ?_
  rw [abs_mul, abs_of_nonneg ha]
  have h2 := abs_add_le (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c)
    (∑ c ∈ innerBonds S (F.depth + 1), topRate R A c)
  have h3 := h2.trans (add_le_add hLow hTop)
  calc _ ≤ Cb * s * Real.sqrt (6432 * expCountSum del) * Nm +
        a * (Cb * s * Real.sqrt (1608 * expCountSum del) * (2 * Nm) +
        Cb * s * (48 * 100284 * (Real.exp del * Real.sqrt (expCountSum del) * Nm))) :=
        add_le_add hP (mul_le_mul_of_nonneg_left h3 ha)
    _ = _ := by ring
theorem abs_deriv_sub_firstVariationFunctional_le (h : ColdTopHyp del C Cb cc s S R V) {a : ℝ} (ha : 0 ≤ a)
    (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) {θ : ℝ} (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) (hCs : C * s ≤ 1 / 2)
    (hsm : 568 * (5 * (C * (1 + Cb) * s)) * hullFactor F.blockSide ≤ 1 / 2) {d : ℝ}
    (hJ : HasDerivAt (fun τ : ℝ => chartAction a S R (ray A τ) V) d 0) :
    |d - firstVariationFunctional a S R A| ≤ a * (40568 * (Real.exp del * Real.sqrt (expCountSum del) *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights (decayWeights F del θ p y0)))) * (sqCoefficient F.blockSide C Cb * s ^ 2) := by
  have hodd := h.odd
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hCb := h.hCb
  have hC0 : 0 ≤ C := by linarith [h.hC]
  have hs0 := h.s0
  set w := invertedWeights (decayWeights F del θ p y0) with hw
  have hϑ : |(-θ)| ≤ 1 / 8 := by
    rw [abs_neg, abs_of_nonneg h0]
    exact h8
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  set Nθ : ℝ := N ^ (-θ) with hNθ
  have hNθ0 : 0 ≤ Nθ := by positivity
  set Ez : F.Cell → ℝ := fun z => 40568 * (cellFactor F del θ y0 z * localNorm S R A w z) with hEzd
  have hEz0 : ∀ z, 0 ≤ Ez z := fun z =>
    mul_nonneg (by norm_num) (mul_nonneg (cellFactor_nonneg hodd _ _ _ _) (localNorm_nonneg _ _ _ _ _))
  set Wt := Nθ * ∑ z ∈ S, Ez z with hWt
  have hWt0 : 0 ≤ Wt := mul_nonneg hNθ0 (Finset.sum_nonneg fun z _ => hEz0 z)
  have hWle : Wt ≤ 40568 * (Real.exp del * Real.sqrt (expCountSum del) * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w) := by
    have h1 := sum_cellFactor_mul_localNorm_le h A w (θ := θ) y0
    rw [hWt, hEzd, ← Finset.mul_sum]
    calc Nθ * (40568 * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z)
        = 40568 * (Nθ * ∑ z ∈ S, cellFactor F del θ y0 z * localNorm S R A w z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hF0 := zero_le_hullFactor F.blockSide
  have hkS : 0 ≤ sqCoefficient F.blockSide C Cb := by
    unfold sqCoefficient
    positivity
  have hkD : 0 ≤ stepCoefficient F.blockSide F.depth N C Cb := by
    unfold stepCoefficient
    positivity
  set δ₀ := min cc (min (1 / 2) (1 / (11360 * N * hullFactor F.blockSide + 1))) with hδ₀
  have hcc := h.cc0
  have hδ₀0 : 0 < δ₀ := lt_min hcc (lt_min (by norm_num) (by positivity))
  have hmain : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → |d - firstVariationFunctional a S R A| ≤
      a * (Wt * (sqCoefficient F.blockSide C Cb * s ^ 2 + stepCoefficient F.blockSide F.depth N C Cb * δ)) := by
    intro δ hδ hδ0
    have d1 : δ ≤ cc := hδ0.trans (min_le_left _ _)
    have d2 : δ ≤ 1 / 2 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have d3 : δ ≤ 1 / (11360 * N * hullFactor F.blockSide + 1) :=
      hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hsmall : 568 * (10 * N * δ + 5 * (C * (1 + Cb) * s)) * hullFactor F.blockSide ≤ 1 := by
      have h1 := (le_div_iff₀ (by positivity : 0 < 11360 * N * hullFactor F.blockSide + 1)).1 d3
      have e : 568 * (10 * N * δ + 5 * (C * (1 + Cb) * s)) * hullFactor F.blockSide =
          (11360 * N * hullFactor F.blockSide) * δ / 2 + 568 * (5 * (C * (1 + Cb) * s)) * hullFactor F.blockSide := by
        ring
      rw [e]
      nlinarith
    obtain ⟨τ₁, hτ₁, hsm'⟩ := exists_isSmallStep h A hδ d1
    refine abs_deriv_sub_le_of_slope hJ (hasDerivAt_smoothPart a S R A) ?_
    have hmem : Set.Ioc (0 : ℝ) τ₁ ∈ nhdsWithin 0 (Set.Ioi 0) := Ioc_mem_nhdsGT hτ₁
    filter_upwards [hmem] with τ hτ
    have hs := hsm' τ hτ.1 hτ.2
    have hE : ∀ z ∈ S, ∀ m, m < F.top →
        weightedScaleNorm (cellBall S z 1) p (-θ) 4 m (rayCoordNorm R A τ m) ≤ τ * Ez z := by
      intro z _ m hm
      have hX0 : 0 ≤ cellFactor F del θ y0 z * localNorm S R A w z :=
        mul_nonneg (cellFactor_nonneg hodd _ _ _ _) (localNorm_nonneg _ _ _ _ _)
      have h1 := weightedScaleNorm_four_ray_le h hs (cellBall_subset S z 1) (card_cellBall_one_le S z) p hϑ hX0
        (fun m hm => weightedScaleNorm_two_coarse_le h A p y0 z hm) hsmall hm
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hτ.1.le)
      have h2 := weightedScaleNorm_four_fine_le h A p (θ := θ) y0 z
      rw [hEzd]
      simp only []
      linarith
    have hsplit := chartAction_ray_sub_eq h a A τ
    have herr := abs_remainder_le h ha hs d2 hCs p h0 h8 (fun z _ => hEz0 z) hE
    have e : chartAction a S R (ray A τ) V - chartAction a S R (ray A 0) V - τ * firstVariationFunctional a S R A -
        (smoothPart a S R A τ - smoothPart a S R A 0 - τ * (∑ p ∈ innerPlaquettes S 0, plaquetteRate R A p +
          a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerRate R A j c)) =
        a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          (‖gaugedBondAverage R (ray A τ) j c‖ - ‖contourAverage (R j) c‖) * innerDefect R A τ j c +
        ∑ c ∈ innerBonds S (F.depth + 1),
          ((‖gaugedBondAverage R (ray A τ) F.depth c‖ - ‖contourAverage (R F.depth) c‖) * topDefect R A τ c +
          (‖contourAverage (R F.depth) c‖ * (topDefect R A τ c - topDefect R A 0 c) - τ * topRate R A c))) := by
      rw [hsplit]
      ring
    rw [e]
    exact herr
  have hX : |d - firstVariationFunctional a S R A| ≤ a * (Wt * (sqCoefficient F.blockSide C Cb * s ^ 2)) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set K := a * Wt * stepCoefficient F.blockSide F.depth N C Cb with hK
    have hδ : 0 < min δ₀ (ε / (K + 1)) := lt_min hδ₀0 (by positivity)
    have h1 := hmain _ hδ (min_le_left _ _)
    refine h1.trans ?_
    have h2 : K * min δ₀ (ε / (K + 1)) ≤ ε := by
      have h3 : min δ₀ (ε / (K + 1)) ≤ ε / (K + 1) := min_le_right _ _
      have h4 := (le_div_iff₀ (by positivity : 0 < K + 1)).1 h3
      nlinarith
    calc a * (Wt * (sqCoefficient F.blockSide C Cb * s ^ 2 +
          stepCoefficient F.blockSide F.depth N C Cb * min δ₀ (ε / (K + 1))))
        = a * (Wt * (sqCoefficient F.blockSide C Cb * s ^ 2)) + K * min δ₀ (ε / (K + 1)) := by
          rw [hK]
          ring
      _ ≤ _ := by linarith
  refine hX.trans ?_
  have h6 : 0 ≤ sqCoefficient F.blockSide C Cb * s ^ 2 := by positivity
  calc a * (Wt * (sqCoefficient F.blockSide C Cb * s ^ 2)) ≤
      a * ((40568 * (Real.exp del * Real.sqrt (expCountSum del) * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w)) *
        (sqCoefficient F.blockSide C Cb * s ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWle h6) ha
    _ = _ := by ring
end Small
theorem chartShiftMulti_single (U A : ChainChart F) (τ : ℝ) :
    chartShiftMulti U ![A] (fun _ => τ) = chartMove U A τ := by
  simp [chartShiftMulti, chartMove]
end FirstVariation
open FirstVariation YangMills.Construction.WeightedAverages.Sums YangMills.Construction.BlockAverages.ChartNorms
  YangMills.Construction.HullBounds in
theorem referenceFirstVariationStatement_holds (hD : chartActionDerivativeBoundsStatement)
    (hB : referenceBoundsStatement) (hO : levelCoordinateStepStatement)
    (hT : bondAngleAndAverageNormStatement) (hZ : YangMills.Construction.BondAverageNorms.bondAverageNormDerivStatement)
    (hK : levelCoordinateQuarticStatement) : referenceFirstVariationStatement := by
  intro a θ del ha hθ hθ8 hdel hdel8
  obtain ⟨LD, hD⟩ := hD
  obtain ⟨Cb0, cB, LB, hCb0, hcB, hB⟩ := hB
  obtain ⟨LO, hO⟩ := hO
  obtain ⟨LT, hT⟩ := hT
  obtain ⟨LZ, hZ⟩ := hZ
  obtain ⟨CK, LK, hCK, hK⟩ := hK
  have hexp : 0 ≤ expCountSum del := expCountSum_nonneg
  set Ca' := Cb0 * (Real.sqrt (6432 * expCountSum del) + a * (2 * Real.sqrt (1608 * expCountSum del) +
    48 * 100284 * (Real.exp del * Real.sqrt (expCountSum del)))) with hCa'
  have hCa'0 : 0 ≤ Ca' := by positivity
  refine ⟨Ca' + 1, max 3 (max LD (max LB (max LO (max LT (max LZ LK))))), by positivity, fun L hodd hL => ?_⟩
  have l3 : 3 ≤ L := (le_max_left _ _).trans hL
  have hL' := (le_max_right _ _).trans hL
  have lD : LD ≤ L := (le_max_left _ _).trans hL'
  have hL'' := (le_max_right _ _).trans hL'
  have lB : LB ≤ L := (le_max_left _ _).trans hL''
  have hL3 := (le_max_right _ _).trans hL''
  have lO : LO ≤ L := (le_max_left _ _).trans hL3
  have hL4 := (le_max_right _ _).trans hL3
  have lT : LT ≤ L := (le_max_left _ _).trans hL4
  have hL5 := (le_max_right _ _).trans hL4
  have lZ : LZ ≤ L := (le_max_left _ _).trans hL5
  have lK : LK ≤ L := (le_max_right _ _).trans hL5
  obtain ⟨cD, CD, Ck, hcD, _, _, hD⟩ := hD L a θ del hodd lD ha hθ hθ8 hdel hdel8
  obtain ⟨CO, cO, hCO, hcO, hO⟩ := hO L hodd lO
  obtain ⟨CT, cT, hCT, hcT, hT⟩ := hT L hodd lT
  obtain ⟨CZ, cZ, hCZ, hcZ, hZ⟩ := hZ L hodd lZ
  obtain ⟨c5, hc5, hK⟩ := hK L hodd lK del hdel
  set C := 1 + CO + CT + CZ + CK with hC
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  set cc := min cO (min cT (min cZ c5)) with hcc
  have hcc0 : 0 < cc := lt_min hcO (lt_min hcT (lt_min hcZ hc5))
  have ccO : cc ≤ cO := min_le_left _ _
  have ccT : cc ≤ cT := (min_le_right _ _).trans (min_le_left _ _)
  have ccZ : cc ≤ cZ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have cc5 : cc ≤ c5 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hF0 := zero_le_hullFactor L
  set c2 := 1 / (2 * C) with hc2
  set c3 := 1 / (2 * (568 * 5 * (C * (1 + Cb0)) * hullFactor L) + 1) with hc3
  have hc20 : 0 < c2 := by positivity
  have hc30 : 0 < c3 := by positivity
  set c := min (min cD cB) (min cc (min 1 (min c2 c3))) with hc
  have hc0 : 0 < c := lt_min (lt_min hcD hcB) (lt_min hcc0 (lt_min one_pos (lt_min hc20 hc30)))
  have cD' : c ≤ cD := (min_le_left _ _).trans (min_le_left _ _)
  have cB' : c ≤ cB := (min_le_left _ _).trans (min_le_right _ _)
  have cc' : c ≤ cc := (min_le_right _ _).trans (min_le_left _ _)
  have c1' : c ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have c2' : c ≤ c2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have c3' : c ≤ c3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set Cst := a * 40568 * (Real.exp del * Real.sqrt (expCountSum del)) * sqCoefficient L C Cb0 + 1 with hCst
  have hkS : 0 ≤ sqCoefficient L C Cb0 := by
    unfold sqCoefficient
    positivity
  refine ⟨c, Cst, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold
  have hoddF : Odd F.blockSide := by
    rw [hFL]
    exact hodd
  have hB' := hB F m S hoddF (by rw [hFL]; exact lB) hamb hm hreg s V hs (hsc.trans cB') hcold
  obtain ⟨_, b2, b3, b4, _, _⟩ := hB'
  have hctx : ColdTopHyp del C Cb0 cc s S (referenceFieldChain S V) V := by
    refine ⟨hoddF, by rw [hFL]; omega, hamb, hC1, hCb0.le, hdel, hs, hsc.trans c1', hcc0, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · unfold referenceFieldChain
      exact Function.update_self _ _ _
    · exact fun q hq => b2 0 (by simp) q hq
    · exact fun j hj c' hc' => b3 j hj c' hc'
    · exact fun c' hc' => b4 c' hc'
    · intro U j b hj hb t ht0 htc hmc hbd
      have h1 := hO F m S hFL hamb hm hreg s V hs ((hsc.trans cc').trans ccO) hcold U j b hj hb t ht0
        (htc.trans ccO) (hmc.trans ccO) hbd
      refine h1.trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
      have hL0 : (0 : ℝ) ≤ F.blockSide := by positivity
      positivity
    · intro U j b hj hb t ht0 htc hbd
      have h1 := (hT F m S hFL hamb hm hreg s V hs ((hsc.trans cc').trans ccT) hcold U j b hj hb t ht0
        (htc.trans ccT) hbd).1
      refine h1.trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
      have hL0 : (0 : ℝ) ≤ F.blockSide := by positivity
      positivity
    · intro j b hj hb
      obtain ⟨z1, z2⟩ := hZ F m S hFL hamb hm hreg s V hs ((hsc.trans cc').trans ccZ) hcold j b hj hb
      refine ⟨z1, fun f t ht0 htc hbd => ?_⟩
      obtain ⟨z3, z4⟩ := z2 f t ht0 (htc.trans ccZ) hbd
      refine ⟨z3, fun g ρ hρ hbg => (z4 g ρ hρ hbg).trans ?_⟩
      have hL0 : (0 : ℝ) ≤ F.blockSide := by positivity
      have : 0 ≤ t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 := by positivity
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) this) hρ
    · intro U hU j hj z hz
      have h1 := hK F m S hFL hamb hm hreg s V hs ((hsc.trans cc').trans cc5) hcold U (hU.trans cc5) j hj z hz
      exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (localNorm_nonneg _ _ _ _ _))
  have hCs : C * s ≤ 1 / 2 := by
    have h1 := hsc.trans c2'
    rw [hc2, le_div_iff₀ (by positivity)] at h1
    linarith only [h1]
  have hsm : 568 * (5 * (C * (1 + Cb0) * s)) * hullFactor F.blockSide ≤ 1 / 2 := by
    have h1 := hsc.trans c3'
    rw [hc3, le_div_iff₀ (by positivity)] at h1
    rw [hFL]
    have e : 568 * (5 * (C * (1 + Cb0) * s)) * hullFactor L = s * (568 * 5 * (C * (1 + Cb0)) * hullFactor L) := by
      ring
    rw [e]
    have e2 : s * (2 * (568 * 5 * (C * (1 + Cb0)) * hullFactor L) + 1) =
        2 * (s * (568 * 5 * (C * (1 + Cb0)) * hullFactor L)) + s := by ring
    rw [e2] at h1
    linarith only [h1, hs]
  refine ⟨firstVariationFunctional a S (referenceFieldChain S V), ?_, ?_, ?_⟩
  · intro A A'
    have h1 := firstVariationFunctional_chartMove a S (referenceFieldChain S V) A A' 1
    rw [one_mul] at h1
    exact h1
  · intro t A
    have h1 := firstVariationFunctional_chartMove a S (referenceFieldChain S V) (zeroChart F) A t
    rw [firstVariationFunctional_zeroChart, zero_add] at h1
    exact h1
  · intro A p y0 θ' hθ'
    have h0 : 0 ≤ θ' := by
      rcases hθ' with h | h
      · rw [h]
        exact hθ
      · exact h.ge
    have h8 : θ' ≤ 1 / 8 := by
      rcases hθ' with h | h
      · rw [h]
        exact hθ8
      · rw [h]
        norm_num
    set Nm := _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) with hNm
    have hNm0 : 0 ≤ Nm := _root_.YangMills.Construction.BlockAverages.ChartNorms.weightedNorm_nonneg _ _ _ _
    refine ⟨?_, ?_⟩
    · refine (abs_firstVariationFunctional_le hctx ha.le A p y0 h0 h8).trans ?_
      have e : (Ca' + 1) * s * Nm = Ca' * s * Nm + s * Nm := by ring
      rw [e]
      exact le_add_of_nonneg_right (mul_nonneg hs.le hNm0)
    · have hn0 : supWeightedNorm S del (referenceFieldChain S V) (zeroChart F) ≤ cD := by
        rw [supWeightedNorm_zeroChart S del hdel.le hoddF.pos]
        exact hcD.le
      have han := (hD F m S hFL hamb hm hreg s V hs (hsc.trans cD') hcold (zeroChart F) hn0).1 1 ![A]
      have hdiff : DifferentiableAt ℝ (fun τ : ℝ => chartAction a S (referenceFieldChain S V)
          (chartMove (zeroChart F) A τ) V) 0 := by
        have h2 := han.differentiableAt
        have h3 : HasDerivAt (fun q : ℝ => ((fun _ => q) : Fin 1 → ℝ)) (fun _ => (1 : ℝ)) 0 :=
          hasDerivAt_pi.2 fun _ => hasDerivAt_id _
        have h4 := (h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h3 rfl).differentiableAt
        refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
        simp only [Function.comp, chartShiftMulti_single]
      have h5 := abs_deriv_sub_firstVariationFunctional_le hctx ha.le A p y0 h0 h8 hCs hsm hdiff.hasDerivAt
      refine h5.trans ?_
      rw [← hNm, hFL]
      have e : a * (40568 * (Real.exp del * Real.sqrt (expCountSum del) * Nm)) * (sqCoefficient L C Cb0 * s ^ 2) =
          (a * 40568 * (Real.exp del * Real.sqrt (expCountSum del)) * sqCoefficient L C Cb0) * s ^ 2 * Nm := by ring
      have e2 : Cst * s ^ 2 * Nm =
          (a * 40568 * (Real.exp del * Real.sqrt (expCountSum del)) * sqCoefficient L C Cb0) * s ^ 2 * Nm +
          s ^ 2 * Nm := by
        rw [hCst]
        ring
      rw [e, e2]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg s) hNm0)
end YangMills.Construction.BlockAverages
end
