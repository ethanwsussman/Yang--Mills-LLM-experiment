import YangMills.Construction.ColdChainAtEveryLevel.CriticalOnTheSliceIsCritical
import YangMills.Construction.ColdChainAtEveryLevel.CriticalPointOnTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormAgainstTheForm
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsOfTheTotal
import YangMills.Construction.ColdChainAtEveryLevel.WeightedEstimateOnTheSlice
import Mathlib
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.SliceCriticalPoint
open YangMills.Construction.GaugeMap YangMills.Construction.LatticeFractionalIntegration
theorem exists_zero_of_contracting_family {W E ι : Type} [AddCommGroup W] [Module ℝ W] [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] [Nonempty ι]
    (Sl : Submodule ℝ W) (res : W →ₗ[ℝ] E) (Y : W → ℝ) (p q : ι → W → ℝ)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (G : W → W →ₗ[ℝ] ℝ)
    (hY0 : ∀ x, 0 ≤ Y x) (hYadd : ∀ x y, Y (x + y) ≤ Y x + Y y)
    (hYsmul : ∀ (t : ℝ) x, Y (t • x) = |t| * Y x) (hYdef : ∀ x, Y x = 0 ↔ res x = 0)
    (hpY : ∀ i x, p i x ≤ Y x) (hYp : ∀ x β, (∀ i, p i x ≤ β) → Y x ≤ β)
    (hqres : ∀ i x y, res x = res y → q i x = q i y) (hq00 : ∀ i, q i 0 = 0) (hBres : ∀ Z A, res A = 0 → B Z A = 0)
    (Ca ε K r : ℝ) (hCa : 0 < Ca) (hε : 0 < ε) (hK : 0 < K)
    (h4 : ∀ i, ∀ Z ∈ Sl, ∀ β : ℝ, 0 ≤ β → (∀ A ∈ Sl, |B Z A| ≤ β * q i A) → p i Z ≤ Ca * β)
    (hsrc : ∀ i, ∀ A ∈ Sl, |G 0 A| ≤ ε * q i A)
    (hlip : ∀ U ∈ Sl, ∀ U' ∈ Sl, Y U ≤ r → Y U' ≤ r → ∀ i, ∀ A ∈ Sl,
      |G U A - G U' A - B (U - U') A| ≤ K * (Y U + Y U') * p i (U - U') * q i A)
    (hr : 2 * Ca * ε ≤ r) (hsmall : 4 * Ca * K * r ≤ 1) :
    ∃ U ∈ Sl, Y U ≤ 2 * Ca * ε ∧ ∀ A ∈ Sl, G U A = 0 := by
  classical
  have hq0 : ∀ i, ∀ A ∈ Sl, 0 ≤ q i A := by
    intro i A hA
    by_contra hneg
    push Not at hneg
    have h1 := hsrc i A hA
    have h2 : ε * q i A < 0 := mul_neg_of_pos_of_neg hε hneg
    linarith [abs_nonneg (G 0 A)]
  have hY00 : Y 0 = 0 := (hYdef 0).2 (map_zero res)
  have hYneg : ∀ x, Y (-x) = Y x := by
    intro x
    have := hYsmul (-1) x
    simpa using this
  let f : Sl →ₗ[ℝ] E := res ∘ₗ Sl.subtype
  let I : Submodule ℝ E := LinearMap.range f
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  let sec : I →ₗ[ℝ] W := Sl.subtype ∘ₗ g
  have hsecSl : ∀ i : I, sec i ∈ Sl := fun i => (g i).2
  have hressec : ∀ i : I, res (sec i) = i := by
    intro i
    have := congrArg (fun h : I →ₗ[ℝ] I => ((h i : I) : E)) hg
    simpa [f, sec] using this
  have hdecomp : ∀ A ∈ Sl, ∃ i : I, A - sec i ∈ Sl ∧ res (A - sec i) = 0 := by
    intro A hA
    refine ⟨f.rangeRestrict ⟨A, hA⟩, Sl.sub_mem hA (hsecSl _), ?_⟩
    rw [map_sub, hressec]
    simp [f]
  letI : Norm I := ⟨fun i => Y (sec i)⟩
  have hnorm : ∀ i : I, ‖i‖ = Y (sec i) := fun _ => rfl
  let core : NormedSpace.Core ℝ I :=
    { norm_nonneg := fun i => hY0 _
      norm_smul := by
        intro t i
        rw [hnorm, hnorm, map_smul, hYsmul, Real.norm_eq_abs]
      norm_triangle := by
        intro i j
        rw [hnorm, hnorm, hnorm, map_add]
        exact hYadd _ _
      norm_eq_zero_iff := by
        intro i
        rw [hnorm, hYdef, hressec]
        simp }
  letI : NormedAddCommGroup I := NormedAddCommGroup.ofCore core
  letI : NormedSpace ℝ I := NormedSpace.ofCore core
  haveI : FiniteDimensional ℝ I := inferInstance
  haveI : CompleteSpace I := FiniteDimensional.complete ℝ I
  let Bh : I →ₗ[ℝ] Module.Dual ℝ I :=
    { toFun := fun i => (B (sec i)) ∘ₗ sec
      map_add' := by
        intro i j
        ext k
        simp
      map_smul' := by
        intro t i
        ext k
        simp }
  have hBh : ∀ i j, Bh i j = B (sec i) (sec j) := fun _ _ => rfl
  have hextend : ∀ (Z : W) (β : ℝ) (k : ι), (∀ j : I, |B Z (sec j)| ≤ β * q k (sec j)) →
      ∀ A ∈ Sl, |B Z A| ≤ β * q k A := by
    intro Z β k h A hA
    obtain ⟨i, hi, hres⟩ := hdecomp A hA
    have h1 : B Z A = B Z (sec i) := by
      have h2 : B Z (A - sec i) = 0 := hBres _ _ hres
      rw [map_sub] at h2
      linarith
    have h3 : q k A = q k (sec i) := hqres k _ _ (by rw [map_sub, sub_eq_zero] at hres; exact hres)
    rw [h1, h3]
    exact h i
  have hBinj : Function.Injective Bh := by
    rw [injective_iff_map_eq_zero]
    intro i hi
    have hall : ∀ k, p k (sec i) ≤ 0 := by
      intro k
      have h1 : ∀ j : I, |B (sec i) (sec j)| ≤ 0 * q k (sec j) := by
        intro j
        have : B (sec i) (sec j) = 0 := by
          rw [← hBh, hi]
          rfl
        simp [this]
      have := h4 k _ (hsecSl i) 0 le_rfl (hextend _ _ k h1)
      simpa using this
    have hY : Y (sec i) = 0 := le_antisymm (hYp _ _ hall) (hY0 _)
    have := (hYdef _).1 hY
    rw [hressec] at this
    exact Subtype.ext this
  have hBsurj : Function.Surjective Bh :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := I)).symm).1 hBinj
  let Beq : I ≃ₗ[ℝ] Module.Dual ℝ I := LinearEquiv.ofBijective Bh ⟨hBinj, hBsurj⟩
  have hBeq : ∀ (φ : Module.Dual ℝ I) (j : I), B (sec (Beq.symm φ)) (sec j) = φ j := by
    intro φ j
    have : Bh (Beq.symm φ) = φ := Beq.apply_symm_apply φ
    rw [← hBh, this]
  let Φ : I → Module.Dual ℝ I := fun i => Bh i - (G (sec i)) ∘ₗ sec
  let Tf : I → I := fun i => Beq.symm (Φ i)
  have hTf : ∀ i j, B (sec (Tf i)) (sec j) = B (sec i) (sec j) - G (sec i) (sec j) := by
    intro i j
    exact hBeq (Φ i) j
  set r' : ℝ := 2 * Ca * ε with hr'
  have hr'0 : 0 < r' := by positivity
  have hsmall' : 4 * Ca * K * r' ≤ 1 := by
    refine le_trans ?_ hsmall
    have : 0 ≤ 4 * Ca * K := by positivity
    exact mul_le_mul_of_nonneg_left hr this
  have hmaps : Set.MapsTo Tf (Metric.closedBall 0 r') (Metric.closedBall 0 r') := by
    intro i hi
    rw [mem_closedBall_zero_iff, hnorm] at hi ⊢
    have hU : Y (sec i) ≤ r := hi.trans hr
    have hb : ∀ k, p k (sec (Tf i)) ≤ Ca * (K * r' * r' + ε) := by
      intro k
      refine h4 k _ (hsecSl _) _ (by positivity) (hextend _ _ k ?_)
      intro j
      have h1 := hlip (sec i) (hsecSl i) 0 Sl.zero_mem hU (by rw [hY00]; linarith) k (sec j) (hsecSl j)
      have h2 := hsrc k (sec j) (hsecSl j)
      have hq := hq0 k (sec j) (hsecSl j)
      rw [hTf]
      rw [sub_zero, hY00, add_zero] at h1
      have h3 : K * Y (sec i) * p k (sec i) * q k (sec j) ≤ K * r' * r' * q k (sec j) := by
        refine mul_le_mul_of_nonneg_right ?_ hq
        have hp := (hpY k (sec i)).trans hi
        have hp0 : 0 ≤ Y (sec i) := hY0 _
        calc K * Y (sec i) * p k (sec i) ≤ K * Y (sec i) * r' :=
              mul_le_mul_of_nonneg_left hp (by positivity)
          _ ≤ K * r' * r' := by
              refine mul_le_mul_of_nonneg_right ?_ hr'0.le
              exact mul_le_mul_of_nonneg_left hi hK.le
      have h5 : |B (sec i) (sec j) - G (sec i) (sec j)| ≤ |G (sec i) (sec j) - G 0 (sec j) - B (sec i) (sec j)| + |G 0 (sec j)| := by
        have : B (sec i) (sec j) - G (sec i) (sec j) = -(G (sec i) (sec j) - G 0 (sec j) - B (sec i) (sec j)) - G 0 (sec j) := by ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
      nlinarith
    refine hYp _ _ (fun k => (hb k).trans ?_)
    have h6 : Ca * K * r' * r' ≤ r' / 4 := by nlinarith
    have h7 : Ca * ε = r' / 2 := by rw [hr']; ring
    nlinarith
  have hlipOn : LipschitzOnWith (1 / 2) Tf (Metric.closedBall 0 r') := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro i hi i' hi'
    rw [mem_closedBall_zero_iff, hnorm] at hi hi'
    rw [dist_eq_norm, dist_eq_norm, hnorm, hnorm]
    have hU : Y (sec i) ≤ r := hi.trans hr
    have hU' : Y (sec i') ≤ r := hi'.trans hr
    rw [map_sub, map_sub]
    have hdm : sec (Tf i) - sec (Tf i') ∈ Sl := Sl.sub_mem (hsecSl _) (hsecSl _)
    have hd0 : 0 ≤ Y (sec i - sec i') := hY0 _
    have hb : ∀ k, p k (sec (Tf i) - sec (Tf i')) ≤ Ca * (K * (2 * r') * Y (sec i - sec i')) := by
      intro k
      refine h4 k _ hdm _ (by positivity) (hextend _ _ k ?_)
      intro j
      have h1 := hlip (sec i) (hsecSl i) (sec i') (hsecSl i') hU hU' k (sec j) (hsecSl j)
      have hq := hq0 k (sec j) (hsecSl j)
      have heq : B (sec (Tf i) - sec (Tf i')) (sec j) =
          -(G (sec i) (sec j) - G (sec i') (sec j) - B (sec i - sec i') (sec j)) := by
        rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, hTf, hTf]
        ring
      rw [heq, abs_neg]
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hq
      have hp := hpY k (sec i - sec i')
      have hsum : Y (sec i) + Y (sec i') ≤ 2 * r' := by linarith
      calc K * (Y (sec i) + Y (sec i')) * p k (sec i - sec i')
          ≤ K * (Y (sec i) + Y (sec i')) * Y (sec i - sec i') :=
            mul_le_mul_of_nonneg_left hp (mul_nonneg hK.le (add_nonneg (hY0 _) (hY0 _)))
        _ ≤ K * (2 * r') * Y (sec i - sec i') := by
            refine mul_le_mul_of_nonneg_right ?_ hd0
            exact mul_le_mul_of_nonneg_left hsum hK.le
    have := hYp _ _ hb
    refine this.trans ?_
    have hc : Ca * (K * (2 * r')) ≤ 1 / 2 := by nlinarith
    have : Ca * (K * (2 * r') * Y (sec i - sec i')) = (Ca * (K * (2 * r'))) * Y (sec i - sec i') := by ring
    rw [this]
    simpa using mul_le_mul_of_nonneg_right hc hd0
  have hc : ContractingWith (1 / 2) (hmaps.restrict Tf _ _) :=
    ⟨by norm_num, hmaps.lipschitzOnWith_iff_restrict.1 hlipOn⟩
  obtain ⟨i, hi, hfix, -⟩ := ContractingWith.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmaps hc (x := 0) (by simp [hr'0.le]) (edist_ne_top _ _)
  refine ⟨sec i, hsecSl i, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, hnorm] at hi
    exact hi
  · have hzero : ∀ j : I, G (sec i) (sec j) = 0 := by
      intro j
      have h1 := hTf i j
      have h2 : Tf i = i := hfix
      rw [h2] at h1
      linarith
    intro A hA
    obtain ⟨j, hj, hres⟩ := hdecomp A hA
    rw [mem_closedBall_zero_iff, hnorm] at hi
    have hU : Y (sec i) ≤ r := hi.trans hr
    have k : ι := Classical.arbitrary ι
    have hqz : q k (A - sec j) = 0 := by
      rw [← hq00 k]
      exact hqres k _ _ (by rw [hres, map_zero])
    have h1 := hlip (sec i) (hsecSl i) 0 Sl.zero_mem hU (by rw [hY00]; linarith) k _ hj
    rw [hqz, mul_zero, sub_zero, hBres _ _ hres, sub_zero] at h1
    have h2 := hsrc k _ hj
    rw [hqz, mul_zero] at h2
    have h3 : G 0 (A - sec j) = 0 := abs_nonpos_iff.1 h2
    have h4' : G (sec i) (A - sec j) = 0 := by
      rw [h3, sub_zero] at h1
      exact abs_nonpos_iff.1 h1
    have h5 := hzero j
    rw [map_sub, h5, sub_zero] at h4'
    exact h4'
variable {F : BlockFrame}
def quarticPart (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4))
def curlPart (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2)
def coarseLevelPart (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) (j : ℕ) : ℝ :=
  Real.sqrt (∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
def coarsePart (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (F.top - 1), coarseLevelPart S B U w j ^ 2)
theorem localNormSq_eq_parts (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    localNormSq S B R U w =
      quarticPart S B U w ^ 2 + curlPart S B R U w ^ 2 + coarsePart S B U w ^ 2 := by
  have h1 : quarticPart S B U w ^ 2 = Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : curlPart S B R U w ^ 2 = ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h3 : coarsePart S B U w ^ 2 = ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    unfold coarsePart
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [h1, h2, h3]
  rfl
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem weightedNorm_chartShift_le (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    weightedNorm S R (chartMove U A t) w ≤ weightedNorm S R U w + |t| * weightedNorm S R A w := by apply _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_chartMove_le <;> assumption
theorem weightedNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ weightedNorm S R U w := Real.sqrt_nonneg _
theorem weightedNorm_sq (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    weightedNorm S R U w ^ 2 = ∑ z ∈ S, localNormSq S (cellBall S z 3) R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_sq <;> assumption
theorem weightedNorm_congr (S : Finset F.Cell) (R : F.FieldChain) (U U' : ChainChart F)
    (w : F.SiteWeights) (h : ChartEqOnBonds S U U') : weightedNorm S R U w = weightedNorm S R U' w := by apply _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_congr <;> assumption
theorem chart_ext {U U' : ChainChart F} (h1 : U.fine = U'.fine) (h2 : U.coarse = U'.coarse) : U = U' := by apply _root_.YangMills.Construction.CoordinateSeminorms.chainChart_ext <;> assumption
theorem weightedNorm_eq_zero_of_agree_zero (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) (h : ChartEqOnBonds S U (chartZero F)) : weightedNorm S R U w = 0 := by apply _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_eq_zero_of_chartEq <;> assumption
theorem enclosingCell_mem {S : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem mem_sitesOfCells_of_mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}
    (hb : b ∈ innerBonds S j) : b.1 ∈ sitesOfCells S j := by
  have := (Finset.mem_filter.1 hb).1
  exact (Finset.mem_product.1 this).1
theorem mem_cellBall_self {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) : z ∈ cellBall S z 3 := by apply _root_.YangMills.Construction.GaugedCriticality.mem_cellBall_self <;> assumption
theorem agree_zero_of_weightedNorm_eq_zero (S : Finset F.Cell) (hL : Odd F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) (hw : ∀ j x, 0 < w j x) (h : weightedNorm S R U w = 0) :
    ChartEqOnBonds S U (chartZero F) := by apply _root_.YangMills.Construction.CoordinateSeminorms.chartEq_zero_of_weightedNorm_eq_zero <;> assumption
theorem decayWeights_pos (hL : 0 < F.blockSide) (del θ : ℝ) (p : F.Site 0) (y0 : F.Cell) (j : ℕ)
    (x : F.Site j) : 0 < decayWeights F del θ p y0 j x := by apply _root_.YangMills.Construction.CoordinateSeminorms.decayWeights_pos <;> assumption
theorem bddAbove_weightedNorm_decay (S : Finset F.Cell) (hL : 0 < F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (del : ℝ) (hdel : 0 ≤ del) :
    BddAbove (Set.range fun y0 : F.Cell => weightedNorm S R U (decayWeights F del 0 0 y0)) := by apply _root_.YangMills.Construction.CoordinateSeminorms.bddAbove_weightedNorm_decay <;> assumption
instance instNonemptyCell : Nonempty F.Cell := ⟨0⟩
theorem supWeightedNorm_nonneg (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) :
    0 ≤ supWeightedNorm S del R U :=
  Real.iSup_nonneg fun _ => weightedNorm_nonneg _ _ _ _
theorem weightedNorm_le_supWeightedNorm (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (hdel : 0 ≤ del)
    (R : F.FieldChain) (U : ChainChart F) (y0 : F.Cell) :
    weightedNorm S R U (decayWeights F del 0 0 y0) ≤ supWeightedNorm S del R U :=
  le_ciSup (bddAbove_weightedNorm_decay S hL R U del hdel) y0
theorem supWeightedNorm_le (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) (β : ℝ)
    (h : ∀ y0, weightedNorm S R U (decayWeights F del 0 0 y0) ≤ β) : supWeightedNorm S del R U ≤ β :=
  ciSup_le h
theorem supWeightedNorm_chartShift_le (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (hdel : 0 ≤ del)
    (R : F.FieldChain) (U A : ChainChart F) (t : ℝ) :
    supWeightedNorm S del R (chartMove U A t) ≤ supWeightedNorm S del R U + |t| * supWeightedNorm S del R A := by apply _root_.YangMills.Construction.CoordinateSeminorms.supWeightedNorm_chartMove_le <;> assumption
theorem supWeightedNorm_chartSmul (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (R : F.FieldChain)
    (A : ChainChart F) (t : ℝ) :
    supWeightedNorm S del R (chartSmul t A) = |t| * supWeightedNorm S del R A := by apply _root_.YangMills.Construction.CoordinateSeminorms.supWeightedNorm_smul <;> assumption
theorem gaugeMap_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) (s : F.Site 0) :
    gaugeMap S V R (fun x k => u x k + t • v x k) s =
      gaugeMap S V R u s + t • gaugeMap S V R v s := by apply _root_.YangMills.Construction.CoordinateSeminorms.gaugeMap_add_smul <;> assumption
abbrev ChartVector (F : BlockFrame) : Type :=
  (F.Site 0 → Fin 4 → imaginaryQuaternions) × ((j : ℕ) → F.Site (j + 1) → Fin 4 → imaginaryQuaternions)
def toChart (x : ChartVector F) : ChainChart F := ⟨x.1, x.2⟩
def ofChart (U : ChainChart F) : ChartVector F := (U.fine, U.coarse)
theorem toChart_ofChart (U : ChainChart F) : toChart (ofChart U) = U := rfl
theorem toChart_add (x y : ChartVector F) : toChart (x + y) = chartSum (toChart x) (toChart y) := by apply _root_.YangMills.Construction.CoordinateSeminorms.toChart_add <;> assumption
theorem toChart_smul (t : ℝ) (x : ChartVector F) : toChart (t • x) = chartSmul t (toChart x) := by apply _root_.YangMills.Construction.CoordinateSeminorms.toChart_smul <;> assumption
theorem toChart_sub (x y : ChartVector F) : toChart (x - y) = chartSub (toChart x) (toChart y) := by
  apply chart_ext
  · funext a i
    simp [toChart, chartSub, chartMove, sub_eq_add_neg]
    exact (neg_one_smul ℝ _).symm
  · funext j a i
    simp [toChart, chartSub, chartMove, sub_eq_add_neg]
    exact (neg_one_smul ℝ _).symm
abbrev ReadValues (S : Finset F.Cell) : Type :=
  (↥(innerBonds S 0) → imaginaryQuaternions) ×
    ((j : Fin (F.top - 1)) → ↥(innerBonds S (j.1 + 1)) → imaginaryQuaternions)
def readValues (S : Finset F.Cell) : ChartVector F →ₗ[ℝ] ReadValues S where
  toFun x := (fun b => x.1 b.1.1 b.1.2, fun j c => x.2 j.1 c.1.1 c.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem readValues_eq_iff (S : Finset F.Cell) (x y : ChartVector F) :
    readValues S x = readValues S y ↔ ChartEqOnBonds S (toChart x) (toChart y) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine ⟨fun b hb => congrFun h1 ⟨b, hb⟩, fun j hj c hc => ?_⟩
    exact congrFun (congrFun h2 ⟨j, by omega⟩) ⟨c, hc⟩
  · intro h
    refine Prod.ext ?_ ?_
    · funext b
      exact h.1 b.1 b.2
    · funext j c
      exact h.2 j.1 (by have := j.2; omega) c.1 c.2
theorem gaugeMap_const_zero (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (s : F.Site 0) :
    gaugeMap S V R (fun _ _ => 0) s = 0 := by apply _root_.YangMills.Construction.CoordinateSeminorms.gaugeMap_zero <;> assumption
def sliceSubmodule (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) :
    Submodule ℝ (ChartVector F) where
  carrier := {x | InGaugeSlice S V R x.1}
  add_mem' := by
    intro x y hx hy s hs
    have h := gaugeMap_add_smul S V R (fun a i => (x.1 a i : ℍ[ℝ])) (fun a i => (y.1 a i : ℍ[ℝ])) 1 s
    have e : (fun a i => (((x + y).1 a i : imaginaryQuaternions) : ℍ[ℝ])) =
        fun a i => (x.1 a i : ℍ[ℝ]) + (1 : ℝ) • (y.1 a i : ℍ[ℝ]) := by
      funext a i
      simp
    rw [e, h, hx s hs, hy s hs]
    simp
  zero_mem' := by
    intro s _
    exact gaugeMap_const_zero S V R s
  smul_mem' := by
    intro t x hx s hs
    have h := gaugeMap_add_smul S V R (fun _ _ => 0) (fun a i => (x.1 a i : ℍ[ℝ])) t s
    have e : (fun a i => (((t • x).1 a i : imaginaryQuaternions) : ℍ[ℝ])) =
        fun a i => (0 : ℍ[ℝ]) + t • (x.1 a i : ℍ[ℝ]) := by
      funext a i
      simp
    rw [e, h, hx s hs, gaugeMap_const_zero]
    simp
theorem mem_sliceSubmodule {S : Finset F.Cell} {V : F.GaugeField F.top} {R : F.GaugeField 0}
    {x : ChartVector F} : x ∈ sliceSubmodule S V R ↔ InGaugeSlice S V R (toChart x).fine := Iff.rfl
theorem cellSupDist_comm (a b : F.Cell) : cellSupDist a b = cellSupDist b a := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem expPowerWeights_zero (p : F.Site 0) : classWeight F (fun _ => 0) 0 p = oneSiteWeights F := by apply _root_.YangMills.Construction.CoordinateSeminorms.classWeight_zero <;> assumption
theorem isExpPowerPair_zero (θ del : ℝ) (hdel : 0 ≤ del) : IsExpPowerPair F θ del (fun _ => 0) 0 :=
  ⟨Or.inr (Or.inl rfl), fun y y' => by
    simp only [sub_self, abs_zero]
    positivity⟩
theorem isExpPowerPair_decay (θ del θ' : ℝ) (hdel : 0 ≤ del) (hθ : θ' = θ ∨ θ' = 0 ∨ θ' = -θ)
    (y0 : F.Cell) : IsExpPowerPair F θ del (fun y => -del * (cellSupDist y y0 : ℝ)) θ' := by
  refine ⟨hθ, fun y y' => ?_⟩
  have t1 : (cellSupDist y y0 : ℝ) ≤ cellSupDist y y' + cellSupDist y' y0 := by
    exact_mod_cast cellSupDist_triangle y y' y0
  have t2 : (cellSupDist y' y0 : ℝ) ≤ cellSupDist y y' + cellSupDist y y0 := by
    have := cellSupDist_triangle y' y y0
    rw [cellSupDist_comm y' y] at this
    exact_mod_cast this
  have e : -del * (cellSupDist y y0 : ℝ) - -del * (cellSupDist y' y0 : ℝ) =
      del * ((cellSupDist y' y0 : ℝ) - cellSupDist y y0) := by ring
  rw [e, abs_mul, abs_of_nonneg hdel]
  refine mul_le_mul_of_nonneg_left ?_ hdel
  rw [abs_le]
  constructor <;> linarith
theorem quadraticFormNormSq_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) : 0 ≤ quadraticFormNormSq a S R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.quadraticFormNormSq_nonneg <;> assumption
set_option maxHeartbeats 1000000 in
theorem exists_sliceCriticalPoint_of_estimates (a θ del Ca4 Ct cT CT c3 Ca2 rL s : ℝ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (hL : Odd F.blockSide) (ha : 0 < a) (hdel : 0 < del) (hCa4 : 0 < Ca4)
    (hCt : 0 < Ct) (hCT : 0 < CT) (hs : 0 < s) (hs1 : s ≤ 1) (hrL : 0 < rL)
    (hT : ActionTaylorBounds a θ del Ct cT CT s S V)
    (h4 : ∀ (φ : F.Cell → ℝ) (p : F.Site 0) (θ' : ℝ), IsExpPowerPair F θ del φ θ' →
      ∀ (U : ChainChart F) (f : ChainChart F → ℝ) (B : ℝ), 0 ≤ B →
        InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
        (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
          referenceSecondDeriv a S (referenceFieldChain S V) V U A = f A) →
        (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
          |f A| ≤ B * weightedNorm S (referenceFieldChain S V) A
            (invertedWeights (classWeight F φ θ' p))) →
        weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) ≤ Ca4 * B)
    (h3 : ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ c3 →
      (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        IsStationaryAlong a S (referenceFieldChain S V) V U A) →
      ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A)
    (h2 : ∀ U : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
      weightedNorm S (referenceFieldChain S V) U (oneSiteWeights F) ≤
        Ca2 * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) U (oneSiteWeights F)))
    (hrT : rL ≤ cT) (hr3 : rL ≤ c3) (hsm : 4 * Ca4 * CT * rL ≤ 1)
    (hfl : CT * (s + rL) * Ca2 ^ 2 ≤ 3 / 4)
    (hball : 2 * Ca4 * (Ct * s + CT * s ^ 2) ≤ rL) :
    ∃ U : ChainChart F, IsSliceCriticalPoint a θ del (Ca4 * Ct) rL
      (2 * (Ca4 * CT + Ca4 * CT * (2 * Ca4 * (Ct + CT)) * (Ca4 * Ct))) s S V U := by
  classical
  have hLpos : 0 < F.blockSide := hL.pos
  set R := referenceFieldChain S V with hR
  set Sl := sliceSubmodule S V (R 0) with hSl
  let Y : ChartVector F → ℝ := fun x => supWeightedNorm S del R (toChart x)
  let pw : F.Cell → F.SiteWeights := fun y0 => decayWeights F del 0 0 y0
  let pn : F.Cell → ChartVector F → ℝ := fun y0 x => weightedNorm S R (toChart x) (pw y0)
  let qn : F.Cell → ChartVector F → ℝ := fun y0 x => weightedNorm S R (toChart x) (invertedWeights (pw y0))
  have hpw : ∀ y0 j (x : F.Site j), 0 < pw y0 j x := fun y0 j x => decayWeights_pos hLpos del 0 0 y0 j x
  let B : ChartVector F →ₗ[ℝ] ChartVector F →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x y => referenceSecondDeriv a S R V (toChart x) (toChart y))
    (fun x x' y => by rw [toChart_add, hT.hessian_add_left])
    (fun t x y => by rw [toChart_smul, hT.hessian_smul_left]; rfl)
    (fun x y y' => by rw [toChart_add, hT.hessian_add_right])
    (fun t x y => by rw [toChart_smul, hT.hessian_smul_right]; rfl)
  have hB : ∀ x y, B x y = referenceSecondDeriv a S R V (toChart x) (toChart y) := fun _ _ => rfl
  let G : ChartVector F → ChartVector F →ₗ[ℝ] ℝ := fun x =>
    if h : supWeightedNorm S del R (toChart x) ≤ cT then
      { toFun := fun y => chartFirstVariation a S R V (toChart x) (toChart y)
        map_add' := fun y y' => by rw [toChart_add, hT.variation_add _ _ _ h]
        map_smul' := fun t y => by rw [toChart_smul, hT.variation_smul _ _ _ h]; rfl }
    else 0
  have hG : ∀ x y, Y x ≤ cT → G x y = chartFirstVariation a S R V (toChart x) (toChart y) := by
    intro x y h
    have h' : supWeightedNorm S del R (toChart x) ≤ cT := h
    simp only [G, dif_pos h']
    rfl
  have hYle : ∀ x y0, pn y0 x ≤ Y x := fun x y0 =>
    weightedNorm_le_supWeightedNorm S hLpos del hdel.le R (toChart x) y0
  have hY0 : ∀ x, 0 ≤ Y x := fun x => supWeightedNorm_nonneg S del R (toChart x)
  have hYzero : Y 0 = 0 := by
    refine le_antisymm ?_ (hY0 0)
    refine supWeightedNorm_le _ _ _ _ _ fun y0 => ?_
    exact (weightedNorm_eq_zero_of_agree_zero S R (toChart 0) _ ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩).le
  have hYadd : ∀ x y, Y (x + y) ≤ Y x + Y y := by
    intro x y
    have := supWeightedNorm_chartShift_le S hLpos del hdel.le R (toChart x) (toChart y) 1
    simpa [Y, toChart_add, chartSum] using this
  have hYsmul : ∀ (t : ℝ) x, Y (t • x) = |t| * Y x := by
    intro t x
    show supWeightedNorm S del R (toChart (t • x)) = _
    rw [toChart_smul]
    exact supWeightedNorm_chartSmul S hLpos del R (toChart x) t
  have hsame0 : ∀ x, readValues S x = 0 → ChartEqOnBonds S (toChart x) (chartZero F) := by
    intro x hx
    have := (readValues_eq_iff S x 0).1 (by rw [hx, map_zero])
    exact this
  have hYdef : ∀ x, Y x = 0 ↔ readValues S x = 0 := by
    intro x
    constructor
    · intro h
      have hp : weightedNorm S R (toChart x) (pw 0) = 0 :=
        le_antisymm ((hYle x 0).trans h.le) (weightedNorm_nonneg _ _ _ _)
      have := agree_zero_of_weightedNorm_eq_zero S hL R (toChart x) _ (hpw 0) hp
      have h2 := (readValues_eq_iff S x 0).2 this
      rw [h2, map_zero]
    · intro h
      refine le_antisymm ?_ (hY0 x)
      refine supWeightedNorm_le _ _ _ _ _ fun y0 => ?_
      exact (weightedNorm_eq_zero_of_agree_zero S R (toChart x) _ (hsame0 x h)).le
  have hqres : ∀ y0 x y, readValues S x = readValues S y → qn y0 x = qn y0 y := by
    intro y0 x y h
    exact weightedNorm_congr S R _ _ _ ((readValues_eq_iff S x y).1 h)
  have hq00 : ∀ y0, qn y0 0 = 0 := fun y0 =>
    weightedNorm_eq_zero_of_agree_zero S R _ _ ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  have hBres : ∀ Z A, readValues S A = 0 → B Z A = 0 := by
    intro Z A hA
    have h1 := hT.hessian_le (fun _ => 0) 0 0 (isExpPowerPair_zero θ del hdel.le) (toChart Z) (toChart A)
    rw [weightedNorm_eq_zero_of_agree_zero S R (toChart A) _ (hsame0 A hA), mul_zero] at h1
    exact abs_nonpos_iff.1 h1
  have h4' : ∀ y0, ∀ Z ∈ Sl, ∀ β : ℝ, 0 ≤ β → (∀ A ∈ Sl, |B Z A| ≤ β * qn y0 A) →
      pn y0 Z ≤ Ca4 * β := by
    intro y0 Z hZ β hβ hb
    exact h4 (fun y => -del * (cellSupDist y y0 : ℝ)) 0 0
      (isExpPowerPair_decay θ del 0 hdel.le (Or.inr (Or.inl rfl)) y0) (toChart Z)
      (fun A => referenceSecondDeriv a S R V (toChart Z) A) β hβ hZ (fun _ _ => rfl) (fun A hA => hb (ofChart A) hA)
  obtain ⟨lsrc, hlsrc_add, hlsrc_smul, hlsrc⟩ := hT.linear_source
  have hlipW : ∀ U ∈ Sl, ∀ U' ∈ Sl, Y U ≤ rL → Y U' ≤ rL → ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0),
      IsExpPowerPair F θ del φ θ' → ∀ A,
      |G U A - G U' A - B (U - U') A| ≤ CT * (Y U + Y U') *
        weightedNorm S R (toChart (U - U')) (classWeight F φ θ' p) *
        weightedNorm S R (toChart A) (invertedWeights (classWeight F φ θ' p)) := by
    intro U _ U' _ hU hU' φ θ' p hcl A
    rw [hG U A (hU.trans hrT), hG U' A (hU'.trans hrT), hB, toChart_sub]
    exact hT.variation_sub_hessian_le _ _ (hU.trans hrT) (hU'.trans hrT) φ θ' p hcl (toChart A)
  have hq0 : ∀ y0 x, 0 ≤ qn y0 x := fun y0 x => weightedNorm_nonneg _ _ _ _
  have hp0 : ∀ y0 x, 0 ≤ pn y0 x := fun y0 x => weightedNorm_nonneg _ _ _ _
  have hYp : ∀ x β, (∀ y0, pn y0 x ≤ β) → Y x ≤ β := fun x β h => supWeightedNorm_le _ _ _ _ _ h
  have hclass0 : ∀ y0 : F.Cell, IsExpPowerPair F θ del (fun y => -del * (cellSupDist y y0 : ℝ)) 0 := fun y0 =>
    isExpPowerPair_decay θ del 0 hdel.le (Or.inr (Or.inl rfl)) y0
  have solve : ∀ (ℓ : ChartVector F →ₗ[ℝ] ℝ) (ε : ℝ), 0 < ε → (∀ y0, ∀ A ∈ Sl, |ℓ A| ≤ ε * qn y0 A) →
      ∃ Z ∈ Sl, ∀ A ∈ Sl, B Z A = ℓ A := by
    intro ℓ ε hε hℓ
    obtain ⟨Z, hZ, -, hz⟩ := exists_zero_of_contracting_family Sl (readValues S) Y pn qn B (fun U => B U - ℓ)
      hY0 hYadd hYsmul hYdef (fun y0 x => hYle x y0) hYp hqres hq00 hBres Ca4 ε
      (1 / (4 * Ca4 * (2 * Ca4 * ε))) (2 * Ca4 * ε) hCa4 hε (by positivity) h4'
      (fun y0 A hA => by
        simpa using hℓ y0 A hA)
      (fun U _ U' _ _ _ y0 A _ => by
        have e : (B U - ℓ) A - (B U' - ℓ) A - B (U - U') A = 0 := by
          simp
        rw [e, abs_zero]
        have := hY0 U
        have := hY0 U'
        have := hp0 y0 (U - U')
        have := hq0 y0 A
        positivity)
      le_rfl (by field_simp; norm_num)
    refine ⟨Z, hZ, fun A hA => ?_⟩
    have := hz A hA
    simp only [LinearMap.sub_apply] at this
    linarith
  set ε : ℝ := Ct * s + CT * s ^ 2 with hε
  have hεpos : 0 < ε := by positivity
  have hG0 : ∀ A, G 0 A = chartFirstVariation a S R V (chartZero F) (toChart A) := fun A =>
    hG 0 A (by rw [hYzero]; exact hrL.le.trans hrT)
  have hsrc : ∀ y0, ∀ A ∈ Sl, |G 0 A| ≤ ε * qn y0 A := by
    intro y0 A _
    obtain ⟨h1, h2'⟩ := hlsrc (toChart A) 0 y0 0 (Or.inr rfl)
    rw [hG0]
    have h3' : |chartFirstVariation a S R V (chartZero F) (toChart A)| ≤
        |chartFirstVariation a S R V (chartZero F) (toChart A) - lsrc (toChart A)| + |lsrc (toChart A)| := by
      have := abs_add_le (chartFirstVariation a S R V (chartZero F) (toChart A) - lsrc (toChart A))
        (lsrc (toChart A))
      simpa using this
    have e : ε * qn y0 A = CT * s ^ 2 * weightedNorm S R (toChart A)
          (invertedWeights (decayWeights F del 0 0 y0)) +
        Ct * s * weightedNorm S R (toChart A) (invertedWeights (decayWeights F del 0 0 y0)) := by
      simp only [qn, pw, hε]
      ring
    rw [e]
    linarith
  have hlip : ∀ U ∈ Sl, ∀ U' ∈ Sl, Y U ≤ rL → Y U' ≤ rL → ∀ y0, ∀ A ∈ Sl,
      |G U A - G U' A - B (U - U') A| ≤ CT * (Y U + Y U') * pn y0 (U - U') * qn y0 A := by
    intro U hU U' hU' h1 h2' y0 A _
    exact hlipW U hU U' hU' h1 h2' _ 0 0 (hclass0 y0) A
  obtain ⟨U0, hU0, hU0Y, hU0z⟩ := exists_zero_of_contracting_family Sl (readValues S) Y pn qn B G
    hY0 hYadd hYsmul hYdef (fun y0 x => hYle x y0) hYp hqres hq00 hBres Ca4 ε CT rL hCa4 hεpos hCT h4'
    hsrc hlip hball hsm
  have hU0r : Y U0 ≤ rL := hU0Y.trans hball
  have hU0T : supWeightedNorm S del R (toChart U0) ≤ cT := hU0r.trans hrT
  have hsliceC : ∀ A : ChainChart F, InGaugeSlice S V (R 0) A.fine →
      IsStationaryAlong a S R V (toChart U0) A := by
    intro A hA
    have h1 := hU0z (ofChart A) hA
    rw [hG U0 _ hU0T, toChart_ofChart] at h1
    have h2' := (hT.differentiableAt (toChart U0) A hU0T).hasDerivAt
    have h3' : deriv (fun τ : ℝ => chartAction a S R (chartMove (toChart U0) A τ) V) 0 = 0 := h1
    rw [h3'] at h2'
    exact h2'
  have hall := h3 (toChart U0) (hU0r.trans hr3) hsliceC
  have hYr0 : Y 0 ≤ rL := by rw [hYzero]; exact hrL.le
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hεle : ε ≤ (Ct + CT) * s := by
    have := mul_le_mul_of_nonneg_left hs2 hCT.le
    simp only [hε]
    nlinarith
  refine ⟨toChart U0, hU0, hU0r, hall, ?_, ?_, ?_⟩
  · intro U' hU'sl hU'r hU'c
    have hU'm : ofChart U' ∈ Sl := hU'sl
    have hdm : U0 - ofChart U' ∈ Sl := Sl.sub_mem hU0 hU'm
    have hbound : ∀ y0, pn y0 (U0 - ofChart U') ≤ 0 := by
      intro y0
      have hA : ∀ A ∈ Sl, |B (U0 - ofChart U') A| ≤ (CT * (2 * rL) * pn y0 (U0 - ofChart U')) * qn y0 A := by
        intro A hA
        have h1 := hlip U0 hU0 (ofChart U') hU'm hU0r hU'r y0 A hA
        have g1 : G U0 A = 0 := hU0z A hA
        have g2 : G (ofChart U') A = 0 := by
          rw [hG (ofChart U') A (hU'r.trans hrT)]
          exact (hU'c (toChart A) hA).deriv
        rw [g1, g2, sub_zero, zero_sub, abs_neg] at h1
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hq0 _ _))
        refine mul_le_mul_of_nonneg_right ?_ (hp0 _ _)
        refine mul_le_mul_of_nonneg_left ?_ hCT.le
        have hU'r' : Y (ofChart U') ≤ rL := hU'r
        linarith
      have h5 := h4' y0 (U0 - ofChart U') hdm (CT * (2 * rL) * pn y0 (U0 - ofChart U'))
        (mul_nonneg (by positivity) (hp0 _ _)) hA
      have h6 := hp0 y0 (U0 - ofChart U')
      have h7 : Ca4 * (CT * (2 * rL)) ≤ 1 / 2 := by nlinarith
      have h8 := mul_le_mul_of_nonneg_right h7 h6
      nlinarith
    have hp : weightedNorm S R (toChart (U0 - ofChart U')) (pw 0) = 0 :=
      le_antisymm (hbound 0) (hp0 _ _)
    have h9 := agree_zero_of_weightedNorm_eq_zero S hL R _ _ (hpw 0) hp
    constructor
    · intro b hb
      have e : U0.1 b.1 b.2 - U'.fine b.1 b.2 = 0 := h9.1 b hb
      exact sub_eq_zero.1 e
    · intro j hj c hc
      have e : U0.2 j c.1 c.2 - U'.coarse j c.1 c.2 = 0 := h9.2 j hj c hc
      exact sub_eq_zero.1 e
  · let ℓ0 : ChartVector F →ₗ[ℝ] ℝ :=
      { toFun := fun x => lsrc (toChart x)
        map_add' := fun x y => by rw [toChart_add, hlsrc_add]
        map_smul' := fun t x => by rw [toChart_smul, hlsrc_smul]; rfl }
    obtain ⟨Zl, hZl, hZlB⟩ := solve (-ℓ0) (Ct * s) (by positivity) (fun y0 A _ => by
      have h1 := (hlsrc (toChart A) 0 y0 0 (Or.inr rfl)).1
      simpa [ℓ0, abs_neg] using h1)
    have hadd : chartSum (toChart Zl) (toChart (U0 - Zl)) = toChart U0 := by
      rw [← toChart_add]
      congr 1
      abel
    refine ⟨toChart Zl, toChart (U0 - Zl), ?_, ?_⟩
    · rw [hadd]
      exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · intro p y0 θ' hθ'
      have hcl : IsExpPowerPair F θ del (fun y => -del * (cellSupDist y y0 : ℝ)) θ' :=
        isExpPowerPair_decay θ del θ' hdel.le (hθ'.elim Or.inl (fun h => Or.inr (Or.inl h))) y0
      have hw0 : ∀ j (x : F.Site j), 0 ≤ decayWeights F del θ' p y0 j x :=
        fun j x => (decayWeights_pos hLpos del θ' p y0 j x).le
      have hNL : weightedNorm S R (toChart Zl) (decayWeights F del θ' p y0) ≤ Ca4 * (Ct * s) := by
        refine h4 _ p θ' hcl (toChart Zl) (fun A => - lsrc A) (Ct * s) (by positivity) hZl
          (fun A hA => hZlB (ofChart A) hA) (fun A _ => ?_)
        rw [abs_neg]
        exact (hlsrc A p y0 θ' hθ').1
      set NL := weightedNorm S R (toChart Zl) (decayWeights F del θ' p y0) with hNLd
      set NR := weightedNorm S R (toChart (U0 - Zl)) (decayWeights F del θ' p y0) with hNRd
      set NU := weightedNorm S R (toChart U0) (decayWeights F del θ' p y0) with hNUd
      have hNU : NU ≤ NL + NR := by
        have := weightedNorm_chartShift_le S R (toChart Zl) (toChart (U0 - Zl)) 1 _ hw0
        have e : chartMove (toChart Zl) (toChart (U0 - Zl)) 1 = toChart U0 := hadd
        rw [e, abs_one, one_mul] at this
        exact this
      have hNR : NR ≤ Ca4 * (CT * s ^ 2 + CT * Y U0 * NU) := by
        have hrest : U0 - Zl ∈ Sl := Sl.sub_mem hU0 hZl
        refine h4 _ p θ' hcl (toChart (U0 - Zl)) (fun A => referenceSecondDeriv a S R V (toChart (U0 - Zl)) A)
          (CT * s ^ 2 + CT * Y U0 * NU) (add_nonneg (by positivity) (mul_nonneg
            (mul_nonneg hCT.le (supWeightedNorm_nonneg _ _ _ _)) (weightedNorm_nonneg _ _ _ _)))
          (mem_sliceSubmodule.1 hrest) (fun _ _ => rfl) (fun A hA => ?_)
        have e1 : referenceSecondDeriv a S R V (toChart (U0 - Zl)) A = B U0 (ofChart A) + lsrc A := by
          have h1 := hZlB (ofChart A) hA
          have h2' : B (U0 - Zl) (ofChart A) = B U0 (ofChart A) - B Zl (ofChart A) := by
            rw [map_sub, LinearMap.sub_apply]
          rw [h1] at h2'
          have h3' : (-ℓ0) (ofChart A) = - lsrc A := rfl
          rw [h3'] at h2'
          have h4'' : referenceSecondDeriv a S R V (toChart (U0 - Zl)) A = B (U0 - Zl) (ofChart A) := rfl
          rw [h4'', h2']
          ring
        have hl := hlipW U0 hU0 0 Sl.zero_mem hU0r hYr0 _ θ' p hcl (ofChart A)
        rw [hU0z (ofChart A) hA, sub_zero, hYzero, add_zero] at hl
        have hs' := (hlsrc A p y0 θ' hθ').2
        rw [← toChart_ofChart A] at hs'
        rw [← hG0 (ofChart A)] at hs'
        have e2 : referenceSecondDeriv a S R V (toChart (U0 - Zl)) A =
            -(G 0 (ofChart A) - lsrc A) - (0 - G 0 (ofChart A) - B U0 (ofChart A)) := by
          rw [e1]
          ring
        show |referenceSecondDeriv a S R V (toChart (U0 - Zl)) A| ≤ _
        rw [e2]
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
        have e3 : (CT * s ^ 2 + CT * Y U0 * NU) *
            weightedNorm S R A (invertedWeights
              (classWeight F (fun y => -del * (cellSupDist y y0 : ℝ)) θ' p)) =
            CT * s ^ 2 * weightedNorm S R A (invertedWeights (decayWeights F del θ' p y0)) +
              CT * Y U0 * NU * weightedNorm S R (toChart (ofChart A)) (invertedWeights
                (classWeight F (fun y => -del * (cellSupDist y y0 : ℝ)) θ' p)) := by
          rw [toChart_ofChart, add_mul]
          rfl
        rw [e3]
        exact add_le_add hs' hl
      have hNL0 : 0 ≤ NL := weightedNorm_nonneg _ _ _ _
      have hNR0 : 0 ≤ NR := weightedNorm_nonneg _ _ _ _
      have hYU0 : 0 ≤ Y U0 := hY0 U0
      set P : ℝ := Ca4 * CT with hP
      have hPpos : 0 < P := by positivity
      set D : ℝ := 2 * Ca4 * (Ct + CT) with hD
      have hYD : Y U0 ≤ D * s := by
        refine hU0Y.trans ?_
        have := mul_le_mul_of_nonneg_left hεle (by positivity : 0 ≤ 2 * Ca4)
        simp only [hD]
        nlinarith
      have hPY : P * Y U0 ≤ 1 / 4 := by
        have := mul_le_mul_of_nonneg_left hU0r hPpos.le
        simp only [hP] at this ⊢
        nlinarith
      have t1 : P * Y U0 * NU ≤ P * Y U0 * NL + P * Y U0 * NR := by
        have := mul_le_mul_of_nonneg_left hNU (mul_nonneg hPpos.le hYU0)
        linarith
      have t2 : P * Y U0 * NR ≤ 1 / 4 * NR := mul_le_mul_of_nonneg_right hPY hNR0
      have t3 : P * Y U0 * NL ≤ P * (D * s) * (Ca4 * (Ct * s)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hYD hPpos.le) hNL (by positivity) (by positivity)
      refine ⟨?_, ?_⟩
      · exact hNL.trans (le_of_eq (by ring))
      · have e : P * s ^ 2 + P * (D * s) * (Ca4 * (Ct * s)) = (P + P * D * (Ca4 * Ct)) * s ^ 2 := by ring
        have : NR * (3 / 4) ≤ (P + P * D * (Ca4 * Ct)) * s ^ 2 := by linarith
        have e2 : 2 * (Ca4 * CT + Ca4 * CT * (2 * Ca4 * (Ct + CT)) * (Ca4 * Ct)) * s ^ 2 =
            2 * ((P + P * D * (Ca4 * Ct)) * s ^ 2) := by
          simp only [hP, hD]
          ring
        rw [e2]
        linarith
  · intro A hA
    have h1 := hT.second_deriv_le (toChart U0) A hU0T
    have h2' := h2 A hA
    set N2 := quadraticFormNormSq a S R A (oneSiteWeights F) with hN2d
    set M := weightedNorm S R A (oneSiteWeights F) with hMd
    have hN2 : 0 ≤ N2 := quadraticFormNormSq_nonneg a ha.le _ _ _ _
    have hM0 : 0 ≤ M := weightedNorm_nonneg _ _ _ _
    have hM2 : M ^ 2 ≤ Ca2 ^ 2 * N2 := by
      have := pow_le_pow_left₀ hM0 h2' 2
      rw [mul_pow, Real.sq_sqrt hN2] at this
      exact this
    have hsum : s + supWeightedNorm S del R (toChart U0) ≤ s + rL := by
      have : supWeightedNorm S del R (toChart U0) ≤ rL := hU0r
      linarith
    have h3' : CT * (s + supWeightedNorm S del R (toChart U0)) * M ^ 2 ≤ 3 / 4 * N2 := by
      calc CT * (s + supWeightedNorm S del R (toChart U0)) * M ^ 2
          ≤ CT * (s + rL) * M ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hsum hCT.le
        _ ≤ CT * (s + rL) * (Ca2 ^ 2 * N2) :=
            mul_le_mul_of_nonneg_left hM2 (by positivity)
        _ = CT * (s + rL) * Ca2 ^ 2 * N2 := by ring
        _ ≤ 3 / 4 * N2 := mul_le_mul_of_nonneg_right hfl hN2
    have h4'' := (abs_le.1 h1).1
    linarith
theorem sliceCriticalPointStatement_proof (hW : weightedSliceEstimateStatement)
    (hS : criticalOnSliceStatement) (hN : sliceNormFormBoundStatement)
    (hT : actionTaylorBoundStatement) : sliceCriticalPointStatement := by
  intro a ha
  obtain ⟨θ, del, Ca4, hθ, hθ8, hdel, hdel8, hCa4, L₄, hW'⟩ := hW a ha
  obtain ⟨Ct, LT, hCt, hT'⟩ := hT a θ del ha hθ.le hθ8 hdel hdel8
  obtain ⟨L₃, hS'⟩ := hS a del ha hdel hdel8
  obtain ⟨c2, Ca2, L₂, hc2, hCa2, hN'⟩ := hN a ha
  refine ⟨θ, del, Ca4 * Ct, hθ, hθ8, hdel, hdel8, by positivity, max (max L₃ LT) (max L₂ L₄),
    fun L hLodd hLge => ?_⟩
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hLT : LT ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLge
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLge
  have hL4 : L₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLge
  obtain ⟨c4, hc4, h4⟩ := hW' L hLodd hL4
  obtain ⟨cT, CT, hcT, hCT, hTL⟩ := hT' L hLodd hLT
  obtain ⟨c3, hc3, hSL⟩ := hS' L hLodd hL3
  set e : ℝ := 3 / (8 * CT * Ca2 ^ 2) with he
  have hepos : 0 < e := by positivity
  set rL : ℝ := min (min cT c3) (min (1 / (4 * Ca4 * CT)) e) with hrLd
  have hrL : 0 < rL := lt_min (lt_min hcT hc3) (lt_min (by positivity) hepos)
  set sL : ℝ := min (min (min c4 cT) (min c3 c2)) (min 1 (min (rL / (2 * Ca4 * (Ct + CT))) e)) with hsLd
  have hsL : 0 < sL := lt_min (lt_min (lt_min hc4 hcT) (lt_min hc3 hc2))
    (lt_min one_pos (lt_min (by positivity) hepos))
  refine ⟨rL, sL, 2 * (Ca4 * CT + Ca4 * CT * (2 * Ca4 * (Ct + CT)) * (Ca4 * Ct)), hrL, hsL,
    by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsle hcold
  have hLF : Odd F.blockSide := hFL ▸ hLodd
  have hL2F : L₂ ≤ F.blockSide := hFL ▸ hL2
  have hs4 : s ≤ c4 := hsle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsT : s ≤ cT := hsle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hs3 : s ≤ c3 := hsle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs2 : s ≤ c2 := hsle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hs1 : s ≤ 1 := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsr : s ≤ rL / (2 * Ca4 * (Ct + CT)) :=
    hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hse : s ≤ e := hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrT : rL ≤ cT := (min_le_left _ _).trans (min_le_left _ _)
  have hr3 : rL ≤ c3 := (min_le_left _ _).trans (min_le_right _ _)
  have hr4 : rL ≤ 1 / (4 * Ca4 * CT) := (min_le_right _ _).trans (min_le_left _ _)
  have hre : rL ≤ e := (min_le_right _ _).trans (min_le_right _ _)
  have hsm : 4 * Ca4 * CT * rL ≤ 1 := by
    have h0 : 0 < 4 * Ca4 * CT := by positivity
    have := mul_le_mul_of_nonneg_left hr4 h0.le
    rwa [mul_one_div_cancel h0.ne'] at this
  have hfl : CT * (s + rL) * Ca2 ^ 2 ≤ 3 / 4 := by
    have h0 : 0 < CT * Ca2 ^ 2 := by positivity
    have h1 : s + rL ≤ 2 * e := by linarith
    have h2 : CT * Ca2 ^ 2 * (2 * e) = 3 / 4 := by
      rw [he]
      field_simp
      norm_num
    have h3 := mul_le_mul_of_nonneg_left h1 h0.le
    calc CT * (s + rL) * Ca2 ^ 2 = CT * Ca2 ^ 2 * (s + rL) := by ring
      _ ≤ 3 / 4 := by rw [← h2]; exact h3
  have hball : 2 * Ca4 * (Ct * s + CT * s ^ 2) ≤ rL := by
    have h0 : 0 < 2 * Ca4 * (Ct + CT) := by positivity
    have h1 : 2 * Ca4 * (Ct + CT) * s ≤ rL := by
      rw [le_div_iff₀ h0] at hsr
      linarith
    have h2 : s ^ 2 ≤ s := by nlinarith
    have h3 : 2 * Ca4 * (Ct * s + CT * s ^ 2) ≤ 2 * Ca4 * (Ct + CT) * s := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * Ca4 * CT)
      nlinarith
    exact h3.trans h1
  refine exists_sliceCriticalPoint_of_estimates a θ del Ca4 Ct cT CT c3 Ca2 rL s S V hLF ha hdel hCa4 hCt hCT
    hs hs1 hrL (hTL F m S hFL hamb hm hreg s V hs hsT hcold) ?_ ?_ ?_ hrT hr3 hsm hfl hball
  · intro φ p θ' hcl U f Bd hBd hU hf hb
    exact h4 F m S hFL hamb hm hreg s V hs hs4 hcold φ p θ' hcl.1 hcl.2 U f Bd hBd hU hf hb
  · exact (hSL F m S hFL hamb hm hreg s V hs hs3 hcold)
  · intro U hU
    have := hN' F m S hLF hL2F hamb hm hreg s V hs hs2 hcold (fun _ => 0) 0 0 0 (by norm_num) (by norm_num)
      (by simp) U hU
    rw [expPowerWeights_zero] at this
    exact this
end YangMills.Construction.BlockAverages.SliceCriticalPoint
end
