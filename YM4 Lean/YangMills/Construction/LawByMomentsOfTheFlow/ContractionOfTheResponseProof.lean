import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACell
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfTheCurlOfAFlatChain
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.LawByMomentsOfTheFlow.PathFormAboutASite
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOnClosedForms
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion ENNReal
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields WeightedResponses TorusLumps StepCosts
open TopLevelSites TorusFrame ExponentialSums RenormalizationStepParameters
namespace MomentLaw
namespace ResponseContraction
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem intCast_cast_add (P m : ℕ) (h : P = m) (a b : ZMod m) :
    (((a + b).cast : ℤ) : ZMod P) = ((a.cast : ℤ) : ZMod P) + ((b.cast : ℤ) : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_add_of_eq <;> assumption
private theorem intCast_cast_intCast (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
private theorem torusSiteInFrame_add {H : BlockFrame} {m : ℕ} [NeZero m] (j : ℕ)
    (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x + y) = torusSiteInFrame H j x + torusSiteInFrame H j y := by
  funext k
  exact intCast_cast_add _ _ (hm k) (x k) (y k)
private theorem torusSiteInFrame_unitStep {H : BlockFrame} {m : ℕ} [NeZero m] (j : ℕ)
    (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by
  funext k
  have h := intCast_cast_intCast _ _ (hm k) ((Pi.single i 1 : Fin 4 → ℤ) k)
  have h2 : (TorusFields.unitStep m i) k = (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod m) := by
    by_cases hk : k = i
    · subst hk
      simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, hk]
  show ((((TorusFields.unitStep m i) k).cast : ℤ) : ZMod (H.period j k)) = _
  rw [h2, h]
  rfl
private theorem abs_curl_responseKernel_le {a ρA del C₃ C₄ : ℝ} {L L₃ L₄ : ℕ} [NeZero L]
    (hodd : Odd L) (h3 : L₃ ≤ L) (h4 : L₄ ≤ L) (hC₃ : 0 < C₃) (hC₄ : 0 < C₄)
    (hS : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
      L₃ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B →
      ∀ (Y : F.Cell) (p : F.Site F.depth) (e : Fin 4 × Fin 4), e ∈ orientedPlanes →
        cellSupDist (enclosingCell p) Y ≤ 2 →
        |plaquetteCurl (B F.depth) p e.1 e.2| ≤
          C₃ * (F.blockSide : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)))
    (hE : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
      L₄ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B → ∀ (z : F.Cell) (r : ℕ), r ≤ 24 →
        chainEnergyOnCells a B (cellBall z r) ≤ C₄ * Real.exp (-(2 * del * cellSupDist z c.1)))
    (hT : ∀ (F : BlockFrame) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions), F.blockSide = L →
      IsLargeCubicTorus F → ‖X‖ = 1 →
        ∃ B : FormChain F, IsFlatChain a b B ∧ IsAxialResponse b B (minimizerResponse a ρA b X))
    (u n : ℕ) [NeZero n] (hn : 64 ≤ n) (c : TorusBond n) (p : OrientedPlaquette (n * L)) :
    |curl (fun b => responseKernel a ρA L u b c) p.1| ≤
      C₃ * Real.sqrt C₄ * (L : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(del * TorusFields.supDist (parentBlock L p.1.1) c.1)) := by
  classical
  have hcub : IsLargeCubicTorus (torusFrame L u n) := ⟨n, hn, fun _ => rfl⟩
  obtain ⟨B, hf, ht⟩ := hT (torusFrame L u n)
    (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) unitGenerator rfl
    hcub norm_unitGenerator
  obtain ⟨⟨x, i, j⟩, hij⟩ := p
  have hij' : i < j := hij
  have hper : ∀ k, (torusFrame L u n).period (torusFrame L u n).depth k = n * L :=
    fun k => period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) k
  set x' := torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth x with hx'
  have e1 : curl (fun b => responseKernel a ρA L u b c) (x, i, j) =
      plaquetteCurl (minimizerResponse (F := torusFrame L u n) a ρA
        (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) unitGenerator) x' i j := by
    simp only [curl, plaquetteCurl, responseKernel]
    rw [torusSiteInFrame_add _ hper, torusSiteInFrame_add _ hper, torusSiteInFrame_unitStep _ hper,
      torusSiteInFrame_unitStep _ hper]
  have hmem : (i, j) ∈ orientedPlanes := by
    simp [orientedPlanes, hij']
  have e2 := ht.curl_eq x' (i, j) hmem
  have hself : cellSupDist (enclosingCell x') (enclosingCell x') ≤ 2 := by
    simp [cellSupDist]
  have hs := hS (torusFrame L u n) _ B hodd h3 hcub hf (enclosingCell x') x' (i, j) hmem hself
  have he := hE (torusFrame L u n) _ B hodd h4 hcub hf (enclosingCell x') 24 le_rfl
  have ed : cellSupDist (enclosingCell x') (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1) =
      TorusFields.supDist (parentBlock L x) c.1 := by
    have : NeZero (n * (torusFrame L u n).blockSide) := (inferInstance : NeZero (n * L))
    have e3 : enclosingCell x' = torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (parentBlock L x) :=
      enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) x
    rw [e3, cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
  simp only [ed] at he
  have hL : ((torusFrame L u n).blockSide : ℝ) = (L : ℝ) := rfl
  rw [hL] at hs
  show |curl (fun b => responseKernel a ρA L u b c) (x, i, j)| ≤ _
  rw [e1, e2]
  have hroot : Real.sqrt (chainEnergyOnCells a B (cellBall (enclosingCell x') 24)) ≤
      Real.sqrt C₄ * Real.exp (-(del * TorusFields.supDist (parentBlock L x) c.1)) := by
    calc Real.sqrt (chainEnergyOnCells a B (cellBall (enclosingCell x') 24))
        ≤ Real.sqrt (C₄ * Real.exp (-(2 * del * TorusFields.supDist (parentBlock L x) c.1))) := Real.sqrt_le_sqrt he
      _ = Real.sqrt C₄ * Real.exp (-(del * TorusFields.supDist (parentBlock L x) c.1)) := by
        rw [Real.sqrt_mul hC₄.le]
        congr 1
        have : -(2 * del * (TorusFields.supDist (parentBlock L x) c.1 : ℝ)) =
            2 * (-(del * TorusFields.supDist (parentBlock L x) c.1)) := by ring
        rw [this, two_mul, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  calc _ ≤ C₃ * (L : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (chainEnergyOnCells a B (cellBall (enclosingCell x') 24)) := hs
    _ ≤ C₃ * (L : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.sqrt C₄ * Real.exp (-(del * TorusFields.supDist (parentBlock L x) c.1))) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by ring
private theorem curl_responseMap_eq_sum (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
    (A : TorusBond n → ℝ) (p : TorusPlaquette (n * L)) :
    curl (responseMap a ρA L u A) p =
      ∑ c : TorusBond n, A c * curl (fun b => responseKernel a ρA L u b c) p := by
  simp only [curl, responseMap]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring
private theorem one_add_sq_le_exp {del d : ℝ} (hdel : 0 < del) (hdel1 : del ≤ 1) (hd : 0 ≤ d) :
    (1 + d) ^ 2 ≤ 64 / del ^ 2 * Real.exp 1 * Real.exp (del / 4 * d) := by
  set x := del / 8 * (1 + d) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : x ^ 2 ≤ Real.exp (2 * x) := by
    rw [two_mul, Real.exp_add, sq]
    exact mul_self_le_mul_self hx0 h1 |>.trans (le_of_eq rfl)
  have h3 : Real.exp (2 * x) ≤ Real.exp 1 * Real.exp (del / 4 * d) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hx]
    nlinarith
  have e : (1 + d) ^ 2 = 64 / del ^ 2 * x ^ 2 := by
    rw [hx]
    field_simp
    ring
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
private theorem exists_curlKernel {a ρA del Aa K κ : ℝ} {L u n : ℕ} [NeZero L] [NeZero n]
    (hdel : 0 < del) (hdel1 : del ≤ 1) (hAa : 0 ≤ Aa) (hK : 0 < K) (hκ0 : 0 ≤ κ) (hκ : κ ≤ del / 4)
    (hcl : ∀ A A' : TorusBond n → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
      curl (responseMap a ρA L u A) p = curl (responseMap a ρA L u A') p)
    (hF : ∀ (c : TorusBond n) (p : OrientedPlaquette (n * L)),
      |curl (fun b => responseKernel a ρA L u b c) p.1| ≤
        Aa * Real.exp (-(del * TorusFields.supDist (parentBlock L p.1.1) c.1)))
    (hpath : ∀ Y : TorusSite n, ∃ co : TorusBond n → OrientedPlaquette n → ℝ,
      (∀ c : TorusBond n, ∑ p : OrientedPlaquette n, |co c p| ≤ K * (1 + (TorusFields.supDist c.1 Y : ℝ)) ^ 2) ∧
      (∀ (c : TorusBond n) (p : OrientedPlaquette n), co c p ≠ 0 → TorusFields.supDist p.1.1 Y ≤ TorusFields.supDist c.1 Y + 1) ∧
      ∀ (A : TorusBond n → ℝ) (p : TorusPlaquette n),
        curl (fun c => ∑ p' : OrientedPlaquette n, co c p' * curl A p'.1) p = curl A p)
    (p : OrientedPlaquette (n * L)) :
    ∃ k : OrientedPlaquette n → ℝ, (∀ A : TorusBond n → ℝ, curl (responseMap a ρA L u A) p.1 =
        ∑ p' : OrientedPlaquette n, k p' * curl A p'.1) ∧
      ∑ p' : OrientedPlaquette n, |k p'| * Real.exp (κ * (1 + (TorusFields.supDist (parentBlock L p.1.1) p'.1.1 : ℝ))) ≤
        Aa * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 * (4 * expLatticeSum (del / 2)) := by
  classical
  set Y := parentBlock L p.1.1 with hY
  obtain ⟨co, hsum, hsupp, hcurl⟩ := hpath Y
  set F : TorusBond n → ℝ := fun c => curl (fun b => responseKernel a ρA L u b c) p.1 with hFdef
  refine ⟨fun p' => ∑ c, F c * co c p', fun A => ?_, ?_⟩
  · rw [hcl A (fun c => ∑ p' : OrientedPlaquette n, co c p' * curl A p'.1) (fun q => (hcurl A q).symm) p.1,
      curl_responseMap_eq_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [hFdef]
    ring
  · set g : OrientedPlaquette n → ℝ := fun p' => Real.exp (κ * (1 + (TorusFields.supDist Y p'.1.1 : ℝ))) with hg
    have hg0 : ∀ p', 0 ≤ g p' := fun p' => (Real.exp_pos _).le
    have hc : ∀ c : TorusBond n, |F c| * ∑ p' : OrientedPlaquette n, |co c p'| * g p' ≤
        Aa * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 * Real.exp (-(del / 2) * TorusFields.supDist c.1 Y) := by
      intro c
      set d : ℝ := (TorusFields.supDist c.1 Y : ℝ) with hd
      have hd0 : 0 ≤ d := Nat.cast_nonneg _
      have h1 : ∀ p', |co c p'| * g p' ≤ |co c p'| * Real.exp (κ * (2 + d)) := by
        intro p'
        by_cases h0 : co c p' = 0
        · simp [h0]
        · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          apply Real.exp_le_exp.mpr
          have h2 := hsupp c p' h0
          rw [supDist_comm] at h2
          have h3 : (TorusFields.supDist Y p'.1.1 : ℝ) ≤ d + 1 := by
            rw [hd]
            exact_mod_cast h2
          nlinarith
      have h2 : ∑ p' : OrientedPlaquette n, |co c p'| * g p' ≤
          K * (1 + d) ^ 2 * Real.exp (κ * (2 + d)) := by
        calc _ ≤ ∑ p' : OrientedPlaquette n, |co c p'| * Real.exp (κ * (2 + d)) :=
              Finset.sum_le_sum fun p' _ => h1 p'
          _ = (∑ p' : OrientedPlaquette n, |co c p'|) * Real.exp (κ * (2 + d)) := by rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hsum c) (Real.exp_pos _).le
      have h3 : Real.exp (κ * (2 + d)) ≤ Real.exp 1 * Real.exp (del / 4 * d) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      have h4 := one_add_sq_le_exp hdel hdel1 hd0
      have h5 : |F c| ≤ Aa * Real.exp (-(del * d)) := by
        have := hF c p
        rw [hd, supDist_comm]
        exact this
      calc |F c| * ∑ p' : OrientedPlaquette n, |co c p'| * g p'
          ≤ (Aa * Real.exp (-(del * d))) * (K * (1 + d) ^ 2 * Real.exp (κ * (2 + d))) :=
            mul_le_mul h5 h2 (Finset.sum_nonneg fun p' _ => mul_nonneg (abs_nonneg _) (hg0 p'))
              (by positivity)
        _ ≤ (Aa * Real.exp (-(del * d))) *
              (K * (64 / del ^ 2 * Real.exp 1 * Real.exp (del / 4 * d)) *
                (Real.exp 1 * Real.exp (del / 4 * d))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hK.le) h3 (Real.exp_pos _).le (by positivity)
        _ = Aa * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 *
              (Real.exp (-(del * d)) * Real.exp (del / 4 * d) * Real.exp (del / 4 * d)) := by ring
        _ = _ := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
    calc ∑ p' : OrientedPlaquette n, |∑ c, F c * co c p'| * g p'
        ≤ ∑ p' : OrientedPlaquette n, ∑ c, |F c| * (|co c p'| * g p') := by
          refine Finset.sum_le_sum fun p' _ => ?_
          calc |∑ c, F c * co c p'| * g p' ≤ (∑ c, |F c * co c p'|) * g p' :=
                mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (hg0 p')
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [abs_mul]
                ring
      _ = ∑ c, |F c| * ∑ p' : OrientedPlaquette n, |co c p'| * g p' := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
      _ ≤ ∑ c : TorusBond n, Aa * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 *
            Real.exp (-(del / 2) * TorusFields.supDist c.1 Y) := Finset.sum_le_sum fun c _ => hc c
      _ = Aa * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 *
            ∑ c : TorusBond n, Real.exp (-(del / 2) * TorusFields.supDist c.1 Y) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_bonds_exp_le (by positivity) Y Finset.univ) (by positivity)
private theorem sqrt_sum_sq_sum_le {ι : Type} [Fintype ι] (k : ι → ℝ) (g : ι → Fin 3 → ℝ) :
    Real.sqrt (∑ e : Fin 3, (∑ i, k i * g i e) ^ 2) ≤ ∑ i, |k i| * Real.sqrt (∑ e : Fin 3, g i e ^ 2) := by
  have hn : ∀ f : Fin 3 → ℝ, ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (∑ e, f e ^ 2) := by
    intro f
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have e : (WithLp.toLp 2 (fun e => ∑ i, k i * g i e) : EuclideanSpace ℝ (Fin 3)) =
      ∑ i, k i • (WithLp.toLp 2 (g i) : EuclideanSpace ℝ (Fin 3)) := by
    ext e
    simp
  rw [← hn, e]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, hn, Real.norm_eq_abs]
private theorem weightedCurvatureNorm_pushColours_le {a ρA κ θ : ℝ} {L u n : ℕ} [NeZero L] [NeZero n]
    (hk : ∀ p : OrientedPlaquette (n * L), ∃ k : OrientedPlaquette n → ℝ,
      (∀ A : TorusBond n → ℝ, curl (responseMap a ρA L u A) p.1 =
        ∑ p' : OrientedPlaquette n, k p' * curl A p'.1) ∧
      ∑ p' : OrientedPlaquette n, |k p'| * Real.exp (κ * (1 + (TorusFields.supDist (parentBlock L p.1.1) p'.1.1 : ℝ))) ≤ θ)
    (ω : TorusPlaquette (n * L) → ℝ) (ω' : TorusPlaquette n → ℝ) (hω : ∀ p, 0 < ω p) (hω' : ∀ p, 0 < ω' p)
    (hs : IsSlowlyVaryingPair L κ ω ω')
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal) (hq : 1 ≤ q)
    (hX : Measurable X) :
    weightedCurvatureNorm μ ω q (fun e => pushColours a ρA L u (X e)) ≤
      ENNReal.ofReal θ * weightedCurvatureNorm μ ω' q X := by
  classical
  have hN : ∀ p' : OrientedPlaquette n, ENNReal.ofReal (ω' p'.1) * eLpNorm (fun e => curlNorm (X e) p'.1) q μ ≤
      weightedCurvatureNorm μ ω' q X := fun p' =>
    le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (ω' p.1) * eLpNorm (fun e => curlNorm (X e) p.1) q μ) p'
  refine iSup_le fun p => ?_
  obtain ⟨k, hk1, hk2⟩ := hk p
  set ψ : OrientedPlaquette n → Ω → ℝ := fun p' w => curlNorm (X w) p'.1 with hψ
  have hmeas : ∀ p', Measurable (ψ p') := by
    intro p'
    have hb : ∀ (e : Fin 3) (b : TorusBond n), Measurable fun w => X w e b :=
      fun e b => (measurable_pi_apply b).comp ((measurable_pi_apply e).comp hX)
    simp only [hψ, curlNorm, curl]
    refine Measurable.sqrt (Finset.measurable_sum _ fun e _ => ?_)
    exact ((((hb e _).add (hb e _)).sub (hb e _)).sub (hb e _)).pow_const 2
  have hpt : ∀ w, curlNorm (pushColours a ρA L u (X w)) p.1 ≤ ∑ p', |k p'| * ψ p' w := by
    intro w
    have h1 := sqrt_sum_sq_sum_le k (fun p' e => curl (X w e) p'.1)
    simp only [curlNorm, pushColours, hψ]
    simp only [hk1]
    exact h1
  have hE1 : eLpNorm (fun e => curlNorm (pushColours a ρA L u (X e)) p.1) q μ ≤
      ∑ p', ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ := by
    calc eLpNorm (fun e => curlNorm (pushColours a ρA L u (X e)) p.1) q μ
        ≤ eLpNorm (∑ p', (|k p'| • ψ p')) q μ := by
          refine eLpNorm_mono_real fun w => ?_
          have h0 : 0 ≤ curlNorm (pushColours a ρA L u (X w)) p.1 := Real.sqrt_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg h0]
          simpa [Finset.sum_apply] using hpt w
      _ ≤ ∑ p', eLpNorm (|k p'| • ψ p') q μ :=
          eLpNorm_sum_le (fun p' _ => ((hmeas p').const_smul _).aestronglyMeasurable) hq
      _ = _ := by
          refine Finset.sum_congr rfl fun p' _ => ?_
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (abs_nonneg _)]
  set Yb := parentBlock L p.1.1 with hYb
  set N := weightedCurvatureNorm μ ω' q X with hNdef
  have hterm : ∀ p' : OrientedPlaquette n,
      ENNReal.ofReal (ω p.1) * (ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ) ≤
      ENNReal.ofReal (|k p'| * Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ)))) * N := by
    intro p'
    have hs1 := hs p.1 p'.1
    have hexp := (Real.exp_pos (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ)))).le
    calc ENNReal.ofReal (ω p.1) * (ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ)
        ≤ ENNReal.ofReal (Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ))) * ω' p'.1) *
            (ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ) := by
          gcongr
      _ = ENNReal.ofReal (|k p'| * Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ)))) *
            (ENNReal.ofReal (ω' p'.1) * eLpNorm (ψ p') q μ) := by
          rw [ENNReal.ofReal_mul hexp, ENNReal.ofReal_mul (abs_nonneg _)]
          ring
      _ ≤ _ := by
          gcongr
          exact hN p'
  have hsum0 : ∀ p' ∈ (Finset.univ : Finset (OrientedPlaquette n)),
      0 ≤ |k p'| * Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ))) :=
    fun p' _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  calc ENNReal.ofReal (ω p.1) * eLpNorm (fun e => curlNorm (pushColours a ρA L u (X e)) p.1) q μ
      ≤ ENNReal.ofReal (ω p.1) * ∑ p', ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ := by gcongr
    _ = ∑ p', ENNReal.ofReal (ω p.1) * (ENNReal.ofReal |k p'| * eLpNorm (ψ p') q μ) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ p', ENNReal.ofReal (|k p'| * Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ)))) * N :=
        Finset.sum_le_sum fun p' _ => hterm p'
    _ = ENNReal.ofReal (∑ p', |k p'| * Real.exp (κ * (1 + (TorusFields.supDist Yb p'.1.1 : ℝ)))) * N := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg hsum0]
    _ ≤ _ := by
        gcongr
end ResponseContraction
open ResponseContraction in
theorem responseContraction_holds (h₁ : responseMapClosedFormsStatement)
    (h₂ : PathForms.pathFormAboutSiteStatement) (h₃ : CurlSizeBound)
    (h₄ : flatChainEnergyNearCell) (h₅ : AxialResponseOfMinimizers) :
    responseContractionStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, hcl⟩ := h₁ a ha
  obtain ⟨K, hK, hpath⟩ := h₂
  obtain ⟨C₃, hC₃, L₃, hS⟩ := h₃ a ha
  obtain ⟨del, C₄, hdel, hdel1, hC₄, L₄, hE⟩ := h₄ a ha
  have hlat : 0 < expLatticeSum (del / 2) := expLatticeSum_pos (by positivity)
  have hs4 : 0 < Real.sqrt C₄ := Real.sqrt_pos.mpr hC₄
  set Cw : ℝ := C₃ * Real.sqrt C₄ * K * (64 / del ^ 2 * Real.exp 1) * Real.exp 1 *
    (4 * expLatticeSum (del / 2)) with hCw
  have hCw0 : 0 < Cw := by positivity
  refine ⟨Cw, hCw0, max (max L₁ L₃) (max L₄ ⌈(2 ^ 10 * Cw) ^ 4⌉₊), fun c => min (rt₁ c) (2 ^ 11 * del), C₁,
    fun c => lt_min (hrt₁ c) (by positivity), fun L hodd hL Tb hTa hTL hD hCS hCH hrt hCd => ?_⟩
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL3 : L₃ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL4 : L₄ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLc : ⌈(2 ^ 10 * Cw) ^ 4⌉₊ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  refine ⟨?_, ?_⟩
  · have hfl : (2 ^ 10 * Cw) ^ 4 ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLc)
    have hroot : 2 ^ 10 * Cw ≤ (L : ℝ) ^ (1 / 4 : ℝ) := by
      have hb0 : (0 : ℝ) ≤ 2 ^ 10 * Cw := by positivity
      generalize (2 : ℝ) ^ 10 * Cw = b at hb0 hfl ⊢
      calc b = (b ^ 4) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast b 4, ← Real.rpow_mul hb0]
            norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hfl (by norm_num)
    have e : (L : ℝ) ^ (-(1 / 4) : ℝ) = (L : ℝ) ^ (1 / 4 : ℝ) * (L : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add hLpos]
      norm_num
    have hp : 0 ≤ (L : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    rw [e]
    calc Cw * (L : ℝ) ^ (-(1 / 2) : ℝ) = 2⁻¹ ^ 10 * (2 ^ 10 * Cw) * (L : ℝ) ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ 2⁻¹ ^ 10 * (L : ℝ) ^ (1 / 4 : ℝ) * (L : ℝ) ^ (-(1 / 2) : ℝ) := by gcongr
      _ = _ := by ring
  obtain ⟨y₀, hy⟩ := hcl L hodd hL1 Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _)) hCd
  refine ⟨y₀, fun z hz hrow hw u n _ hn ω ω' hω hω' hslow Ω _ μ X q hq hX => ?_⟩
  have hc3 := (hy z hz hrow hw u n hn).2.2
  obtain ⟨c, nss, hties, -⟩ := hCS
  obtain ⟨-, -, hρ, -, -, -, -, hholds⟩ := hties
  subst hTL
  subst hTa
  have hT : ∀ (F : BlockFrame) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      F.blockSide = (Tb.stepParameters z).side → IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain Tb.coupling b B ∧
        IsAxialResponse b B (minimizerResponse Tb.coupling Tb.ρA b X) := by
    intro F b X hF hcub hX
    have h0 := h₅ Tb.coupling ha Tb.side hodd c hholds F b X hF hcub hX
    rwa [hρ] at h0
  have hF := fun (c' : TorusBond n) (p : OrientedPlaquette (n * (Tb.stepParameters z).side)) =>
    abs_curl_responseKernel_le (L := (Tb.stepParameters z).side) hodd hL3 hL4 hC₃ hC₄ hS hE hT u n hn c' p
  have hrate : (Tb.stepParameters z).weightRate / 8 = Tb.rt / 2 ^ 13 := by
    show Tb.rt / 2 ^ 10 / 8 = _
    ring
  have hrt2 : Tb.rt ≤ 2 ^ 11 * del := hrt.trans (min_le_right _ _)
  have hrt0 : 0 < Tb.rt := hD.rt_pos
  have hκ0 : 0 ≤ (Tb.stepParameters z).weightRate / 8 := by
    rw [hrate]
    positivity
  have hκ : (Tb.stepParameters z).weightRate / 8 ≤ del / 4 := by
    rw [hrate]
    linarith
  have hLp : 0 ≤ ((Tb.stepParameters z).side : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hker := exists_curlKernel (a := Tb.coupling) (ρA := Tb.ρA) (del := del)
    (Aa := C₃ * Real.sqrt C₄ * ((Tb.stepParameters z).side : ℝ) ^ (-(1 / 2 : ℝ))) (K := K)
    (κ := (Tb.stepParameters z).weightRate / 8) (L := (Tb.stepParameters z).side) (u := u) (n := n)
    hdel hdel1 (by positivity) hK hκ0 hκ hc3 hF (hpath n (by omega))
  refine weightedCurvatureNorm_pushColours_le (κ := (Tb.stepParameters z).weightRate / 8) (fun p => ?_)
    ω ω' hω hω' hslow Ω μ X q hq hX
  obtain ⟨k, k1, k2⟩ := hker p
  refine ⟨k, k1, k2.trans (le_of_eq ?_)⟩
  show _ = Cw * ((Tb.stepParameters z).side : ℝ) ^ (-(1 / 2) : ℝ)
  rw [hCw]
  ring
end MomentLaw
end YangMills.Construction
end
