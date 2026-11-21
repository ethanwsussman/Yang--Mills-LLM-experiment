import YangMills.Construction.LawByMomentsOfTheFlow.ChainIsBuiltDownwardProof
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import YangMills.Construction.LawByMomentsOfTheFlow.ChainObeysTheFirstLevelProof
import YangMills.Construction.LawByMomentsOfTheFlow.FluctuationsOfTheGaussianChain
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfTheLevelsAtASmallRate
import YangMills.Construction.SummableBoundsOfTheFlow.InverseOfAMixture
import YangMills.Construction.SummableBoundsOfTheFlow.PolarOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace GaussianFluctuations
open TorusFields WeightedResponses
section Forms
variable {V : Type} [AddCommGroup V] [Module ℝ V]
private theorem bilin_sq_le (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (x y : V) :
    (B x y) ^ 2 ≤ B x x * B y y :=
  LinearMap.BilinForm.apply_sq_le_of_symm (B := B) hp ⟨fun x y => hs x y⟩ x y
private theorem gaussianVariance_bilin (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (w : V) :
    gaussianVariance (fun x => B x x) (B w) = B w w := by
  unfold gaussianVariance
  rcases (hp w).eq_or_lt with h0 | hpos
  · have hsub : {t | ∃ x, 0 < B x x ∧ t = (B w x) ^ 2 / B x x} ⊆ {0} := by
      rintro t ⟨x, hx, rfl⟩
      have h1 := bilin_sq_le B hs hp w x
      rw [← h0, zero_mul] at h1
      have h2 : (B w x) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      simp [h2]
    rcases Set.subset_singleton_iff_eq.1 hsub with h | h
    · rw [h, Real.sSup_empty]
      exact h0
    · rw [h, csSup_singleton]
      exact h0
  · apply IsGreatest.csSup_eq
    refine ⟨⟨w, hpos, ?_⟩, ?_⟩
    · field_simp
    · rintro t ⟨x, hx, rfl⟩
      rw [div_le_iff₀ hx]
      exact bilin_sq_le B hs hp w x
private theorem map_gaussian_of_ae_bilin [MeasurableSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, 0 ≤ B x x) {μ : Measure V} (h : IsCanonicalGaussian (fun x => B x x) μ) (w : V) {F : V → ℝ}
    (hF : F =ᵐ[μ] B w) :
    μ.map F = gaussianReal 0 (B w w).toNNReal := by
  rw [Measure.map_congr hF, ← gaussianVariance_bilin B hs hp w]
  refine h.map_eq (B w) fun x hx => ?_
  have h1 := bilin_sq_le B hs hp w x
  have hx' : B x x = 0 := hx
  rw [hx', mul_zero] at h1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))
private theorem exists_rep_on_submodule (T : Submodule ℝ V) [FiniteDimensional ℝ T] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ T, B x x = 0 → f x = 0) :
    ∃ w ∈ T, ∀ x ∈ T, f x = B w x := by apply _root_.YangMills.SharedProofs.p88707 <;> assumption
end Forms
section Independence
variable {Ω E F : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]
private theorem charFun_gaussianReal_at_one (v : ℝ) (hv : 0 ≤ v) :
    charFun (gaussianReal 0 v.toNNReal) 1 = Complex.exp (-((v : ℂ) / 2)) := by
  rw [charFun_gaussianReal, Real.coe_toNNReal v hv]
  congr 1
  simp
private theorem indepFun_of_joint_gaussian {X : Ω → E} {Y : Ω → F} (hX : Measurable X) (hY : Measurable Y)
    (v : StrongDual ℝ E → ℝ) (w : StrongDual ℝ F → ℝ) (hv : ∀ l, 0 ≤ v l) (hw : ∀ m, 0 ≤ w m)
    (h₁ : ∀ l : StrongDual ℝ E, μ.map (fun ω => l (X ω)) = gaussianReal 0 (v l).toNNReal)
    (h₂ : ∀ m : StrongDual ℝ F, μ.map (fun ω => m (Y ω)) = gaussianReal 0 (w m).toNNReal)
    (h : ∀ (l : StrongDual ℝ E) (m : StrongDual ℝ F),
      μ.map (fun ω => l (X ω) + m (Y ω)) = gaussianReal 0 (v l + w m).toNNReal) :
    IndepFun X Y μ := by
  rw [indepFun_iff_charFunDual_prod hX.aemeasurable hY.aemeasurable]
  intro L
  set l := L.comp (ContinuousLinearMap.inl ℝ E F) with hl
  set m := L.comp (ContinuousLinearMap.inr ℝ E F) with hm
  have e1 : charFunDual (μ.map X) l = Complex.exp (-((v l : ℂ) / 2)) := by
    rw [charFunDual_eq_charFun_map_one, Measure.map_map l.continuous.measurable hX]
    have : (⇑l ∘ X) = fun ω => l (X ω) := rfl
    rw [this, h₁, charFun_gaussianReal_at_one _ (hv l)]
  have e2 : charFunDual (μ.map Y) m = Complex.exp (-((w m : ℂ) / 2)) := by
    rw [charFunDual_eq_charFun_map_one, Measure.map_map m.continuous.measurable hY]
    have : (⇑m ∘ Y) = fun ω => m (Y ω) := rfl
    rw [this, h₂, charFun_gaussianReal_at_one _ (hw m)]
  have e3 : charFunDual (μ.map fun ω => (X ω, Y ω)) L = Complex.exp (-(((v l + w m : ℝ) : ℂ) / 2)) := by
    rw [charFunDual_eq_charFun_map_one, Measure.map_map L.continuous.measurable (hX.prodMk hY)]
    have : (⇑L ∘ fun ω => (X ω, Y ω)) = fun ω => l (X ω) + m (Y ω) := by
      funext ω
      simp only [Function.comp, hl, hm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply]
      rw [← map_add]
      simp
    rw [this, h, charFun_gaussianReal_at_one _ (add_nonneg (hv l) (hw m))]
  rw [e1, e2, e3, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end Independence
section Chains
variable {L : ℕ} [NeZero L]
@[reducible] private def levelBondFintype (L : ℕ) [NeZero L] : (s n : ℕ) → [NeZero n] → Fintype (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Fintype (TorusBond n))
  | s + 1, n, _ => by
    letI := levelBondFintype L s (n * L)
    exact inferInstanceAs (Fintype (LevelBond L s (n * L) ⊕ TorusBond n))
private instance (s n : ℕ) [NeZero n] : Fintype (LevelBond L s n) := levelBondFintype L s n
private theorem sumAlongWord_add {m : ℕ} (A B : TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
variable {n : ℕ}
private theorem contourAverage_add [NeZero n] (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A + B) c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c + _root_.YangMills.Construction.MomentLaw.contourAverage L B c := by
  simp only [_root_.YangMills.Construction.MomentLaw.contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul [NeZero n] (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (r • A) c = r * _root_.YangMills.Construction.MomentLaw.contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n), chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainLower_add {s : ℕ} (X Y : LevelChain L (s + 1) n) :
    chainLower (X + Y) = chainLower X + chainLower Y := rfl
private theorem chainLower_smul {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) :
    chainLower (r • X) = r • chainLower X := rfl
private theorem chainDefect_add [NeZero n] {s : ℕ} (X Y : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (X + Y) e c = chainDefect X e c + chainDefect Y e c := by apply _root_.YangMills.SharedProofs.p32985 <;> assumption
private theorem chainDefect_smul [NeZero n] {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (r • X) e c = r * chainDefect X e c := by apply _root_.YangMills.SharedProofs.p30900 <;> assumption
private def energyPairing (a : ℝ) : (s n : ℕ) → [NeZero n] → LevelChain L s n → LevelChain L s n → ℝ
  | 0, n, _, X, Y => ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ e : Fin 3,
      curl (chainTop 0 n X e) p * curl (chainTop 0 n Y e) p
  | s + 1, n, _, X, Y => energyPairing a s (n * L) (chainLower X) (chainLower Y) +
      a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c
private theorem curl_add' {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) : curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem curl_smul' {m : ℕ} (r : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) : curl (r • A) p = r * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private theorem energyPairing_comm (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n),
    energyPairing a s n X Y = energyPairing a s n Y X
  | 0, n, _, X, Y => by
    simp only [energyPairing]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => mul_comm _ _
  | s + 1, n, _, X, Y => by
    simp only [energyPairing]
    rw [energyPairing_comm a s (n * L)]
    congr 2
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_comm _ _
private theorem energyPairing_add_left (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X X' Y : LevelChain L s n),
    energyPairing a s n (X + X') Y = energyPairing a s n X Y + energyPairing a s n X' Y
  | 0, n, _, X, X', Y => by
    simp only [energyPairing, chainTop_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show chainTop 0 n X e + chainTop 0 n X' e = (chainTop 0 n X + chainTop 0 n X') e from rfl,
      Pi.add_apply, curl_add']
    ring
  | s + 1, n, _, X, X', Y => by
    simp only [energyPairing, chainLower_add]
    rw [energyPairing_add_left a s (n * L)]
    have : ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (X + X') e c * chainDefect Y e c =
        ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c +
          ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X' e c * chainDefect Y e c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [chainDefect_add]
      ring
    rw [this]
    ring
private theorem energyPairing_smul_left (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X Y : LevelChain L s n),
    energyPairing a s n (r • X) Y = r * energyPairing a s n X Y
  | 0, n, _, r, X, Y => by
    simp only [energyPairing, chainTop_smul, Pi.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show r • chainTop 0 n X e = (r • chainTop 0 n X) e from rfl, Pi.smul_apply, curl_smul']
    ring
  | s + 1, n, _, r, X, Y => by
    simp only [energyPairing, chainLower_smul]
    rw [energyPairing_smul_left a s (n * L)]
    have : ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (r • X) e c * chainDefect Y e c =
        r * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [chainDefect_smul]
      ring
    rw [this]
    ring
private def energyForm (a : ℝ) (s n : ℕ) [NeZero n] : LevelChain L s n →ₗ[ℝ] LevelChain L s n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (energyPairing a s n) (energyPairing_add_left a s n) (energyPairing_smul_left a s n)
    (fun X Y Y' => by
      rw [energyPairing_comm a s n X, energyPairing_add_left, energyPairing_comm a s n Y, energyPairing_comm a s n Y'])
    (fun r X Y => by
      rw [energyPairing_comm a s n X, energyPairing_smul_left, energyPairing_comm a s n Y]
      rfl)
private theorem energyForm_apply (a : ℝ) (s n : ℕ) [NeZero n] (X Y : LevelChain L s n) :
    energyForm a s n X Y = energyPairing a s n X Y := rfl
private theorem energyForm_comm (a : ℝ) (s n : ℕ) [NeZero n] (X Y : LevelChain L s n) :
    energyForm a s n X Y = energyForm a s n Y X := energyPairing_comm a s n X Y
private theorem energyForm_self (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    energyForm a s n X X = levelEnergy a s n X
  | 0, n, _, X => by
    simp only [energyForm_apply, energyPairing, levelEnergy]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun e _ => (sq _).symm
  | s + 1, n, _, X => by
    have ih := energyForm_self a s (n * L) (chainLower X)
    rw [energyForm_apply] at ih ⊢
    simp only [energyPairing, levelEnergy]
    rw [ih]
    congr 2
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => (sq _).symm
private theorem levelEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    0 ≤ levelEnergy a s n X
  | 0, n, _, X => by
    simp only [levelEnergy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  | s + 1, n, _, X => by
    simp only [levelEnergy]
    exact add_nonneg (levelEnergy_nonneg ha s (n * L) _)
      (mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
end Chains
section Steps
variable {L : ℕ} [NeZero L] {n : ℕ}
private theorem responseMap_add (a ρA : ℝ) (u : ℕ) [NeZero n] (A B : TorusBond n → ℝ) :
    responseMap a ρA L u (A + B) = responseMap a ρA L u A + responseMap a ρA L u B := by
  funext b
  simp only [responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem responseMap_smul (a ρA : ℝ) (u : ℕ) [NeZero n] (r : ℝ) (A : TorusBond n → ℝ) :
    responseMap a ρA L u (r • A) = r • responseMap a ρA L u A := by apply _root_.YangMills.SharedProofs.p84206 <;> assumption
private theorem responseMap_zero (a ρA : ℝ) (u : ℕ) [NeZero n] : responseMap a ρA L u (0 : TorusBond n → ℝ) = 0 := by
  funext b
  simp [responseMap]
private theorem pushColours_add (a ρA : ℝ) (u : ℕ) [NeZero n] (X Y : ColourForm n) :
    pushColours a ρA L u (X + Y) = pushColours a ρA L u X + pushColours a ρA L u Y :=
  funext fun e => responseMap_add a ρA u (X e) (Y e)
private theorem pushColours_smul (a ρA : ℝ) (u : ℕ) [NeZero n] (r : ℝ) (X : ColourForm n) :
    pushColours a ρA L u (r • X) = r • pushColours a ρA L u X :=
  funext fun e => responseMap_smul a ρA u r (X e)
private theorem pushColours_zero (a ρA : ℝ) (u : ℕ) [NeZero n] : pushColours a ρA L u (0 : ColourForm n) = 0 :=
  funext fun _ => responseMap_zero a ρA u
private theorem stepDefect_add (a ρA : ℝ) (u m : ℕ) [NeZero m] (Z Z' : LevelChain L (u + 1) m) :
    stepDefect a ρA u m (Z + Z') = stepDefect a ρA u m Z + stepDefect a ρA u m Z' := by
  funext e b
  simp only [stepDefect, chainTop_add, chainLower_add, pushColours_add, Pi.add_apply]
  ring
private theorem stepDefect_smul (a ρA : ℝ) (u m : ℕ) [NeZero m] (r : ℝ) (Z : LevelChain L (u + 1) m) :
    stepDefect a ρA u m (r • Z) = r • stepDefect a ρA u m Z := by
  funext e b
  simp only [stepDefect, chainTop_smul, chainLower_smul, pushColours_smul, Pi.smul_apply, smul_eq_mul]
  ring
private theorem chartValues_add {u : ℕ} [NeZero n] (X Y : ColourForm (n * L)) (e : Fin 3) (b : ChartBondIndex L u n) :
    chartValues (u := u) (X + Y) e b = chartValues (u := u) X e b + chartValues (u := u) Y e b := by
  classical
  simp only [chartValues]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem chartValues_smul {u : ℕ} [NeZero n] (r : ℝ) (X : ColourForm (n * L)) (e : Fin 3) (b : ChartBondIndex L u n) :
    chartValues (u := u) (r • X) e b = r * chartValues (u := u) X e b := by
  classical
  simp only [chartValues]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private def fluct (a ρA : ℝ) (u m : ℕ) [NeZero m] (Z : LevelChain L (u + 1) m) (e : Fin 3) : ChartBondIndex L u m → ℝ :=
  fun b => chartValues (u := u) (stepDefect a ρA u m Z) e b
private theorem fluct_add (a ρA : ℝ) (u m : ℕ) [NeZero m] (Z Z' : LevelChain L (u + 1) m) (e : Fin 3) :
    fluct a ρA u m (Z + Z') e = fluct a ρA u m Z e + fluct a ρA u m Z' e := by
  funext b
  simp only [fluct, stepDefect_add, chartValues_add, Pi.add_apply]
private theorem fluct_smul (a ρA : ℝ) (u m : ℕ) [NeZero m] (r : ℝ) (Z : LevelChain L (u + 1) m) (e : Fin 3) :
    fluct a ρA u m (r • Z) e = r • fluct a ρA u m Z e := by
  funext b
  simp only [fluct, stepDefect_smul, chartValues_smul, Pi.smul_apply, smul_eq_mul]
private theorem fluct_sub (a ρA : ℝ) (u m : ℕ) [NeZero m] (Z Z' : LevelChain L (u + 1) m) (e : Fin 3) :
    fluct a ρA u m (Z - Z') e = fluct a ρA u m Z e - fluct a ρA u m Z' e := by
  rw [sub_eq_add_neg, fluct_add, ← neg_one_smul ℝ Z', fluct_smul, neg_one_smul, ← sub_eq_add_neg]
private def hessianRest (a ρA : ℝ) : (s n : ℕ) → [NeZero n] → LevelChain L s n → LevelChain L s n → ℝ
  | 0, _, _, _, _ => 0
  | s + 1, n, _, X, Y => hessianRest a ρA s (n * L) (chainLower X) (chainLower Y) +
      ∑ e : Fin 3, fluct a ρA s n X e ⬝ᵥ (trivialHessian a L s n).mulVec (fluct a ρA s n Y e)
private theorem isTreeGauge_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n Y → IsTreeGauge s n (X + Y)
  | 0, _, _, _, _, _, _ => trivial
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨fun e b hb => by
      rw [chainLower_add, chainTop_add, Pi.add_apply, Pi.add_apply, h1 e b hb, h3 e b hb, add_zero],
    isTreeGauge_add s (n * L) _ _ h2 h4⟩
private theorem isTreeGauge_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n (r • X)
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨fun e b hb => by
      rw [chainLower_smul, chainTop_smul, Pi.smul_apply, Pi.smul_apply, h1 e b hb, smul_zero],
    isTreeGauge_smul s (n * L) r _ h2⟩
private theorem isTreeGauge_zero : ∀ (s n : ℕ) [NeZero n], IsTreeGauge s n (0 : LevelChain L s n)
  | 0, _, _ => trivial
  | s + 1, n, _ => ⟨fun e b _ => by
      have h := chainTop_smul s (n * L) 0 (chainLower (0 : LevelChain L (s + 1) n))
      rw [zero_smul] at h
      have h' : chainLower (0 : LevelChain L (s + 1) n) = 0 := rfl
      rw [h', h]
      simp, isTreeGauge_zero s (n * L)⟩
private def treeGaugeSubmodule (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsTreeGauge s n X}
  add_mem' := fun {X Y} hX hY => isTreeGauge_add s n X Y hX hY
  zero_mem' := isTreeGauge_zero s n
  smul_mem' := fun r X hX => isTreeGauge_smul s n r X hX
private def consTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) : LevelChain L (s + 1) n := fun e =>
  (Sum.elim (B e) (A e) : LevelBond L s (n * L) ⊕ TorusBond n → ℝ)
private def pushDown (a ρA : ℝ) : (s n : ℕ) → [NeZero n] → ColourForm n → LevelChain L s n
  | 0, _, _, A => A
  | s + 1, n, _, A => consTop (pushDown a ρA s (n * L) (pushColours a ρA L s A)) A
private theorem chainTop_pushDown (a ρA : ℝ) : ∀ (s n : ℕ) [NeZero n] (A : ColourForm n),
    chainTop s n (pushDown (L := L) a ρA s n A) = A
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private def padAbove (s : ℕ) : (d n : ℕ) → LevelChain L s (fineSide L d n) → LevelChain L (s + d) n
  | 0, _, W => W
  | d + 1, n, W => consTop (padAbove s d (n * L) W) 0
private theorem chainDescend_padAbove (s : ℕ) : ∀ (d n : ℕ) (W : LevelChain L s (fineSide L d n)),
    chainDescend s d n (padAbove s d n W) = W
  | 0, _, _ => rfl
  | d + 1, n, W => chainDescend_padAbove s d (n * L) W
private theorem chainTop_padAbove (s : ℕ) : ∀ (d n : ℕ) (W : LevelChain L s (fineSide L d n)),
    chainTop s (fineSide L d n) W = 0 → chainTop (s + d) n (padAbove s d n W) = 0
  | 0, _, _, h => h
  | _ + 1, _, _, _ => rfl
private theorem isTreeGauge_padAbove (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (W : LevelChain L s (fineSide L d n)),
    chainTop s (fineSide L d n) W = 0 → IsTreeGauge s (fineSide L d n) W → IsTreeGauge (s + d) n (padAbove s d n W)
  | 0, _, _, _, _, h => h
  | d + 1, n, _, W, h0, h => ⟨fun e b _ => by
      show chainTop (s + d) (n * L) (padAbove s d (n * L) W) e b = 0
      rw [chainTop_padAbove s d (n * L) W h0]
      rfl, isTreeGauge_padAbove s d (n * L) W h0 h⟩
private theorem isTreeGauge_chainDescend (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (X : LevelChain L (s + d) n),
    IsTreeGauge (s + d) n X → IsTreeGauge s (fineSide L d n) (chainDescend s d n X)
  | 0, _, _, _, h => h
  | d + 1, n, _, _, ⟨_, h⟩ => isTreeGauge_chainDescend s d (n * L) _ h
private theorem chainDescend_add (s : ℕ) : ∀ (d n : ℕ) (X Y : LevelChain L (s + d) n),
    chainDescend s d n (X + Y) = chainDescend s d n X + chainDescend s d n Y
  | 0, _, _, _ => rfl
  | d + 1, n, X, Y => chainDescend_add s d (n * L) (chainLower X) (chainLower Y)
private theorem chainDescend_smul (s : ℕ) : ∀ (d n : ℕ) (r : ℝ) (X : LevelChain L (s + d) n),
    chainDescend s d n (r • X) = r • chainDescend s d n X
  | 0, _, _, _ => rfl
  | d + 1, n, r, X => chainDescend_smul s d (n * L) r (chainLower X)
end Steps
private structure ChainHypotheses (a ρA κ : ℝ) (L N : ℕ) [NeZero L] : Prop where
  a_pos : 0 < a
  κ_pos : 0 < κ
  one_le : 1 ≤ L
  square : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (Y : TorusBond n → ℝ) (η : ChartBondIndex L u n → ℝ),
    maxwellForm a L u (fun b => responseMap a ρA L u Y b + extendChart η b)
        (fun b => responseMap a ρA L u Y b + extendChart η b) +
      a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (fun b => responseMap a ρA L u Y b + extendChart η b) c - Y c) ^ 2 =
    maxwellForm a L (u + 1) Y Y + η ⬝ᵥ ((trivialHessian a L u n).mulVec η)
  trees : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (Y : TorusBond n → ℝ), ∀ b ∉ StepCosts.chartBonds L n,
    responseMap a ρA L u Y b = 0
  lift_read : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (X : ColourForm (n * L)) (e : Fin 3),
    (∀ b ∉ StepCosts.chartBonds L n, X e b = 0) →
    extendChart (u := u) (fun b => chartValues (u := u) X e b) = X e
  read_lift : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (X : ColourForm (n * L)) (e : Fin 3) (η : ChartBondIndex L u n → ℝ),
    X e = extendChart η → ∀ b, chartValues (u := u) X e b = η b
  lift_off : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (η : ChartBondIndex L u n → ℝ), ∀ b ∉ StepCosts.chartBonds L n,
    extendChart η b = 0
  bare : ∀ (m : ℕ) [NeZero m] (A A' : TorusBond m → ℝ), maxwellForm a L 0 A A' =
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p * curl A' p
  posDef : ∀ (u n : ℕ) [NeZero n], N ≤ n → (trivialHessian a L u n).PosDef
  curl_le : ∀ (u m : ℕ) [NeZero m], N ≤ m → ∀ A : TorusBond m → ℝ,
    κ * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 ≤ maxwellForm a L u A A
section Energy
variable {a ρA κ : ℝ} {L N : ℕ} [NeZero L]
private theorem kineticForm_eq_sum {n : ℕ} [NeZero n] (u : ℕ) (X : ColourForm n) :
    kineticForm a L u X = ∑ e : Fin 3, maxwellForm a L u (X e) (X e) := rfl
private theorem le_side_mul (P : ChainHypotheses a ρA κ L N) {n : ℕ} (hn : N ≤ n) : N ≤ n * L :=
  hn.trans (Nat.le_mul_of_pos_right n P.one_le)
private theorem le_fineSide (P : ChainHypotheses a ρA κ L N) : ∀ (d : ℕ) {n : ℕ}, N ≤ n → N ≤ fineSide L d n
  | 0, _, hn => hn
  | d + 1, _, hn => le_fineSide P d (le_side_mul P hn)
private theorem chainTop_lower_eq (P : ChainHypotheses a ρA κ L N) {s n : ℕ} [NeZero n] (hn : N ≤ n)
    (Z : LevelChain L (s + 1) n)
    (hZ : ∀ e, ∀ b ∉ StepCosts.chartBonds L n, chainTop s (n * L) (chainLower Z) e b = 0) (e : Fin 3) :
    (fun b => responseMap a ρA L s (chainTop (s + 1) n Z e) b + extendChart (fluct a ρA s n Z e) b) =
      chainTop s (n * L) (chainLower Z) e := by
  have h := P.lift_read s n hn (stepDefect a ρA s n Z) e fun b hb => by
    show chainTop s (n * L) (chainLower Z) e b - responseMap a ρA L s (chainTop (s + 1) n Z e) b = 0
    rw [hZ e b hb, P.trees s n hn _ b hb, sub_zero]
  funext b
  have hb := congrFun h b
  have e1 : extendChart (fluct a ρA s n Z e) b = stepDefect a ρA s n Z e b := hb
  rw [e1]
  show _ + (chainTop s (n * L) (chainLower Z) e b - responseMap a ρA L s (chainTop (s + 1) n Z e) b) = _
  ring
private theorem levelEnergy_eq (P : ChainHypotheses a ρA κ L N) : ∀ (s n : ℕ) [NeZero n], N ≤ n →
    ∀ X : LevelChain L s n, IsTreeGauge s n X →
    levelEnergy a s n X = kineticForm a L s (chainTop s n X) + hessianRest a ρA s n X X
  | 0, n, _, _, X, _ => by
    rw [kineticForm_eq_sum]
    simp only [levelEnergy, hessianRest, add_zero, P.bare]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun e _ => sq _
  | s + 1, n, _, hn, X, ⟨h1, h2⟩ => by
    have ih := levelEnergy_eq P s (n * L) (le_side_mul P hn) (chainLower X) h2
    have hsq : ∀ e : Fin 3, maxwellForm a L s (chainTop s (n * L) (chainLower X) e)
          (chainTop s (n * L) (chainLower X) e) +
        a * ∑ c : TorusBond n, chainDefect X e c ^ 2 =
        maxwellForm a L (s + 1) (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) +
          fluct a ρA s n X e ⬝ᵥ ((trivialHessian a L s n).mulVec (fluct a ρA s n X e)) := by
      intro e
      have h := P.square s n hn (chainTop (s + 1) n X e) (fluct a ρA s n X e)
      rw [chainTop_lower_eq P hn X h1 e] at h
      rw [← h]
      congr 2
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [chainDefect]
      ring
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 3)) = Finset.univ) fun e _ => hsq e
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at hs
    simp only [levelEnergy, hessianRest]
    rw [ih]
    rw [kineticForm_eq_sum, kineticForm_eq_sum]
    linarith
private theorem dotProduct_mulVec_comm_of_posDef {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (hH : H.PosDef) (v w : ι → ℝ) : v ⬝ᵥ H.mulVec w = w ⬝ᵥ H.mulVec v := by apply _root_.YangMills.SharedProofs.p101518 <;> assumption
private theorem hessianRest_polar (P : ChainHypotheses a ρA κ L N) : ∀ (s n : ℕ) [NeZero n], N ≤ n →
    ∀ X Y : LevelChain L s n,
    hessianRest a ρA s n (X + Y) (X + Y) - hessianRest a ρA s n (X - Y) (X - Y) = 4 * hessianRest a ρA s n X Y
  | 0, _, _, _, _, _ => by simp [hessianRest]
  | s + 1, n, _, hn, X, Y => by
    classical
    have ih := hessianRest_polar P s (n * L) (le_side_mul P hn) (chainLower X) (chainLower Y)
    have hb : chainLower (X - Y) = chainLower X - chainLower Y := rfl
    simp only [hessianRest, chainLower_add, hb]
    have hterm : ∀ e : Fin 3,
        fluct a ρA s n (X + Y) e ⬝ᵥ (trivialHessian a L s n).mulVec (fluct a ρA s n (X + Y) e) -
        fluct a ρA s n (X - Y) e ⬝ᵥ (trivialHessian a L s n).mulVec (fluct a ρA s n (X - Y) e) =
        4 * (fluct a ρA s n X e ⬝ᵥ (trivialHessian a L s n).mulVec (fluct a ρA s n Y e)) := by
      intro e
      rw [fluct_add, fluct_sub]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
      rw [dotProduct_mulVec_comm_of_posDef (P.posDef s n hn) (fluct a ρA s n Y e) (fluct a ρA s n X e)]
      ring
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 3)) = Finset.univ) fun e _ => hterm e
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
    linarith
private theorem chainTop_sub {s n : ℕ} (X Y : LevelChain L s n) :
    chainTop s n (X - Y) = chainTop s n X - chainTop s n Y := by
  rw [sub_eq_add_neg, chainTop_add, ← neg_one_smul ℝ Y, chainTop_smul, neg_one_smul, ← sub_eq_add_neg]
private theorem isTreeGauge_sub {s n : ℕ} [NeZero n] {X Y : LevelChain L s n} (hX : IsTreeGauge s n X)
    (hY : IsTreeGauge s n Y) : IsTreeGauge s n (X - Y) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y]
  exact isTreeGauge_add s n _ _ hX (isTreeGauge_smul s n _ _ hY)
private theorem maxwellForm_neg_neg {m : ℕ} [NeZero m] (u : ℕ) (A : TorusBond m → ℝ) :
    maxwellForm a L u (-A) (-A) = maxwellForm a L u A A := by
  simp only [maxwellForm, Pi.neg_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem energyForm_eq_hessianRest (P : ChainHypotheses a ρA κ L N) {s n : ℕ} [NeZero n] (hn : N ≤ n)
    {w x : LevelChain L s n} (hw : IsTreeGauge s n w) (hx : IsTreeGauge s n x) (h0 : chainTop s n w = 0) :
    energyForm a s n w x = hessianRest a ρA s n w x := by
  have e1 := levelEnergy_eq P s n hn (w + x) (isTreeGauge_add s n _ _ hw hx)
  have e2 := levelEnergy_eq P s n hn (w - x) (isTreeGauge_sub hw hx)
  have e3 := hessianRest_polar P s n hn w x
  rw [chainTop_add, h0, zero_add] at e1
  rw [chainTop_sub, h0, zero_sub] at e2
  have e4 : kineticForm a L s (-chainTop s n x) = kineticForm a L s (chainTop s n x) := by
    rw [kineticForm_eq_sum, kineticForm_eq_sum]
    exact Finset.sum_congr rfl fun e _ => maxwellForm_neg_neg s _
  rw [e4] at e2
  rw [← energyForm_self] at e1 e2
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at e1 e2
  rw [energyForm_comm a s n x w] at e1 e2
  linarith
private theorem hessianRest_nonneg (P : ChainHypotheses a ρA κ L N) : ∀ (s n : ℕ) [NeZero n], N ≤ n →
    ∀ X : LevelChain L s n, 0 ≤ hessianRest a ρA s n X X
  | 0, _, _, _, _ => le_rfl
  | s + 1, n, _, hn, X => by
    classical
    simp only [hessianRest]
    refine add_nonneg (hessianRest_nonneg P s (n * L) (le_side_mul P hn) _) (Finset.sum_nonneg fun e _ => ?_)
    have h := (P.posDef s n hn).posSemidef.dotProduct_mulVec_nonneg (fluct a ρA s n X e)
    simpa using h
private theorem levelEnergy_chainDescend_le (P : ChainHypotheses a ρA κ L N) (s : ℕ) : ∀ (d n : ℕ) [NeZero n]
    (X : LevelChain L (s + d) n),
    levelEnergy a s (fineSide L d n) (chainDescend s d n X) ≤ levelEnergy a (s + d) n X
  | 0, _, _, _ => le_rfl
  | d + 1, n, _, X => by
    have h := levelEnergy_chainDescend_le P s d (n * L) (chainLower X)
    show levelEnergy a s (fineSide L d (n * L)) (chainDescend s d (n * L) (chainLower X)) ≤
      levelEnergy a (s + d) (n * L) (chainLower X) + a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2
    have : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
      mul_nonneg P.a_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
private theorem curl_eq_zero_of_plaquettesIn {m : ℕ} [NeZero m] (A : TorusBond m → ℝ)
    (h : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p = 0) (p : TorusPlaquette m) :
    curl A p = 0 := by apply _root_.YangMills.SharedProofs.p30341 <;> assumption
private theorem curl_eq_zero_of_energy_eq_zero (P : ChainHypotheses a ρA κ L N) {s d n : ℕ} [NeZero n] (hn : N ≤ n)
    {X : LevelChain L (s + d) n} (hX : IsTreeGauge (s + d) n X) (h0 : levelEnergy a (s + d) n X = 0) (e : Fin 3)
    (p : TorusPlaquette (fineSide L d n)) :
    curl (chainTop s _ (chainDescend s d n X) e) p = 0 := by
  have hb := le_fineSide P d hn
  have h1 := levelEnergy_chainDescend_le P s d n X
  have h2 := levelEnergy_eq P s _ hb _ (isTreeGauge_chainDescend s d n X hX)
  have h3 := hessianRest_nonneg P s _ hb (chainDescend s d n X)
  rw [h0] at h1
  rw [kineticForm_eq_sum] at h2
  have h4 : ∑ e : Fin 3, κ * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      curl (chainTop s _ (chainDescend s d n X) e) p ^ 2 ≤ 0 := by
    refine (Finset.sum_le_sum fun e _ => P.curl_le s _ hb _).trans ?_
    linarith
  have h5 : ∀ e ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ κ * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      curl (chainTop s _ (chainDescend s d n X) e) p ^ 2 := fun e _ =>
    mul_nonneg P.κ_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg h5).1 (le_antisymm h4 (Finset.sum_nonneg h5)) e (Finset.mem_univ _)
  have h7 := (mul_eq_zero.1 h6).resolve_left P.κ_pos.ne'
  have h8 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h7
  exact curl_eq_zero_of_plaquettesIn _ (fun p hp => pow_eq_zero_iff two_ne_zero |>.1 (h8 p hp)) p
end Energy
section Vector
variable {a ρA κ : ℝ} {L N : ℕ} [NeZero L]
private theorem fluct_eq_zero_of_stepDefect {u m : ℕ} [NeZero m] {Z : LevelChain L (u + 1) m}
    (h : stepDefect a ρA u m Z = 0) (e : Fin 3) : fluct a ρA u m Z e = 0 := by
  funext b
  simp [fluct, h, chartValues]
private theorem hessianRest_pushDown : ∀ (s n : ℕ) [NeZero n] (A : ColourForm n) (X : LevelChain L s n),
    hessianRest a ρA s n (pushDown a ρA s n A) X = 0
  | 0, _, _, _, _ => rfl
  | s + 1, n, _, A, X => by
    have h0 : stepDefect a ρA s n (pushDown (L := L) a ρA (s + 1) n A) = 0 := by
      funext e b
      show chainTop s (n * L) (pushDown a ρA s (n * L) (pushColours a ρA L s A)) e b -
        pushColours a ρA L s A e b = 0
      rw [chainTop_pushDown, sub_self]
    simp only [hessianRest]
    rw [show chainLower (pushDown (L := L) a ρA (s + 1) n A) =
      pushDown a ρA s (n * L) (pushColours a ρA L s A) from rfl, hessianRest_pushDown s (n * L), zero_add]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [fluct_eq_zero_of_stepDefect h0, zero_dotProduct]
private theorem isTreeGauge_pushDown (P : ChainHypotheses a ρA κ L N) : ∀ (s n : ℕ) [NeZero n], N ≤ n →
    ∀ A : ColourForm n, IsTreeGauge s n (pushDown (L := L) a ρA s n A)
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, hn, A => ⟨fun e b hb => by
      show chainTop s (n * L) (pushDown a ρA s (n * L) (pushColours a ρA L s A)) e b = 0
      rw [chainTop_pushDown]
      exact P.trees s n hn (A e) b hb, isTreeGauge_pushDown P s (n * L) (le_side_mul P hn) _⟩
private theorem hessianRest_padAbove (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (W : LevelChain L s (fineSide L d n))
    (X : LevelChain L (s + d) n), chainTop s (fineSide L d n) W = 0 →
    hessianRest a ρA (s + d) n (padAbove s d n W) X = hessianRest a ρA s (fineSide L d n) W (chainDescend s d n X)
  | 0, _, _, _, _, _ => rfl
  | d + 1, n, _, W, X, h0 => by
    have hs : stepDefect a ρA (s + d) n (consTop (padAbove s d (n * L) W) (0 : ColourForm n)) = 0 := by
      funext e b
      show chainTop (s + d) (n * L) (padAbove s d (n * L) W) e b - pushColours a ρA L (s + d) (0 : ColourForm n) e b = 0
      rw [chainTop_padAbove s d (n * L) W h0, pushColours_zero]
      simp
    show hessianRest a ρA (s + d) (n * L) (padAbove s d (n * L) W) (chainLower X) +
      ∑ e : Fin 3, fluct a ρA (s + d) n (consTop (padAbove s d (n * L) W) (0 : ColourForm n)) e ⬝ᵥ _ =
      hessianRest a ρA s (fineSide L d (n * L)) W (chainDescend s d (n * L) (chainLower X))
    rw [hessianRest_padAbove s d (n * L) W _ h0,
      Finset.sum_eq_zero fun e _ => by rw [fluct_eq_zero_of_stepDefect hs, zero_dotProduct], add_zero]
private def pulse (a ρA : ℝ) (u m : ℕ) [NeZero m] (η : Fin 3 → ChartBondIndex L u m → ℝ) : LevelChain L (u + 1) m :=
  consTop (pushDown a ρA u (m * L) fun e => extendChart (η e)) 0
private theorem isTreeGauge_pulse (P : ChainHypotheses a ρA κ L N) {u m : ℕ} [NeZero m] (hm : N ≤ m)
    (η : Fin 3 → ChartBondIndex L u m → ℝ) : IsTreeGauge (u + 1) m (pulse a ρA u m η) :=
  ⟨fun e b hb => by
    show chainTop u (m * L) (pushDown a ρA u (m * L) fun e => extendChart (η e)) e b = 0
    rw [chainTop_pushDown]
    exact P.lift_off u m hm (η e) b hb, isTreeGauge_pushDown P u (m * L) (le_side_mul P hm) _⟩
private theorem fluct_pulse (P : ChainHypotheses a ρA κ L N) {u m : ℕ} [NeZero m] (hm : N ≤ m)
    (η : Fin 3 → ChartBondIndex L u m → ℝ) (e : Fin 3) : fluct a ρA u m (pulse a ρA u m η) e = η e := by
  funext b
  refine P.read_lift u m hm _ e (η e) ?_ b
  funext c
  show chainTop u (m * L) (pushDown a ρA u (m * L) fun e => extendChart (η e)) e c -
    pushColours a ρA L u (0 : ColourForm m) e c = _
  rw [chainTop_pushDown, pushColours_zero]
  simp
private theorem hessianRest_pulse (P : ChainHypotheses a ρA κ L N) {u m : ℕ} [NeZero m] (hm : N ≤ m)
    (η : Fin 3 → ChartBondIndex L u m → ℝ) (x : LevelChain L (u + 1) m) :
    hessianRest a ρA (u + 1) m (pulse a ρA u m η) x =
      ∑ e : Fin 3, η e ⬝ᵥ (trivialHessian a L u m).mulVec (fluct a ρA u m x e) := by
  simp only [hessianRest]
  rw [show chainLower (pulse a ρA u m η) = pushDown a ρA u (m * L) (fun e => extendChart (η e)) from rfl,
    hessianRest_pushDown, zero_add]
  exact Finset.sum_congr rfl fun e _ => by rw [fluct_pulse P hm]
variable (u j d n : ℕ)
private def levelAt (X : LevelChain L (u + 1 + j + d) n) : LevelChain L (u + 1) (fineSide L j (fineSide L d n)) :=
  chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d n X)
variable [NeZero n]
private def fluctVector (a ρA : ℝ) (η : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) :
    LevelChain L (u + 1 + j + d) n :=
  padAbove (u + 1 + j) d n (padAbove (u + 1) j (fineSide L d n) (pulse a ρA u _ η))
private theorem levelAt_fluctVector (η : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) :
    levelAt u j d n (fluctVector u j d n a ρA η) = pulse a ρA u _ η := by
  unfold levelAt fluctVector
  rw [chainDescend_padAbove, chainDescend_padAbove]
private theorem chainTop_fluctVector (η : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) :
    chainTop (u + 1 + j + d) n (fluctVector u j d n a ρA η) = 0 :=
  chainTop_padAbove _ d n _ (chainTop_padAbove _ j _ _ rfl)
private theorem isTreeGauge_fluctVector (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    (η : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) :
    IsTreeGauge (u + 1 + j + d) n (fluctVector u j d n a ρA η) :=
  isTreeGauge_padAbove _ d n _ (chainTop_padAbove _ j _ _ rfl)
    (isTreeGauge_padAbove _ j _ _ rfl (isTreeGauge_pulse P (le_fineSide P j (le_fineSide P d hn)) η))
private theorem energyForm_fluctVector (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    (η : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ)
    {x : LevelChain L (u + 1 + j + d) n} (hx : IsTreeGauge (u + 1 + j + d) n x) :
    energyForm a (u + 1 + j + d) n (fluctVector u j d n a ρA η) x =
      ∑ e : Fin 3, η e ⬝ᵥ (trivialHessian a L u _).mulVec (fluct a ρA u _ (levelAt u j d n x) e) := by
  rw [energyForm_eq_hessianRest P hn (isTreeGauge_fluctVector u j d n P hn η) hx (chainTop_fluctVector u j d n η)]
  unfold fluctVector
  rw [hessianRest_padAbove _ d n _ _ (chainTop_padAbove _ j _ _ rfl), hessianRest_padAbove _ j _ _ _ rfl,
    hessianRest_pulse P (le_fineSide P j (le_fineSide P d hn))]
  rfl
private theorem energyForm_fluctVector_inv (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    (co : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ)
    {x : LevelChain L (u + 1 + j + d) n} (hx : IsTreeGauge (u + 1 + j + d) n x) :
    energyForm a (u + 1 + j + d) n
      (fluctVector u j d n a ρA fun e => (trivialHessian a L u _)⁻¹.mulVec (co e)) x =
      ∑ e : Fin 3, ∑ b, co e b * fluct a ρA u _ (levelAt u j d n x) e b := by
  classical
  have hm := le_fineSide P j (le_fineSide P d hn)
  have hH := P.posDef u _ hm
  rw [energyForm_fluctVector u j d n P hn _ hx]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [dotProduct_mulVec_comm_of_posDef hH, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit), Matrix.one_mulVec]
  exact dotProduct_comm _ _
end Vector
section Requirements
variable {a ρA κ : ℝ} {L N : ℕ} [NeZero L] (u j d n : ℕ) [NeZero n]
private def stepDefectLinear (a ρA : ℝ) (L : ℕ) [NeZero L] (u j d n : ℕ) [NeZero n] :
    LevelChain L (u + 1 + j + d) n →ₗ[ℝ] ColourForm (fineSide L j (fineSide L d n) * L) where
  toFun X := stepDefect a ρA u _ (levelAt u j d n X)
  map_add' X Y := by
    unfold levelAt
    rw [chainDescend_add, chainDescend_add, stepDefect_add]
  map_smul' r X := by
    unfold levelAt
    rw [chainDescend_smul, chainDescend_smul, stepDefect_smul]
    rfl
private def curlLinear (L : ℕ) [NeZero L] (u j d n : ℕ) [NeZero n] :
    LevelChain L (u + 1 + j + d) n →ₗ[ℝ] (Fin 3 → TorusPlaquette (fineSide L d n) → ℝ) where
  toFun X e p := curl (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) d n X) e) p
  map_add' X Y := by
    funext e p
    rw [chainDescend_add, chainTop_add]
    exact curl_add' _ _ _
  map_smul' r X := by
    funext e p
    rw [chainDescend_smul, chainTop_smul]
    exact curl_smul' _ _ _
private theorem stepDefect_off_chart (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    {X : LevelChain L (u + 1 + j + d) n}
    (hX : IsTreeGauge (u + 1 + j + d) n X) (e : Fin 3) (b : TorusBond (fineSide L j (fineSide L d n) * L))
    (hb : b ∉ StepCosts.chartBonds L (fineSide L j (fineSide L d n))) :
    stepDefect a ρA u _ (levelAt u j d n X) e b = 0 := by
  have hm := le_fineSide P j (le_fineSide P d hn)
  obtain ⟨h1, _⟩ := isTreeGauge_chainDescend (u + 1) j _ _ (isTreeGauge_chainDescend (u + 1 + j) d n X hX)
  have h1' : chainTop u _ (chainLower (levelAt u j d n X)) e b = 0 := h1 e b hb
  show chainTop u _ (chainLower (levelAt u j d n X)) e b - responseMap a ρA L u _ b = 0
  rw [h1', P.trees u _ hm _ b hb, sub_zero]
private theorem exists_coeffs_of_functional (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    (l : StrongDual ℝ (ColourForm (fineSide L j (fineSide L d n) * L))) :
    ∃ co : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ, ∀ X : LevelChain L (u + 1 + j + d) n,
      IsTreeGauge (u + 1 + j + d) n X →
        l (stepDefectLinear a ρA L u j d n X) = ∑ e : Fin 3, ∑ b, co e b * fluct a ρA u _ (levelAt u j d n X) e b := by
  classical
  have hm := le_fineSide P j (le_fineSide P d hn)
  let lift : (Fin 3 × ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun η => l fun e => extendChart fun b => η (e, b)
      map_add' := fun η ζ => by
        have h : (fun e => extendChart fun b => (η + ζ) (e, b)) =
            (fun e => extendChart fun b => η (e, b)) + fun e => extendChart fun b => ζ (e, b) := by
          funext e c
          simp only [extendChart, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
        rw [h, map_add]
      map_smul' := fun r η => by
        have h : (fun e => extendChart fun b => (r • η) (e, b)) = r • fun e => extendChart fun b => η (e, b) := by
          funext e c
          simp only [extendChart, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
        rw [h, map_smul]
        rfl }
  refine ⟨fun e b => lift fun i => if (e, b) = i then 1 else 0, fun X hX => ?_⟩
  have e1 : stepDefectLinear a ρA L u j d n X = fun e => extendChart fun b => fluct a ρA u _ (levelAt u j d n X) e b := by
    funext e
    exact (P.lift_read u _ hm _ e fun b hb => stepDefect_off_chart u j d n P hn hX e b hb).symm
  rw [e1]
  have e2 := LinearMap.pi_apply_eq_sum_univ lift (fun i : Fin 3 × ChartBondIndex L u (fineSide L j (fineSide L d n)) =>
    fluct a ρA u _ (levelAt u j d n X) i.1 i.2)
  have e3 : l (fun e => extendChart fun b => fluct a ρA u _ (levelAt u j d n X) e b) =
      lift fun i => fluct a ρA u _ (levelAt u j d n X) i.1 i.2 := rfl
  rw [e3, e2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_eq_mul, mul_comm]
private theorem fluctuation_bounds (P : ChainHypotheses a ρA κ L N) (hn : N ≤ n)
    (μ : Measure (LevelChain L (u + 1 + j + d) n))
    (hμ : IsCanonicalGaussian (levelEnergy a (u + 1 + j + d) n) μ)
    (hT : ∀ᵐ X ∂μ, IsTreeGauge (u + 1 + j + d) n X) :
    (∀ᵐ X ∂μ, ∀ (e : Fin 3), ∀ b ∉ StepCosts.chartBonds L (fineSide L j (fineSide L d n)),
      stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d n X)) e b = 0) ∧
    (∀ co : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ,
      μ.map (fun X => ∑ e : Fin 3, ∑ b, co e b * chartValues (u := u)
          (stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d n X))) e b) =
        gaussianReal 0 (∑ e : Fin 3, co e ⬝ᵥ
          ((trivialHessian a L u (fineSide L j (fineSide L d n)))⁻¹.mulVec (co e))).toNNReal) ∧
    IndepFun (fun X => stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d n X)))
      (fun X (e : Fin 3) (p : TorusPlaquette (fineSide L d n)) =>
        curl (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) d n X) e) p) μ := by
  classical
  have hm := le_fineSide P j (le_fineSide P d hn)
  set B := energyForm (L := L) a (u + 1 + j + d) n with hB
  have hs : ∀ x y, B x y = B y x := energyForm_comm a _ n
  have hself : ∀ x, B x x = levelEnergy a _ n x := energyForm_self a _ n
  have hp : ∀ x, 0 ≤ B x x := fun x => by
    rw [hself]
    exact levelEnergy_nonneg P.a_pos.le _ n x
  have hG : IsCanonicalGaussian (fun x => B x x) μ := by
    have : (fun x => B x x) = levelEnergy a (u + 1 + j + d) n := funext hself
    rw [this]
    exact hμ
  have := hμ.isProbabilityMeasure
  set w₁ : (Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d n)) → ℝ) → LevelChain L (u + 1 + j + d) n :=
    fun co => fluctVector u j d n a ρA fun e => (trivialHessian a L u _)⁻¹.mulVec (co e) with hw₁
  have hw₁T : ∀ co, IsTreeGauge (u + 1 + j + d) n (w₁ co) := fun co => isTreeGauge_fluctVector u j d n P hn _
  have hw₁f : ∀ co x, IsTreeGauge (u + 1 + j + d) n x →
      B (w₁ co) x = ∑ e : Fin 3, ∑ b, co e b * fluct a ρA u _ (levelAt u j d n x) e b :=
    fun co x hx => energyForm_fluctVector_inv u j d n P hn co hx
  refine ⟨hT.mono fun X hX e b hb => stepDefect_off_chart u j d n P hn hX e b hb, fun co => ?_, ?_⟩
  · have hF : (fun X => ∑ e : Fin 3, ∑ b, co e b * chartValues (u := u)
        (stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d n X))) e b) =ᵐ[μ] B (w₁ co) :=
      hT.mono fun X hX => (hw₁f co X hX).symm
    rw [map_gaussian_of_ae_bilin B hs hp hG (w₁ co) hF, hw₁f co _ (hw₁T co), levelAt_fluctVector]
    congr 2
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [fluct_pulse P hm]
    rfl
  · have hX : Measurable (stepDefectLinear a ρA L u j d n) :=
      (LinearMap.continuous_of_finiteDimensional _).measurable
    have hY : Measurable (curlLinear L u j d n) :=
      (LinearMap.continuous_of_finiteDimensional _).measurable
    choose coOf hco using fun l : StrongDual ℝ (ColourForm (fineSide L j (fineSide L d n) * L)) =>
      exists_coeffs_of_functional u j d n P hn l
    have hex : ∀ m : StrongDual ℝ (Fin 3 → TorusPlaquette (fineSide L d n) → ℝ),
        ∃ w ∈ treeGaugeSubmodule (L := L) (u + 1 + j + d) n, ∀ x ∈ treeGaugeSubmodule (L := L) (u + 1 + j + d) n,
          m (curlLinear L u j d n x) = B w x := by
      intro m
      refine exists_rep_on_submodule (treeGaugeSubmodule (L := L) (u + 1 + j + d) n) B hs
        ((m : _ →ₗ[ℝ] ℝ).comp (curlLinear L u j d n)) fun x hx h0 => ?_
      have hz : curlLinear L u j d n x = 0 := by
        funext e p
        exact curl_eq_zero_of_energy_eq_zero P hn hx (by rw [← hself]; exact h0) e p
      show m (curlLinear L u j d n x) = 0
      rw [hz, map_zero]
    choose w₂ hw₂T hw₂ using hex
    have hcross : ∀ l m, B (w₂ m) (w₁ (coOf l)) = 0 := by
      intro l m
      rw [← hw₂ m _ (hw₁T (coOf l))]
      have hz : curlLinear L u j d n (w₁ (coOf l)) = 0 := by
        funext e p
        show curl (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) d n (w₁ (coOf l))) e) p = 0
        have e1 : chainDescend (u + 1 + j) d n (w₁ (coOf l)) =
            padAbove (u + 1) j (fineSide L d n) (pulse a ρA u _ _) :=
          chainDescend_padAbove _ d n _
        rw [e1, chainTop_padAbove _ j _ _ rfl]
        simp [curl]
      rw [hz, map_zero]
    refine indepFun_of_joint_gaussian hX hY (fun l => B (w₁ (coOf l)) (w₁ (coOf l))) (fun m => B (w₂ m) (w₂ m))
      (fun _ => hp _) (fun _ => hp _) (fun l => ?_) (fun m => ?_) (fun l m => ?_)
    · refine map_gaussian_of_ae_bilin B hs hp hG _ (hT.mono fun X hX => ?_)
      show l (stepDefectLinear a ρA L u j d n X) = _
      rw [hco l X hX, hw₁f _ X hX]
    · exact map_gaussian_of_ae_bilin B hs hp hG _ (hT.mono fun X hX => hw₂ m X hX)
    · have h1 : (fun X => l (stepDefectLinear a ρA L u j d n X) + m (curlLinear L u j d n X)) =ᵐ[μ]
          B (w₁ (coOf l) + w₂ m) := hT.mono fun X hX => by
        show l (stepDefectLinear a ρA L u j d n X) + m (curlLinear L u j d n X) = B (w₁ (coOf l) + w₂ m) X
        rw [map_add, LinearMap.add_apply, hco l X hX, hw₁f _ X hX, hw₂ m X hX]
      have h2 := map_gaussian_of_ae_bilin B hs hp hG _ h1
      have h3 : B (w₁ (coOf l) + w₂ m) (w₁ (coOf l) + w₂ m) =
          B (w₁ (coOf l)) (w₁ (coOf l)) + B (w₂ m) (w₂ m) := by
        simp only [map_add, LinearMap.add_apply]
        rw [hs (w₁ (coOf l)) (w₂ m), hcross l m]
        ring
      rw [h3] at h2
      exact h2
end Requirements
section Contours
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem siteOfInt_basisVector {m : ℕ} (i : Fin 4) :
    (siteOfInt (LatticeFractionalIntegration.basisVector i) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.SharedProofs.p5838 <;> assumption
private theorem toTorusSite_siteOfCoords (z : Fin 4 → ℤ) :
    (TorusLumps.toTorusSite (n * L) (BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame L n) 0 z) :
      TorusSite (n * L)) = siteOfInt z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.toTorusSite_siteOfCoords <;> assumption
private theorem pathSum_eq_sumAlongWord (A : TorusBond (n * L) → ℝ) (z : Fin 4 → ℤ) (l : List BlockAverages.PathStep) :
    ColdStepAtMirrorFrames.pathSum (F := TorusLumps.stepBlockFrame L n) (j := 0)
        (fun x i => A (TorusLumps.toTorusSite (n * L) x, i)) (BlockAverages.siteOfCoords 0 z) l =
      sumAlongWord A (TorusContours.pathToWord (siteOfInt z) l) := by
  induction l generalizing z with
  | nil => simp [ColdStepAtMirrorFrames.pathSum, TorusContours.pathToWord, sumAlongWord]
  | cons st r ih =>
    have e1 : (BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame L n) 0 z +
        BlockAverages.stepDisplacement 0 st) =
        BlockAverages.siteOfCoords 0 (z + FlatPairing.stepDisplacement st) := by
      rw [ColdStepAtMirrorFrames.stepDisplacement_eq_siteOfCoords, ColdStepAtMirrorFrames.siteOfCoords_map_add]
    have e2 : (BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame L n) 0 z - BlockAverages.unitStep 0 st.1) =
        BlockAverages.siteOfCoords 0 (z - LatticeFractionalIntegration.basisVector st.1) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ColdStepAtMirrorFrames.siteOfCoords_map_add,
        ColdStepAtMirrorFrames.siteOfCoords_map_neg]
      rfl
    have e3 : (siteOfInt (z + FlatPairing.stepDisplacement st) : TorusSite (n * L)) =
        if st.2 then siteOfInt z + TorusFields.unitStep (n * L) st.1
        else siteOfInt z - TorusFields.unitStep (n * L) st.1 := by
      rw [siteOfInt_add]
      unfold FlatPairing.stepDisplacement
      split_ifs
      · rw [siteOfInt_basisVector]
      · rw [sub_eq_add_neg, ← siteOfInt_basisVector]
        congr 1
        funext k
        simp [siteOfInt]
    have e4 : (siteOfInt (z - LatticeFractionalIntegration.basisVector st.1) : TorusSite (n * L)) =
        siteOfInt z - TorusFields.unitStep (n * L) st.1 := by
      rw [← siteOfInt_basisVector]
      funext k
      simp [siteOfInt]
    simp only [ColdStepAtMirrorFrames.pathSum]
    rw [e1, e2, ih, toTorusSite_siteOfCoords, toTorusSite_siteOfCoords, e3, e4]
    by_cases h : st.2 = true
    · simp [TorusContours.pathToWord, sumAlongWord, h]
    · simp [TorusContours.pathToWord, sumAlongWord, h]
private theorem contourMean_eq_contourAverage (W : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    TwoLevelMixtures.contourMean L W c = _root_.YangMills.Construction.MomentLaw.contourAverage L W c := by
  have e2 : BlockAverages.refineSite (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 c.1) =
      BlockAverages.siteOfCoords 0 fun k => (L : ℤ) * ((c.1 k).cast : ℤ) :=
    ColdStepAtMirrorFrames.refineSite_siteOfCoords_mul (F := TorusLumps.stepBlockFrame L n) (j := 0)
      (Nat.zero_lt_succ _) _
  unfold TwoLevelMixtures.contourMean ColdStepAtMirrorFrames.contourAverage _root_.YangMills.Construction.MomentLaw.contourAverage
    TorusContours.contourWeight TorusContours.contourIndex
  rw [e2, Finset.sum_product]
  simp only [pathSum_eq_sumAlongWord]
  rfl
end Contours
section Chart
variable {L n u : ℕ} [NeZero L] [NeZero n]
private theorem period_depth (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period (torusFrame L u n).depth i = n * L :=
  TopLevelSites.period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private def frameBond (L u : ℕ) {n : ℕ} (b : TorusBond (n * L)) :
    (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4 :=
  (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
private def torusBond (L u n : ℕ) [NeZero L] [NeZero n] (b : ChartBondIndex L u n) : TorusBond (n * L) :=
  (TorusLumps.toTorusSite (n * L) b.1.1, b.1.2)
private theorem frameBond_torusBond (b : ChartBondIndex L u n) : frameBond L u (torusBond L u n b) = b.1 :=
  Prod.ext (TopLevelSites.torusSiteInFrame_toTorusSite (period_depth L u n) _) rfl
private theorem torusBond_frameBond (c : TorusBond (n * L)) :
    (TorusLumps.toTorusSite (n * L) (frameBond L u c).1, (frameBond L u c).2) = c :=
  Prod.ext (TopLevelSites.toTorusSite_torusSiteInFrame (period_depth L u n) c.1) rfl
private theorem mem_chartBonds_iff (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    b ∈ StepCosts.chartBonds L n ↔ ¬ BlockAverages.IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by apply _root_.YangMills.DeltaSharedProofs.p2283 <;> assumption
private theorem torusBond_mem (hL : Odd L) (h2 : 2 ≤ n) (b : ChartBondIndex L u n) :
    torusBond L u n b ∈ StepCosts.chartBonds L n := by apply _root_.YangMills.DeltaSharedProofs.p502481 <;> assumption
private theorem chartValues_eq (X : ColourForm (n * L)) (e : Fin 3) (b : ChartBondIndex L u n) :
    chartValues (u := u) X e b = X e (torusBond L u n b) := by apply _root_.YangMills.DeltaSharedProofs.p501607 <;> assumption
private theorem extendChart_torusBond (η : ChartBondIndex L u n → ℝ) (b : ChartBondIndex L u n) :
    extendChart η (torusBond L u n b) = η b := by apply _root_.YangMills.DeltaSharedProofs.p501933 <;> assumption
private theorem extendChart_off (hL : Odd L) (h2 : 2 ≤ n) (η : ChartBondIndex L u n → ℝ) {c : TorusBond (n * L)}
    (hc : c ∉ StepCosts.chartBonds L n) : extendChart η c = 0 := by apply _root_.YangMills.SharedProofs.p85564 <;> assumption
private theorem extendChart_chartValues (h6 : ColdStepAtMirrorFrames.chartEquivarianceStatement) (hL : Odd L)
    (h2 : 2 ≤ n) (X : ColourForm (n * L)) (e : Fin 3) (hX : ∀ b ∉ StepCosts.chartBonds L n, X e b = 0) :
    extendChart (u := u) (fun b => chartValues (u := u) X e b) = X e := by apply _root_.YangMills.SharedProofs.p20242 <;> assumption
private theorem extendChart_add (η ζ : ChartBondIndex L u n → ℝ) :
    extendChart (η + ζ) = extendChart η + extendChart ζ := by
  classical
  funext c
  simp only [extendChart, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp
private theorem extendChart_sub (η ζ : ChartBondIndex L u n → ℝ) :
    extendChart (η - ζ) = extendChart η - extendChart ζ := by
  classical
  funext c
  simp only [extendChart, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp
end Chart
section Distances
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem supDist_le_blockDist (hL : Odd L) (x y : TorusSite (n * L)) :
    TorusFields.supDist x y ≤
      L * TorusFields.supDist (TorusLumps.parentBlock L x) (TorusLumps.parentBlock L y) + 2 * L := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (TorusLumps.parentBlock L x) (TorusLumps.parentBlock L y)
  have h1 : TorusFields.supDist x (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L x)) ≤ L :=
    TorusLumps.supDist_le_of_parentBlock_eq L (TorusBlocks.parentBlock_blockCentreSite hL _).symm
  have h2 : TorusFields.supDist (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L y)) y ≤ L :=
    TorusLumps.supDist_le_of_parentBlock_eq L (TorusBlocks.parentBlock_blockCentreSite hL _)
  have h3 : TorusFields.supDist (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L x))
      (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L y)) ≤
      L * TorusFields.supDist (TorusLumps.parentBlock L x) (TorusLumps.parentBlock L y) := by
    rw [he, ContourMeans.blockCentreSite_add, ← he]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hb i)
  have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle x (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L x)) y
  have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L x))
    (TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L y)) y
  omega
end Distances
section Inverse
variable {a ρA lam r c : ℝ} {L n u : ℕ} [NeZero L] [NeZero n]
private theorem maxwellForm_add_left {m : ℕ} [NeZero m] (A B C : TorusBond m → ℝ) :
    maxwellForm a L u (A + B) C = maxwellForm a L u A C + maxwellForm a L u B C := by
  simp only [maxwellForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem maxwellForm_add_right {m : ℕ} [NeZero m] (A B C : TorusBond m → ℝ) :
    maxwellForm a L u A (B + C) = maxwellForm a L u A B + maxwellForm a L u A C := by
  simp only [maxwellForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem maxwellForm_sub_left {m : ℕ} [NeZero m] (A B C : TorusBond m → ℝ) :
    maxwellForm a L u (A - B) C = maxwellForm a L u A C - maxwellForm a L u B C := by
  simp only [maxwellForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem maxwellForm_sub_right {m : ℕ} [NeZero m] (A B C : TorusBond m → ℝ) :
    maxwellForm a L u A (B - C) = maxwellForm a L u A B - maxwellForm a L u A C := by
  simp only [maxwellForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
private theorem contourAverage_sub (A B : TorusBond (n * L) → ℝ) (c' : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A - B) c' = _root_.YangMills.Construction.MomentLaw.contourAverage L A c' - _root_.YangMills.Construction.MomentLaw.contourAverage L B c' := by
  rw [sub_eq_add_neg, contourAverage_add, ← neg_one_smul ℝ B, contourAverage_smul]
  ring
private theorem interpForm_extendChart
    (hsq : ∀ (Y : TorusBond n → ℝ) (η : ChartBondIndex L u n → ℝ),
      maxwellForm a L u (fun b => responseMap a ρA L u Y b + extendChart η b)
          (fun b => responseMap a ρA L u Y b + extendChart η b) +
        a * ∑ c : TorusBond n, (contourAverage L (fun b => responseMap a ρA L u Y b + extendChart η b) c - Y c) ^ 2 =
      maxwellForm a L (u + 1) Y Y + η ⬝ᵥ ((trivialHessian a L u n).mulVec η))
    (hsym : ∀ b b' : TorusBond (n * L), maxwellKernel a L u b b' = maxwellKernel a L u b' b)
    (hH : (trivialHessian a L u n).PosDef) (η ζ : ChartBondIndex L u n → ℝ) :
    TwoLevelMixtures.interpForm a L u 0 (extendChart η) (extendChart ζ) = η ⬝ᵥ (trivialHessian a L u n).mulVec ζ := by
  classical
  have q : ∀ ξ : ChartBondIndex L u n → ℝ, maxwellForm a L u (extendChart ξ) (extendChart ξ) +
      a * ∑ c : TorusBond n, _root_.YangMills.Construction.MomentLaw.contourAverage L (extendChart ξ) c ^ 2 = ξ ⬝ᵥ (trivialHessian a L u n).mulVec ξ := by
    intro ξ
    have h := hsq 0 ξ
    have e : (fun b => responseMap a ρA L u (0 : TorusBond n → ℝ) b + extendChart ξ b) = extendChart ξ := by
      funext b
      rw [responseMap_zero]
      simp
    have z : maxwellForm a L (u + 1) (0 : TorusBond n → ℝ) 0 = 0 := by simp [maxwellForm]
    rw [e, z, zero_add] at h
    simpa using h
  set G := extendChart η with hG
  set Z := extendChart ζ with hZ
  have hp := q (η + ζ)
  have hm := q (η - ζ)
  rw [extendChart_add, ← hG, ← hZ] at hp
  rw [extendChart_sub, ← hG, ← hZ] at hm
  have hc : maxwellForm a L u Z G = maxwellForm a L u G Z := by
    unfold maxwellForm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [hsym b' b]
    ring
  have hr : (η + ζ) ⬝ᵥ (trivialHessian a L u n).mulVec (η + ζ) - (η - ζ) ⬝ᵥ (trivialHessian a L u n).mulVec (η - ζ) =
      4 * (η ⬝ᵥ (trivialHessian a L u n).mulVec ζ) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
    rw [dotProduct_mulVec_comm_of_posDef hH ζ η]
    ring
  have hf : ∑ c : TorusBond n, _root_.YangMills.Construction.MomentLaw.contourAverage L (G + Z) c ^ 2 - ∑ c : TorusBond n, _root_.YangMills.Construction.MomentLaw.contourAverage L (G - Z) c ^ 2 =
      4 * ∑ c : TorusBond n, _root_.YangMills.Construction.MomentLaw.contourAverage L G c * _root_.YangMills.Construction.MomentLaw.contourAverage L Z c := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [contourAverage_add, contourAverage_sub]
    ring
  have hk : maxwellForm a L u (G + Z) (G + Z) - maxwellForm a L u (G - Z) (G - Z) = 4 * maxwellForm a L u G Z := by
    simp only [maxwellForm_add_left, maxwellForm_add_right, maxwellForm_sub_left, maxwellForm_sub_right]
    rw [hc]
    ring
  have e1 : TwoLevelMixtures.interpForm a L u 0 G Z =
      maxwellForm a L u G Z + a * ∑ c : TorusBond n, _root_.YangMills.Construction.MomentLaw.contourAverage L G c * _root_.YangMills.Construction.MomentLaw.contourAverage L Z c := by
    unfold TwoLevelMixtures.interpForm TwoLevelMixtures.interpKinetic TwoLevelMixtures.contourPairing
    simp only [contourMean_eq_contourAverage]
    ring
  rw [e1]
  linear_combination (1 / 4) * hp - (1 / 4) * hm - (1 / 4) * hk - (a / 4) * hf + (1 / 4) * hr
private theorem abs_le_inv_of_coercive {ι : Type} [Fintype ι] {lam : ℝ} (hlam : 0 < lam) (η : ι → ℝ) (b b' : ι)
    (hS : lam * ∑ x, η x ^ 2 ≤ η b') : |η b| ≤ 1 / lam := by
  classical
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = ∑ x, η x ^ 2 := ⟨_, rfl⟩
  rw [← hSd] at hS
  have hS0 : 0 ≤ S := hSd ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : ∀ x, η x ^ 2 ≤ S := fun x => by
    rw [hSd]
    exact Finset.single_le_sum (f := fun x => η x ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  rcases hS0.eq_or_lt with h0 | hpos
  · have h1 : η b ^ 2 ≤ 0 := h0 ▸ hle b
    have h3 : η b = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _))
    rw [h3, abs_zero]
    positivity
  · have h3 : (lam * S) ^ 2 ≤ η b' ^ 2 := pow_le_pow_left₀ (mul_nonneg hlam.le hS0) hS 2
    have h4 : lam ^ 2 * S ≤ 1 := by
      have h5 := h3.trans (hle b')
      have h6' : lam ^ 2 * S * S ≤ 1 * S := by nlinarith
      exact le_of_mul_le_mul_right h6' hpos
    have h7 : (lam * |η b|) ^ 2 ≤ 1 := by
      rw [mul_pow, sq_abs]
      have := hle b
      nlinarith [sq_nonneg lam]
    have h8 : lam * |η b| ≤ 1 := by
      have h9 : 0 ≤ lam * |η b| := mul_nonneg hlam.le (abs_nonneg _)
      nlinarith
    rw [le_div_iff₀ hlam]
    linarith
private theorem abs_inv_trivialHessian_le (hodd : Odd L) (h6 : ColdStepAtMirrorFrames.chartEquivarianceStatement)
    (hlam : 0 < lam) (hc0 : 0 ≤ c) (hc1 : 3 * c * L ≤ r) (hc2 : 8 * c * L ≤ 1) (hn : 64 ≤ n)
    (hsq : ∀ (Y : TorusBond n → ℝ) (η : ChartBondIndex L u n → ℝ),
      maxwellForm a L u (fun b => responseMap a ρA L u Y b + extendChart η b)
          (fun b => responseMap a ρA L u Y b + extendChart η b) +
        a * ∑ c : TorusBond n, (contourAverage L (fun b => responseMap a ρA L u Y b + extendChart η b) c - Y c) ^ 2 =
      maxwellForm a L (u + 1) Y Y + η ⬝ᵥ ((trivialHessian a L u n).mulVec η))
    (hsym : ∀ b b' : TorusBond (n * L), maxwellKernel a L u b b' = maxwellKernel a L u b' b)
    (hH : (trivialHessian a L u n).PosDef)
    (hfl : ∀ v : ChartBondIndex L u n → ℝ, lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian a L u n).mulVec v)
    (hinv : ∀ (b₀ : TorusBond (n * L)) (g : TorusBond (n * L) → ℝ), b₀ ∈ StepCosts.chartBonds L n →
      TwoLevelMixtures.SolvesShiftedEq a L u 0 1 lam (MixtureJets.bondIndicator b₀) g → ∀ b : TorusBond (n * L),
        |g b| ≤ 2 / lam * Real.exp (-(2 * r * TorusFields.supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b₀.1))))
    (b b' : ChartBondIndex L u n) :
    |(trivialHessian a L u n)⁻¹ b b'| ≤
      2 / lam * Real.exp (-(2 * c * (TorusFields.supDist (TorusLumps.toTorusSite (n * L) b.1.1)
        (TorusLumps.toTorusSite (n * L) b'.1.1) : ℝ))) := by
  classical
  have h2 : 2 ≤ n := by omega
  have hU : IsUnit (trivialHessian a L u n).det := (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit
  set δ : ChartBondIndex L u n → ℝ := Pi.single b' 1 with hδ
  set η : ChartBondIndex L u n → ℝ := (trivialHessian a L u n)⁻¹.mulVec δ with hηd
  have hη : ∀ x, η x = (trivialHessian a L u n)⁻¹ x b' := fun x => by
    rw [hηd, hδ, Matrix.mulVec_single_one]
    rfl
  have hHη : (trivialHessian a L u n).mulVec η = δ := by
    rw [hηd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hsolve : TwoLevelMixtures.SolvesShiftedEq a L u 0 1 lam (MixtureJets.bondIndicator (torusBond L u n b'))
      (extendChart η) := by
    refine ⟨fun x hx => extendChart_off hodd h2 η hx, fun φ hφ => ?_⟩
    obtain ⟨ζ, rfl⟩ : ∃ ζ : ChartBondIndex L u n → ℝ, φ = extendChart ζ :=
      ⟨_, (extendChart_chartValues (u := u) h6 hodd h2 (fun _ => φ) 0 hφ).symm⟩
    unfold TwoLevelMixtures.shiftedInterpForm
    rw [interpForm_extendChart hsq hsym hH, dotProduct_mulVec_comm_of_posDef hH, hHη]
    have e1 : ∑ x, MixtureJets.bondIndicator (torusBond L u n b') x * extendChart ζ x = ζ b' := by
      rw [Finset.sum_eq_single (torusBond L u n b')]
      · rw [extendChart_torusBond]
        simp [MixtureJets.bondIndicator]
      · intro x _ hx
        simp [MixtureJets.bondIndicator, hx]
      · simp
    rw [e1, hδ]
    simp
  have hb1 := hinv (torusBond L u n b') _ (torusBond_mem hodd h2 b') hsolve (torusBond L u n b)
  rw [extendChart_torusBond, hη] at hb1
  have hS := hfl η
  rw [hHη, hδ] at hS
  have hηb' : η ⬝ᵥ Pi.single b' 1 = η b' := by simp
  rw [hηb'] at hS
  have hb2 : |η b| ≤ 1 / lam := abs_le_inv_of_coercive hlam η b b' hS
  rw [← hη]
  rw [← hη] at hb1
  have hfine := supDist_le_blockDist hodd (torusBond L u n b).1 (torusBond L u n b').1
  set D : ℕ := TorusFields.supDist (TorusLumps.parentBlock L (torusBond L u n b).1)
    (TorusLumps.parentBlock L (torusBond L u n b').1) with hD
  set d : ℕ := TorusFields.supDist (TorusLumps.toTorusSite (n * L) b.1.1) (TorusLumps.toTorusSite (n * L) b'.1.1) with hd
  have hfine' : (d : ℝ) ≤ L * D + 2 * L := by exact_mod_cast hfine
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · have h3 : 2 * c * (d : ℝ) ≤ 1 / 2 := by
      rw [hD0] at hfine'
      have h4 : (d : ℝ) ≤ 2 * L := by simpa using hfine'
      nlinarith
    have h5 : (1 / 2 : ℝ) ≤ Real.exp (-(2 * c * (d : ℝ))) := by
      have h6' := Real.add_one_le_exp (-(2 * c * (d : ℝ)))
      linarith
    calc |η b| ≤ 1 / lam := hb2
      _ = 2 / lam * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
  · refine hb1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have h3 : (d : ℝ) ≤ 3 * L * D := by nlinarith
    have h4 : 2 * c * (d : ℝ) ≤ 2 * c * (3 * L * D) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * c * (3 * L * D) ≤ 2 * r * D := by nlinarith
    linarith
end Inverse
private theorem exists_params_of_eventuallyOrdered (hC : ColdStepAtMirrorFrames.ExistsCutoff)
    {Pr : ColdStepAtMirrorFrames.StepParameters → Prop} (h : ColdStepAtMirrorFrames.EventuallyOrdered Pr) (a : ℝ)
    (ha : 1 ≤ a) :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ c : ColdStepAtMirrorFrames.ColdChainParameters, c.Admissible a L →
      ∃ (Ct κ η₃ : ℝ) (nss : ℕ) (σ : ℝ) (p : ℝ → ℝ) (Cs E : ℝ) (n₀ : ℕ) (CE y₁ : ℝ),
        Pr ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, y₁⟩ := by apply _root_.YangMills.SharedProofs.p26215 <;> assumption
private theorem eventuallyOrdered_and {P Q : ColdStepAtMirrorFrames.StepParameters → Prop}
    (h₁ : ColdStepAtMirrorFrames.EventuallyOrdered P) (h₂ : ColdStepAtMirrorFrames.EventuallyOrdered Q) :
    ColdStepAtMirrorFrames.EventuallyOrdered fun T => P T ∧ Q T := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.EventuallyOrdered.and <;> assumption
end GaussianFluctuations
open GaussianFluctuations TorusFields WeightedResponses
theorem gaussianChainFluctuations (hS : completedSquareStatement)
    (hG : ResponseInTheExpansion.gradientMaxwellStatement) (hB : MomentMethod.bareMaxwellFormStatement)
    (hH : trivialHessianPosDefStatement) (hR : TwoLevelMixtures.levelExpansionsAtSmallRateStatement)
    (hI : CriticalGerms.interpInverseDecayStatement) (hM : LevelComparisons.responsesAreInterpResponsesStatement)
    (hP : StepPolarity.polarIdentityStatement) (hC : ColdStepAtMirrorFrames.ExistsCutoff)
    (h6 : ColdStepAtMirrorFrames.chartEquivarianceStatement) : gaussianChainFluctuationsStatement := by
  classical
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, g₁⟩ := hS a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, g₂⟩ := hG a ha
  obtain ⟨L₃, g₃⟩ := exists_params_of_eventuallyOrdered hC
    (eventuallyOrdered_and hR (eventuallyOrdered_and hI (eventuallyOrdered_and hM hP))) a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (rt₁ c) (rt₂ c), max C₁ C₂, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hCd Kr hKr
  subst hTa hTL
  obtain ⟨y₁, g₁'⟩ := g₁ Tb.side hodd ((le_max_left _ _).trans hL) Tb rfl rfl hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd)
  obtain ⟨y₂, g₂'⟩ := g₂ Tb.side hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) Tb rfl rfl hD hCS hCH
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hCd)
  obtain ⟨c₀, nss, hT, -⟩ := id hCS
  have hcH : c₀.Admissible Tb.coupling Tb.side := hT.2.2.2.2.2.2.2
  have hρ : 0 < c₀.ρA := by
    rw [hT.2.2.1]
    exact hD.chain.2.2.2.1
  obtain ⟨Ct, κ, η₃, nss', σ, p, Cs, E, n₀, CE, y₃, hRows, hInv, hResp, hPol⟩ :=
    g₃ Tb.side hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) c₀ hcH
  obtain ⟨r, hr0, -, hrows⟩ := @hRows Tb.side_ne
  have hinv := @hInv Tb.side_ne r hr0.le hrows
  obtain ⟨Cr, -, hresp⟩ := @hResp Tb.side_ne
  have hsym := (@hPol Tb.side_ne).1
  have hlamTb : 0 < c₀.lam := hcH.positivity.2.2.1
  have hL0 : (0 : ℝ) < Tb.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Tb.side)
  refine ⟨max y₁ y₂, fun y hy hret hrow g hg hgy k _ hk2 hk8 R d hd => ?_⟩
  have hsqY := g₁' y ((le_max_left _ _).trans hy) hret hrow
  have hgrY := g₂' y ((le_max_right _ _).trans hy) hret hrow
  have hn64 : 64 ≤ Tb.n₀ := le_trans (by norm_num) hD.n₀_ge
  have hoddL : Odd (Tb.stepParameters y).side := hD.L_odd
  have htrees : ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ (Y : TorusBond n → ℝ),
      ∀ b ∉ StepCosts.chartBonds (Tb.stepParameters y).side n,
      responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u Y b = 0 := by
    intro u n _ hn Y b hb
    unfold responseMap
    refine Finset.sum_eq_zero fun c _ => ?_
    have h1 := (hresp u n c hn).1.vanishes b hb
    have h2 : responseKernel Tb.coupling c₀.ρA Tb.side u b c = 0 := h1
    rw [hT.2.2.1] at h2
    show responseKernel Tb.coupling Tb.ρA Tb.side u b c * Y c = 0
    rw [h2, zero_mul]
  have P : ChainHypotheses Tb.coupling Tb.ρA (2 * Tb.coercivity) (Tb.stepParameters y).side Tb.n₀ :=
    { a_pos := lt_of_lt_of_le one_pos hD.a_ge
      κ_pos := mul_pos two_pos hD.cK_pos
      one_le := Nat.pos_of_ne_zero (NeZero.ne _)
      square := fun u n _ hn Y η => hsqY u n (hn64.trans hn) Y η
      trees := fun u n _ hn Y b hb => htrees u n (hn64.trans hn) Y b hb
      lift_read := fun u n _ hn X e hX => extendChart_chartValues h6 hoddL (by omega) X e hX
      read_lift := fun u n _ hn X e η hX b => by
        rw [chartValues_eq, hX, extendChart_torusBond]
      lift_off := fun u n _ hn η b hb => extendChart_off hoddL (by omega) η hb
      bare := fun m _ A A' => hB _ _ m A A'
      posDef := fun u n _ hn =>
        (hH Tb.coupling Tb.side c₀ hD.a_ge hD.L_odd hD.L_ge hcH hρ u n (hn64.trans hn)).1
      curl_le := fun u m _ hm A => (hgrY u m hm).2.2 A }
  have hcc : 0 < min (r / (3 * Tb.side)) (1 / (8 * Tb.side)) := lt_min (by positivity) (by positivity)
  refine ⟨fun _ => 0, min (r / (3 * Tb.side)) (1 / (8 * Tb.side)), y, hcc, le_rfl, fun S => ?_⟩
  refine ⟨fun u j d _ μ hμ hTr => ?_, fun u n _ hn b b' => ?_⟩
  · have hside : Tb.n₀ ≤ S.data.period (Tb.stepParameters y).side :=
      le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))) S.side_le
    exact fluctuation_bounds u j d _ P hside μ hμ hTr
  · have hlam : Tb.lam = c₀.lam := hT.2.1.symm
    have hc1 : 3 * min (r / (3 * Tb.side)) (1 / (8 * Tb.side)) * Tb.side ≤ r := by
      have h := min_le_left (r / (3 * (Tb.side : ℝ))) (1 / (8 * Tb.side))
      have h' : min (r / (3 * (Tb.side : ℝ))) (1 / (8 * Tb.side)) * (3 * Tb.side) ≤ r := by
        rwa [← le_div_iff₀ (by positivity)]
      linarith
    have hc2 : 8 * min (r / (3 * Tb.side)) (1 / (8 * Tb.side)) * Tb.side ≤ 1 := by
      have h := min_le_right (r / (3 * (Tb.side : ℝ))) (1 / (8 * Tb.side))
      have h' : min (r / (3 * (Tb.side : ℝ))) (1 / (8 * Tb.side)) * (8 * Tb.side) ≤ 1 := by
        rwa [← le_div_iff₀ (by positivity)]
      linarith
    have hHn := hH Tb.coupling Tb.side c₀ hD.a_ge hD.L_odd hD.L_ge hcH hρ u n hn
    have hfin := abs_inv_trivialHessian_le (a := Tb.coupling) (ρA := Tb.ρA) (lam := c₀.lam) (r := r)
      (c := min (r / (3 * Tb.side)) (1 / (8 * Tb.side))) (L := (Tb.stepParameters y).side) (n := n) (u := u)
      hoddL h6 hlamTb hcc.le hc1 hc2 hn
      (hsqY u n hn)
      (fun b b' => (hsym u _ b b' (hn.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne _))))))
      hHn.1 hHn.2
      (fun b₀ g hb₀ hs x => hinv u n 0 b₀ g hn le_rfl zero_le_one hb₀ hs x) b b'
    rw [← hlam] at hfin
    exact hfin
end YangMills.Construction.MomentLaw
end
