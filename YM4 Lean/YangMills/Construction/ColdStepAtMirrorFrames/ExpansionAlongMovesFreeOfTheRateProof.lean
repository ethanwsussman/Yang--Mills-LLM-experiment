import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAlongMovesFreeOfTheRate
import YangMills.Construction.SummableBoundsOfTheFlow.BoundAlongMovesAboveTheFramesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem le_runningMax (a : ℕ → ℝ) {i n : ℕ} (hi : 1 ≤ i) (hn : i ≤ n) : a i ≤ runningMax a n := by apply _root_.YangMills.Construction.Estimates.le_runningMax <;> assumption
private theorem runningMax_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n : ℕ) : 0 ≤ runningMax a n := by apply _root_.YangMills.Construction.Estimates.runningMax_nonneg <;> assumption
variable {F : BlockFrame}
private theorem Perturbation.decayWeight_le_exp (w : Perturbation F) (r : ℝ) (x : F.Site F.depth) (i : Fin 4)
    (hdiag : ∀ z : F.Cell, cellSupDist z z = 0) :
    w.decayWeight r x i ≤ Real.exp (-(r * cellSupDist (enclosingCell x) w.cell)) := by apply _root_.YangMills.Construction.Estimates.Perturbation.decayWeight_le_exp <;> assumption
private theorem sum_over_slots_le {L p : ℕ} {κ r Cg : ℝ} {M : ℕ → ℝ} {e : ℕ → ℝ} {F : BlockFrame}
    (hκ : 0 < κ) (hr : 2 ^ 9 * κ ≤ r) (hL : 2 ^ 40 ≤ L) (hFL : F.blockSide = L) (hM : ∀ q, 0 ≤ M q)
    (hgeo : (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧
      (∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) ∧
      ∀ x y : F.Site F.depth, F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (hsite : ∀ x y : F.Site F.depth, siteSupDist x y = siteSupDist y x)
    (hsum : ∀ z : F.Cell, ∑ b ∈ fineBonds F, Real.exp (-(r / 2 * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (L : ℝ) ^ 4)
    {w : Fin p → Perturbation F} {y : F.Site F.depth} (c : OrderedFinpartition p) (hc6 : c.length ≤ 6) (he : 0 ≤ e c.length)
    {A : ∀ m : Fin c.length, F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hA : ∀ (m : Fin c.length) (x : F.Site F.depth) (i : Fin 4) (q : Fin (c.partSize m)),
      ‖A m x i‖ ≤ M (c.partSize m) * Real.exp (-(r * cellSupDist (enclosingCell x) (w (c.emb m q)).cell))) :
    ∑ b ∈ Fintype.piFinset fun _ : Fin c.length => fineBonds F,
        (e c.length / torusDecayFactor L (κ / 2 ^ 10) (bondSpan y b)) * ∏ m, ‖A m (b m).1 (b m).2‖ ≤
      e c.length * (Real.exp (κ / 2 ^ 10 * L) * (∏ m, M (c.partSize m)) * (Cg * (L : ℝ) ^ 4) ^ c.length) *
        Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))) := by apply _root_.YangMills.Construction.Estimates.sum_partition_slots_le <;> assumption
private theorem bondDeriv_subtractTrivial {F : BlockFrame} {N i : ℕ} {f : LocalFamily} {y : F.Site F.depth}
    {W : F.GaugeField F.depth} {c : Fin i → F.Site F.depth × Fin 4} {X : Fin i → imaginaryQuaternions}
    (hi : i ≠ 0) (hN : i ≤ N)
    (h : ContDiffAt ℝ N (fun τ : Fin i → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by apply _root_.YangMills.Construction.Estimates.bondDeriv_subtractTrivial <;> assumption
theorem expansionAlongPerturbationsUniformInRate_holds (hmot : motionAboveFrameStatement)
    (hexp : expansionAlongMotionStatement) (hsm : SmoothAlongMotion)
    (hcov : BlocksCoverLowerLevel) (hgeo : CubicTorusCellGeometry) :
    ExpansionAlongPerturbationsUniformInRate := by
  intro K r L hK hr0 hLodd hL
  obtain ⟨M, hM, hmo⟩ := hmot 6 K hK
  obtain ⟨Cg, hCg, hsum⟩ := hgeo.2 (r / 2) (by linarith)
  have hL0 : 0 < L := by omega
  let Cp : ℕ → ℝ := fun p => ∑ c : OrderedFinpartition p,
    Real.exp (r / 2 ^ 19 * L) * (∏ m, M (c.partSize m)) * (Cg * (L : ℝ) ^ 4) ^ c.length
  have hCp : ∀ p, 0 ≤ Cp p := fun p => Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => hM _))
      (pow_nonneg (by positivity) _)
  let C : ℝ := ∑ p ∈ Finset.range 7, Cp p + 1
  have hC : 0 < C := by
    have : 0 ≤ ∑ p ∈ Finset.range 7, Cp p := Finset.sum_nonneg fun p _ => hCp p
    linarith
  refine ⟨C, hC, ?_⟩
  intro κ hκ hr F n₀ k p m σ s a ρA e f V η w y hFL hcub hlow hk6 he hf hcold hsmall hana hdec hunit
  have hodd : Odd F.blockSide := hFL ▸ hLodd
  obtain ⟨n, hn64, hside⟩ := hcub
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hper : ∀ i, F.period F.depth i ≠ 0 := fun i => by
    have : 0 < F.blockSide := by rw [hFL]; exact hL0
    simp only [BlockFrame.period]
    exact mul_ne_zero (hpos i).ne' (pow_ne_zero _ this.ne')
  have hall := hcov F hodd hpos
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b => by
    simp [fineBonds, hall]
  have hchord : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    simp [chordBonds, innerBonds, hall, hd]
  obtain ⟨α, hα0, hαs, -, hαe, hαp, -⟩ :=
    hmo F s a ρA r m p V η w hper hr0.le hchord hsmall hana hdec hunit
  set W₀ := interpolatedField s a ρA m V η with hW₀
  set G : F.GaugeField F.depth → ℝ := subtractTrivial f F y with hGdef
  have hGf : ∀ (q : ℕ) (c : Fin q → F.Site F.depth × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => f F y (leftTranslate (bondSpread c X τ) W₀)) 0 :=
    hf.smooth F hlow y W₀ hcold
  have hG : ∀ (q : ℕ) (c : Fin q → F.Site F.depth × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W₀)) 0 := fun q c X =>
    (hGf q c X).sub contDiffAt_const
  have hev : (fun τ => G (perturbedField s a ρA m V η w τ)) =ᶠ[𝓝 0] fun τ => G (leftTranslate (α τ) W₀) :=
    hαe.mono fun τ h => by
      simp only [perturbedField]
      rw [h]
  have hk6' : ((k : ℕ) : WithTop ℕ∞) ≤ (6 : ℕ) := by exact_mod_cast hk6
  refine ⟨?_, ?_⟩
  · have h1 := hsm F F.depth k p G W₀ α hper hG (fun x b => (hαs x b).of_le hk6') hα0
    exact h1.congr_of_eventuallyEq hev
  · intro hp1 hpk
    have hp6 : p ≤ 6 := hpk.trans hk6
    have hpk' : ((p : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast hpk
    have hp6' : ((p : ℕ) : WithTop ℕ∞) ≤ (6 : ℕ) := by exact_mod_cast hp6
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev p).eq_of_nhds]
    obtain ⟨-, hex⟩ := hexp.1 F F.depth p G W₀ α hper (fun q c X => (hG q c X).of_le hpk')
      (fun x b => (hαs x b).of_le hp6') hα0
    rw [hex]
    set D := cellSetDiameter (insert (enclosingCell y) (perturbationCells w)) with hD
    have hterm : ∀ c : OrderedFinpartition p,
        |mixedDerivAlong G W₀ fun m => motionComponent α (c.emb m)| ≤
          runningMax e p * (Real.exp (r / 2 ^ 19 * L) * (∏ m, M (c.partSize m)) *
            (Cg * (L : ℝ) ^ 4) ^ c.length) * Real.exp (-(2 ^ 7 * κ * D)) := by
      intro c
      have hlen : c.length ≤ p := c.length_le
      have hlen0 : c.length ≠ 0 := fun h => by
        have := c.length_pos hp1
        omega
      have hlenk : ((c.length : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast hlen.trans hpk
      have h1 := hexp.2 F F.depth c.length G W₀ (fun m => motionComponent α (c.emb m)) (fineBonds F)
        (fun b => e c.length / torusDecayFactor L (κ / 2 ^ 10) (bondSpan y b)) hper hbond
        (fun q c' X => (hG q c' X).of_le hlenk) (fun b X hX => by
          rw [hGdef, bondDeriv_subtractTrivial hlen0 (hlen.trans hpk) (hGf _ b X)]
          exact hf.decay F hlow y W₀ c.length b X hcold (Nat.one_le_iff_ne_zero.2 hlen0)
            (hlen.trans hpk) hX)
      refine h1.trans ?_
      have hgeo1 := hgeo.1 F hodd ⟨n, hn64, hside⟩
      have h2 := sum_over_slots_le (L := L) (κ := κ) (r := r) (Cg := Cg) (M := M) (e := e) (F := F)
        (w := w) (y := y) hκ hr hL hFL hM ⟨hgeo1.2.2.1, hgeo1.2.2.2.1, hgeo1.2.2.2.2⟩
        (hgeo1.1 F.depth) (fun z => by
          have := hsum F hodd ⟨n, hn64, hside⟩ z
          rwa [hFL] at this) c ((hlen.trans hpk).trans hk6) (he _)
        (A := fun m => motionComponent α (c.emb m)) (fun m x i q => by
          refine (hαp _ (c.emb m) x i q ((c.partSize_le m).trans hp6)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (hM _)
          exact Perturbation.decayWeight_le_exp _ r x i (fun z => by simp [cellSupDist]))
      refine h2.trans ?_
      have hP : 0 ≤ ∏ m, M (c.partSize m) := Finset.prod_nonneg fun _ _ => hM _
      have hQ : 0 ≤ (Cg * (L : ℝ) ^ 4) ^ c.length := pow_nonneg (by positivity) _
      have hrate : κ / 2 ^ 10 * L ≤ r / 2 ^ 19 * L := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        linarith
      refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ ?_ (runningMax_nonneg he p)) (Real.exp_pos _).le
      · exact le_runningMax e (Nat.one_le_iff_ne_zero.2 hlen0) hlen
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hrate) hP) hQ
      · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hP) hQ
    have hlE := runningMax_nonneg he p
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hterm c).trans ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hlE
    have h3 : Cp p ≤ ∑ q ∈ Finset.range 7, Cp q :=
      Finset.single_le_sum (f := Cp) (fun q _ => hCp q) (Finset.mem_range.2 (by omega))
    show Cp p ≤ _
    simp only [C]
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
