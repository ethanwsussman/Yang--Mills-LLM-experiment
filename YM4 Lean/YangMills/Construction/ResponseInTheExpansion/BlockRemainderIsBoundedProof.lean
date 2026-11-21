import YangMills.Construction.ResponseInTheExpansion.BlockRemainderDecaysNearItsValueProof
import YangMills.Construction.ResponseInTheExpansion.BlockRemainderIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Cumulants Estimates CellCounting WeightedResponses LinearResponse
namespace ResponseInTheExpansion
variable {F : BlockFrame}
namespace BlockSumBound
open Classical in
private def supportedOn (F : BlockFrame) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : LocalFamily :=
  fun F' => if h : F' = F then h ▸ r else fun _ _ => 0
private theorem supportedOn_self (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : supportedOn F r F = r := dif_pos rfl
private theorem supportedOn_other (r : F.Site F.depth → F.GaugeField F.depth → ℝ) {F' : BlockFrame} (h : F' ≠ F) :
    supportedOn F r F' = fun _ _ => 0 := dif_neg h
private theorem decayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
private theorem decayFactor_mono {L : ℕ} {δ u v : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (hu : 0 ≤ u) (huv : u ≤ v) :
    torusDecayFactor L δ u ≤ torusDecayFactor L δ v := by apply _root_.YangMills.SharedProofs.p54195 <;> assumption
private theorem hasBoundedDerivatives_supportedOn {L t n₀ : ℕ} {σ δ e e₃ e' : ℝ}
    {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (he : e ≤ e') (he₃ : e₃ ≤ e') (he' : 0 ≤ e') (hf : IsDecayingSiteFamily L σ δ e e₃ r) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun _ => e') (supportedOn F r) := by
  refine ⟨fun F' _ y W hW j c X => ?_, fun F' _ y W γ hW => ?_, fun F' _ y W j c X hW h1 h3 hX => ?_⟩
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      exact_mod_cast hf.smooth y W hW j c X
    · rw [supportedOn_other r h]
      exact contDiffAt_const
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      exact hf.gauge_invariant y W γ hW
    · rw [supportedOn_other r h]
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      refine (hf.decay y W j c X hW h1 h3 hX).trans ?_
      refine div_le_div_of_nonneg_right ?_ (decayFactor_pos _ _ _).le
      split_ifs
      · exact he₃
      · exact he
    · rw [supportedOn_other r h]
      have h0 : bondDeriv (fun _ : F'.GaugeField F'.depth => (0 : ℝ)) W c X = 0 := by
        simp [bondDeriv]
      simp only [h0, abs_zero]
      exact div_nonneg he' (decayFactor_pos _ _ _).le
private theorem runningMax_const_le {e' : ℝ} (he' : 0 ≤ e') (j : ℕ) : runningMax (fun _ => e') j ≤ e' := by
  induction j with
  | zero => exact he'
  | succ j ih => exact max_le ih le_rfl
private theorem interpolatedExpansion_one (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion 1 a ρA m f y η V = centredExpansion false a ρA m f y η V := by apply _root_.YangMills.SharedProofs.p6614 <;> assumption
private theorem liftedExpansion_eq (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.liftedExpansion r y η V =
      centredExpansion false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F r) y η V + r y (uniformField F F.depth) := by
  rw [← interpolatedExpansion_one]
  simp only [ColdHalfLaw.liftedExpansion, interpolatedExpansion, ColdStepAtMirrorFrames.subtractTrivial, supportedOn_self,
    sub_add_cancel]
open Classical in
private def valueSumAtTrivial (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell) : ℝ :=
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), r y (uniformField F F.depth)
private theorem blockSum_eq (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.blockSum r Y η V =
      cellExpansionInField false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F r) Y η V + valueSumAtTrivial r Y := by
  unfold ColdHalfLaw.blockSum Cumulants.cellExpansionInField cellCentredExpansion valueSumAtTrivial
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => liftedExpansion_eq Q r y η V
private theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem bondDeriv_add_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W : F.GaugeField j)
    (c : Fin (k + 1) → F.Site j × Fin 4) (X : Fin (k + 1) → imaginaryQuaternions) :
    bondDeriv (fun W' => G W' + a) W c X = bondDeriv G W c X := by apply _root_.YangMills.SharedProofs.p46198 <;> assumption
private theorem bondDeriv_blockSum (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ∃ s : ℝ, (1 ≤ k → s = 0) ∧ ∀ η : StepVariable (finiteCells F), bondDeriv (Q.blockSum r Y η) V c X =
      fieldDeriv (cellExpansionInField false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F r) Y) V c X η + s := by
  have e : ∀ η : StepVariable (finiteCells F), Q.blockSum r Y η =
      fun V' => cellExpansionInField false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F r) Y η V' +
        valueSumAtTrivial r Y := fun η => by
    funext V'
    exact blockSum_eq Q r Y η V'
  cases k with
  | zero =>
    refine ⟨valueSumAtTrivial r Y, fun h => absurd h (by norm_num), fun η => ?_⟩
    rw [e η, bondDeriv_zero]
    simp only [fieldDeriv, bondDeriv_zero]
  | succ k =>
    refine ⟨0, fun _ => rfl, fun η => ?_⟩
    rw [e η, bondDeriv_add_const, add_zero]
    rfl
open Classical in
private theorem blockSites_card (hb : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤ F.blockSide ^ 4 := by apply _root_.YangMills.SharedProofs.p41914 <;> assumption
private theorem decayFactor_inv_add_exp_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {Cw : ℝ} (hκ : 0 < T.κ) (hL : 16 ≤ T.L)
    (hCw : ∀ u : ℝ, 0 ≤ u → torusDecayFactor T.L T.decayRate u ≤ Cw * Real.exp (2 * T.decayRate * u)) (n : ℕ) :
    (torusDecayFactor T.L T.decayRate ((T.L : ℝ) * n / 16))⁻¹ + Real.exp (-(2 ^ 6 * T.κ * n)) ≤
      (1 + Cw) / torusDecayFactor T.L T.decayRate n := by
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hG := decayFactor_pos T.L T.decayRate (n : ℝ)
  have hL16 : (16 : ℝ) ≤ T.L := by exact_mod_cast hL
  have h1 : (torusDecayFactor T.L T.decayRate ((T.L : ℝ) * n / 16))⁻¹ ≤
      1 / torusDecayFactor T.L T.decayRate n := by
    rw [one_div]
    refine inv_anti₀ hG (decayFactor_mono (by omega) hδ.le hn ?_)
    nlinarith
  have hw := hCw n hn
  have hCw0 : 0 ≤ Cw := by
    by_contra h
    push Not at h
    have : Cw * Real.exp (2 * T.decayRate * n) < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have h2 : Real.exp (-(2 ^ 6 * T.κ * n)) ≤ Cw / torusDecayFactor T.L T.decayRate n := by
    rw [le_div_iff₀ hG]
    have h3 : Real.exp (-(2 ^ 6 * T.κ * n)) * Real.exp (2 * T.decayRate * n) ≤ 1 := by
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.2 ?_
      have : T.decayRate = T.κ / 2 ^ 10 := rfl
      rw [this]
      nlinarith [mul_nonneg hκ.le hn]
    calc Real.exp (-(2 ^ 6 * T.κ * n)) * torusDecayFactor T.L T.decayRate n
        ≤ Real.exp (-(2 ^ 6 * T.κ * n)) * (Cw * Real.exp (2 * T.decayRate * n)) :=
          mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
      _ = Cw * (Real.exp (-(2 ^ 6 * T.κ * n)) * Real.exp (2 * T.decayRate * n)) := by ring
      _ ≤ Cw * 1 := mul_le_mul_of_nonneg_left h3 hCw0
      _ = Cw := mul_one _
  rw [add_div]
  exact add_le_add h1 h2
private theorem transportBounded_supportedOn {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered)
    (hTr : TransportBoundsAt T C₀ Ck) {t : ℕ} {x e : ℝ} {f : LocalFamily} {V : F.GaugeField F.top}
    {r : F.Site F.depth → F.GaugeField F.depth → ℝ} (hst : IsAdmissibleAt T t x f F V) (he : 0 < e)
    (hr : IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r) {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    IsTransportBounded 1 T.a T.chainParams.ρA T.κ T.decayRate C₀ Ck T.L (frameRadius x) 3 (fun _ => e / T.η₃)
      (supportedOn F r) V η := by
  have hη₃ := hD.η₃_pos
  have h0 : 0 ≤ e / T.η₃ := (div_pos he hη₃).le
  have h1 : e ≤ e / T.η₃ := by
    rw [le_div_iff₀ hη₃]
    nlinarith [hD.η₃_le_one]
  exact hTr x t 3 (fun _ => e / T.η₃) (supportedOn F r) F V 1 η hst.coupling_le le_rfl (by norm_num) (fun _ => h0)
    (hasBoundedDerivatives_supportedOn h1 le_rfl h0 hr.decaying) hst.torus hst.small_curvature zero_le_one le_rfl hη
private theorem centredExpansion_jointlySmooth {a ρA κ δ C₀ ρ : ℝ} {Ck : ℕ → ℝ} {L m : ℕ} {e : ℕ → ℝ} {h : LocalFamily}
    {V : F.GaugeField F.top}
    (hT : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → IsTransportBounded 1 a ρA κ δ C₀ Ck L m 3 e h V η)
    (y : F.Site F.depth) : JointlyContDiffOnBalls ρ V (centredExpansion false a ρA m h y) := by apply _root_.YangMills.SharedProofs.p47465 <;> assumption
set_option maxHeartbeats 1600000 in
private theorem bounds_at {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {C₀ W Cw Cn : ℝ} {Ck Cm Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hTD : fieldDerivRegularityStatement) (hMC : CutoffExpectationIsPositiveForm)
    (hMD : meanFieldDerivNearValueStatement) (hb : SiteDecomposition)
    (hFew : cellBondsCardStatement) (hD : T.IsOrdered) (hL : 16 ≤ T.L) (hn : 2 ≤ T.n₀) (hy : 1 ≤ T.coupling)
    (hC₀ : 0 < C₀) (hW0 : 0 ≤ W)
    (hWs : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * T.L ^ 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (y b) z : ℝ))) ≤ W)
    (hCw : ∀ u : ℝ, 0 ≤ u → torusDecayFactor T.L T.decayRate u ≤ Cw * Real.exp (2 * T.decayRate * u))
    (hTr : TransportBoundsAt T C₀ Ck)
    (hFB : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cm Cz Cr t x)
    (hA : (T.L : ℝ) ^ 4 * (C₀ * (1 + Cw)) ≤ Cn)
    (hB : (T.L : ℝ) ^ 4 * C₀ * W * (1 + |Cm 1|) ≤ Cn) :
    BlockSumDerivBoundAt T Cn ∧ BlockSumNearValueAt T Cn := by
  classical
  have hκ := hD.κ_pos
  have hη₃ := hD.η₃_pos
  have hLp : (0 : ℝ) ≤ (T.L : ℝ) ^ 4 := by positivity
  refine ⟨fun t x e f F V r Y η k c X hst he hr hη h1 h3 hX => ?_,
    fun t x e f F V r Y k c X hst _ he hr hk hX => ?_⟩
  · obtain ⟨hFL, -, n, hsn, hnn⟩ := hst.torus
    have hodd : Odd F.blockSide := by
      rw [hFL]
      exact hD.odd_L
    have hside : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hsn i]
      omega
    have he0 : 0 ≤ e / T.η₃ := (div_pos he hη₃).le
    have hT : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ T.ballRadius) →
        IsTransportBounded 1 T.a T.chainParams.ρA T.κ T.decayRate C₀ Ck T.L (frameRadius x) 3 (fun _ => e / T.η₃)
          (supportedOn F r) V ζ :=
      fun ζ hζ => transportBounded_supportedOn hD hTr hst he hr hζ
    have hrows := centredExpansion_jointlySmooth hT
    obtain ⟨s, hs0, hs⟩ := bondDeriv_blockSum (coldHalfLawAt T x f) r Y V c X
    set S := (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y with hS
    have hs' : bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X =
        fieldDeriv (cellExpansionInField false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) Y) V c X η + s :=
      hs η
    have hsum : fieldDeriv (cellExpansionInField false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) Y) V c X η =
        ∑ y ∈ S, fieldDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) V c X η :=
      (hTD F T.ballRadius V).sum _ S
        (fun y => centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) k c X η
        (fun y _ => hrows y) h3 hη
    rw [hs', hs0 h1, add_zero, hsum]
    set G := torusDecayFactor T.L T.decayRate (bondSpan Y c) with hG
    have hGp : 0 < G := decayFactor_pos _ _ _
    have hCw0 : 0 ≤ 1 + Cw := by
      have := decayFactor_inv_add_exp_le hκ hL hCw 0
      by_contra h
      push Not at h
      have h4 : (1 + Cw) / torusDecayFactor T.L T.decayRate ((0 : ℕ) : ℝ) < 0 :=
        div_neg_of_neg_of_pos h (decayFactor_pos _ _ _)
      have h5 : 0 < (torusDecayFactor T.L T.decayRate ((T.L : ℝ) * ((0 : ℕ) : ℝ) / 16))⁻¹ +
          Real.exp (-(2 ^ 6 * T.κ * ((0 : ℕ) : ℝ))) :=
        add_pos (inv_pos.mpr (decayFactor_pos _ _ _)) (Real.exp_pos _)
      linarith
    have hq : 0 ≤ C₀ * (e / T.η₃) * ((1 + Cw) / G) :=
      mul_nonneg (mul_nonneg hC₀.le he0) (div_nonneg hCw0 hGp.le)
    have hterm : ∀ y ∈ S,
        |fieldDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) V c X η| ≤
          C₀ * (e / T.η₃) * ((1 + Cw) / G) := fun y hy => by
      have hyY : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
      have h2 := (hT η hη).decay y k c X h1 h3 hX
      rw [hyY] at h2
      have e1 : centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y η =
          interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y η :=
        funext fun V' => (interpolatedExpansion_one _ _ _ _ _ _ _).symm
      have e2 : fieldDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) V c X η =
          bondDeriv (interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y η) V c X := by
        simp only [fieldDeriv, e1]
      rw [e2]
      refine h2.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (runningMax_const_le he0 k) hC₀.le)
        (decayFactor_inv_add_exp_le hκ hL hCw _)
        (add_nonneg (inv_pos.mpr (decayFactor_pos _ _ _)).le (Real.exp_pos _).le)
        (mul_nonneg hC₀.le he0)
    have hcard : (S.card : ℝ) ≤ (T.L : ℝ) ^ 4 := by
      have := blockSites_card hb hodd hside Y
      rw [hFL] at this
      exact_mod_cast this
    calc |∑ y ∈ S, fieldDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) V c X η|
        ≤ ∑ y ∈ S, |fieldDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) V c X η| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (S.card : ℝ) * (C₀ * (e / T.η₃) * ((1 + Cw) / G)) := by
          have := Finset.sum_le_card_nsmul S _ _ hterm
          rwa [nsmul_eq_mul] at this
      _ ≤ (T.L : ℝ) ^ 4 * (C₀ * (e / T.η₃) * ((1 + Cw) / G)) := mul_le_mul_of_nonneg_right hcard hq
      _ = (T.L : ℝ) ^ 4 * (C₀ * (1 + Cw)) * (e / T.η₃) / G := by ring
      _ ≤ Cn * (e / T.η₃) / G :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA he0) hGp.le
  · obtain ⟨hFL, -, n, hsn, hnn⟩ := hst.torus
    have hodd : Odd F.blockSide := by
      rw [hFL]
      exact hD.odd_L
    have hside : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hsn i]
      omega
    have he0 : 0 ≤ e / T.η₃ := (div_pos he hη₃).le
    have hx : 0 < x := by
      have := hst.coupling_le
      linarith
    have hρ : 0 < T.ballRadius := by
      have := hD.σ_pos
      show 0 < T.σ / 64
      positivity
    have hT : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ T.ballRadius) →
        IsTransportBounded 1 T.a T.chainParams.ρA T.κ T.decayRate C₀ Ck T.L (frameRadius x) 3 (fun _ => e / T.η₃)
          (supportedOn F r) V ζ :=
      fun ζ hζ => transportBounded_supportedOn hD hTr hst he hr hζ
    have hrows := centredExpansion_jointlySmooth hT
    let Mw : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V ((coldHalfLawAt T x f).exponent V)
    have hadm : Mw.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
        T.n₀ (frameRadius x) (chordBondDist F) :=
      ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
        Function.injective_id, fun _ _ => rfl⟩
    obtain ⟨hconv, hlaw, -⟩ := (hFB t x hst.coupling_le).laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => Mw)
      ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
    rw [convexCombinationExponent_lawAtTop] at hconv hlaw
    obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
    have Fm : IsPositiveUnitalForm T.ballRadius T.p Ψ' :=
      hMC _ T.ballRadius T.p Ψ' hρ hD.cutoff hconvex.smooth.continuous
    have hmom : ∀ b : ↥(chordBonds (finiteCells F)),
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ' (fun η => ‖η b‖ ^ 2) ≤ |Cm 1| * x⁻¹ := fun b => by
      rw [Fm.congr_potential ((coldHalfLawAt T x f).exponent V) (fun η => ‖η b‖ ^ 2) (fun η hη => hΨ' η hη)]
      have h := hlaw.moments 1 b
      simp only [mul_one, pow_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hx.le))
    have hWsum : ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ W :=
      hWs F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z => by
        have := hFew F hodd hside z
        rwa [hFL] at this) Y
    have hcard : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
        (T.L : ℝ) ^ 4 := by
      have := blockSites_card hb hodd hside Y
      rw [hFL] at this
      exact_mod_cast this
    have hgrad : ∀ (y : F.Site F.depth) (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
        (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        (∀ b, ‖ζ b‖ ≤ T.ballRadius) → ‖u‖ = 1 → k ≤ 2 → AreUnitVectors X →
        |jointMixedDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y) ζ V ![b] ![u] c X| ≤
          C₀ * (e / T.η₃) * Real.exp (-(2 ^ 7 * T.κ *
            cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c)))) := by
      intro y ζ b u k c X hζ hu hk hX
      have e1 : centredExpansion false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y =
          interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) y :=
        funext fun η => funext fun V' => (interpolatedExpansion_one _ _ _ _ _ _ _).symm
      rw [e1]
      have h2 := (hT ζ hζ).jointDeriv_le y 1 k ![b] ![u] c X (by omega) (by omega)
        (fun i => by
          fin_cases i
          simpa using hu) hX
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (runningMax_const_le he0 _) hC₀.le)
        (Real.exp_pos _).le
    set t₀ : ℝ := x ^ (-(1 / 2) : ℝ) with ht₀
    have ht : 0 < t₀ := Real.rpow_pos_of_pos hx _
    have hmain := hMD F false T.a T.chainParams.ρA (frameRadius x) T.ballRadius T.κ C₀ (e / T.η₃) W ((T.L : ℝ) ^ 4)
      (|Cm 1| * x⁻¹) t₀ T.p Ψ' (supportedOn F r) V Y hρ hκ hC₀.le he0 ht hW0 hLp (by positivity)
      hrows Fm hgrad hmom hWsum hcard k c X hk hX
    set g := fieldDeriv (cellExpansionInField false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) Y) V c X with hg
    have hHJ : JointlyContDiffOnBalls T.ballRadius V
        (cellExpansionInField false T.a T.chainParams.ρA (frameRadius x) (supportedOn F r) Y) :=
      fun j c' X' η hη => ContDiffAt.sum fun y _ => hrows y j c' X' η hη
    have hk3 : k ≤ 3 := by omega
    have hnice : IsBoundedContinuousOn ↥(chordBonds (finiteCells F)) T.ballRadius g := by
      obtain ⟨B, hB⟩ := (hTD F T.ballRadius V).bounded _ k c X hHJ hk3
      exact ⟨(hTD F T.ballRadius V).continuousOn _ k c X hHJ hk3, B, fun η hη => hB η fun b => (hη b).le⟩
    obtain ⟨s, -, hs⟩ := bondDeriv_blockSum (coldHalfLawAt T x f) r Y V c X
    have hs' : ∀ η, bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X = g η + s := hs
    have e1 : (coldHalfLawAt T x f).expectation V
        (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X) =
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ' g + s := by
      have e2 : (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X) = fun η => g η + s := funext hs'
      rw [e2]
      show ballExpectation (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) (fun η => g η + s) = _
      rw [← Fm.congr_potential ((coldHalfLawAt T x f).exponent V) _ (fun η hη => hΨ' η hη),
        Fm.map_add g (fun _ => s) hnice (IsBoundedContinuousOn.const s)]
      have h3 := Fm.map_smul s (fun _ => 1)
      simp only [mul_one] at h3
      rw [h3, Fm.map_one, mul_one]
    rw [e1, hs' 0]
    have e3 : ballExpectation (cutoffFactor T.ballRadius T.p) Ψ' g + s - (g 0 + s) =
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ' g - g 0 := by
      ring
    rw [e3]
    refine hmain.trans ?_
    have htt : t₀ * t₀ = x⁻¹ := by
      rw [ht₀, ← Real.rpow_add hx]
      norm_num
      exact Real.rpow_neg_one x
    have h5 : t₀ / 2 + |Cm 1| * x⁻¹ / (2 * t₀) = (1 + |Cm 1|) / 2 * t₀ := by
      rw [← htt]
      field_simp
    rw [h5]
    have hE : Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y c : ℝ) := by positivity
      linarith
    have hA0 : 0 ≤ (T.L : ℝ) ^ 4 * (C₀ * (e / T.η₃)) * W * ((1 + |Cm 1|) / 2 * t₀) := by positivity
    calc (T.L : ℝ) ^ 4 * (C₀ * (e / T.η₃)) * W * ((1 + |Cm 1|) / 2 * t₀) *
          Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ)))
        ≤ (T.L : ℝ) ^ 4 * (C₀ * (e / T.η₃)) * W * ((1 + |Cm 1|) / 2 * t₀) * 1 :=
          mul_le_mul_of_nonneg_left hE hA0
      _ = ((T.L : ℝ) ^ 4 * C₀ * W * (1 + |Cm 1|)) * (e / T.η₃) * t₀ / 2 := by ring
      _ ≤ ((T.L : ℝ) ^ 4 * C₀ * W * (1 + |Cm 1|)) * (e / T.η₃) * t₀ := by
          have : 0 ≤ ((T.L : ℝ) ^ 4 * C₀ * W * (1 + |Cm 1|)) * (e / T.η₃) * t₀ := by positivity
          linarith
      _ ≤ Cn * (e / T.η₃) * t₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB he0) ht.le
end BlockSumBound
open BlockSumBound in
theorem blockSumBound (hTr : transportBoundsStatement)
    (hFr : interpolatedFramesStatement) (hTD : fieldDerivRegularityStatement)
    (hMC : CutoffExpectationIsPositiveForm) (hMD : meanFieldDerivNearValueStatement)
    (hb : SiteDecomposition) (hFew : cellBondsCardStatement)
    (hSum : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hWE : DecayFactorExpBound)
    (hJ : EventuallyInParametersCombines) : blockSumBoundStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Ct, Ck, hCt, -, hTrT⟩ := hTr
  obtain ⟨Cm, Cz, Cr, hFrT⟩ := hFr
  have hW' : ∀ (L : ℕ) (δ : ℝ), ∃ C : ℝ, 0 < L → 0 < δ → 1 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      torusDecayFactor L δ u ≤ C * Real.exp (2 * δ * u) := fun L δ => by
    by_cases h : 0 < L ∧ 0 < δ
    · obtain ⟨C, hC⟩ := hWE L δ h.1 h.2
      exact ⟨C, fun _ _ => hC⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Cw hCw using hW'
  have hS' : ∀ (N : ℕ) (κ : ℝ), ∃ W : ℝ, 0 < κ → 0 ≤ W ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W := fun N κ => by
    by_cases h : 0 < κ
    · obtain ⟨W, hW⟩ := hSum N κ h
      exact ⟨W, fun _ => hW⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using hS'
  have floors : EventuallyInParameters fun T => 16 ≤ T.L ∧ 2 ≤ T.n₀ ∧ 1 ≤ T.coupling :=
    fun _ _ => ⟨16, fun _ _ hL _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ hn => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨hL, hn, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  let A : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => (U.L : ℝ) ^ 4 * (Ct (rateParameters U) * (1 + Cw U.L U.decayRate))
  let B : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => (U.L : ℝ) ^ 4 * Ct (rateParameters U) * Wf (4 * U.L ^ 4) (2 ^ 6 * U.κ) *
    (1 + |Cm (momentParameters U) 1|)
  refine ⟨fun U => 1 + |A U| + |B U|, fun U => by positivity, ?_⟩
  refine weaken _ _ (fun T hD h => ?_) (join _ _ hTrT (join _ _ hFrT floors))
  obtain ⟨hTrA, hFrA, hL, hn, hy⟩ := h
  have hκ := hD.κ_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hLp : 0 < T.L := by omega
  have hκ6 : 0 < 2 ^ 6 * T.κ := by positivity
  have hA : A (parametersBeforeSide T) ≤ 1 + |A (parametersBeforeSide T)| + |B (parametersBeforeSide T)| := by
    linarith [le_abs_self (A (parametersBeforeSide T)), abs_nonneg (B (parametersBeforeSide T))]
  have hB : B (parametersBeforeSide T) ≤ 1 + |A (parametersBeforeSide T)| + |B (parametersBeforeSide T)| := by
    linarith [le_abs_self (B (parametersBeforeSide T)), abs_nonneg (A (parametersBeforeSide T))]
  exact bounds_at hTD hMC hMD hb hFew hD hL hn hy (hCt _) (hWf _ _ hκ6).1 (hWf _ _ hκ6).2
    (hCw _ _ hLp hδ).2 hTrA (fun t x h => hFrA t x h) hA hB
end ResponseInTheExpansion
end YangMills.Construction
end
