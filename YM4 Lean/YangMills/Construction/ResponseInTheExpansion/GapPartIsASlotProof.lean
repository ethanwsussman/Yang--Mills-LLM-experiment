import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheRest
import YangMills.Construction.ResponseInTheExpansion.GapPartIsASlot
import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses IteratedDerivative Estimates
namespace ResponseInTheExpansion
namespace GapTerm
open RemainderCalculus
variable {F : BlockFrame}
abbrev TermIndex (F : BlockFrame) : Type := (F.Site F.top × Fin 4) ⊕ ↥(chordBonds (finiteCells F))
def term (a ρA x : ℝ) (m : ℕ) : TermIndex F → AboveFrames F :=
  Sum.elim (fun c => contourHaarGap 1 a ρA x m c) (fun b => interpolatedHaarLogRatio 1 a ρA m b)
def termCell : TermIndex F → F.Cell := Sum.elim (fun c => c.1) (fun b => enclosingCell b.1.1)
def termIndices (F : BlockFrame) : Finset (TermIndex F) := (innerBonds (finiteCells F) F.top).disjSum Finset.univ
def termSum (a ρA x : ℝ) (m : ℕ) : AboveFrames F := fun η V => ∑ j ∈ termIndices F, term a ρA x m j η V
theorem gapHaarExcess_eq_termSum_sub (Q : ColdHalfLaw) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.gapHaarExcess η V = termSum Q.a Q.chartRadius Q.coupling Q.mirrorRadius η V -
      ((innerBonds (finiteCells F) F.top).card : ℝ) * haarGap (Q.a * Q.coupling) := by
  unfold termSum termIndices
  rw [Finset.sum_disjSum]
  simp only [term, Sum.elim_inl, Sum.elim_inr]
  unfold ColdHalfLaw.gapHaarExcess haarGapExcess contourHaarGap interpolatedHaarLogRatio
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring
theorem gapTerm_eq_dilation (Q : ColdHalfLaw) (Y : F.Cell) :
    Q.gapTerm Y = dilation (cellChordBonds Y) (termSum Q.a Q.chartRadius Q.coupling Q.mirrorRadius) := by
  classical
  funext η V
  unfold ColdHalfLaw.gapTerm ColdHalfLaw.sumOverBlock dilation cellChordBonds
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · unfold bondPartialDeriv
    have e : (fun ζ => Q.gapHaarExcess ζ V) = fun ζ => termSum Q.a Q.chartRadius Q.coupling Q.mirrorRadius ζ V -
        ((innerBonds (finiteCells F) F.top).card : ℝ) * haarGap (Q.a * Q.coupling) :=
      funext fun ζ => gapHaarExcess_eq_termSum_sub Q ζ V
    rw [e, fderiv_sub_const]
  · rfl
theorem exp_le_mul_exp_of_le {κ n s d : ℝ} (hκ : 0 ≤ κ) (hs : s ≤ n) (hd : d ≤ n) (hs0 : 0 ≤ s) (hd0 : 0 ≤ d) :
    Real.exp (-(2 ^ 8 * κ * n)) ≤ Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(κ * d)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : κ * s ≤ κ * n := mul_le_mul_of_nonneg_left hs hκ
  have h2 : κ * d ≤ κ * n := mul_le_mul_of_nonneg_left hd hκ
  nlinarith [mul_nonneg hκ hs0, mul_nonneg hκ hd0]
theorem exp_le_mul_mul_exp_of_le {κ n s d d' : ℝ} (hκ : 0 ≤ κ) (hs : s ≤ n) (hd : d ≤ n) (hd' : d' ≤ n)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d) (hd'0 : 0 ≤ d') :
    Real.exp (-(2 ^ 8 * κ * n)) ≤
      Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 * κ * d)) * Real.exp (-(κ * d')) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 : κ * s ≤ κ * n := mul_le_mul_of_nonneg_left hs hκ
  have h2 : κ * d ≤ κ * n := mul_le_mul_of_nonneg_left hd hκ
  have h3 : κ * d' ≤ κ * n := mul_le_mul_of_nonneg_left hd' hκ
  nlinarith [mul_nonneg hκ hs0, mul_nonneg hκ hd0, mul_nonneg hκ hd'0]
theorem term_hasDecayingKernelAt {a ρA κ κ₂ rE x : ℝ} {m : ℕ} {Kf : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)}
    (hk : HasInterpolationKernels 1 a ρA κ κ₂ rE x m Kf D V η) (j : TermIndex F) (l i : ℕ)
    (b : Fin l → ↥(chordBonds (finiteCells F))) (w : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin i → F.Site F.top × Fin 4) (X : Fin i → imaginaryQuaternions) (hli : 1 ≤ l + i)
    (hw : ∀ i, ‖w i‖ = 1) (hX : AreUnitVectors X) :
    HasDecayingKernelAt (term a ρA x m j) (D l i) (2 ^ 8 * κ) {termCell j} η V b w c X := by
  rcases j with c₀ | b₀
  · exact hk.gap c₀ l i b w c X hli hw hX
  · exact hk.haar b₀ l i b w c X hli hw hX
theorem sum_exp_termCell_le {κ W₁ S₀ : ℝ} (Y : F.Cell)
    (h₁ : ∑ c : ↥(innerBonds (finiteCells F) F.top), Real.exp (-(κ * (cellSupDist c.1.1 Y : ℝ))) ≤ W₁)
    (h₂ : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ S₀) :
    ∑ j ∈ termIndices F, Real.exp (-(κ * (cellSupDist (termCell j) Y : ℝ))) ≤ W₁ + S₀ := by
  unfold termIndices
  rw [Finset.sum_disjSum]
  simp only [termCell, Sum.elim_inl, Sum.elim_inr]
  have e := Finset.sum_coe_sort (innerBonds (finiteCells F) F.top)
    fun c => Real.exp (-(κ * (cellSupDist c.1 Y : ℝ)))
  rw [← e]
  exact add_le_add h₁ h₂
end GapTerm
open GapTerm RemainderCalculus in
theorem gapTermSecondOrder_holds (hPB : remainderOfBoundsStatement)
    (hKern : interpolationKernelBoundsStatement)
    (hJS : JointlyContDiffOnBallsOfDisplacements) (hL : DerivAlongRulesHold)
    (hAl : JointMixedDerivEqDerivAlong) (hTwo : Calculus.IteratedFDerivParamDiff)
    (hSl : SmoothSlices.IteratedFDerivSlices) (hSum : CellCounting.ExpDecaySumBounded)
    (hFew : cellBondsCardStatement) (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel)
    (hJ : EventuallyInParametersCombines) : gapTermSecondOrderStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Kf, Dk, hKf, hDk, hKT⟩ := hKern
  choose! Wf hWf0 hWf using hSum
  let A₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U =>
    lowOrderSum (Dk (rateParameters U)) * (Wf 4 U.κ + Wf (4 * U.L ^ 4) U.κ)
  let At : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => |A₀ U * (1 + U.ballRadius * Wf (4 * U.L ^ 4) U.κ)|
  obtain ⟨Cq, C, hCq, hC', hPT⟩ := hPB At fun T => abs_nonneg _
  refine ⟨Cq, C, hCq, hC', ?_⟩
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hPT (join _ _ hKT h64))
  rintro T hDr ⟨hPBT, hKTT, h64', hy1⟩
  intro t x f F V Y hst hrow
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx : 0 < x := by linarith
  set Q := coldHalfLawAt T x f with hQ
  set U := parametersBeforeSide T with hU
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have htor := hst.torus
  obtain ⟨hLF, htt, n, hside, hn⟩ := htor
  have hnpos : 64 ≤ n := h64'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hne := nonempty_chordBonds hB hC hoddF hs2
  have hN : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
        4 * U.L ^ 4 := fun z => by
    have := hFew F hoddF hs2 z
    rwa [hLF] at this
  have hS₀ : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ Wf (4 * U.L ^ 4) U.κ :=
    hWf _ _ hκ F ↥(chordBonds (finiteCells F))
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) hN Y
  have hN₄ : ∀ z : F.Cell,
      (Finset.univ.filter fun c : ↥(innerBonds (finiteCells F) F.top) => c.1.1 = z).card ≤ 4 := fun z => by
    have := Finset.card_le_card_of_injOn
      (s := Finset.univ.filter fun c : ↥(innerBonds (finiteCells F) F.top) => c.1.1 = z)
      (t := (Finset.univ : Finset (Fin 4))) (fun c => c.1.2) (fun _ _ => by simp) (by
        intro c hc c' hc' h
        have h1 : c.1.1 = z := by simpa using hc
        have h2 : c'.1.1 = z := by simpa using hc'
        exact Subtype.ext (Prod.ext (h1.trans h2.symm) h))
    simpa using this
  have hW₁ : ∑ c : ↥(innerBonds (finiteCells F) F.top),
      Real.exp (-(T.κ * (cellSupDist c.1.1 Y : ℝ))) ≤ Wf 4 U.κ :=
    hWf 4 _ hκ F ↥(innerBonds (finiteCells F) F.top)
      (fun c : ↥(innerBonds (finiteCells F) F.top) => c.1.1) hN₄ Y
  have hUo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  set Dl := Dk (rateParameters T) with hDl
  have hk : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        (Kf (rateParameters T)) Dl V η :=
    fun η hη => hKTT x t F V 1 η hfl hst.torus hst.small_curvature zero_le_one le_rfl hη
  set P := term (F := F) T.a T.chainParams.ρA x (frameRadius x) with hP
  set G := termSum (F := F) T.a T.chainParams.ρA x (frameRadius x) with hG
  have hread : ∀ (j : TermIndex F) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      AreUnitVectors X → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ∀ m : ℕ,
      ContDiffAt ℝ (m : WithTop ℕ∞) (rotatedEval (P j) V c X) (η, 0) := fun j k c X hX η hη m =>
    (hAl F V _ η k c X).1 hne
      (fun l b w hl hw => (term_hasDecayingKernelAt (hk η hη) j l k b w c X (by omega) hw hX).1) m
  have hjs : ∀ j : TermIndex F, JointlyContDiffOnBalls T.ballRadius V (P j) := fun j =>
    hJS F T.ballRadius V _ fun η hη l i b w c X hw hX =>
      jointDisplacement_contDiffAt b w c X (hread j i c X hX η hη 3)
  have hwhole : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)),
      (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, η) := fun k c X η hη =>
    ContDiffAt.sum fun j _ => hjs j k c X η hη
  set Dm := lowOrderSum Dl with hDm
  have hDm0 : 0 ≤ Dm := lowOrderSum_nonneg (hDk _)
  have hself : ∀ a : F.Cell, cellSupDist a a = 0 := fun a => by simp [cellSupDist]
  have hbound : ∀ {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (w : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ l → l ≤ 2 → k ≤ 2 →
      (∀ i, ‖w i‖ = 1) → AreUnitVectors X →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      |jointMixedDeriv G η V b w c X| ≤ Dm * ∑ j ∈ termIndices F, Real.exp (-(2 ^ 8 * T.κ *
        cellSetDiameter ({termCell j} ∪ chordBondCells b ∪ topBondCells c))) := by
    intro l k b w c X hl1 hl2 hk2 hw hX η hη
    have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    have e := jointMixedDeriv_finset_sum (termIndices F) P (V := V) (η := η) b w c X fun j _ =>
      (term_hasDecayingKernelAt (hk η hη') j l k b w c X (by omega) hw hX).1
    have e' : jointMixedDeriv G η V b w c X = ∑ j ∈ termIndices F, jointMixedDeriv (P j) η V b w c X := e
    rw [e', Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 := (term_hasDecayingKernelAt (hk η hη') j l k b w c X (by omega) hw hX).2
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (le_lowOrderSum (hDk _) l k (by omega) (by omega)) (Real.exp_pos _).le
  have hplace : ∑ j ∈ termIndices F, Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ))) ≤
      Wf 4 U.κ + Wf (4 * U.L ^ 4) U.κ :=
    sum_exp_termCell_le Y hW₁ hS₀
  set Wt := Wf 4 U.κ + Wf (4 * U.L ^ 4) U.κ with hWt
  have hdil : HasDilationBounds T (Dm * Wt) Y (cellChordBonds Y) G V := by
    refine ⟨hwhole, fun k c X hk2 hX η hη b hb e => ?_, fun k c X hk1 hX η hη b hb b₀ e e' => ?_⟩
    · have hbY : enclosingCell b.1.1 = Y := by simpa [cellChordBonds] using hb
      have h33 : ContDiffAt ℝ 3 (rotatedEval G V c X) (η, 0) :=
        rotatedEval_contDiffAt (hwhole k c X η fun b => (hη b).le)
      have hs : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) :=
        h33.of_le (by exact_mod_cast (by omega : k + 1 ≤ 3))
      have hfin := abs_fderiv_bondDeriv_le hL hAl hs b
        (B := Dm * Wt * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))) (fun w hw => ?_) e
      · rw [hbY, hself]
        simpa using hfin
      · refine (hbound ![b] ![w] c X le_rfl (by norm_num) hk2 (fun i => by fin_cases i; exact hw) hX η hη).trans ?_
        have hterm : ∀ j ∈ termIndices F, Real.exp (-(2 ^ 8 * T.κ *
            cellSetDiameter ({termCell j} ∪ chordBondCells ![b] ∪ topBondCells c))) ≤
            Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) * Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ))) := by
          intro j _
          set R := ({termCell j} ∪ chordBondCells ![b] ∪ topBondCells c : Finset F.Cell) with hR
          have m1 : Y ∈ R := by
            rw [hR]
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, hbY⟩
          have m2 : termCell j ∈ R := by
            rw [hR]
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
          have m3 : ∀ l, (c l).1 ∈ R := fun l => by
            rw [hR]
            exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
          have h1 : (bondSpan Y c : ℝ) ≤ cellSetDiameter R := by
            exact_mod_cast bondSpan_le_cellSetDiameter m1 m3
          have h2 : (cellSupDist (termCell j) Y : ℝ) ≤ cellSetDiameter R := by
            exact_mod_cast cellSupDist_le_cellSetDiameter m2 m1
          exact exp_le_mul_exp_of_le hκ.le h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hE0 := (Real.exp_pos (-(2 ^ 5 * T.κ * bondSpan Y c))).le
        calc Dm * ∑ j ∈ termIndices F, Real.exp (-(2 ^ 8 * T.κ *
              cellSetDiameter ({termCell j} ∪ chordBondCells ![b] ∪ topBondCells c)))
            ≤ Dm * ∑ j ∈ termIndices F, Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
                Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hDm0
          _ = Dm * (∑ j ∈ termIndices F, Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ)))) *
                Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) := by
              rw [← Finset.mul_sum]
              ring
          _ ≤ Dm * Wt * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hplace hDm0) hE0
    · have hbY : enclosingCell b.1.1 = Y := by simpa [cellChordBonds] using hb
      have h33 : ContDiffAt ℝ 3 (rotatedEval G V c X) (η, 0) :=
        rotatedEval_contDiffAt (hwhole k c X η fun b => (hη b).le)
      have hs : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) :=
        h33.of_le (by exact_mod_cast (by omega : k + 2 ≤ 3))
      have hfin := abs_fderiv_fderiv_bondDeriv_le hL hAl hs b b₀
        (B := Dm * Wt * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
          Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ)))) (fun w w' hw hw' => ?_) e e'
      · rw [hbY, hself]
        simpa using hfin
      · refine (hbound ![b₀, b] ![w', w] c X (by norm_num) le_rfl (by omega)
          (fun i => by fin_cases i; exacts [hw', hw]) hX η hη).trans ?_
        have hterm : ∀ j ∈ termIndices F, Real.exp (-(2 ^ 8 * T.κ *
            cellSetDiameter ({termCell j} ∪ chordBondCells ![b₀, b] ∪ topBondCells c))) ≤
            Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
              Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
              Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ))) := by
          intro j _
          set R := ({termCell j} ∪ chordBondCells ![b₀, b] ∪ topBondCells c : Finset F.Cell) with hR
          have m1 : Y ∈ R := by
            rw [hR]
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_image.2 ⟨1, Finset.mem_univ _, hbY⟩
          have m0 : enclosingCell b₀.1.1 ∈ R := by
            rw [hR]
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
          have m2 : termCell j ∈ R := by
            rw [hR]
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
          have m3 : ∀ l, (c l).1 ∈ R := fun l => by
            rw [hR]
            exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
          have h1 : (bondSpan Y c : ℝ) ≤ cellSetDiameter R := by
            exact_mod_cast bondSpan_le_cellSetDiameter m1 m3
          have h0 : (cellSupDist (enclosingCell b₀.1.1) Y : ℝ) ≤ cellSetDiameter R := by
            exact_mod_cast cellSupDist_le_cellSetDiameter m0 m1
          have h2 : (cellSupDist (termCell j) Y : ℝ) ≤ cellSetDiameter R := by
            exact_mod_cast cellSupDist_le_cellSetDiameter m2 m1
          exact exp_le_mul_mul_exp_of_le hκ.le h1 h0 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hE0 := (Real.exp_pos (-(2 ^ 5 * T.κ * bondSpan Y c))).le
        calc Dm * ∑ j ∈ termIndices F, Real.exp (-(2 ^ 8 * T.κ *
              cellSetDiameter ({termCell j} ∪ chordBondCells ![b₀, b] ∪ topBondCells c)))
            ≤ Dm * ∑ j ∈ termIndices F, Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
                Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
                Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hDm0
          _ = Dm * (∑ j ∈ termIndices F, Real.exp (-(T.κ * (cellSupDist (termCell j) Y : ℝ)))) *
                (Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
                  Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ)))) := by
              rw [← Finset.mul_sum]
              ring
          _ ≤ Dm * Wt * (Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
                Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ)))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hplace hDm0) (by positivity)
          _ = _ := by ring
  have hWt0 : 0 ≤ Wt := add_nonneg (hWf0 _ _ hκ) (hWf0 _ _ hκ)
  have hfin : WeightedResponses.HasRemainderBounds T x (At U) Y (Q.gapTerm Y) V := by
    rw [gapTerm_eq_dilation]
    exact RemainderCalculus.HasRemainderBounds.mono hx.le (le_abs_self _)
      ((hdil.hasRemainderBounds hTwo hSl hx.le (by positivity) hκ.le hρ.le hUo hS₀))
  exact hPBT t x f F V Y _ hst hfin
end ResponseInTheExpansion
end YangMills.Construction
end
