import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace LevelFieldLocality
open Tower TorusMetric Matrices
section MatrixBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_matInv {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x)
    (hu : IsUnit (Matrix.det (f x))) : AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
private theorem norm_inv_sub_one_le {M : ComplexMatrix2} (hM : Matrix.det M = 1)
    (h : ‖M - 1‖ ≤ 1 / 2) : ‖M⁻¹ - 1‖ ≤ 2 * ‖M - 1‖ := by apply _root_.YangMills.SharedProofs.p71492 <;> assumption
private theorem norm_mul_sub_one_le {A B : ComplexMatrix2} {s t : ℝ} (hA : ‖A - 1‖ ≤ s)
    (hB : ‖B - 1‖ ≤ t) (hB' : ‖B - 1‖ ≤ 1 / 2) : ‖A * B - 1‖ ≤ 3 / 2 * s + t := by apply _root_.YangMills.SharedProofs.p8624 <;> assumption
private theorem norm_sub_le_of_analyticOn_ball {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {ρ B : ℝ} (hρ : 0 < ρ) (hf : AnalyticOnNhd ℂ f (ball 0 ρ))
    (hB : ∀ w ∈ ball (0 : E) ρ, ‖f w - f 0‖ ≤ B) {w : E} (hw : w ∈ ball (0 : E) ρ) :
    ‖f w - f 0‖ ≤ B / ρ * ‖w‖ := by
  by_cases h0 : w = 0
  · subst h0
    simp
  have hn : 0 < ‖w‖ := norm_pos_iff.2 h0
  set u : E := ((‖w‖ : ℂ)⁻¹) • w with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hmap : ∀ t ∈ ball (0 : ℂ) ρ, t • u ∈ ball (0 : E) ρ := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rwa [norm_smul, hu, mul_one]
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (t • u)) (ball 0 ρ) := by
    intro t ht
    have h1 : DifferentiableAt ℂ f (t • u) := (hf _ (hmap t ht)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun t : ℂ => t • u) t := differentiableAt_id.smul_const u
    exact (DifferentiableAt.comp t h1 h2).differentiableWithinAt
  have hm : Set.MapsTo (fun t : ℂ => f (t • u)) (ball 0 ρ)
      (closedBall ((fun t : ℂ => f (t • u)) 0) B) := by
    intro t ht
    simp only [zero_smul]
    rw [mem_closedBall, dist_eq_norm]
    exact hB _ (hmap t ht)
  have hwt : ((‖w‖ : ℝ) : ℂ) ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, Complex.norm_real, norm_norm]
    exact mem_ball_zero_iff.1 hw
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hm hwt
  have e1 : ((‖w‖ : ℝ) : ℂ) • u = w := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  simp only [e1, zero_smul, dist_eq_norm, sub_zero, Complex.norm_real, norm_norm] at key
  exact key
end MatrixBounds
section LevelBounds
variable {L n k : ℕ}
private def MeanFacts (L : ℕ) (ρ : ℝ) : Prop :=
  ∀ n k m : ℕ, 0 < n → m < k → ∀ [Fintype (Edge L n k m)],
    ∀ V ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup,
      (∀ b, ‖V b - 1‖ < ρ) → ∀ c : Edge L n k (m + 1), c.IsPositivelyOriented →
        ‖meanRadius V c - 1‖ < 1 / 2 ∧ ‖normalizedMean V c - 1‖ < 1 / 2 ∧
        normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
        AnalyticAt ℂ (fun V' : Edge L n k m → ComplexMatrix2 => meanRadius V' c) V ∧
        AnalyticAt ℂ (fun V' : Edge L n k m → ComplexMatrix2 => normalizedMean V' c) V
private theorem exists_meanFacts (hA : NormalizedMeanAnalytic) (hN : NormalizedMeanNearOne)
    (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ ρ : ℝ, 0 < ρ ∧ MeanFacts L ρ := by
  obtain ⟨ρ₁, h₁, A⟩ := hA L hL
  obtain ⟨ρ₂, h₂, N⟩ := hN L hL
  refine ⟨min ρ₁ ρ₂, lt_min h₁ h₂, ?_⟩
  intro n k m hn hm _ V hV hs c hc
  obtain ⟨-, a₁, a₂, a₃, -⟩ :=
    N n k m hn hm V hV (fun b => (hs b).trans_le (min_le_right _ _)) c hc
  obtain ⟨b₁, b₂⟩ := A n k m hn hm V hV (fun b => (hs b).trans_le (min_le_left _ _)) c hc
  exact ⟨a₁, a₂, a₃, b₁, b₂⟩
private theorem levelField_pos (X : ChainPoint L n k) {m : ℕ} (h : m < k)
    {b : Edge L n k (m + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (m + 1) b = X.noise ⟨m, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X m) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_neg (X : ChainPoint L n k) {m : ℕ} (h : m < k)
    {b : Edge L n k (m + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (m + 1) b = (levelField X (m + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
private theorem levelField_succ_mem (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (X : ChainPoint L n k) {m : ℕ} (h : m < k)
    (hp : ∀ b : Edge L n k (m + 1), b.IsPositivelyOriented →
      Matrix.det (levelField X (m + 1) b) = 1) :
    levelField X (m + 1) ∈ fieldsIn L n k (m + 1) PeriodicLattice.complexGaugeGroup := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hx : ∀ b : Edge L n k (m + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have inv_inv' : ∀ {M : ComplexMatrix2}, Matrix.det M = 1 → (M⁻¹)⁻¹ = M := fun {M} hM =>
    Matrix.nonsing_inv_nonsing_inv _ (by rw [hM]; exact isUnit_one)
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · show Matrix.det _ = 1
    by_cases hb : b.IsPositivelyOriented
    · exact hp b hb
    · rw [levelField_neg X h hb, Matrix.det_nonsing_inv,
        hp _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · have hr : ¬b.opposite.IsPositivelyOriented := by
        rcases hx b with ⟨_, h₂⟩ | h₂
        · exact h₂
        · exact absurd hb h₂.2
      have e : b.opposite.opposite = b := by
        ext <;> rfl
      have := levelField_neg X h hr
      rwa [e] at this
    · rw [levelField_neg X h hb,
        inv_inv' (hp _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb))]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private structure IsSmallFamily (X : E → ChainPoint L n k) (ρ C : ℝ) : Prop where
  zero : X 0 = unitPoint L n k
  mem : ∀ w ∈ ball (0 : E) ρ, (X w).fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup
  fine_analytic : ∀ b, AnalyticOnNhd ℂ (fun w => (X w).fine b) (ball 0 ρ)
  fine_near : ∀ w ∈ ball (0 : E) ρ, ∀ b, ‖(X w).fine b - 1‖ ≤ C * ‖w‖
  noise_det : ∀ w ∈ ball (0 : E) ρ, ∀ i c, Matrix.det ((X w).noise i c) = 1
  noise_analytic : ∀ i c, AnalyticOnNhd ℂ (fun w => (X w).noise i c) (ball 0 ρ)
  noise_near : ∀ w ∈ ball (0 : E) ρ, ∀ i c, ‖(X w).noise i c - 1‖ ≤ C * ‖w‖
private structure LevelBound (X : E → ChainPoint L n k) (ρ C : ℝ) (m : ℕ) : Prop where
  one : levelField (X 0) m = fun _ => 1
  mem : ∀ w ∈ ball (0 : E) ρ, levelField (X w) m ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup
  analytic : ∀ b, AnalyticOnNhd ℂ (fun w => levelField (X w) m b) (ball 0 ρ)
  near : ∀ w ∈ ball (0 : E) ρ, ∀ b, ‖levelField (X w) m b - 1‖ ≤ C * ‖w‖
private structure RadiusBound (X : E → ChainPoint L n k) (ρ C : ℝ) (i : Fin k) : Prop where
  analytic : ∀ c : PositiveEdge L n k (i + 1),
    AnalyticOnNhd ℂ (fun w => meanRadius (levelField (X w) i) c.1) (ball 0 ρ)
  near : ∀ w ∈ ball (0 : E) ρ, ∀ c : PositiveEdge L n k (i + 1),
    ‖meanRadius (levelField (X w) i) c.1 - 1‖ ≤ C * ‖w‖
private theorem LevelBound.mono {X : E → ChainPoint L n k} {ρ C ρ' C' : ℝ} {m : ℕ}
    (h : LevelBound X ρ C m) (hρ : ρ' ≤ ρ) (hC : C ≤ C') : LevelBound X ρ' C' m := by
  have s := ball_subset_ball (x := (0 : E)) hρ
  exact ⟨h.one, fun w hw => h.mem w (s hw), fun b => (h.analytic b).mono s, fun w hw b =>
    (h.near w (s hw) b).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))⟩
private theorem RadiusBound.mono {X : E → ChainPoint L n k} {ρ C ρ' C' : ℝ} {i : Fin k}
    (h : RadiusBound X ρ C i) (hρ : ρ' ≤ ρ) (hC : C ≤ C') : RadiusBound X ρ' C' i := by
  have s := ball_subset_ball (x := (0 : E)) hρ
  exact ⟨fun c => (h.analytic c).mono s, fun w hw c =>
    (h.near w (s hw) c).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))⟩
private theorem mean_along_family {ρL ρ : ℝ} (hP : MeanFacts L ρL)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hD : NormalizedMeanAtOne) (hn : 0 < n)
    {m : ℕ} (hm : m < k) (hρ : 0 < ρ) {V : E → Edge L n k m → ComplexMatrix2}
    (hc : ∀ w ∈ ball (0 : E) ρ, V w ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup)
    (ha : ∀ b, AnalyticOnNhd ℂ (fun w => V w b) (ball 0 ρ))
    (hs : ∀ w ∈ ball (0 : E) ρ, ∀ b, ‖V w b - 1‖ < ρL) (h₁ : V 0 = fun _ => 1)
    {c : Edge L n k (m + 1)} (hcp : c.IsPositivelyOriented) :
    AnalyticOnNhd ℂ (fun w => meanRadius (V w) c) (ball 0 ρ) ∧
      AnalyticOnNhd ℂ (fun w => normalizedMean (V w) c) (ball 0 ρ) ∧
      ∀ w ∈ ball (0 : E) ρ, ‖meanRadius (V w) c - 1‖ ≤ 1 / 2 / ρ * ‖w‖ ∧
        ‖normalizedMean (V w) c - 1‖ ≤ 1 / 2 / ρ * ‖w‖ ∧ ‖normalizedMean (V w) c - 1‖ ≤ 1 / 2 ∧
        Matrix.det (normalizedMean (V w) c) = 1 := by
  have hL0 : NeZero L := ⟨by have := hL.2; omega⟩
  have hfin : Finite (Edge L n k m) := PeriodicLattice.instFiniteBond _
  let _ := Fintype.ofFinite (Edge L n k m)
  have flat := hD L hL n k m hn hm 0 (Submodule.zero_mem _) c hcp
  have hr0 : meanRadius (V 0) c = 1 := by rw [h₁]; exact flat.2.1
  have hu0 : normalizedMean (V 0) c = 1 := by rw [h₁]; exact flat.2.2.1
  have facts := fun w (hw : w ∈ ball (0 : E) ρ) => hP n k m hn hm (V w) (hc w hw) (hs w hw) c hcp
  have hVa : ∀ w ∈ ball (0 : E) ρ, AnalyticAt ℂ V w := fun w hw =>
    analyticAt_pi_iff.2 fun b => ha b w hw
  have an₁ : AnalyticOnNhd ℂ (fun w => meanRadius (V w) c) (ball 0 ρ) := fun w hw =>
    AnalyticAt.comp (g := fun V' : Edge L n k m → ComplexMatrix2 => meanRadius V' c)
      (facts w hw).2.2.2.1 (hVa w hw)
  have an₂ : AnalyticOnNhd ℂ (fun w => normalizedMean (V w) c) (ball 0 ρ) := fun w hw =>
    AnalyticAt.comp (g := fun V' : Edge L n k m → ComplexMatrix2 => normalizedMean V' c)
      (facts w hw).2.2.2.2 (hVa w hw)
  refine ⟨an₁, an₂, fun w hw => ⟨?_, ?_, (facts w hw).2.1.le, (facts w hw).2.2.1⟩⟩
  · have := norm_sub_le_of_analyticOn_ball (f := fun w => meanRadius (V w) c) (B := 1 / 2) hρ an₁
      (fun v hv => by simpa [hr0] using (facts v hv).1.le) hw
    simpa [hr0] using this
  · have := norm_sub_le_of_analyticOn_ball (f := fun w => normalizedMean (V w) c) (B := 1 / 2) hρ
      an₂ (fun v hv => by simpa [hu0] using (facts v hv).2.1.le) hw
    simpa [hu0] using this
private theorem levelBounds {L : ℕ} {ρL ρ₀ C₀ : ℝ} (hP : MeanFacts L ρL) (hρL : 0 < ρL)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hD : NormalizedMeanAtOne)
    (hρ₀ : 0 < ρ₀) (hC₀ : 0 ≤ C₀) (k : ℕ) :
    ∀ m, m ≤ k → ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧ ∀ n, 0 < n →
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (X : E → ChainPoint L n k),
        IsSmallFamily X ρ₀ C₀ →
        (∀ i, i ≤ m → LevelBound X ρ C i) ∧ ∀ i : Fin k, (i : ℕ) < m → RadiusBound X ρ C i := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨ρ₀, C₀, hρ₀, le_rfl, hC₀, fun n hn E _ _ X hF =>
      ⟨fun i hi => ?_, fun i hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨by rw [hF.zero]; rfl, hF.mem, hF.fine_analytic, hF.fine_near⟩
  | succ m ih =>
    intro hm'
    have hm : m < k := hm'
    obtain ⟨ρ, C, hρ, hρ₀', hC, H⟩ := ih hm.le
    obtain ⟨ρ₁, hρ₁d⟩ : ∃ ρ₁, ρ₁ = min ρ (ρL / (2 * (C + 1))) := ⟨_, rfl⟩
    have hρ₁ : 0 < ρ₁ := by rw [hρ₁d]; exact lt_min hρ (by positivity)
    have hρ₁a : ρ₁ ≤ ρ := hρ₁d ▸ min_le_left _ _
    have hρ₁b : ρ₁ ≤ ρL / (2 * (C + 1)) := hρ₁d ▸ min_le_right _ _
    obtain ⟨C₁, hC₁d⟩ : ∃ C₁, C₁ = 3 / 2 * C₀ + 1 / 2 / ρ₁ := ⟨_, rfl⟩
    have hC₁ : 0 ≤ C₁ := by rw [hC₁d]; positivity
    obtain ⟨ρ₂, hρ₂d⟩ : ∃ ρ₂, ρ₂ = min ρ₁ (1 / (2 * (C₁ + 1))) := ⟨_, rfl⟩
    have hρ₂ : 0 < ρ₂ := by rw [hρ₂d]; exact lt_min hρ₁ (by positivity)
    have hρ₂a : ρ₂ ≤ ρ₁ := hρ₂d ▸ min_le_left _ _
    have hρ₂b : ρ₂ ≤ 1 / (2 * (C₁ + 1)) := hρ₂d ▸ min_le_right _ _
    refine ⟨ρ₂, max C (2 * C₁), hρ₂, (hρ₂a.trans hρ₁a).trans hρ₀', le_max_of_le_left hC, ?_⟩
    intro n hn E _ _ X hF
    obtain ⟨hG, hLn⟩ := H n hn E X hF
    have hg := hG m le_rfl
    have s₁ : ball (0 : E) ρ₁ ⊆ ball 0 ρ := ball_subset_ball hρ₁a
    have s₀ : ball (0 : E) ρ₁ ⊆ ball 0 ρ₀ := ball_subset_ball (hρ₁a.trans hρ₀')
    have s₂ : ball (0 : E) ρ₂ ⊆ ball 0 ρ₁ := ball_subset_ball hρ₂a
    have hsm : ∀ w ∈ ball (0 : E) ρ₁, ∀ b, ‖levelField (X w) m b - 1‖ < ρL := by
      intro w hw b
      have h1 := hg.near w (s₁ hw) b
      have h2 : ‖w‖ < ρL / (2 * (C + 1)) := (mem_ball_zero_iff.1 hw).trans_le hρ₁b
      rw [lt_div_iff₀ (by positivity)] at h2
      nlinarith [norm_nonneg w, mul_nonneg hC (norm_nonneg w)]
    have hal := fun (c : Edge L n k (m + 1)) (hc : c.IsPositivelyOriented) =>
      mean_along_family hP hL hD hn hm hρ₁ (V := fun w => levelField (X w) m)
        (fun w hw => hg.mem w (s₁ hw)) (fun b => (hg.analytic b).mono s₁) hsm hg.one hc
    have pos : ∀ (c : Edge L n k (m + 1)) (hc : c.IsPositivelyOriented),
        AnalyticOnNhd ℂ (fun w => levelField (X w) (m + 1) c) (ball 0 ρ₁) ∧
        levelField (X 0) (m + 1) c = 1 ∧
        ∀ w ∈ ball (0 : E) ρ₁, Matrix.det (levelField (X w) (m + 1) c) = 1 ∧
          ‖levelField (X w) (m + 1) c - 1‖ ≤ C₁ * ‖w‖ := by
      intro c hc
      obtain ⟨-, a₂, a₃⟩ := hal c hc
      refine ⟨?_, ?_, fun w hw => ?_⟩
      · simp only [levelField_pos _ hm hc]
        exact fun w hw => ((hF.noise_analytic _ _) w (s₀ hw)).mul (a₂ w hw)
      · have h0 : normalizedMean (levelField (X 0) m) c = 1 := by
          rw [hg.one]
          exact (hD L hL n k m hn hm 0 (Submodule.zero_mem _) c hc).2.2.1
        rw [levelField_pos _ hm hc, h0, hF.zero]
        simp [unitPoint]
      · obtain ⟨-, h₂, h₃, h₄⟩ := a₃ w hw
        rw [levelField_pos _ hm hc]
        refine ⟨by rw [Matrix.det_mul, hF.noise_det w (s₀ hw), h₄, one_mul], ?_⟩
        have := norm_mul_sub_one_le (hF.noise_near w (s₀ hw) ⟨m, hm⟩ ⟨c, hc⟩) h₂ h₃
        refine this.trans (le_of_eq ?_)
        rw [hC₁d]
        ring
    have small₂ : ∀ w ∈ ball (0 : E) ρ₂, C₁ * ‖w‖ ≤ 1 / 2 := by
      intro w hw
      have h2 : ‖w‖ < 1 / (2 * (C₁ + 1)) := (mem_ball_zero_iff.1 hw).trans_le hρ₂b
      rw [lt_div_iff₀ (by positivity)] at h2
      nlinarith [norm_nonneg w]
    have all : ∀ b : Edge L n k (m + 1),
        AnalyticOnNhd ℂ (fun w => levelField (X w) (m + 1) b) (ball 0 ρ₂) ∧
        levelField (X 0) (m + 1) b = 1 ∧
        ∀ w ∈ ball (0 : E) ρ₂, ‖levelField (X w) (m + 1) b - 1‖ ≤ 2 * C₁ * ‖w‖ := by
      intro b
      by_cases hb : b.IsPositivelyOriented
      · obtain ⟨a, o, h⟩ := pos b hb
        refine ⟨a.mono s₂, o, fun w hw => (h w (s₂ hw)).2.trans ?_⟩
        nlinarith [mul_nonneg hC₁ (norm_nonneg w)]
      · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
        obtain ⟨a, o, h⟩ := pos _ hr
        refine ⟨?_, ?_, fun w hw => ?_⟩
        · simp only [levelField_neg _ hm hb]
          intro w hw
          exact analyticAt_matInv (a w (s₂ hw)) (by rw [(h w (s₂ hw)).1]; exact isUnit_one)
        · rw [levelField_neg _ hm hb, o]
          simp
        · rw [levelField_neg _ hm hb]
          obtain ⟨h₁, h₂⟩ := h w (s₂ hw)
          have := norm_inv_sub_one_le h₁ (h₂.trans (small₂ w hw))
          nlinarith
    have hmax : 1 / 2 / ρ₁ ≤ max C (2 * C₁) := by
      refine le_max_of_le_right ?_
      have : 0 ≤ 1 / 2 / ρ₁ := by positivity
      rw [hC₁d]
      nlinarith
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_cases h : i ≤ m
      · exact (hG i h).mono (hρ₂a.trans hρ₁a) (le_max_left _ _)
      · obtain rfl : i = m + 1 := by omega
        refine ⟨funext fun b => (all b).2.1, fun w hw => levelField_succ_mem hL hn _ hm fun b hb =>
          ((pos b hb).2.2 w (s₂ hw)).1, fun b => (all b).1, fun w hw b => ?_⟩
        exact ((all b).2.2 w hw).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · by_cases h : (i : ℕ) < m
      · exact (hLn i h).mono (hρ₂a.trans hρ₁a) (le_max_left _ _)
      · have e : (i : ℕ) = m := by omega
        obtain rfl : i = ⟨m, hm⟩ := Fin.ext e
        refine ⟨fun c => ((hal c.1 c.2).1).mono s₂, fun w hw c => ?_⟩
        exact ((hal c.1 c.2).2.2 w (s₂ hw)).1.trans
          (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
end LevelBounds
section PauliExponential
private def expPauli (a : Fin 3 → ℂ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • ∑ γ, a γ • ComplexMatrix2.pauliFamily γ)
private theorem analyticAt_expPauli (a : Fin 3 → ℂ) : AnalyticAt ℂ expPauli a := by
  have h0 : ∀ γ, AnalyticAt ℂ (fun a : Fin 3 → ℂ => a γ • ComplexMatrix2.pauliFamily γ) a :=
    fun γ => AnalyticAt.fun_smul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) γ).analyticAt a)
      analyticAt_const
  have h2 : AnalyticAt ℂ (fun a : Fin 3 → ℂ => ∑ γ, a γ • ComplexMatrix2.pauliFamily γ) a :=
    Finset.analyticAt_fun_sum _ fun γ _ => h0 γ
  have h1 : AnalyticAt ℂ
      (fun a : Fin 3 → ℂ => Complex.I • ∑ γ, a γ • ComplexMatrix2.pauliFamily γ) a :=
    AnalyticAt.fun_smul analyticAt_const h2
  exact AnalyticAt.comp (g := fun Z : ComplexMatrix2 => NormedSpace.exp Z)
    (NormedSpace.exp_analytic (𝕂 := ℂ) _) h1
private theorem det_expPauli (a : Fin 3 → ℂ) : Matrix.det (expPauli a) = 1 := by
  refine SpinHarmonics.det_matExp_of_trace_eq_zero ?_
  rw [ComplexMatrix2.sum_smul_pauliFamily]
  simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_fin_two]
private theorem expPauli_zero : expPauli 0 = 1 := by
  simp [expPauli, ComplexMatrix2.matExp]
private theorem expPauli_fun_zero : (expPauli fun _ => (0 : ℂ)) = 1 := expPauli_zero
private theorem exists_norm_expPauli_sub_one_le : ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
    ∀ a : Fin 3 → ℂ, ‖a‖ < δ → ‖expPauli a - 1‖ ≤ C * ‖a‖ := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1 (analyticAt_expPauli 0).continuousAt 1 one_pos
  refine ⟨δ, 1 / δ, hδ, by positivity, fun a ha => ?_⟩
  have hb : ∀ w ∈ ball (0 : Fin 3 → ℂ) δ, ‖expPauli w - expPauli 0‖ ≤ 1 := fun w hw => by
    have := H (mem_ball.1 hw)
    rw [dist_eq_norm] at this
    exact this.le
  have := norm_sub_le_of_analyticOn_ball (f := expPauli) (B := 1) hδ
    (fun w _ => analyticAt_expPauli w) hb (mem_ball_zero_iff.2 ha)
  simpa [expPauli_zero] using this
variable {I : Type} [Fintype I]
private theorem norm_comp_le (w : I → ℂ) (e : Fin 3 → I) : ‖fun a => w (e a)‖ ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun a => norm_le_pi_norm w (e a)
private theorem analyticAt_expPauli_comp (e : Fin 3 → I) (w : I → ℂ) :
    AnalyticAt ℂ (fun w : I → ℂ => expPauli fun a => w (e a)) w := by
  have h : AnalyticAt ℂ (fun w : I → ℂ => fun a => w (e a)) w :=
    analyticAt_pi_iff.2 fun a =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) (e a)).analyticAt w
  exact AnalyticAt.comp (g := expPauli) (analyticAt_expPauli _) h
end PauliExponential
section ComplexChainPoint
variable {L n k : ℕ}
private def fineValueAt (w : TripleCoordIndex L n k → ℂ) (p : PositiveEdge L n k 0) :
    ComplexMatrix2 :=
  expPauli fun a => w (.inl (.inl (a, p)))
private theorem complexFineValues_pos (w : TripleCoordIndex L n k → ℂ) {b : Edge L n k 0}
    (hb : b.IsPositivelyOriented) :
    complexFineValues w b = ∑ a, w (.inl (.inl (a, ⟨b, hb⟩))) • ComplexMatrix2.pauliFamily a := by
  simp [complexFineValues, edgeFormOfPositiveValues, extendOddly, hb, ofPauliCoeffs]
private theorem fine_pos (w : TripleCoordIndex L n k → ℂ) {b : Edge L n k 0}
    (hb : b.IsPositivelyOriented) : (complexChainPoint w).fine b = fineValueAt w ⟨b, hb⟩ := by
  simp only [complexChainPoint, PeriodicLattice.expTwist, if_pos hb, complexFineValues_pos w hb,
    unitPoint, mul_one]
  rfl
private theorem fine_neg (w : TripleCoordIndex L n k → ℂ) {b : Edge L n k 0}
    (hb : ¬b.IsPositivelyOriented) :
    (complexChainPoint w).fine b =
      (fineValueAt w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented hb⟩)⁻¹ := by
  simp only [complexChainPoint, PeriodicLattice.expTwist, if_neg hb,
    complexFineValues_pos w (PeriodicLattice.Bond.opposite_isPositivelyOriented hb), unitPoint,
    mul_one]
  rfl
private theorem noise_eq (w : TripleCoordIndex L n k → ℂ) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (complexChainPoint w).noise i c = expPauli fun a => w (.inl (.inr ⟨i, (a, c)⟩)) := by
  simp only [complexChainPoint, complexLevelValues, ofPauliCoeffs, unitPoint, mul_one]
  rfl
private theorem opposite_opposite {m : ℕ} (b : Edge L n k m) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem exists_isSmallFamily_complexChainPoint : ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
    ∀ (L n k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)],
    IsSmallFamily (E := TripleCoordIndex L n k → ℂ) complexChainPoint ρ C := by
  obtain ⟨δ, C, hδ, hC, H⟩ := exists_norm_expPauli_sub_one_le
  refine ⟨min δ (1 / (2 * (C + 1))), 2 * C, lt_min hδ (by positivity), by positivity, ?_⟩
  intro L n k hL hn _ _
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have near : ∀ w : TripleCoordIndex L n k → ℂ, w ∈ ball 0 (min δ (1 / (2 * (C + 1)))) →
      ∀ e : Fin 3 → TripleCoordIndex L n k,
        ‖expPauli (fun a => w (e a)) - 1‖ ≤ C * ‖w‖ ∧ C * ‖w‖ ≤ 1 / 2 := by
    intro w hw e
    have h₁ := mem_ball_zero_iff.1 hw
    have h₂ : ‖w‖ < δ := h₁.trans_le (min_le_left _ _)
    have h₃ : ‖w‖ < 1 / (2 * (C + 1)) := h₁.trans_le (min_le_right _ _)
    have hp := norm_comp_le w e
    refine ⟨(H _ (hp.trans_lt h₂)).trans (mul_le_mul_of_nonneg_left hp hC), ?_⟩
    rw [lt_div_iff₀ (by positivity)] at h₃
    nlinarith [norm_nonneg w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e₁ : (complexChainPoint (0 : TripleCoordIndex L n k → ℂ)).fine =
        (unitPoint L n k).fine := by
      funext b
      by_cases hb : b.IsPositivelyOriented
      · rw [fine_pos _ hb]
        simpa [fineValueAt, unitPoint] using expPauli_fun_zero
      · rw [fine_neg _ hb]
        have : fineValueAt (0 : TripleCoordIndex L n k → ℂ)
            ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented hb⟩ = 1 := by
          simpa [fineValueAt] using expPauli_fun_zero
        rw [this]
        simp [unitPoint]
    have e₂ : (complexChainPoint (0 : TripleCoordIndex L n k → ℂ)).noise =
        (unitPoint L n k).noise := by
      funext i c
      rw [noise_eq]
      simpa [unitPoint] using expPauli_fun_zero
    cases hX : complexChainPoint (0 : TripleCoordIndex L n k → ℂ)
    rw [hX] at e₁ e₂
    simp only at e₁ e₂
    subst e₁ e₂
    rfl
  · intro w _
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · show Matrix.det _ = 1
      by_cases hb : b.IsPositivelyOriented
      · rw [fine_pos _ hb]
        exact det_expPauli _
      · rw [fine_neg _ hb, Matrix.det_nonsing_inv]
        simp [fineValueAt, det_expPauli]
    · by_cases hb : b.IsPositivelyOriented
      · have hr : ¬b.opposite.IsPositivelyOriented := by
          rcases hx b with ⟨_, h₂⟩ | h₂
          · exact h₂
          · exact absurd hb h₂.2
        rw [fine_neg _ hr, fine_pos _ hb]
        simp only [opposite_opposite]
      · rw [fine_neg _ hb, fine_pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
        exact (Matrix.nonsing_inv_nonsing_inv _ (by simp [fineValueAt, det_expPauli])).symm
  · intro b w _
    by_cases hb : b.IsPositivelyOriented
    · simp only [fine_pos _ hb]
      exact analyticAt_expPauli_comp _ w
    · simp only [fine_neg _ hb]
      exact analyticAt_matInv (analyticAt_expPauli_comp _ w)
        (by simp only [fineValueAt, det_expPauli, isUnit_one])
  · intro w hw b
    by_cases hb : b.IsPositivelyOriented
    · rw [fine_pos _ hb]
      have h := (near w hw fun a => .inl (.inl (a, ⟨b, hb⟩))).1
      exact h.trans (by nlinarith [mul_nonneg hC (norm_nonneg w)])
    · rw [fine_neg _ hb]
      obtain ⟨h₁, h₂⟩ := near w hw fun a => .inl (.inl (a, ⟨b.opposite,
        PeriodicLattice.Bond.opposite_isPositivelyOriented hb⟩))
      have := norm_inv_sub_one_le (det_expPauli _) (h₁.trans h₂)
      exact this.trans (by nlinarith)
  · intro w _ i c
    rw [noise_eq]
    exact det_expPauli _
  · intro i c w _
    simp only [noise_eq]
    exact analyticAt_expPauli_comp _ w
  · intro w hw i c
    rw [noise_eq]
    have h := (near w hw fun a => .inl (.inr ⟨i, (a, c)⟩)).1
    exact h.trans (by nlinarith [mul_nonneg hC (norm_nonneg w)])
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem expTwist_congr {m : ℕ} {A A' U : Edge L n k m → ComplexMatrix2}
    (h : ∀ b : Edge L n k m, b.IsPositivelyOriented → A b = A' b) :
    PeriodicLattice.expTwist A U = PeriodicLattice.expTwist A' U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, h b hb]
  · simp only [PeriodicLattice.expTwist, if_neg hb,
      h _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private theorem complexChainPoint_complexifyCoords (P : PauliCoordinates L n k)
    (x : TripleCoordIndex L n k → ℝ) :
    complexChainPoint (complexifyCoords x) = pointOfCoords P x := by
  set ξ : LevelForms L n k := P.formCoords.symm fun p => x (.inl p) with hξ
  have hc : ∀ p, P.formCoords ξ p = x (.inl p) := fun p => by
    rw [hξ, LinearEquiv.apply_symm_apply]
  have h₀ : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      complexFineValues (complexifyCoords x) b = (ξ.1 : Edge L n k 0 → ComplexMatrix2) b := by
    intro b hb
    rw [complexFineValues_pos _ hb]
    have hs : (ξ.1 : Edge L n k 0 → ComplexMatrix2) b ∈ ComplexMatrix2.traceless :=
      (ξ.1.2.1 b hb).2
    refine Eq.trans ?_ (sum_pauliCoeff_smul hs)
    refine Finset.sum_congr rfl fun a _ => ?_
    have := P.formCoords_base ξ (a, ⟨b, hb⟩)
    rw [hc] at this
    congr 1
    exact this.symm
  have h₁ : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      complexLevelValues (complexifyCoords x) i c =
        (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c := by
    intro i c
    have hs : (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c ∈ ComplexMatrix2.traceless :=
      ((ξ.2 i).2.1 c.1 c.2).2
    have e : complexLevelValues (complexifyCoords x) i c =
        ∑ a, complexifyCoords x (.inl (.inr ⟨i, (a, c)⟩)) • ComplexMatrix2.pauliFamily a := rfl
    rw [e]
    refine Eq.trans ?_ (sum_pauliCoeff_smul hs)
    refine Finset.sum_congr rfl fun a _ => ?_
    have := P.formCoords_level ξ i (a, c)
    rw [hc] at this
    congr 1
    exact this.symm
  simp only [complexChainPoint, pointOfCoords, expMove, tripleOfCoords]
  rw [expTwist_congr h₀]
  congr 1
  funext i c
  rw [h₁]
end ComplexChainPoint
section VertexCells
variable {L n k : ℕ}
private theorem cellDist_le_of_near (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m m' : ℕ} (x : Vertex L n k m)
    (x' : Vertex L n k m') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) -
      (x' : PeriodicLattice.FourTorus L n)) μ‖ ≤ t) :
    cellDist (levelVertexCell x) (levelVertexCell x') ≤ 2 * (t + 1) := by apply _root_.YangMills.SharedProofs.p26872 <;> assumption
private theorem norm_target_sub_source_le (hL : 1 ≤ (L : ℝ)) {m : ℕ} (hm : m ≤ k)
    (b : Edge L n k m) (ν : Fin 4) :
    ‖((b.target : PeriodicLattice.FourTorus L n) -
      (b.source : PeriodicLattice.FourTorus L n)) ν‖ ≤ 1 := by apply _root_.YangMills.SharedProofs.p39837 <;> assumption
private theorem cellDist_source_le_of_mem_bondsInDoubleBlock (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m < k)
    (c : Edge L n k (m + 1)) {b : Edge L n k m}
    (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k m))) :
    cellDist (levelVertexCell b.source) (levelVertexCell c.source) ≤ 5 := by apply _root_.YangMills.SharedProofs.p40516 <;> assumption
private theorem levelField_eq_of_eqOn_near (hR : NormalizedMeanLocal)
    (hC : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ m, m ≤ k → ∀ (b : Edge L n k m) (w w' : TripleCoordIndex L n k → ℂ),
      (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell b.source) ≤ 9 * (m : ℝ) + 4 →
        w i = w' i) →
      levelField (complexChainPoint w) m b = levelField (complexChainPoint w') m b := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have self0 : ∀ {m : ℕ} (x : Vertex L n k m),
      cellDist (levelVertexCell x) (levelVertexCell x) ≤ 2 := by
    intro m x
    have := cellDist_le_of_near hC hL x x (t := 0) le_rfl (fun μ => by simp)
    linarith
  have ends : ∀ {m : ℕ}, m ≤ k → ∀ b : Edge L n k m,
      cellDist (levelVertexCell b.target) (levelVertexCell b.source) ≤ 4 := by
    intro m hm b
    have := cellDist_le_of_near hC hL b.target b.source (t := 1) zero_le_one
      (norm_target_sub_source_le hL1 hm b)
    linarith
  have tri := (hC L hL n k).2.1
  intro m
  induction m with
  | zero =>
    intro _ b w w' h
    show (complexChainPoint w).fine b = (complexChainPoint w').fine b
    by_cases hb : b.IsPositivelyOriented
    · rw [fine_pos _ hb, fine_pos _ hb]
      unfold fineValueAt
      congr 1
      funext a
      refine h _ ?_
      have := self0 b.source
      simp only [Nat.cast_zero]
      refine le_trans ?_ (by linarith : (2 : ℝ) ≤ 9 * 0 + 4)
      exact this
    · rw [fine_neg _ hb, fine_neg _ hb]
      unfold fineValueAt
      congr 2
      funext a
      refine h _ ?_
      simp only [Nat.cast_zero]
      refine le_trans ?_ (by norm_num : (4 : ℝ) ≤ 9 * 0 + 4)
      exact ends (Nat.zero_le k) b
  | succ m ih =>
    intro hm' b w w' h
    have hm : m < k := hm'
    have pos : ∀ (c : Edge L n k (m + 1)), c.IsPositivelyOriented →
        ∀ (v v' : TripleCoordIndex L n k → ℂ),
        (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell c.source) ≤ 9 * (m : ℝ) + 9 →
          v i = v' i) →
        levelField (complexChainPoint v) (m + 1) c = levelField (complexChainPoint v') (m + 1) c := by
      intro c hc v v' hv
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hA : ∀ a, v (.inl (.inr ⟨⟨m, hm⟩, (a, ⟨c, hc⟩)⟩)) =
          v' (.inl (.inr ⟨⟨m, hm⟩, (a, ⟨c, hc⟩)⟩)) := fun a =>
        hv _ (le_trans (self0 c.source) (by linarith))
      have hB : normalizedMean (levelField (complexChainPoint v) m) c =
          normalizedMean (levelField (complexChainPoint v') m) c := by
        refine (hR L hL n k m hn hm c hc _ _ fun b' hb' => ?_).2.2
        refine ih hm.le b' v v' fun i hi => hv i ?_
        have h₅ := cellDist_source_le_of_mem_bondsInDoubleBlock hC hL hm c hb'
        have := tri (tripleCoordIndexCell i) (levelVertexCell b'.source) (levelVertexCell c.source)
        linarith
      rw [levelField_pos _ hm hc, levelField_pos _ hm hc, noise_eq, noise_eq, hB]
      simp only [hA]
    by_cases hb : b.IsPositivelyOriented
    · refine pos b hb w w' fun i hi => h i ?_
      push_cast
      linarith
    · have e : levelField (complexChainPoint w) (m + 1) b.opposite =
          levelField (complexChainPoint w') (m + 1) b.opposite := by
        refine pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb) w w' fun i hi => h i ?_
        have h₄ := ends hm' b
        have := tri (tripleCoordIndexCell i) (levelVertexCell b.target) (levelVertexCell b.source)
        have hi' : cellDist (tripleCoordIndexCell i) (levelVertexCell b.target) ≤
            9 * (m : ℝ) + 9 := hi
        push_cast
        linarith
      rw [levelField_neg _ hm hb, levelField_neg _ hm hb, e]
end VertexCells
private theorem meanRadius_eq_of_eqOn_near {L n k : ℕ} (hR : NormalizedMeanLocal)
    (hC : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (w w' : TripleCoordIndex L n k → ℂ)
    (h : ∀ i', cellDist (tripleCoordIndexCell i') (levelVertexCell c.1.source) ≤
      9 * (k : ℝ) + 9 → w i' = w' i') :
    meanRadius (levelField (complexChainPoint w) i) c.1 =
      meanRadius (levelField (complexChainPoint w') i) c.1 := by
  refine (hR L hL n k i hn i.2 c.1 c.2 _ _ fun b hb => ?_).2.1
  refine levelField_eq_of_eqOn_near hR hC hL hn i i.2.le b w w' fun i' hi' => h i' ?_
  have h₅ := cellDist_source_le_of_mem_bondsInDoubleBlock hC hL i.2 c.1 hb
  have := (hC L hL n k).2.1 (tripleCoordIndexCell i') (levelVertexCell b.source)
    (levelVertexCell c.1.source)
  have hik : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast i.2.le
  linarith
end LevelFieldLocality
open Tower LevelFieldLocality in
theorem levelFieldsHolomorphicAndLocal_proof (hA : NormalizedMeanAnalytic)
    (hN : NormalizedMeanNearOne) (hD : NormalizedMeanAtOne) (hR : NormalizedMeanLocal)
    (hC : NeighbouringFineVertexCells) :
    LevelFieldsHolomorphicAndLocal := by
  intro L hL k hk
  obtain ⟨ρL, hρL, hP⟩ := exists_meanFacts hA hN L hL
  obtain ⟨ρ₀, C₀, hρ₀, hC₀, hS⟩ := exists_isSmallFamily_complexChainPoint
  obtain ⟨ρ, C, hρ, -, hCn, H⟩ := levelBounds hP hρL hL hD hρ₀ hC₀ k k le_rfl
  refine ⟨ρ, C, 9 * (k : ℝ) + 9, hρ, hCn, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro _ _ _ _ _ _ _ _ _ P
  obtain ⟨hG, hLn⟩ := H n hn (TripleCoordIndex L n k → ℂ) complexChainPoint (hS L n k hL hn)
  refine ⟨complexChainPoint_complexifyCoords P, fun m hm w hw => (hG m hm).mem w hw,
    fun m hm b => ⟨(hG m hm).analytic b, fun w hw => (hG m hm).near w hw b,
      fun w _ w' _ h => ?_⟩, fun i c =>
    ⟨(hLn i i.2).analytic c, fun w hw => (hLn i i.2).near w hw c, fun w _ w' _ h =>
      meanRadius_eq_of_eqOn_near hR hC hL hn i c w w' h⟩⟩
  refine levelField_eq_of_eqOn_near hR hC hL hn m hm b w w' fun i hi => h i ?_
  have : (m : ℝ) ≤ k := by exact_mod_cast hm
  linarith
end YangMills.Construction.RunningCouplingSlope
end
