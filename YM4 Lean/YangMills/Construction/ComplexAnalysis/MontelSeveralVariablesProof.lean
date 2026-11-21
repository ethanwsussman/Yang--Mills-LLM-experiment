import YangMills.Construction.ComplexAnalysis.MontelSeveralVariables
import YangMills.Construction.Coordinates.BoundedHolomorphicLipschitz
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.ComplexAnalysis.Montel
open YangMills.Construction.Coordinates
variable {n : ℕ}
theorem exists_nhds_norm_sub_lt_of_bounded
    (h : ComplexCoordinates.BoundedHolomorphicLipschitz.Bound) (hn : 1 ≤ n)
    {O : Set (ComplexCoordinates n)} (hO : IsOpen O) {F : ℕ → ComplexCoordinates n → ℂ}
    (hF : ∀ j, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => F j z) {M : ℝ}
    (hM : ∀ j, ∀ z ∈ O, ‖F j z‖ ≤ M) {x : ComplexCoordinates n} (hx : x ∈ O) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ U ∈ 𝓝 x, ∀ j, ∀ z ∈ U, ‖F j z - F j x‖ < ε := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO x hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 x hx)
  set ρ : ℝ := r / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set C : ℝ := 2 * M / ρ * n with hC
  have hC0 : 0 ≤ C := by positivity
  have hsub : ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk x (2 * ρ) ⊆ O := by
    intro z hz
    apply hball
    have : dist z x ≤ 2 * ρ :=
      (dist_pi_le_iff (by positivity)).2 fun k => by simpa [dist_eq_norm] using hz k
    rw [Metric.mem_ball]
    linarith
  have hmem : ∀ z ∈ Metric.ball x ρ,
      z ∈ ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk x ρ := by
    intro z hz k
    have h1 : dist (z k) (x k) ≤ dist z x := dist_le_pi_dist z x k
    have h2 : dist z x < ρ := hz
    rw [dist_eq_norm] at h1
    linarith
  have hδ : 0 < min ρ (ε / (C + 1)) := lt_min hρ0 (by positivity)
  refine ⟨Metric.ball x (min ρ (ε / (C + 1))), Metric.ball_mem_nhds x hδ, fun j z hz => ?_⟩
  have hzρ : z ∈ Metric.ball x ρ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hLip := h n hn O hO (F j) M (hF j) (hM j) ρ x (by positivity) hx hsub z (hmem z hzρ) x
    (hmem x (Metric.mem_ball_self hρ0))
  have hsum : ∑ k, ‖z k - x k‖ ≤ n * ‖z - x‖ := by
    calc ∑ k, ‖z k - x k‖ ≤ ∑ _k : Fin n, ‖z - x‖ :=
          Finset.sum_le_sum fun k _ => norm_le_pi_norm (z - x) k
      _ = n * ‖z - x‖ := by simp
  have hzx : ‖z - x‖ < ε / (C + 1) := by
    have : dist z x < min ρ (ε / (C + 1)) := hz
    rw [dist_eq_norm] at this
    exact this.trans_le (min_le_right _ _)
  have hq : 0 ≤ 2 * M / ρ := by positivity
  calc ‖F j z - F j x‖ ≤ 2 * M / ρ * ∑ k, ‖z k - x k‖ := hLip
    _ ≤ 2 * M / ρ * (n * ‖z - x‖) := mul_le_mul_of_nonneg_left hsum hq
    _ = C * ‖z - x‖ := by rw [hC]; ring
    _ ≤ (C + 1) * ‖z - x‖ := by nlinarith [norm_nonneg (z - x)]
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hzx (by positivity)
    _ = ε := by field_simp
theorem exists_strictMono_tendsto_on_countable {O S : Set (ComplexCoordinates n)}
    {F : ℕ → ComplexCoordinates n → ℂ} {M : ℝ} (hM : ∀ j, ∀ z ∈ O, ‖F j z‖ ≤ M)
    (hS : S.Countable) (hSO : S ⊆ O) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ s ∈ S, ∃ c, Tendsto (fun l => F (φ l) s) atTop (𝓝 c) := by
  have : Countable S := hS.to_subtype
  have hK : IsCompact (Set.pi univ fun _ : S => Metric.closedBall (0 : ℂ) M) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 M
  obtain ⟨c, -, φ, hφ, hc⟩ := hK.tendsto_subseq (x := fun j (s : S) => F j s)
    (fun j s _ => by simpa using hM j s (hSO s.2))
  exact ⟨φ, hφ, fun s hs => ⟨c ⟨s, hs⟩, (tendsto_pi_nhds.1 hc) ⟨s, hs⟩⟩⟩
theorem exists_tendsto_of_equicontinuousAt {S : Set (ComplexCoordinates n)}
    {G : ℕ → ComplexCoordinates n → ℂ} {x : ComplexCoordinates n} (hxS : x ∈ closure S)
    (hE : ∀ ε > 0, ∃ U ∈ 𝓝 x, ∀ j, ∀ z ∈ U, ‖G j z - G j x‖ < ε)
    (hS : ∀ s ∈ S, ∃ c, Tendsto (fun l => G l s) atTop (𝓝 c)) :
    ∃ c, Tendsto (fun l => G l x) atTop (𝓝 c) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨U, hU, hUx⟩ := hE (ε / 3) (by positivity)
  obtain ⟨s, hsU, hsS⟩ := mem_closure_iff_nhds.1 hxS U hU
  obtain ⟨c, hc⟩ := hS s hsS
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun p hp q hq => ?_⟩
  have h1 := hUx p s hsU
  have h2 := hUx q s hsU
  have h3 := hN p hp q hq
  rw [dist_eq_norm] at h3 ⊢
  have h4 : ‖G p x - G q x‖ ≤ ‖G p s - G p x‖ + ‖G p s - G q s‖ + ‖G q s - G q x‖ := by
    have : G p x - G q x = -(G p s - G p x) + (G p s - G q s) + (G q s - G q x) := by ring
    rw [this]
    exact (norm_add₃_le).trans (by rw [norm_neg])
  linarith
theorem tendstoLocallyUniformlyOn_of_equicontinuousAt {O : Set (ComplexCoordinates n)}
    {G : ℕ → ComplexCoordinates n → ℂ} {g : ComplexCoordinates n → ℂ}
    (hE : ∀ x ∈ O, ∀ ε > 0, ∃ U ∈ 𝓝 x, ∀ j, ∀ z ∈ U, ‖G j z - G j x‖ < ε)
    (hg : ∀ x ∈ O, Tendsto (fun l => G l x) atTop (𝓝 (g x))) :
    TendstoLocallyUniformlyOn G g atTop O := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨U, hU, hUx⟩ := hE x hx (ε / 3) (by positivity)
  refine ⟨U ∩ O, inter_mem (mem_nhdsWithin_of_mem_nhds hU) self_mem_nhdsWithin, ?_⟩
  have hev := (Metric.tendsto_nhds.1 (hg x hx)) (ε / 3) (by positivity)
  filter_upwards [hev] with l hl y hy
  have h1 : ‖g y - g x‖ ≤ ε / 3 := by
    have ht : Tendsto (fun l => ‖G l y - G l x‖) atTop (𝓝 ‖g y - g x‖) :=
      ((hg y hy.2).sub (hg x hx)).norm
    exact le_of_tendsto ht (Eventually.of_forall fun l => (hUx l y hy.1).le)
  have h2 := hUx l y hy.1
  rw [dist_eq_norm] at hl ⊢
  have h3 : ‖g y - G l y‖ ≤ ‖g y - g x‖ + ‖G l x - g x‖ + ‖G l y - G l x‖ := by
    have : g y - G l y = (g y - g x) + -(G l x - g x) + -(G l y - G l x) := by ring
    rw [this]
    exact (norm_add₃_le).trans (by rw [norm_neg, norm_neg])
  linarith
theorem isHolomorphicIn_of_tendstoLocallyUniformlyOn {O : Set (ComplexCoordinates n)}
    (hO : IsOpen O) {G : ℕ → ComplexCoordinates n → ℂ} {g : ComplexCoordinates n → ℂ}
    (hG : ∀ l, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => G l z)
    (hlim : TendstoLocallyUniformlyOn G g atTop O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by
  refine ⟨hO, ?_, ?_⟩
  · have hc : ContinuousOn g O := hlim.continuousOn
      (Eventually.of_forall fun l => continuousOn_pi.1 (hG l).2.1 0).frequently
    exact continuousOn_pi.2 fun _ => hc
  · intro x hx j
    set e : ComplexCoordinates n := ComplexCoordinates.stdBasisVector j with he
    set L : ℂ → ComplexCoordinates n := fun ζ => x + ζ • e with hL
    have hLc : Continuous L := by
      rw [hL]
      fun_prop
    have hV : IsOpen (L ⁻¹' O) := hO.preimage hLc
    have h0 : (0 : ℂ) ∈ L ⁻¹' O := by simpa [hL] using hx
    have hdiff : ∀ l, DifferentiableOn ℂ (G l ∘ L) (L ⁻¹' O) := by
      intro l ζ₀ hζ₀
      have h1 := ((hG l).2.2 (L ζ₀) hζ₀ j).self_of_nhds
      have h2 : DifferentiableAt ℂ (fun ζ : ℂ => G l (L ζ₀ + ζ • e)) 0 :=
        differentiableAt_pi.1 h1 0
      have h3 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ζ₀) ζ₀ :=
        differentiableAt_id.sub_const ζ₀
      have h2' : DifferentiableAt ℂ (fun ζ : ℂ => G l (L ζ₀ + ζ • e)) (ζ₀ - ζ₀) := by
        simpa using h2
      have h4 : DifferentiableAt ℂ
          ((fun ζ : ℂ => G l (L ζ₀ + ζ • e)) ∘ (fun ζ : ℂ => ζ - ζ₀)) ζ₀ :=
        DifferentiableAt.comp ζ₀ h2' h3
      have h5 : (fun ζ : ℂ => G l (L ζ₀ + ζ • e)) ∘ (fun ζ : ℂ => ζ - ζ₀) = G l ∘ L := by
        funext ζ
        simp only [Function.comp, hL, sub_smul]
        congr 1
        abel
      rw [h5] at h4
      exact h4.differentiableWithinAt
    have hlimL : TendstoLocallyUniformlyOn (fun l => G l ∘ L) (g ∘ L) atTop (L ⁻¹' O) :=
      hlim.comp L (mapsTo_preimage L O) hLc.continuousOn
    have hgd : DifferentiableOn ℂ (g ∘ L) (L ⁻¹' O) :=
      hlimL.differentiableOn (Eventually.of_forall hdiff) hV
    filter_upwards [hV.mem_nhds h0] with ζ hζ
    exact differentiableAt_pi.2 fun _ => hgd.differentiableAt (hV.mem_nhds hζ)
theorem montelSeveralVariables_of_bound
    (h : ComplexCoordinates.BoundedHolomorphicLipschitz.Bound) :
    YangMills.Construction.ComplexAnalysis.MontelSeveralVariables := by
  rintro n hn O hO f hf ⟨M, hM⟩
  have hF : ∀ j, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => f (j + 1) z :=
    fun j => hf (j + 1) (by omega)
  have hFM : ∀ j, ∀ z ∈ O, ‖f (j + 1) z‖ ≤ M := fun j => hM (j + 1) (by omega)
  obtain ⟨S, hSO, hSc, hOS⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace O).exists_countable_dense_subset
  obtain ⟨φ, hφ, hconv⟩ :=
    exists_strictMono_tendsto_on_countable (F := fun j => f (j + 1)) hFM hSc hSO
  have hE : ∀ x ∈ O, ∀ ε > 0, ∃ U ∈ 𝓝 x, ∀ l, ∀ z ∈ U,
      ‖f (φ l + 1) z - f (φ l + 1) x‖ < ε := by
    intro x hx ε hε
    obtain ⟨U, hU, hUx⟩ := exists_nhds_norm_sub_lt_of_bounded h hn hO hF hFM hx hε
    exact ⟨U, hU, fun l => hUx (φ l)⟩
  have hpt : ∀ x ∈ O, ∃ c, Tendsto (fun l => f (φ l + 1) x) atTop (𝓝 c) := fun x hx =>
    exists_tendsto_of_equicontinuousAt (G := fun l => f (φ l + 1)) (hOS hx) (hE x hx) hconv
  choose! g hg using hpt
  have hlim : TendstoLocallyUniformlyOn (fun l => f (φ l + 1)) g atTop O :=
    tendstoLocallyUniformlyOn_of_equicontinuousAt hE hg
  refine ⟨fun l => φ l + 1, fun p q hpq => Nat.succ_lt_succ (hφ hpq),
    fun l => Nat.le_add_left 1 _, g,
    isHolomorphicIn_of_tendstoLocallyUniformlyOn hO (fun l => hF (φ l)) hlim, fun K hKO hK => ?_⟩
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1 hlim K hKO hK
end YangMills.Construction.ComplexAnalysis.Montel
