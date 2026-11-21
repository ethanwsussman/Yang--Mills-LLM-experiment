import YangMills.Construction.ToriAtArbitraryCouplings.ApproximationThatKeepsTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityByTelescoping
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open Set Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace SeparatedApproximation
private theorem closedThickening_eq_ambient (s : TorusSide) (E : Ambient) (P : Set (s.Point E))
    (r : ℝ) :
    s.closedThickening E P r =
      AmbientPoints.closedThickening s.asMirrorData.toStandingParameters E P r := by
  cases E <;> rfl
private theorem openThickening_eq_ambient (s : TorusSide) (E : Ambient) (P : Set (s.Point E))
    (r : ℝ) :
    s.openThickening E P r =
      AmbientPoints.openThickening s.asMirrorData.toStandingParameters E P r := by
  cases E <;> rfl
private theorem setDist_singleton_eq_zero (s : TorusSide) (E : Ambient) {P : Set (s.Point E)}
    {x : s.Point E} (hx : x ∈ P) : s.setDist E {x} P = 0 := by
  have h : s.setDist E {x} P =
      AmbientPoints.setDist s.asMirrorData.toStandingParameters E {x} P := by
    cases E <;> rfl
  rw [h]
  refine le_antisymm ?_ bot_le
  unfold AmbientPoints.setDist
  refine (iInf₂_le x (mem_singleton x)).trans ((iInf₂_le x hx).trans ?_)
  have hz := AmbientPoints.pointDist_self (s := s.asMirrorData.toStandingParameters) E x
  exact (congrArg ENNReal.ofReal hz).le.trans (by simp)
private theorem subset_openThickening (s : TorusSide) (E : Ambient) (P : Set (s.Point E)) {r : ℝ}
    (hr : 0 < r) : P ⊆ s.openThickening E P r := fun x hx => by
  rw [s.mem_openThickening_iff, setDist_singleton_eq_zero s E hx]
  exact ENNReal.ofReal_pos.2 hr
private theorem openThickening_subset_closed (s : TorusSide) (E : Ambient) (P : Set (s.Point E))
    (r : ℝ) : s.openThickening E P r ⊆ s.closedThickening E P r := fun x hx => by
  rw [s.mem_openThickening_iff] at hx
  rw [s.mem_closedThickening_iff]
  exact hx.le
private theorem tendsto_approxDefect (s : TorusSide) (m' : ℕ) (E : Ambient) {n : ℕ}
    (f : Fin n → s.Point E → ℝ) :
    Filter.Tendsto (s.approxDefect m' E f) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (s.approxDefect m' E f) := by
    have h : s.approxDefect m' E f = fun ε => ∑ i, 80 * (cubeEdge s.L m' : ℝ) * ε *
        ∏ l ∈ Finset.univ.erase i, (s.sharpNormAt m' E (f l) + 80 * (cubeEdge s.L m' : ℝ) * ε) :=
      funext fun _ => rfl
    rw [h]
    fun_prop
  have h0 : s.approxDefect m' E f 0 = 0 := by
    simp [TorusSide.approxDefect]
  exact (hcont.tendsto' 0 0 h0).mono_left nhdsWithin_le_nhds
private theorem telescope_term_le {n : ℕ} (a b : Fin n → ℝ) (t e : ℝ) (i : Fin n)
    (ha : ∀ l, 0 ≤ a l) (hb : ∀ l, 0 ≤ b l) (hab : ∀ l, a l ≤ b l + e) (ht : t ≤ e)
    (he : 0 ≤ e) :
    t * (∏ l ∈ Finset.Iio i, a l) * ∏ l ∈ Finset.Ioi i, b l ≤
      e * ∏ l ∈ Finset.univ.erase i, (b l + e) := by
  have hsplit : Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun h => h.ne) fun h => h.ne'⟩
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    rw [Finset.disjoint_left]
    intro l h h'
    exact absurd (Finset.mem_Iio.1 h) (not_lt.2 (Finset.mem_Ioi.1 h').le)
  rw [hsplit, Finset.prod_union hdisj, mul_assoc]
  refine mul_le_mul ht (mul_le_mul ?_ ?_ ?_ ?_) ?_ he
  · exact Finset.prod_le_prod (fun l _ => ha l) fun l _ => hab l
  · exact Finset.prod_le_prod (fun l _ => hb l) fun l _ => le_add_of_nonneg_right he
  · exact Finset.prod_nonneg fun l _ => hb l
  · exact Finset.prod_nonneg fun l _ => add_nonneg (hb l) he
  · exact mul_nonneg (Finset.prod_nonneg fun l _ => ha l) (Finset.prod_nonneg fun l _ => hb l)
theorem holds (hE : LipschitzEstimates.Combined)
    (hF : SupportAdaptedFamily.Claim)
    (hT : TelescopingEquicontinuity.Claim) : Statement := by
  intro s hL m' E D hD n hn f hf d hd hdf ε hε
  obtain ⟨⟨hB, hC1, hSN⟩, -, -, hNb, hDist⟩ := hE s hL m' E
  obtain ⟨hSup, hFit, -, -⟩ := hF s hL m' E
  obtain ⟨-, hent, hpw⟩ := (s.mem_sepOfLength_iff E n _).1 hf
  rw [List.forall_mem_ofFn_iff] at hent
  rw [List.pairwise_ofFn] at hpw
  have hdisj : ∀ i k, i ≠ k → Disjoint (s.closedSupport E (f i)) (s.closedSupport E (f k)) := by
    intro i k hik
    rcases lt_or_gt_of_ne hik with h | h
    · exact hpw h
    · exact (hpw h).symm
  have hsep : ∀ i k, i ≠ k → ENNReal.ofReal d ≤
      s.setDist E (s.closedSupport E (f i)) (s.closedSupport E (f k)) := by
    intro i k hik
    rw [s.gapAllLengths_eq_supportGap, s.supportGap_ofFn] at hdf
    exact hdf.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
  have hd3 : 0 < d / 3 := by positivity
  set A : Fin n → Set (s.Point E) := s.supportThickening E f d with hAdef
  have hAcomp : ∀ i, s.IsCompactWrt E (A i) := by
    intro i
    have h := (hNb (s.closedSupport E (f i)) (d / 3) (hent i).2 hd3).2
    rw [← closedThickening_eq_ambient] at h
    exact h
  have hAdist : ∀ i k, i ≠ k → ENNReal.ofReal (d / 3) ≤ s.setDist E (A i) (A k) := by
    intro i k hik
    have h := hDist _ _ d (d / 3) (hent i).2 (hent k).2 hd (hsep i k hik) hd3 (by linarith)
    rw [← closedThickening_eq_ambient, ← closedThickening_eq_ambient] at h
    have h3 : d - 2 * (d / 3) = d / 3 := by ring
    rw [h3] at h
    exact h
  set W : Fin n → Set (s.Point E) :=
    fun i => s.openThickening E (s.closedSupport E (f i)) (d / 3) with hWdef
  have hWopen : ∀ i, s.IsOpenWrt E (W i) := by
    intro i
    have h := (hNb (s.closedSupport E (f i)) (d / 3) (hent i).2 hd3).1
    rw [← openThickening_eq_ambient] at h
    exact h
  have hsubW : ∀ i, s.closedSupport E (f i) ⊆ W i := fun i => subset_openThickening s E _ hd3
  have hWA : ∀ i, W i ⊆ A i := fun i => openThickening_subset_closed s E _ _
  obtain ⟨Q, hQ, hQsub, hQdisj⟩ := hFit.2 n (fun i => s.closedSupport E (f i)) W
    (fun i => (hent i).2) (fun i k hik => hdisj i k hik) hWopen hsubW
  have hCQ : ∀ i, s.c1VanishingOutside E (Q i) = s.c1SuppIn E (Q i) :=
    fun i => (hSup.1 (Q i) (hQ i)).2.1
  have hfQ : ∀ i, f i ∈ s.c1VanishingOutside E (Q i) := by
    intro i
    rw [hCQ]
    exact ⟨(hent i).1, (hent i).2, (hQsub i).1⟩
  choose φ hφD hφε using fun i => hD.dense ⟨Q i, hQ i⟩ (f i) (hfQ i) ε hε
  have hφQ : ∀ i, φ i ∈ s.c1SuppIn E (Q i) := by
    intro i
    rw [← hCQ]
    exact hD.subset ⟨Q i, hQ i⟩ (hφD i)
  have hφA : ∀ i, s.closedSupport E (φ i) ⊆ A i :=
    fun i => (hφQ i).2.2.trans ((hQsub i).2.trans (hWA i))
  have hfV : ∀ i, f i ∈ s.c1Submodule E (A i) := fun i =>
    (s.mem_c1Submodule_iff E _ _).2
      ⟨(hent i).1, (hent i).2, (hsubW i).trans (hWA i)⟩
  have hφV : ∀ i, φ i ∈ s.c1Submodule E (A i) := fun i =>
    (s.mem_c1Submodule_iff E _ _).2 ⟨(hφQ i).1, (hφQ i).2.1, hφA i⟩
  refine ⟨hAcomp, hAdist, ⟨φ, ⟨?_, fun i => ⟨hφA i, (hφε i).le⟩⟩, hfV, hφV, ?_⟩,
    tendsto_approxDefect s m' E f⟩
  · refine mem_iUnion₂.2 ⟨n, hn, fun i => ⟨Q i, hQ i⟩, φ, ?_, hφD, rfl⟩
    exact hQdisj
  · intro c hc Ψ hΨ
    obtain ⟨-, V0, p, hV0, hp⟩ := hSN
    have hle : ∀ B : Set (s.Point E), s.c1Submodule E B ≤ V0 := by
      intro B g hg
      exact show g ∈ (V0 : Set (s.Point E → ℝ)) from by
        rw [hV0]
        have h := hC1.1 B ((s.mem_c1Submodule_iff E _ _).1 hg)
        exact ⟨h.1, h.2.1, subset_univ _⟩
    let q : ∀ l, Seminorm ℝ (s.c1Submodule E (A l)) :=
      fun l => p.comp (Submodule.inclusion (hle (A l)))
    have hq : ∀ l (u : s.c1Submodule E (A l)),
        q l u = s.sharpNormAt m' E (u : s.Point E → ℝ) := fun l u =>
      hp (Submodule.inclusion (hle (A l)) u)
    let F : ∀ l, s.c1Submodule E (A l) := fun l => ⟨f l, hfV l⟩
    let Φ : ∀ l, s.c1Submodule E (A l) := fun l => ⟨φ l, hφV l⟩
    have key := hT.1 n hn (fun l => s.c1Submodule E (A l)) q c hc Ψ
      (fun u => by
        simp only [hq]
        exact hΨ u) F Φ
    set e : ℝ := 80 * (cubeEdge s.L m' : ℝ) * ε with hedef
    have he : 0 ≤ e := by positivity
    have hdiff : ∀ l, q l (F l - Φ l) ≤ e := by
      intro l
      rw [hq]
      have hmem := (s.mem_c1Submodule_iff E _ _).1 (F l - Φ l).2
      have hc1 : ((F l - Φ l : s.c1Submodule E (A l)) : s.Point E → ℝ) ∈
          s.c1CompactSet E := ⟨hmem.1, hmem.2.1⟩
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := hB _ hc1
      have h3 : s.c1NormOn E ((F l - Φ l : s.c1Submodule E (A l)) : s.Point E → ℝ) ≤ ε :=
        (hφε l).le
      have hM : (0 : ℝ) ≤ 80 * (cubeEdge s.L m' : ℝ) := by positivity
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hM))
    have hφle : ∀ l, q l (Φ l) ≤ q l (F l) + e := by
      intro l
      have h : Φ l = F l - (F l - Φ l) := by abel
      calc q l (Φ l) = q l (F l - (F l - Φ l)) := by rw [← h]
        _ ≤ q l (F l) + q l (F l - Φ l) := map_sub_le_add _ _ _
        _ ≤ q l (F l) + e := by linarith [hdiff l]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hc)
    refine Finset.sum_le_sum fun i _ => ?_
    have h := telescope_term_le (fun l => q l (Φ l)) (fun l => q l (F l)) (q i (F i - Φ i)) e i
      (fun l => apply_nonneg _ _) (fun l => apply_nonneg _ _) hφle (hdiff i) he
    simp only [hq] at h ⊢
    exact h
end SeparatedApproximation
end YangMills.Construction.ToriAtArbitraryCouplings
end
