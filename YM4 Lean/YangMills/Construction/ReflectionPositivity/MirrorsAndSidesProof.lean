import YangMills.Construction.ReflectionPositivity.ConcatenationOfSeparatedTuplesAtAMirror
import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMapProof
import YangMills.Construction.ReflectionPositivity.MirrorsAndSides
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace Sides
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_pi_single (μ : Fin 4) (t : ℝ) :
    TorusMetric.euclidNormVec (Pi.single μ t) = |t| := by apply _root_.YangMills.Construction.InfiniteLattice.euclidNormVec_single <;> assumption
theorem sub_update_eq_single (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) :
    x - Function.update x μ t = Pi.single μ (x μ - t) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [hν]
theorem side_pos (D : MirrorData) : 0 < D.side := by apply _root_.YangMills.SharedProofs.p8577 <;> assumption
variable {D : MirrorData}
theorem apply_of_mem_periodGroup {γ : Fin 4 → ℝ}
    (hγ : γ ∈ LimitSpaces.Ambient.periodic.periodGroup D.toStandingParameters) (μ : Fin 4) :
    ∃ k : ℤ, γ μ = D.side * k := by
  have hzero := (LimitSpaces.Ambient.periodic.mem_periodGroup_iff D.toStandingParameters γ).mp hγ
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp (congrFun hzero μ)
  refine ⟨k, ?_⟩
  rw [← hk, zsmul_eq_mul, mul_comm]
theorem proj_update_sub_mul (y : Fin 4 → ℝ) (μ : Fin 4) (k : ℤ) :
    LimitSpaces.Ambient.periodic.proj D.toStandingParameters
        (Function.update y μ (y μ - D.side * k)) =
      LimitSpaces.Ambient.periodic.proj D.toStandingParameters y := by
  have hk : Function.update y μ (y μ - D.side * k) = y + -Pi.single μ (D.side * k) := by
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp [sub_eq_add_neg]
    · simp [hν]
  have hmem : (Pi.single μ (D.side * k) : Fin 4 → ℝ) ∈
      LimitSpaces.Ambient.periodic.periodGroup D.toStandingParameters := by
    rw [LimitSpaces.Ambient.mem_periodGroup_iff]
    funext ν
    refine (AddCircle.coe_eq_zero_iff _).mpr ?_
    by_cases hν : ν = μ
    · subst hν
      exact ⟨k, by simp [mul_comm]⟩
    · exact ⟨0, by simp [hν]⟩
  have hzero := (LimitSpaces.Ambient.periodic.mem_periodGroup_iff D.toStandingParameters _).mp hmem
  rw [hk, LimitSpaces.Ambient.proj_add, LimitSpaces.Ambient.proj_neg, hzero]
  simp
theorem distToHyperplane_eq_iInf (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ)
    (x : P.Carrier D.toStandingParameters) :
    distToHyperplane D P μ c x =
      ⨅ y ∈ hyperplane D P μ c, ENNReal.ofReal (P.pointDist D.toStandingParameters x y) := by
  simp [distToHyperplane, LimitSpaces.Ambient.infSetDist]
theorem euclidDistToHyperplane_holds (μ : Fin 4) (c : ℝ) :
    EuclidDistToHyperplane D μ c := by
  intro x
  refine (distToHyperplane_eq_iInf .euclidean μ c x).trans ?_
  apply le_antisymm
  · have hz : Function.update x μ c ∈ hyperplane D .euclidean μ c := by
      show (Function.update x μ c) μ = c
      simp
    refine (iInf₂_le (Function.update x μ c) hz).trans (ENNReal.ofReal_le_ofReal ?_)
    show TorusMetric.euclidNormVec (x - Function.update x μ c) ≤ _
    rw [sub_update_eq_single, euclidNormVec_pi_single]
  · refine le_iInf₂ fun (z : Fin 4 → ℝ) hz => ENNReal.ofReal_le_ofReal ?_
    have hz' : z μ = c := hz
    have hle := abs_apply_le_euclidNormVec (x - z) μ
    rw [Pi.sub_apply, hz'] at hle
    exact hle
theorem proj_mem_hyperplane {y : Fin 4 → ℝ} {μ : Fin 4} {c : ℝ} {n : ℤ}
    (hy : y μ = D.side / 2 * n + c) :
    LimitSpaces.Ambient.periodic.proj D.toStandingParameters y ∈ hyperplane D .periodic μ c := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · refine ⟨Function.update y μ (y μ - D.side * k), Or.inl ?_, proj_update_sub_mul y μ k⟩
    show (Function.update y μ (y μ - D.side * k)) μ = c
    rw [Function.update_self, hy]
    push_cast
    ring
  · refine ⟨Function.update y μ (y μ - D.side * k), Or.inr ?_, proj_update_sub_mul y μ k⟩
    show (Function.update y μ (y μ - D.side * k)) μ = c + D.side / 2
    rw [Function.update_self, hy]
    push_cast
    ring
theorem exists_abs_apply_le_pointDist
    (hS : LimitSpaces.AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    (x y : Fin 4 → ℝ) (μ : Fin 4) :
    ∃ k : ℤ, |x μ - y μ - D.side * k| ≤
      LimitSpaces.Ambient.periodic.pointDist D.toStandingParameters
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x)
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) := by
  obtain ⟨⟨γ, hγ, e⟩, -⟩ := (hS.1 x y).1
  obtain ⟨k, hk⟩ := apply_of_mem_periodGroup hγ μ
  refine ⟨k, ?_⟩
  have hle := abs_apply_le_euclidNormVec (x - y - γ) μ
  rw [Pi.sub_apply, Pi.sub_apply, hk] at hle
  rw [← e]
  exact hle
theorem realInfDist_eq_min {a c : ℝ} (h0 : 0 < a - c) (h1 : a - c < D.side / 2) :
    LimitSpaces.realInfDist a
        (translateSet (LimitSpaces.multiplesOf (D.side / 2)) c) =
      ENNReal.ofReal (min (a - c) (D.side / 2 - (a - c))) := by
  unfold LimitSpaces.realInfDist
  apply le_antisymm
  · rcases le_total (a - c) (D.side / 2 - (a - c)) with h | h
    · rw [min_eq_left h]
      refine (iInf₂_le c ⟨0, ⟨0, by simp⟩, by simp⟩).trans ?_
      rw [abs_of_pos h0]
    · rw [min_eq_right h]
      refine (iInf₂_le (c + D.side / 2) ⟨D.side / 2, ⟨1, by simp⟩, by ring⟩).trans ?_
      rw [abs_of_neg (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine le_iInf₂ fun t ht => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := ht
    have hp := side_pos D
    rcases le_or_gt n 0 with hn | hn
    · have h2 : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      have h3 : D.side / 2 * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h2
      refine (min_le_left _ _).trans (le_abs.2 (Or.inl ?_))
      linarith
    · have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h3 : D.side / 2 ≤ D.side / 2 * n := by nlinarith
      refine (min_le_right _ _).trans (le_abs.2 (Or.inr ?_))
      linarith
theorem torusDistToHyperplane_holds
    (hS : LimitSpaces.AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    (μ : Fin 4) (c : ℝ) : TorusDistToHyperplane D μ c := by
  have key : ∀ x : Fin 4 → ℝ,
      distToHyperplane D .periodic μ c
          (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x) =
        LimitSpaces.realInfDist (x μ)
          (translateSet (LimitSpaces.multiplesOf (D.side / 2)) c) := by
    intro x
    rw [distToHyperplane_eq_iInf]
    unfold LimitSpaces.realInfDist
    apply le_antisymm
    · refine le_iInf₂ fun t ht => ?_
      obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := ht
      have hz : LimitSpaces.Ambient.periodic.proj D.toStandingParameters
          (Function.update x μ (D.side / 2 * n + c)) ∈ hyperplane D .periodic μ c :=
        proj_mem_hyperplane (n := n) (by simp)
      refine (iInf₂_le _ hz).trans (ENNReal.ofReal_le_ofReal ?_)
      refine ((hS.1 x _).2).trans ?_
      rw [sub_update_eq_single, euclidNormVec_pi_single]
    · refine le_iInf₂ fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨k, hk⟩ := exists_abs_apply_le_pointDist hS x y μ
      have hmem : y μ + D.side * k ∈
          translateSet (LimitSpaces.multiplesOf (D.side / 2)) c := by
        rcases hy with hy | hy
        · have hy' : y μ = c := hy
          exact ⟨D.side * k, ⟨2 * k, by push_cast; ring⟩, by rw [hy']; ring⟩
        · have hy' : y μ = c + D.side / 2 := hy
          exact ⟨D.side / 2 + D.side * k, ⟨2 * k + 1, by push_cast; ring⟩, by rw [hy']; ring⟩
      refine (iInf₂_le _ hmem).trans (ENNReal.ofReal_le_ofReal ?_)
      have e : x μ - (y μ + D.side * k) = x μ - y μ - D.side * k := by ring
      rw [e]
      exact hk
  intro x
  refine ⟨key x, fun h0 h1 => ?_⟩
  rw [key x]
  exact realInfDist_eq_min h0 h1
theorem openHalfOffHyperplane_holds
    (hS : LimitSpaces.AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ) :
    OpenHalfOffHyperplane D P μ c := by
  cases P with
  | euclidean =>
    intro (x : Fin 4 → ℝ) hx
    have hx' : x μ > c := hx
    refine lt_of_lt_of_eq ?_ (euclidDistToHyperplane_holds μ c x).symm
    exact ENNReal.ofReal_pos.2 (abs_pos.2 (by linarith : 0 < x μ - c).ne')
  | periodic =>
    rintro _ ⟨y, ⟨h0, h1⟩, rfl⟩
    have e := ((torusDistToHyperplane_holds hS μ c) y).2 h0 h1
    refine lt_of_lt_of_eq ?_ e.symm
    exact ENNReal.ofReal_pos.2 (lt_min h0 (by linarith))
theorem reflectR4_apply_self (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    LimitSpaces.reflectR4 μ c y μ = 2 * c - y μ := by
  simp [LimitSpaces.reflectR4, LimitSpaces.stdBasisVec]
  ring
theorem reflectedPointsFar_holds
    (hS : LimitSpaces.AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ) : ReflectedPointsFar D P μ c := by
  cases P with
  | euclidean =>
    intro (x : Fin 4 → ℝ) hx (y : Fin 4 → ℝ) hy
    have hx' : x μ > c := hx
    have hy' : y μ > c := hy
    have e₁ := euclidDistToHyperplane_holds (D := D) μ c x
    have e₂ := euclidDistToHyperplane_holds (D := D) μ c y
    rw [e₁, e₂, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [LimitSpaces.Ambient.reflect_euclidean]
    show _ ≤ TorusMetric.euclidNormVec (x - LimitSpaces.reflectR4 μ c y)
    refine le_trans ?_ (abs_apply_le_euclidNormVec _ μ)
    rw [Pi.sub_apply, reflectR4_apply_self, abs_of_pos (by linarith : 0 < x μ - c),
      abs_of_pos (by linarith : 0 < y μ - c)]
    refine le_trans ?_ (le_abs_self _)
    linarith
  | periodic =>
    rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩ _ ⟨y, ⟨hy0, hy1⟩, rfl⟩
    have hx0' : 0 < x μ - c := hx0
    have hx1' : x μ - c < D.side / 2 := hx1
    have hy0' : 0 < y μ - c := hy0
    have hy1' : y μ - c < D.side / 2 := hy1
    have e₁ := (torusDistToHyperplane_holds hS μ c x).2 hx0' hx1'
    have e₂ := (torusDistToHyperplane_holds hS μ c y).2 hy0' hy1'
    have hθ : LimitSpaces.Ambient.periodic.reflect D.toStandingParameters μ c
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) =
        LimitSpaces.Ambient.periodic.proj D.toStandingParameters
          (LimitSpaces.reflectR4 μ c y) :=
      congrFun (LimitSpaces.Ambient.periodic.reflect_comp_proj D.toStandingParameters μ c) y
    obtain ⟨k, hk⟩ := exists_abs_apply_le_pointDist hS x
      (LimitSpaces.reflectR4 μ c y) μ
    rw [← hθ, reflectR4_apply_self] at hk
    have hm₁ : 0 ≤ min (x μ - c) (D.side / 2 - (x μ - c)) := le_min hx0'.le (by linarith)
    have hm₂ : 0 ≤ min (y μ - c) (D.side / 2 - (y μ - c)) := le_min hy0'.le (by linarith)
    have hsum : min (x μ - c) (D.side / 2 - (x μ - c)) + min (y μ - c) (D.side / 2 - (y μ - c)) ≤
        |x μ - (2 * c - y μ) - D.side * k| := by
      have hp := side_pos D
      have a₁ := min_le_left (x μ - c) (D.side / 2 - (x μ - c))
      have a₂ := min_le_right (x μ - c) (D.side / 2 - (x μ - c))
      have b₁ := min_le_left (y μ - c) (D.side / 2 - (y μ - c))
      have b₂ := min_le_right (y μ - c) (D.side / 2 - (y μ - c))
      rcases le_or_gt k 0 with hn | hn
      · have h2 : (k : ℝ) ≤ 0 := by exact_mod_cast hn
        have h3 : D.side * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le h2
        refine le_trans ?_ (le_abs_self _)
        linarith
      · have h2 : (1 : ℝ) ≤ k := by exact_mod_cast hn
        have h3 : D.side ≤ D.side * k := by nlinarith
        refine le_trans ?_ (neg_le_abs _)
        linarith
    show distToHyperplane D .periodic μ c
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x) +
      distToHyperplane D .periodic μ c
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) ≤ _
    rw [e₁, e₂, ← ENNReal.ofReal_add hm₁ hm₂]
    exact ENNReal.ofReal_le_ofReal (hsum.trans hk)
theorem translateOpenHalf_holds (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ) :
    TranslateOpenHalf D P μ c := by
  have hv : ∀ t : ℝ, (t • LimitSpaces.stdBasisVec μ) μ = t := fun t => by
    simp [LimitSpaces.stdBasisVec]
  intro t
  cases P with
  | euclidean =>
    ext (x : Fin 4 → ℝ)
    constructor
    · rintro ⟨(y : Fin 4 → ℝ), hy, rfl⟩
      have hy' : y μ > c := hy
      show (y + t • LimitSpaces.stdBasisVec μ) μ > c + t
      rw [Pi.add_apply, hv]
      linarith
    · intro hx
      have hx' : x μ > c + t := hx
      refine ⟨x - t • LimitSpaces.stdBasisVec μ, ?_, ?_⟩
      · show (x - t • LimitSpaces.stdBasisVec μ) μ > c
        rw [Pi.sub_apply, hv]
        linarith
      · show x - t • LimitSpaces.stdBasisVec μ + t • LimitSpaces.stdBasisVec μ = x
        abel
  | periodic =>
    ext x
    constructor
    · rintro ⟨_, ⟨y, ⟨h0, h1⟩, rfl⟩, rfl⟩
      have h0' : 0 < y μ - c := h0
      have h1' : y μ - c < D.side / 2 := h1
      refine ⟨y + t • LimitSpaces.stdBasisVec μ, ⟨?_, ?_⟩, ?_⟩
      · show 0 < (y + t • LimitSpaces.stdBasisVec μ) μ - (c + t)
        rw [Pi.add_apply, hv]
        linarith
      · show (y + t • LimitSpaces.stdBasisVec μ) μ - (c + t) < D.side / 2
        rw [Pi.add_apply, hv]
        linarith
      · exact LimitSpaces.Ambient.periodic.proj_add D.toStandingParameters y _
    · rintro ⟨y, ⟨h0, h1⟩, rfl⟩
      have h0' : 0 < y μ - (c + t) := h0
      have h1' : y μ - (c + t) < D.side / 2 := h1
      refine ⟨D.projection (y - t • LimitSpaces.stdBasisVec μ),
        ⟨y - t • LimitSpaces.stdBasisVec μ, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · show 0 < (y - t • LimitSpaces.stdBasisVec μ) μ - c
        rw [Pi.sub_apply, hv]
        linarith
      · show (y - t • LimitSpaces.stdBasisVec μ) μ - c < D.side / 2
        rw [Pi.sub_apply, hv]
        linarith
      · have hadd := LimitSpaces.Ambient.periodic.proj_add D.toStandingParameters
          (y - t • LimitSpaces.stdBasisVec μ) (t • LimitSpaces.stdBasisVec μ)
        rw [sub_add_cancel] at hadd
        exact hadd.symm
theorem infSetDist_pos_of_compact (P : LimitSpaces.Ambient)
    (hd : FamilyTopology.IsMetricFunction (P.pointDist D.toStandingParameters)) (μ : Fin 4) (c : ℝ)
    {K : Set (P.Carrier D.toStandingParameters)} (hK : P.IsCompactSubset D.toStandingParameters K)
    (hpos : ∀ x ∈ K, 0 < distToHyperplane D P μ c x) :
    0 < P.infSetDist D.toStandingParameters K (hyperplane D P μ c) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [LimitSpaces.Ambient.infSetDist]
  have hr : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ distToHyperplane D P μ c x := by
    intro x hx
    obtain ⟨r, hr0, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hpos x hx)
    exact ⟨r, NNReal.coe_pos.2 (ENNReal.coe_pos.1 hr0), by
      rw [ENNReal.ofReal_coe_nnreal]
      exact hr1.le⟩
  choose! r hr0 hr1 using hr
  let B : P.Carrier D.toStandingParameters → Set (P.Carrier D.toStandingParameters) :=
    fun x => {y | P.pointDist D.toStandingParameters x y < r x / 2}
  obtain ⟨𝒰, hsub, hfin, hc⟩ := hK (B '' K)
    (by
      rintro _ ⟨x, -, rfl⟩ y hy
      refine ⟨r x / 2 - P.pointDist D.toStandingParameters x y, sub_pos.2 hy, fun w hw => ?_⟩
      have h₁ := hd.triangle x y w
      show P.pointDist D.toStandingParameters x w < r x / 2
      linarith)
    (by
      intro x hx
      refine ⟨B x, ⟨x, hx, rfl⟩, ?_⟩
      show P.pointDist D.toStandingParameters x x < r x / 2
      rw [(hd.eq_zero_iff x x).2 rfl]
      linarith [hr0 x hx])
  have hU : ∀ U ∈ 𝒰, ∃ x ∈ K, U = B x := fun U hmem => by
    obtain ⟨x, hx, rfl⟩ := hsub hmem
    exact ⟨x, hx, rfl⟩
  choose! ctr hctr hctrU using hU
  have hne' : 𝒰.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨U, hU, -⟩ := hc hx
    exact ⟨U, hU⟩
  obtain ⟨U₀, hU₀, hmin⟩ := Set.exists_min_image 𝒰 (fun U => r (ctr U)) hfin hne'
  have hε : 0 < r (ctr U₀) / 2 := by linarith [hr0 _ (hctr U₀ hU₀)]
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) ?_
  refine le_iInf₂ fun x hx => le_iInf₂ fun z hz => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨U, hU, hxU⟩ := hc hx
  have hxb : P.pointDist D.toStandingParameters (ctr U) x < r (ctr U) / 2 := by
    rw [hctrU U hU] at hxU
    exact hxU
  have hz₀ : r (ctr U) ≤ P.pointDist D.toStandingParameters (ctr U) z := by
    have h₁ := hr1 _ (hctr U hU)
    rw [distToHyperplane_eq_iInf] at h₁
    exact (ENNReal.ofReal_le_ofReal_iff (hd.nonneg _ _)).1 (h₁.trans (iInf₂_le z hz))
  have h₂ := hd.triangle (ctr U) x z
  have h₃ : r (ctr U₀) ≤ r (ctr U) := hmin U hU
  linarith
theorem infSetDist_le_distToHyperplane (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ)
    {K : Set (P.Carrier D.toStandingParameters)} {x : P.Carrier D.toStandingParameters}
    (hx : x ∈ K) :
    P.infSetDist D.toStandingParameters K (hyperplane D P μ c) ≤ distToHyperplane D P μ c x := by
  rw [distToHyperplane_eq_iInf]
  exact iInf₂_le (f := fun a _ => ⨅ y ∈ hyperplane D P μ c,
    ENNReal.ofReal (P.pointDist D.toStandingParameters a y)) x hx
theorem compactInOpenHalfStable_holds
    (hS : LimitSpaces.AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    (P : LimitSpaces.Ambient)
    (hd : FamilyTopology.IsMetricFunction (P.pointDist D.toStandingParameters)) (μ : Fin 4) (c : ℝ) :
    CompactInOpenHalfStable D P μ c := by
  intro K hK hsub
  refine ⟨infSetDist_pos_of_compact P hd μ c hK
    fun x hx => openHalfOffHyperplane_holds hS P μ c x (hsub hx), fun c' hc' x hx => ?_⟩
  have hlt := hc'.trans_le (infSetDist_le_distToHyperplane P μ c hx)
  cases P with
  | euclidean =>
    have hx' : (x : Fin 4 → ℝ) μ > c := hsub hx
    have e := euclidDistToHyperplane_holds (D := D) μ c x
    rw [e, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _),
      abs_of_pos (by linarith : 0 < (x : Fin 4 → ℝ) μ - c)] at hlt
    show (x : Fin 4 → ℝ) μ > c'
    linarith [le_abs_self (c' - c)]
  | periodic =>
    obtain ⟨y, ⟨h0, h1⟩, rfl⟩ := hsub hx
    have h0' : 0 < y μ - c := h0
    have h1' : y μ - c < D.side / 2 := h1
    have e := (torusDistToHyperplane_holds hS μ c y).2 h0' h1'
    have hlt' : ENNReal.ofReal |c' - c| <
        distToHyperplane D .periodic μ c
          (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) := hlt
    rw [e, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _), lt_min_iff, abs_lt] at hlt'
    obtain ⟨⟨h2, h3⟩, h4⟩ := hlt'
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · show 0 < y μ - c'
      linarith
    · show y μ - c' < D.side / 2
      linarith [neg_abs_le (c' - c)]
theorem compactInOpenHalfLowerLevels_holds (μ : Fin 4) (c : ℝ) :
    CompactInOpenHalfLowerLevels D μ c := by
  intro K _ hsub c' hc' x hx
  have hx' : (x : Fin 4 → ℝ) μ > c := hsub hx
  show (x : Fin 4 → ℝ) μ > c'
  linarith
theorem metricAndSymmetries_holds (hS : LimitSpaces.AmbientMetric.Claim)
    (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ) :
    MetricAndSymmetries D P μ c := by
  obtain ⟨hE, hC, hF, -, hT, hR, -⟩ := hS D.toStandingParameters P
  obtain ⟨-, hpres, hinv, hR₁⟩ := hR μ c
  have hinv' : Function.Involutive (P.reflect D.toStandingParameters μ c) := congrFun hinv
  refine ⟨hE.2.1, fun x y => ((hS D.toStandingParameters .periodic).1.1 x y).2, fun v => (hT v).2.1,
    hpres, hinv, fun Z _ f v => ⟨?_, (hT v).2.2.1 Z f⟩, fun 𝕜 _ f hf => ?_, fun f hf =>
      ⟨(hR₁ f hf).1, fun v => ((hT v).2.2.2 f hf).1, (hF f hf).2.2.2.2.2.2.1⟩⟩
  · have hZ := (hC.2 (hinv'.toPerm) hpres).2.2 Z f
    refine hZ.trans ?_
    exact (congrFun (Set.image_eq_preimage_of_inverse hinv'.leftInverse hinv'.rightInverse) _).symm
  · obtain ⟨C, hC₀, hlip⟩ := hf
    refine ⟨C, hC₀, fun x y => ?_⟩
    have h₁ := hlip (P.reflect D.toStandingParameters μ c x) (P.reflect D.toStandingParameters μ c y)
    rwa [hpres] at h₁
theorem isCompactSubset_image (P : LimitSpaces.Ambient)
    {t : P.Carrier D.toStandingParameters → P.Carrier D.toStandingParameters}
    (ht : LimitSpaces.AmbientMetric.IsDistPreserving D.toStandingParameters P t)
    (hsurj : Function.Surjective t) {K : Set (P.Carrier D.toStandingParameters)}
    (hK : P.IsCompactSubset D.toStandingParameters K) :
    P.IsCompactSubset D.toStandingParameters (t '' K) := by
  intro 𝒰 hopen hcov
  obtain ⟨𝒱, h𝒱, hfin, hc⟩ := hK ((fun U => t ⁻¹' U) '' 𝒰)
    (by
      rintro _ ⟨U, hU, rfl⟩ x hx
      obtain ⟨r, hr, hball⟩ := hopen U hU (t x) hx
      exact ⟨r, hr, fun y hy => hball (t y) (by rw [ht]; exact hy)⟩)
    (by
      intro x hx
      obtain ⟨U, hU, hxU⟩ := hcov ⟨x, hx, rfl⟩
      exact ⟨t ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩)
  refine ⟨(fun V => t '' V) '' 𝒱, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨U, hU, rfl⟩ := h𝒱 hV
    show t '' (t ⁻¹' U) ∈ 𝒰
    rwa [Set.image_preimage_eq _ hsurj]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hV, hxV⟩ := hc hx
    exact ⟨t '' V, ⟨V, hV, rfl⟩, x, hxV, rfl⟩
theorem gapsPositive_holds (hS : LimitSpaces.AmbientMetric.Claim)
    (P : LimitSpaces.Ambient) : GapsPositive D P := by
  have hC := (hS D.toStandingParameters P).2.1.1
  refine ⟨hC, fun X hX => ?_⟩
  have key : ∀ p : Fin X.length × Fin X.length, p ∈ Finset.univ.offDiag →
      0 < P.infSetDist D.toStandingParameters (P.closedSupport D.toStandingParameters (X.get p.1))
        (P.closedSupport D.toStandingParameters (X.get p.2)) := fun p hp =>
    hC _ _ (hX.1 p.1).2.1 (hX.1 p.2).2.1 (hX.2 (Finset.mem_offDiag.1 hp).2.2)
  cases P with
  | euclidean => exact (Finset.lt_inf_iff ENNReal.zero_lt_top).2 key
  | periodic => exact (Finset.lt_inf_iff ENNReal.zero_lt_top).2 key
theorem isSepLipList_iff (P : LimitSpaces.Ambient)
    (X : List (P.Carrier D.toStandingParameters → ℝ)) :
    IsSepLipList D P X ↔
      (∀ f ∈ X, f ∈ P.lipWithin D.toStandingParameters Set.univ) ∧
        X.Pairwise fun f g =>
          Disjoint (P.closedSupport D.toStandingParameters f)
            (P.closedSupport D.toStandingParameters g) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun f hf => ?_, List.pairwise_iff_get.2 fun i j hij => h₂ hij.ne⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hf
    exact h₁ i
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => h₁ _ (List.get_mem _ _), fun i j hij => ?_⟩
    have h₃ := List.pairwise_iff_get.1 h₂
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact h₃ i j hlt
    · exact (h₃ j i hlt).symm
theorem reflectAppendSepLip_holds (hS : LimitSpaces.AmbientMetric.Claim)
    (P : LimitSpaces.Ambient) (μ : Fin 4) (c : ℝ) :
    ReflectAppendSepLip D P μ c := by
  intro X Y hX hY hXs hYs
  obtain ⟨hX₁, hX₂⟩ := (isSepLipList_iff P X).1 hX
  obtain ⟨hY₁, hY₂⟩ := (isSepLipList_iff P Y).1 hY
  have ha := metricAndSymmetries_holds (D := D) hS P μ c
  obtain ⟨-, -, -, hpres, hinv, hsupp, hlip, -⟩ := ha
  have hinv' : Function.Involutive (P.reflect D.toStandingParameters μ c) := congrFun hinv
  have hsupp' : ∀ f : P.Carrier D.toStandingParameters → ℝ,
      P.closedSupport D.toStandingParameters (P.reflectFun D.toStandingParameters μ c f) =
        P.reflect D.toStandingParameters μ c '' P.closedSupport D.toStandingParameters f :=
    fun f => (hsupp ℝ f 0).1
  have hE := ((hS D.toStandingParameters .periodic).1)
  have hfar := reflectedPointsFar_holds (D := D) hE P μ c
  have hoff := openHalfOffHyperplane_holds (D := D) hE P μ c
  have hd := (hS D.toStandingParameters P).1.2.1
  refine (isSepLipList_iff P _).2 ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      obtain ⟨hl, hc, -⟩ := hX₁ f hf
      refine ⟨?_, ?_, Set.subset_univ _⟩
      · exact (isLipschitzMap_iff_isLip D P _).1
          (hlip ℝ f ((isLipschitzMap_iff_isLip D P f).2 hl))
      · rw [hsupp']
        exact isCompactSubset_image P hpres hinv'.surjective hc
    · exact hY₁ g hg
  · refine List.pairwise_append.2 ⟨?_, hY₂, ?_⟩
    · refine List.pairwise_map.2 (hX₂.imp ?_)
      intro f g hfg
      rw [hsupp', hsupp']
      exact (Set.disjoint_image_iff hinv'.injective).2 hfg
    · intro g hg h hh
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      rw [hsupp', Set.disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ hx
      have hy₁ := (hXs f hf).2 hy
      have hx₁ := (hYs h hh).2 hx
      have h₁ := hfar _ hx₁ _ hy₁
      rw [(hd.eq_zero_iff _ _).2 rfl] at h₁
      have h₂ := hoff _ hy₁
      simp only [ENNReal.ofReal_zero, nonpos_iff_eq_zero, add_eq_zero] at h₁
      exact h₂.ne' h₁.2
end Sides
theorem Sides.hyperplaneSidesClaim_holds (h₁ : LimitSpaces.AmbientMetric.Claim)
    (h₂ : ReflectionPositivity.AxisMirror.ReflectAppendSeparated) : Sides.HyperplaneSidesClaim := by
  intro D μ c
  have hE := (h₁ D.toStandingParameters .periodic).1
  refine ⟨fun P => ?_, Sides.euclidDistToHyperplane_holds μ c,
    Sides.torusDistToHyperplane_holds hE μ c,
    Sides.compactInOpenHalfLowerLevels_holds μ c,
    fun E X Y hX hY => (h₂ D E μ c X Y hX hY).2⟩
  exact ⟨Sides.metricAndSymmetries_holds h₁ P μ c,
    Sides.openHalfOffHyperplane_holds hE P μ c,
    Sides.reflectedPointsFar_holds hE P μ c,
    Sides.compactInOpenHalfStable_holds hE P (h₁ D.toStandingParameters P).1.2.1 μ c,
    Sides.gapsPositive_holds h₁ P,
    Sides.reflectAppendSepLip_holds h₁ P μ c,
    Sides.translateOpenHalf_holds P μ c⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror
end
