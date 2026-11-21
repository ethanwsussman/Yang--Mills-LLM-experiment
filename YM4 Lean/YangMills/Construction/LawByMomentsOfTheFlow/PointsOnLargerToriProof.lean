import YangMills.Construction.HullsInEveryVolume.EachTowerHasARuleOfTheNoises
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtTheFarLevel
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreSized
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open TorusFields TorusFrame TorusLumps WeightedResponses ResponseInTheExpansion LevelTestFunctions ChainNoise FieldHaar
namespace MomentLaw
section Parameters
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_imp {Q Q' : MomentParameters → Prop} (h : ForAllHullParameters Q)
    (f : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.table.floorMin ≤ Λ.floor → Q Λ → Q' Λ) :
    ForAllHullParameters Q' := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ Tb.floorMin, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ d₁ ((le_max_right _ _).trans hy)
    (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end Parameters
section Side
variable {k : ℕ}
private theorem circleRep_add_mul {c : ℝ} (hc : c ≠ 0) (v : ℝ) (j : ℤ) : circleRep c (v + c * j) = circleRep c v := by
  unfold circleRep
  have e : (v + c * j) / c = v / c + j := by field_simp
  rw [e, round_add_intCast]
  push_cast
  ring
private theorem circleRep_of_small {c v : ℝ} (hc : 0 < c) (hv : 2 * |v| < c) : circleRep c v = v := by
  unfold circleRep
  have h : round (v / c) = 0 := by
    rw [round_eq_zero_iff]
    have h1 := abs_lt.mp (show |v| < c / 2 by linarith)
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hc]
      linarith [h1.1]
    · rw [div_lt_iff₀ hc]
      linarith [h1.2]
  rw [h]
  simp
private theorem two_abs_circleRep_le {c : ℝ} (hc : 0 < c) (v : ℝ) : 2 * |circleRep c v| ≤ c := by
  have h := abs_sub_round (v / c)
  have e : circleRep c v = c * (v / c - round (v / c)) := by
    unfold circleRep
    field_simp
  rw [e, abs_mul, abs_of_pos hc]
  nlinarith
private theorem exists_ne_zero_larger (P : LevelData k) (L m : ℕ) [NeZero L] (hL : 2 ≤ L) (hm : P.sideExponent < m) (i : Fin k)
    (h : ∃ p : OrientedPlaquette (P.period L * L ^ P.windowLevel), P.testWeight L i _ p.1 ≠ 0) :
    ∃ p : OrientedPlaquette (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel),
      ({ P with sideExponent := m } : LevelData k).testWeight L i _ p.1 ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := h
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (P.period L : ℝ) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = (({ P with sideExponent := m } : LevelData k).period L : ℝ) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (L : ℝ) ^ P.windowLevel := ⟨_, rfl⟩
  have hD0 : 0 < D := hD ▸ pow_pos hLr _
  have hc0 : 0 < c := by
    rw [hc]
    unfold LevelData.period
    push_cast
    positivity
  have hcc : 2 * c ≤ c' := by
    rw [hc, hc']
    unfold LevelData.period
    push_cast
    have h1 : (L : ℝ) ^ (P.sideExponent + 1) ≤ (L : ℝ) ^ m := pow_le_pow_right₀ (by linarith) hm
    have h2 : (L : ℝ) ^ (P.sideExponent + 1) = (L : ℝ) ^ P.sideExponent * L := pow_succ _ _
    have h3 : 0 < (L : ℝ) ^ P.sideExponent := pow_pos hLr _
    nlinarith
  have hc'0 : 0 < c' := by linarith
  have hN' : NeZero (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel) :=
    ⟨by
      have h1 : 0 < ({ P with sideExponent := m } : LevelData k).period L := by
        unfold LevelData.period
        have : 0 < L ^ m := pow_pos (by omega) _
        simpa using this
      have h2 : 0 < L ^ P.windowLevel := pow_pos (by omega) _
      exact (Nat.mul_pos h1 h2).ne'⟩
  obtain ⟨X, hX⟩ : ∃ X : Fin 4 → ℝ, X = fun a => barycenterCoord p.1 a / (L : ℝ) ^ P.windowLevel - P.center a := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 4 → ℤ, j = fun a => round (X a / c) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → ℤ, e = fun a => ((p.1.1 a).val : ℤ) - ((P.period L * L ^ P.windowLevel : ℕ) : ℤ) * j a := ⟨_, rfl⟩
  refine ⟨⟨(fun a => ((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel)), p.1.2), p.2⟩, ?_⟩
  have key : ∀ a : Fin 4, circleRep (({ P with sideExponent := m } : LevelData k).period L)
      (barycenterCoord ((fun a => ((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel))), p.1.2) a / (L : ℝ) ^ P.windowLevel - P.center a) =
      circleRep (P.period L) (barycenterCoord p.1 a / (L : ℝ) ^ P.windowLevel - P.center a) := by
    intro a
    obtain ⟨N', hN'e⟩ : ∃ N' : ℕ, N' = ({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel := ⟨_, rfl⟩
    have hval : ((((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel)).val : ℕ) : ℤ) =
        e a - ((({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel : ℕ) : ℤ) *
          (e a / ((({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel : ℕ) : ℤ)) := by
      rw [ZMod.val_intCast]
      exact Int.emod_def _ _
    obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, κ = e a / ((({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel : ℕ) : ℤ) := ⟨_, rfl⟩
    rw [← hκ] at hval
    have hvalr : ((((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel)).val : ℕ) : ℝ) =
        ((p.1.1 a).val : ℝ) - c * D * j a - c' * D * κ := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hval
      simp only [Int.cast_natCast] at this
      rw [this, he]
      push_cast
      rw [hc, hc', hD]
    have hb : barycenterCoord ((fun a => ((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel))), p.1.2) a / (L : ℝ) ^ P.windowLevel - P.center a =
        circleRep c (X a) + c' * ((-κ : ℤ) : ℝ) := by
      unfold barycenterCoord
      rw [hvalr]
      unfold circleRep
      rw [hX, ← hD]
      have hjj : (round ((barycenterCoord p.1 a / D - P.center a) / c) : ℝ) = (j a : ℝ) := by
        rw [hj, hX, hD]
      rw [hjj]
      unfold barycenterCoord
      push_cast
      field_simp
      ring
    have hsm : 2 * |circleRep c (X a)| < c' := by
      have := two_abs_circleRep_le hc0 (X a)
      linarith
    have hfin : circleRep c' (circleRep c (X a) + c' * ((-κ : ℤ) : ℝ)) = circleRep c (X a) := by
      rw [circleRep_add_mul hc'0.ne', circleRep_of_small hc'0 hsm]
    rw [hb, ← hc', hfin, hc, hX]
  have heq : ({ P with sideExponent := m } : LevelData k).testWeight L i _
      ((fun a => ((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel))), p.1.2) = P.testWeight L i _ p.1 := by
    have e' : (fun a => (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel * circleRep (({ P with sideExponent := m } : LevelData k).period L)
        (barycenterCoord ((fun a => ((e a : ℤ) : ZMod (({ P with sideExponent := m } : LevelData k).period L * L ^ P.windowLevel))), p.1.2) a / (L : ℝ) ^ P.windowLevel - P.center a)) =
        fun a => (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel * circleRep (P.period L) (barycenterCoord p.1 a / (L : ℝ) ^ P.windowLevel - P.center a) := by
      funext a
      rw [key a]
    exact congrArg (fun v : Fin 4 → ℝ => P.fn i (WithLp.toLp 2 v)) e'
  show ({ P with sideExponent := m } : LevelData k).testWeight L i _ _ ≠ 0
  rw [heq]
  exact hp
private theorem supAdmissible_larger (P : LevelData k) (L : ℕ) [NeZero L] (hL : 2 ≤ L) (R d : ℝ) (h : P.SupAdmissible L R d)
    (m : ℕ) (hm : P.sideExponent < m) : ({ P with sideExponent := m } : LevelData k).SupAdmissible L R d := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  refine ⟨h.isSupTestFamily, h.scaleLevel_le, ?_, h.center_mem_lattice, fun i => exists_ne_zero_larger P L m hL hm i (h.exists_ne_zero i)⟩
  refine h.support_small.trans ?_
  have h1 : (P.period L : ℝ) ≤ (({ P with sideExponent := m } : LevelData k).period L : ℝ) := by
    unfold LevelData.period
    push_cast
    have : (L : ℝ) ^ P.sideExponent ≤ (L : ℝ) ^ m := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) hm.le
    linarith
  have h2 : 0 < (L : ℝ) ^ P.windowLevel := pow_pos hLr _
  show (P.period L : ℝ) / 4 * (L : ℝ) ^ P.windowLevel ≤ (({ P with sideExponent := m } : LevelData k).period L : ℝ) / 4 * (L : ℝ) ^ P.windowLevel
  nlinarith
end Side
section Bounds
variable {Λ : MomentParameters}
private theorem kappa_congr (S : MomentPoint Λ) (u : ℕ) (i : Fin Λ.k) {n n' : ℕ} [NeZero n] [NeZero n'] (h : n = n') :
    S.kappa u n i = S.kappa u n' i := by
  subst h
  rfl
private theorem sideAtLevel_eq (S : MomentPoint Λ) (u : ℕ) : S.sideAtLevel u = S.levelSide u := by apply _root_.YangMills.SharedProofs.p7138 <;> assumption
private theorem lastSeparated_le_scaleLevel (S : MomentPoint Λ) : S.lastSeparated ≤ S.data.scaleLevel := by apply _root_.YangMills.SharedProofs.p10799 <;> assumption
private theorem abs_curvatureObservable_le (S : MomentPoint Λ) (i : Fin Λ.k) (N : ℕ) [NeZero N]
    (hN : N = S.data.sideAt Λ.stepParams.side 0) (W : TorusField N) :
    |curvatureObservable (S.weight i N) W| ≤ 32 * ((S.data.supportSites Λ.stepParams.side 0 i).card : ℝ) := by
  classical
  subst hN
  obtain ⟨A, hA⟩ : ∃ A, A = S.data.supportSites Λ.stepParams.side 0 i := ⟨_, rfl⟩
  rw [← hA]
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Finset (TorusPlaquette (S.data.sideAt Λ.stepParams.side 0)),
      Bs = A ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := ⟨_, rfl⟩
  have hmem : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))),
      S.weight i _ p ≠ 0 → p ∈ Bs := by
    intro p hp hne
    have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
    rw [hBs, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hA]
    unfold LevelData.supportSites weightSupportSites
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, ⟨hlt, p.1, ?_, ?_⟩, hne⟩
    · exact List.mem_cons_self
    · exact Finset.mem_singleton_self _
  have hterm : ∀ p, |S.weight i (S.data.sideAt Λ.stepParams.side 0) p * plaquetteEnergyOf W p| ≤ 2 := by
    intro p
    rw [abs_mul]
    have h1 : |S.weight i (S.data.sideAt Λ.stepParams.side 0) p| ≤ 1 := S.supAdmissible.isSupTestFamily.abs_le_one i _
    have e : plaquetteEnergyOf W p = plaquetteEnergy W p.1 p.2.1 p.2.2 := rfl
    have h2 : |plaquetteEnergyOf W p| ≤ 2 := by
      rw [e, abs_of_nonneg (plaquetteEnergy_nonneg W p.1 p.2.1 p.2.2)]
      exact plaquetteEnergy_le_two W p.1 p.2.1 p.2.2
    nlinarith [abs_nonneg (S.weight i (S.data.sideAt Λ.stepParams.side 0) p), abs_nonneg (plaquetteEnergyOf W p)]
  have hle : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))),
      |S.weight i (S.data.sideAt Λ.stepParams.side 0) p * plaquetteEnergyOf W p| ≤ if p ∈ Bs then (2 : ℝ) else 0 := by
    intro p hp
    by_cases h0 : S.weight i (S.data.sideAt Λ.stepParams.side 0) p = 0
    · rw [h0, zero_mul, abs_zero]
      split_ifs <;> norm_num
    · rw [if_pos (hmem p hp h0)]
      exact hterm p
  unfold curvatureObservable
  calc |∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))),
          S.weight i (S.data.sideAt Λ.stepParams.side 0) p * plaquetteEnergyOf W p|
      ≤ ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))),
          |S.weight i (S.data.sideAt Λ.stepParams.side 0) p * plaquetteEnergyOf W p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))),
          if p ∈ Bs then (2 : ℝ) else 0 := Finset.sum_le_sum hle
    _ = ∑ _p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))) ∩ Bs, (2 : ℝ) :=
        Finset.sum_ite_mem _ _ _
    _ ≤ 32 * (A.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have h1 : ((plaquettesIn (Finset.univ : Finset (TorusSite (S.data.sideAt Λ.stepParams.side 0))) ∩ Bs).card : ℝ) ≤
          (Bs.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      have h2 : (Bs.card : ℝ) = (A.card : ℝ) * 16 := by
        rw [hBs, Finset.card_product]
        simp
      rw [h2] at h1
      linarith
private theorem abs_le_of_integral_eq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (O G F N : Ω → ℝ)
    (κ a e bO c : ℝ) (hOm : AEStronglyMeasurable O μ) (hO : ∀ w, |O w| ≤ bO) (hF : ∀ᵐ w ∂μ, |F w| ≤ a * N w)
    (hG : ∀ᵐ w ∂μ, |G w - F w| ≤ e * N w) (hat : ∫ w, (O w - κ) ∂μ = ∫ w, G w ∂μ) (hNi : Integrable N μ)
    (hNc : ∫ w, N w ∂μ ≤ c) (hae : 0 ≤ a + e) : |κ| ≤ bO + (a + e) * c := by
  have hOi : Integrable O μ := Integrable.of_bound hOm bO (Filter.Eventually.of_forall hO)
  have e1 : ∫ w, (O w - κ) ∂μ = ∫ w, O w ∂μ - κ := by
    rw [integral_sub hOi (integrable_const _)]
    simp
  have hG' : ∀ᵐ w ∂μ, ‖G w‖ ≤ (a + e) * N w := by
    filter_upwards [hF, hG] with w h1 h2
    have h3 : |G w| ≤ |G w - F w| + |F w| := by
      have := abs_add_le (G w - F w) (F w)
      simpa using this
    rw [Real.norm_eq_abs]
    linarith
  have h2 : ‖∫ w, G w ∂μ‖ ≤ ∫ w, (a + e) * N w ∂μ := norm_integral_le_of_norm_le (hNi.const_mul _) hG'
  rw [integral_const_mul, Real.norm_eq_abs] at h2
  have h3 : |∫ w, O w ∂μ| ≤ bO := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := O) (C := bO) (Filter.Eventually.of_forall hO)
    simpa using this
  have h4 : (a + e) * ∫ w, N w ∂μ ≤ (a + e) * c := mul_le_mul_of_nonneg_left hNc hae
  have h5 : κ = ∫ w, O w ∂μ - ∫ w, G w ∂μ := by
    rw [← hat, e1]
    ring
  rw [h5]
  have h6 := abs_sub (∫ w, O w ∂μ) (∫ w, G w ∂μ)
  linarith
private theorem measurable_curvatureObservable {N : ℕ} [NeZero N] (h : PlaquetteWeight N) :
    Measurable (curvatureObservable h) := by
  unfold curvatureObservable
  refine Finset.measurable_sum _ fun p _ => ?_
  exact ((continuous_plaquetteEnergy p.1 p.2.1 p.2.2).measurable).const_mul _
private theorem measurable_bottomField {ℓ : StepParameters} (s : ℕ) : ∀ n : ℕ, Measurable (bottomField ℓ s n) := by apply _root_.YangMills.SharedProofs.p4086 <;> assumption
private theorem separation_sum_le (L : ℝ) (hL : 1 ≤ L) (rt : ℝ) (hrt : 0 < rt) (g : ℕ → ℕ) (c₁ c₂ : ℝ) (s t : ℕ)
    (hts : t ≤ s) :
    c₁ * ∑ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) ≤
      |c₁| * ((s : ℝ) * L ^ (|c₂| * (s : ℝ))) := by
  have hterm : ∀ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) ≤
      L ^ (|c₂| * (s : ℝ)) := by
    intro u hu
    have hu' : (u : ℝ) ≤ (s : ℝ) := by
      have := Finset.mem_range.mp hu
      exact_mod_cast (by omega : u ≤ s)
    have h1 : c₂ * ((s : ℝ) - (u : ℝ)) ≤ |c₂| * (s : ℝ) := by
      have h2 : c₂ * ((s : ℝ) - (u : ℝ)) ≤ |c₂| * ((s : ℝ) - (u : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      have h3 : |c₂| * ((s : ℝ) - (u : ℝ)) ≤ |c₂| * (s : ℝ) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      linarith
    have h4 : L ^ (c₂ * ((s : ℝ) - (u : ℝ))) ≤ L ^ (|c₂| * (s : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL h1
    have h5 : Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ rt * (g u : ℝ) / 2 ^ 8 := by positivity
      linarith
    have h6 : 0 ≤ L ^ (c₂ * ((s : ℝ) - (u : ℝ))) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have hX : 0 ≤ L ^ (|c₂| * (s : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hsum : ∑ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) ≤
      (s : ℝ) * L ^ (|c₂| * (s : ℝ)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast hts
    exact mul_le_mul_of_nonneg_right this hX
  have hsum0 : 0 ≤ ∑ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) :=
    Finset.sum_nonneg fun u _ => mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  calc c₁ * ∑ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8))
      ≤ |c₁| * ∑ u ∈ Finset.range t, L ^ (c₂ * ((s : ℝ) - (u : ℝ))) * Real.exp (-(rt * (g u : ℝ) / 2 ^ 8)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
    _ ≤ |c₁| * ((s : ℝ) * L ^ (|c₂| * (s : ℝ))) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
end Bounds
section Noises
variable (ℓ : StepParameters)
private theorem measurePreserving_pi_perm {J : Type} [Fintype J] (e : J ≃ J) :
    MeasurePreserving (fun (x : J → unitInterval) j => x (e j)) (Measure.pi fun _ : J => (volume : Measure unitInterval))
      (Measure.pi fun _ : J => (volume : Measure unitInterval)) := by apply _root_.YangMills.SharedProofs.p46286 <;> assumption
private theorem isProbability_chainNoiseLaw : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac () : Measure Unit)
    infer_instance
  | s + 1, n, _ => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := isProbability_chainNoiseLaw s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    show IsProbabilityMeasure ((chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n))
    infer_instance
private theorem measurePreserving_noiseTranslate : ∀ (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ),
    MeasurePreserving (noiseTranslate ℓ u n h) (chainNoiseLaw ℓ u n) (chainNoiseLaw ℓ u n)
  | 0, n, _, h => MeasurePreserving.id (chainNoiseLaw ℓ 0 n)
  | u + 1, n, _, h => by
    letI := instMeasurableSpaceChainNoise ℓ u (n * ℓ.side)
    haveI := isProbability_chainNoiseLaw ℓ u (n * ℓ.side)
    have h0 := measurePreserving_noiseTranslate u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i)
    have h1 := measurePreserving_pi_perm (J := TorusSite n) (Equiv.addRight (siteOfInt h))
    have h2 := measurePreserving_pi_perm (J := TorusBond n) ((Equiv.addRight (siteOfInt h)).prodCongr (Equiv.refl _))
    have h3 := measurePreserving_pi_perm (J := TorusBond (n * ℓ.side))
      ((Equiv.addRight (siteOfInt fun i => (ℓ.side : ℤ) * h i)).prodCongr (Equiv.refl _))
    exact h0.prod (h1.prod (h2.prod h3))
private theorem bottomField_chain {ℓ : StepParameters} (rule : NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) :
    ∀ (s n : ℕ) [NeZero n] (W : TorusField (fineSide ℓ.side s n)) (U : ChainNoise.ChainNoise ℓ s n),
      bottomField ℓ s n (rule.chain T s n W U) = W
  | 0, _, _, _, _ => rfl
  | s + 1, n, _, W, U => bottomField_chain rule T s (n * ℓ.side) W U.1
end Noises
section Translation
variable {m : ℕ} [NeZero m]
private theorem measurePreserving_translate_haar (hH : HaarInvariantUnderSymmetries) (u : TorusSite m) :
    MeasurePreserving (TorusFields.translate u) (fieldHaar m) (fieldHaar m) := by
  let v : Fin 4 → ℤ := fun i => -(((u i).val : ℕ) : ℤ)
  let g : TorusIsometry := ⟨1, fun _ => 1, v, fun _ => Or.inl rfl⟩
  obtain ⟨Ψ, hΨ, hc⟩ := (hH m).2 g
  have e : Ψ = TorusFields.translate u := by
    funext W x k
    have h1 := hc W (x + u) k
    have hs : g.axisSign (g.axisPerm.symm k) = 1 := rfl
    rw [if_pos hs] at h1
    have hd : g.axisPerm.symm k = k := rfl
    rw [hd] at h1
    have hx : g.mapSite (x + u) = x := by
      funext i
      simp [g, v, TorusIsometry.mapSite]
    rw [hx] at h1
    exact h1
  exact e ▸ hΨ
private theorem wilsonAction_translate (u : TorusSite m) (W : TorusField m) :
    wilsonAction Finset.univ (TorusFields.translate u W) = wilsonAction Finset.univ W := by apply _root_.YangMills.SharedProofs.p7329 <;> assumption
private theorem measurePreserving_translate_wilson (hH : HaarInvariantUnderSymmetries) (β : ℝ) (u : TorusSite m) :
    MeasurePreserving (TorusFields.translate u) (wilsonLaw β m) (wilsonLaw β m) := by
  have hS := measurePreserving_translate_haar hH u
  obtain ⟨ρ, hρ⟩ : ∃ ρ : TorusField m → ENNReal, ρ = fun W => ENNReal.ofReal (Real.exp (-β * wilsonAction Finset.univ W) /
      ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar m)) := ⟨_, rfl⟩
  have hρm : Measurable ρ := by
    rw [hρ]
    refine ENNReal.measurable_ofReal.comp (Measurable.div_const ?_ _)
    refine Real.measurable_exp.comp (Measurable.const_mul ?_ _)
    unfold wilsonAction
    exact Finset.measurable_sum _ fun p _ => (continuous_plaquetteEnergy p.1 p.2.1 p.2.2).measurable
  have hρs : ∀ W, ρ (TorusFields.translate u W) = ρ W := fun W => by
    rw [hρ]
    simp only [wilsonAction_translate]
  have hlaw : wilsonLaw β m = (fieldHaar m).withDensity ρ := by
    rw [hρ]
    rfl
  refine ⟨hS.measurable, ?_⟩
  rw [hlaw]
  ext s hs
  rw [Measure.map_apply hS.measurable hs, withDensity_apply _ (hS.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (hS.measurable hs), ← lintegral_indicator hs]
  rw [← hS.lintegral_comp (hρm.indicator hs)]
  refine lintegral_congr fun W => ?_
  by_cases hW : TorusFields.translate u W ∈ s
  · rw [Set.indicator_of_mem (show W ∈ TorusFields.translate u ⁻¹' s from hW), Set.indicator_of_mem hW, hρs]
  · rw [Set.indicator_of_notMem (show W ∉ TorusFields.translate u ⁻¹' s from hW), Set.indicator_of_notMem hW]
end Translation
section Moments
variable {Λ : MomentParameters}
private theorem length_flatMap_replicate {ι : Type} (l : List ι) (q : ℕ) :
    (l.flatMap fun j => List.replicate q j).length = l.length * q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_replicate, List.length_cons]
    ring
private theorem prod_flatMap_replicate {ι : Type} (l : List ι) (q : ℕ) (g : ι → ℝ) :
    ((l.flatMap fun j => List.replicate q j).map g).prod = (l.map fun j => g j ^ q).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate, List.prod_replicate, List.map_cons,
      List.prod_cons]
private theorem lastSeparated_moments (S : MomentPoint Λ)
    [IsProbabilityMeasure (S.law S.lastSeparated (S.levelSide S.lastSeparated))] (a c₀ : ℝ) (ha : 0 ≤ a)
    (hSz : ∀ i : Fin Λ.k, AEMeasurable (fun w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
      ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
        1 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∧
        |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
          a * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
    (hM : ∀ p : ℕ, 1 ≤ p → ∀ J : List (Fin Λ.k), J.length = p →
      ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal (c₀ ^ p * (p.factorial : ℝ) ^ 6))
    (B : Finset (Fin Λ.k)) (q : ℕ) :
    AEMeasurable (fun w => ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
    ∫⁻ w, ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
      ENNReal.ofReal (a ^ (B.card * q) * (1 + |c₀| ^ (B.card * q) * (((B.card * q).factorial : ℝ)) ^ 6)) := by
  classical
  refine ⟨Finset.aemeasurable_fun_prod _ fun i _ => (hSz i).1, ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J : List (Fin Λ.k), J = B.toList.flatMap fun j => List.replicate q j := ⟨_, rfl⟩
  have hlen : J.length = B.card * q := by
    rw [hJ, length_flatMap_replicate, Finset.length_toList]
  have hall : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), ∀ i : Fin Λ.k,
      1 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∧
      |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
        a * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) :=
    ae_all_iff.mpr fun i => (hSz i).2
  have hprod : ∀ w, (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod =
      ∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ^ q := by
    intro w
    rw [hJ, prod_flatMap_replicate, Finset.prod_map_toList]
  have hpt : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
      ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q) ≤
        ENNReal.ofReal (a ^ (B.card * q)) *
          ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod := by
    filter_upwards [hall] with w hw
    rw [← ENNReal.ofReal_mul (pow_nonneg ha _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hprod, Finset.abs_prod, ← Finset.prod_pow]
    have h1 : ∀ i ∈ B, |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q ≤
        a ^ q * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ^ q := by
      intro i _
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hw i).2 q
    refine (Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _) h1).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, mul_comm q B.card]
  have hint : ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
      ENNReal.ofReal (1 + |c₀| ^ (B.card * q) * (((B.card * q).factorial : ℝ)) ^ 6) := by
    rcases Nat.eq_zero_or_pos (B.card * q) with h0 | hp
    · have hJ0 : J = [] := List.length_eq_zero_iff.mp (hlen.trans h0)
      rw [hJ0]
      simp only [List.map_nil, List.prod_nil, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 0 ≤ |c₀| ^ (B.card * q) * (((B.card * q).factorial : ℝ)) ^ 6 := by positivity
      linarith
    · refine (hM _ hp J hlen).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : c₀ ^ (B.card * q) ≤ |c₀| ^ (B.card * q) := by
        refine (le_abs_self _).trans ?_
        rw [abs_pow]
      have h2 : (0 : ℝ) ≤ (((B.card * q).factorial : ℝ)) ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_right h1 h2
      linarith
  calc ∫⁻ w, ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))
      ≤ ∫⁻ w, ENNReal.ofReal (a ^ (B.card * q)) *
          ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (a ^ (B.card * q)) *
          ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (a ^ (B.card * q)) *
          ENNReal.ofReal (1 + |c₀| ^ (B.card * q) * (((B.card * q).factorial : ℝ)) ^ 6) := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul (pow_nonneg ha _)).symm
private theorem lastSeparated_moments_of_eq (S : MomentPoint Λ) (n : ℕ) [NeZero n] (hn : n = S.levelSide S.lastSeparated)
    (C : ℝ) (B : Finset (Fin Λ.k)) (q : ℕ)
    (h : AEMeasurable (fun w => ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
      ∫⁻ w, ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal C) :
    AEMeasurable (fun w => ∏ i ∈ B, S.supportTotal S.lastSeparated n i (S.state S.lastSeparated n w)) (S.law S.lastSeparated n) ∧
      ∫⁻ w, ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated n i (S.state S.lastSeparated n w)| ^ q)
        ∂(S.law S.lastSeparated n) ≤ ENNReal.ofReal C := by
  subst hn
  exact h
private theorem markedSampleLaw_cast {ℓ : StepParameters} (T : WeightedResponses.StageTower ℓ) (β : ℝ) (n : ℕ) [NeZero n]
    {K K' : ℕ} (e : K = K') :
    Measurable (fun w : MarkedSample ℓ K n => e ▸ w) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => e ▸ w) = markedSampleLaw T β K' n := by
  subst e
  exact ⟨measurable_id, Measure.map_id⟩
private theorem law_sampleAtLevel (hB : sampleBelowLawStatement) (hFit : Λ.stepParams.Admissible) (S : MomentPoint Λ) (u : ℕ)
    (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by
  obtain ⟨hc1, hc2⟩ := markedSampleLaw_cast S.tower S.β (S.data.period Λ.stepParams.side) (Nat.add_sub_of_le hu).symm
  obtain ⟨hd1, hd2⟩ := (hB Λ.stepParams hFit hFit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β S.coeff).1 u
    (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨hd1.comp hc1, ?_⟩
  have e : S.sampleAtLevel u hu = sampleBelow Λ.stepParams u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) ∘
      (fun w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) => (Nat.add_sub_of_le hu).symm ▸ w) := rfl
  rw [e, ← Measure.map_map hd1 hc1]
  show ((markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)).map _).map _ = _
  rw [hc2]
  exact hd2
private theorem responseProduct_moments (hB : sampleBelowLawStatement) (hDr : ruleDrawsChainStatement)
    (hFit : Λ.stepParams.Admissible) (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (hr : rule.IsAdmissible S.tower)
    (h1 : Λ.stepParams.side ∣ S.data.period Λ.stepParams.side) (h2 : 64 ≤ S.data.period Λ.stepParams.side)
    (B : Finset (Fin Λ.k)) (q : ℕ) (C : ℝ)
    (h : AEMeasurable (fun w => ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
      ∫⁻ w, ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ^ q) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal C) :
    AEMeasurable (fun ω => responseProduct B S (S.sampleOf rule ω)) S.sampleLaw ∧
      ∫⁻ ω, ENNReal.ofReal (|responseProduct B S (S.sampleOf rule ω)| ^ q) ∂S.sampleLaw ≤ ENNReal.ofReal C := by
  obtain ⟨hm, hmap⟩ := hDr Λ.stepParams hFit S.tower rule S.β S.isCutoff S.marksMeasurable hr S.data.windowLevel
    (S.data.period Λ.stepParams.side) h1 h2
  obtain ⟨hd, hdmap⟩ := law_sampleAtLevel hB hFit S S.lastSeparated S.lastSeparated_le
  have hDm : Measurable fun ω : S.SampleSpace => S.sampleAtLevel S.lastSeparated S.lastSeparated_le (S.sampleOf rule ω) :=
    hd.comp hm
  have hDmap : S.sampleLaw.map (fun ω : S.SampleSpace => S.sampleAtLevel S.lastSeparated S.lastSeparated_le (S.sampleOf rule ω)) =
      S.law S.lastSeparated (S.sideAtLevel S.lastSeparated) := by
    have e : (fun ω : S.SampleSpace => S.sampleAtLevel S.lastSeparated S.lastSeparated_le (S.sampleOf rule ω)) =
        S.sampleAtLevel S.lastSeparated S.lastSeparated_le ∘
          fun p : S.SampleSpace => rule.chain S.tower S.data.windowLevel (S.data.period Λ.stepParams.side) p.1 p.2 := rfl
    rw [e, ← Measure.map_map hd hm]
    have e2 : S.sampleLaw.map (fun p : S.SampleSpace => rule.chain S.tower S.data.windowLevel (S.data.period Λ.stepParams.side) p.1 p.2) =
        S.law S.data.windowLevel (S.data.period Λ.stepParams.side) := hmap
    rw [e2]
    exact hdmap
  obtain ⟨g1, g2⟩ := lastSeparated_moments_of_eq S (S.sideAtLevel S.lastSeparated) (sideAtLevel_eq S S.lastSeparated) C B q h
  rw [← hDmap] at g1 g2
  refine ⟨g1.comp_measurable hDm, ?_⟩
  have hg : AEMeasurable (fun w => ENNReal.ofReal (|∏ i ∈ B, S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.state S.lastSeparated (S.sideAtLevel S.lastSeparated) w)| ^ q))
      (S.sampleLaw.map fun ω : S.SampleSpace => S.sampleAtLevel S.lastSeparated S.lastSeparated_le (S.sampleOf rule ω)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((continuous_abs.measurable.comp_aemeasurable g1).pow_const q)
  rw [lintegral_map' hg hDm.aemeasurable] at g2
  exact g2
private theorem bottomProduct_moments (S : MomentPoint Λ) [IsProbabilityMeasure S.sampleLaw] (rule : NoiseRule Λ.stepParams)
    (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (q : ℕ) (bO : ℝ)
    (hO : ∀ i W, |curvatureObservable (S.weight i (fineSide Λ.stepParams.side S.data.windowLevel
      (S.data.period Λ.stepParams.side))) W| ≤ bO) :
    AEMeasurable (fun ω => bottomProduct c B S (S.sampleOf rule ω)) S.sampleLaw ∧
      ∫⁻ ω, ENNReal.ofReal (|bottomProduct c B S (S.sampleOf rule ω)| ^ q) ∂S.sampleLaw ≤
        ENNReal.ofReal ((∏ i ∈ B, (bO + |c i|)) ^ q) := by
  have e : ∀ ω : S.SampleSpace, bottomProduct c B S (S.sampleOf rule ω) =
      ∏ i ∈ B, (curvatureObservable (S.weight i (fineSide Λ.stepParams.side S.data.windowLevel
        (S.data.period Λ.stepParams.side))) ω.1 - c i) := by
    intro ω
    unfold bottomProduct MomentPoint.sampleOf
    rw [bottomField_chain]
  have hm : Measurable fun ω : S.SampleSpace => ∏ i ∈ B, (curvatureObservable (S.weight i (fineSide Λ.stepParams.side
      S.data.windowLevel (S.data.period Λ.stepParams.side))) ω.1 - c i) :=
    Finset.measurable_prod _ fun i _ => ((measurable_curvatureObservable _).comp measurable_fst).sub_const _
  refine ⟨(funext e ▸ hm).aemeasurable, ?_⟩
  have hb : ∀ ω : S.SampleSpace, ENNReal.ofReal (|bottomProduct c B S (S.sampleOf rule ω)| ^ q) ≤
      ENNReal.ofReal ((∏ i ∈ B, (bO + |c i|)) ^ q) := by
    intro ω
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) ?_ q)
    rw [e, Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
    have := abs_sub (curvatureObservable (S.weight i (fineSide Λ.stepParams.side S.data.windowLevel
      (S.data.period Λ.stepParams.side))) ω.1) (c i)
    linarith [hO i ω.1]
  refine (lintegral_mono hb).trans ?_
  simp
private theorem period_dvd_and_ge (S : MomentPoint Λ) (hFit : Λ.stepParams.Admissible) (hn : 4096 ≤ Λ.stepParams.n₀) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by
  have hLge : 2 ^ 16 ≤ Λ.stepParams.side := hFit.L_ge
  have hside : Λ.stepParams.side * Λ.stepParams.n₀ ≤ 2 * Λ.stepParams.side ^ S.data.sideExponent := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hside
    nlinarith
  refine ⟨Dvd.dvd.mul_left (dvd_pow_self _ hm) _, ?_⟩
  show 64 ≤ 2 * Λ.stepParams.side ^ S.data.sideExponent
  nlinarith
private theorem fineSide_levelSide (S : MomentPoint Λ) (t : ℕ) (ht : t ≤ S.data.windowLevel) :
    fineSide Λ.stepParams.side t (S.levelSide t) = S.data.sideAt Λ.stepParams.side 0 := by
  rw [fineSide_eq]
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t) * Λ.stepParams.side ^ t =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - 0)
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ht, Nat.sub_zero]
private theorem fineSide_period (S : MomentPoint Λ) :
    fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side) = S.data.sideAt Λ.stepParams.side 0 := by
  rw [fineSide_eq]
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ S.data.windowLevel =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - 0)
  rw [Nat.sub_zero]
end Moments
private theorem forAll_of_forAllPoints {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
theorem largerToriStatement_holds (hMS : meanScoreMomentBoundStatement) (hSz : supportTotalBoundStatement)
    (hW : weightsSitesBelowScaleStatement) (hNr : productApproxAtLastSeparatedStatement)
    (hAt : separatedLevelMomentsStatement) (hRule : existsNoiseRuleStatement)
    (hDraw : ruleDrawsChainStatement) (hBelow : sampleBelowLawStatement) (hH : HaarInvariantUnderSymmetries)
    (hTP : TwoPointByTotalCovarianceStatement) : largerToriStatement := by
  unfold largerToriStatement
  unfold meanScoreMomentBoundStatement ForAllHullPoints at hMS
  have h := forAllHull_and hMS (forAllHull_and (forAllHull_of_forAll (forAll_of_forAllPoints hSz))
    (forAllHull_and (forAllHull_of_forAll (forAll_of_forAllPoints hW))
      (forAllHull_and (forAllHull_of_forAll (forAll_of_forAllPoints hNr)) (forAllHull_of_forAll (forAll_of_forAllPoints hAt)))))
  refine forAllHull_imp h fun Λ hDr hy hh => ?_
  obtain ⟨⟨Cm, _, _, _, _, HMS⟩, ⟨_, _, _, _, _, HSz⟩, ⟨Cw, _, _, _, _, HW⟩, ⟨Cn, _, _, _, _, HNr⟩, ⟨_, _, _, _, _, HAt⟩⟩ := hh
  have hFit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hn₀ : 4096 ≤ Λ.stepParams.n₀ := hDr.n₀_ge
  have hLge : 2 ≤ Λ.stepParams.side := by
    have h16 : 2 ^ 16 ≤ Λ.stepParams.side := hFit.L_ge
    omega
  have hL1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ.stepParams.side)
  obtain ⟨cW, hcW⟩ : ∃ cW : ℕ → ℝ, cW = fun s => |Cw 0| * (Λ.stepParams.side : ℝ) ^ (4 * s) := ⟨_, rfl⟩
  have hcW0 : ∀ s, 0 ≤ cW s := fun s => by
    rw [hcW]
    positivity
  have hcard : ∀ (S : MomentPoint Λ) (u : ℕ) (i : Fin Λ.k), u ≤ S.data.scaleLevel →
      ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ cW S.data.scaleLevel := by
    intro S u i hu
    refine (HW S u hu i).2.trans ?_
    rw [hcW]
    have h1 : (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) ≤ (Λ.stepParams.side : ℝ) ^ (4 * S.data.scaleLevel) :=
      pow_le_pow_right₀ hL1 (by omega)
    have h2 : (0 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) := by positivity
    have h3 : Cw 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) ≤
        |Cw 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h2
    exact h3.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  have hobs : ∀ (S : MomentPoint Λ) (i : Fin Λ.k) (N : ℕ) [NeZero N], N = S.data.sideAt Λ.stepParams.side 0 →
      ∀ W : TorusField N, |curvatureObservable (S.weight i N) W| ≤ 32 * cW S.data.scaleLevel := by
    intro S i N _ hN W
    refine (abs_curvatureObservable_le S i N hN W).trans ?_
    have := hcard S 0 i (Nat.zero_le _)
    linarith
  have hprob : ∀ (S : MomentPoint Λ) (u n : ℕ) [NeZero n], IsProbabilityMeasure (S.law u n) := fun S u n _ =>
    (hTP Λ.stepParams hFit hFit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β S.coeff u n).1
  have hpair : ∀ S : MomentPoint Λ, IsProbabilityMeasure S.sampleLaw := by
    intro S
    haveI : IsProbabilityMeasure (wilsonLaw S.β (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side))) :=
      hprob S 0 (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side))
    haveI := isProbability_chainNoiseLaw Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
    show IsProbabilityMeasure ((wilsonLaw S.β _).prod (chainNoiseLaw Λ.stepParams S.data.windowLevel _))
    infer_instance
  have hkeep : ∀ (S : MomentPoint Λ) (p : ℕ), MeasurePreserving (pairTranslate Λ.stepParams S.data.windowLevel
      (S.data.period Λ.stepParams.side) (translationVector Λ.stepParams.side p)) S.sampleLaw S.sampleLaw := by
    intro S p
    haveI : IsProbabilityMeasure (wilsonLaw S.β (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side))) :=
      hprob S 0 (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side))
    haveI := isProbability_chainNoiseLaw Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
    exact (measurePreserving_translate_wilson hH S.β _).prod
      (measurePreserving_noiseTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
        (translationVector Λ.stepParams.side p))
  obtain ⟨aS, haS⟩ : ∃ aS : ℕ → ℝ, aS = fun s => |Λ.response.C₀| * cW s := ⟨_, rfl⟩
  have haS0 : ∀ s, 0 ≤ aS s := fun s => by
    rw [haS]
    exact mul_nonneg (abs_nonneg _) (hcW0 s)
  have hsized : ∀ (S : MomentPoint Λ) (i : Fin Λ.k), ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
      1 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∧
        |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
          aS S.data.scaleLevel * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by
    intro S i
    filter_upwards [(HSz S i).2] with w hw
    refine ⟨hw.1, hw.2.trans ?_⟩
    have hN0 : 0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by linarith [hw.1]
    refine mul_le_mul_of_nonneg_right ?_ hN0
    rw [haS]
    have h1 := hcard S S.lastSeparated i (lastSeparated_le_scaleLevel S)
    have h2 : (0 : ℝ) ≤ ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) := Nat.cast_nonneg _
    have h3 : Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤
        |Λ.response.C₀| * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h2
    exact h3.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  obtain ⟨eS, heS⟩ : ∃ eS : ℕ → ℝ, eS = fun s : ℕ =>
      |Cn 100| * ((s : ℝ) * (Λ.stepParams.side : ℝ) ^ (|Cn 101| * (s : ℝ))) := ⟨_, rfl⟩
  have heS0 : ∀ s, 0 ≤ eS s := fun s => by
    rw [heS]
    have : 0 ≤ (Λ.stepParams.side : ℝ) ^ (|Cn 101| * (s : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  have hcentre : ∀ (S : MomentPoint Λ) (i : Fin Λ.k), |S.kappaAtLast i| ≤
      32 * cW S.data.scaleLevel + (aS S.data.scaleLevel + eS S.data.scaleLevel) * |Cm 0| := by
    intro S i
    have hct : S.kappaAtLast i = S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i :=
      kappa_congr S _ i (sideAtLevel_eq S _)
    rw [hct]
    haveI := hprob S S.lastSeparated (S.levelSide S.lastSeparated)
    obtain ⟨hNear, hErr, -⟩ := HNr S {i}
    have hAt' := HAt S {i} (fun j => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) j)
    simp only [Finset.prod_singleton] at hNear hAt'
    have hM1 := HMS S 1 le_rfl [i] rfl
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hM1
    have herr : S.separationError (Cn ({i} : Finset (Fin Λ.k)).card) S.lastSeparated {i} ≤ eS S.data.scaleLevel := by
      refine hErr.trans ?_
      rw [heS]
      exact separation_sum_le _ hL1 _ hFit.rt_pos _ _ _ _ _ (lastSeparated_le_scaleLevel S)
    have hsz := hsized S i
    refine abs_le_of_integral_eq (S.law S.lastSeparated (S.levelSide S.lastSeparated))
      (fun w => curvatureObservable (S.weight i _) (bottomField Λ.stepParams S.lastSeparated (S.levelSide S.lastSeparated) w))
      (conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated) (fun i => S.weight i _) {i}
        fun j => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) j)
      (fun w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      (fun w => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      _ (aS S.data.scaleLevel) (eS S.data.scaleLevel) (32 * cW S.data.scaleLevel) |Cm 0|
      ((measurable_curvatureObservable _).comp (measurable_bottomField _ _)).aestronglyMeasurable
      (fun w => hobs S i _ (fineSide_levelSide S S.lastSeparated S.lastSeparated_le) _) (hsz.mono fun w hw => hw.2) ?_ hAt' hM1.1 ?_
      (add_nonneg (haS0 _) (heS0 _))
    · filter_upwards [hNear, hsz] with w h1 h2
      refine h1.trans (mul_le_mul_of_nonneg_right herr ?_)
      linarith [h2.1]
    · have hnn : 0 ≤ᵐ[S.law S.lastSeparated (S.levelSide S.lastSeparated)] fun w =>
          S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) :=
        hsz.mono fun w hw => by
          show 0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
          linarith [hw.1]
      have e := ofReal_integral_eq_lintegral_ofReal hM1.1 hnn
      have h2 : ENNReal.ofReal (∫ w, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))) ≤
          ENNReal.ofReal |Cm 0| := by
        rw [e]
        refine hM1.2.trans (ENNReal.ofReal_le_ofReal ?_)
        simpa using le_abs_self (Cm 0)
      exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h2
  intro S
  refine ⟨⟨S.data.sideExponent + 1, fun m hm =>
      ⟨supAdmissible_larger S.data Λ.stepParams.side hLge _ _ S.supAdmissible m (by omega), ?_⟩⟩,
    ⟨32 * cW S.data.scaleLevel + (aS S.data.scaleLevel + eS S.data.scaleLevel) * |Cm 0|,
      fun m hp hs i => hcentre (S.withSideExponent m hp hs) i⟩, hRule Λ.stepParams hFit S.tower, ?_⟩
  · refine S.side_le.trans ?_
    show 2 * Λ.stepParams.side ^ S.data.sideExponent ≤ 2 * Λ.stepParams.side ^ m
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  · intro rule ms Sq p hrule _ _ hsides
    have hT : ∀ i, (Sq i).tower = S.tower ∧ (Sq i).data.scaleLevel = S.data.scaleLevel := by
      intro i
      obtain ⟨a, b, e⟩ := hsides i
      rw [e]
      exact ⟨rfl, rfl⟩
    have hr : ∀ i, rule.IsAdmissible (Sq i).tower := fun i => by
      rw [(hT i).1]
      exact hrule
    refine ⟨⟨fun i => hpair (Sq i), fun i => hkeep (Sq i) p⟩,
      fun c B => ⟨⟨fun i => ?_, fun q => ?_⟩, ⟨fun i => ?_, fun q => ?_⟩⟩⟩
    · haveI := hpair (Sq i)
      exact (bottomProduct_moments (Sq i) rule c B 0 (32 * cW (Sq i).data.scaleLevel)
        fun j W => hobs (Sq i) j _ (fineSide_period (Sq i)) W).1
    · refine ⟨(∏ j ∈ B, (32 * cW S.data.scaleLevel + |c j|)) ^ q, fun i => ?_⟩
      haveI := hpair (Sq i)
      have h := (bottomProduct_moments (Sq i) rule c B q (32 * cW (Sq i).data.scaleLevel)
        fun j W => hobs (Sq i) j _ (fineSide_period (Sq i)) W).2
      rw [(hT i).2] at h
      exact h
    · haveI := hprob (Sq i) (Sq i).lastSeparated ((Sq i).levelSide (Sq i).lastSeparated)
      obtain ⟨b1, b2⟩ := period_dvd_and_ge (Sq i) hFit hn₀
      exact (responseProduct_moments hBelow hDraw hFit (Sq i) rule (hr i) b1 b2 B 0 _
        (lastSeparated_moments (Sq i) (aS (Sq i).data.scaleLevel) (Cm 0) (haS0 _)
          (fun j => ⟨(HSz (Sq i) j).1, hsized (Sq i) j⟩)
          (fun p hp J hJ => (HMS (Sq i) p hp J hJ).2) B 0)).1
    · refine ⟨aS S.data.scaleLevel ^ (B.card * q) * (1 + |Cm 0| ^ (B.card * q) * (((B.card * q).factorial : ℝ)) ^ 6),
        fun i => ?_⟩
      haveI := hprob (Sq i) (Sq i).lastSeparated ((Sq i).levelSide (Sq i).lastSeparated)
      obtain ⟨b1, b2⟩ := period_dvd_and_ge (Sq i) hFit hn₀
      have h := (responseProduct_moments hBelow hDraw hFit (Sq i) rule (hr i) b1 b2 B q _
        (lastSeparated_moments (Sq i) (aS (Sq i).data.scaleLevel) (Cm 0) (haS0 _)
          (fun j => ⟨(HSz (Sq i) j).1, hsized (Sq i) j⟩)
          (fun p hp J hJ => (HMS (Sq i) p hp J hJ).2) B q)).2
      rw [(hT i).2] at h
      exact h
end MomentLaw
end
end YangMills.Construction
