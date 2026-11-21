import YangMills.Construction.FamiliesOfLimits.WhatTheTransportToATorusKeeps
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import YangMills.Construction.TotalDensitiesGiveASystem.PerBallBoundOfALimitAlongTori
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open FamiliesOfLimits.TorusPeriodization (periodizeOnTorus)
private theorem torusSide_tendsto {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : ToriSequence L) :
    Tendsto (fun j => PeriodicLattice.torusSide L (Q.m j)) atTop atTop := by
  have h₁ : (1 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have h₂ : Tendsto (fun K : ℕ+ => (K : ℕ)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨⟨b + 1, Nat.succ_pos b⟩, fun a ha => by
      have h : b + 1 ≤ (a : ℕ) := ha
      omega⟩
  exact ((tendsto_pow_atTop_atTop_of_one_lt h₁).comp (h₂.comp Q.m_tendsto)).const_mul_atTop (by norm_num)
private theorem sharpNormTorus_nonneg' {ℓ : ℝ} (f : TorusMetric.Torus4 ℓ → ℝ) :
    0 ≤ TestFunctions.sharpNormTorus 1 f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem ballBoundPassesToLimit_of_periodization
    (hKeep : FamiliesOfLimits.TorusPeriodization.PeriodizationProperties) : BallBoundPassesToLimit := by
  intro L hL Q c hc hP S hS n hn R d hR hd X hb hs
  let s₀ : Conventions.StandingParameters := ⟨L, hL, 1, 1⟩
  have hn₁ : 1 ≤ n := by omega
  obtain ⟨⟨ρ, hρ, hsup⟩, -, -⟩ :=
    (hKeep s₀ 1 le_rfl).2 n hn₁ X.1 ((AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2)
  have hbound : ∀ᶠ j in atTop,
      ‖SchwingerFunctions.connectedSchwingerR4 L (Q.m j) (Q.K j) (Q.β j) X.1‖ ≤
        c n d R * ∏ i, TestFunctions.sharpNormR4 1 (X.1 i) := by
    filter_upwards [(torusSide_tendsto hL Q).eventually_ge_atTop (max (4 * ρ) (4 * R))] with j hj
    let s : Conventions.StandingParameters := ⟨L, hL, Q.K j, Q.m j⟩
    have hXs : X.1 ∈ AmbientPoints.separatedTuples s .euclidean n :=
      (AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2
    have hside : PeriodicLattice.torusSide L (Q.m j) = s.side := rfl
    obtain ⟨-, hk, -⟩ := (hKeep s 1 le_rfl).2 n hn₁ X.1 hXs
    obtain ⟨-, -, hlip, hdist, hball⟩ := hk ρ hρ hsup ((le_max_left _ _).trans hj)
    have hR4 : R ≤ s.side / 4 := by
      have := (le_max_right _ _).trans hj
      rw [hside] at this
      linarith
    have h := hP j n hn R d hR hd (SchwingerFunctions.periodizeAll L (Q.m j) X.1) (fun i => (hlip i).1)
      (fun i => by
        obtain ⟨x, hx⟩ := hb i
        have hx' := hball i x R hR hR4 fun y hy => hx ((AmbientPoints.tsupport_eq_of_r4 _).le hy)
        exact ⟨AmbientPoints.proj s .torus x, fun y hy => hx' ((AmbientPoints.tsupport_eq_of_torus (s := s) _).ge hy)⟩)
      ((AmbientPoints.supportsApartBy_torus_iff (s := s) (AmbientPoints.periodizedTuple s X.1) d).1
        ⟨hd, le_iInf fun i => le_iInf fun k => le_iInf fun hik => by
          rw [hdist i k hik]
          have h₁ := hs i k hik
          rw [← AmbientPoints.tsupport_eq_of_r4 (s := s) (X.1 i),
            ← AmbientPoints.tsupport_eq_of_r4 (s := s) (X.1 k)] at h₁
          exact h₁⟩)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (hc n hn d R hd hR))
    exact Finset.prod_le_prod (fun i _ => sharpNormTorus_nonneg' _) fun i _ => (hlip i).2
  have hlim := (hS n hn X).norm
  have := le_of_tendsto hlim hbound
  rwa [Complex.norm_real, Real.norm_eq_abs] at this
end YangMills.Construction.TotalDensities
end
