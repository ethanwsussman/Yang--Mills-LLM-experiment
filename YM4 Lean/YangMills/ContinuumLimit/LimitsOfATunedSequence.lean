import YangMills.ContinuumLimit.FirstPassageOfATunedPair
import YangMills.ContinuumLimit.DilationOfSeparatedTuples
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZero
set_option autoImplicit false

open Filter Set
open scoped Topology

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open TorusMetric TestFunctions PeriodicLattice FourPointBounds SchwingerFunctions Conventions

namespace LimitsOfATunedSequence

theorem tendsto_pnat_coe_atTop {K : ℕ+ → ℕ+} (hK : Tendsto K atTop atTop) :
    Tendsto (fun j => (K j : ℕ)) atTop atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hK ⟨b + 1, by omega⟩).mono fun j hj => by
    have hb : b + 1 ≤ (K j : ℕ) := hj
    omega

theorem tendsto_atTop_of_coe {K : ℕ+ → ℕ+} (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop) :
    Tendsto K atTop atTop :=
  tendsto_atTop.2 fun b => (hK.eventually_ge_atTop (b : ℕ)).mono fun _ hj => hj

theorem tendsto_of_strictMono_pnat {φ : ℕ+ → ℕ+} (hφ : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun _ ha => ha.trans hφ.le_apply⟩

theorem exists_frequently_eq_of_forall_lt {ρ : ℕ → ℕ} {D : ℕ} (hρ : ∀ n, ρ n < D) :
    ∃ r < D, ∃ᶠ n in atTop, ρ n = r := by
  by_contra hcon
  have hev : ∀ i : Fin D, ∀ᶠ n in atTop, ρ n ≠ (i : ℕ) := fun i =>
    Filter.not_frequently.mp fun hfr => hcon ⟨i, i.isLt, hfr⟩
  obtain ⟨n, hn⟩ := (Filter.eventually_all.mpr hev).exists
  exact hn ⟨ρ n, hρ n⟩ rfl

theorem exists_strictMono_pnat_of_frequently {P : ℕ+ → Prop}
    (h : ∃ᶠ n in atTop, P (Nat.succPNat n)) : ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧ ∀ j, P (φ j) := by
  obtain ⟨φ₀, hφ₀, hP⟩ := Filter.extraction_of_frequently_atTop h
  refine ⟨fun j => Nat.succPNat (φ₀ (j : ℕ)), fun a b hab => ?_, fun j => hP (j : ℕ)⟩
  have h1 : φ₀ (a : ℕ) < φ₀ (b : ℕ) := hφ₀ ((PNat.coe_lt_coe a b).2 hab)
  rw [← PNat.coe_lt_coe, Nat.succPNat_coe, Nat.succPNat_coe]
  omega

end LimitsOfATunedSequence

open LimitsOfATunedSequence

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : WeightedResponses.ResponseParameters} {lam c₅ : ℝ}

theorem tuned_limit_is_dilated_top_limit (hGives : TotalDensityFlow.ExpansionGivesFlow)
    (hUniq : TotalDensityFlow.FlowIsUnique) (hR : CutoffRescalingInvariance)
    (h : RunTable T y Kr lam c₅) {Bs g P : ℝ}
    (hLim : QuaternionicWilsonModel.TopLimitsRealNonzero.ExistsSubseqFamilyOnTorus
      (T.stepParameters y) Bs g)
    (hP : SequencePassage.passageThreshold Bs g = P)
    (s : StandingParameters) (hs : s.L = (T.stepParameters y).side)
    (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hK : Tendsto K atTop atTop)
    (hdepth : ∀ j, runDepth lam c₅ ≤ (K j : ℕ)) (hβ : ∀ j, IsTunedAt T y P (K j) (β j)) :
    ∃ r < runDepth lam c₅, ∃ (φ : ℕ+ → ℕ+) (K' : ℕ+ → ℕ+)
      (S' : AmbientPoints.TupleMapFamily (shiftSide s r) .torus),
      StrictMono φ ∧ (∀ j, (K' j : ℕ) + r = (K (φ j) : ℕ)) ∧
      (∀ j, TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) Bs g (K' j) (β (φ j))) ∧
      TotalDensitySystem.IsTorusLimit (T.stepParameters y) Bs g (shiftSide s r) S' ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X' : AmbientPoints.separatedTuples (shiftSide s r) .torus n),
        Tendsto (fun j => connectedSchwinger s.L ((s.m : ℕ) + r) (K' j : ℕ) (β (φ j)) X'.1) atTop
          (𝓝 ((S' n hn X' : ℝ) : ℂ))) ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X : AmbientPoints.separatedTuples s .torus n),
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
          (𝓝 ((S' n hn ⟨fun i => dilateToSide s.L s.m ((s.m : ℕ) + r) (X.1 i),
            dilate_up_mem s r X.2⟩ : ℝ) : ℂ))) ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X' : AmbientPoints.separatedTuples (shiftSide s r) .torus n),
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j))
          (fun i => dilateToSide s.L ((s.m : ℕ) + r) s.m (X'.1 i))) atTop
          (𝓝 ((S' n hn X' : ℝ) : ℂ))) := by
  classical
  have hL3 : 3 ≤ s.L := by
    have := s.isAdmissible.2
    omega
  have hI : ∀ j : ℕ+, ∃ K₁ : ℕ, 1 ≤ K₁ ∧ K₁ ≤ (K j : ℕ) ∧ (K j : ℕ) - K₁ < runDepth lam c₅ ∧
      TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) Bs g K₁ (β j) :=
    fun j => tuned_first_passage_index hGives hUniq h (hβ j) (hdepth j) Bs g hP
  choose Kc hKc1 hKcle hKcr hKcp using hI
  obtain ⟨r, hrD, hfr⟩ := exists_frequently_eq_of_forall_lt
    (ρ := fun n => (K (Nat.succPNat n) : ℕ) - Kc (Nat.succPNat n)) (D := runDepth lam c₅)
    (fun n => hKcr (Nat.succPNat n))
  obtain ⟨φ₁, hφ₁, hr⟩ := exists_strictMono_pnat_of_frequently
    (P := fun j => (K j : ℕ) - Kc j = r) hfr
  obtain ⟨K', hK'add, hK'pass⟩ : ∃ K' : ℕ+ → ℕ+, (∀ j, (K' j : ℕ) + r = (K (φ₁ j) : ℕ)) ∧
      ∀ j, TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) Bs g (K' j) (β (φ₁ j)) := by
    refine ⟨fun j => ⟨Kc (φ₁ j), by have := hKc1 (φ₁ j); omega⟩, fun j => ?_, fun j => hKcp (φ₁ j)⟩
    have h1 := hr j
    have h2 := hKcle (φ₁ j)
    show Kc (φ₁ j) + r = (K (φ₁ j) : ℕ)
    omega
  have hK'top : Tendsto K' atTop atTop := by
    apply tendsto_atTop_of_coe
    have h1 := tendsto_pnat_coe_atTop (hK.comp (tendsto_of_strictMono_pnat hφ₁))
    refine Tendsto.congr (fun j => ?_) ((tendsto_sub_atTop_nat r).comp h1)
    have := hK'add j
    show (K (φ₁ j) : ℕ) - r = (K' j : ℕ)
    omega
  obtain ⟨φ₂, S', hφ₂, hS'lim, hconv⟩ :=
    hLim (shiftSide s r) hs K' (fun j => β (φ₁ j)) hK'pass hK'top
  refine ⟨r, hrD, φ₁ ∘ φ₂, fun j => K' (φ₂ j), S', hφ₁.comp hφ₂, fun j => hK'add (φ₂ j),
    fun j => hK'pass (φ₂ j), hS'lim, fun n hn X' => hconv n hn X', ?_, ?_⟩
  · intro n hn X
    refine Tendsto.congr (fun j => ?_) (hconv n hn
      ⟨fun i => dilateToSide s.L s.m ((s.m : ℕ) + r) (X.1 i), dilate_up_mem s r X.2⟩)
    have hk : (K' (φ₂ j) : ℕ) = (K (φ₁ (φ₂ j)) : ℕ) - r := by
      have := hK'add (φ₂ j)
      omega
    have hle : r ≤ (K (φ₁ (φ₂ j)) : ℕ) := by
      have := hK'add (φ₂ j)
      omega
    dsimp only
    rw [hk]
    exact (connectedSchwinger_dilate_up hR hL3 (s.m : ℕ) (K (φ₁ (φ₂ j)) : ℕ) r hle _ X.1).symm
  · intro n hn X'
    refine Tendsto.congr (fun j => ?_) (hconv n hn X')
    have hk : (K' (φ₂ j) : ℕ) = (K (φ₁ (φ₂ j)) : ℕ) - r := by
      have := hK'add (φ₂ j)
      omega
    have hle : r ≤ (K (φ₁ (φ₂ j)) : ℕ) := by
      have := hK'add (φ₂ j)
      omega
    rw [hk]
    exact connectedSchwinger_dilate_down hR hL3 (s.m : ℕ) (K (φ₁ (φ₂ j)) : ℕ) r hle _ X'.1

end YangMills.ContinuumLimit

end
