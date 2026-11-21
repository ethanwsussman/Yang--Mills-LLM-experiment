import YangMills.Construction.ToriAtArbitraryCouplings.ApproximationThatKeepsTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.ExtractionOfASetOfIndices
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace SubsequenceExtraction
open TorusSide
private theorem tendsto_inf_principal_range {α : Type*} [TopologicalSpace α] {g : ℕ → ℕ+}
    (hg : StrictMono g) {u : ℕ+ → α} {a : α} (hu : Tendsto (u ∘ g) atTop (𝓝 a)) :
    Tendsto u (atTop ⊓ 𝓟 (range g)) (𝓝 a) := by
  have hle : (atTop : Filter ℕ+) ⊓ 𝓟 (range g) ≤ map g atTop := by
    intro S hS
    obtain ⟨N, hN⟩ := mem_atTop_sets.1 (mem_map.1 hS)
    refine mem_inf_of_inter (mem_atTop (g N)) (mem_principal_self _) ?_
    rintro _ ⟨hj, k, rfl⟩
    exact hN k (hg.le_iff_le.1 hj)
  exact (tendsto_map'_iff.2 hu).mono_left hle
private theorem Infinite.exists_strictMono_seq {A : Set ℕ+} (hA : A.Infinite) :
    ∃ e : ℕ → ℕ+, StrictMono e ∧ ∀ k, e k ∈ A := by
  have hP : ∀ N : ℕ, ∃ m > N, m.succPNat ∈ A := by
    intro N
    obtain ⟨b, hb, hlt⟩ := hA.exists_gt N.succPNat
    refine ⟨b.natPred, ?_, by simpa using hb⟩
    have h1 : (N.succPNat : ℕ) < b := hlt
    have h2 := PNat.natPred_add_one b
    simp only [Nat.succPNat_coe] at h1
    omega
  obtain ⟨φ, hφ, hmem⟩ := Nat.exists_strictMono_subsequence hP
  exact ⟨fun k => (φ k).succPNat, fun a b hab => Nat.succPNat_lt_succPNat.2 (hφ hab), hmem⟩
private theorem exists_common_convergent_subseq {T : Type*} [Countable T] (u : T → ℕ+ → ℂ)
    (hu : ∀ t, ∃ (i₀ : ℕ+) (B : ℝ), ∀ j, i₀ ≤ j → ‖u t j‖ ≤ B) {e : ℕ → ℕ+}
    (he : StrictMono e) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ t, ∃ a, Tendsto (fun k => u t (e (ψ k))) atTop (𝓝 a) := by
  choose i₀ B hB using hu
  let x : ℕ → T → ℂ := fun k t => if ‖u t (e k)‖ ≤ max (B t) 0 then u t (e k) else 0
  have hx : ∀ k, x k ∈ Set.pi univ fun t => Metric.closedBall (0 : ℂ) (max (B t) 0) := by
    intro k t _
    simp only [x, mem_closedBall_zero_iff]
    split_ifs with hh
    · exact hh
    · simp
  obtain ⟨a, -, ψ, hψ, ha⟩ :=
    (isCompact_univ_pi fun t => isCompact_closedBall (0 : ℂ) (max (B t) 0)).tendsto_subseq hx
  refine ⟨ψ, hψ, fun t => ⟨a t, ?_⟩⟩
  have h1 : Tendsto (fun k => x (ψ k) t) atTop (𝓝 (a t)) := (tendsto_pi_nhds.1 ha) t
  refine h1.congr' ?_
  have hmono : StrictMono fun k => ((e (ψ k) : ℕ+) : ℕ) := fun p q hpq => he (hψ hpq)
  filter_upwards [eventually_ge_atTop ((i₀ t : ℕ+) : ℕ)] with k hk
  have hle : i₀ t ≤ e (ψ k) := by
    have : ((i₀ t : ℕ+) : ℕ) ≤ (e (ψ k) : ℕ+) := hk.trans (hmono.le_apply)
    exact this
  have hb : ‖u t (e (ψ k))‖ ≤ max (B t) 0 := (hB t _ hle).trans (le_max_left _ _)
  simp only [x, if_pos hb]
private theorem exists_tendsto_of_approx {w : ℕ → ℂ}
    (h : ∀ η : ℝ, 0 < η → ∃ w' : ℕ → ℂ, (∃ a, Tendsto w' atTop (𝓝 a)) ∧ ∀ k, ‖w k - w' k‖ ≤ η) :
    ∃ a, Tendsto w atTop (𝓝 a) := by
  refine ⟨_, (cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)).choose_spec⟩
  obtain ⟨w', ⟨a, ha⟩, hw⟩ := h (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 ha.cauchySeq (ε / 4) (by positivity)
  refine ⟨N, fun p hp q hq => ?_⟩
  have h1 := hN p hp q hq
  have h2 := hw p
  have h3 := hw q
  rw [dist_eq_norm] at h1 ⊢
  have h4 : w p - w q = (w p - w' p) + (w' p - w' q) - (w q - w' q) := by ring
  rw [h4]
  calc ‖(w p - w' p) + (w' p - w' q) - (w q - w' q)‖
      ≤ ‖w p - w' p‖ + ‖w' p - w' q‖ + ‖w q - w' q‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith
private theorem exists_pos_le_gap (hLip : LipschitzEstimates.Combined) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) (m' n : ℕ) (hn : 1 ≤ n) {X : s.FnTuple .torus}
    (hX : X ∈ s.sepOfLength .torus n) :
    X ∈ s.lipDisjointOfLength .torus n ∧
      ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ s.gapAllLengths .torus X := by
  obtain ⟨⟨-, ⟨-, hmem⟩, -⟩, -, ⟨-, hpos⟩, -⟩ := hLip s hL m' .torus
  have hXL : X ∈ s.lipDisjointOfLength .torus n := hmem ⟨n, hn⟩ hX
  have h0 : 0 < s.gapAllLengths .torus X := hpos ⟨n, hn⟩ X hXL
  have htop : min 1 (s.gapAllLengths .torus X) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  refine ⟨hXL, (min 1 (s.gapAllLengths .torus X)).toReal,
    ENNReal.toReal_pos (lt_min one_pos h0).ne' htop, ?_⟩
  rw [ENNReal.ofReal_toReal htop]
  exact min_le_right _ _
private theorem List.exists_eq_ofFn_of_length {α : Type*} {X : List α} {n : ℕ}
    (h : X.length = n) : ∃ f : Fin n → α, X = List.ofFn f := by
  subst h
  exact ⟨X.get, (List.ofFn_get X).symm⟩
private theorem exists_adapted_cumulant_close (hLip : LipschitzEstimates.Combined)
    (hApp : SeparatedApproximation.Statement)
    (hForms : BoundedMultilinearForms.Statement) (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L)
    {m' : ℕ} {K : ℕ+ → ℕ+} {β : ℕ+ → ℝ} {C : ℕ → ℝ → ℝ}
    (h : s.IsUniformlyBoundedSeq m' K β C)
    {D : s.supportFamily .torus → Set (s.Point .torus → ℝ)} (hD : s.IsCountableC1DenseChoice .torus D)
    {n : ℕ} (hn : 2 ≤ n) {X : s.FnTuple .torus} (hX : X ∈ s.sepOfLength .torus n)
    {η : ℝ} (hη : 0 < η) :
    ∃ φ : Fin n → s.Point .torus → ℝ, List.ofFn φ ∈ s.adaptedTupleSet .torus D ∧
      ∀ j, ‖s.cumulantAt (K j) (β j) X -
        s.cumulantAt (K j) (β j) (List.ofFn φ)‖ ≤ η := by
  obtain ⟨f, rfl⟩ := List.exists_eq_ofFn_of_length hX.1
  obtain ⟨-, d, hd, hdf⟩ := exists_pos_le_gap hLip s hL m' n (by omega) hX
  have hd3 : 0 < d / 3 := by positivity
  have hc : 0 ≤ C n (d / 3) := h.isClusterConstant.nonneg n hn _ hd3
  have herr := (hApp s hL m' .torus D hD n (by omega) f hX d hd hdf 1 one_pos).2.2.2
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      C n (d / 3) * s.approxDefect m' .torus f ε < η := by
    have := herr.const_mul (C n (d / 3))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hη)
  obtain ⟨ε, hε, hε0⟩ := (hsmall.and self_mem_nhdsWithin).exists
  obtain ⟨-, hdist, ⟨φ, ⟨hφ, -⟩, hf', hφ', hch⟩, -⟩ :=
    hApp s hL m' .torus D hD n (by omega) f hX d hd hdf ε hε0
  refine ⟨φ, hφ, fun j => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hForms s hL m' K β C h j n hn (d / 3) hd3
    (s.supportThickening .torus f d) hdist
  have hb := hch (C n (d / 3)) hc Ψ fun u => (hΨ u).2
  have e1 : ((Ψ fun i => ⟨f i, hf' i⟩ : ℝ) : ℂ) =
      s.cumulantAt (K j) (β j) (List.ofFn f) := (hΨ fun i => ⟨f i, hf' i⟩).1
  have e2 : ((Ψ fun i => ⟨φ i, hφ' i⟩ : ℝ) : ℂ) =
      s.cumulantAt (K j) (β j) (List.ofFn φ) := (hΨ fun i => ⟨φ i, hφ' i⟩).1
  rw [← e1, ← e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hb.trans hε.le
theorem holds (hLip : LipschitzEstimates.Combined)
    (hFam : SupportAdaptedFamily.Claim)
    (hApp : SeparatedApproximation.Statement)
    (hForms : BoundedMultilinearForms.Statement) : Holds := by
  intro s hL m' K β C h J₀ hJ₀ I hI i₀ v hv
  obtain ⟨⟨-, ⟨D, hD⟩, -⟩, -, hAdapted, -⟩ := hFam s hL m' .torus
  obtain ⟨hcount, hsep, -⟩ := hAdapted D hD
  have hT : Countable (s.adaptedTupleSetLengthGeTwo .torus D) :=
    (hcount.mono fun X hX => hX.1).to_subtype
  let u : I ⊕ s.adaptedTupleSetLengthGeTwo .torus D → ℕ+ → ℂ :=
    Sum.elim v fun X j => s.cumulantAt (K j) (β j) X.1
  have hu : ∀ t, ∃ (j₁ : ℕ+) (B : ℝ), ∀ j, j₁ ≤ j → ‖u t j‖ ≤ B := by
    rintro (ι | X)
    · obtain ⟨B, hB⟩ := hv ι
      exact ⟨i₀ ι, B, hB⟩
    · have hX : X.1 ∈ s.sepOfLength .torus X.1.length :=
        ⟨rfl, (mem_iUnion.1 (hsep X.2.1)).choose_spec.2⟩
      obtain ⟨hXL, d, hd, hdX⟩ := exists_pos_le_gap hLip s hL m' _ (by have := X.2.2; omega) hX
      exact ⟨1, _, fun j _ => h.bound j _ X.2.2 d hd X.1 hXL hdX⟩
  obtain ⟨e, he, heJ⟩ := Infinite.exists_strictMono_seq hJ₀
  obtain ⟨ψ, hψ, hconv⟩ := exists_common_convergent_subseq u hu he
  have hg : StrictMono (e ∘ ψ) := he.comp hψ
  have hlim : ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n), ∃ a,
      Tendsto (fun k => s.cumulantFnsAt (K (e (ψ k))) (β (e (ψ k))) n hn X) atTop (𝓝 a) := by
    intro n hn X
    refine exists_tendsto_of_approx fun η hη => ?_
    obtain ⟨φ, hφ, hclose⟩ := exists_adapted_cumulant_close hLip hApp hForms s hL h hD hn X.2 hη
    have hφ2 : List.ofFn φ ∈ s.adaptedTupleSetLengthGeTwo .torus D :=
      ⟨hφ, by simpa using hn⟩
    exact ⟨_, hconv (Sum.inr ⟨_, hφ2⟩), fun k => hclose _⟩
  choose S hS using hlim
  refine ⟨range (e ∘ ψ), ?_, infinite_range_of_injective hg.injective, ⟨S, ?_⟩, fun ι => ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact heJ _
  · exact fun n hn X => tendsto_inf_principal_range hg (hS n hn X)
  · obtain ⟨a, ha⟩ := hconv (Sum.inl ι)
    exact ⟨a, tendsto_inf_principal_range hg ha⟩
end SubsequenceExtraction
end YangMills.Construction.ToriAtArbitraryCouplings
end
