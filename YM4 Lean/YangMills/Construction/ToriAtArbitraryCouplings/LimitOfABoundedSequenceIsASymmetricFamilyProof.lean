import YangMills.Construction.ToriAtArbitraryCouplings.ConnectedFunctionsAsCumulantsAndCentredMomentsAtOneCutoff
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityAlongABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.LimitOfABoundedSequenceIsASymmetricFamily
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.ToriAtArbitraryCouplings.TheVectorSpacesOfClassC1AndTheNeighbourhoodsAtASide
import YangMills.Construction.TotalDensitiesGiveASystem.WhatALimitAlongToriHasProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace SymmetricLimitFamily
open TorusSide
private theorem apply_get_ofFn {A B : Type*} (Φ : ∀ n : ℕ, (Fin n → A) → B) {n : ℕ}
    (u : Fin n → A) : Φ _ (List.ofFn u).get = Φ n u := by
  have aux : ∀ {k : ℕ} (hk : k = n) (v : Fin k → A), (∀ i, v i = u (Fin.cast hk i)) →
      Φ k v = Φ n u := by
    intro k hk v hv
    subst hk
    congr 1
    funext i
    exact hv i
  exact aux List.length_ofFn _ fun i => by
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rfl
private theorem cumulantAt_ofFn (s : TorusSide) (K : ℕ+) (β : ℝ) {n : ℕ}
    (u : Fin n → s.Point .torus → ℝ) :
    s.cumulantAt K β (List.ofFn u) =
      PeriodicLattice.connectedFunction s.L s.m K (β : ℂ) u :=
  apply_get_ofFn (fun _ v => PeriodicLattice.connectedFunction s.L s.m K (β : ℂ) v) u
private theorem isBoundedOnTorus_of_mem (hN : LipschitzEstimates.Combined) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) {u : s.Point .torus → ℝ}
    (hu : u ∈ s.c1CompactSet .torus) :
    ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) u := by
  obtain ⟨c, hc⟩ := ((hN s hL 0 .torus).1.1 u hu).1
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := c)) (iSup_le fun y => ?_)
  exact ENNReal.ofReal_le_ofReal (hc y)
private theorem inf_principal_neBot_of_infinite {I : Set ℕ+} (hI : I.Infinite) :
    (atTop ⊓ 𝓟 I : Filter ℕ+).NeBot := by apply _root_.YangMills.SharedProofs.p125520 <;> assumption
theorem statement_holds (hC : OneCutoffCumulants.Statement)
    (hE : EquicontinuityAlongSequence.Holds)
    (hN : LipschitzEstimates.Combined) : Statement := by
  intro s hL m' K β C h J hJ S hS
  have := inf_principal_neBot_of_infinite hJ
  have hform : ∀ j, OneCutoffCumulants.IsRealSymmMultilinear
      (s.mirrorDataOf (K j) (β j) (h.β_pos j)) :=
    fun j => (hC (s.mirrorDataOf (K j) (β j) (h.β_pos j)) hL).1.2.2.2.1
  have hbdd : ∀ {g : s.Point .torus → ℝ}, g ∈ s.c1CompactSet .torus →
      ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) g :=
    fun hg => isBoundedOnTorus_of_mem hN s hL hg
  have him : ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n), (S n hn X).im = 0 := by
    intro n hn X
    have hlim := (Complex.continuous_im.tendsto _).comp (hS n hn X)
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun j => ?_)
    have hlen : 1 ≤ X.1.length := by rw [X.2.1]; omega
    exact ((hform j X.1.length hlen).1 X.1.get fun i => hbdd (X.2.2.1 _ (List.get_mem _ _))).symm
  have hreal : ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n),
      (((S n hn X).re : ℝ) : ℂ) = S n hn X := fun n hn X =>
    Complex.ext (by simp) (by simp [him n hn X])
  have hvalue : ∀ (n : ℕ) (hn : 2 ≤ n) (u : Fin n → s.Point .torus → ℝ)
      (hu : List.ofFn u ∈ s.sepOfLength .torus n),
      Tendsto (fun j => PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ) u)
        (atTop ⊓ 𝓟 J) (𝓝 (S n hn ⟨_, hu⟩)) := by
    intro n hn u hu
    refine (hS n hn ⟨_, hu⟩).congr fun j => ?_
    exact cumulantAt_ofFn s (K j) (β j) u
  have hentry : ∀ {n : ℕ} {u : Fin n → s.Point .torus → ℝ},
      List.ofFn u ∈ s.sepOfLength .torus n → ∀ k,
        ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) (u k) :=
    fun hu k => hbdd (hu.2.1 _ ((List.mem_ofFn' _ _).2 ⟨k, rfl⟩))
  have hmulti : ∀ (n : ℕ) (hn : 2 ≤ n),
      Ambient.IsSeparatedMultilinear s.asMirrorData .torus fun X : s.sepOfLength .torus n =>
        (S n hn X).re := by
    intro n hn A hA f hf i g hg a b
    have hmem : ∀ {u : Fin n → s.Point .torus → ℝ},
        (∀ k, u k ∈ Ambient.compactC1SuppIn s.asMirrorData .torus (A k)) →
        List.ofFn u ∈ s.sepOfLength .torus n :=
      fun hu => Ambient.ofFn_mem_separatedN _ _ hA hu
    have hsp : ∀ {A' : Set (s.Point .torus)} {u : s.Point .torus → ℝ},
        u ∈ Ambient.compactC1SuppIn s.asMirrorData .torus A' ↔ u ∈ s.c1Submodule .torus A' := by
      intro A' u
      rw [mem_c1Submodule_iff, c1SuppIn_eq_compactC1SuppIn]
    have hlin : a • f i + b • g ∈ Ambient.compactC1SuppIn s.asMirrorData .torus (A i) :=
      hsp.2 (Submodule.add_mem _ (Submodule.smul_mem _ _ (hsp.1 (hf i)))
        (Submodule.smul_mem _ _ (hsp.1 hg)))
    have hupd : ∀ {v : s.Point .torus → ℝ}, v ∈ Ambient.compactC1SuppIn s.asMirrorData .torus (A i) →
        ∀ k, Function.update f i v k ∈ Ambient.compactC1SuppIn s.asMirrorData .torus (A k) := by
      intro v hv k
      by_cases hk : k = i
      · subst hk
        simpa using hv
      · simpa [Function.update_of_ne hk] using hf k
    have h0 := hmem hf
    have h1 := hmem (hupd hlin)
    have h2 := hmem (hupd hg)
    have hlim := (hvalue n hn _ h1)
    have hlim' : Tendsto
        (fun j => PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
          (Function.update f i (a • f i + b • g))) (atTop ⊓ 𝓟 J)
        (𝓝 ((a : ℂ) * S n hn ⟨_, h0⟩ + (b : ℂ) * S n hn ⟨_, h2⟩)) := by
      refine (((hvalue n hn _ h0).const_mul (a : ℂ)).add
        ((hvalue n hn _ h2).const_mul (b : ℂ))).congr fun j => ?_
      have hfb : ∀ k, ConnectedFunctionExpansion.IsBoundedOnTorus
          (L := s.L) (m := s.m) (f k) := hentry h0
      have hgb : ConnectedFunctionExpansion.IsBoundedOnTorus
          (L := s.L) (m := s.m) g := hbdd hg.1
      have hj : PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
            (Function.update f i (a • f i + b • g)) =
          (a : ℂ) * PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
              (Function.update f i (f i)) +
            (b : ℂ) * PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
              (Function.update f i g) :=
        (hform j n (by omega)).2.2 f i (f i) g a b hfb (hfb i) hgb
      exact (hj.trans (congrArg (fun u : Fin n → PeriodicLattice.FourTorus s.L s.m → ℝ =>
        (a : ℂ) * PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ) u +
          (b : ℂ) * PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
            (Function.update f i g)) (Function.update_eq_self i f))).symm
    have heq := tendsto_nhds_unique hlim hlim'
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at hre
    simp only [Ambient.evalOrZero, dif_pos h0, dif_pos h1, dif_pos h2]
    exact hre
  let F : Ambient.ConnectedFamily s.asMirrorData .torus :=
    ⟨fun n hn X => (S n hn X).re, hmulti⟩
  have hFS : s.toComplexTupleFns F = S := by
    funext n hn X
    exact hreal n hn X
  refine ⟨F, hFS, ?_, ?_, ?_⟩
  · intro n hn f ς hf hf'
    have hlim := hvalue n hn _ hf'
    have hlim' := (hvalue n hn _ hf).congr fun j =>
      (((hform j n (by omega)).2.1 f ς (hentry hf)).symm)
    exact congrArg Complex.re (tendsto_nhds_unique hlim hlim')
  · rw [hFS]
    intro n hn d hd X hX
    refine le_of_tendsto (hS n hn X).norm (Eventually.of_forall fun j => ?_)
    have hpos : 0 < n := by omega
    exact h.bound j n hn d hd X.1
      (((hN s hL m' .torus).1.2.1.2 ⟨n, hpos⟩) X.2) hX
  · rw [hFS]
    intro n hn d hd A hA f g hf hg hfA hgA
    refine le_of_tendsto ((hS n hn ⟨_, hf⟩).sub (hS n hn ⟨_, hg⟩)).norm
      (Eventually.of_forall fun j => ?_)
    exact hE s hL m' K β C h j n hn d hd A hA f g hf hg hfA hgA
end SymmetricLimitFamily
end YangMills.Construction.ToriAtArbitraryCouplings
end
