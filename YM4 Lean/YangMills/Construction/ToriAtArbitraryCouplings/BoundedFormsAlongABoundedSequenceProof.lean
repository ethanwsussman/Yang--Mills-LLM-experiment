import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.ConnectedFunctionsAsCumulantsAndCentredMomentsAtOneCutoff
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.BoundedMultilinearForms
open TorusSide
theorem coe_update_eq {P : Type} {n : ℕ} {V : Fin n → Submodule ℝ (P → ℝ)} (u : ∀ l, V l) (i : Fin n)
    (x : V i) :
    (fun l => ((Function.update u i x l : V l) : P → ℝ)) =
      Function.update (fun l => (u l : P → ℝ)) i (x : P → ℝ) := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
def reMultilinear {P : Type} {n : ℕ} (V : Fin n → Submodule ℝ (P → ℝ))
    (Φ : (Fin n → P → ℝ) → ℂ)
    (hΦ : ∀ (u : ∀ l, V l) (i : Fin n) (g g' : V i) (a a' : ℝ),
      Φ (Function.update (fun l => (u l : P → ℝ)) i (a • (g : P → ℝ) + a' • (g' : P → ℝ))) =
        (a : ℂ) * Φ (Function.update (fun l => (u l : P → ℝ)) i (g : P → ℝ)) +
          (a' : ℂ) * Φ (Function.update (fun l => (u l : P → ℝ)) i (g' : P → ℝ))) :
    MultilinearMap ℝ (fun l => V l) ℝ where
  toFun u := (Φ fun l => (u l : P → ℝ)).re
  map_update_add' := by
    intro inst u i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hxy := hΦ u i x y 1 1
    simp only [one_smul, Complex.ofReal_one, one_mul] at hxy
    simp only [coe_update_eq, Submodule.coe_add, hxy, Complex.add_re]
  map_update_smul' := by
    intro inst u i a x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hax := hΦ u i x x a 0
    simp only [zero_smul, add_zero, Complex.ofReal_zero, zero_mul] at hax
    simp only [coe_update_eq, Submodule.coe_smul, hax, Complex.re_ofReal_mul, smul_eq_mul]
theorem connectedFunction_get_ofFn (L m J : ℕ) (β : ℂ) {n : ℕ}
    (f : Fin n → PeriodicLattice.FourTorus L m → ℝ) :
    PeriodicLattice.connectedFunction L m J β (List.ofFn f).get =
      PeriodicLattice.connectedFunction L m J β f := by
  have key : ∀ (k : ℕ) (e : k = n) (g : Fin k → PeriodicLattice.FourTorus L m → ℝ),
      (∀ i, g i = f (Fin.cast e i)) →
      PeriodicLattice.connectedFunction L m J β g =
        PeriodicLattice.connectedFunction L m J β f := by
    intro k e g hg
    subst e
    exact congrArg _ (funext hg)
  exact key _ List.length_ofFn _ fun i => by simp; rfl
theorem setDist_antitone {s : TorusSide} {A A' B B' : Set (s.Point .torus)} (hA : A' ⊆ A)
    (hB : B' ⊆ B) : s.setDist .torus A B ≤ s.setDist .torus A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem isBoundedOnTorus_of_isBoundedFun {L m : ℕ} {f : PeriodicLattice.FourTorus L m → ℝ}
    (hf : TestFunctions.IsBoundedFun f) : ConnectedFunctionExpansion.IsBoundedOnTorus f := by
  obtain ⟨c, hc⟩ := hf
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hc y))
theorem statement_holds
    (hCum : OneCutoffCumulants.Statement)
    (hLip : LipschitzEstimates.Combined) : Statement := by
  intro s hL m' K β C h j n hn d hd A hA
  have hn1 : 1 ≤ n := by omega
  let D : ReflectionPositivity.AxisMirror.MirrorData := s.mirrorDataOf (K j) (β j) (h.β_pos j)
  obtain ⟨⟨-, -, -, hlin, -⟩, -, -⟩ := hCum D hL
  obtain ⟨hre, -, hadd⟩ := hlin n hn1
  obtain ⟨⟨hbd, hC1, -⟩, -, -, -, -⟩ := hLip s hL m' .torus
  have hbdd : ∀ {A' : Set (s.Point .torus)} (f : s.c1Submodule .torus A'),
      ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) f.1 := by
    intro A' f
    have hf := (s.mem_c1Submodule_iff .torus _ _).1 f.2
    have hmem : f.1 ∈ s.c1CompactSet .torus := by
      rw [← s.c1SuppIn_univ]
      exact ⟨hf.1, hf.2.1, subset_univ _⟩
    exact isBoundedOnTorus_of_isBoundedFun (hbd _ hmem).1
  let Φ : (Fin n → s.Point .torus → ℝ) → ℂ :=
    fun f => PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ) f
  have hΦ : ∀ (u : ∀ l, s.c1Submodule .torus (A l)) (i : Fin n)
      (g g' : s.c1Submodule .torus (A i)) (a a' : ℝ),
      Φ (Function.update (fun l => (u l : s.Point .torus → ℝ)) i
          (a • (g : s.Point .torus → ℝ) + a' • (g' : s.Point .torus → ℝ))) =
        (a : ℂ) * Φ (Function.update (fun l => (u l : s.Point .torus → ℝ)) i g) +
          (a' : ℂ) * Φ (Function.update (fun l => (u l : s.Point .torus → ℝ)) i g') :=
    fun u i g g' a a' => hadd (fun l => (u l : s.Point .torus → ℝ)) i g.1 g'.1 a a'
      (fun k => hbdd (u k)) (hbdd g) (hbdd g')
  refine ⟨reMultilinear _ Φ hΦ, fun u => ?_⟩
  have hget : s.cumulantAt (K j) (β j) (s.componentsAsTuple .torus u) =
      Φ fun l => (u l : s.Point .torus → ℝ) :=
    connectedFunction_get_ofFn _ _ _ _ _
  have him : (Φ fun l => (u l : s.Point .torus → ℝ)).im = 0 :=
    hre (fun l => (u l : s.Point .torus → ℝ)) fun k => hbdd (u k)
  have hval : ((reMultilinear _ Φ hΦ u : ℝ) : ℂ) =
      Φ fun l => (u l : s.Point .torus → ℝ) :=
    Complex.ext (by simp [reMultilinear]) (by simp [him])
  refine ⟨hval.trans hget.symm, ?_⟩
  have hpos : Pairwise fun i k =>
      0 < ReflectionPositivity.AxisMirror.Ambient.setDist s.asMirrorData .torus (A i) (A k) :=
    fun i k hik => lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd) (hA i k hik)
  have hsep : s.componentsAsTuple .torus u ∈ s.sepOfLength .torus n := by
    refine ReflectionPositivity.AxisMirror.Ambient.ofFn_mem_separatedN s.asMirrorData .torus hpos
      fun l => ?_
    rw [← s.c1SuppIn_eq_compactC1SuppIn]
    exact (s.mem_c1Submodule_iff .torus _ _).1 (u l).2
  have hlip : s.componentsAsTuple .torus u ∈ s.lipDisjointOfLength .torus n :=
    hC1.2 ⟨n, by omega⟩ hsep
  have hd' : ENNReal.ofReal d ≤ s.gapAllLengths .torus (s.componentsAsTuple .torus u) := by
    rw [s.gapAllLengths_eq_supportGap]
    refine le_iInf fun i => le_iInf fun k => le_iInf fun hik => ?_
    have hsupp : ∀ p : Fin (s.componentsAsTuple .torus u).length,
        s.closedSupport .torus ((s.componentsAsTuple .torus u).get p) ⊆
          A (Fin.cast List.length_ofFn p) := by
      intro p
      have e : (s.componentsAsTuple .torus u).get p =
          (u (Fin.cast List.length_ofFn p) : s.Point .torus → ℝ) := List.get_ofFn _ p
      rw [e]
      exact ((s.mem_c1Submodule_iff .torus _ _).1 (u _).2).2.2
    refine (hA _ _ fun e => hik ?_).trans (setDist_antitone (hsupp i) (hsupp k))
    have e' := congrArg Fin.val e
    exact Fin.ext e'
  have hb := h.bound j n hn d hd _ hlip hd'
  have hprod : s.sharpNormProduct m' .torus (s.componentsAsTuple .torus u) =
      ∏ l, s.sharpNormAt m' .torus (u l : s.Point .torus → ℝ) := by
    simp only [TorusSide.sharpNormProduct, TorusSide.componentsAsTuple, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply]
  rw [hprod, hget, ← hval, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb
end YangMills.Construction.ToriAtArbitraryCouplings.BoundedMultilinearForms
end
