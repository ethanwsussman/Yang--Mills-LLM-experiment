import YangMills.Construction.Functions.MultilinearTelescoping
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityByTelescoping
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TelescopingEquicontinuity
variable {s : TorusSide} {m' : ℕ} {E : Ambient}
theorem boundedMultilinear_satisfiesTelescoping (hT : MultilinearTelescoping.TelescopingBound)
    (hS : LipschitzEstimates.SharpNormSeminorm s m' E) {n : ℕ} (hn : 1 ≤ n)
    (V : Fin n → Submodule ℝ (s.Point E → ℝ))
    (hV : ∀ l, ∀ f ∈ V l, f ∈ s.lipSuppIn E univ) {c : ℝ} (hc : 0 ≤ c) :
    s.BoundedMultilinearSatisfyTelescoping m' E V c := by
  obtain ⟨-, W, p, hW, hp⟩ := hS
  have hVW : ∀ l, V l ≤ W := fun l f hf => by
    exact show f ∈ (W : Set (s.Point E → ℝ)) from hW ▸ hV l f hf
  let q : ∀ l, Seminorm ℝ (V l) := fun l => p.comp (Submodule.inclusion (hVW l))
  have hq : ∀ l (u : V l), q l u = s.sharpNormAt m' E (u : s.Point E → ℝ) := fun l u => hp _
  intro Φ hΦ g hg
  have hbound : ∀ u : ∀ l, V l, |Φ u| ≤ c * ∏ l, q l (u l) := fun u => by
    simpa only [hq] using hΦ u
  have htel := hT n hn (fun l => V l) q c hc Φ hbound g hg
  have hchain := htel.1.trans htel.2
  simpa only [hq, Submodule.coe_sub] using hchain
theorem mem_lipSuppIn_univ {A : Set (s.Point E)} {f : s.Point E → ℝ}
    (hf : f ∈ s.lipSuppIn E A) : f ∈ s.lipSuppIn E univ :=
  ⟨hf.1, hf.2.1, subset_univ _⟩
theorem setDist_antitone {A A' B B' : Set (s.Point E)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    s.setDist E A B ≤ s.setDist E A' B' := by
  cases E
  · exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
  · exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem pairwisePosSeparated_of_separatedBy {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Fin n → Set (s.Point E)} (hA : PairwiseSeparatedBy s E δ A) :
    s.PairwisePosSeparated E A :=
  fun i k hik => lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) (hA i k hik)
theorem componentsAsTuple_mem_sepOfLength {n : ℕ} {A : Fin n → Set (s.Point E)}
    (hA : s.PairwisePosSeparated E A) (u : (l : Fin n) → s.c1Submodule E (A l)) :
    s.componentsAsTuple E u ∈ s.sepOfLength E n := by
  have hA' : Pairwise fun i j => 0 < Ambient.setDist s.asMirrorData E (A i) (A j) := by
    intro i k hik
    have hpos := hA hik
    cases E
    · exact hpos
    · exact hpos
  refine Ambient.ofFn_mem_separatedN s.asMirrorData E hA' fun l => ?_
  rw [← s.c1SuppIn_eq_compactC1SuppIn]
  exact (s.mem_c1Submodule_iff E _ _).1 (u l).2
theorem coe_update_apply {n : ℕ} {V : Fin n → Submodule ℝ (s.Point E → ℝ)} (u : ∀ l, V l)
    (i : Fin n) (x : V i) :
    (fun l => ((Function.update u i x l : V l) : s.Point E → ℝ)) =
      Function.update (fun l => (u l : s.Point E → ℝ)) i (x : s.Point E → ℝ) := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
def restrictMultilinear {n : ℕ} {A : Fin n → Set (s.Point E)}
    (hA : s.PairwisePosSeparated E A) (Φ : s.sepOfLength E n → ℝ)
    (hΦ : Ambient.IsSeparatedMultilinear s.asMirrorData E Φ) :
    MultilinearMap ℝ (fun l => s.c1Submodule E (A l)) ℝ where
  toFun := s.restrictToProduct E Φ fun l => s.c1Submodule E (A l)
  map_update_add' := by
    intro inst u i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hlin := (s.isSeparatedMultilinear_iff E Φ).1 hΦ A hA
    have hval : ∀ z : s.c1Submodule E (A i),
        s.restrictToProduct E Φ (fun l => s.c1Submodule E (A l)) (Function.update u i z) =
          Ambient.evalOrZero Φ (List.ofFn (Function.update (fun l => (u l : s.Point E → ℝ)) i
            (z : s.Point E → ℝ))) := fun z => by
      simp only [TorusSide.restrictToProduct, TorusSide.componentsAsTuple]
      rw [coe_update_apply]
    have hmem : ∀ l, Function.update (fun l => (u l : s.Point E → ℝ)) i (x : s.Point E → ℝ) l ∈
        s.c1SuppIn E (A l) := fun l => by
      rw [← coe_update_apply]
      exact (s.mem_c1Submodule_iff E _ _).1 (Function.update u i x l).2
    have hxy := hlin _ hmem i y ((s.mem_c1Submodule_iff E _ _).1 y.2) 1 1
    rw [Function.update_idem, Function.update_idem, Function.update_self] at hxy
    simp only [one_smul, one_mul] at hxy
    rw [hval, hval, hval, Submodule.coe_add]
    exact hxy
  map_update_smul' := by
    intro inst u i a x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have hlin := (s.isSeparatedMultilinear_iff E Φ).1 hΦ A hA
    have hval : ∀ z : s.c1Submodule E (A i),
        s.restrictToProduct E Φ (fun l => s.c1Submodule E (A l)) (Function.update u i z) =
          Ambient.evalOrZero Φ (List.ofFn (Function.update (fun l => (u l : s.Point E → ℝ)) i
            (z : s.Point E → ℝ))) := fun z => by
      simp only [TorusSide.restrictToProduct, TorusSide.componentsAsTuple]
      rw [coe_update_apply]
    have hmem : ∀ l, Function.update (fun l => (u l : s.Point E → ℝ)) i (x : s.Point E → ℝ) l ∈
        s.c1SuppIn E (A l) := fun l => by
      rw [← coe_update_apply]
      exact (s.mem_c1Submodule_iff E _ _).1 (Function.update u i x l).2
    have hax := hlin _ hmem i x ((s.mem_c1Submodule_iff E _ _).1 x.2) a 0
    rw [Function.update_idem, Function.update_idem, Function.update_self] at hax
    simp only [zero_smul, add_zero, zero_mul] at hax
    rw [hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact hax
theorem ballSupportedSeparated_ofFn {n : ℕ} {δ R : ℝ} {A : Fin n → Set (s.Point E)}
    (hA : PairwiseSeparatedBy s E δ A)
    (hball : ∀ l, ∃ B, s.IsBallWithRadius E B R ∧ A l ⊆ B) {F : Fin n → s.Point E → ℝ}
    (hF : ∀ l, s.closedSupport E (F l) ⊆ A l) :
    s.BallSupportedSeparated E δ R (List.ofFn F) := by
  refine ⟨fun f hf => ?_, fun i k hik => ?_⟩
  · obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    obtain ⟨B, hB, hAB⟩ := hball l
    exact ⟨B, hB, (hF l).trans hAB⟩
  · rw [List.get_ofFn, List.get_ofFn]
    refine (hA _ _ fun e => hik ?_).trans (setDist_antitone (hF _) (hF _))
    exact Fin.ext (by simpa [Fin.ext_iff] using e)
theorem abs_restrictToProduct_le {n : ℕ} (hn : 2 ≤ n) {δ R : ℝ} (hδ : 0 < δ)
    {A : Fin n → Set (s.Point E)} (hA : PairwiseSeparatedBy s E δ A)
    {C : Schwinger.ClusterBound} {S : Ambient.ConnectedFamily s.asMirrorData E}
    (hS : s.SatisfiesClusterBound m' C E S) (hR : R ∈ s.admissibleRadiusSet E)
    (hball : ∀ l, ∃ B, s.IsBallWithRadius E B R ∧ A l ⊆ B)
    (u : (l : Fin n) → s.c1Submodule E (A l)) :
    |s.restrictToProduct E (S.fn n hn) (fun l => s.c1Submodule E (A l)) u| ≤
      C.value n δ R * ∏ l, s.sharpNormAt m' E (u l : s.Point E → ℝ) := by
  have hmem := componentsAsTuple_mem_sepOfLength (pairwisePosSeparated_of_separatedBy hδ hA) u
  have hb := hS n hn δ R hδ hR ⟨_, hmem⟩ (ballSupportedSeparated_ofFn hA hball fun l =>
    ((s.mem_c1Submodule_iff E _ _).1 (u l).2).2.2)
  have hval : s.restrictToProduct E (S.fn n hn) (fun l => s.c1Submodule E (A l)) u =
      S.fn n hn ⟨_, hmem⟩ := dif_pos hmem
  have hprod : s.sharpNormProduct m' E (s.componentsAsTuple E u) =
      ∏ l, s.sharpNormAt m' E (u l : s.Point E → ℝ) := by
    simp only [TorusSide.sharpNormProduct, TorusSide.componentsAsTuple, List.map_ofFn,
      List.prod_ofFn, Function.comp_apply]
  rw [hval, ← hprod]
  exact hb
theorem claim_holds (hT : MultilinearTelescoping.TelescopingBound)
    (hN : LipschitzEstimates.Combined) : Claim := by
  refine ⟨fun n hn V _ _ p c hc Φ hb g hg => (hT n hn V p c hc Φ hb g hg).1, ?_⟩
  intro s hL m' E n hn δ hδ A hA
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hC1, hS⟩ := (hN s hL m' E).1
  have hlip : ∀ l, ∀ f ∈ s.lipSubmodule E (A l), f ∈ s.lipSuppIn E univ := fun l f hf =>
    mem_lipSuppIn_univ ((s.mem_lipSubmodule_iff E _ f).1 hf)
  have hc1 : ∀ l, ∀ f ∈ s.c1Submodule E (A l), f ∈ s.lipSuppIn E univ := fun l f hf =>
    mem_lipSuppIn_univ (hC1.1 _ ((s.mem_c1Submodule_iff E _ f).1 hf))
  refine ⟨fun c hc => ⟨boundedMultilinear_satisfiesTelescoping hT hS hn1 _ hlip hc,
    boundedMultilinear_satisfiesTelescoping hT hS hn1 _ hc1 hc⟩, ?_⟩
  intro C S hCS R hR hball
  have hpos := pairwisePosSeparated_of_separatedBy hδ hA
  refine ⟨componentsAsTuple_mem_sepOfLength hpos, ?_⟩
  have hR0 : 0 < R := by
    cases E
    · exact hR.1
    · exact hR
  exact boundedMultilinear_satisfiesTelescoping hT hS hn1 _ hc1 (C.value_nonneg n hn δ R hδ hR0)
    (restrictMultilinear hpos (S.fn n hn) (S.fn_multilinear n hn))
    (abs_restrictToProduct_le hn hδ hA hCS hR hball)
end TelescopingEquicontinuity
end YangMills.Construction.ToriAtArbitraryCouplings
end
