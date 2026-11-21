import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpaces
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace FlatSubspaces
variable {n : ℕ}
theorem supNormVec_pos_iff (v : Fin 4 → ℝ) :
    0 < YangMills.Construction.PeriodicLattice.supNormVec v ↔ v ≠ 0 := by
  constructor
  · rintro hv rfl
    simp [YangMills.Construction.PeriodicLattice.supNormVec] at hv
  · intro hv
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hv
    exact (abs_pos.2 hμ).trans_le (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
theorem minSeparation_pos_iff (x : Config n) :
    0 < minSeparation x ↔ ∀ i j : Fin n, i < j → x i ≠ x j := by
  have hmin : minSeparation x = Finset.univ.inf fun i : Fin n => Finset.univ.inf fun j : Fin n =>
      ⨅ (_ : i < j), ENNReal.ofReal (YangMills.Construction.PeriodicLattice.supNormVec (x i - x j)) := by
    simp only [minSeparation, Finset.inf_univ_eq_iInf]
  rw [hmin, Finset.lt_inf_iff ENNReal.zero_lt_top]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, true_implies]
  rw [Finset.lt_inf_iff ENNReal.zero_lt_top]
  refine forall_congr' fun j => ?_
  simp only [Finset.mem_univ, true_implies]
  by_cases hij : i < j
  · simp only [hij, iInf_pos, true_implies, ENNReal.ofReal_pos, supNormVec_pos_iff]
    exact sub_ne_zero
  · simp [hij]
theorem distinctArgs_eq_setOf_minSeparation_pos (n : ℕ) :
    distinctArgs n = {x : Config n | 0 < minSeparation x} := by
  ext x
  have hmem : x ∈ distinctArgs n ↔ x ∉ diagonalSet n := by
    rw [← compl_distinctArgs]
    simp
  rw [hmem, Set.mem_ofPred_eq, minSeparation_pos_iff]
  simp only [diagonalSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, not_exists, not_and]
theorem exists_submodule_schwartz_flatOff {U : Set (Config n)} (hU : IsOpen U)
    (hlin : ∀ f g : Config n → ℂ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → ∀ a b : ℂ,
      ContDiff ℝ ∞ (a • f + b • g) ∧
      ∀ α : MultiIndex n, iteratedPartial α (a • f + b • g) =
        a • iteratedPartial α f + b • iteratedPartial α g)
    (hcomb : ∀ f g : Config n → ℂ, IsSchwartz f → IsSchwartz g → ∀ a b : ℂ,
      IsSchwartz (a • f + b • g))
    (hzero : IsSchwartz (0 : Config n → ℂ)) :
    ∃ W : Submodule ℂ (Config n → ℂ),
      (W : Set (Config n → ℂ)) = {f | IsSchwartz f ∧ FlatOff f U} := by
  have hclosed : ∀ f g : Config n → ℂ, IsSchwartz f ∧ FlatOff f U →
      IsSchwartz g ∧ FlatOff g U → ∀ a b : ℂ,
      IsSchwartz (a • f + b • g) ∧ FlatOff (a • f + b • g) U := by
    intro f g hf hg a b
    obtain ⟨hsmooth, hderiv⟩ := hlin f g hf.1.1 hg.1.1 a b
    refine ⟨hcomb f g hf.1 hg.1 a b, hsmooth, hU, fun x hx => ⟨hsmooth, fun α => ?_⟩⟩
    rw [hderiv α]
    simp [(hf.2.2.2 x hx).2 α, (hg.2.2.2 x hx).2 α]
  have hzero' : IsSchwartz (0 : Config n → ℂ) ∧ FlatOff (0 : Config n → ℂ) U := by
    refine ⟨hzero, hzero.1, hU, fun x _ => ⟨hzero.1, fun α => ?_⟩⟩
    have hα := (hlin 0 0 hzero.1 hzero.1 0 0).2 α
    simp only [zero_smul, add_zero] at hα
    rw [hα]
    rfl
  refine ⟨{ carrier := {f | IsSchwartz f ∧ FlatOff f U}
            add_mem' := ?_
            zero_mem' := hzero'
            smul_mem' := ?_ }, rfl⟩
  · intro f g hf hg
    simpa using hclosed f g hf hg 1 1
  · intro a f hf
    simpa using hclosed f f hf hf a 0
theorem FlatOff.mono {f : Config n → ℂ} {U U' : Set (Config n)} (hf : FlatOff f U)
    (hU' : IsOpen U') (hsub : U ⊆ U') : FlatOff f U' :=
  ⟨hf.1, hU', fun x hx => hf.2.2 x fun hxU => hx (hsub hxU)⟩
end FlatSubspaces
open FlatSubspaces in
theorem openLociAndFlatSubspaces_of_schwartzSuprema (hsup : SchwartzSupremaStatement) :
    OpenLociAndFlatSubspaces := by
  intro n hn
  obtain ⟨-, hlin, hschw, -, -, S, hS, -⟩ := hsup n hn
  have hpos : posTimeSet n ⊆ distinctArgs n := fun x hx => hx.1
  have hneg : negTimeSet n ⊆ distinctArgs n := fun x hx => hx.1
  have hzero : IsSchwartz (0 : Config n → ℂ) := by
    have h0 := S.zero_mem
    rw [← SetLike.mem_coe, hS] at h0
    exact h0
  have hl : ∀ f g : Config n → ℂ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → ∀ a b : ℂ,
      ContDiff ℝ ∞ (a • f + b • g) ∧
      ∀ α : MultiIndex n, iteratedPartial α (a • f + b • g) =
        a • iteratedPartial α f + b • iteratedPartial α g :=
    fun f g hf hg a b => (hlin f g hf hg a b 0 0 le_rfl).2
  have hc : ∀ f g : Config n → ℂ, IsSchwartz f → IsSchwartz g → ∀ a b : ℂ,
      IsSchwartz (a • f + b • g) :=
    fun f g hf hg a b => (hschw f g hf hg a b).2
  obtain ⟨W, hW⟩ := exists_submodule_schwartz_flatOff isOpen_distinctArgs hl hc hzero
  obtain ⟨Wp, hWp⟩ := exists_submodule_schwartz_flatOff isOpen_posTimeSet hl hc hzero
  obtain ⟨Wm, hWm⟩ := exists_submodule_schwartz_flatOff isOpen_negTimeSet hl hc hzero
  have hleS : ∀ {U : Set (Config n)} (T : Submodule ℂ (Config n → ℂ)),
      (T : Set (Config n → ℂ)) = {f | IsSchwartz f ∧ FlatOff f U} → T ≤ S := by
    intro U T hT f hf
    rw [← SetLike.mem_coe, hT] at hf
    rw [← SetLike.mem_coe, hS]
    exact hf.1
  have hleW : ∀ {U : Set (Config n)} (T : Submodule ℂ (Config n → ℂ)),
      (T : Set (Config n → ℂ)) = {f | IsSchwartz f ∧ FlatOff f U} →
      U ⊆ distinctArgs n → T ≤ W := by
    intro U T hT hU f hf
    rw [← SetLike.mem_coe, hT] at hf
    rw [← SetLike.mem_coe, hW]
    exact ⟨hf.1, FlatOff.mono hf.2 isOpen_distinctArgs hU⟩
  exact ⟨distinctArgs_eq_setOf_minSeparation_pos n,
    ⟨isOpen_distinctArgs, isOpen_posTimeSet, isOpen_negTimeSet, hpos, hneg⟩,
    S, W, Wp, Wm, hS, hW, hWp, hWm, hleS W hW, hleS Wp hWp, hleS Wm hWm, hleW Wp hWp hpos,
    hleW Wm hWm hneg⟩
end YangMills.Construction.ConfigSpace
end
