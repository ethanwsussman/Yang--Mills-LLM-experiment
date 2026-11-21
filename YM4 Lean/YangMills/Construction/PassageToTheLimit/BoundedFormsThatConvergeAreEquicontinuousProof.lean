import YangMills.Construction.LinearAlgebra.BoundedMultilinearForms
import YangMills.Construction.NormedSpaces.BanachSteinhausLinearAndMultilinear
import YangMills.Construction.PassageToTheLimit.BoundedFormsThatConvergeAreEquicontinuous
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpaces
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Set Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LimitSpaces
namespace BanachForms
open YangMills.Construction.NormedSpaces.BanachSteinhaus
section Abstract
variable {q : ℕ} {Y : Fin q → Type} [∀ l, NormedAddCommGroup (Y l)] [∀ l, NormedSpace ℝ (Y l)]
theorem abs_sub_le_of_bound (hF : Multilinear.BoundedMultilinearEstimates)
    (hq : 1 ≤ q) (Ψ : MultilinearMap ℝ Y ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : ∀ l, Y l, |Ψ x| ≤ C * ∏ l, ‖x l‖) (f g : ∀ l, Y l) :
    |Ψ f - Ψ g| ≤ C * ∑ l, ‖f l - g l‖ * ∏ l' ∈ Finset.univ.erase l, (‖f l'‖ + ‖g l'‖) := by
  obtain ⟨h₁, h₂⟩ := (hF q hq Y (fun l => normSeminorm ℝ (Y l))).1 Ψ C hC hb f g
  exact h₁.trans h₂
theorem exists_trivial_factor_of_neg_bound {C : ℝ} (hC : C < 0) (Ψ : (∀ l, Y l) → ℝ)
    (hb : ∀ x : ∀ l, Y l, |Ψ x| ≤ C * ∏ l, ‖x l‖) : ∃ l₀, ∀ y : Y l₀, y = 0 := by
  by_contra hcon
  push Not at hcon
  choose y hy using hcon
  have hpos : 0 < ∏ l, ‖y l‖ := Finset.prod_pos fun l _ => norm_pos_iff.2 (hy l)
  have h₁ := (abs_nonneg _).trans (hb y)
  nlinarith [mul_neg_of_neg_of_pos hC hpos]
theorem eq_zero_of_neg_bound {C : ℝ} (hC : C < 0) (Ψ : (∀ l, Y l) → ℝ)
    (hb : ∀ x : ∀ l, Y l, |Ψ x| ≤ C * ∏ l, ‖x l‖) (x : ∀ l, Y l) : Ψ x = 0 := by
  have h₀ : 0 ≤ ∏ l, ‖x l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
  have h₁ : |Ψ x| ≤ 0 := (hb x).trans (mul_nonpos_of_nonpos_of_nonneg hC.le h₀)
  exact abs_eq_zero.1 (le_antisymm h₁ (abs_nonneg _))
theorem telescope_sum_eq_zero_of_trivial {l₀ : Fin q} (h₀ : ∀ y : Y l₀, y = 0) (f g : ∀ l, Y l) :
    ∑ l, ‖f l - g l‖ * ∏ l' ∈ Finset.univ.erase l, (‖f l'‖ + ‖g l'‖) = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = l₀
  · subst hl
    rw [h₀ (f l), h₀ (g l)]
    simp
  · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := l₀) ?_ ?_)
    · exact Finset.mem_erase.2 ⟨fun h => hl h.symm, Finset.mem_univ _⟩
    · rw [h₀ (f l₀), h₀ (g l₀)]
      simp
theorem difference_bound_and_tendsto (hF : Multilinear.BoundedMultilinearEstimates) (hq : 1 ≤ q)
    {J : Type} (L : Filter J) (Ψ : J → MultilinearMap ℝ Y ℝ) (C : ℝ)
    (hb : ∀ (j : J) (x : ∀ l, Y l), |Ψ j x| ≤ C * ∏ l, ‖x l‖)
    (conv : ∀ x : ∀ l, Y l, ∃ c : ℝ, Tendsto (fun j => Ψ j x) L (𝓝 c)) :
    (∀ (f g : ∀ l, Y l) (j : J), |Ψ j f - Ψ j g| ≤
      C * ∑ l, ‖f l - g l‖ * ∏ l' ∈ Finset.univ.erase l, (‖f l'‖ + ‖g l'‖)) ∧
    ∀ (u : J → ∀ l, Y l) (x : ∀ l, Y l),
      (∀ l, Tendsto (fun j => ‖u j l - x l‖) L (𝓝 0)) →
      ∃ c : ℝ, Tendsto (fun j => Ψ j (u j)) L (𝓝 c) ∧ Tendsto (fun j => Ψ j x) L (𝓝 c) := by
  rcases lt_or_ge C 0 with hC | hC
  · have hz : ∀ (j : J) (x : ∀ l, Y l), Ψ j x = 0 := fun j x =>
      eq_zero_of_neg_bound hC (fun z => Ψ j z) (hb j) x
    refine ⟨fun f g j => ?_, fun u x _ => ⟨0, ?_, ?_⟩⟩
    · obtain ⟨l₀, h₀⟩ := exists_trivial_factor_of_neg_bound hC (fun z => Ψ j z) (hb j)
      rw [telescope_sum_eq_zero_of_trivial h₀ f g, hz j f, hz j g]
      simp
    · simp only [hz]
      exact tendsto_const_nhds
    · simp only [hz]
      exact tendsto_const_nhds
  · refine ⟨fun f g j => abs_sub_le_of_bound hF hq (Ψ j) hC (hb j) f g,
      fun u x hu => ?_⟩
    obtain ⟨c, hc⟩ := conv x
    refine ⟨c, ?_, hc⟩
    have hn : ∀ l, Tendsto (fun j => ‖u j l‖) L (𝓝 ‖x l‖) := fun l =>
      (tendsto_iff_norm_sub_tendsto_zero.2 (hu l)).norm
    have hbound : Tendsto (fun j => C * ∑ l, ‖u j l - x l‖ *
        ∏ l' ∈ Finset.univ.erase l, (‖u j l'‖ + ‖x l'‖)) L (𝓝 0) := by
      have h₁ : Tendsto (fun j => C * ∑ l, ‖u j l - x l‖ *
          ∏ l' ∈ Finset.univ.erase l, (‖u j l'‖ + ‖x l'‖)) L
          (𝓝 (C * ∑ l : Fin q, 0 * ∏ l' ∈ Finset.univ.erase l, (‖x l'‖ + ‖x l'‖))) :=
        tendsto_const_nhds.mul (tendsto_finsetSum _ fun l _ => (hu l).mul
          (tendsto_finsetProd _ fun l' _ => (hn l').add tendsto_const_nhds))
      simpa using h₁
    have hdiff : Tendsto (fun j => Ψ j (u j) - Ψ j x) L (𝓝 0) :=
      squeeze_zero_norm (fun j => by
        simpa using abs_sub_le_of_bound hF hq (Ψ j) hC (hb j) (u j) x) hbound
    simpa using hdiff.add hc
theorem abs_le_multilinearFormNorm (Ψ : MultilinearMap ℝ Y ℝ)
    (hb : BddAbove (formValuesOnUnitPolyball Ψ))
    (x : ∀ l, Y l) (hx : ∀ l, ‖x l‖ ≤ 1) : |Ψ x| ≤ multilinearFormNorm Ψ :=
  le_csSup hb ⟨x, hx, rfl⟩
end Abstract
theorem cofinite_le_indexAtTop (𝒥 : Set ℕ+) : cofinite ≤ indexAtTop 𝒥 := by
  refine tendsto_iff_comap.1 (tendsto_atTop.2 fun b => ?_)
  exact show {a : 𝒥 | ¬ b ≤ (a : ℕ+)}.Finite from by
    refine ((Set.finite_Iio b).preimage Subtype.val_injective.injOn).subset fun a ha => ?_
    exact not_le.1 ha
theorem bddAbove_abs_of_tendsto_indexAtTop {𝒥 : Set ℕ+} (u : 𝒥 → ℝ) {c : ℝ}
    (hu : Tendsto u (indexAtTop 𝒥) (𝓝 c)) : BddAbove (Set.range fun j => |u j|) :=
  ((hu.mono_left (cofinite_le_indexAtTop 𝒥)).abs.isBoundedUnder_le).bddAbove_range_of_cofinite
section Elements
variable {X : Type} {V : Set (X → ℝ)} {n : (X → ℝ) → ℝ}
theorem fnorm_nonneg (hV : IsBanachFunctionSpace V n) {f : X → ℝ} (hf : f ∈ V) :
    0 ≤ n f := by
  have hz : n 0 = 0 := (hV.norm_eq_zero_iff 0 hV.zero_mem).2 rfl
  have hm : (-1 : ℝ) • f ∈ V := by
    simpa using hV.lincomb_mem f hf f hf 0 (-1)
  have h₁ := hV.norm_add_le f hf _ hm
  have h₂ := hV.norm_smul f hf (-1)
  have h₃ : f + (-1 : ℝ) • f = 0 := by simp
  rw [h₃, hz, h₂] at h₁
  simp only [abs_neg, abs_one, one_mul] at h₁
  linarith
def toSubmodule (hV : IsBanachFunctionSpace V n) : Submodule ℝ (X → ℝ) where
  carrier := V
  zero_mem' := hV.zero_mem
  add_mem' := fun {f g} hf hg => by simpa using hV.lincomb_mem f hf g hg 1 1
  smul_mem' := fun a f hf => by simpa using hV.lincomb_mem f hf 0 hV.zero_mem a 0
def Elem (hV : IsBanachFunctionSpace V n) : Type := toSubmodule hV
instance (hV : IsBanachFunctionSpace V n) : AddCommGroup (Elem hV) :=
  inferInstanceAs (AddCommGroup (toSubmodule hV))
instance (hV : IsBanachFunctionSpace V n) : Module ℝ (Elem hV) :=
  inferInstanceAs (Module ℝ (toSubmodule hV))
instance (hV : IsBanachFunctionSpace V n) : Norm (Elem hV) :=
  ⟨fun f => n (f : toSubmodule hV).1⟩
def Elem.val {hV : IsBanachFunctionSpace V n} (f : Elem hV) : X → ℝ :=
  (f : toSubmodule hV).1
theorem Elem.val_mem {hV : IsBanachFunctionSpace V n} (f : Elem hV) : f.val ∈ V :=
  (f : toSubmodule hV).2
def Elem.mk (hV : IsBanachFunctionSpace V n) (f : X → ℝ) (hf : f ∈ V) : Elem hV :=
  (⟨f, hf⟩ : toSubmodule hV)
theorem Elem.norm_eq {hV : IsBanachFunctionSpace V n} (f : Elem hV) : ‖f‖ = n f.val := rfl
@[simp] theorem Elem.val_add {hV : IsBanachFunctionSpace V n} (f g : Elem hV) :
    (f + g).val = f.val + g.val := rfl
@[simp] theorem Elem.val_smul {hV : IsBanachFunctionSpace V n} (a : ℝ) (f : Elem hV) :
    (a • f).val = a • f.val := rfl
theorem Elem.ext {hV : IsBanachFunctionSpace V n} {f g : Elem hV} (h : f.val = g.val) :
    f = g :=
  Subtype.ext h
theorem elemNormedCore (hV : IsBanachFunctionSpace V n) : NormedSpace.Core ℝ (Elem hV) where
  norm_nonneg f := fnorm_nonneg hV f.val_mem
  norm_smul a f := by
    rw [Elem.norm_eq, Elem.norm_eq, Elem.val_smul, hV.norm_smul _ f.val_mem]
    rfl
  norm_triangle f g := by
    rw [Elem.norm_eq, Elem.norm_eq, Elem.norm_eq, Elem.val_add]
    exact hV.norm_add_le _ f.val_mem _ g.val_mem
  norm_eq_zero_iff f := by
    rw [Elem.norm_eq, hV.norm_eq_zero_iff _ f.val_mem]
    exact ⟨fun h => Elem.ext h, fun h => by rw [h]; rfl⟩
instance (hV : IsBanachFunctionSpace V n) : NormedAddCommGroup (Elem hV) :=
  NormedAddCommGroup.ofCore (elemNormedCore hV)
instance (hV : IsBanachFunctionSpace V n) : NormedSpace ℝ (Elem hV) :=
  NormedSpace.ofCore (elemNormedCore hV)
instance (hV : IsBanachFunctionSpace V n) : CompleteSpace (Elem hV) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N, n ((u a).val - (u b).val) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun a ha b hb => ?_⟩
    have := hN a ha b hb
    rwa [dist_eq_norm] at this
  obtain ⟨f, hf, hlim⟩ := hV.cauchy_tendsto (fun k => (u k).val) (fun k => (u k).val_mem) hC
  refine ⟨Elem.mk hV f hf, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hlim ε hε
  refine ⟨N, fun a ha => ?_⟩
  rw [dist_eq_norm]
  exact hN a ha
end Elements
section Concrete
open Ambient
variable {s : Conventions.StandingParameters} {E : Ambient} {q : ℕ} {W : Fin q → Set (E.Carrier s)}
  (hB : ∀ l, IsBanachFunctionSpace (E.c1Within s (W l)) (E.normC1 s))
def toProduct (y : ∀ l, Elem (hB l)) : E.C1ProductSpace s W := fun l => ⟨(y l).val, (y l).val_mem⟩
def ofProduct (x : E.C1ProductSpace s W) : ∀ l, Elem (hB l) :=
  fun l => Elem.mk (hB l) (x l).1 (x l).2
theorem toProduct_val (y : ∀ l, Elem (hB l)) (l : Fin q) : (toProduct hB y l).1 = (y l).val := rfl
def toMultilinear (Ψ : E.C1ProductSpace s W → ℝ) (hΨ : IsMultilinearRealForm Ψ) :
    MultilinearMap ℝ (fun l => Elem (hB l)) ℝ where
  toFun y := Ψ (toProduct hB y)
  map_update_add' := by
    intro _ m i x y
    have h := hΨ i 1 1 (toProduct hB (Function.update m i x)) (toProduct hB (Function.update m i y))
      (toProduct hB (Function.update m i (x + y)))
      (fun l hl => by simp only [toProduct_val, Function.update_of_ne hl])
      (fun l hl => by simp only [toProduct_val, Function.update_of_ne hl])
      (by simp only [toProduct_val, Function.update_self, Elem.val_add, one_smul])
    rw [one_mul, one_mul] at h
    exact h
  map_update_smul' := by
    intro _ m i c x
    have h := hΨ i c 0 (toProduct hB (Function.update m i x)) (toProduct hB (Function.update m i x))
      (toProduct hB (Function.update m i (c • x)))
      (fun l hl => rfl)
      (fun l hl => by simp only [toProduct_val, Function.update_of_ne hl])
      (by simp only [toProduct_val, Function.update_self, Elem.val_smul, zero_smul, add_zero])
    rw [zero_mul, add_zero] at h
    exact h
include hB in
theorem convergentBoundedForms_of_complete (hU : multilinearFormsBounded)
    (hF : Multilinear.BoundedMultilinearEstimates) (hq : 1 ≤ q) :
    E.ConvergentBoundedFormsEquicontinuous s W := by
  intro 𝒥 Ψ hJ hreal hbdd hconv
  have : Nonempty 𝒥 := hJ.nonempty.to_subtype
  let F : 𝒥 → MultilinearMap ℝ (fun l => Elem (hB l)) ℝ := fun j => toMultilinear hB (Ψ j) (hreal j)
  have hval : ∀ (j : 𝒥) (y : ∀ l, Elem (hB l)), (∀ l, ‖y l‖ ≤ 1) →
      ENNReal.ofReal |F j y| ≤ operatorBound (Ψ j) := fun j y hy =>
    le_iSup₂_of_le (f := fun (x : E.C1ProductSpace s W) (_ : ∀ l, E.normC1 s (x l).1 ≤ 1) =>
      ENNReal.ofReal |Ψ j x|) (toProduct hB y) (fun l => hy l) le_rfl
  have hbddF : ∀ j, BddAbove (formValuesOnUnitPolyball (F j)) := fun j =>
    ⟨(operatorBound (Ψ j)).toReal, by
      rintro r ⟨y, hy, rfl⟩
      exact (ENNReal.ofReal_le_iff_le_toReal (hbdd j).ne).1 (hval j y hy)⟩
  have hptw : ∀ y, BddAbove (Set.range fun j => |F j y|) := fun y => by
    obtain ⟨c, hc⟩ := hconv (toProduct hB y)
    exact bddAbove_abs_of_tendsto_indexAtTop _ hc
  obtain ⟨hsup, hest⟩ := hU 𝒥 q hq (fun l => Elem (hB l)) F hbddF hptw
  have hle : ∀ j, operatorBound (Ψ j) ≤ ENNReal.ofReal (multilinearFormNorm (F j)) := fun j =>
    iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal
      (abs_le_multilinearFormNorm (F j) (hbddF j) (ofProduct hB x) hx)
  have hlt : (⨆ j, operatorBound (Ψ j)) < ⊤ :=
    lt_of_le_of_lt (iSup_le fun j => (hle j).trans (ENNReal.ofReal_le_ofReal (le_ciSup hsup j)))
      ENNReal.ofReal_lt_top
  have hBle : (⨆ i, multilinearFormNorm (F i)) ≤ (⨆ j, operatorBound (Ψ j)).toReal :=
    ciSup_le fun j => by
      refine csSup_le ⟨|F j 0|, 0, fun l => ?_, rfl⟩ ?_
      · simp
      · rintro r ⟨y, hy, rfl⟩
        exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).1
          ((hval j y hy).trans (le_iSup (fun j => operatorBound (Ψ j)) j))
  have hunif : UniformEstimate Ψ (⨆ j, operatorBound (Ψ j)).toReal := fun j x => by
    have h₁ := hest j (ofProduct hB x)
    have h₂ : 0 ≤ ∏ l, ‖ofProduct hB x l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
    exact h₁.trans (mul_le_mul_of_nonneg_right hBle h₂)
  refine ⟨⟨⟨_, hunif⟩, hlt, hunif⟩, fun C hC => ?_⟩
  obtain ⟨h₁, h₂⟩ := difference_bound_and_tendsto hF hq (indexAtTop 𝒥) F C
    (fun j y => hC j (toProduct hB y)) (fun y => hconv (toProduct hB y))
  exact ⟨fun f g j => h₁ (ofProduct hB f) (ofProduct hB g) j,
    fun u x hu => h₂ (fun j => ofProduct hB (u j)) (ofProduct hB x) hu⟩
end Concrete
end BanachForms
open Ambient
theorem Ambient.pointwiseConvergentFormsEquicontinuous_holds
    (hBanach : Ambient.c1WithinComplete)
    (hUB : NormedSpaces.BanachSteinhaus.linearAndMultilinear)
    (hForms : Multilinear.BoundedMultilinearEstimates)
    (hProducts : Ambient.testSpacesAndSepTuples)
    (hSpace : AmbientMetric.Claim) :
    Ambient.pointwiseConvergentFormsEquicontinuous := by
  intro s E q hq W hW hd
  have hB : ∀ l, IsBanachFunctionSpace (E.c1Within s (W l)) (E.normC1 s) := fun l =>
    (hBanach s E (W l) (hW l)).2
  refine ⟨fun x => ?_, BanachForms.convergentBoundedForms_of_complete hB hUB.2 hForms hq⟩
  obtain ⟨-, hprod, -, -⟩ := hProducts s E ⟨1, Set.mem_Ici.2 le_rfl⟩ univ (⋃ l, W l) q hq
  exact (hprod.1 W (fun i => subset_iUnion W i) (fun i j hij =>
    (hSpace s E).2.1.1 (W i) (W j) (hW i) (hW j) (hd hij))).2 (components x) (fun i => (x i).2)
end YangMills.Construction.LimitSpaces
end
