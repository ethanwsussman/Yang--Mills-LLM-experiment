import YangMills.Construction.ConfigurationSpace.MinSeparationProperties
import YangMills.Construction.Continuum.FiniteSeminormsOnTheSchwartzFunctions
import YangMills.Construction.Continuum.TwoFamiliesOfSeminormsOnSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
namespace SeminormFamilies
section Operators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def IsSmoothLocalOp (D : (V → ℂ) → V → ℂ) : Prop :=
  (∀ f, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (D f)) ∧
    (∀ f g, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → D (f + g) = D f + D g) ∧
    ∀ f, tsupport (D f) ⊆ tsupport f
theorem isSmoothLocalOp_id : IsSmoothLocalOp (fun f : V → ℂ => f) :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ => subset_rfl⟩
theorem IsSmoothLocalOp.comp {D E : (V → ℂ) → V → ℂ} (hD : IsSmoothLocalOp D)
    (hE : IsSmoothLocalOp E) : IsSmoothLocalOp (fun f => D (E f)) := by
  refine ⟨fun f hf => hD.1 _ (hE.1 f hf), fun f g hf hg => ?_,
    fun f => (hD.2.2 _).trans (hE.2.2 f)⟩
  show D (E (f + g)) = D (E f) + D (E g)
  rw [hE.2.1 f g hf hg, hD.2.1 _ _ (hE.1 f hf) (hE.1 g hg)]
theorem IsSmoothLocalOp.iterate {D : (V → ℂ) → V → ℂ} (hD : IsSmoothLocalOp D) (m : ℕ) :
    IsSmoothLocalOp (fun f => D^[m] f) := by
  induction m with
  | zero => exact isSmoothLocalOp_id
  | succ m ih =>
    have h : (fun f => D^[m + 1] f) = fun f => D (D^[m] f) := by
      funext f
      exact Function.iterate_succ_apply' D m f
    rw [h]
    exact hD.comp ih
theorem isSmoothLocalOp_dirDeriv (v : V) :
    IsSmoothLocalOp (dirDeriv v : (V → ℂ) → V → ℂ) := by
  have hder : ∀ f : V → ℂ, ContDiff ℝ ∞ f → ∀ x, HasFDerivAt f (fderiv ℝ f x) x :=
    fun f hf x => ((hf.differentiable (by simp)) x).hasFDerivAt
  refine ⟨fun f hf => ?_, fun f g hf hg => ?_, fun f => ?_⟩
  · have h : dirDeriv v f = fun x => fderiv ℝ f x v := by
      funext x
      exact (hder f hf x).hasLineDerivAt v |>.lineDeriv
    rw [h]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  · funext x
    have h := ((hder f hf x).add (hder g hg x)).hasLineDerivAt v |>.lineDeriv
    have h₁ := (hder f hf x).hasLineDerivAt v |>.lineDeriv
    have h₂ := (hder g hg x).hasLineDerivAt v |>.lineDeriv
    simp only [dirDeriv, Pi.add_apply]
    rw [h₁, h₂]
    exact h
  · refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
    by_contra hxf
    have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxf
    apply hx
    show lineDeriv ℝ f x v = 0
    rw [hz.lineDeriv_eq]
    simp [lineDeriv]
theorem isSmoothLocalOp_iterDirDeriv {I : Type*} [Fintype I] [LinearOrder I] (e : I → V)
    (α : MultiIdx I) : IsSmoothLocalOp (iterDirDeriv e α) := by
  have h : ∀ l : List I, IsSmoothLocalOp
      (fun f : V → ℂ => l.foldr (fun ι g => (dirDeriv (e ι))^[α ι] g) f) := by
    intro l
    induction l with
    | nil => exact isSmoothLocalOp_id
    | cons a l ih => exact ((isSmoothLocalOp_dirDeriv (e a)).iterate (α a)).comp ih
  exact h _
end Operators
variable {n : ℕ}
theorem isSmoothLocalOp_configMultiDeriv (α : MultiIdx (CoordIndex n)) :
    IsSmoothLocalOp (configMultiDeriv α) :=
  isSmoothLocalOp_iterDirDeriv coordBasis α
theorem configNorm_nonneg (x : Config n) : 0 ≤ configNorm x := Real.sqrt_nonneg _
theorem continuous_configNorm : Continuous (configNorm : Config n → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun ι _ =>
    ((continuous_apply (ofLex ι).2).comp (continuous_apply (ofLex ι).1)).pow 2)
theorem one_add_pow_le_rpow_weight {k p : ℕ} (hkp : k ≤ p) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ k ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * (1 + a ^ 2) ^ ((p : ℝ) / 2) := by
  have h1 : (1 + a) ^ 2 ≤ 2 * (1 + a ^ 2) := by nlinarith [sq_nonneg (1 - a)]
  have hb : (0 : ℝ) ≤ (1 + a) ^ 2 := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  have hs : (1 : ℝ) ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg a]
  calc (1 + a) ^ k = ((1 + a) ^ 2) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_natCast (1 + a) 2, ← Real.rpow_mul (by positivity),
          show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
    _ ≤ (2 * (1 + a ^ 2)) ^ ((k : ℝ) / 2) := Real.rpow_le_rpow hb h1 hk
    _ = (2 : ℝ) ^ ((k : ℝ) / 2) * (1 + a ^ 2) ^ ((k : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs ?_) (by positivity)
        have : (k : ℝ) ≤ p := by exact_mod_cast hkp
        linarith
theorem decaySeminorm_le_sobolevWeightNorm {k q p : ℕ} (hk : k ≤ p) (hq : q ≤ p)
    (φ : Config n → ℂ) :
    decaySeminorm k q φ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * sobolevWeightNorm p φ := by
  unfold decaySeminorm sobolevWeightNorm weightedDerivSup
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
  calc ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2) *
          ((1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖configMultiDeriv α φ x‖)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (one_add_pow_le_rpow_weight hk (configNorm_nonneg x)) (norm_nonneg _)
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) *
          ENNReal.ofReal ((1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖configMultiDeriv α φ x‖) :=
        ENNReal.ofReal_mul hc
    _ ≤ _ := by
        gcongr
        exact le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le (hα.trans hq) le_rfl))
section OpenSets
variable {ι : Type*} [Nonempty ι] (F : ι → schwartzSet n → ℝ≥0∞)
theorem isOpenForFamily_univ : IsOpenForFamily F Set.univ :=
  fun _ _ => ⟨0, Fin.elim0, 1, one_pos, fun _ _ _ _ => trivial⟩
theorem isOpenForFamily_inter {U W : Set (schwartzSet n)} (hU : IsOpenForFamily F U)
    (hW : IsOpenForFamily F W) : IsOpenForFamily F (U ∩ W) := by
  intro φ hφ
  obtain ⟨s₁, p₁, ε₁, h₁, hs₁⟩ := hU φ hφ.1
  obtain ⟨s₂, p₂, ε₂, h₂, hs₂⟩ := hW φ hφ.2
  refine ⟨s₁ + s₂, Fin.append p₁ p₂, min ε₁ ε₂, lt_min h₁ h₂, fun φ' δ hδ h =>
    ⟨hs₁ φ' δ hδ fun a => ?_, hs₂ φ' δ hδ fun a => ?_⟩⟩
  · have ha := h (Fin.castAdd s₂ a)
    rw [Fin.append_left] at ha
    exact ha.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  · have ha := h (Fin.natAdd s₁ a)
    rw [Fin.append_right] at ha
    exact ha.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
theorem isOpenForFamily_sUnion {S : Set (Set (schwartzSet n))}
    (hS : ∀ U ∈ S, IsOpenForFamily F U) : IsOpenForFamily F (⋃₀ S) := by
  rintro φ ⟨U, hU, hφ⟩
  obtain ⟨s, p, ε, hε, h⟩ := hS U hU φ hφ
  exact ⟨s, p, ε, hε, fun φ' δ hδ ha => ⟨U, hU, h φ' δ hδ ha⟩⟩
end OpenSets
theorem exists_topology_schwartzOpenSets (n : ℕ) : ∃ t : TopologicalSpace (schwartzSet n),
    ∀ U : Set (schwartzSet n), @IsOpen _ t U ↔ U ∈ schwartzOpenSets n :=
  ⟨{ IsOpen := fun U => U ∈ schwartzOpenSets n
     isOpen_univ := isOpenForFamily_univ _
     isOpen_inter := fun _ _ hU hW => isOpenForFamily_inter _ hU hW
     isOpen_sUnion := fun _ hS => isOpenForFamily_sUnion _ hS }, fun _ => Iff.rfl⟩
theorem rpow_half_mul_lt_of_lt {k p : ℕ} (hk : k ≤ p) {ε : ℝ} (hε : 0 < ε) {w : ℝ≥0∞}
    (hw : w < ENNReal.ofReal ((2 : ℝ) ^ (-(p : ℝ) / 2) * ε)) :
    ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * w < ENNReal.ofReal ε := by
  have htop : w ≠ ⊤ := (hw.trans ENNReal.ofReal_lt_top).ne
  have hc : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
  rw [← ENNReal.ofReal_toReal htop] at hw ⊢
  have hr : w.toReal < (2 : ℝ) ^ (-(p : ℝ) / 2) * ε :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hw
  rw [← ENNReal.ofReal_mul hc.le]
  refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
  have hprod : (2 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ (-(p : ℝ) / 2) ≤ 1 := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (k : ℝ) ≤ p := by exact_mod_cast hk
    linarith
  calc (2 : ℝ) ^ ((k : ℝ) / 2) * w.toReal
      < (2 : ℝ) ^ ((k : ℝ) / 2) * ((2 : ℝ) ^ (-(p : ℝ) / 2) * ε) :=
        mul_lt_mul_of_pos_left hr hc
    _ = ((2 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ (-(p : ℝ) / 2)) * ε := by ring
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hprod hε.le
    _ = ε := one_mul ε
theorem generatesSchwartzTopology_sobolevWeightNormFamily
    (hle : ∀ (p : ℕ), ∀ φ ∈ schwartzSet n, sobolevWeightNorm p φ ≤ decaySeminorm p p φ) :
    GeneratesSchwartzTopology (sobolevWeightNormFamily n) := by
  intro U
  constructor
  · intro hU φ hφ
    obtain ⟨s, p, ε, hε, h⟩ := hU φ hφ
    exact ⟨s, fun a => (p a, p a), ε, hε, fun φ' δ hδ ha => h φ' δ hδ fun a =>
      lt_of_le_of_lt (hle (p a) δ.1 δ.2) (ha a)⟩
  · intro hU φ hφ
    obtain ⟨s, p, ε, hε, h⟩ := hU φ hφ
    let P : ℕ := Finset.univ.sup fun a => max (p a).1 (p a).2
    refine ⟨1, fun _ => P, (2 : ℝ) ^ (-(P : ℝ) / 2) * ε, by positivity,
      fun φ' δ hδ ha => h φ' δ hδ fun a => ?_⟩
    have hP : max (p a).1 (p a).2 ≤ P :=
      Finset.le_sup (f := fun a => max (p a).1 (p a).2) (Finset.mem_univ a)
    have hk : (p a).1 ≤ P := (le_max_left _ _).trans hP
    have hq : (p a).2 ≤ P := (le_max_right _ _).trans hP
    have hw : sobolevWeightNorm P δ.1 < ENNReal.ofReal ((2 : ℝ) ^ (-(P : ℝ) / 2) * ε) := ha 0
    exact lt_of_le_of_lt (decaySeminorm_le_sobolevWeightNorm hk hq δ.1)
      (rpow_half_mul_lt_of_lt hk hε hw)
theorem isSchwartzClosed_flatSchwartzSet (n : ℕ) :
    IsSchwartzClosed {φ : schwartzSet n | φ.1 ∈ flatSchwartzSet n} := by
  intro φ hφ
  have hne : ¬ ∀ x ∈ fatDiagonal n, ∀ α : MultiIdx (CoordIndex n),
      configMultiDeriv α φ.1 x = 0 := fun h => hφ ⟨φ.2, h⟩
  push Not at hne
  obtain ⟨x₀, hx₀, α, hα⟩ := hne
  refine ⟨1, fun _ => (0, α.order), ‖configMultiDeriv α φ.1 x₀‖, norm_pos_iff.2 hα,
    fun φ' δ hδ ha => ?_⟩
  intro hflat
  have hz : configMultiDeriv α φ'.1 x₀ = 0 := hflat.2 x₀ hx₀ α
  have hsum : φ'.1 = φ.1 + δ.1 := by rw [hδ]; abel
  have hadd := (isSmoothLocalOp_configMultiDeriv α).2.1 φ.1 δ.1 φ.2.1 δ.2.1
  have hval : configMultiDeriv α δ.1 x₀ = - configMultiDeriv α φ.1 x₀ := by
    have h := congrFun hadd x₀
    rw [← hsum, hz, Pi.add_apply] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hb : ENNReal.ofReal ‖configMultiDeriv α δ.1 x₀‖ ≤ decaySeminorm 0 α.order δ.1 := by
    unfold decaySeminorm weightedDerivSup
    refine le_iSup_of_le α (le_iSup_of_le le_rfl (le_iSup_of_le x₀ ?_))
    simp
  have h0 : decaySeminorm 0 α.order δ.1 < ENNReal.ofReal ‖configMultiDeriv α φ.1 x₀‖ := ha 0
  rw [hval, norm_neg] at hb
  exact absurd (hb.trans_lt h0) (lt_irrefl _)
theorem offDiagonalTestSet_subset_flatSchwartzSet
    (hcomp : (fatDiagonal n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n) :
    offDiagonalTestSet n ⊆ flatSchwartzSet n := by
  rintro φ ⟨⟨hs, hc⟩, hsupp⟩
  have hsub : ∀ α : MultiIdx (CoordIndex n),
      tsupport (configMultiDeriv α φ) ⊆ tsupport φ :=
    fun α => (isSmoothLocalOp_configMultiDeriv α).2.2 φ
  refine ⟨⟨hs, fun k α => ?_⟩, fun x hx α => ?_⟩
  · have hcont : Continuous (configMultiDeriv α φ) :=
      ((isSmoothLocalOp_configMultiDeriv α).1 φ hs).continuous
    have hg : Continuous fun x : Config n => (1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖ :=
      ((continuous_const.add continuous_configNorm).pow k).mul hcont.norm
    have hgs : HasCompactSupport fun x : Config n =>
        (1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖ := by
      refine HasCompactSupport.of_support_subset_isCompact hc (fun x hx => hsub α ?_)
      refine subset_tsupport _ fun h0 => hx ?_
      simp [h0]
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
    refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun x => ?_) ENNReal.ofReal_lt_top
    exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC x))
  · have hnot : x ∉ tsupport φ := fun h => by
      have hm : x ∈ (fatDiagonal n)ᶜ := by
        rw [hcomp]
        exact hsupp h
      exact hm hx
    exact image_eq_zero_of_notMem_tsupport fun h => hnot (hsub α h)
end SeminormFamilies
open SeminormFamilies in
theorem seminormFamiliesComparison_holds
    (hlin : SmoothSubspaces)
    (hsep : MinSeparationProperties)
    (hnorm : schwartzSeminormsFinite) :
    SeminormFamiliesComparison := by
  intro n hn
  have hcomp : (fatDiagonal n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact hsep.2.2.1
    · exact (hsep.1 n h).2.2.1
  obtain ⟨-, ⟨-, hrapid⟩, ⟨-, hflat⟩⟩ := hlin n hn
  refine ⟨fun k q p h φ _ => decaySeminorm_le_sobolevWeightNorm ((le_max_left _ _).trans h)
      ((le_max_right _ _).trans h) φ,
    ⟨exists_topology_schwartzOpenSets n, fun _ => Iff.rfl,
      generatesSchwartzTopology_sobolevWeightNormFamily
        fun p φ hφ => ((hnorm n hn 0 0 p).1 φ hφ).2⟩,
    ⟨⟨fun _ h => h.1, ?_⟩, isSchwartzClosed_flatSchwartzSet n⟩,
    offDiagonalTestSet_subset_flatSchwartzSet hcomp⟩
  rw [flatSchwartzSet_eq_rapidDecaySet_inter]
  exact ⟨⟨hrapid.1, hflat.1⟩,
    fun _ h _ h' => ⟨hrapid.2.1 _ h.1 _ h'.1, hflat.2.1 _ h.2 _ h'.2⟩,
    fun c _ h => ⟨hrapid.2.2 c _ h.1, hflat.2.2 c _ h.2⟩⟩
end YangMills.Construction.ConfigurationSpace
end
