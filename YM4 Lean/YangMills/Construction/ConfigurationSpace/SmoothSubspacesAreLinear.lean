import YangMills.Construction.Continuum.FiniteSeminormsOnTheSchwartzFunctionsProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
namespace SmoothSubspaceLinearity
section Operators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def IsSmoothLinearOp (D : (V → ℂ) → V → ℂ) : Prop :=
  (∀ f, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (D f)) ∧
    (∀ f g, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → D (f + g) = D f + D g) ∧
    ∀ (c : ℂ) (f : V → ℂ), ContDiff ℝ ∞ f → D (c • f) = c • D f
theorem isSmoothLinearOp_id : IsSmoothLinearOp (fun f : V → ℂ => f) :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
theorem IsSmoothLinearOp.comp {D E : (V → ℂ) → V → ℂ} (hD : IsSmoothLinearOp D)
    (hE : IsSmoothLinearOp E) : IsSmoothLinearOp (fun f => D (E f)) := by
  refine ⟨fun f hf => hD.1 _ (hE.1 f hf), fun f g hf hg => ?_, fun c f hf => ?_⟩
  · show D (E (f + g)) = D (E f) + D (E g)
    rw [hE.2.1 f g hf hg, hD.2.1 _ _ (hE.1 f hf) (hE.1 g hg)]
  · show D (E (c • f)) = c • D (E f)
    rw [hE.2.2 c f hf, hD.2.2 c _ (hE.1 f hf)]
theorem IsSmoothLinearOp.iterate {D : (V → ℂ) → V → ℂ} (hD : IsSmoothLinearOp D) (m : ℕ) :
    IsSmoothLinearOp (fun f => D^[m] f) := by
  induction m with
  | zero => exact isSmoothLinearOp_id
  | succ m ih =>
    have h : (fun f => D^[m + 1] f) = fun f => D (D^[m] f) := by
      funext f
      exact Function.iterate_succ_apply' D m f
    rw [h]
    exact hD.comp ih
theorem isSmoothLinearOp_dirDeriv (v : V) :
    IsSmoothLinearOp (dirDeriv v : (V → ℂ) → V → ℂ) := by
  have hder : ∀ f : V → ℂ, ContDiff ℝ ∞ f → ∀ x, HasFDerivAt f (fderiv ℝ f x) x :=
    fun f hf x => ((hf.differentiable (by simp)) x).hasFDerivAt
  refine ⟨fun f hf => ?_, fun f g hf hg => ?_, fun c f hf => ?_⟩
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
  · funext x
    have h := ((hder f hf x).const_smul c).hasLineDerivAt v |>.lineDeriv
    have h₁ := (hder f hf x).hasLineDerivAt v |>.lineDeriv
    simp only [dirDeriv, Pi.smul_apply]
    rw [h₁]
    exact h
theorem isSmoothLinearOp_iterDirDeriv {I : Type*} [Fintype I] [LinearOrder I] (e : I → V)
    (α : MultiIdx I) : IsSmoothLinearOp (iterDirDeriv e α) := by
  have h : ∀ l : List I, IsSmoothLinearOp
      (fun f : V → ℂ => l.foldr (fun ι g => (dirDeriv (e ι))^[α ι] g) f) := by
    intro l
    induction l with
    | nil => exact isSmoothLinearOp_id
    | cons a l ih => exact ((isSmoothLinearOp_dirDeriv (e a)).iterate (α a)).comp ih
  exact h _
end Operators
variable {n : ℕ}
theorem zero_mem_smoothSet : (0 : Config n → ℂ) ∈ smoothSet (Config n) :=
  (contDiff_const : ContDiff ℝ ∞ fun _ : Config n => (0 : ℂ))
theorem add_mem_smoothSet {φ φ' : Config n → ℂ} (h : φ ∈ smoothSet (Config n))
    (h' : φ' ∈ smoothSet (Config n)) : φ + φ' ∈ smoothSet (Config n) :=
  ContDiff.add (show ContDiff ℝ ∞ φ from h) (show ContDiff ℝ ∞ φ' from h')
theorem smul_mem_smoothSet (c : ℂ) {φ : Config n → ℂ} (h : φ ∈ smoothSet (Config n)) :
    c • φ ∈ smoothSet (Config n) :=
  ContDiff.const_smul c (show ContDiff ℝ ∞ φ from h)
theorem configMultiDeriv_add (α : MultiIdx (CoordIndex n)) {φ φ' : Config n → ℂ}
    (h : φ ∈ smoothSet (Config n)) (h' : φ' ∈ smoothSet (Config n)) :
    configMultiDeriv α (φ + φ') = configMultiDeriv α φ + configMultiDeriv α φ' :=
  (isSmoothLinearOp_iterDirDeriv coordBasis α).2.1 φ φ' h h'
theorem configMultiDeriv_smul (α : MultiIdx (CoordIndex n)) (c : ℂ) {φ : Config n → ℂ}
    (h : φ ∈ smoothSet (Config n)) : configMultiDeriv α (c • φ) = c • configMultiDeriv α φ :=
  (isSmoothLinearOp_iterDirDeriv coordBasis α).2.2 c φ h
theorem configMultiDeriv_zero (α : MultiIdx (CoordIndex n)) :
    configMultiDeriv α (0 : Config n → ℂ) = 0 := by
  have h := configMultiDeriv_smul α (0 : ℂ) (zero_mem_smoothSet (n := n))
  simpa using h
theorem polyWeight_nonneg (k : ℕ) (x : Config n) : 0 ≤ (1 + configNorm x) ^ k := by apply _root_.YangMills.Construction.ConfigurationSpace.SchwartzSeminorms.polyWeight_nonneg <;> assumption
theorem smoothSet_isLinear : IsLinearFunctionSet (smoothSet (Config n)) :=
  ⟨zero_mem_smoothSet, fun _ h _ h' => add_mem_smoothSet h h',
    fun c _ h => smul_mem_smoothSet c h⟩
theorem rapidDecaySet_isLinear : IsLinearFunctionSet (rapidDecaySet n) := by
  refine ⟨⟨zero_mem_smoothSet, fun k α => ?_⟩, ?_, ?_⟩
  · simp [weightedDerivSup, configMultiDeriv_zero]
  · rintro φ ⟨h, hb⟩ φ' ⟨h', hb'⟩
    refine ⟨add_mem_smoothSet h h', fun k α => ?_⟩
    refine lt_of_le_of_lt (b := weightedDerivSup k α φ + weightedDerivSup k α φ')
      (iSup_le fun x => ?_) (ENNReal.add_lt_top.2 ⟨hb k α, hb' k α⟩)
    have hw := polyWeight_nonneg k x
    rw [configMultiDeriv_add α h h', Pi.add_apply]
    calc ENNReal.ofReal ((1 + configNorm x) ^ k *
          ‖configMultiDeriv α φ x + configMultiDeriv α φ' x‖)
        ≤ ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖ +
            (1 + configNorm x) ^ k * ‖configMultiDeriv α φ' x‖) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
      _ = ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖) +
            ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ' x‖) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ _ := add_le_add
          (le_iSup (fun x => ENNReal.ofReal
            ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖)) x)
          (le_iSup (fun x => ENNReal.ofReal
            ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ' x‖)) x)
  · rintro c φ ⟨h, hb⟩
    refine ⟨smul_mem_smoothSet c h, fun k α => ?_⟩
    refine lt_of_le_of_lt (b := ENNReal.ofReal ‖c‖ * weightedDerivSup k α φ)
      (iSup_le fun x => ?_) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hb k α))
    have hw := polyWeight_nonneg k x
    rw [configMultiDeriv_smul α c h, Pi.smul_apply, norm_smul]
    calc ENNReal.ofReal ((1 + configNorm x) ^ k * (‖c‖ * ‖configMultiDeriv α φ x‖))
        = ENNReal.ofReal ‖c‖ *
            ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖) := by
          rw [← ENNReal.ofReal_mul (norm_nonneg c)]
          congr 1
          ring
      _ ≤ _ := by
          gcongr
          exact le_iSup
            (fun x => ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖)) x
theorem flatOnDiagonalSet_isLinear : IsLinearFunctionSet (flatOnDiagonalSet n) := by
  refine ⟨⟨zero_mem_smoothSet, fun x _ α => ?_⟩, ?_, ?_⟩
  · rw [configMultiDeriv_zero]
    rfl
  · rintro φ ⟨h, hz⟩ φ' ⟨h', hz'⟩
    refine ⟨add_mem_smoothSet h h', fun x hx α => ?_⟩
    rw [configMultiDeriv_add α h h', Pi.add_apply, hz x hx α, hz' x hx α, add_zero]
  · rintro c φ ⟨h, hz⟩
    refine ⟨smul_mem_smoothSet c h, fun x hx α => ?_⟩
    rw [configMultiDeriv_smul α c h, Pi.smul_apply, hz x hx α, smul_zero]
end SmoothSubspaceLinearity
theorem smoothSubspaces_holds : SmoothSubspaces :=
  fun _ _ => ⟨SmoothSubspaceLinearity.smoothSet_isLinear,
    ⟨fun _ h => h.1, SmoothSubspaceLinearity.rapidDecaySet_isLinear⟩,
    ⟨fun _ h => h.1, SmoothSubspaceLinearity.flatOnDiagonalSet_isLinear⟩⟩
end YangMills.Construction.ConfigurationSpace
end
