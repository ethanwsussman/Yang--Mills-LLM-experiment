import YangMills.Construction.ConfigurationSpace.IterDirDerivLinear
import YangMills.Construction.Continuum.FiniteSeminormsOnTheSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
namespace SchwartzSeminorms
variable {n : ℕ}
theorem finite_setOf_order_le (q : ℕ) :
    {α : MultiIdx (CoordIndex n) | α.order ≤ q}.Finite := by
  refine (Set.Finite.pi' (t := fun _ => Set.Iic q) fun _ => Set.finite_Iic q).subset ?_
  intro α hα i
  exact le_trans (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hα
theorem decaySeminorm_lt_top (k q : ℕ) {f : Config n → ℂ} (hf : f ∈ schwartzSet n) :
    decaySeminorm k q f < ⊤ := by
  have hsup : (finite_setOf_order_le (n := n) q).toFinset.sup
      (fun α => weightedDerivSup k α f) < ⊤ :=
    (Finset.sup_lt_iff bot_lt_top).2 fun α _ => hf.2 k α
  refine lt_of_le_of_lt (iSup₂_le fun α hα => ?_) hsup
  exact Finset.le_sup (f := fun α => weightedDerivSup k α f)
    ((finite_setOf_order_le q).mem_toFinset.2 hα)
theorem configNorm_nonneg (x : Config n) : 0 ≤ configNorm x := Real.sqrt_nonneg _
theorem japaneseBracket_rpow_le (p : ℕ) (x : Config n) :
    (1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) ≤ (1 + configNorm x) ^ p := by
  have h0 := configNorm_nonneg x
  have h1 : 1 + configNorm x ^ 2 ≤ (1 + configNorm x) ^ 2 := by nlinarith
  calc (1 + configNorm x ^ 2) ^ ((p : ℝ) / 2)
      ≤ ((1 + configNorm x) ^ 2) ^ ((p : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = (1 + configNorm x) ^ p := by
        rw [← Real.rpow_natCast (1 + configNorm x) 2, ← Real.rpow_mul (by positivity),
          show ((2 : ℕ) : ℝ) * ((p : ℝ) / 2) = (p : ℝ) by push_cast; ring, Real.rpow_natCast]
theorem sobolevWeightNorm_le_decaySeminorm (p : ℕ) (f : Config n → ℂ) :
    sobolevWeightNorm p f ≤ decaySeminorm p p f := by
  refine iSup_le fun x => iSup₂_le fun α hα => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (japaneseBracket_rpow_le p x) (norm_nonneg _))) ?_
  exact le_trans (le_iSup (fun x => ENNReal.ofReal
    ((1 + configNorm x) ^ p * ‖configMultiDeriv α f x‖)) x)
    (le_iSup₂ (f := fun (α : MultiIdx (CoordIndex n)) (_ : α.order ≤ p) =>
      weightedDerivSup p α f) α hα)
theorem polyWeight_nonneg (k : ℕ) (x : Config n) : 0 ≤ (1 + configNorm x) ^ k := by
  have h := configNorm_nonneg x
  positivity
theorem bracketWeight_nonneg (p : ℕ) (x : Config n) :
    0 ≤ (1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) := by
  positivity
section Terms
variable (hlin : IterDirDerivLinear)
include hlin
theorem ofReal_weighted_deriv_smul (w : ℝ) (α : MultiIdx (CoordIndex n)) (c : ℂ)
    {f : Config n → ℂ} (hf : f ∈ smoothSet (Config n)) (x : Config n) :
    ENNReal.ofReal (w * ‖configMultiDeriv α (c • f) x‖) =
      ENNReal.ofReal ‖c‖ * ENNReal.ofReal (w * ‖configMultiDeriv α f x‖) := by
  have hd : configMultiDeriv α (c • f) = c • configMultiDeriv α f :=
    (hlin (Config n) (CoordIndex n) coordBasis α).2.2 c f hf
  rw [hd, Pi.smul_apply, norm_smul, ← ENNReal.ofReal_mul (norm_nonneg c)]
  congr 1
  ring
theorem ofReal_weighted_deriv_add_le {w : ℝ} (hw : 0 ≤ w) (α : MultiIdx (CoordIndex n))
    {f g : Config n → ℂ} (hf : f ∈ smoothSet (Config n))
    (hg : g ∈ smoothSet (Config n)) (x : Config n) :
    ENNReal.ofReal (w * ‖configMultiDeriv α (f + g) x‖) ≤
      ENNReal.ofReal (w * ‖configMultiDeriv α f x‖) +
        ENNReal.ofReal (w * ‖configMultiDeriv α g x‖) := by
  have hd : configMultiDeriv α (f + g) = configMultiDeriv α f + configMultiDeriv α g :=
    (hlin (Config n) (CoordIndex n) coordBasis α).2.1 f hf g hg
  rw [hd, Pi.add_apply,
    ← ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _)), ← mul_add]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_add_le _ _) hw)
end Terms
section Seminorms
variable (hlin : IterDirDerivLinear)
include hlin
theorem decaySeminorm_smul (k q : ℕ) (c : ℂ) {f : Config n → ℂ}
    (hf : f ∈ smoothSet (Config n)) :
    decaySeminorm k q (c • f) = ENNReal.ofReal ‖c‖ * decaySeminorm k q f := by
  unfold decaySeminorm weightedDerivSup
  simp only [ENNReal.mul_iSup]
  exact iSup_congr fun α => iSup_congr fun _ => iSup_congr fun x =>
    ofReal_weighted_deriv_smul hlin _ α c hf x
theorem sobolevWeightNorm_smul (p : ℕ) (c : ℂ) {f : Config n → ℂ}
    (hf : f ∈ smoothSet (Config n)) :
    sobolevWeightNorm p (c • f) = ENNReal.ofReal ‖c‖ * sobolevWeightNorm p f := by
  unfold sobolevWeightNorm
  simp only [ENNReal.mul_iSup]
  exact iSup_congr fun x => iSup_congr fun α => iSup_congr fun _ =>
    ofReal_weighted_deriv_smul hlin _ α c hf x
theorem decaySeminorm_add_le (k q : ℕ) {f g : Config n → ℂ} (hf : f ∈ smoothSet (Config n))
    (hg : g ∈ smoothSet (Config n)) :
    decaySeminorm k q (f + g) ≤ decaySeminorm k q f + decaySeminorm k q g := by
  have hup : ∀ (ψ : Config n → ℂ) (α : MultiIdx (CoordIndex n)), α.order ≤ q →
      ∀ x, ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α ψ x‖) ≤
        decaySeminorm k q ψ :=
    fun ψ α hα x => le_trans
      (le_iSup (fun x => ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α ψ x‖)) x)
      (le_iSup₂ (f := fun (α : MultiIdx (CoordIndex n)) (_ : α.order ≤ q) =>
        weightedDerivSup k α ψ) α hα)
  refine iSup₂_le fun α hα => iSup_le fun x => ?_
  exact (ofReal_weighted_deriv_add_le hlin (polyWeight_nonneg k x) α hf hg x).trans
    (add_le_add (hup f α hα x) (hup g α hα x))
theorem sobolevWeightNorm_add_le (p : ℕ) {f g : Config n → ℂ} (hf : f ∈ smoothSet (Config n))
    (hg : g ∈ smoothSet (Config n)) :
    sobolevWeightNorm p (f + g) ≤ sobolevWeightNorm p f + sobolevWeightNorm p g := by
  have hup : ∀ (ψ : Config n → ℂ) (x : Config n) (α : MultiIdx (CoordIndex n)), α.order ≤ p →
      ENNReal.ofReal ((1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖configMultiDeriv α ψ x‖) ≤
        sobolevWeightNorm p ψ :=
    fun ψ x α hα => le_iSup_of_le x (le_iSup₂ (f := fun
      (α : MultiIdx (CoordIndex n)) (_ : α.order ≤ p) =>
        ENNReal.ofReal ((1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖configMultiDeriv α ψ x‖)) α hα)
  refine iSup_le fun x => iSup₂_le fun α hα => ?_
  exact (ofReal_weighted_deriv_add_le hlin (bracketWeight_nonneg p x) α hf hg x).trans
    (add_le_add (hup f x α hα) (hup g x α hα))
end Seminorms
end SchwartzSeminorms
open SchwartzSeminorms in
theorem schwartzSeminormsFinite_of_linear (hlin : IterDirDerivLinear) :
    schwartzSeminormsFinite := by
  intro n _ k q p
  refine ⟨fun f hf => ⟨decaySeminorm_lt_top k q hf, sobolevWeightNorm_le_decaySeminorm p f⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact fun f hf => decaySeminorm_lt_top k q hf
  · exact fun c f hf => decaySeminorm_smul hlin k q c hf.1
  · exact fun f hf g hg => decaySeminorm_add_le hlin k q hf.1 hg.1
  · exact fun f hf => lt_of_le_of_lt (sobolevWeightNorm_le_decaySeminorm p f)
      (decaySeminorm_lt_top p p hf)
  · exact fun c f hf => sobolevWeightNorm_smul hlin p c hf.1
  · exact fun f hf g hg => sobolevWeightNorm_add_le hlin p hf.1 hg.1
end YangMills.Construction.ConfigurationSpace
end
