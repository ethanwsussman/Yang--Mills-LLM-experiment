import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationOfARegularChain
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmNearOne
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def criticalUnderGaugedVariationsStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ Y : GaugedVariation F,
              (∀ t ∈ actionTerms S, DifferentiableAt ℝ (fun τ : ℝ =>
                actionTermValue a (variedFieldChain (criticalFieldChain S V v U) Y τ)
                  (variedGauge (criticalGauge S V U) Y τ) t) 0) ∧
              ∑ t ∈ actionTerms S, firstVariation a (criticalFieldChain S V v U) (criticalGauge S V U) Y t = 0
end YangMills.Construction.BlockAverages
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GaugedCriticality
open YangMills.Construction.BlockAverages YangMills.Construction.BlockAverages.ChartCoordinates YangMills.Construction.LatticePaths
variable {F : BlockFrame} {S : Finset F.Cell}
section Differentiability
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}
theorem differentiableAt_gaugedContourAverage_family {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} {k : P → F.Site (j + 1) → UnitQuaternion}
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j)))
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1))
    (h1 : DifferentiableAt ℝ (fun p => ((k p c.1 : UnitQuaternion) : ℍ[ℝ])) p₀)
    (h2 : DifferentiableAt ℝ (fun p => ((k p (c.1 + unitStep (j + 1) c.2) : UnitQuaternion) : ℍ[ℝ])) p₀) :
    DifferentiableAt ℝ (fun p => gaugedContourAverage (X p) (k p) c) p₀ := by
  unfold gaugedContourAverage
  exact (h1.mul (differentiableAt_contourAverage hodd hj h hc)).mul (differentiableAt_unitQuaternion_inv h2)
theorem differentiableAt_gaugedBlockFit_family {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} {k : P → F.Site (j + 1) → UnitQuaternion} {X' : P → F.GaugeField (j + 1)}
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j)))
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1))
    (h1 : DifferentiableAt ℝ (fun p => ((k p c.1 : UnitQuaternion) : ℍ[ℝ])) p₀)
    (h2 : DifferentiableAt ℝ (fun p => ((k p (c.1 + unitStep (j + 1) c.2) : UnitQuaternion) : ℍ[ℝ])) p₀)
    (hX' : DifferentiableAt ℝ (fun p => ((X' p c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) p₀)
    (h0 : gaugedContourAverage (X p₀) (k p₀) c ≠ 0) :
    DifferentiableAt ℝ (fun p => gaugedBlockFit (X p) (k p) (X' p) c) p₀ := by
  have hfr := differentiableAt_gaugedContourAverage_family hodd hj h hc h1 h2
  unfold gaugedBlockFit
  exact (hfr.norm ℝ h0).sub (differentiableAt_re (hfr.mul (differentiableAt_unitQuaternion_inv hX')))
theorem differentiableAt_plaquetteHolonomy {X : P → F.GaugeField 0}
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S 0 : Set (F.Site 0)))
    {q : F.Site 0 × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes S 0) :
    DifferentiableAt ℝ (fun p => ((plaquetteHolonomy (X p) q : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  have := differentiableAt_pathHolonomy h q.1 _ 0 (allAlong_plaquette hq)
  rw [add_siteOfCoords_zero] at this
  exact this
theorem differentiableAt_actionTermValue (hodd : Odd F.blockSide) (a : ℝ) {X : P → F.FieldChain}
    {k : P → F.SiteGauge}
    (hX : ∀ j, j ≤ F.top → GaugeDifferentiableOn (fun p => X p j) p₀ (sitesOfCells S j : Set (F.Site j)))
    (hk : ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1),
      DifferentiableAt ℝ (fun p => ((k p (j + 1) y : UnitQuaternion) : ℍ[ℝ])) p₀)
    (hreg : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), gaugedContourAverage (X p₀ j) (k p₀ (j + 1)) c ≠ 0)
    {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    DifferentiableAt ℝ (fun p => actionTermValue a (X p) (k p) t) p₀ := by
  rcases t with q | ⟨j, c⟩
  · have hq : q ∈ innerPlaquettes S 0 := Finset.inl_mem_disjSum.1 ht
    simp only [actionTermValue]
    exact (differentiableAt_const _).sub
      (differentiableAt_re (differentiableAt_plaquetteHolonomy (hX 0 (Nat.zero_le _)) hq))
  · have h1 := Finset.inr_mem_disjSum.1 ht
    have h2 := Finset.mem_sigma.1 h1
    have hj : j < F.top := Finset.mem_range.1 h2.1
    have hc : c ∈ innerBonds S (j + 1) := h2.2
    simp only [actionTermValue]
    refine (differentiableAt_gaugedBlockFit_family hodd hj (hX j hj.le) hc (hk j hj _ (innerBonds_ends hc).1)
      (hk j hj _ (innerBonds_ends hc).2) ?_ (hreg j hj c hc)).const_mul a
    exact hX (j + 1) hj c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2
theorem sum_actionTermValue (a : ℝ) (X : F.FieldChain) (k : F.SiteGauge) :
    ∑ t ∈ actionTerms S, actionTermValue a X k t = gaugedChainAction a S X k := by
  unfold actionTerms gaugedChainAction wilsonAction
  rw [Finset.sum_disjSum, Finset.sum_sigma, Finset.mul_sum]
  simp only [actionTermValue]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
theorem differentiableAt_gaugedChainAction (hodd : Odd F.blockSide) (a : ℝ) {X : P → F.FieldChain}
    {k : P → F.SiteGauge}
    (hX : ∀ j, j ≤ F.top → GaugeDifferentiableOn (fun p => X p j) p₀ (sitesOfCells S j : Set (F.Site j)))
    (hk : ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1),
      DifferentiableAt ℝ (fun p => ((k p (j + 1) y : UnitQuaternion) : ℍ[ℝ])) p₀)
    (hreg : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), gaugedContourAverage (X p₀ j) (k p₀ (j + 1)) c ≠ 0) :
    DifferentiableAt ℝ (fun p => gaugedChainAction a S (X p) (k p)) p₀ := by
  simp only [← sum_actionTermValue]
  exact DifferentiableAt.fun_sum fun t ht => differentiableAt_actionTermValue hodd a hX hk hreg ht
end Differentiability
theorem gaugedChainAction_congr (hodd : Odd F.blockSide) (a : ℝ) {X X' : F.FieldChain} {k k' : F.SiteGauge}
    (hX : ∀ j, j ≤ F.top → GaugeAgreeOnBonds S j (X j) (X' j))
    (hk : ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1), k (j + 1) y = k' (j + 1) y) :
    gaugedChainAction a S X k = gaugedChainAction a S X' k' := by
  unfold gaugedChainAction
  rw [wilsonAction_congr (hX 0 (Nat.zero_le _))]
  refine congrArg (fun r => _ + a * r)
    (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_)
  have hjn : j < F.top := Finset.mem_range.1 hj
  unfold gaugedBlockFit gaugedContourAverage
  rw [contourAverage_congr hodd hjn (hX j hjn.le) hc, hk j hjn _ (innerBonds_ends hc).1,
    hk j hjn _ (innerBonds_ends hc).2, hX (j + 1) hjn c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2]
theorem polarUnit_coe (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
abbrev ReadIndex (S : Finset F.Cell) : Type :=
  ((j : Fin F.top) × ↥(innerBonds S j.val)) ⊕ ((j : Fin F.top) × ↥(sitesOfCells S (j.val + 1)))
abbrev Displacement (S : Finset F.Cell) : Type := ReadIndex S → ℍ[ℝ]
open Classical in
def displacedField (W : F.FieldChain) (e : Displacement S) : F.FieldChain := fun j x i =>
  if h : j < F.top then
    if hb : (x, i) ∈ innerBonds S j then
      polarUnit ((W j x i : ℍ[ℝ]) + e (Sum.inl ⟨⟨j, h⟩, ⟨(x, i), hb⟩⟩))
    else W j x i
  else W j x i
open Classical in
def displacedGauge (κ : F.SiteGauge) (e : Displacement S) : F.SiteGauge
  | 0 => κ 0
  | m + 1 => fun y =>
    if h : m < F.top then
      if hy : y ∈ sitesOfCells S (m + 1) then
        polarUnit ((κ (m + 1) y : ℍ[ℝ]) + e (Sum.inr ⟨⟨m, h⟩, ⟨y, hy⟩⟩))
      else κ (m + 1) y
    else κ (m + 1) y
def actionOfDisplacement (a : ℝ) (S : Finset F.Cell) (W : F.FieldChain) (κ : F.SiteGauge)
    (e : Displacement S) : ℝ :=
  gaugedChainAction a S (displacedField W e) (displacedGauge κ e)
theorem differentiableAt_apply (idx : ReadIndex S) (e₀ : Displacement S) :
    DifferentiableAt ℝ (fun e : Displacement S => e idx) e₀ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ReadIndex S => ℍ[ℝ]) idx).differentiableAt
theorem displacedField_differentiableOn (W : F.FieldChain) (j : ℕ) :
    GaugeDifferentiableOn (fun e : Displacement S => displacedField W e j) 0
      (sitesOfCells S j : Set (F.Site j)) := by
  intro x i hx hx'
  have hb := mem_innerBonds hx hx'
  by_cases h : j < F.top
  · have e1 : (fun e : Displacement S => ((displacedField W e j x i : UnitQuaternion) : ℍ[ℝ])) =
        fun e : Displacement S =>
          ((polarUnit ((W j x i : ℍ[ℝ]) + e (Sum.inl ⟨⟨j, h⟩, ⟨(x, i), hb⟩⟩)) : UnitQuaternion) : ℍ[ℝ]) := by
      funext e
      simp only [displacedField, dif_pos h, dif_pos hb]
    rw [e1]
    refine differentiableAt_polarUnit ((differentiableAt_const _).add (differentiableAt_apply _ _)) ?_
    simpa using coe_unitQuaternion_ne_zero (W j x i)
  · have e1 : (fun e : Displacement S => ((displacedField W e j x i : UnitQuaternion) : ℍ[ℝ])) =
        fun _ => ((W j x i : UnitQuaternion) : ℍ[ℝ]) := by
      funext e
      simp only [displacedField, dif_neg h]
    rw [e1]
    exact differentiableAt_const _
theorem differentiableAt_displacedGauge (κ : F.SiteGauge) {m : ℕ} (h : m < F.top) {y : F.Site (m + 1)}
    (hy : y ∈ sitesOfCells S (m + 1)) :
    DifferentiableAt ℝ (fun e : Displacement S => ((displacedGauge κ e (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have e1 : (fun e : Displacement S => ((displacedGauge κ e (m + 1) y : UnitQuaternion) : ℍ[ℝ])) =
      fun e : Displacement S =>
        ((polarUnit ((κ (m + 1) y : ℍ[ℝ]) + e (Sum.inr ⟨⟨m, h⟩, ⟨y, hy⟩⟩)) : UnitQuaternion) : ℍ[ℝ]) := by
    funext e
    simp only [displacedGauge, dif_pos h, dif_pos hy]
  rw [e1]
  refine differentiableAt_polarUnit ((differentiableAt_const _).add (differentiableAt_apply _ _)) ?_
  simpa using coe_unitQuaternion_ne_zero (κ (m + 1) y)
theorem displacedField_zero (W : F.FieldChain) : displacedField (S := S) W 0 = W := by
  funext j x i
  unfold displacedField
  split_ifs
  · simp [polarUnit_coe]
  · rfl
  · rfl
theorem displacedGauge_zero (κ : F.SiteGauge) : displacedGauge (S := S) κ 0 = κ := by
  funext m
  cases m with
  | zero => rfl
  | succ m =>
    funext y
    simp only [displacedGauge]
    split_ifs
    · simp [polarUnit_coe]
    · rfl
    · rfl
theorem differentiableAt_actionOfDisplacement (hodd : Odd F.blockSide) (a : ℝ) (W : F.FieldChain)
    (κ : F.SiteGauge)
    (hreg : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), gaugedContourAverage (W j) (κ (j + 1)) c ≠ 0) :
    DifferentiableAt ℝ (actionOfDisplacement a S W κ) 0 := by
  refine differentiableAt_gaugedChainAction hodd a (fun j _ => displacedField_differentiableOn W j)
    (fun j hj y hy => differentiableAt_displacedGauge κ hj hy) ?_
  rw [displacedField_zero, displacedGauge_zero]
  exact hreg
def displacementOf (W : F.FieldChain) (κ : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge) : Displacement S
  | Sum.inl ⟨j, b⟩ => (X j.val b.1.1 b.1.2 : ℍ[ℝ]) - W j.val b.1.1 b.1.2
  | Sum.inr ⟨j, y⟩ => (k (j.val + 1) y.1 : ℍ[ℝ]) - κ (j.val + 1) y.1
theorem actionOfDisplacement_displacementOf (hodd : Odd F.blockSide) (a : ℝ) (W : F.FieldChain)
    (κ : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (htop : GaugeAgreeOnBonds S F.top (X F.top) (W F.top)) :
    actionOfDisplacement a S W κ (displacementOf W κ X k) = gaugedChainAction a S X k := by
  refine gaugedChainAction_congr hodd a (fun j hj x i hx hx' => ?_) (fun j hj y hy => ?_)
  · have hb := mem_innerBonds hx hx'
    by_cases h : j < F.top
    · simp only [displacedField, dif_pos h, dif_pos hb, displacementOf, add_sub_cancel, polarUnit_coe]
    · obtain rfl : j = F.top := by omega
      simp only [displacedField, dif_neg h]
      exact (htop x i hx hx').symm
  · simp only [displacedGauge, dif_pos hj, dif_pos hy, displacementOf, add_sub_cancel, polarUnit_coe]
theorem hasDerivAt_gaugedChainAction_comp (hodd : Odd F.blockSide) (a : ℝ) (W : F.FieldChain) (κ : F.SiteGauge)
    (hΨ : DifferentiableAt ℝ (actionOfDisplacement a S W κ) 0)
    {X : ℝ → F.FieldChain} {k : ℝ → F.SiteGauge} {v : Displacement S}
    (htop : ∀ τ, GaugeAgreeOnBonds S F.top (X τ F.top) (W F.top))
    (h0 : displacementOf (S := S) W κ (X 0) (k 0) = 0)
    (hv : ∀ idx : ReadIndex S, HasDerivAt (fun τ => displacementOf (S := S) W κ (X τ) (k τ) idx) (v idx) 0) :
    HasDerivAt (fun τ => gaugedChainAction a S (X τ) (k τ)) (fderiv ℝ (actionOfDisplacement a S W κ) 0 v) 0 := by
  have hc : HasDerivAt (fun τ => displacementOf (S := S) W κ (X τ) (k τ)) v 0 := hasDerivAt_pi.2 hv
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ))
    (f := fun τ => displacementOf (S := S) W κ (X τ) (k τ))
    (l := actionOfDisplacement a S W κ) (by rw [h0]; exact hΨ.hasFDerivAt) hc
  have e : (fun τ => gaugedChainAction a S (X τ) (k τ)) =
      (actionOfDisplacement a S W κ) ∘ fun τ => displacementOf (S := S) W κ (X τ) (k τ) := by
    funext τ
    exact (actionOfDisplacement_displacementOf hodd a W κ (X τ) (k τ) (htop τ)).symm
  rw [e]
  exact hcomp
def gaugeVelocity (κ : F.SiteGauge) (l : (m : ℕ) → F.Site (m + 1) → imaginaryQuaternions) : Displacement S
  | Sum.inl _ => 0
  | Sum.inr ⟨j, y⟩ => ((l j.val y.1 : imaginaryQuaternions) : ℍ[ℝ]) * κ (j.val + 1) y.1
def fieldVelocity (W : F.FieldChain) (x : (j : ℕ) → F.Site j → Fin 4 → imaginaryQuaternions) : Displacement S
  | Sum.inl ⟨j, b⟩ => ((x j.val b.1.1 b.1.2 : imaginaryQuaternions) : ℍ[ℝ]) * W j.val b.1.1 b.1.2
  | Sum.inr _ => 0
section GaugeInvariance
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_inv_mul_coe_mul (g : UnitQuaternion) (x : ℍ[ℝ]) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((g : ℍ[ℝ]) * x) = x := by
  rw [← mul_assoc, coe_inv_mul_coe, one_mul]
theorem re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem re_conj_unit (A : UnitQuaternion) (q : ℍ[ℝ]) :
    ((A : ℍ[ℝ]) * q * ((A⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by
  rw [re_mul_comm, ← mul_assoc, coe_inv_mul_coe, one_mul]
theorem conj_mul_inv_eq (A B x : UnitQuaternion) (f : ℍ[ℝ]) :
    (A : ℍ[ℝ]) * f * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((A * x * B⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (A : ℍ[ℝ]) * (f * ((x⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((A⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, coe_inv_mul_coe_mul]
theorem gaugedContourAverage_gaugeTransform {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide)
    (hg : gaugeCovarianceStatement)
    (γ : F.Site j → UnitQuaternion) (γ' : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage (gaugeTransform γ X) (fun y => γ' y * k y * (γ (refineSite y))⁻¹) c =
      (γ' c.1 : ℍ[ℝ]) * gaugedContourAverage X k c *
        (((γ' (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have hM := (hg F j hj hL).2.1 γ X c
  unfold gaugedContourAverage
  rw [hM]
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, coe_inv_mul_coe_mul]
theorem gaugedBlockFit_gaugeTransform {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide)
    (hg : gaugeCovarianceStatement)
    (γ : F.Site j → UnitQuaternion) (γ' : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit (gaugeTransform γ X) (fun y => γ' y * k y * (γ (refineSite y))⁻¹) (gaugeTransform γ' X') c =
      gaugedBlockFit X k X' c := by
  unfold gaugedBlockFit
  rw [gaugedContourAverage_gaugeTransform hj hL hg]
  set A := γ' c.1
  set B := γ' (c.1 + unitStep (j + 1) c.2)
  set f := gaugedContourAverage X k c
  have hn : ‖(A : ℍ[ℝ]) * f * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖f‖ := by
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion]
    ring
  have hr : ((A : ℍ[ℝ]) * f * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      (((gaugeTransform γ' X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      (f * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
    rw [show gaugeTransform γ' X' c.1 c.2 = A * X' c.1 c.2 * B⁻¹ from rfl, conj_mul_inv_eq, re_conj_unit]
  rw [hn, hr]
def gaugedLinks (k Γ : F.SiteGauge) : F.SiteGauge
  | 0 => k 0
  | j + 1 => gaugedLink k Γ j
theorem gaugedChainAction_gaugeTransform (hL : 0 < F.blockSide) (hg : gaugeCovarianceStatement) (a : ℝ)
    (X : F.FieldChain) (k Γ : F.SiteGauge) :
    gaugedChainAction a S (gaugedChainFields X Γ) (gaugedLinks k Γ) = gaugedChainAction a S X k := by
  unfold gaugedChainAction wilsonAction
  have h0 : 0 < F.top := Nat.succ_pos _
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    have := (hg F 0 h0 hL).2.2.1 (Γ 0) (X 0) p
    simp only [gaugedChainFields]
    rw [this]
    simp only [Submonoid.coe_mul]
    rw [re_conj_unit]
  · refine congrArg (fun r => a * r)
      (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_)
    exact gaugedBlockFit_gaugeTransform (Finset.mem_range.1 hj) hL hg (Γ j) (Γ (j + 1)) (X j) (k (j + 1))
      (X (j + 1)) c
end GaugeInvariance
section Logarithm
def lieLog (g : UnitQuaternion) : imaginaryQuaternions :=
  ⟨unitQuaternionLog g, by show (unitQuaternionLog g).re = 0; exact re_unitQuaternionLog g⟩
theorem expUnit_lieLog (g : UnitQuaternion) : expUnit (lieLog g) = g := expUnit_unitQuaternionLog g
theorem lieLog_expUnit {w : imaginaryQuaternions} (h : ‖(w : ℍ[ℝ])‖ ≤ 1 / 8) : lieLog (expUnit w) = w :=
  Subtype.ext (unitQuaternionLog_expUnit h)
theorem exists_logRadius : ∃ ε : ℝ, 0 < ε ∧ ∀ h : UnitQuaternion, ‖(h : ℍ[ℝ]) - 1‖ < ε →
    unitQuaternionLog h = QuaternionLog.qlog (h : ℍ[ℝ]) ∧
      DifferentiableAt ℝ QuaternionLog.qlog (h : ℍ[ℝ]) := by
  have hc : Filter.Tendsto QuaternionLog.qlog (nhds 1) (nhds 0) := by
    have := QuaternionLog.hasStrictFDerivAt_qlog_one.hasFDerivAt.continuousAt.tendsto
    rwa [QuaternionLog.qlog_one] at this
  have h2 : ∀ᶠ g in nhds (1 : ℍ[ℝ]), ‖QuaternionLog.qlog g‖ < 1 / 8 := by
    have := hc.eventually (Metric.ball_mem_nhds (0 : ℍ[ℝ]) (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [this] with g hg
    simpa using hg
  obtain ⟨r, hr, h3⟩ := Metric.eventually_nhds_iff.1 h2
  have hr0 := QuaternionLog.qlogRadii_spec
  refine ⟨min r QuaternionLog.rightRadius, lt_min hr hr0.right_pos, fun h hh => ?_⟩
  have h4 : ‖(h : ℍ[ℝ]) - 1‖ < QuaternionLog.rightRadius := lt_of_lt_of_le hh (min_le_right _ _)
  have h5 : ‖QuaternionLog.qlog (h : ℍ[ℝ])‖ < 1 / 8 :=
    h3 (by simpa [dist_eq_norm] using lt_of_lt_of_le hh (min_le_left _ _))
  refine ⟨?_, (hr0.contDiffAt _ h4).differentiableAt (by norm_num)⟩
  set w := QuaternionLog.qlog (h : ℍ[ℝ]) with hw
  have he : NormedSpace.exp w = (h : ℍ[ℝ]) := hr0.exp_qlog _ h4
  have hre : w.re = 0 := by
    have h6 : ‖NormedSpace.exp w‖ = 1 := by rw [he, norm_coe_unitQuaternion]
    rw [Quaternion.norm_exp, ← Real.exp_eq_exp_ℝ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h6
    exact Real.exp_eq_one_iff _ |>.1 h6
  have hg : expUnit ⟨w, hre⟩ = h := Subtype.ext he
  have := unitQuaternionLog_expUnit (w := ⟨w, hre⟩) h5.le
  rw [hg] at this
  exact this
def logRadius : ℝ := exists_logRadius.choose
theorem logRadius_pos : 0 < logRadius := exists_logRadius.choose_spec.1
theorem unitQuaternionLog_eq_qlog {h : UnitQuaternion} (hh : ‖(h : ℍ[ℝ]) - 1‖ < logRadius) :
    unitQuaternionLog h = QuaternionLog.qlog (h : ℍ[ℝ]) ∧
      DifferentiableAt ℝ QuaternionLog.qlog (h : ℍ[ℝ]) :=
  exists_logRadius.choose_spec.2 h hh
def imaginaryPartCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := imaginaryPart
      map_add' := fun a b => Subtype.ext (pureComponent_add a b)
      map_smul' := fun r a => Subtype.ext (pureComponent_smul r a) }
theorem imaginaryPartCLM_apply (q : ℍ[ℝ]) :
    ((imaginaryPartCLM q : imaginaryQuaternions) : ℍ[ℝ]) = pureComponent q := rfl
theorem lieLog_eq_imaginaryPartCLM (h : UnitQuaternion) : lieLog h = imaginaryPartCLM (unitQuaternionLog h) :=
  Subtype.ext (by
    rw [imaginaryPartCLM_apply]; exact (pureComponent_of_re_eq_zero (re_unitQuaternionLog h)).symm)
theorem differentiableAt_lieLog {g : ℝ → UnitQuaternion}
    (hd : DifferentiableAt ℝ (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) 0)
    (h0 : ‖((g 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ < logRadius) :
    DifferentiableAt ℝ (fun τ => lieLog (g τ)) 0 := by
  have hev : ∀ᶠ τ in nhds (0 : ℝ), ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖ < logRadius := by
    have hc : ContinuousAt (fun τ => ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖) 0 :=
      (hd.continuousAt.sub continuousAt_const).norm
    exact hc.eventually_lt continuousAt_const h0
  have e : (fun τ => lieLog (g τ)) =ᶠ[nhds 0]
      fun τ => imaginaryPartCLM (QuaternionLog.qlog ((g τ : UnitQuaternion) : ℍ[ℝ])) := by
    filter_upwards [hev] with τ hτ
    rw [lieLog_eq_imaginaryPartCLM, (unitQuaternionLog_eq_qlog hτ).1]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ e
  have h1 : DifferentiableAt ℝ (fun τ => QuaternionLog.qlog ((g τ : UnitQuaternion) : ℍ[ℝ])) 0 :=
    DifferentiableAt.comp (g := QuaternionLog.qlog) (f := fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) 0
      (unitQuaternionLog_eq_qlog h0).2 hd
  exact imaginaryPartCLM.differentiableAt.comp 0 h1
theorem norm_expUnit_sub_one_lt {w : imaginaryQuaternions} (h : ‖(w : ℍ[ℝ])‖ < logRadius) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ < logRadius :=
  lt_of_le_of_lt (norm_exp_sub_one_le w.2) h
end Logarithm
section Chart
def balancingLinks (R X : F.FieldChain) : F.SiteGauge
  | 0 => fun _ => 1
  | j + 1 => balancingGauge (X j) (R j)
open Classical in
def chartOf (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (X : F.FieldChain) : ChainChart F :=
  ⟨fun x i => if (x, i) ∈ innerBonds S 0 then lieLog (X 0 x i * (R 0 x i)⁻¹) else U.fine x i,
    fun j y i => if j + 1 < F.top ∧ (y, i) ∈ innerBonds S (j + 1) then
      lieLog (X (j + 1) y i * (polarUnit (gaugedContourAverage (X j) (balancingGauge (X j) (R j)) (y, i)))⁻¹ *
        (referenceDefect R j (y, i))⁻¹)
      else U.coarse j y i⟩
theorem chartField_chartOf (hodd : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F) (X : F.FieldChain) :
    ∀ j, j < F.top → GaugeAgreeOnBonds S j (chartField R (chartOf S R U X) j) (X j) := by
  intro j
  induction j with
  | zero =>
    intro _ x i hx hx'
    have hb := mem_innerBonds hx hx'
    simp only [chartField, chartOf, if_pos hb, expUnit_lieLog, inv_mul_cancel_right]
  | succ j ih =>
    intro hj x i hx hx'
    have hb := mem_innerBonds hx hx'
    have e := gaugedContourAverage_congr hodd (by omega) (R j) (ih (by omega)) hb
    simp only [chartField]
    rw [e]
    simp only [chartOf]
    rw [if_pos ⟨hj, hb⟩, expUnit_lieLog]
    simp [mul_assoc]
theorem chartAction_chartOf (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain) (U : ChainChart F)
    (X : F.FieldChain) (V : F.GaugeField F.top) (htop : GaugeAgreeOnBonds S F.top (X F.top) V) :
    chartAction a S R (chartOf S R U X) V = gaugedChainAction a S X (balancingLinks R X) := by
  unfold chartAction
  refine gaugedChainAction_congr hodd a (fun j hj x i hx hx' => ?_) (fun j hj y hy => ?_)
  · by_cases h : j < F.top
    · rw [chartChain_of_lt R _ V h]
      exact chartField_chartOf hodd R U X j h x i hx hx'
    · obtain rfl : j = F.top := by omega
      rw [chartChain_top R _ V]
      exact (htop x i hx hx').symm
  · exact balancingGauge_congr hodd hj (R j) (chartField_chartOf hodd R U X j hj) hy
theorem mul_inv_reference_eq_expUnit_fine (R : F.FieldChain) (U : ChainChart F) {X₀ : F.FieldChain}
    (h0 : GaugeAgreeOnBonds S 0 (X₀ 0) (chartField R U 0)) {b : F.Site 0 × Fin 4}
    (hb : b ∈ innerBonds S 0) :
    X₀ 0 b.1 b.2 * (R 0 b.1 b.2)⁻¹ = expUnit (U.fine b.1 b.2) := by
  rw [h0 b.1 b.2 (innerBonds_ends hb).1 (innerBonds_ends hb).2]
  simp only [chartField, mul_inv_cancel_right]
theorem coarse_ratio_eq_expUnit (hodd : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F)
    {X₀ : F.FieldChain} {j : ℕ} (hj : j + 1 < F.top)
    (h0 : ∀ j, j < F.top → GaugeAgreeOnBonds S j (X₀ j) (chartField R U j)) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    X₀ (j + 1) c.1 c.2 * (polarUnit (gaugedContourAverage (X₀ j) (balancingGauge (X₀ j) (R j)) c))⁻¹ *
      (referenceDefect R j c)⁻¹ = expUnit (U.coarse j c.1 c.2) := by
  have e := gaugedContourAverage_congr hodd (by omega) (R j) (h0 j (by omega)) hc
  rw [h0 (j + 1) hj c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2, e]
  simp only [chartField]
  simp [mul_assoc]
theorem chartOf_agreeOn (hodd : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F) {X₀ : F.FieldChain}
    (h0 : ∀ j, j < F.top → GaugeAgreeOnBonds S j (X₀ j) (chartField R U j))
    (hu : ∀ b ∈ innerBonds S 0, ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 / 8)
    (hmu : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      ‖((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 / 8) :
    ChartEqOnBonds S (chartOf S R U X₀) U := by
  refine ⟨fun b hb => ?_, fun j hj c hc => ?_⟩
  · have hb' : (b.1, b.2) ∈ innerBonds S 0 := hb
    simp only [chartOf]
    rw [if_pos hb', mul_inv_reference_eq_expUnit_fine R U (h0 0 (Nat.succ_pos _)) hb, lieLog_expUnit (hu b hb)]
  · have hc' : (c.1, c.2) ∈ innerBonds S (j + 1) := hc
    simp only [chartOf]
    rw [if_pos ⟨hj, hc'⟩]
    have := coarse_ratio_eq_expUnit hodd R U hj h0 hc
    simp only [Prod.mk.eta]
    rw [this, lieLog_expUnit (hmu j hj c hc)]
theorem hasDerivAt_zero_of_balanced (hodd : Odd F.blockSide) (hfv : regularChainFirstVariationStatement)
    (a : ℝ) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (hreg : ChartIsRegular S R U)
    (hcrit : ∀ A, IsStationaryAlong a S R V U A)
    (hu : ∀ b ∈ innerBonds S 0,
      ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < min logRadius (1 / 8))
    (hmu : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      ‖((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < min logRadius (1 / 8))
    {X : ℝ → F.FieldChain}
    (hX : ∀ j, j < F.top → GaugeDifferentiableOn (fun τ => X τ j) 0 (sitesOfCells S j : Set (F.Site j)))
    (h0 : ∀ j, j < F.top → GaugeAgreeOnBonds S j (X 0 j) (chartField R U j))
    (htop : ∀ τ, GaugeAgreeOnBonds S F.top (X τ F.top) V) :
    HasDerivAt (fun τ => gaugedChainAction a S (X τ) (balancingLinks R (X τ))) 0 0 := by
  obtain ⟨D, -, -, hcur⟩ := hfv F a S R U V hodd hreg
  have hD : ∀ A, D A = 0 := by
    intro A
    have hc : IsChartCurve S (chartMove U A) U A := by
      refine ⟨⟨fun b _ => by simp [chartMove], fun j _ c _ => by simp [chartMove]⟩, fun b _ => ?_,
        fun j _ c _ => ?_⟩
      · simp only [chartMove]
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (A.fine b.1 b.2)).const_add (U.fine b.1 b.2)
      · simp only [chartMove]
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (A.coarse j c.1 c.2)).const_add (U.coarse j c.1 c.2)
    exact (hcur _ A hc).unique (hcrit A)
  set C : ℝ → ChainChart F := fun τ => chartOf S R U (X τ) with hC
  have hdu : ∀ b ∈ innerBonds S 0, DifferentiableAt ℝ (fun τ => (C τ).fine b.1 b.2) 0 := by
    intro b hb
    have hb' : (b.1, b.2) ∈ innerBonds S 0 := hb
    have e : (fun τ => (C τ).fine b.1 b.2) = fun τ => lieLog (X τ 0 b.1 b.2 * (R 0 b.1 b.2)⁻¹) := by
      funext τ
      simp only [hC, chartOf]
      rw [if_pos hb']
    rw [e]
    refine differentiableAt_lieLog (differentiableAt_unitQuaternion_mul
      (hX 0 (Nat.succ_pos _) _ _ (innerBonds_ends hb).1 (innerBonds_ends hb).2) (differentiableAt_const _)) ?_
    rw [mul_inv_reference_eq_expUnit_fine R U (h0 0 (Nat.succ_pos _)) hb]
    exact norm_expUnit_sub_one_lt (lt_of_lt_of_le (hu b hb) (min_le_left _ _))
  have hdmu : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      DifferentiableAt ℝ (fun τ => (C τ).coarse j c.1 c.2) 0 := by
    intro j hj c hc
    have hc' : (c.1, c.2) ∈ innerBonds S (j + 1) := hc
    have e : (fun τ => (C τ).coarse j c.1 c.2) = fun τ =>
        lieLog (X τ (j + 1) c.1 c.2 *
          (polarUnit (gaugedContourAverage (X τ j) (balancingGauge (X τ j) (R j)) c))⁻¹ *
          (referenceDefect R j c)⁻¹) := by
      funext τ
      simp only [hC, chartOf]
      rw [if_pos ⟨hj, hc'⟩]
    rw [e]
    have hj' : j < F.top := by omega
    have l1 : relativePathAverage (X 0 j) (R j) c.1 ≠ 0 := by
      rw [relativePathAverage_congr hodd hj' (R j) (h0 j hj') (innerBonds_ends hc).1]
      exact (hreg j hj').1 _ (innerBonds_ends hc).1
    have l2 : relativePathAverage (X 0 j) (R j) (c.1 + unitStep (j + 1) c.2) ≠ 0 := by
      rw [relativePathAverage_congr hodd hj' (R j) (h0 j hj') (innerBonds_ends hc).2]
      exact (hreg j hj').1 _ (innerBonds_ends hc).2
    have l3 : gaugedContourAverage (X 0 j) (balancingGauge (X 0 j) (R j)) c ≠ 0 := by
      rw [gaugedContourAverage_congr hodd hj' (R j) (h0 j hj') hc]
      exact (hreg j hj').2 _ hc
    have hfr := differentiableAt_gaugedContourAverage hodd hj' (R j) (hX j hj') hc l1 l2
    refine differentiableAt_lieLog (differentiableAt_unitQuaternion_mul (differentiableAt_unitQuaternion_mul
      (hX (j + 1) hj _ _ (innerBonds_ends hc).1 (innerBonds_ends hc).2)
      (differentiableAt_unitQuaternion_inv (differentiableAt_polarUnit hfr l3))) (differentiableAt_const _)) ?_
    rw [coarse_ratio_eq_expUnit hodd R U hj h0 hc]
    exact norm_expUnit_sub_one_lt (lt_of_lt_of_le (hmu j hj c hc) (min_le_left _ _))
  set A : ChainChart F := ⟨fun x i => deriv (fun τ => (C τ).fine x i) 0,
    fun j y i => deriv (fun τ => (C τ).coarse j y i) 0⟩ with hA
  have hcv : IsChartCurve S C U A :=
    ⟨chartOf_agreeOn hodd R U h0 (fun b hb => (hu b hb).le.trans (min_le_right _ _))
      (fun j hj c hc => (hmu j hj c hc).le.trans (min_le_right _ _)),
      fun b hb => (hdu b hb).hasDerivAt, fun j hj c hc => (hdmu j hj c hc).hasDerivAt⟩
  have hfin := hcur C A hcv
  rw [hD A] at hfin
  have e : (fun τ => gaugedChainAction a S (X τ) (balancingLinks R (X τ))) =
      fun τ => chartAction a S R (C τ) V := by
    funext τ
    exact (chartAction_chartOf hodd a R U (X τ) V (htop τ)).symm
  rw [e]
  exact hfin
end Chart
section Algebra
theorem hasDerivAt_quaternion_star {f : ℝ → ℍ[ℝ]} {f' : ℍ[ℝ]} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun τ => star (f τ)) (star f') x := by
  let L : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
    { toFun := star, map_add' := star_add, map_smul' := fun c a => Quaternion.star_smul c a,
      cont := continuous_star }
  exact L.hasFDerivAt.comp_hasDerivAt x h
theorem re_mul_star_eq_zero_of_hasDerivAt {h : ℝ → UnitQuaternion} {v : ℍ[ℝ]}
    (hv : HasDerivAt (fun τ => ((h τ : UnitQuaternion) : ℍ[ℝ])) v 0) :
    (v * star ((h 0 : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
  have hs : HasDerivAt (fun τ => star ((h τ : UnitQuaternion) : ℍ[ℝ])) (star v) 0 :=
    hasDerivAt_quaternion_star hv
  have hm := hv.mul hs
  have hc : ((fun τ => ((h τ : UnitQuaternion) : ℍ[ℝ])) * fun τ => star ((h τ : UnitQuaternion) : ℍ[ℝ])) =
      fun _ => 1 := by
    funext τ
    exact (Unitary.mem_iff.1 (h τ).2).2
  rw [hc] at hm
  have he := hm.unique (hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ]))
  have hr := congrArg reCLM he
  rw [map_add, map_zero] at hr
  change (v * star ((h 0 : UnitQuaternion) : ℍ[ℝ])).re + (((h 0 : UnitQuaternion) : ℍ[ℝ]) * star v).re = 0 at hr
  have h2 : (((h 0 : UnitQuaternion) : ℍ[ℝ]) * star v).re = (v * star ((h 0 : UnitQuaternion) : ℍ[ℝ])).re := by
    have := Quaternion.re_star (v * star ((h 0 : UnitQuaternion) : ℍ[ℝ]))
    rw [star_mul, star_star] at this
    exact this
  linarith
theorem exists_hasDerivAt_polarUnit_inv {Q : ℝ → ℍ[ℝ]} {p : ℍ[ℝ]} (hQ : HasDerivAt Q p 0) (h0 : Q 0 ≠ 0) :
    ∃ v, HasDerivAt (fun τ => (((polarUnit (Q τ))⁻¹ : UnitQuaternion) : ℍ[ℝ])) v 0 ∧
      v * ((polarUnit (Q 0) : UnitQuaternion) : ℍ[ℝ]) =
        ‖Q 0‖⁻¹ • pureComponent (star p * ((polarUnit (Q 0) : UnitQuaternion) : ℍ[ℝ])) := by
  have hne : ∀ᶠ τ in nhds (0 : ℝ), Q τ ≠ 0 := hQ.continuousAt.eventually_ne h0
  have hN : DifferentiableAt ℝ (fun τ => ‖Q τ‖⁻¹) 0 :=
    (hQ.differentiableAt.norm ℝ h0).inv (norm_ne_zero_iff.2 h0)
  have hs : HasDerivAt (fun τ => star (Q τ)) (star p) 0 := hasDerivAt_quaternion_star hQ
  have hv := hN.hasDerivAt.smul hs
  have hcurve : HasDerivAt (fun τ => (((polarUnit (Q τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (‖Q 0‖⁻¹ • star p + deriv (fun τ => ‖Q τ‖⁻¹) 0 • star (Q 0)) 0 := by
    refine hv.congr_of_eventuallyEq ?_
    filter_upwards [hne] with τ hτ
    rw [coe_unitQuaternion_inv, coe_polarUnit hτ, quaternion_star_real_smul]
    rfl
  refine ⟨_, hcurve, ?_⟩
  have ht := re_mul_star_eq_zero_of_hasDerivAt hcurve
  rw [coe_unitQuaternion_inv, star_star] at ht
  rw [← pureComponent_of_re_eq_zero ht, add_mul, pureComponent_add, smul_mul_assoc, smul_mul_assoc,
    pureComponent_smul, pureComponent_smul]
  have hz : pureComponent (star (Q 0) * ((polarUnit (Q 0) : UnitQuaternion) : ℍ[ℝ])) = 0 := by
    rw [coe_polarUnit h0, mul_smul_comm, pureComponent_smul, Quaternion.star_mul_self, pureComponent_coe,
      smul_zero]
  rw [hz, smul_zero, add_zero]
theorem exists_imaginaryPart_mul_eq {u : ℍ[ℝ]} (hu : u.re ≠ 0) (φ : imaginaryQuaternions) :
    ∃ ζ : imaginaryQuaternions, pureComponent ((ζ : ℍ[ℝ]) * u) = φ := by
  let T : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions :=
    { toFun := fun ζ => imaginaryPart ((ζ : ℍ[ℝ]) * u)
      map_add' := fun a b => Subtype.ext (by
        show pureComponent (((a + b : imaginaryQuaternions) : ℍ[ℝ]) * u) =
          pureComponent ((a : ℍ[ℝ]) * u) + pureComponent ((b : ℍ[ℝ]) * u)
        rw [Submodule.coe_add, add_mul, pureComponent_add])
      map_smul' := fun r a => Subtype.ext (by
        show pureComponent (((r • a : imaginaryQuaternions) : ℍ[ℝ]) * u) = r • pureComponent ((a : ℍ[ℝ]) * u)
        rw [Submodule.coe_smul, smul_mul_assoc, pureComponent_smul]) }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ζ hz
    have hz' : pureComponent ((ζ : ℍ[ℝ]) * u) = 0 :=
      congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) hz
    have h1 := re_add_pureComponent ((ζ : ℍ[ℝ]) * u)
    rw [hz', add_zero] at h1
    have hre : (ζ : ℍ[ℝ]).re = 0 := ζ.2
    have h2 : (star (ζ : ℍ[ℝ]) * ((ζ : ℍ[ℝ]) * u)).re = Quaternion.normSq (ζ : ℍ[ℝ]) * u.re := by
      rw [← mul_assoc, Quaternion.star_mul_self]
      simp
    have h3 : (star (ζ : ℍ[ℝ]) * ((ζ : ℍ[ℝ]) * u)).re = 0 := by
      rw [← h1]
      simp [hre]
    rw [h3] at h2
    have h4 : Quaternion.normSq (ζ : ℍ[ℝ]) = 0 := by
      rcases mul_eq_zero.1 h2.symm with h | h
      · exact h
      · exact absurd h hu
    exact Subtype.ext (Quaternion.normSq_eq_zero.1 h4)
  have hsur : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨ζ, hζ⟩ := hsur φ
  exact ⟨ζ, congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) hζ⟩
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
theorem hasDerivAt_expUnit_smul (ζ : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • ζ) : UnitQuaternion) : ℍ[ℝ])) (ζ : ℍ[ℝ]) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (ζ : ℍ[ℝ]) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
theorem hasDerivAt_add_smul_inv_sub_one (q : ℍ[ℝ]) (c : ℝ) (ζ : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => q + c • ((((expUnit (τ • ζ))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1))
      (c • star (ζ : ℍ[ℝ])) 0 := by
  have h2 : HasDerivAt (fun τ : ℝ => (((expUnit (τ • ζ))⁻¹ : UnitQuaternion) : ℍ[ℝ])) (star (ζ : ℍ[ℝ])) 0 :=
    hasDerivAt_quaternion_star (hasDerivAt_expUnit_smul ζ)
  exact ((h2.sub_const 1).const_smul c).const_add q
end Algebra
section Blocks
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem siteOfCoords_endpoint (j : ℕ) (l : List PathStep) :
    ∀ u : LatticeFractionalIntegration.Lattice4,
      siteOfCoords (F := F) j (endpoint u l) = siteOfCoords j u + pathDisplacement j l := by
  induction l with
  | nil =>
    intro u
    simp [endpoint, pathDisplacement]
  | cons st r ih =>
    intro u
    simp only [endpoint]
    rw [ih, siteOfCoords_add, ← stepDisplacement_eq_siteOfCoords]
    simp only [pathDisplacement, List.map_cons, List.sum_cons]
    rw [add_assoc]
theorem pathDisplacement_axisPath (j : ℕ) (h : LatticeFractionalIntegration.Lattice4)
    (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
theorem axisPath_zero (π : Equiv.Perm (Fin 4)) :
    axisPath (0 : LatticeFractionalIntegration.Lattice4) π = [] := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.axisPath_zero <;> assumption
theorem period_eq_mul_succ (j : ℕ) (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.blockSide * F.period (j + 1) i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_succ <;> assumption
theorem eq_zero_of_refineSite_add (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) {y y' : F.Site (j + 1)}
    {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube F.blockSide) (he : refineSite y + siteOfCoords j h = refineSite y') : h = 0 := by
  funext i
  have h1 := congrFun he i
  simp only [refineSite, siteOfCoords, Pi.add_apply] at h1
  rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub, period_eq_mul_succ j hj i] at h1
  have hL : (F.blockSide : ℤ) ∣ h i := by
    have h2 : (F.blockSide : ℤ) ∣ (F.blockSide : ℤ) * siteCoords y' i -
        ((F.blockSide : ℤ) * siteCoords y i + h i) :=
      dvd_trans (by push_cast; exact Dvd.intro _ rfl) h1
    have h3 : (F.blockSide : ℤ) ∣ (F.blockSide : ℤ) * siteCoords y' i - (F.blockSide : ℤ) * siteCoords y i :=
      by rw [← mul_sub]; exact Dvd.intro _ rfl
    have h4 := dvd_sub h3 h2
    have e : (F.blockSide : ℤ) * siteCoords y' i - (F.blockSide : ℤ) * siteCoords y i -
      ((F.blockSide : ℤ) * siteCoords y' i - ((F.blockSide : ℤ) * siteCoords y i + h i)) = h i := by ring
    rwa [e] at h4
  have hb := ((mem_centredCube_iff _ _).1 hh) i
  have hpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  refine Int.eq_zero_of_abs_lt_dvd hL ?_
  rw [abs_lt]
  constructor <;> omega
theorem zero_mem_centredCube (hodd : Odd F.blockSide) :
    (0 : LatticeFractionalIntegration.Lattice4) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.GaugeFixing.zero_mem_centredCube <;> assumption
theorem relativePathAverage_gaugeTransform (hodd : Odd F.blockSide) {j : ℕ} {γ : F.Site j → UnitQuaternion}
    (X R : F.GaugeField j) (y : F.Site (j + 1))
    (hγ : ∀ h ∈ centredCube F.blockSide, h ≠ 0 → γ (refineSite y + siteOfCoords j h) = 1) :
    relativePathAverage (gaugeTransform γ X) R y = (γ (refineSite y) : ℍ[ℝ]) *
      (relativePathAverage X R y +
        ((F.blockSide : ℝ) ^ 4)⁻¹ • ((((γ (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)) := by
  set E : ℍ[ℝ] := (((γ (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 with hE
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (gaugeTransform γ X) (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (γ (refineSite y) : ℍ[ℝ]) * (((pathHolonomy X (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
          if h = 0 then E else 0) := by
    intro h hh π
    rw [pathHolonomy_gaugeTransform, pathDisplacement_axisPath]
    by_cases h0 : h = 0
    · subst h0
      rw [axisPath_zero, siteOfCoords_zero, if_pos rfl, hE]
      simp only [pathHolonomy, mul_one, add_zero, inv_one]
      have e1 : ((1 : UnitQuaternion) : ℍ[ℝ]) = 1 := rfl
      rw [mul_inv_cancel, e1, add_sub_cancel, coe_mul_coe_inv]
    · rw [hγ h hh h0, if_neg h0]
      simp only [inv_one, mul_one, add_zero, Submonoid.coe_mul, mul_assoc]
  have hs : ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (if h = 0 then E else 0) =
      (24 : ℝ) • E := by
    rw [Finset.sum_eq_single (0 : LatticeFractionalIntegration.Lattice4)]
    · simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rw [show Nat.factorial 4 = 24 from rfl]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      norm_num
    · intro b _ hb
      simp [hb]
    · intro hn
      exact absurd (zero_mem_centredCube hodd) hn
  have hL : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  unfold relativePathAverage
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => hterm h hh π]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hs, ← mul_smul_comm, smul_add, smul_smul]
  congr 3
  field_simp
end Blocks
structure CriticalSetting (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) : Prop where
  odd : Odd F.blockSide
  covariance : gaugeCovarianceStatement
  variation : regularChainFirstVariationStatement
  regular : ChartIsRegular S R U
  critical : ∀ A, IsStationaryAlong a S R V U A
  fine_lt : ∀ b ∈ innerBonds S 0,
    ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < min logRadius (1 / 8)
  coarse_lt : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
    ‖((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ < min logRadius (1 / 8)
  re_ne_zero : ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1),
    (relativePathAverage (chartField R U j) (R j) y).re ≠ 0
abbrev firstVariationAt (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) : Displacement S →L[ℝ] ℝ :=
  fderiv ℝ (actionOfDisplacement a S (chartChain R U V) (chartGauge R U)) 0
def centreGauge {j : ℕ} (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) (x : F.Site j) : UnitQuaternion :=
  expUnit (τ • Function.extend refineSite ζ 0 x)
theorem centreGauge_zero {j : ℕ} (ζ : F.Site (j + 1) → imaginaryQuaternions) :
    centreGauge ζ 0 = fun _ => 1 := by
  funext x
  simp [centreGauge, expUnit_zero]
theorem differentiableAt_centreGauge {j : ℕ} (ζ : F.Site (j + 1) → imaginaryQuaternions) (x : F.Site j) :
    DifferentiableAt ℝ (fun τ => ((centreGauge ζ τ x : UnitQuaternion) : ℍ[ℝ])) 0 :=
  differentiableAt_expUnit (differentiableAt_id.smul_const _)
theorem centreGauge_off (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) {y : F.Site (j + 1)}
    {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide) (h0 : h ≠ 0) :
    centreGauge ζ τ (refineSite y + siteOfCoords j h) = 1 := by
  have hn : ¬ ∃ y', refineSite y' = refineSite y + siteOfCoords j h :=
    fun ⟨y', e⟩ => h0 (eq_zero_of_refineSite_add hodd hj hh e.symm)
  simp only [centreGauge]
  rw [Function.extend_apply' _ _ _ hn]
  simp [expUnit_zero]
theorem centreGauge_refineSite {j : ℕ} (hinj : Function.Injective (refineSite (F := F) (j := j)))
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) (y : F.Site (j + 1)) :
    centreGauge ζ τ (refineSite y) = expUnit (τ • ζ y) := by
  simp only [centreGauge]
  rw [hinj.extend_apply]
def recentredGauge {j : ℕ} (Wj Rj : F.GaugeField j) (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  balancingGauge (gaugeTransform (centreGauge ζ τ) Wj) Rj y * centreGauge ζ τ (refineSite y)
theorem recentredGauge_eq (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) (Wj Rj : F.GaugeField j)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) (y : F.Site (j + 1))
    (hQ : relativePathAverage Wj Rj y +
      ((F.blockSide : ℝ) ^ 4)⁻¹ • ((((centreGauge ζ τ (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) ≠ 0) :
    recentredGauge Wj Rj ζ τ y =
      (polarUnit (relativePathAverage Wj Rj y +
        ((F.blockSide : ℝ) ^ 4)⁻¹ • ((((centreGauge ζ τ (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)))⁻¹ := by
  unfold recentredGauge balancingGauge
  rw [relativePathAverage_gaugeTransform hodd Wj Rj y (fun h hh h0 => centreGauge_off hodd hj ζ τ hh h0),
    polarUnit_mul (coe_unitQuaternion_ne_zero _) hQ, polarUnit_coe, mul_inv_rev, inv_mul_cancel_right]
theorem exists_hasDerivAt_recentredGauge (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    (hinj : Function.Injective (refineSite (F := F) (j := j)))
    (Wj Rj : F.GaugeField j) (ζ : F.Site (j + 1) → imaginaryQuaternions) (y : F.Site (j + 1))
    (hq : relativePathAverage Wj Rj y ≠ 0) :
    ∃ v, HasDerivAt (fun τ => ((recentredGauge Wj Rj ζ τ y : UnitQuaternion) : ℍ[ℝ])) v 0 ∧
      v * ((polarUnit (relativePathAverage Wj Rj y) : UnitQuaternion) : ℍ[ℝ]) =
        (‖relativePathAverage Wj Rj y‖⁻¹ * ((F.blockSide : ℝ) ^ 4)⁻¹) •
          pureComponent (((ζ y : imaginaryQuaternions) : ℍ[ℝ]) *
            ((polarUnit (relativePathAverage Wj Rj y) : UnitQuaternion) : ℍ[ℝ])) := by
  set q := relativePathAverage Wj Rj y with hqd
  set c : ℝ := ((F.blockSide : ℝ) ^ 4)⁻¹ with hc
  set Q : ℝ → ℍ[ℝ] := fun τ => q + c • ((((expUnit (τ • ζ y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) with hQd
  have hQ0 : Q 0 = q := by
    simp only [hQd, zero_smul, expUnit_zero, inv_one]
    have e1 : ((1 : UnitQuaternion) : ℍ[ℝ]) = 1 := rfl
    rw [e1, sub_self, smul_zero, add_zero]
  have hder : HasDerivAt Q (c • star ((ζ y : imaginaryQuaternions) : ℍ[ℝ])) 0 :=
    hasDerivAt_add_smul_inv_sub_one q c (ζ y)
  obtain ⟨v, hv, hv2⟩ := exists_hasDerivAt_polarUnit_inv hder (by rw [hQ0]; exact hq)
  refine ⟨v, ?_, ?_⟩
  · refine hv.congr_of_eventuallyEq ?_
    have hne : ∀ᶠ τ in nhds (0 : ℝ), Q τ ≠ 0 := hder.continuousAt.eventually_ne (by rw [hQ0]; exact hq)
    filter_upwards [hne] with τ hτ
    have hτ' : relativePathAverage Wj Rj y +
        ((F.blockSide : ℝ) ^ 4)⁻¹ • ((((centreGauge ζ τ (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) ≠ 0 := by
      rw [centreGauge_refineSite hinj]
      exact hτ
    rw [recentredGauge_eq hodd hj Wj Rj ζ τ y hτ', centreGauge_refineSite hinj]
  · rw [hQ0] at hv2
    rw [hv2, quaternion_star_real_smul, star_star, smul_mul_assoc, pureComponent_smul, smul_smul]
def gaugedLinkCurve {j : ℕ} (κ : F.SiteGauge) (Wj Rj : F.GaugeField j) (ζ : F.Site (j + 1) → imaginaryQuaternions)
    (τ : ℝ) : F.SiteGauge :=
  Function.update (Function.update κ (j + 1) (recentredGauge Wj Rj ζ τ)) j
    (fun x => (centreGauge ζ τ x)⁻¹ * κ j x)
theorem gaugedLinkCurve_succ {j : ℕ} (κ : F.SiteGauge) (Wj Rj : F.GaugeField j)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) :
    gaugedLinkCurve κ Wj Rj ζ τ (j + 1) = recentredGauge Wj Rj ζ τ := by
  rw [gaugedLinkCurve, Function.update_of_ne (by omega), Function.update_self]
theorem gaugedLinkCurve_self {j : ℕ} (κ : F.SiteGauge) (Wj Rj : F.GaugeField j)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) :
    gaugedLinkCurve κ Wj Rj ζ τ j = fun x => (centreGauge ζ τ x)⁻¹ * κ j x := by
  rw [gaugedLinkCurve, Function.update_self]
theorem gaugedLinkCurve_of_ne {j m : ℕ} (κ : F.SiteGauge) (Wj Rj : F.GaugeField j)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) (h1 : m ≠ j) (h2 : m ≠ j + 1) :
    gaugedLinkCurve κ Wj Rj ζ τ m = κ m := by
  rw [gaugedLinkCurve, Function.update_of_ne h1, Function.update_of_ne h2]
def gaugedFieldCurve {j : ℕ} (W : F.FieldChain) (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) :
    F.FieldChain :=
  Function.update W j (gaugeTransform (centreGauge ζ τ) (W j))
def levelGauge {j : ℕ} (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) : F.SiteGauge :=
  Function.update (fun _ _ => 1) j (centreGauge ζ τ)
theorem gaugeTransform_one {j : ℕ} (X : F.GaugeField j) : gaugeTransform (fun _ => (1 : UnitQuaternion)) X = X := by
  funext x i
  simp [gaugeTransform]
theorem gaugedFieldCurve_zero {j : ℕ} (W : F.FieldChain) (ζ : F.Site (j + 1) → imaginaryQuaternions) :
    gaugedFieldCurve W ζ 0 = W := by
  rw [gaugedFieldCurve, centreGauge_zero, gaugeTransform_one]
  exact Function.update_eq_self _ _
theorem chartGauge_succ {R : F.FieldChain} {U : ChainChart F} (V : F.GaugeField F.top) {m : ℕ} (hm : m < F.top) :
    chartGauge R U (m + 1) = balancingGauge (chartChain R U V m) (R m) := by
  rw [chartChain_of_lt R U V hm]
  rfl
section Steps
variable {a : ℝ} {R : F.FieldChain} {U : ChainChart F} {V : F.GaugeField F.top}
theorem CriticalSetting.differentiableAt (st : CriticalSetting a S R U V) :
    DifferentiableAt ℝ (actionOfDisplacement a S (chartChain R U V) (chartGauge R U)) 0 := by
  refine differentiableAt_actionOfDisplacement st.odd a _ _ fun j hj c hc => ?_
  rw [chartChain_of_lt R U V hj]
  exact (st.regular j hj).2 c hc
theorem gaugedChainAction_gaugedLinkCurve (st : CriticalSetting a S R U V) {j : ℕ} (hj : j < F.top)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) :
    gaugedChainAction a S (chartChain R U V)
        (gaugedLinkCurve (chartGauge R U) (chartChain R U V j) (R j) ζ τ) =
      gaugedChainAction a S (gaugedFieldCurve (chartChain R U V) ζ τ)
        (balancingLinks R (gaugedFieldCurve (chartChain R U V) ζ τ)) := by
  rw [← gaugedChainAction_gaugeTransform st.odd.pos st.covariance a (chartChain R U V) _ (levelGauge ζ τ)]
  refine gaugedChainAction_congr st.odd a (fun m _ x i _ _ => ?_) (fun m hm y hy => ?_)
  · show gaugeTransform (levelGauge ζ τ m) (chartChain R U V m) x i = gaugedFieldCurve (chartChain R U V) ζ τ m x i
    rcases eq_or_ne m j with rfl | h
    · simp only [levelGauge, gaugedFieldCurve, Function.update_self]
    · rw [levelGauge, gaugedFieldCurve, Function.update_of_ne h, Function.update_of_ne h, gaugeTransform_one]
  · show levelGauge ζ τ (m + 1) y * gaugedLinkCurve (chartGauge R U) (chartChain R U V j) (R j) ζ τ (m + 1) y *
        (levelGauge ζ τ m (refineSite y))⁻¹ =
        balancingGauge (gaugedFieldCurve (chartChain R U V) ζ τ m) (R m) y
    rcases eq_or_ne m j with rfl | h
    · rw [gaugedLinkCurve_succ]
      simp only [levelGauge, gaugedFieldCurve, Function.update_self]
      rw [Function.update_of_ne (by omega)]
      simp [recentredGauge]
    · rcases eq_or_ne (m + 1) j with h2 | h2
      · subst h2
        rw [gaugedLinkCurve_self]
        simp only [levelGauge, gaugedFieldCurve, Function.update_self]
        rw [Function.update_of_ne h, Function.update_of_ne h, chartGauge_succ V hm]
        simp
      · rw [gaugedLinkCurve_of_ne _ _ _ _ _ h2 (by omega), chartGauge_succ V hm]
        simp only [levelGauge, gaugedFieldCurve]
        rw [Function.update_of_ne h2, Function.update_of_ne h, Function.update_of_ne h]
        simp
theorem hasDerivAt_gaugedFieldCurve (st : CriticalSetting a S R U V) {j : ℕ} (hj : j < F.top)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) :
    HasDerivAt (fun τ => gaugedChainAction a S (gaugedFieldCurve (chartChain R U V) ζ τ)
      (balancingLinks R (gaugedFieldCurve (chartChain R U V) ζ τ))) 0 0 := by
  refine hasDerivAt_zero_of_balanced st.odd st.variation a R U V st.regular st.critical st.fine_lt st.coarse_lt
    ?_ ?_ ?_
  · intro m hm x i _ _
    rcases eq_or_ne m j with rfl | h
    · simp only [gaugedFieldCurve, Function.update_self, gaugeTransform]
      exact differentiableAt_unitQuaternion_mul
        (differentiableAt_unitQuaternion_mul (differentiableAt_centreGauge ζ x) (differentiableAt_const _))
        (differentiableAt_unitQuaternion_inv (differentiableAt_centreGauge ζ _))
    · simp only [gaugedFieldCurve]
      rw [show (fun τ : ℝ => ((Function.update (chartChain R U V) j
          (gaugeTransform (centreGauge ζ τ) (chartChain R U V j)) m x i : UnitQuaternion) : ℍ[ℝ])) =
          fun _ => ((chartChain R U V m x i : UnitQuaternion) : ℍ[ℝ]) from by
        funext τ
        rw [Function.update_of_ne h]]
      exact differentiableAt_const _
  · intro m hm x i _ _
    rw [gaugedFieldCurve_zero, chartChain_of_lt R U V hm]
  · intro τ x i _ _
    have h : F.top ≠ j := by omega
    simp only [gaugedFieldCurve]
    rw [Function.update_of_ne h, chartChain_top]
theorem gaugedLinkCurve_zero {j : ℕ} (hj : j < F.top) (ζ : F.Site (j + 1) → imaginaryQuaternions) :
    gaugedLinkCurve (chartGauge R U) (chartChain R U V j) (R j) ζ 0 = chartGauge R U := by
  funext m y
  rcases eq_or_ne m j with rfl | h
  · rw [gaugedLinkCurve_self, centreGauge_zero]
    simp
  · rcases eq_or_ne m (j + 1) with rfl | h2
    · rw [gaugedLinkCurve_succ, chartGauge_succ V hj]
      simp [recentredGauge, centreGauge_zero, gaugeTransform_one]
    · rw [gaugedLinkCurve_of_ne _ _ _ _ _ h h2]
def linkDirection (κ : F.SiteGauge) (k : ℝ → F.SiteGauge) (m : ℕ) (y : F.Site (m + 1)) : imaginaryQuaternions :=
  imaginaryPart (deriv (fun τ => ((k τ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 *
    star ((κ (m + 1) y : UnitQuaternion) : ℍ[ℝ]))
theorem hasDerivAt_linkDirection {κ : F.SiteGauge} {k : ℝ → F.SiteGauge} {m : ℕ} {y : F.Site (m + 1)}
    (hd : DifferentiableAt ℝ (fun τ => ((k τ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0)
    (h0 : k 0 (m + 1) y = κ (m + 1) y) :
    HasDerivAt (fun τ => ((k τ (m + 1) y : UnitQuaternion) : ℍ[ℝ]))
      (((linkDirection κ k m y : imaginaryQuaternions) : ℍ[ℝ]) * ((κ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have hv := hd.hasDerivAt
  have ht := re_mul_star_eq_zero_of_hasDerivAt hv
  rw [h0] at ht
  have e : ((linkDirection κ k m y : imaginaryQuaternions) : ℍ[ℝ]) * ((κ (m + 1) y : UnitQuaternion) : ℍ[ℝ]) =
      deriv (fun τ => ((k τ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 := by
    show pureComponent _ * _ = _
    rw [pureComponent_of_re_eq_zero ht, mul_assoc, ← coe_unitQuaternion_inv, coe_inv_mul_coe, mul_one]
  rw [e]
  exact hv
theorem gaugeVelocity_sub (κ : F.SiteGauge) (l l' : (m : ℕ) → F.Site (m + 1) → imaginaryQuaternions) :
    gaugeVelocity (S := S) κ (fun m y => l m y - l' m y) = gaugeVelocity κ l - gaugeVelocity κ l' := by
  funext idx
  rcases idx with b | ⟨m, y⟩
  · simp [gaugeVelocity]
  · simp [gaugeVelocity, sub_mul]
theorem firstVariationAt_gaugedLinkCurve (st : CriticalSetting a S R U V) {j : ℕ} (hj : j < F.top)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) :
    firstVariationAt a S R U V (gaugeVelocity (chartGauge R U) (linkDirection (chartGauge R U)
      (gaugedLinkCurve (chartGauge R U) (chartChain R U V j) (R j) ζ))) = 0 := by
  have hinj := (st.covariance F j hj st.odd.pos).1
  set κ := chartGauge R U with hκ
  set W := chartChain R U V with hW
  set K := gaugedLinkCurve κ (W j) (R j) ζ with hK
  have hq : ∀ y ∈ sitesOfCells S (j + 1), relativePathAverage (W j) (R j) y ≠ 0 := by
    intro y hy
    rw [hW, chartChain_of_lt R U V hj]
    exact (st.regular j hj).1 y hy
  have hKd : ∀ m, m < F.top → ∀ y ∈ sitesOfCells S (m + 1),
      DifferentiableAt ℝ (fun τ => ((K τ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro m hm y hy
    rcases eq_or_ne m j with rfl | h
    · simp only [hK, gaugedLinkCurve_succ]
      obtain ⟨v, hv, -⟩ := exists_hasDerivAt_recentredGauge st.odd hm hinj (W m) (R m) ζ y (hq y hy)
      exact hv.differentiableAt
    · rcases eq_or_ne (m + 1) j with h2 | h2
      · subst h2
        simp only [hK, gaugedLinkCurve_self]
        exact differentiableAt_unitQuaternion_mul
          (differentiableAt_unitQuaternion_inv (differentiableAt_centreGauge ζ y)) (differentiableAt_const _)
      · simp only [hK]
        simp only [gaugedLinkCurve_of_ne κ (W j) (R j) ζ _ h2 (show m + 1 ≠ j + 1 by omega)]
        exact differentiableAt_const _
  have hK0 : K 0 = κ := gaugedLinkCurve_zero hj ζ
  have hal := hasDerivAt_gaugedChainAction_comp (X := fun _ => W) (k := K)
    (v := gaugeVelocity κ (linkDirection κ K)) st.odd a W κ st.differentiableAt
    (fun _ _ _ _ _ => rfl)
    (by
      funext idx
      rcases idx with ⟨m, b⟩ | ⟨m, y⟩
      · simp [displacementOf]
      · simp [displacementOf, hK0])
    (by
      rintro (⟨m, b⟩ | ⟨m, y⟩)
      · simp only [displacementOf, gaugeVelocity, sub_self]
        exact hasDerivAt_const _ _
      · simp only [displacementOf, gaugeVelocity]
        exact (hasDerivAt_linkDirection (hKd m.val m.2 y.1 y.2) (by rw [hK0])).sub_const _)
  have e : (fun τ => gaugedChainAction a S W (K τ)) =
      fun τ => gaugedChainAction a S (gaugedFieldCurve W ζ τ) (balancingLinks R (gaugedFieldCurve W ζ τ)) := by
    funext τ
    exact gaugedChainAction_gaugedLinkCurve st hj ζ τ
  rw [e] at hal
  exact hal.unique (hasDerivAt_gaugedFieldCurve st hj ζ)
end Steps
section Links
variable {a : ℝ} {R : F.FieldChain} {U : ChainChart F} {V : F.GaugeField F.top}
theorem exists_linkDirection_eq (st : CriticalSetting a S R U V) {j : ℕ} (hj : j < F.top)
    (f : F.Site (j + 1) → imaginaryQuaternions) :
    ∃ ζ : F.Site (j + 1) → imaginaryQuaternions, ∀ y ∈ sitesOfCells S (j + 1),
      linkDirection (chartGauge R U) (gaugedLinkCurve (chartGauge R U) (chartChain R U V j) (R j) ζ) j y = f y := by
  have hinj := (st.covariance F j hj st.odd.pos).1
  have hLpos : (0 : ℝ) < (F.blockSide : ℝ) ^ 4 := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast st.odd.pos
    positivity
  have hre : ∀ y ∈ sitesOfCells S (j + 1), (relativePathAverage (chartChain R U V j) (R j) y).re ≠ 0 := by
    intro y hy
    rw [chartChain_of_lt R U V hj]
    exact st.re_ne_zero j hj y hy
  have hq : ∀ y ∈ sitesOfCells S (j + 1), relativePathAverage (chartChain R U V j) (R j) y ≠ 0 := by
    intro y hy h0
    apply hre y hy
    rw [h0]
    rfl
  have hex : ∀ y ∈ sitesOfCells S (j + 1), ∃ z : imaginaryQuaternions,
      pureComponent ((z : ℍ[ℝ]) *
        ((polarUnit (relativePathAverage (chartChain R U V j) (R j) y) : UnitQuaternion) : ℍ[ℝ])) =
        (‖relativePathAverage (chartChain R U V j) (R j) y‖⁻¹ * ((F.blockSide : ℝ) ^ 4)⁻¹)⁻¹ •
          ((f y : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro y hy
    have hu : ((polarUnit (relativePathAverage (chartChain R U V j) (R j) y) : UnitQuaternion) : ℍ[ℝ]).re ≠ 0 := by
      rw [coe_polarUnit (hq y hy)]
      show ‖relativePathAverage (chartChain R U V j) (R j) y‖⁻¹ *
        (relativePathAverage (chartChain R U V j) (R j) y).re ≠ 0
      exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 (hq y hy))) (hre y hy)
    obtain ⟨z, hz⟩ := exists_imaginaryPart_mul_eq hu
      ((‖relativePathAverage (chartChain R U V j) (R j) y‖⁻¹ * ((F.blockSide : ℝ) ^ 4)⁻¹)⁻¹ • f y)
    exact ⟨z, by rw [hz]; rfl⟩
  choose! ζ hζ using hex
  refine ⟨ζ, fun y hy => ?_⟩
  obtain ⟨v, hv, hv2⟩ :=
    exists_hasDerivAt_recentredGauge st.odd hj hinj (chartChain R U V j) (R j) ζ y (hq y hy)
  apply Subtype.ext
  show pureComponent _ = _
  simp only [gaugedLinkCurve_succ]
  rw [hv.deriv, congrFun (chartGauge_succ V hj) y, balancingGauge, coe_unitQuaternion_inv, star_star, hv2,
    hζ y hy, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 (hq y hy))) (inv_ne_zero hLpos.ne')),
    one_smul]
  exact pureComponent_of_re_eq_zero (f y).2
theorem linkDirection_of_ne {j m : ℕ} (κ : F.SiteGauge) (Wj Rj : F.GaugeField j)
    (ζ : F.Site (j + 1) → imaginaryQuaternions) (y : F.Site (m + 1)) (h1 : m + 1 ≠ j) (h2 : m ≠ j) :
    linkDirection κ (gaugedLinkCurve κ Wj Rj ζ) m y = 0 := by
  apply Subtype.ext
  show pureComponent _ = 0
  simp only [gaugedLinkCurve_of_ne κ Wj Rj ζ _ h1 (show m + 1 ≠ j + 1 by omega)]
  simp [pureComponent]
theorem firstVariationAt_gaugeVelocity (st : CriticalSetting a S R U V)
    (l : (m : ℕ) → F.Site (m + 1) → imaginaryQuaternions) :
    firstVariationAt a S R U V (gaugeVelocity (chartGauge R U) l) = 0 := by
  have Q : ∀ m, m ≤ F.top → ∀ l : (m : ℕ) → F.Site (m + 1) → imaginaryQuaternions,
      (∀ m', m ≤ m' → m' < F.top → ∀ y ∈ sitesOfCells S (m' + 1), l m' y = 0) →
      firstVariationAt a S R U V (gaugeVelocity (chartGauge R U) l) = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ l hl
      have : gaugeVelocity (S := S) (chartGauge R U) l = 0 := by
        funext idx
        rcases idx with b | ⟨m, y⟩
        · rfl
        · simp [gaugeVelocity, hl m.val (Nat.zero_le _) m.2 y.1 y.2]
      rw [this, map_zero]
    | succ m ih =>
      intro hm l hl
      have hmn : m < F.top := by omega
      obtain ⟨ζ, hζ⟩ := exists_linkDirection_eq st hmn (l m)
      have h1 := firstVariationAt_gaugedLinkCurve st hmn ζ
      have h2 := ih (by omega) (fun m' y => l m' y - linkDirection (chartGauge R U)
        (gaugedLinkCurve (chartGauge R U) (chartChain R U V m) (R m) ζ) m' y) (by
        intro m' hm' hm'n y hy
        rcases Nat.lt_or_ge m m' with h | h
        · rw [linkDirection_of_ne _ _ _ _ _ (by omega) (by omega), hl m' h hm'n y hy, sub_zero]
        · obtain rfl : m' = m := by omega
          rw [hζ y hy, sub_self])
      rw [gaugeVelocity_sub, map_sub, h1, sub_zero] at h2
      exact h2
  exact Q F.top le_rfl l (fun m' h1 h2 => absurd h2 (by omega))
theorem variedFieldChain_zero (W : F.FieldChain) (Y : GaugedVariation F) : variedFieldChain W Y 0 = W := by
  funext j x i
  simp only [variedFieldChain, zero_smul, expUnit_zero, one_mul, ite_self]
theorem variedGauge_zero (k : F.SiteGauge) (Y : GaugedVariation F) : variedGauge k Y 0 = k := by
  funext m
  cases m with
  | zero => rfl
  | succ m =>
    funext y
    simp only [variedGauge, zero_smul, expUnit_zero, one_mul]
theorem variedFieldChain_differentiableOn (W : F.FieldChain) (Y : GaugedVariation F) (j : ℕ) :
    GaugeDifferentiableOn (fun τ => variedFieldChain W Y τ j) 0 (sitesOfCells S j : Set (F.Site j)) := by
  intro x i _ _
  by_cases h : j < F.top
  · simp only [variedFieldChain, if_pos h]
    exact differentiableAt_unitQuaternion_mul (differentiableAt_expUnit (differentiableAt_id.smul_const _))
      (differentiableAt_const _)
  · simp only [variedFieldChain, if_neg h]
    exact differentiableAt_const _
theorem hasDerivAt_variedFieldChain (W : F.FieldChain) (Y : GaugedVariation F) {j : ℕ} (h : j < F.top)
    (x : F.Site j) (i : Fin 4) :
    HasDerivAt (fun τ => ((variedFieldChain W Y τ j x i : UnitQuaternion) : ℍ[ℝ]))
      (((Y.bondVariation j x i : imaginaryQuaternions) : ℍ[ℝ]) * ((W j x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  simp only [variedFieldChain, if_pos h, Submonoid.coe_mul]
  exact (hasDerivAt_expUnit_smul (Y.bondVariation j x i)).mul_const _
theorem firstVariationAt_fieldVelocity (st : CriticalSetting a S R U V) (Y : GaugedVariation F) :
    firstVariationAt a S R U V (fieldVelocity (chartChain R U V) Y.bondVariation) = 0 := by
  set W := chartChain R U V with hW
  set κ := chartGauge R U with hκ
  set Xv : ℝ → F.FieldChain := variedFieldChain W Y with hXv
  have hz : Xv 0 = W := variedFieldChain_zero W Y
  have hc := hasDerivAt_zero_of_balanced (X := Xv) st.odd st.variation a R U V st.regular st.critical
    st.fine_lt st.coarse_lt
    (fun j _ => variedFieldChain_differentiableOn W Y j)
    (fun j hj x i _ _ => by rw [hz, hW, chartChain_of_lt R U V hj])
    (fun τ x i _ _ => by
      simp only [hXv, variedFieldChain, lt_irrefl, if_false, hW, chartChain_top])
  set k : ℝ → F.SiteGauge := fun τ => balancingLinks R (Xv τ) with hk
  have hk0 : ∀ m, m < F.top → k 0 (m + 1) = κ (m + 1) := by
    intro m hm
    simp only [hk, hz]
    exact (chartGauge_succ V hm).symm
  have hkd : ∀ m, m < F.top → ∀ y ∈ sitesOfCells S (m + 1),
      DifferentiableAt ℝ (fun τ => ((k τ (m + 1) y : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro m hm y hy
    refine differentiableAt_balancingGauge st.odd hm (R m) (variedFieldChain_differentiableOn W Y m) hy ?_
    rw [show variedFieldChain W Y 0 = W from hz, hW, chartChain_of_lt R U V hm]
    exact (st.regular m hm).1 y hy
  have hal := hasDerivAt_gaugedChainAction_comp (X := Xv) (k := k)
    (v := fieldVelocity W Y.bondVariation + gaugeVelocity κ (linkDirection κ k)) st.odd a W κ st.differentiableAt
    (fun τ x i _ _ => by simp only [hXv, variedFieldChain, lt_irrefl, if_false])
    (by
      funext idx
      rcases idx with ⟨m, b⟩ | ⟨m, y⟩
      · simp [displacementOf, hz]
      · simp [displacementOf, hk0 m.val m.2])
    (by
      rintro (⟨m, b⟩ | ⟨m, y⟩)
      · simp only [displacementOf, fieldVelocity, gaugeVelocity, Pi.add_apply, add_zero]
        exact (hasDerivAt_variedFieldChain W Y m.2 _ _).sub_const _
      · simp only [displacementOf, fieldVelocity, gaugeVelocity, Pi.add_apply, zero_add]
        exact (hasDerivAt_linkDirection (hkd m.val m.2 y.1 y.2) (by rw [hk0 m.val m.2])).sub_const _)
  have h0 := hal.unique hc
  rw [map_add, firstVariationAt_gaugeVelocity st, add_zero] at h0
  exact h0
theorem hasDerivAt_variedAction (st : CriticalSetting a S R U V) (Y : GaugedVariation F) :
    HasDerivAt (fun τ => gaugedChainAction a S (variedFieldChain (chartChain R U V) Y τ)
      (variedGauge (chartGauge R U) Y τ)) 0 0 := by
  set W := chartChain R U V with hW
  set κ := chartGauge R U with hκ
  have hal := hasDerivAt_gaugedChainAction_comp (X := variedFieldChain W Y) (k := variedGauge κ Y)
    (v := fieldVelocity W Y.bondVariation + gaugeVelocity κ Y.linkVariation)
    st.odd a W κ st.differentiableAt
    (fun τ x i _ _ => by simp only [variedFieldChain, lt_irrefl, if_false])
    (by
      funext idx
      rcases idx with ⟨m, b⟩ | ⟨m, y⟩
      · simp [displacementOf, variedFieldChain_zero]
      · simp [displacementOf, variedGauge_zero])
    (by
      rintro (⟨m, b⟩ | ⟨m, y⟩)
      · simp only [displacementOf, fieldVelocity, gaugeVelocity, Pi.add_apply, add_zero]
        exact (hasDerivAt_variedFieldChain W Y m.2 _ _).sub_const _
      · simp only [displacementOf, fieldVelocity, gaugeVelocity, Pi.add_apply, zero_add, variedGauge,
          Submonoid.coe_mul]
        exact ((hasDerivAt_expUnit_smul (Y.linkVariation m.val y.1)).mul_const _).sub_const _)
  rw [map_add, firstVariationAt_fieldVelocity st Y, firstVariationAt_gaugeVelocity st, add_zero] at hal
  exact hal
theorem sum_firstVariation_eq_zero (st : CriticalSetting a S R U V) (Y : GaugedVariation F) :
    (∀ t ∈ actionTerms S, DifferentiableAt ℝ (fun τ : ℝ =>
      actionTermValue a (variedFieldChain (chartChain R U V) Y τ) (variedGauge (chartGauge R U) Y τ) t) 0) ∧
    ∑ t ∈ actionTerms S, firstVariation a (chartChain R U V) (chartGauge R U) Y t = 0 := by
  have hd : ∀ t ∈ actionTerms S, DifferentiableAt ℝ (fun τ : ℝ =>
      actionTermValue a (variedFieldChain (chartChain R U V) Y τ) (variedGauge (chartGauge R U) Y τ) t) 0 := by
    intro t ht
    refine differentiableAt_actionTermValue st.odd a (fun j _ => variedFieldChain_differentiableOn _ Y j)
      (fun j _ y _ => ?_) (fun j hj c hc => ?_) ht
    · simp only [variedGauge]
      exact differentiableAt_unitQuaternion_mul (differentiableAt_expUnit (differentiableAt_id.smul_const _))
        (differentiableAt_const _)
    · rw [variedFieldChain_zero, variedGauge_zero, chartChain_of_lt R U V hj]
      exact (st.regular j hj).2 c hc
  refine ⟨hd, ?_⟩
  have hs := HasDerivAt.fun_sum fun t ht => (hd t ht).hasDerivAt
  simp only [sum_actionTermValue] at hs
  exact hs.unique (hasDerivAt_variedAction st Y)
end Links
section Sizes
theorem norm_average_sub_average_le (hodd : Odd F.blockSide)
    {f g : LatticeFractionalIntegration.Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]} {B : ℝ}
    (h : ∀ a ∈ centredCube F.blockSide, ∀ π, ‖f a π - g a π‖ ≤ B) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), f a π -
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), g a π‖ ≤ B := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  have hsum : ‖∑ a ∈ centredCube F.blockSide,
      (∑ π : Equiv.Perm (Fin 4), f a π - ∑ π : Equiv.Perm (Fin 4), g a π)‖ ≤
      (24 * (F.blockSide : ℝ) ^ 4) * B := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ a ∈ centredCube F.blockSide,
        ‖∑ π : Equiv.Perm (Fin 4), f a π - ∑ π : Equiv.Perm (Fin 4), g a π‖ ≤ 24 * B := by
      intro a ha
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => h a ha π).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      norm_num [Nat.factorial]
    refine (Finset.sum_le_sum h1).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul, card_centredCube hodd]
    push_cast
    apply le_of_eq
    ring
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * ((24 * (F.blockSide : ℝ) ^ 4) * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp
theorem average_one (hodd : Odd F.blockSide) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ _a ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube hodd]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((F.blockSide ^ 4 : ℕ) : ℝ) * ((Nat.factorial 4 : ℕ) : ℝ) = 1 := by
    rw [show Nat.factorial 4 = 24 from rfl]
    push_cast
    field_simp
  rw [this, one_smul]
theorem norm_pathHolonomy_ratio_sub_one_le {j : ℕ} {X R : F.GaugeField j} {D : Set (F.Site j)} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hb : ∀ x i, x ∈ D → x + unitStep j i ∈ D →
      ‖((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : LatticeFractionalIntegration.Lattice4),
      AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      ‖((pathHolonomy X (x0 + siteOfCoords j v) l * (pathHolonomy R (x0 + siteOfCoords j v) l)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.norm_pathHolonomy_ratio_le <;> assumption
theorem norm_coe_sub_coe (g h : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) - h‖ = ‖((g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  have e : (g : ℍ[ℝ]) - h = (((g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * h := by
    rw [sub_mul, one_mul, Submonoid.coe_mul, mul_assoc, coe_inv_mul_coe, mul_one]
  rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
theorem length_axisPath_le {h : LatticeFractionalIntegration.Lattice4} (π : Equiv.Perm (Fin 4))
    (hh : h ∈ centredCube F.blockSide) (hL : 1 ≤ F.blockSide) :
    (axisPath h π).length ≤ 5 * F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.length_axisPath_le <;> assumption
theorem norm_relativePathAverage_sub_one_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {X R : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ b ∈ innerBonds S j, ‖((X b.1 b.2 * (R b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) :
    ‖relativePathAverage X R y - 1‖ ≤ 5 * F.blockSide * ε := by
  have h1 := norm_average_sub_average_le (F := F) (B := 5 * F.blockSide * ε) hodd
    (f := fun a π => ((pathHolonomy X (refineSite y) (axisPath a π) *
      (pathHolonomy R (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    (g := fun _ _ => 1) (by
      intro a ha π
      have h2 := norm_pathHolonomy_ratio_sub_one_le (D := (sitesOfCells S j : Set (F.Site j))) hε
        (fun x i hx hx' => hb (x, i) (mem_innerBonds hx hx')) (refineSite y) _ 0
        (allAlong_axisPath hodd hj hy ha π)
      rw [add_siteOfCoords_zero] at h2
      refine h2.trans ?_
      have h3 : ((axisPath a π).length : ℝ) ≤ 5 * F.blockSide := by
        exact_mod_cast length_axisPath_le π ha hodd.pos
      exact mul_le_mul_of_nonneg_right h3 hε)
  rw [average_one hodd] at h1
  exact h1
theorem norm_contourAverage_sub_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {X R : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ b ∈ innerBonds S j, ‖((X b.1 b.2 * (R b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    ‖contourAverage X c - contourAverage R c‖ ≤ 5 * F.blockSide * ε := by
  refine norm_average_sub_average_le hodd fun a ha π => ?_
  rw [norm_coe_sub_coe]
  have h2 := norm_pathHolonomy_ratio_sub_one_le (D := (sitesOfCells S j : Set (F.Site j))) hε
    (fun x i hx hx' => hb (x, i) (mem_innerBonds hx hx')) (refineSite c.1) _ 0
    (allAlong_bondContour hodd hj hc ha π)
  rw [add_siteOfCoords_zero] at h2
  refine h2.trans ?_
  have h3 : ((bondContour F.blockSide a π c.2).length : ℝ) ≤ 5 * F.blockSide := by
    exact_mod_cast length_bondContour_le π c.2 hodd.pos ha
  exact mul_le_mul_of_nonneg_right h3 hε
theorem localNorm_le_weightedNorm {R : F.FieldChain} {A : ChainChart F} {w : F.SiteWeights} {z : F.Cell}
    (hz : z ∈ S) : localNorm S R A w z ≤ weightedNorm S R A w := by apply _root_.YangMills.Construction.BlockWeights.localNorm_le_weightedNorm <;> assumption
theorem mem_cellBall_self {z : F.Cell} (hz : z ∈ S) : z ∈ cellBall S z 3 := by
  unfold cellBall
  refine Finset.mem_filter.2 ⟨hz, ?_⟩
  have : cellSupDist z z = 0 := by simp [cellSupDist]
  omega
theorem decayWeights_enclosingCell (del : ℝ) (p : F.Site 0) {j : ℕ} (x : F.Site j) :
    decayWeights F del 0 p (enclosingCell x) j x = 1 := by
  have : cellSupDist (enclosingCell x) (enclosingCell x) = 0 := by simp [cellSupDist]
  simp [decayWeights, this]
theorem norm_fine_le (hodd : Odd F.blockSide) {R : F.FieldChain} (A : ChainChart F) (del : ℝ) (p : F.Site 0)
    {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    ‖A.fine b.1 b.2‖ ≤ weightedNorm S R A (decayWeights F del 0 p (enclosingCell b.1)) := by
  set w := decayWeights F del 0 p (enclosingCell b.1) with hw
  have hz : enclosingCell b.1 ∈ S := LocalPartition.enclosingCell_mem hodd (innerBonds_ends hb).1
  refine le_trans ?_ (localNorm_le_weightedNorm hz)
  unfold localNorm
  refine Real.le_sqrt_of_sq_le ?_
  unfold localNormSq
  have hmem : b ∈ bondsOver S (cellBall S (enclosingCell b.1) 3) 0 := by
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨hb, mem_cellBall_self hz⟩
  have h1 : ‖A.fine b.1 b.2‖ ^ 4 ≤
      ∑ b ∈ bondsOver S (cellBall S (enclosingCell b.1) 3) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 := by
    have := Finset.single_le_sum (f := fun b : F.Site 0 × Fin 4 => (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4)
      (fun _ _ => by positivity) hmem
    simpa [hw, decayWeights_enclosingCell] using this
  have h2 : ‖A.fine b.1 b.2‖ ^ 2 ≤
      Real.sqrt (∑ b ∈ bondsOver S (cellBall S (enclosingCell b.1) 3) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (‖A.fine b.1 b.2‖ ^ 2) ^ 2 = ‖A.fine b.1 b.2‖ ^ 4 := by ring
      _ ≤ _ := h1
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S (enclosingCell b.1) 3) 0,
      (w 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S (enclosingCell b.1) 3) (j + 1),
      (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith
theorem norm_coarse_le (hodd : Odd F.blockSide) {R : F.FieldChain} (A : ChainChart F) (del : ℝ) (p : F.Site 0)
    {j : ℕ} (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    ‖A.coarse j c.1 c.2‖ ≤ weightedNorm S R A (decayWeights F del 0 p (enclosingCell c.1)) := by
  set w := decayWeights F del 0 p (enclosingCell c.1) with hw
  have hz : enclosingCell c.1 ∈ S := LocalPartition.enclosingCell_mem hodd (innerBonds_ends hc).1
  refine le_trans ?_ (localNorm_le_weightedNorm hz)
  unfold localNorm
  refine Real.le_sqrt_of_sq_le ?_
  unfold localNormSq
  have hmem : c ∈ bondsOver S (cellBall S (enclosingCell c.1) 3) (j + 1) := by
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨hc, mem_cellBall_self hz⟩
  have h1 : ‖A.coarse j c.1 c.2‖ ^ 2 ≤
      ∑ c ∈ bondsOver S (cellBall S (enclosingCell c.1) 3) (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 := by
    have := Finset.single_le_sum
      (f := fun c : F.Site (j + 1) × Fin 4 => (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2)
      (fun _ _ => by positivity) hmem
    simpa [hw, decayWeights_enclosingCell] using this
  have hjr : j ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
  have h2 := Finset.single_le_sum
    (f := fun j => ∑ c ∈ bondsOver S (cellBall S (enclosingCell c.1) 3) (j + 1),
      (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hjr
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S (enclosingCell c.1) 3) 0,
      (w 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S (enclosingCell c.1) 3) 0,
    (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4)
  linarith
end Sizes
section Smallness
theorem re_ge_of_norm_sub_one_le {q : ℍ[ℝ]} (h : ‖q - 1‖ ≤ 1 / 8) : 7 / 8 ≤ q.re := by
  have h1 := quaternion_re_le_norm (1 - q)
  have e : (1 - q).re = 1 - q.re := rfl
  rw [e, norm_sub_rev] at h1
  linarith
theorem norm_chartField_ratio_sub_one_le {R : F.FieldChain} {U : ChainChart F} {θ C₁ s : ℝ} (hθ : 0 < θ)
    (hL : 1 ≤ F.blockSide) (hpos : 0 ≤ C₁ * s)
    (hq : ∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
      localQuarticSum S R U j p r ≤ (C₁ * s) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ))
    {j : ℕ} (hj : j < F.top) {b : F.Site j × Fin 4} (hb : b ∈ innerBonds S j) :
    ‖((chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C₁ * s := by
  have hL' : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hpw : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - j) := one_le_pow₀ hL'
  have h1 := hq j (baseSite b.1) 1 hj le_rfl hpw
  have hsingle : normSubOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) ^ 4 ≤
      localQuarticSum S R U j (baseSite b.1) 1 := by
    unfold localQuarticSum
    refine Finset.single_le_sum (f := fun b : F.Site j × Fin 4 =>
      normSubOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) ^ 4) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨hb, ?_⟩)
    have : baseDistance b.1 (baseSite b.1) = 0 := by simp [baseDistance]
    rw [this]
    push_cast
    positivity
  have hfac : ((1 : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    rw [div_le_one (by positivity)]
    exact hpw
  have h2 : normSubOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) ^ 4 ≤ (C₁ * s) ^ 4 := by
    refine hsingle.trans (h1.trans ?_)
    calc (C₁ * s) ^ 4 * _ ≤ (C₁ * s) ^ 4 * 1 := mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := mul_one _
  by_contra hcon
  have h3 : C₁ * s < normSubOne (chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹) := not_le.1 hcon
  have := pow_lt_pow_left₀ h3 hpos (n := 4) (by norm_num)
  linarith
end Smallness
theorem criticalUnderGaugedVariations (h₁ : referenceBoundsStatement) (h₂ : gaugeCovarianceStatement)
    (h₃ : regularChainFirstVariationStatement) :
    criticalUnderGaugedVariationsStatement := by
  intro a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨C, c, L1, hC, hc, hB⟩ := h₁
  refine ⟨max L1 1, fun L hLodd hL0 C₁ hC₁ => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL0
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  set e : ℝ := min logRadius (1 / 8) with he
  have hepos : 0 < e := lt_min logRadius_pos (by norm_num)
  set σ : ℝ := min (min c 1) (min (1 / (40 * L * C₁)) (min (1 / (4 * C)) (e / (2 * (Ca + C₁))))) with hσd
  have hσpos : 0 < σ := by
    refine lt_min (lt_min hc one_pos) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hσc : σ ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hσ1 : σ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hσ2 : σ ≤ 1 / (40 * L * C₁) := (min_le_right _ _).trans (min_le_left _ _)
  have hσ3 : σ ≤ 1 / (4 * C) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσ4 : σ ≤ e / (2 * (Ca + C₁)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨σ, hσpos, ?_⟩
  intro F m S hFL hamb hm hregS s V v hs hsσ hcold hv U hU Y
  have hodd : Odd F.blockSide := hFL ▸ hLodd
  have hF1 : 1 ≤ F.blockSide := hFL ▸ hL1
  have hL1F : L1 ≤ F.blockSide := hFL ▸ ((le_max_left _ _).trans hL0)
  have hFr : (F.blockSide : ℝ) = L := by rw [hFL]
  have hB' := hB F m S hodd hL1F hamb hm hregS s V hs (hsσ.trans hσc) hcold
  have hmean := hB'.2.2.2.2.2
  set R := referenceFieldChain S V with hR
  have hs1 : s ≤ 1 := hsσ.trans hσ1
  have hε : 0 ≤ C₁ * s := by positivity
  have hE : 5 * (F.blockSide : ℝ) * (C₁ * s) ≤ 1 / 8 := by
    rw [hFr]
    have h1 : s * (40 * L * C₁) ≤ 1 := by
      have := hsσ.trans hσ2
      rwa [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hCs : C * s ^ 2 ≤ 1 / 4 := by
    have h1 : s * (4 * C) ≤ 1 := by
      have := hsσ.trans hσ3
      rwa [le_div_iff₀ (by positivity)] at this
    have h2 : s ^ 2 ≤ s := by nlinarith
    nlinarith
  have hnear : ∀ j, j < F.top → ∀ b ∈ innerBonds S j,
      ‖((chartField R U j b.1 b.2 * (R j b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C₁ * s :=
    fun j hj b hb => norm_chartField_ratio_sub_one_le hθ hF1 hε hU.quartic hj hb
  have hleg : ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1),
      7 / 8 ≤ (relativePathAverage (chartField R U j) (R j) y).re := by
    intro j hj y hy
    exact re_ge_of_norm_sub_one_le ((norm_relativePathAverage_sub_one_le hodd hj hε (hnear j hj) hy).trans hE)
  have hsmall : Ca * s + C₁ * s ^ 2 < e := by
    have h1 : s * (2 * (Ca + C₁)) ≤ e := by
      have := hsσ.trans hσ4
      rwa [le_div_iff₀ (by positivity)] at this
    have h2 : s ^ 2 ≤ s := by nlinarith
    have h3 : C₁ * s ^ 2 ≤ C₁ * s := mul_le_mul_of_nonneg_left h2 hC₁.le
    nlinarith
  obtain ⟨Ulin, Urest, hsame, hnorm⟩ := hU.split
  have st : CriticalSetting a S R U (rotatedField v V) := by
    refine ⟨hodd, h₂, h₃, ?_, hU.critical, ?_, ?_, ?_⟩
    · intro j hj
      refine ⟨fun y hy h0 => ?_, fun c' hc' => ?_⟩
      · have := hleg j hj y hy
        rw [h0] at this
        have e0 : (0 : ℍ[ℝ]).re = 0 := rfl
        rw [e0] at this
        norm_num at this
      · have hm1 := norm_contourAverage_sub_le hodd hj hε (hnear j hj) hc'
        have hm2 := (hmean j hj c' hc').2
        have hsc : levelScale F (j + 1) ^ 4 ≤ 1 := by
          have h0 : (0 : ℝ) ≤ levelScale F (j + 1) := by
            unfold levelScale
            positivity
          have h1 : levelScale F (j + 1) ≤ 1 := by
            unfold levelScale
            refine pow_le_one₀ (by positivity) ?_
            rw [div_le_one (by exact_mod_cast hodd.pos)]
            exact_mod_cast hF1
          exact pow_le_one₀ h0 h1
        have hm3 : C * s ^ 2 * levelScale F (j + 1) ^ 4 ≤ C * s ^ 2 := by
          have : 0 ≤ C * s ^ 2 := by positivity
          nlinarith
        unfold gaugedContourAverage
        refine mul_ne_zero (mul_ne_zero (coe_unitQuaternion_ne_zero _) fun h0 => ?_)
          (coe_unitQuaternion_ne_zero _)
        rw [h0, zero_sub, norm_neg] at hm1
        linarith
    · intro b hb
      have e1 := hsame.1 b hb
      have e2 : ‖U.fine b.1 b.2‖ ≤ ‖Ulin.fine b.1 b.2‖ + ‖Urest.fine b.1 b.2‖ := by
        rw [e1]
        simp only [chartSum, chartMove, one_smul]
        exact norm_add_le _ _
      have e3 := norm_fine_le (R := R) hodd Ulin del 0 hb
      have e4 := norm_fine_le (R := R) hodd Urest del 0 hb
      have e5 := hnorm 0 (enclosingCell b.1) 0 (Or.inr rfl)
      show ‖U.fine b.1 b.2‖ < e
      linarith [e5.1, e5.2]
    · intro j hj c' hc'
      have e1 := hsame.2 j hj c' hc'
      have e2 : ‖U.coarse j c'.1 c'.2‖ ≤ ‖Ulin.coarse j c'.1 c'.2‖ + ‖Urest.coarse j c'.1 c'.2‖ := by
        rw [e1]
        simp only [chartSum, chartMove, one_smul]
        exact norm_add_le _ _
      have e3 := norm_coarse_le (R := R) hodd Ulin del 0 hj hc'
      have e4 := norm_coarse_le (R := R) hodd Urest del 0 hj hc'
      have e5 := hnorm 0 (enclosingCell c'.1) 0 (Or.inr rfl)
      show ‖U.coarse j c'.1 c'.2‖ < e
      linarith [e5.1, e5.2]
    · intro j hj y hy h0
      have := hleg j hj y hy
      rw [h0] at this
      norm_num at this
  exact sum_firstVariation_eq_zero st Y
end GaugedCriticality
end YangMills.Construction
end
