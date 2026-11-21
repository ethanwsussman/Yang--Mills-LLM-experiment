import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace VariationRates
variable {F : BlockFrame} {j : ℕ}
theorem quaternion_re_star (a : ℍ[ℝ]) : (star a).re = a.re := by simp
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem star_coe_imaginary (w : imaginaryQuaternions) : star (w : ℍ[ℝ]) = - (w : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
theorem re_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : (adjointAction g w).re = w.re := by apply _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (v w : ℍ[ℝ]) :
    adjointAction g (v + w) = adjointAction g v + adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (w : ℍ[ℝ]) :
    adjointAction g (r • w) = r • adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_neg (g : UnitQuaternion) (w : ℍ[ℝ]) : adjointAction g (- w) = - adjointAction g w := by
  unfold adjointAction
  rw [mul_neg, neg_mul]
def holonomyRate (X : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions) :
    F.Site j → List PathStep → ℍ[ℝ]
  | _, [] => 0
  | x, st :: r =>
    (if st.2 then (y x st.1 : ℍ[ℝ]) else
      - adjointAction ((X (x - unitStep j st.1) st.1)⁻¹) (y (x - unitStep j st.1) st.1)) +
      adjointAction (linkValue X x st) (holonomyRate X y (x + stepDisplacement j st) r)
def bondSum (g : F.Site j → Fin 4 → ℝ) : F.Site j → List PathStep → ℝ
  | _, [] => 0
  | x, st :: r => (if st.2 then g x st.1 else g (x - unitStep j st.1) st.1) +
      bondSum g (x + stepDisplacement j st) r
theorem re_holonomyRate (X : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (l : List PathStep) : (holonomyRate X y x l).re = 0 := by
  induction l generalizing x with
  | nil => simp [holonomyRate]
  | cons st r ih =>
    simp only [holonomyRate, Quaternion.re_add, re_adjointAction, ih, add_zero]
    split_ifs
    · exact (y _ _).2
    · simp only [Quaternion.re_neg, re_adjointAction]
      have h : (y (x - unitStep j st.1) st.1 : ℍ[ℝ]).re = 0 := (y (x - unitStep j st.1) st.1).2
      rw [h, neg_zero]
theorem norm_holonomyRate_le (X : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (l : List PathStep) : ‖holonomyRate X y x l‖ ≤ bondSum (fun x i => ‖y x i‖) x l := by
  induction l generalizing x with
  | nil => simp [holonomyRate, bondSum]
  | cons st r ih =>
    simp only [holonomyRate, bondSum]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs
      · rfl
      · rw [norm_neg, norm_adjointAction]
        rfl
    · rw [norm_adjointAction]
      exact ih _
theorem holonomyRate_add (X : F.GaugeField j) (y y' : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (l : List PathStep) :
    holonomyRate X (fun x i => y x i + y' x i) x l = holonomyRate X y x l + holonomyRate X y' x l := by
  induction l generalizing x with
  | nil => simp [holonomyRate]
  | cons st r ih =>
    simp only [holonomyRate, ih, adjointAction_add]
    split_ifs
    · simp only [Submodule.coe_add]
      abel
    · simp only [Submodule.coe_add, adjointAction_add]
      abel
theorem holonomyRate_smul (X : F.GaugeField j) (c : ℝ) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (l : List PathStep) :
    holonomyRate X (fun x i => c • y x i) x l = c • holonomyRate X y x l := by
  induction l generalizing x with
  | nil => simp [holonomyRate]
  | cons st r ih =>
    simp only [holonomyRate, ih, adjointAction_smul, smul_add]
    split_ifs
    · simp only [Submodule.coe_smul]
    · simp only [Submodule.coe_smul, adjointAction_smul, smul_neg]
theorem hasDerivAt_pathHolonomy {Xc : ℝ → F.GaugeField j} {X : F.GaugeField j}
    {y : F.Site j → Fin 4 → imaginaryQuaternions} (h0 : Xc 0 = X)
    (hd : ∀ x i, HasDerivAt (fun τ => ((Xc τ x i : UnitQuaternion) : ℍ[ℝ])) ((y x i : ℍ[ℝ]) * (X x i : ℍ[ℝ])) 0)
    (x : F.Site j) (l : List PathStep) :
    HasDerivAt (fun τ => ((pathHolonomy (Xc τ) x l : UnitQuaternion) : ℍ[ℝ]))
      (holonomyRate X y x l * ((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ])) 0 := by
  subst h0
  induction l generalizing x with
  | nil =>
    simp only [pathHolonomy, holonomyRate, zero_mul]
    exact hasDerivAt_const _ _
  | cons st r ih =>
    simp only [pathHolonomy, Submonoid.coe_mul]
    have hs : HasDerivAt (fun τ => ((linkValue (Xc τ) x st : UnitQuaternion) : ℍ[ℝ]))
        ((if st.2 then (y x st.1 : ℍ[ℝ]) else
          - adjointAction ((Xc 0 (x - unitStep j st.1) st.1)⁻¹) (y (x - unitStep j st.1) st.1)) *
          ((linkValue (Xc 0) x st : UnitQuaternion) : ℍ[ℝ])) 0 := by
      rcases st with ⟨i, b⟩
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false, coe_unitQuaternion_inv]
        have h1 := (ChartCoordinates.starCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd (x - unitStep j i) i)
        have e : (ChartCoordinates.starCLM) ((y (x - unitStep j i) i : ℍ[ℝ]) * (Xc 0 (x - unitStep j i) i : ℍ[ℝ])) =
            - adjointAction ((Xc 0 (x - unitStep j i) i)⁻¹) (y (x - unitStep j i) i) *
              star (Xc 0 (x - unitStep j i) i : ℍ[ℝ]) := by
          show star _ = _
          rw [star_mul, star_coe_imaginary]
          unfold adjointAction
          have e2 := coe_mul_coe_inv (Xc 0 (x - unitStep j i) i)
          rw [coe_unitQuaternion_inv] at e2
          rw [coe_unitQuaternion_inv, inv_inv, mul_neg, neg_mul, mul_assoc, mul_assoc, e2, mul_one]
        rw [e] at h1
        exact h1
      · simp only [linkValue, if_true]
        exact hd x i
    refine (hs.fun_mul (ih (x + stepDisplacement j st))).congr_deriv ?_
    simp only [holonomyRate, add_mul]
    congr 1
    · rw [mul_assoc]
    · unfold adjointAction
      have e := coe_inv_mul_coe (linkValue (Xc 0) x st)
      calc _ = (linkValue (Xc 0) x st : ℍ[ℝ]) * holonomyRate (Xc 0) y (x + stepDisplacement j st) r *
              ((((linkValue (Xc 0) x st)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (linkValue (Xc 0) x st : ℍ[ℝ])) *
              ((pathHolonomy (Xc 0) (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) := by
            rw [e, mul_one, mul_assoc]
        _ = _ := by simp only [mul_assoc]
def contourAverageRate (X : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    holonomyRate X y (refineSite c.1) (bondContour F.blockSide h π c.2) *
      ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])
def contourBondSum (g : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    bondSum g (refineSite c.1) (bondContour F.blockSide h π c.2)
def gaugedAverageRate (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (y : F.Site j → Fin 4 → imaginaryQuaternions) (yk : F.Site (j + 1) → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (yk c.1 : ℍ[ℝ]) * gaugedContourAverage X k c -
      gaugedContourAverage X k c * (yk (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) +
    (k c.1 : ℍ[ℝ]) * contourAverageRate X y c * (((k (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ])
def blockFitRate (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1))
    (y : F.Site j → Fin 4 → imaginaryQuaternions) (yk : F.Site (j + 1) → imaginaryQuaternions)
    (yb : imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (gaugedAverageRate X k y yk c * (star ((polarUnit (gaugedContourAverage X k c) : UnitQuaternion) : ℍ[ℝ]) -
      star ((X' c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))).re +
    (gaugedContourAverage X k c * star ((X' c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) * (yb : ℍ[ℝ])).re
section Derivatives
variable {Xc : ℝ → F.GaugeField j} {X : F.GaugeField j} {y : F.Site j → Fin 4 → imaginaryQuaternions}
theorem hasDerivAt_contourAverage (h0 : Xc 0 = X)
    (hd : ∀ x i, HasDerivAt (fun τ => ((Xc τ x i : UnitQuaternion) : ℍ[ℝ])) ((y x i : ℍ[ℝ]) * (X x i : ℍ[ℝ])) 0)
    (c : F.Site (j + 1) × Fin 4) :
    HasDerivAt (fun τ => contourAverage (Xc τ) c) (contourAverageRate X y c) 0 := by
  unfold contourAverage contourAverageRate
  have h1 : HasDerivAt (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (Xc τ) (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]))
      (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        holonomyRate X y (refineSite c.1) (bondContour F.blockSide h π c.2) *
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) 0 :=
    HasDerivAt.fun_sum fun h _ => HasDerivAt.fun_sum fun π _ => hasDerivAt_pathHolonomy h0 hd _ _
  exact h1.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
theorem hasDerivAt_coe_inv {g : ℝ → UnitQuaternion} {w : imaginaryQuaternions}
    (h : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) ((w : ℍ[ℝ]) * (g 0 : ℍ[ℝ])) 0) :
    HasDerivAt (fun τ => (((g τ)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (- ((((g 0)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]))) 0 := by
  have h1 := (ChartCoordinates.starCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (ChartCoordinates.starCLM) ((w : ℍ[ℝ]) * (g 0 : ℍ[ℝ])) =
      - ((((g 0)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ])) := by
    show star _ = _
    rw [star_mul, star_coe_imaginary, mul_neg, coe_unitQuaternion_inv]
  rw [e] at h1
  exact h1
variable {kc : ℝ → F.Site (j + 1) → UnitQuaternion} {k : F.Site (j + 1) → UnitQuaternion}
  {yk : F.Site (j + 1) → imaginaryQuaternions}
theorem hasDerivAt_gaugedContourAverage (h0 : Xc 0 = X)
    (hd : ∀ x i, HasDerivAt (fun τ => ((Xc τ x i : UnitQuaternion) : ℍ[ℝ])) ((y x i : ℍ[ℝ]) * (X x i : ℍ[ℝ])) 0)
    (hk0 : kc 0 = k)
    (hk : ∀ x, HasDerivAt (fun τ => ((kc τ x : UnitQuaternion) : ℍ[ℝ])) ((yk x : ℍ[ℝ]) * (k x : ℍ[ℝ])) 0)
    (c : F.Site (j + 1) × Fin 4) :
    HasDerivAt (fun τ => gaugedContourAverage (Xc τ) (kc τ) c) (gaugedAverageRate X k y yk c) 0 := by
  subst h0 hk0
  unfold gaugedContourAverage
  have h1 := ((hk c.1).fun_mul (hasDerivAt_contourAverage rfl hd c)).fun_mul
    (hasDerivAt_coe_inv (g := fun τ => kc τ (c.1 + unitStep (j + 1) c.2)) (hk (c.1 + unitStep (j + 1) c.2)))
  refine h1.congr_deriv ?_
  unfold gaugedAverageRate gaugedContourAverage
  simp only [add_mul, mul_neg, mul_assoc]
  abel
end Derivatives
theorem hasDerivAt_norm_of_ne_zero {q : ℝ → ℍ[ℝ]} {q' : ℍ[ℝ]} (h : HasDerivAt q q' 0) (h0 : q 0 ≠ 0) :
    HasDerivAt (fun τ => ‖q τ‖) ((q' * star ((polarUnit (q 0) : UnitQuaternion) : ℍ[ℝ])).re) 0 := by
  have hn : 0 < ‖q 0‖ := norm_pos_iff.2 h0
  have h1 := h.norm_sq
  have h2 := h1.sqrt (by simpa using h0)
  have e : (fun τ => √(‖q τ‖ ^ 2)) = fun τ => ‖q τ‖ := by
    funext τ
    exact Real.sqrt_sq (norm_nonneg _)
  rw [e] at h2
  refine h2.congr_deriv ?_
  rw [Real.sqrt_sq hn.le, coe_polarUnit h0, quaternion_star_real_smul, Quaternion.inner_def]
  have e2 : (q 0 * star q').re = (q' * star (q 0)).re := by
    rw [← quaternion_re_star, star_mul, star_star]
  rw [e2, mul_smul_comm]
  simp only [Quaternion.re_smul, smul_eq_mul]
  field_simp
theorem hasDerivAt_gaugedBlockFit {Xc : ℝ → F.GaugeField j} {X : F.GaugeField j}
    {y : F.Site j → Fin 4 → imaginaryQuaternions}
    {kc : ℝ → F.Site (j + 1) → UnitQuaternion} {k : F.Site (j + 1) → UnitQuaternion}
    {yk : F.Site (j + 1) → imaginaryQuaternions}
    {X'c : ℝ → F.GaugeField (j + 1)} {X' : F.GaugeField (j + 1)} {yb : imaginaryQuaternions}
    {c : F.Site (j + 1) × Fin 4} (h0 : Xc 0 = X)
    (hd : ∀ x i, HasDerivAt (fun τ => ((Xc τ x i : UnitQuaternion) : ℍ[ℝ])) ((y x i : ℍ[ℝ]) * (X x i : ℍ[ℝ])) 0)
    (hk0 : kc 0 = k)
    (hk : ∀ x, HasDerivAt (fun τ => ((kc τ x : UnitQuaternion) : ℍ[ℝ])) ((yk x : ℍ[ℝ]) * (k x : ℍ[ℝ])) 0)
    (hb0 : X'c 0 = X')
    (hb : HasDerivAt (fun τ => ((X'c τ c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) ((yb : ℍ[ℝ]) * (X' c.1 c.2 : ℍ[ℝ])) 0)
    (hq : gaugedContourAverage X k c ≠ 0) :
    HasDerivAt (fun τ => gaugedBlockFit (Xc τ) (kc τ) (X'c τ) c) (blockFitRate X k X' y yk yb c) 0 := by
  subst h0 hk0 hb0
  have hm := hasDerivAt_gaugedContourAverage (Xc := Xc) (kc := kc) rfl hd rfl hk c
  have hn := hasDerivAt_norm_of_ne_zero hm hq
  have hi := hasDerivAt_coe_inv (g := fun τ => X'c τ c.1 c.2) hb
  have hp := hm.fun_mul hi
  have hr := (ChartCoordinates.reCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp
  unfold gaugedBlockFit
  refine (hn.fun_sub hr).congr_deriv ?_
  show _ - (_ : ℍ[ℝ]).re = _
  unfold blockFitRate
  simp only [coe_unitQuaternion_inv, mul_sub, mul_neg, Quaternion.re_sub, Quaternion.re_add, Quaternion.re_neg,
    mul_assoc]
  ring
def plaquetteBoundary {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : List PathStep :=
  [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
def upperBondRate (Y : GaugedVariation F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : imaginaryQuaternions :=
  if j + 1 < F.top then Y.bondVariation (j + 1) c.1 c.2 else 0
def actionTermRate (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (Y : GaugedVariation F) : F.ActionTerm → ℝ
  | Sum.inl p => - (holonomyRate (W 0) (Y.bondVariation 0) p.1 (plaquetteBoundary p) *
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])).re
  | Sum.inr c => a * blockFitRate (W c.1) (k (c.1 + 1)) (W (c.1 + 1)) (Y.bondVariation c.1)
      (Y.linkVariation c.1) (upperBondRate Y c.1 c.2) c.2
def AveragesNeZero (W : F.FieldChain) (k : F.SiteGauge) : F.ActionTerm → Prop
  | Sum.inl _ => True
  | Sum.inr c => gaugedContourAverage (W c.1) (k (c.1 + 1)) c.2 ≠ 0
theorem hasDerivAt_actionTermValue {a : ℝ} {Wc : ℝ → F.FieldChain} {W : F.FieldChain} {kc : ℝ → F.SiteGauge}
    {k : F.SiteGauge} {Y : GaugedVariation F} (h0 : Wc 0 = W) (hk0 : kc 0 = k)
    (hd : ∀ j, j < F.top → ∀ x i, HasDerivAt (fun τ => ((Wc τ j x i : UnitQuaternion) : ℍ[ℝ]))
      ((Y.bondVariation j x i : ℍ[ℝ]) * (W j x i : ℍ[ℝ])) 0)
    (htop : ∀ x i, HasDerivAt (fun τ => ((Wc τ F.top x i : UnitQuaternion) : ℍ[ℝ])) 0 0)
    (hk : ∀ j y, HasDerivAt (fun τ => ((kc τ (j + 1) y : UnitQuaternion) : ℍ[ℝ]))
      ((Y.linkVariation j y : ℍ[ℝ]) * (k (j + 1) y : ℍ[ℝ])) 0)
    {S : Finset F.Cell} {t : F.ActionTerm} (ht : t ∈ actionTerms S) (hq : AveragesNeZero W k t) :
    HasDerivAt (fun τ => actionTermValue a (Wc τ) (kc τ) t) (actionTermRate a W k Y t) 0 := by
  subst h0 hk0
  rcases t with p | ⟨j, c⟩
  · have hh := hasDerivAt_pathHolonomy (Xc := fun τ => Wc τ 0) rfl (hd 0 (by simp)) p.1 (plaquetteBoundary p)
    have hr := (ChartCoordinates.reCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hh
    have := hr.const_sub (1 : ℝ)
    exact this
  · have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)).1
    have hb : HasDerivAt (fun τ => ((Wc τ (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))
        ((upperBondRate Y j c : ℍ[ℝ]) * (Wc 0 (j + 1) c.1 c.2 : ℍ[ℝ])) 0 := by
      unfold upperBondRate
      by_cases h : j + 1 < F.top
      · rw [if_pos h]
        exact hd _ h _ _
      · rw [if_neg h]
        have hn : F.top = F.depth + 1 := rfl
        obtain rfl : j = F.depth := by omega
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact htop _ _
    exact (hasDerivAt_gaugedBlockFit (Xc := fun τ => Wc τ j) (kc := fun τ => kc τ (j + 1))
      (X'c := fun τ => Wc τ (j + 1)) rfl (hd j hj) rfl (hk j) rfl hb hq).const_mul a
theorem hasDerivAt_expUnit_smul (w : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • w) : UnitQuaternion) : ℍ[ℝ])) (w : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_expUnit_smul <;> assumption
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_zero_smul (w : imaginaryQuaternions) : expUnit ((0 : ℝ) • w) = 1 := by
  rw [zero_smul, expUnit_zero]
theorem variedFieldChain_zero (W : F.FieldChain) (Y : GaugedVariation F) : variedFieldChain W Y 0 = W := by apply _root_.YangMills.Construction.GaugedCriticality.variedFieldChain_zero <;> assumption
theorem variedGauge_zero (k : F.SiteGauge) (Y : GaugedVariation F) : variedGauge k Y 0 = k := by apply _root_.YangMills.Construction.GaugedCriticality.variedGauge_zero <;> assumption
theorem hasDerivAt_actionTermValue_varied (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (Y : GaugedVariation F)
    {S : Finset F.Cell} {t : F.ActionTerm} (ht : t ∈ actionTerms S) (hq : AveragesNeZero W k t) :
    HasDerivAt (fun τ => actionTermValue a (variedFieldChain W Y τ) (variedGauge k Y τ) t)
      (actionTermRate a W k Y t) 0 := by
  refine hasDerivAt_actionTermValue (variedFieldChain_zero W Y) (variedGauge_zero k Y)
    (fun j hj x i => ?_) (fun x i => ?_) (fun j y => ?_) ht hq
  · simp only [variedFieldChain, if_pos hj, Submonoid.coe_mul]
    have := (hasDerivAt_expUnit_smul (Y.bondVariation j x i)).mul_const (W j x i : ℍ[ℝ])
    exact this
  · simp only [variedFieldChain, lt_irrefl, if_false]
    exact hasDerivAt_const _ _
  · simp only [variedGauge, Submonoid.coe_mul]
    exact (hasDerivAt_expUnit_smul (Y.linkVariation j y)).mul_const (k (j + 1) y : ℍ[ℝ])
theorem firstVariation_eq_actionTermRate (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (Y : GaugedVariation F)
    {S : Finset F.Cell} {t : F.ActionTerm} (ht : t ∈ actionTerms S) (hq : AveragesNeZero W k t) :
    firstVariation a W k Y t = actionTermRate a W k Y t :=
  (hasDerivAt_actionTermValue_varied a W k Y ht hq).deriv
abbrev VariationSlot (F : BlockFrame) : Type := (Σ j, F.Site j × Fin 4) ⊕ (Σ j, F.Site (j + 1))
def slotOfBond (j : ℕ) (x : F.Site j) (i : Fin 4) : VariationSlot F := Sum.inl ⟨j, x, i⟩
def slotOfLink (j : ℕ) (y : F.Site (j + 1)) : VariationSlot F := Sum.inr ⟨j, y⟩
def variationOfSlots (Y : VariationSlot F → imaginaryQuaternions) : GaugedVariation F :=
  ⟨fun j x i => Y (slotOfBond j x i), fun j y => Y (slotOfLink j y)⟩
def restrictToBonds (g : VariationSlot F → ℝ) (j : ℕ) : F.Site j → Fin 4 → ℝ :=
  fun x i => g (slotOfBond j x i)
theorem contourAverageRate_add (X : F.GaugeField j) (y y' : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) :
    contourAverageRate X (fun x i => y x i + y' x i) c = contourAverageRate X y c + contourAverageRate X y' c := by
  unfold contourAverageRate
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [holonomyRate_add, add_mul]
theorem contourAverageRate_smul (X : F.GaugeField j) (r : ℝ) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) :
    contourAverageRate X (fun x i => r • y x i) c = r • contourAverageRate X y c := by
  unfold contourAverageRate
  rw [smul_comm r, Finset.smul_sum (r := r)]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.smul_sum (r := r)]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [holonomyRate_smul, smul_mul_assoc]
theorem gaugedAverageRate_add (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (y y' : F.Site j → Fin 4 → imaginaryQuaternions) (yk yk' : F.Site (j + 1) → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) :
    gaugedAverageRate X k (fun x i => y x i + y' x i) (fun x => yk x + yk' x) c =
      gaugedAverageRate X k y yk c + gaugedAverageRate X k y' yk' c := by
  unfold gaugedAverageRate
  rw [contourAverageRate_add]
  simp only [Submodule.coe_add, add_mul, mul_add]
  abel
theorem gaugedAverageRate_smul (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (r : ℝ)
    (y : F.Site j → Fin 4 → imaginaryQuaternions) (yk : F.Site (j + 1) → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) :
    gaugedAverageRate X k (fun x i => r • y x i) (fun x => r • yk x) c = r • gaugedAverageRate X k y yk c := by
  unfold gaugedAverageRate
  rw [contourAverageRate_smul]
  simp only [Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
theorem blockFitRate_add (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1))
    (y y' : F.Site j → Fin 4 → imaginaryQuaternions) (yk yk' : F.Site (j + 1) → imaginaryQuaternions)
    (yb yb' : imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    blockFitRate X k X' (fun x i => y x i + y' x i) (fun x => yk x + yk' x) (yb + yb') c =
      blockFitRate X k X' y yk yb c + blockFitRate X k X' y' yk' yb' c := by
  unfold blockFitRate
  rw [gaugedAverageRate_add]
  simp only [Submodule.coe_add, add_mul, mul_add, Quaternion.re_add]
  ring
theorem blockFitRate_smul (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1))
    (r : ℝ) (y : F.Site j → Fin 4 → imaginaryQuaternions) (yk : F.Site (j + 1) → imaginaryQuaternions)
    (yb : imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    blockFitRate X k X' (fun x i => r • y x i) (fun x => r • yk x) (r • yb) c =
      r * blockFitRate X k X' y yk yb c := by
  unfold blockFitRate
  rw [gaugedAverageRate_smul]
  simp only [Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, Quaternion.re_smul, smul_eq_mul]
  ring
theorem upperBondRate_add (Y Y' : VariationSlot F → imaginaryQuaternions) (j : ℕ) (c : F.Site (j + 1) × Fin 4) :
    upperBondRate (variationOfSlots (Y + Y')) j c =
      upperBondRate (variationOfSlots Y) j c + upperBondRate (variationOfSlots Y') j c := by
  unfold upperBondRate
  split_ifs
  · rfl
  · simp
theorem upperBondRate_smul (r : ℝ) (Y : VariationSlot F → imaginaryQuaternions) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) :
    upperBondRate (variationOfSlots (r • Y)) j c = r • upperBondRate (variationOfSlots Y) j c := by
  unfold upperBondRate
  split_ifs
  · rfl
  · simp
def actionTermRateLinear (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (t : F.ActionTerm) :
    (VariationSlot F → imaginaryQuaternions) →ₗ[ℝ] ℝ where
  toFun Y := actionTermRate a W k (variationOfSlots Y) t
  map_add' Y Y' := by
    rcases t with p | c
    · simp only [actionTermRate]
      have : (variationOfSlots (Y + Y')).bondVariation 0 =
          fun x i => (variationOfSlots Y).bondVariation 0 x i + (variationOfSlots Y').bondVariation 0 x i := rfl
      rw [this, holonomyRate_add, add_mul, Quaternion.re_add]
      ring
    · simp only [actionTermRate]
      rw [upperBondRate_add]
      have e1 : (variationOfSlots (Y + Y')).bondVariation c.1 =
          fun x i => (variationOfSlots Y).bondVariation c.1 x i + (variationOfSlots Y').bondVariation c.1 x i := rfl
      have e2 : (variationOfSlots (Y + Y')).linkVariation c.1 =
          fun x => (variationOfSlots Y).linkVariation c.1 x + (variationOfSlots Y').linkVariation c.1 x := rfl
      rw [e1, e2, blockFitRate_add]
      ring
  map_smul' r Y := by
    rcases t with p | c
    · simp only [actionTermRate, RingHom.id_apply, smul_eq_mul]
      have : (variationOfSlots (r • Y)).bondVariation 0 =
          fun x i => r • (variationOfSlots Y).bondVariation 0 x i := rfl
      rw [this, holonomyRate_smul, smul_mul_assoc, Quaternion.re_smul, smul_eq_mul]
      ring
    · simp only [actionTermRate, RingHom.id_apply, smul_eq_mul]
      rw [upperBondRate_smul]
      have e1 : (variationOfSlots (r • Y)).bondVariation c.1 =
          fun x i => r • (variationOfSlots Y).bondVariation c.1 x i := rfl
      have e2 : (variationOfSlots (r • Y)).linkVariation c.1 =
          fun x => r • (variationOfSlots Y).linkVariation c.1 x := rfl
      rw [e1, e2, blockFitRate_smul]
      ring
theorem actionTermRateLinear_apply (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (t : F.ActionTerm)
    (Y : VariationSlot F → imaginaryQuaternions) :
    actionTermRateLinear a W k t Y = actionTermRate a W k (variationOfSlots Y) t := rfl
def readWeight (g : VariationSlot F → ℝ) : F.ActionTerm → ℝ
  | Sum.inl p => bondSum (restrictToBonds g 0) p.1 (plaquetteBoundary p)
  | Sum.inr c => g (slotOfLink c.1 c.2.1) + g (slotOfLink c.1 (c.2.1 + unitStep (c.1 + 1) c.2.2)) +
      (if c.1 + 1 < F.top then g (slotOfBond (c.1 + 1) c.2.1 c.2.2) else 0) +
      contourBondSum (restrictToBonds g c.1) c.2
def actionTermSize (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) : F.ActionTerm → ℝ
  | Sum.inl p => ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖
  | Sum.inr c => a * normSubOne (bondMisfit (W c.1) (k (c.1 + 1)) (W (c.1 + 1)) c.2)
theorem actionTermSize_nonneg {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain) (k : F.SiteGauge) (t : F.ActionTerm) :
    0 ≤ actionTermSize a W k t := by
  rcases t with p | c
  · exact norm_nonneg _
  · exact mul_nonneg ha (norm_nonneg _)
theorem quaternion_abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by
  rw [abs_le]
  constructor
  · have := quaternion_re_le_norm (-q)
    rw [norm_neg, Quaternion.re_neg] at this
    linarith
  · exact quaternion_re_le_norm q
theorem norm_contourAverage_le_one (hodd : Odd F.blockSide) (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    ‖contourAverage X c‖ ≤ 1 := by
  unfold contourAverage
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      24 * (F.blockSide : ℝ) ^ 4 := by
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤ 24 := by
      intro h _
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_coe_unitQuaternion, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    refine (Finset.sum_le_sum h2).trans ?_
    rw [Finset.sum_const, LatticePaths.card_centredCube hodd]
    simp only [nsmul_eq_mul]
    push_cast
    linarith
  calc _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp
theorem norm_gaugedContourAverage (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) : ‖gaugedContourAverage X k c‖ = ‖contourAverage X c‖ := by
  unfold gaugedContourAverage
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion]
  ring
theorem norm_contourAverageRate_le (X : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : ‖contourAverageRate X y c‖ ≤ contourBondSum (fun x i => ‖y x i‖) c := by
  unfold contourAverageRate contourBondSum
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [norm_mul, norm_coe_unitQuaternion, mul_one]
  exact norm_holonomyRate_le _ _ _ _
theorem norm_gaugedAverageRate_le (hodd : Odd F.blockSide) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (yk : F.Site (j + 1) → imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    ‖gaugedAverageRate X k y yk c‖ ≤
      ‖yk c.1‖ + ‖yk (c.1 + unitStep (j + 1) c.2)‖ + contourBondSum (fun x i => ‖y x i‖) c := by
  unfold gaugedAverageRate
  have hq : ‖gaugedContourAverage X k c‖ ≤ 1 := by
    rw [norm_gaugedContourAverage]; exact norm_contourAverage_le_one hodd X c
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul]
    have : ‖((yk c.1 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖yk c.1‖ := rfl
    rw [this]
    exact mul_le_of_le_one_right (norm_nonneg _) hq
  · rw [norm_mul]
    have : ‖((yk (c.1 + unitStep (j + 1) c.2) : imaginaryQuaternions) : ℍ[ℝ])‖ =
        ‖yk (c.1 + unitStep (j + 1) c.2)‖ := rfl
    rw [this]
    exact mul_le_of_le_one_left (norm_nonneg _) hq
  · rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
    exact norm_contourAverageRate_le _ _ _
theorem abs_blockFitRate_le (hodd : Odd F.blockSide) (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (y : F.Site j → Fin 4 → imaginaryQuaternions)
    (yk : F.Site (j + 1) → imaginaryQuaternions) (yb : imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    |blockFitRate X k X' y yk yb c| ≤ normSubOne (bondMisfit X k X' c) *
      (‖yk c.1‖ + ‖yk (c.1 + unitStep (j + 1) c.2)‖ + ‖yb‖ + contourBondSum (fun x i => ‖y x i‖) c) := by
  set q := gaugedContourAverage X k c with hq
  set u := polarUnit q with hu
  set v := X' c.1 c.2 with hv
  have hm : normSubOne (bondMisfit X k X' c) = ‖(v : ℍ[ℝ]) - (u : ℍ[ℝ])‖ := by
    unfold normSubOne bondMisfit
    rw [← hq, ← hu, ← hv]
    have e : ((v * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
        ((v : ℍ[ℝ]) - (u : ℍ[ℝ])) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [Submonoid.coe_mul, sub_mul, coe_mul_coe_inv]
    rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
  have hw : ‖star (u : ℍ[ℝ]) - star (v : ℍ[ℝ])‖ = normSubOne (bondMisfit X k X' c) := by
    rw [hm, ← star_sub, norm_star, norm_sub_rev]
  have hnq : ‖q‖ ≤ 1 := by rw [hq, norm_gaugedContourAverage]; exact norm_contourAverage_le_one hodd X c
  have h2 : |(q * star (v : ℍ[ℝ]) * (yb : ℍ[ℝ])).re| ≤ normSubOne (bondMisfit X k X' c) * ‖yb‖ := by
    by_cases h0 : q = 0
    · rw [h0]
      simp only [zero_mul, Quaternion.re_zero, abs_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have hqu : q = ‖q‖ • (u : ℍ[ℝ]) := by
        rw [hu, coe_polarUnit h0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
      have hyb : (yb : ℍ[ℝ]).re = 0 := yb.2
      have e : (q * star (v : ℍ[ℝ]) * (yb : ℍ[ℝ])).re =
          ‖q‖ * (((u : ℍ[ℝ]) * star (v : ℍ[ℝ]) - 1) * (yb : ℍ[ℝ])).re := by
        conv_lhs => rw [hqu]
        rw [smul_mul_assoc, smul_mul_assoc, Quaternion.re_smul, smul_eq_mul, sub_mul, one_mul,
          Quaternion.re_sub, hyb, sub_zero]
      rw [e, abs_mul, abs_of_nonneg (norm_nonneg q)]
      have e2 : ‖(u : ℍ[ℝ]) * star (v : ℍ[ℝ]) - 1‖ = normSubOne (bondMisfit X k X' c) := by
        rw [hm]
        have e3 : (u : ℍ[ℝ]) * star (v : ℍ[ℝ]) - 1 = ((u : ℍ[ℝ]) - (v : ℍ[ℝ])) * star (v : ℍ[ℝ]) := by
          have := coe_mul_coe_inv v
          rw [coe_unitQuaternion_inv] at this
          rw [sub_mul, this]
        rw [e3, norm_mul, norm_star, norm_coe_unitQuaternion, mul_one, norm_sub_rev]
      calc _ ≤ 1 * ‖((u : ℍ[ℝ]) * star (v : ℍ[ℝ]) - 1) * (yb : ℍ[ℝ])‖ :=
            mul_le_mul hnq (quaternion_abs_re_le_norm _) (abs_nonneg _) zero_le_one
        _ = _ := by rw [one_mul, norm_mul, e2]; rfl
  unfold blockFitRate
  rw [← hq, ← hu, ← hv]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(gaugedAverageRate X k y yk c * (star (u : ℍ[ℝ]) - star (v : ℍ[ℝ]))).re| ≤
      normSubOne (bondMisfit X k X' c) *
        (‖yk c.1‖ + ‖yk (c.1 + unitStep (j + 1) c.2)‖ + contourBondSum (fun x i => ‖y x i‖) c) := by
    refine (quaternion_abs_re_le_norm _).trans ?_
    rw [norm_mul, hw, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_gaugedAverageRate_le hodd X k y yk c) (norm_nonneg _)
  have := add_le_add h1 h2
  refine this.trans (le_of_eq ?_)
  ring
theorem abs_actionTermRateLinear_le (hodd : Odd F.blockSide) {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain)
    (k : F.SiteGauge) (Y : VariationSlot F → imaginaryQuaternions) (t : F.ActionTerm) :
    |actionTermRateLinear a W k t Y| ≤ actionTermSize a W k t * readWeight (fun u => ‖Y u‖) t := by
  rw [actionTermRateLinear_apply]
  rcases t with p | c
  · simp only [actionTermRate, actionTermSize, readWeight, abs_neg]
    set T := holonomyRate (W 0) ((variationOfSlots Y).bondVariation 0) p.1 (plaquetteBoundary p) with hT
    set H := ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) with hH
    have hTre : T.re = 0 := re_holonomyRate _ _ _ _
    have e : (T * H).re = (T * H.im).re := by
      conv_lhs => rw [← Quaternion.re_add_im H]
      rw [mul_add, Quaternion.re_add]
      have : (T * (H.re : ℍ[ℝ])).re = 0 := by
        simp [Quaternion.re_mul, hTre]
      rw [this, zero_add]
    rw [e]
    refine (quaternion_abs_re_le_norm _).trans ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_holonomyRate_le _ _ _ _) (norm_nonneg _)
  · simp only [actionTermRate, actionTermSize, readWeight]
    rw [abs_mul, abs_of_nonneg ha, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ha
    refine (abs_blockFitRate_le hodd _ _ _ _ _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)
    have e : ‖upperBondRate (variationOfSlots Y) c.1 c.2‖ =
        if c.1 + 1 < F.top then ‖Y (slotOfBond (c.1 + 1) c.2.1 c.2.2)‖ else 0 := by
      unfold upperBondRate
      split_ifs
      · rfl
      · simp
    rw [e]
    rfl
def LiesOnPath (b : F.Site j × Fin 4) : F.Site j → List PathStep → Prop
  | _, [] => False
  | x, st :: r => (if st.2 then b = (x, st.1) else b = (x - unitStep j st.1, st.1)) ∨
      LiesOnPath b (x + stepDisplacement j st) r
theorem bondSum_mono {g g' : F.Site j → Fin 4 → ℝ} (x : F.Site j) (l : List PathStep)
    (h : ∀ b, LiesOnPath b x l → g b.1 b.2 ≤ g' b.1 b.2) : bondSum g x l ≤ bondSum g' x l := by
  induction l generalizing x with
  | nil => simp [bondSum]
  | cons st r ih =>
    simp only [bondSum]
    refine add_le_add ?_ (ih _ fun b hb => h b (Or.inr hb))
    split_ifs with hs
    · exact h (x, st.1) (Or.inl (by simp [hs]))
    · exact h (x - unitStep j st.1, st.1) (Or.inl (by simp [hs]))
theorem bondSum_zero (x : F.Site j) (l : List PathStep) : bondSum (fun _ _ => (0 : ℝ)) x l = 0 := by
  induction l generalizing x with
  | nil => simp [bondSum]
  | cons st r ih => simp [bondSum, ih]
theorem bondSum_nonneg {g : F.Site j → Fin 4 → ℝ} (hg : ∀ x i, 0 ≤ g x i) (x : F.Site j) (l : List PathStep) :
    0 ≤ bondSum g x l := by
  induction l generalizing x with
  | nil => simp [bondSum]
  | cons st r ih =>
    simp only [bondSum]
    refine add_nonneg ?_ (ih _)
    split_ifs <;> exact hg _ _
theorem contourBondSum_mono {g g' : F.Site j → Fin 4 → ℝ} (c : F.Site (j + 1) × Fin 4)
    (h : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ b,
      LiesOnPath b (refineSite c.1) (bondContour F.blockSide a π c.2) → g b.1 b.2 ≤ g' b.1 b.2) :
    contourBondSum g c ≤ contourBondSum g' c := by
  unfold contourBondSum
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun π _ => bondSum_mono _ _ (h a ha π)
def ReadsSlot : F.ActionTerm → VariationSlot F → Prop
  | Sum.inl p, u => ∃ b : F.Site 0 × Fin 4, u = slotOfBond 0 b.1 b.2 ∧ LiesOnPath b p.1 (plaquetteBoundary p)
  | Sum.inr c, u => u = slotOfLink c.1 c.2.1 ∨ u = slotOfLink c.1 (c.2.1 + unitStep (c.1 + 1) c.2.2) ∨
      (c.1 + 1 < F.top ∧ u = slotOfBond (c.1 + 1) c.2.1 c.2.2) ∨
      ∃ a ∈ centredCube F.blockSide, ∃ π : Equiv.Perm (Fin 4), ∃ b : F.Site c.1 × Fin 4,
        u = slotOfBond c.1 b.1 b.2 ∧ LiesOnPath b (refineSite c.2.1) (bondContour F.blockSide a π c.2.2)
theorem readWeight_mono {g g' : VariationSlot F → ℝ} (t : F.ActionTerm) (h : ∀ u, ReadsSlot t u → g u ≤ g' u) :
    readWeight g t ≤ readWeight g' t := by
  rcases t with p | c
  · exact bondSum_mono _ _ fun b hb => h _ ⟨b, rfl, hb⟩
  · simp only [readWeight]
    refine add_le_add (add_le_add (add_le_add (h _ (Or.inl rfl)) (h _ (Or.inr (Or.inl rfl)))) ?_) ?_
    · split_ifs with hc
      · exact h _ (Or.inr (Or.inr (Or.inl ⟨hc, rfl⟩)))
      · exact le_rfl
    · exact contourBondSum_mono _ fun a ha π b hb => h _ (Or.inr (Or.inr (Or.inr ⟨a, ha, π, b, rfl, hb⟩)))
theorem readWeight_zero (t : F.ActionTerm) : readWeight (fun _ : VariationSlot F => (0 : ℝ)) t = 0 := by
  rcases t with p | c
  · exact bondSum_zero _ _
  · simp only [readWeight, contourBondSum]
    have : ∀ a π, bondSum (restrictToBonds (fun _ : VariationSlot F => (0 : ℝ)) c.1) (refineSite c.2.1)
        (bondContour F.blockSide a π c.2.2) = 0 :=
      fun a π => bondSum_zero _ _
    simp [this]
theorem actionTermRateLinear_eq_zero (hodd : Odd F.blockSide) {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain)
    (k : F.SiteGauge) {Y : VariationSlot F → imaginaryQuaternions} {t : F.ActionTerm}
    (h : ∀ u, ReadsSlot t u → Y u = 0) : actionTermRateLinear a W k t Y = 0 := by
  have h1 := abs_actionTermRateLinear_le hodd ha W k Y t
  have h2 : readWeight (fun u => ‖Y u‖) t ≤ 0 := by
    rw [← readWeight_zero t]
    exact readWeight_mono t fun u hu => by simp [h u hu]
  have h3 : actionTermSize a W k t * readWeight (fun u => ‖Y u‖) t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (actionTermSize_nonneg ha W k t) h2
  exact abs_eq_zero.1 (le_antisymm (h1.trans h3) (abs_nonneg _))
def farWeight (g : VariationSlot F → ℝ) : F.ActionTerm → ℝ
  | Sum.inl p => bondSum (restrictToBonds g 0) p.1 (plaquetteBoundary p)
  | Sum.inr c => g (slotOfLink c.1 (c.2.1 + unitStep (c.1 + 1) c.2.2)) +
      contourBondSum (restrictToBonds g c.1) c.2
theorem readWeight_eq_farWeight {g : VariationSlot F → ℝ} (t : F.ActionTerm)
    (h : ∀ c : (j : ℕ) × (F.Site (j + 1) × Fin 4), t = Sum.inr c →
      g (slotOfLink c.1 c.2.1) = 0 ∧ g (slotOfBond (c.1 + 1) c.2.1 c.2.2) = 0) :
    readWeight g t = farWeight g t := by
  rcases t with p | c
  · rfl
  · obtain ⟨h1, h2⟩ := h c rfl
    simp only [readWeight, farWeight, h1, h2, zero_add, ite_self, add_zero]
end VariationRates
end YangMills.Construction.BlockAverages
end
