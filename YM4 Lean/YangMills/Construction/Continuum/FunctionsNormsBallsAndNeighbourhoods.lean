import YangMills.Construction.Continuum.TermsReadOnATorus
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusTransport
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
section Numbers
variable {X E : Type*}
def ennSupNorm [Norm E] (h : X → E) : ℝ≥0∞ := ⨆ u, ENNReal.ofReal ‖h u‖
variable [NormedAddCommGroup E]
def ennLipConst (d : X → X → ℝ) (h : X → E) : ℝ≥0∞ :=
  ⨆ (u : X) (v : X) (_ : u ≠ v), ENNReal.ofReal (‖h u - h v‖ / d u v)
def LipConstFinite (d : X → X → ℝ) (h : X → E) : Prop := ennLipConst d h < ∞
theorem ennLipConst_le_ofReal_iff {d : X → X → ℝ} (hd : ∀ u v, u ≠ v → 0 < d u v)
    (hd₀ : ∀ u, 0 ≤ d u u) {h : X → E} {C : ℝ} (hC : 0 ≤ C) :
    ennLipConst d h ≤ ENNReal.ofReal C ↔ ∀ u v, ‖h u - h v‖ ≤ C * d u v := by
  constructor
  · intro H u v
    by_cases huv : u = v
    · subst huv
      simpa using mul_nonneg hC (hd₀ u)
    · have h₁ : ENNReal.ofReal (‖h u - h v‖ / d u v) ≤ ENNReal.ofReal C :=
        le_trans (le_iSup₂_of_le u v
          (le_iSup (fun _ : u ≠ v => ENNReal.ofReal (‖h u - h v‖ / d u v)) huv)) H
      exact (div_le_iff₀ (hd u v huv)).mp ((ENNReal.ofReal_le_ofReal_iff hC).mp h₁)
  · intro H
    refine iSup_le fun u => iSup_le fun v => iSup_le fun huv => ?_
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (hd u v huv)).mpr (H u v))
theorem lipConstFinite_iff_isLipschitzFor {d : X → X → ℝ} (hd : ∀ u v, u ≠ v → 0 < d u v)
    (hd₀ : ∀ u, 0 ≤ d u u) {h : X → E} : LipConstFinite d h ↔ IsLipschitzFor d h := by
  constructor
  · intro H
    refine ⟨(ennLipConst d h).toReal, ENNReal.toReal_nonneg, ?_⟩
    refine (ennLipConst_le_ofReal_iff hd hd₀ ENNReal.toReal_nonneg).mp ?_
    rw [ENNReal.ofReal_toReal H.ne]
  · rintro ⟨C, hC, H⟩
    exact lt_of_le_of_lt ((ennLipConst_le_ofReal_iff hd hd₀ hC).mpr H) ENNReal.ofReal_lt_top
theorem ofReal_bestLipschitzConstant {d : X → X → ℝ} (hd : ∀ u v, u ≠ v → 0 < d u v)
    (hd₀ : ∀ u, 0 ≤ d u u) {h : X → E} (hl : LipConstFinite d h) :
    ENNReal.ofReal (bestLipschitzConstant d h) = ennLipConst d h := by
  have hmem : (ennLipConst d h).toReal ∈ {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖h x - h y‖ ≤ C * d x y} := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    refine (ennLipConst_le_ofReal_iff hd hd₀ ENNReal.toReal_nonneg).mp ?_
    rw [ENNReal.ofReal_toReal hl.ne]
  have hlow : BddBelow {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖h x - h y‖ ≤ C * d x y} :=
    ⟨0, fun _ hC => hC.1⟩
  apply le_antisymm
  · have h₁ : bestLipschitzConstant d h ≤ (ennLipConst d h).toReal := csInf_le hlow hmem
    calc ENNReal.ofReal (bestLipschitzConstant d h)
        ≤ ENNReal.ofReal (ennLipConst d h).toReal := ENNReal.ofReal_le_ofReal h₁
      _ = ennLipConst d h := ENNReal.ofReal_toReal hl.ne
  · refine iSup_le fun u => iSup_le fun v => iSup_le fun huv => ?_
    refine ENNReal.ofReal_le_ofReal (le_csInf ⟨_, hmem⟩ fun C hC => ?_)
    exact (div_le_iff₀ (hd u v huv)).mpr (hC.2 u v)
end Numbers
section RealFuns
variable {X : Type*}
theorem ennSupNorm_toComplex (h : RealFun X) :
    ennSupNorm h.toComplex = ennSupNorm h := by
  simp [ennSupNorm, RealFun.toComplex]
theorem ennLipConst_toComplex (d : X → X → ℝ) (h : RealFun X) :
    ennLipConst d h.toComplex = ennLipConst d h := by
  have e : ∀ u v, ‖h.toComplex u - h.toComplex v‖ = ‖h u - h v‖ := fun u v => by
    change ‖((h u : ℝ) : ℂ) - ((h v : ℝ) : ℂ)‖ = _
    rw [← Complex.ofReal_sub, Complex.norm_real]
  simp only [ennLipConst, e]
end RealFuns
theorem euclidNormVec_pos {x : Fin 4 → ℝ} (hx : x ≠ 0) : 0 < euclidNormVec x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
  positivity
namespace TransportData
variable (D : TransportData)
theorem torusDist_nonneg (p q : D.Torus) : 0 ≤ D.torusDist p q := by
  have hl := D.isLeast_torusDist (liftPoint p) (liftPoint q)
  rw [show D.projHom (liftPoint p) = p from torusProj_liftPoint p,
    show D.projHom (liftPoint q) = q from torusProj_liftPoint q] at hl
  obtain ⟨γ, -, e⟩ := hl.1
  rw [← e]
  exact Real.sqrt_nonneg _
theorem torusDist_pos {p q : D.Torus} (h : p ≠ q) : 0 < D.torusDist p q := by
  have hp : D.projHom (liftPoint p) = p := torusProj_liftPoint p
  have hq : D.projHom (liftPoint q) = q := torusProj_liftPoint q
  have hl := D.isLeast_torusDist (liftPoint p) (liftPoint q)
  rw [hp, hq] at hl
  obtain ⟨γ, hγ, e⟩ := hl.1
  rw [← e]
  refine euclidNormVec_pos fun h₀ => h ?_
  have hγ' : liftPoint p - liftPoint q ∈ D.periods := by
    rw [sub_eq_zero.mp h₀]
    exact hγ
  exact hp.symm.trans ((projHom_eq_iff.mpr hγ').trans hq)
end TransportData
namespace Domain
variable (D : TransportData)
def pointDist : (Y : Domain) → Y.Point D → Y.Point D → ℝ
  | .euclidean, u, v => euclidDistR4 u v
  | .torus, u, v => D.torusDist u v
theorem pointDist_pos (Y : Domain) {u v : Y.Point D} (h : u ≠ v) : 0 < Y.pointDist D u v := by
  cases Y with
  | euclidean => exact euclidNormVec_pos (sub_ne_zero.mpr h)
  | torus => exact D.torusDist_pos h
theorem pointDist_self_nonneg (Y : Domain) (u : Y.Point D) : 0 ≤ Y.pointDist D u u := by
  cases Y with
  | euclidean => exact Real.sqrt_nonneg _
  | torus => exact D.torusDist_nonneg u u
def fnSupport {E : Type*} [Zero E] : (Y : Domain) → (Y.Point D → E) → Set (Y.Point D)
  | .euclidean, h => tsupport (h : (Fin 4 → ℝ) → E)
  | .torus, h => D.torusSupport h
section Lipschitz
variable {E : Type*} [NormedAddCommGroup E]
def lipConst (Y : Domain) (h : Y.Point D → E) : ℝ≥0∞ := ennLipConst (Y.pointDist D) h
def ennSharpNorm (Y : Domain) (h : Y.Point D → E) : ℝ≥0∞ :=
  max (ennSupNorm h) (ENNReal.ofReal (40 * D.M) * Y.lipConst D h)
def LipschitzOn (Y : Domain) (h : Y.Point D → E) : Prop := Y.lipConst D h < ∞
theorem lipschitzOn_iff (Y : Domain) {h : Y.Point D → E} :
    Y.LipschitzOn D h ↔ IsLipschitzFor (Y.pointDist D) h :=
  lipConstFinite_iff_isLipschitzFor (fun _ _ huv => Y.pointDist_pos D huv)
    (Y.pointDist_self_nonneg D)
theorem ofReal_bestLipschitzConstant_eq_lipConst (Y : Domain) {h : Y.Point D → E}
    (hl : Y.LipschitzOn D h) :
    ENNReal.ofReal (bestLipschitzConstant (Y.pointDist D) h) = Y.lipConst D h :=
  YangMills.Construction.TorusTransport.ofReal_bestLipschitzConstant
    (fun _ _ huv => Y.pointDist_pos D huv) (Y.pointDist_self_nonneg D) hl
end Lipschitz
section Derivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def IsC1On : (Y : Domain) → (Y.Point D → E) → Prop
  | .euclidean, f => IsC1R4 f
  | .torus, f => D.IsC1 f
def partialDeriv (i : Fin 4) : (Y : Domain) → (Y.Point D → E) → Y.Point D → E
  | .euclidean, f => partialDerivR4 i f
  | .torus, f => D.partialDeriv i f
def gradNorm (Y : Domain) (f : Y.Point D → E) (u : Y.Point D) : ℝ :=
  Real.sqrt (∑ i, ‖Y.partialDeriv D i f u‖ ^ 2)
def gradSupNorm (Y : Domain) (f : Y.Point D → E) : ℝ≥0∞ :=
  ennSupNorm (Y.gradNorm D f)
end Derivatives
def setDist (Y : Domain) (A A' : Set (Y.Point D)) : ℝ≥0∞ :=
  ⨅ u ∈ A, ⨅ v ∈ A', ENNReal.ofReal (Y.pointDist D u v)
theorem setDist_empty_right (Y : Domain) (A : Set (Y.Point D)) :
    Y.setDist D A ∅ = ∞ := by
  simp [setDist]
theorem setDist_empty_left (Y : Domain) (A : Set (Y.Point D)) :
    Y.setDist D ∅ A = ∞ := by
  simp [setDist]
theorem setDist_euclidean (A A' : Set (Fin 4 → ℝ)) :
    Domain.euclidean.setDist D A A' = setDistR4 A A' :=
  rfl
end Domain
def HasCompactSupportIn {E : Type*} [Zero E] (h : (Fin 4 → ℝ) → E) (A : Set (Fin 4 → ℝ)) :
    Prop :=
  IsCompact (tsupport h) ∧ tsupport h ⊆ A
def lipschitzSupportedIn (A : Set (Fin 4 → ℝ)) : Set (RealFun (Fin 4 → ℝ)) :=
  {h | LipConstFinite euclidDistR4 h ∧ HasCompactSupportIn h A}
def c1SupportedIn (A : Set (Fin 4 → ℝ)) : Set (RealFun (Fin 4 → ℝ)) :=
  {h | IsC1R4 h ∧ HasCompactSupportIn h A}
def c1CompactSupport : Set (ComplexFun (Fin 4 → ℝ)) :=
  {h | IsC1R4 h ∧ IsCompact (tsupport h)}
abbrev ballR4 (x : Fin 4 → ℝ) (R : ℝ) : Set (Fin 4 → ℝ) := closedBallR4 x R
def openBallZero (ρ : ℝ) : Set (Fin 4 → ℝ) := {x | euclidNorm x < ρ}
def closedNbhd (S : Set (Fin 4 → ℝ)) (η : ℝ) : Set (Fin 4 → ℝ) :=
  {x | setDistR4 {x} S ≤ ENNReal.ofReal η}
end TorusTransport
end YangMills.Construction
end
