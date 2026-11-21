import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace RegionShares
open BlockAverages TorusFields TorusShares TorusLumps StepCosts ColdChain
section TopLevel
variable {L t m : ℕ} [NeZero m]
theorem period_torusFrame (i : Fin 4) : (torusFrame L t m).period (torusFrame L t m).top i = m := by
  simp [BlockAverages.BlockFrame.period, torusFrame, BlockAverages.BlockFrame.top]
instance neZero_period_torusFrame (i : Fin 4) : NeZero ((torusFrame L t m).period (torusFrame L t m).top i) :=
  ⟨by rw [period_torusFrame]; exact NeZero.ne m⟩
def siteOfCell (x : (torusFrame L t m).Cell) : TorusSite m := fun k => ((siteCoords x k : ℤ) : ZMod m)
theorem readAtLevel_torusFrame (W : TorusField m) (x : (torusFrame L t m).Cell) (i : Fin 4) :
    readAtLevel (torusFrame L t m) (torusFrame L t m).top W x i = W (siteOfCell x) i := rfl
theorem siteOfCell_torusSiteInFrame (y : TorusSite m) :
    siteOfCell (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y) = y := by apply _root_.YangMills.Construction.TorusFrame.siteOfCell_torusSiteInFrame <;> assumption
theorem siteOfCell_add (x y : (torusFrame L t m).Cell) : siteOfCell (x + y) = siteOfCell x + siteOfCell y := by apply _root_.YangMills.Construction.TorusFrame.siteOfCell_add <;> assumption
theorem siteOfCell_siteOfCoords (h : Fin 4 → ℤ) :
    siteOfCell (siteOfCoords (torusFrame L t m).top h : (torusFrame L t m).Cell) = siteOfInt h := by apply _root_.YangMills.Construction.TorusFrame.siteOfCell_siteOfCoords <;> assumption
theorem siteOfCell_injective {x y : (torusFrame L t m).Cell} (h : siteOfCell x = siteOfCell y) : x = y := by apply _root_.YangMills.Construction.TorusFrame.siteOfCell_injective <;> assumption
theorem torusSiteInFrame_siteOfCell (x : (torusFrame L t m).Cell) :
    torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top (siteOfCell x) = x := by apply _root_.YangMills.Construction.TorusFrame.torusSiteInFrame_siteOfCell <;> assumption
theorem valMinAbs_sub_castInt {p q : ℕ} (hp : p = q) [NeZero p] (a b : ZMod p) :
    (a - b).valMinAbs = (((a.cast : ℤ) : ZMod q) - ((b.cast : ℤ) : ZMod q)).valMinAbs := by apply _root_.YangMills.Construction.TorusFrame.valMinAbs_sub_castInt <;> assumption
theorem cellSupDist_torusFrame (x z : (torusFrame L t m).Cell) :
    cellSupDist x z = _root_.YangMills.Construction.TorusFields.supDist (siteOfCell x) (siteOfCell z) := by apply _root_.YangMills.Construction.TorusFrame.cellSupDist_torusFrame <;> assumption
theorem isOrthantRegular_torusFrame {X : Finset (TorusSite m)} {k : ℕ} (h : IsLocallyOrthantClosed X k) :
    IsOrthantRegular (cellsOfSites (torusFrame L t m) X) k := by apply _root_.YangMills.Construction.TorusFrame.isOrthantRegular_torusFrame <;> assumption
theorem mem_cellsOfSites_torusFrame {X : Finset (TorusSite m)} {x : (torusFrame L t m).Cell} :
    x ∈ cellsOfSites (torusFrame L t m) X ↔ siteOfCell x ∈ X := by apply _root_.YangMills.Construction.TorusFrame.mem_cellsOfSites_torusFrame <;> assumption
theorem isCold_torusFrame {X : Finset (TorusSite m)} {s : ℝ} {W : TorusField m} (h : IsColdOn X s W) :
    IsCold (cellsOfSites (torusFrame L t m) X) (torusFrame L t m).top s
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top W) := by apply _root_.YangMills.Construction.TorusFrame.isCold_torusFrame <;> assumption
theorem isAdmissibleAmbient_torusFrame (h : 64 ≤ m) : IsAdmissibleAmbient (torusFrame L t m) := Or.inr fun _ => h
theorem agreeOnBall_torusFrame {X X' : Finset (TorusSite m)} {W W' : TorusField m} {y : TorusSite m} {ρ : ℕ}
    (h : RegionsAgreeNear X X' W W' y ρ) :
    AgreeOnBall (cellsOfSites (torusFrame L t m) X) (readAtLevel (torusFrame L t m) (torusFrame L t m).top W)
      (cellsOfSites (torusFrame L t m) X') (readAtLevel (torusFrame L t m) (torusFrame L t m).top W')
      (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y)
      (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y) ρ := by
  obtain ⟨hs, hm, hf⟩ := h
  refine ⟨fun _ => Or.inr hs, fun _ => Or.inr hs, fun v hv => ?_, fun b hb => ?_⟩
  · rw [mem_cellsOfSites_torusFrame, mem_cellsOfSites_torusFrame, siteOfCell_add, siteOfCell_torusSiteInFrame,
      siteOfCell_siteOfCoords]
    exact hm v hv
  · rw [readAtLevel_torusFrame, readAtLevel_torusFrame, siteOfCell_add, siteOfCell_torusSiteInFrame,
      siteOfCell_siteOfCoords]
    exact hf b hb
end TopLevel
section Lipschitz
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
variable {m : ℕ}
theorem norm_holonomy_sub_le (W W' : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    ‖((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - holonomy W' x μ ν‖ ≤
      ‖(W x μ : ℍ[ℝ]) - W' x μ‖ +
        ‖(W (x + TorusFields.unitStep m μ) ν : ℍ[ℝ]) - W' (x + TorusFields.unitStep m μ) ν‖ +
        ‖(W (x + TorusFields.unitStep m ν) μ : ℍ[ℝ]) - W' (x + TorusFields.unitStep m ν) μ‖ +
        ‖(W x ν : ℍ[ℝ]) - W' x ν‖ := by apply _root_.YangMills.Construction.TorusFrame.norm_holonomy_sub_le <;> assumption
theorem abs_plaquetteEnergy_sub_le (W W' : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    |plaquetteEnergy W x μ ν - plaquetteEnergy W' x μ ν| ≤
      ‖(W x μ : ℍ[ℝ]) - W' x μ‖ +
        ‖(W (x + TorusFields.unitStep m μ) ν : ℍ[ℝ]) - W' (x + TorusFields.unitStep m μ) ν‖ +
        ‖(W (x + TorusFields.unitStep m ν) μ : ℍ[ℝ]) - W' (x + TorusFields.unitStep m ν) μ‖ +
        ‖(W x ν : ℍ[ℝ]) - W' x ν‖ := by
  refine le_trans ?_ (norm_holonomy_sub_le W W' x μ ν)
  unfold plaquetteEnergy
  have : |(((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - holonomy W' x μ ν).re| ≤
      ‖((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - holonomy W' x μ ν‖ := abs_re_le_norm _
  have e : (1 - ((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]).re -
      (1 - ((holonomy W' x μ ν : UnitQuaternion) : ℍ[ℝ]).re)) =
      -(((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - holonomy W' x μ ν).re := by
    simp
  rw [e, abs_neg]
  exact this
theorem plaquetteEnergy_le_two (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteEnergy W x μ ν ≤ 2 := by apply _root_.YangMills.Construction.TorusFrame.plaquetteEnergy_le_two <;> assumption
theorem norm_expUnit_sub_one_le (v : imaginaryQuaternions) :
    ‖((expUnit v : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(v : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
theorem expUnit_smul_mul (v : imaginaryQuaternions) (p q : ℝ) :
    expUnit (p • v) * expUnit (q • v) = expUnit ((p + q) • v) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
end Lipschitz
section SuccessorLevel
variable {a δ : ℝ} {L : ℕ} {lam ρ σA cg : ℝ} {N : ℕ → ℝ}
theorem levelShare_succ_sub_le (hch : ColdChainConstants a δ L lam ρ σA cg N) (t m : ℕ) [NeZero m]
    (X X' : Finset (TorusSite m)) (W W' : TorusField m) (y : TorusSite m) (r : ℕ) (s : ℝ)
    (hm : 64 ≤ m) (hs : 0 < s) (hsσ : s ≤ σA) (hX : IsLocallyOrthantClosed X 1024)
    (hX' : IsLocallyOrthantClosed X' 1024)
    (hc : IsColdOn X s W) (hc' : IsColdOn X' s W') (hag : RegionsAgreeNear X X' W W' y r) :
    |levelShare a L (t + 1) X y W - levelShare a L (t + 1) X' y W'| ≤ σA ^ 2 * N 0 * Real.exp (-(δ * r)) := by
  obtain ⟨hδ, -, -, -, -, hσ, -, hN, main⟩ := hch
  have h := main (torusFrame L t m) 1024 (cellsOfSites (torusFrame L t m) X) rfl
    (isAdmissibleAmbient_torusFrame hm) le_rfl (isOrthantRegular_torusFrame hX) s
    (readAtLevel (torusFrame L t m) (torusFrame L t m).top W) hs hsσ (isCold_torusFrame hc)
  obtain ⟨-, -, -, -, -, h6⟩ := h
  have h7 := (h6 (torusFrame L t m) (cellsOfSites (torusFrame L t m) X')
    (readAtLevel (torusFrame L t m) (torusFrame L t m).top W')
    (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y)
    (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y) r rfl rfl
    (isAdmissibleAmbient_torusFrame hm) (isOrthantRegular_torusFrame hX') (isCold_torusFrame hc')
    (agreeOnBall_torusFrame hag)).1
  have h8 := h7 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
  have e0 : ∀ (S : Finset (torusFrame L t m).Cell) (V : (torusFrame L t m).GaugeField (torusFrame L t m).top)
      (Y : (torusFrame L t m).Cell), mixedBondDerivative (minimalCellShare a S Y) V
        (offsetBonds Y (Fin.elim0 : Fin 0 → _)) (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
        minimalCellShare a S Y V := by
    intro S V Y
    unfold mixedBondDerivative
    rw [iteratedFDeriv_zero_apply]
    congr 1
    funext z i
    simp [rotatedField, bondSpread, expUnit_zero]
  rw [e0, e0] at h8
  have hf : derivativeScale s 0 = s ^ 2 := by simp [derivativeScale]
  rw [hf, neg_mul] at h8
  refine h8.trans ?_
  have h2 : s ^ 2 ≤ σA ^ 2 := by nlinarith
  have := hN 0
  have he := Real.exp_pos (-(δ * r))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 this.le) he.le
theorem rotatedField_readAtLevel (a : ℝ) (t m : ℕ) [NeZero m] (W : TorusField m) (b : TorusBond m)
    (v : imaginaryQuaternions) (u : imaginaryQuaternions) (κ τ₀ : ℝ)
    (hu : u = κ • v) (σ : Fin 1 → ℝ) :
    rotatedField (bondSpread (fun _ : Fin 1 => (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top b.1, b.2))
        (fun _ => u) σ) (readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b (τ₀ • v) W)) =
      readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b ((σ 0 * κ + τ₀) • v) W) := by
  funext z i
  simp only [rotatedField, bondSpread, readAtLevel_torusFrame, multiplyAtBond]
  by_cases h : (siteOfCell z, i) = b
  · have hz : (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top b.1, b.2) = (z, i) := by
      subst h
      simp [torusSiteInFrame_siteOfCell]
    simp only [Finset.univ_unique, Finset.sum_singleton, hz, if_true, h]
    rw [← mul_assoc, hu, smul_smul]
    have : (default : Fin 1) = 0 := rfl
    rw [this, expUnit_smul_mul]
  · have hz : (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top b.1, b.2) ≠ (z, i) := by
      intro e
      apply h
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only at e1 e2
      rw [← e1, siteOfCell_torusSiteInFrame, ← e2]
    simp [hz, h, expUnit_zero]
theorem levelShare_succ_multiplyAtBond_sub_le (hch : ColdChainConstants a δ L lam ρ σA cg N) (t m : ℕ) [NeZero m]
    (X : Finset (TorusSite m)) (W : TorusField m) (b : TorusBond m) (v : imaginaryQuaternions) (y : TorusSite m)
    (s : ℝ) (hm : 64 ≤ m) (hs : 0 < s) (hsσ : s ≤ σA) (hX : IsLocallyOrthantClosed X 1024)
    (hc : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → IsColdOn X s (multiplyAtBond b (τ • v) W)) :
    |levelShare a L (t + 1) X y (multiplyAtBond b v W) - levelShare a L (t + 1) X y W| ≤
      N 1 * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) := by
  obtain ⟨hδ, -, -, -, -, hσ, -, hN, main⟩ := hch
  by_cases hv : (v : ℍ[ℝ]) = 0
  · have h0 : v = 0 := Subtype.ext hv
    have : multiplyAtBond b v W = W := by
      funext z i
      simp [multiplyAtBond, h0, expUnit_zero]
    rw [this, hv]
    simp
  have hnv : 0 < ‖(v : ℍ[ℝ])‖ := norm_pos_iff.mpr hv
  set κ : ℝ := ‖(v : ℍ[ℝ])‖⁻¹ with hκ
  set u : imaginaryQuaternions := κ • v with hu
  have hun : ‖u‖ = 1 := by
    have : ‖u‖ = ‖(u : ℍ[ℝ])‖ := rfl
    rw [this, hu, Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnv)]
    exact inv_mul_cancel₀ hnv.ne'
  set Yc := torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y with hYc
  set S := cellsOfSites (torusFrame L t m) X with hS
  set c : Fin 1 → (torusFrame L t m).Cell × Fin 4 :=
    fun _ => (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top b.1, b.2) with hcdef
  set f : ℝ → ℝ := fun τ => minimalCellShare a S Yc
    (readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b (τ • v) W)) with hf
  have key : ∀ τ₀ : ℝ, 0 ≤ τ₀ → τ₀ ≤ 1 → ∃ f' : ℝ, HasDerivAt f f' τ₀ ∧
      |f'| ≤ N 1 * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) := by
    intro τ₀ h0 h1
    have hA := (main (torusFrame L t m) 1024 S rfl (isAdmissibleAmbient_torusFrame hm) le_rfl
      (isOrthantRegular_torusFrame hX) s
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b (τ₀ • v) W)) hs hsσ
      (isCold_torusFrame (hc τ₀ h0 h1)))
    obtain ⟨-, -, h3, -, -, -⟩ := hA
    obtain ⟨-, han, -, -, -, -, hder, -, -⟩ := h3
    set g : (Fin 1 → ℝ) → ℝ := fun σ => minimalCellShare a S Yc (rotatedField (bondSpread c (fun _ => u) σ)
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b (τ₀ • v) W))) with hg
    have hga : AnalyticAt ℝ g 0 := han Yc 1 c (fun _ => u)
    have hgd := hga.differentiableAt.hasFDerivAt
    have hfg : ∀ τ : ℝ, f τ = g (fun _ => (τ - τ₀) * ‖(v : ℍ[ℝ])‖) := by
      intro τ
      simp only [hf, hg, hcdef]
      rw [rotatedField_readAtLevel a t m W b v u κ τ₀ hu]
      congr 3
      have : (τ - τ₀) * ‖(v : ℍ[ℝ])‖ * κ = τ - τ₀ := by
        rw [hκ, mul_assoc, mul_inv_cancel₀ hnv.ne', mul_one]
      rw [this]
      simp
    have hφ : HasDerivAt (fun τ : ℝ => (fun _ : Fin 1 => (τ - τ₀) * ‖(v : ℍ[ℝ])‖))
        (fun _ : Fin 1 => ‖(v : ℍ[ℝ])‖) τ₀ := by
      rw [hasDerivAt_pi]
      intro _
      have := ((hasDerivAt_id τ₀).sub_const τ₀).mul_const ‖(v : ℍ[ℝ])‖
      simpa using this
    have hφ0 : (fun _ : Fin 1 => (τ₀ - τ₀) * ‖(v : ℍ[ℝ])‖) = 0 := by
      funext _
      simp
    have hcomp : HasDerivAt f (fderiv ℝ g 0 (fun _ : Fin 1 => ‖(v : ℍ[ℝ])‖)) τ₀ := by
      have h2 : HasFDerivAt g (fderiv ℝ g 0)
          ((fun τ : ℝ => (fun _ : Fin 1 => (τ - τ₀) * ‖(v : ℍ[ℝ])‖)) τ₀) := by
        simp only [hφ0]
        exact hgd
      have := h2.comp_hasDerivAt τ₀ hφ
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
      exact hfg τ
    refine ⟨_, hcomp, ?_⟩
    have hmd := hder Yc 1 c (fun _ => u) le_rfl (fun _ => hun)
    have e1 : mixedBondDerivative (minimalCellShare a S Yc)
        (readAtLevel (torusFrame L t m) (torusFrame L t m).top (multiplyAtBond b (τ₀ • v) W)) c (fun _ => u) =
        fderiv ℝ g 0 (Pi.single 0 1) := by
      unfold mixedBondDerivative
      rw [iteratedFDeriv_one_apply]
    have e2 : (fun _ : Fin 1 => ‖(v : ℍ[ℝ])‖) = ‖(v : ℍ[ℝ])‖ • (Pi.single 0 1 : Fin 1 → ℝ) := by
      funext l
      have : l = 0 := Subsingleton.elim _ _
      subst this
      simp
    have e3 : bondListDistance Yc c = _root_.YangMills.Construction.TorusFields.supDist y b.1 := by
      simp only [bondListDistance, hcdef, Finset.univ_unique, Finset.sup_singleton, hYc]
      rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
    rw [e1, e3, neg_mul] at hmd
    rw [e2, map_smul, smul_eq_mul, abs_mul, abs_of_pos hnv]
    calc ‖(v : ℍ[ℝ])‖ * |fderiv ℝ g 0 (Pi.single 0 1)| ≤
          ‖(v : ℍ[ℝ])‖ * (N 1 * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1))) :=
          mul_le_mul_of_nonneg_left hmd hnv.le
      _ = _ := by ring
  choose! f' hf' hb using key
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f) (f' := f')
    (C := N 1 * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)))
    (fun x hx => (hf' x hx.1 hx.2).hasDerivWithinAt)
    (fun x hx => by simpa using hb x hx.1 hx.2.le)
  have e1 : f 1 = levelShare a L (t + 1) X y (multiplyAtBond b v W) := by
    simp only [hf, one_smul]
    rfl
  have e0 : f 0 = levelShare a L (t + 1) X y W := by
    have : multiplyAtBond b ((0 : ℝ) • v) W = W := by
      funext z i
      simp [multiplyAtBond, expUnit_zero]
    simp only [hf, this]
    rfl
  rw [e1, e0] at hmvt
  simpa using hmvt
end SuccessorLevel
section LevelZero
variable {m : ℕ} [NeZero m]
open Classical in
def plaquetteQuarter (X : Finset (TorusSite m)) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) : ℝ :=
  if ((x, μ, ν) : TorusPlaquette m) ∈ plaquettesIn X then plaquetteEnergy W x μ ν / 4 else 0
theorem sum_indicator_add_eq (y c : TorusSite m) (G : TorusSite m → ℝ) :
    ∑ x : TorusSite m, (if x + c = y then (1 : ℝ) else 0) * G x = G (y - c) := by
  rw [Finset.sum_eq_single (y - c)]
  · simp
  · intro x _ hx
    have : x + c ≠ y := fun h => hx (by rw [← h]; abel)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem count_plaquetteVertices (x y : TorusSite m) (μ ν : Fin 4) :
    (((plaquetteVertices x μ ν).count y : ℕ) : ℝ) =
      (if x + 0 = y then (1 : ℝ) else 0) + (if x + TorusFields.unitStep m μ = y then (1 : ℝ) else 0) +
        (if x + TorusFields.unitStep m ν = y then (1 : ℝ) else 0) +
        (if x + (TorusFields.unitStep m μ + TorusFields.unitStep m ν) = y then (1 : ℝ) else 0) := by
  simp only [plaquetteVertices, List.count_cons, List.count_nil, add_zero, beq_iff_eq, ← add_assoc]
  split_ifs <;> simp_all <;> norm_num
theorem levelShare_zero_eq (a : ℝ) (L : ℕ) (X : Finset (TorusSite m)) (y : TorusSite m) (W : TorusField m) :
    levelShare a L 0 X y W = ∑ μ, ∑ ν, (plaquetteQuarter X W (y - 0) μ ν +
      plaquetteQuarter X W (y - TorusFields.unitStep m μ) μ ν +
      plaquetteQuarter X W (y - TorusFields.unitStep m ν) μ ν +
      plaquetteQuarter X W (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν) := by
  classical
  have h1 : levelShare a L 0 X y W = ∑ p : TorusPlaquette m,
      (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) * plaquetteQuarter X W p.1 p.2.1 p.2.2 := by
    show ∑ p ∈ plaquettesIn X, _ = _
    rw [← Finset.sum_subset (Finset.subset_univ (plaquettesIn X))]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have : ((p.1, p.2.1, p.2.2) : TorusPlaquette m) ∈ plaquettesIn X := hp
      simp only [plaquetteQuarter, if_pos this]
      ring
    · intro p _ hp
      have : ((p.1, p.2.1, p.2.2) : TorusPlaquette m) ∉ plaquettesIn X := hp
      simp [plaquetteQuarter, this]
  rw [h1, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [count_plaquetteVertices, add_mul, Finset.sum_add_distrib, sum_indicator_add_eq]
theorem plaquetteQuarter_nonneg (X : Finset (TorusSite m)) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    0 ≤ plaquetteQuarter X W x μ ν := by
  unfold plaquetteQuarter
  split_ifs
  · have := plaquetteEnergy_nonneg W x μ ν
    positivity
  · exact le_rfl
theorem plaquetteQuarter_le (X : Finset (TorusSite m)) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteQuarter X W x μ ν ≤ 1 / 2 := by
  unfold plaquetteQuarter
  split_ifs
  · have := plaquetteEnergy_le_two W x μ ν
    linarith
  · norm_num
theorem levelShare_zero_bounds (a : ℝ) (L : ℕ) (X : Finset (TorusSite m)) (y : TorusSite m) (W : TorusField m) :
    0 ≤ levelShare a L 0 X y W ∧ levelShare a L 0 X y W ≤ 32 := by
  rw [levelShare_zero_eq]
  constructor
  · refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
    have := plaquetteQuarter_nonneg X W (y - 0) μ ν
    have := plaquetteQuarter_nonneg X W (y - TorusFields.unitStep m μ) μ ν
    have := plaquetteQuarter_nonneg X W (y - TorusFields.unitStep m ν) μ ν
    have := plaquetteQuarter_nonneg X W (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν
    linarith
  · have h : ∀ μ ν : Fin 4, plaquetteQuarter X W (y - 0) μ ν +
        plaquetteQuarter X W (y - TorusFields.unitStep m μ) μ ν +
        plaquetteQuarter X W (y - TorusFields.unitStep m ν) μ ν +
        plaquetteQuarter X W (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν ≤ 2 := by
      intro μ ν
      have := plaquetteQuarter_le X W (y - 0) μ ν
      have := plaquetteQuarter_le X W (y - TorusFields.unitStep m μ) μ ν
      have := plaquetteQuarter_le X W (y - TorusFields.unitStep m ν) μ ν
      have := plaquetteQuarter_le X W (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν
      linarith
    calc _ ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, (2 : ℝ) :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => h μ ν
      _ = 32 := by simp; norm_num
theorem plaquetteQuarter_eq_of_agree {X X' : Finset (TorusSite m)} {W W' : TorusField m} {y : TorusSite m} {r : ℕ}
    (hr : 1 ≤ r) (hag : RegionsAgreeNear X X' W W' y r) (a : Fin 4 → ℤ) (μ ν : Fin 4)
    (ha : μ < ν → ∀ d ∈ plaquetteOffsets μ ν, TorusFields.OffsetInBox 1 (a + d)) :
    plaquetteQuarter X W (y + siteOfInt a) μ ν = plaquetteQuarter X' W' (y + siteOfInt a) μ ν := by
  classical
  obtain ⟨-, hm, hf⟩ := hag
  by_cases hμν : μ < ν
  · have hbox : ∀ d ∈ plaquetteOffsets μ ν, TorusFields.OffsetInBox r (a + d) := fun d hd i =>
      (ha hμν d hd i).trans (by exact_mod_cast hr)
    have hmem : ((y + siteOfInt a, μ, ν) : TorusPlaquette m) ∈ plaquettesIn X ↔
        ((y + siteOfInt a, μ, ν) : TorusPlaquette m) ∈ plaquettesIn X' := by
      rw [mem_plaquettesIn_iff_forall_vertex, mem_plaquettesIn_iff_forall_vertex]
      refine and_congr_right fun _ => forall₂_congr fun z hz => ?_
      obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hz
      have e : y + siteOfInt a + siteOfInt d = y + siteOfInt (a + d) := by rw [siteOfInt_add, add_assoc]
      show y + siteOfInt a + siteOfInt d ∈ X ↔ y + siteOfInt a + siteOfInt d ∈ X'
      rw [e]
      exact hm _ (hbox d hd)
    have m0 : (0 : Fin 4 → ℤ) ∈ plaquetteOffsets μ ν := by simp [plaquetteOffsets]
    have m1 : (Pi.single μ 1 : Fin 4 → ℤ) ∈ plaquetteOffsets μ ν := by simp [plaquetteOffsets]
    have m2 : (Pi.single ν 1 : Fin 4 → ℤ) ∈ plaquetteOffsets μ ν := by simp [plaquetteOffsets]
    have m3 : (Pi.single μ 1 + Pi.single ν 1 : Fin 4 → ℤ) ∈ plaquetteOffsets μ ν := by simp [plaquetteOffsets]
    have b0 := hbox 0 m0
    have b1 := hbox _ m1
    have b2 := hbox _ m2
    have b3 := hbox _ m3
    rw [add_zero] at b0
    have e1 : y + siteOfInt a + TorusFields.unitStep m μ = y + siteOfInt (a + Pi.single μ 1) := by
      rw [siteOfInt_add, add_assoc, unitStep_eq_siteOfInt]
    have e2 : y + siteOfInt a + TorusFields.unitStep m ν = y + siteOfInt (a + Pi.single ν 1) := by
      rw [siteOfInt_add, add_assoc, unitStep_eq_siteOfInt]
    have f1 : W (y + siteOfInt a) μ = W' (y + siteOfInt a) μ := hf (a, μ) ⟨b0, b1⟩
    have f2 : W (y + siteOfInt (a + Pi.single μ 1)) ν = W' (y + siteOfInt (a + Pi.single μ 1)) ν :=
      hf (a + Pi.single μ 1, ν) ⟨b1, by rw [add_assoc]; exact b3⟩
    have f3 : W (y + siteOfInt (a + Pi.single ν 1)) μ = W' (y + siteOfInt (a + Pi.single ν 1)) μ :=
      hf (a + Pi.single ν 1, μ) ⟨b2, by rw [add_assoc, add_comm (Pi.single ν 1 : Fin 4 → ℤ)]; exact b3⟩
    have f4 : W (y + siteOfInt a) ν = W' (y + siteOfInt a) ν := hf (a, ν) ⟨b0, b2⟩
    have hE : plaquetteEnergy W (y + siteOfInt a) μ ν = plaquetteEnergy W' (y + siteOfInt a) μ ν := by
      unfold plaquetteEnergy holonomy
      rw [e1, e2, f1, f2, f3, f4]
    unfold plaquetteQuarter
    simp only [hmem, hE]
  · have h1 : ((y + siteOfInt a, μ, ν) : TorusPlaquette m) ∉ plaquettesIn X :=
      fun h => hμν (mem_plaquettesIn_iff_forall_vertex.mp h).1
    have h2 : ((y + siteOfInt a, μ, ν) : TorusPlaquette m) ∉ plaquettesIn X' :=
      fun h => hμν (mem_plaquettesIn_iff_forall_vertex.mp h).1
    simp [plaquetteQuarter, h1, h2]
theorem offsetInBox_one_add {μ ν : Fin 4} (hμν : μ < ν) {a d : Fin 4 → ℤ}
    (ha : a = 0 ∨ a = -Pi.single μ 1 ∨ a = -Pi.single ν 1 ∨ a = -(Pi.single μ 1 + Pi.single ν 1))
    (hd : d ∈ plaquetteOffsets μ ν) : TorusFields.OffsetInBox 1 (a + d) := by
  have hne : μ ≠ ν := hμν.ne
  intro i
  simp only [plaquetteOffsets, List.mem_cons, List.not_mem_nil, or_false] at hd
  by_cases h1 : i = μ
  · subst h1
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
      simp [Pi.single_apply, hne]
  · by_cases h2 : i = ν
    · subst h2
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
        simp [Pi.single_apply, h1]
    · rcases ha with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
        simp [Pi.single_apply, h1, h2]
theorem levelShare_zero_eq_of_agree {X X' : Finset (TorusSite m)} {W W' : TorusField m} {y : TorusSite m} {r : ℕ}
    (a : ℝ) (L : ℕ) (hr : 1 ≤ r) (hag : RegionsAgreeNear X X' W W' y r) :
    levelShare a L 0 X y W = levelShare a L 0 X' y W' := by
  rw [levelShare_zero_eq, levelShare_zero_eq]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  have k : ∀ a' : Fin 4 → ℤ, (a' = 0 ∨ a' = -Pi.single μ 1 ∨ a' = -Pi.single ν 1 ∨
      a' = -(Pi.single μ 1 + Pi.single ν 1)) →
      plaquetteQuarter X W (y + siteOfInt a') μ ν = plaquetteQuarter X' W' (y + siteOfInt a') μ ν := fun a' ha' =>
    plaquetteQuarter_eq_of_agree hr hag a' μ ν fun h d hd => offsetInBox_one_add h ha' hd
  have e0 : y - 0 = y + siteOfInt (0 : Fin 4 → ℤ) := by rw [siteOfInt_zero_offset]; simp
  have e1 : y - TorusFields.unitStep m μ = y + siteOfInt (-Pi.single μ 1) := by
    rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt]
  have e2 : y - TorusFields.unitStep m ν = y + siteOfInt (-Pi.single ν 1) := by
    rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt]
  have e3 : y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν) =
      y + siteOfInt (-(Pi.single μ 1 + Pi.single ν 1)) := by
    rw [unitStep_eq_siteOfInt, unitStep_eq_siteOfInt, sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt, add_comm]
  rw [e0, e1, e2, e3, k _ (Or.inl rfl), k _ (Or.inr (Or.inl rfl)), k _ (Or.inr (Or.inr (Or.inl rfl))),
    k _ (Or.inr (Or.inr (Or.inr rfl)))]
theorem norm_multiplyAtBond_sub_le (b : TorusBond m) (v : imaginaryQuaternions) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    ‖(multiplyAtBond b v W x i : ℍ[ℝ]) - W x i‖ ≤ ‖(v : ℍ[ℝ])‖ := by
  unfold multiplyAtBond
  split_ifs
  · have e : ((expUnit v * W x i : UnitQuaternion) : ℍ[ℝ]) - W x i =
        (((expUnit v : UnitQuaternion) : ℍ[ℝ]) - 1) * W x i := by
      show ((expUnit v : UnitQuaternion) : ℍ[ℝ]) * W x i - W x i = _
      noncomm_ring
    rw [e, norm_mul, norm_unitQuaternion, mul_one]
    exact norm_expUnit_sub_one_le v
  · simp
theorem abs_plaquetteQuarter_multiplyAtBond_sub_le (X : Finset (TorusSite m)) (b : TorusBond m)
    (v : imaginaryQuaternions) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    |plaquetteQuarter X (multiplyAtBond b v W) x μ ν - plaquetteQuarter X W x μ ν| ≤ ‖(v : ℍ[ℝ])‖ := by
  classical
  unfold plaquetteQuarter
  split_ifs
  · have h := abs_plaquetteEnergy_sub_le (multiplyAtBond b v W) W x μ ν
    have h1 := norm_multiplyAtBond_sub_le b v W x μ
    have h2 := norm_multiplyAtBond_sub_le b v W (x + TorusFields.unitStep m μ) ν
    have h3 := norm_multiplyAtBond_sub_le b v W (x + TorusFields.unitStep m ν) μ
    have h4 := norm_multiplyAtBond_sub_le b v W x ν
    have e : plaquetteEnergy (multiplyAtBond b v W) x μ ν / 4 - plaquetteEnergy W x μ ν / 4 =
        (plaquetteEnergy (multiplyAtBond b v W) x μ ν - plaquetteEnergy W x μ ν) / 4 := by ring
    rw [e, abs_div]
    norm_num
    linarith
  · simp
theorem plaquetteQuarter_multiplyAtBond_of_ne (X : Finset (TorusSite m)) (b : TorusBond m)
    (v : imaginaryQuaternions) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4)
    (h1 : (x, μ) ≠ b) (h2 : (x + TorusFields.unitStep m μ, ν) ≠ b) (h3 : (x + TorusFields.unitStep m ν, μ) ≠ b)
    (h4 : (x, ν) ≠ b) :
    plaquetteQuarter X (multiplyAtBond b v W) x μ ν = plaquetteQuarter X W x μ ν := by
  unfold plaquetteQuarter plaquetteEnergy holonomy multiplyAtBond
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
theorem bonds_ne_of_supDist_le {y x : TorusSite m} (h : _root_.YangMills.Construction.TorusFields.supDist y x ≤ 2) {b : TorusBond m}
    (hd : 3 < _root_.YangMills.Construction.TorusFields.supDist y b.1) (μ ν : Fin 4) :
    (x, μ) ≠ b ∧ (x + TorusFields.unitStep m μ, ν) ≠ b ∧ (x + TorusFields.unitStep m ν, μ) ≠ b ∧ (x, ν) ≠ b := by
  have k : ∀ z : TorusSite m, _root_.YangMills.Construction.TorusFields.supDist y z ≤ 3 → ∀ i : Fin 4, (z, i) ≠ b := by
    rintro z hz i rfl
    simp only at hd
    omega
  exact ⟨k _ (by omega) _,
    k _ ((_root_.YangMills.Construction.TorusFields.supDist_triangle y x _).trans (by have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x μ; omega)) _,
    k _ ((_root_.YangMills.Construction.TorusFields.supDist_triangle y x _).trans (by have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x ν; omega)) _, k _ (by omega) _⟩
theorem supDist_sub_corners_le (y : TorusSite m) (μ ν : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist y (y - 0) ≤ 2 ∧ _root_.YangMills.Construction.TorusFields.supDist y (y - TorusFields.unitStep m μ) ≤ 2 ∧
      _root_.YangMills.Construction.TorusFields.supDist y (y - TorusFields.unitStep m ν) ≤ 2 ∧
      _root_.YangMills.Construction.TorusFields.supDist y (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) ≤ 2 := by
  have k1 : ∀ i, _root_.YangMills.Construction.TorusFields.supDist y (y - TorusFields.unitStep m i) ≤ 1 := by
    intro i
    have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (y - TorusFields.unitStep m i) i
    rw [sub_add_cancel, _root_.YangMills.Construction.TorusFields.supDist_comm] at this
    exact this
  refine ⟨by simp [_root_.YangMills.Construction.TorusFields.supDist_self], (k1 μ).trans (by norm_num), (k1 ν).trans (by norm_num), ?_⟩
  have h := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ
  have e : y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν) + TorusFields.unitStep m μ =
      y - TorusFields.unitStep m ν := by abel
  rw [e, _root_.YangMills.Construction.TorusFields.supDist_comm] at h
  have := k1 ν
  exact (_root_.YangMills.Construction.TorusFields.supDist_triangle y (y - TorusFields.unitStep m ν) _).trans (by omega)
theorem abs_levelShare_zero_multiplyAtBond_sub_le (a : ℝ) (L : ℕ) (X : Finset (TorusSite m)) (W : TorusField m)
    (b : TorusBond m) (v : imaginaryQuaternions) (y : TorusSite m) {δ : ℝ} (hδ : 0 < δ) :
    |levelShare a L 0 X y (multiplyAtBond b v W) - levelShare a L 0 X y W| ≤
      64 * Real.exp (3 * δ) * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) := by
  by_cases hd : 3 < _root_.YangMills.Construction.TorusFields.supDist y b.1
  · have : levelShare a L 0 X y (multiplyAtBond b v W) = levelShare a L 0 X y W := by
      rw [levelShare_zero_eq, levelShare_zero_eq]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      obtain ⟨n0, n1, n2, n3⟩ := _root_.YangMills.Construction.RegionShares.supDist_sub_corners_le y μ ν
      have k : ∀ x, _root_.YangMills.Construction.TorusFields.supDist y x ≤ 2 →
          plaquetteQuarter X (multiplyAtBond b v W) x μ ν = plaquetteQuarter X W x μ ν := fun x hx => by
        obtain ⟨p1, p2, p3, p4⟩ := bonds_ne_of_supDist_le hx hd μ ν
        exact plaquetteQuarter_multiplyAtBond_of_ne X b v W x μ ν p1 p2 p3 p4
      rw [k _ n0, k _ n1, k _ n2, k _ n3]
    rw [this]
    simp only [sub_self, abs_zero]
    positivity
  · have h1 : |levelShare a L 0 X y (multiplyAtBond b v W) - levelShare a L 0 X y W| ≤ 64 * ‖(v : ℍ[ℝ])‖ := by
      rw [levelShare_zero_eq, levelShare_zero_eq, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have k : ∀ μ ν : Fin 4, |(plaquetteQuarter X (multiplyAtBond b v W) (y - 0) μ ν +
          plaquetteQuarter X (multiplyAtBond b v W) (y - TorusFields.unitStep m μ) μ ν +
          plaquetteQuarter X (multiplyAtBond b v W) (y - TorusFields.unitStep m ν) μ ν +
          plaquetteQuarter X (multiplyAtBond b v W)
            (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν) -
          (plaquetteQuarter X W (y - 0) μ ν + plaquetteQuarter X W (y - TorusFields.unitStep m μ) μ ν +
          plaquetteQuarter X W (y - TorusFields.unitStep m ν) μ ν +
          plaquetteQuarter X W (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν)| ≤
          4 * ‖(v : ℍ[ℝ])‖ := by
        intro μ ν
        have a0 := abs_le.mp (abs_plaquetteQuarter_multiplyAtBond_sub_le X b v W (y - 0) μ ν)
        have a1 := abs_le.mp (abs_plaquetteQuarter_multiplyAtBond_sub_le X b v W
          (y - TorusFields.unitStep m μ) μ ν)
        have a2 := abs_le.mp (abs_plaquetteQuarter_multiplyAtBond_sub_le X b v W
          (y - TorusFields.unitStep m ν) μ ν)
        have a3 := abs_le.mp (abs_plaquetteQuarter_multiplyAtBond_sub_le X b v W
          (y - (TorusFields.unitStep m μ + TorusFields.unitStep m ν)) μ ν)
        rw [abs_le]
        constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
      calc _ ≤ ∑ _μ : Fin 4, 16 * ‖(v : ℍ[ℝ])‖ := by
            refine Finset.sum_le_sum fun μ _ => ?_
            rw [← Finset.sum_sub_distrib]
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc _ ≤ ∑ _ν : Fin 4, 4 * ‖(v : ℍ[ℝ])‖ := Finset.sum_le_sum fun ν _ => k μ ν
              _ = 16 * ‖(v : ℍ[ℝ])‖ := by simp; ring
        _ = 64 * ‖(v : ℍ[ℝ])‖ := by simp; ring
    refine h1.trans ?_
    have hd' : (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) ≤ 3 := by exact_mod_cast not_lt.mp hd
    have he : 1 ≤ Real.exp (3 * δ) * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hv := norm_nonneg (v : ℍ[ℝ])
    have : 64 * ‖(v : ℍ[ℝ])‖ * 1 ≤
        64 * ‖(v : ℍ[ℝ])‖ * (Real.exp (3 * δ) * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    nlinarith
end LevelZero
end RegionShares
namespace TorusShares
open BlockAverages TorusFields TorusLumps StepCosts ColdChain RegionShares
theorem shareLocalityExists_holds : ShareLocalityExists := by
  intro a δ L lam ρ σA cg N ha hL hch
  have hδ : 0 < δ := hch.1
  have hσ : 0 < σA := hch.2.2.2.2.2.1
  have hN : ∀ k, 0 < N k := hch.2.2.2.2.2.2.2.1
  have e3 := Real.exp_pos (3 * δ)
  have hN0 := hN 0
  have hN1 := hN 1
  have hsq : 0 < σA ^ 2 * N 0 := by positivity
  refine ⟨32 + 64 * Real.exp (3 * δ) + σA ^ 2 * N 0 + N 1, by positivity, ?_, ?_⟩
  · intro t m _ X X' W W' y r s hm hs hsσ hX hX' hc hc' hag
    have hb : 0 < Real.exp (-(δ * r)) := Real.exp_pos _
    cases t with
    | zero =>
      by_cases hr : 1 ≤ r
      · rw [levelShare_zero_eq_of_agree a L hr hag]
        simp only [sub_self, abs_zero]
        positivity
      · have hr0 : r = 0 := by omega
        subst hr0
        obtain ⟨p1, p2⟩ := levelShare_zero_bounds a L X y W
        obtain ⟨q1, q2⟩ := levelShare_zero_bounds a L X' y W'
        have : |levelShare a L 0 X y W - levelShare a L 0 X' y W'| ≤ 32 := by
          rw [abs_le]
          constructor <;> linarith
        refine this.trans ?_
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        linarith
    | succ t =>
      refine (levelShare_succ_sub_le hch t m X X' W W' y r s hm hs hsσ hX hX' hc hc' hag).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hb.le
  · intro t m _ X W b v y s hm hs hsσ hX hc
    have hb : 0 < Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) := Real.exp_pos _
    have hv := norm_nonneg (v : ℍ[ℝ])
    cases t with
    | zero =>
      refine (abs_levelShare_zero_multiplyAtBond_sub_le a L X W b v y hδ).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hv) hb.le
      linarith
    | succ t =>
      refine (levelShare_succ_multiplyAtBond_sub_le hch t m X W b v y s hm hs hsσ hX hc).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hv) hb.le
      linarith
end TorusShares
end YangMills.Construction
end
