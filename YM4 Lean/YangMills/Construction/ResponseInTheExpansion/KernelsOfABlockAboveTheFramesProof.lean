import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import YangMills.Construction.ResponseInTheExpansion.KernelsOfABlockAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.KernelsOfAShare
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
section calculus
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
private theorem exists_isOpen_contDiffOn {f : E₁ → E₂} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
private theorem iteratedFDeriv_comp_eq_sum {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    {g : E₂ → E₃} {β : E₁ → E₂} {x : E₁} {n : ℕ} (hg : ContDiffAt ℝ n g (β x))
    (hβ : ContDiffAt ℝ n β x) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ β) x v = ∑ c : OrderedFinpartition n,
      iteratedFDeriv ℝ c.length g (β x)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x) v) := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_comp_eq_sum_orderedFinpartition <;> assumption
private theorem iteratedFDeriv_comp_clm {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_isOpen_contDiffOn hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
private theorem iteratedFDeriv_affine_of_two_le (L : E₁ →L[ℝ] E₂) (v₀ : E₂) {r : ℕ} (hr : 2 ≤ r)
    (x : E₁) : iteratedFDeriv ℝ r (fun τ => v₀ + L τ) x = 0 := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_const_add_clm_of_two_le <;> assumption
private theorem iteratedFDeriv_affine_one (L : E₁ →L[ℝ] E₂) (v₀ : E₂) (x : E₁)
    (v : Fin 1 → E₁) : iteratedFDeriv ℝ 1 (fun τ => v₀ + L τ) x v = L (v 0) := by
  rw [iteratedFDeriv_one_apply, ((L.hasFDerivAt).const_add v₀).fderiv]
private theorem multilinear_eq_sum_basis {k N : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) ℝ) (v : Fin k → Fin N → ℝ) :
    M v = ∑ n ∈ Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin N)),
      (∏ m, v m (n m)) * M fun m => Pi.single (n m) 1 := by apply _root_.YangMills.SharedProofs.p22319 <;> assumption
private def reindexMap {j r : ℕ} (q : Fin r → Fin j) : (Fin r → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin r → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (q l) 1)
private theorem reindexMap_apply {j r : ℕ} (q : Fin r → Fin j) (τ : Fin r → ℝ) :
    reindexMap q τ = ∑ l, τ l • (Pi.single (q l) 1 : Fin j → ℝ) := by
  simp [reindexMap]
private theorem reindexMap_single {j r : ℕ} (q : Fin r → Fin j) (l : Fin r) :
    reindexMap q (Pi.single l 1) = Pi.single (q l) 1 := by
  rw [reindexMap_apply]
  simp [Pi.single_apply]
private theorem sum_reindexMap_smul {E : Type*} [AddCommMonoid E] [Module ℝ E] {j r : ℕ}
    (q : Fin r → Fin j) (τ : Fin r → ℝ) (g : Fin j → E) :
    ∑ p, reindexMap q τ p • g p = ∑ l, τ l • g (q l) := by
  simp only [reindexMap_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Pi.single_apply, ite_smul]
end calculus
section sums
variable {ι : Type*}
private theorem sum_over_slot_cells_le (d : ι → ι → ℕ) (hz : ∀ x, d x x = 0)
    (hsym : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (Y : ι) {N p : ℕ} (cl : Fin N → ι) (pc : Fin p → ι)
    (P : Finset ι) (hP : ∀ u ∈ P, u = Y ∨ ∃ i, pc i = u) (c : OrderedFinpartition p)
    (v : Fin c.length → Fin N → ℝ) (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q) {R r₀ r₁ Cs : ℝ}
    (hr₀ : 0 ≤ r₀) (h1 : 2 * r₀ ≤ r₁) (h2 : 4 * r₀ ≤ R)
    (hv : ∀ (m : Fin c.length) (n : Fin N) (q : Fin (c.partSize m)),
      |v m n| ≤ M (c.partSize m) * Real.exp (-(R * d (cl n) (pc (c.emb m q)))))
    (hs : ∀ z, ∑ n, Real.exp (-(R / 2 * d (cl n) z)) ≤ Cs) :
    ∑ n ∈ Fintype.piFinset fun _ : Fin c.length => (Finset.univ : Finset (Fin N)),
        (∏ m, |v m (n m)|) * Real.exp (-(r₁ * (Finset.univ.sup fun m : Fin c.length =>
          d Y (cl (n m)) : ℕ))) ≤
      (∏ m, M (c.partSize m)) * Cs ^ c.length *
        Real.exp (-(r₀ * (P.sup fun u => P.sup fun u' => d u u' : ℕ))) := by
  classical
  set D : ℕ := P.sup fun u => P.sup fun u' => d u u' with hD
  let l₀ : ∀ m : Fin c.length, Fin (c.partSize m) := fun m => ⟨0, c.partSize_pos m⟩
  let g : Fin c.length → Fin N → ℝ := fun m n =>
    Real.exp (-(R / 2 * d (cl n) (pc (c.emb m (l₀ m)))))
  have hg0 : ∀ m n, 0 ≤ g m n := fun m n => (Real.exp_pos _).le
  have hMp : 0 ≤ ∏ m, M (c.partSize m) := Finset.prod_nonneg fun m _ => hM _
  have hpt : ∀ n : Fin c.length → Fin N,
      (∏ m, |v m (n m)|) * Real.exp (-(r₁ * (Finset.univ.sup fun m : Fin c.length =>
          d Y (cl (n m)) : ℕ))) ≤
        ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * ∏ m, g m (n m) := by
    intro n
    set Δ : ℕ := Finset.univ.sup fun m : Fin c.length => d Y (cl (n m)) with hΔ
    let E : Fin c.length → ℕ := fun m => Finset.univ.sup fun q : Fin (c.partSize m) =>
      d (cl (n m)) (pc (c.emb m q))
    have hslot : ∀ m, |v m (n m)| ≤ M (c.partSize m) * Real.exp (-(R / 2 * E m)) * g m (n m) := by
      intro m
      have hne : (Finset.univ : Finset (Fin (c.partSize m))).Nonempty := ⟨l₀ m, Finset.mem_univ _⟩
      obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup Finset.univ hne
        (fun q : Fin (c.partSize m) => d (cl (n m)) (pc (c.emb m q)))
      have hEq : (E m : ℝ) = d (cl (n m)) (pc (c.emb m q)) := by
        simp only [E]
        rw [hq]
      refine (hv m (n m) q).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hM _)
      simp only [g]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [← hEq]
      have h3 : ((d (cl (n m)) (pc (c.emb m (l₀ m))) : ℕ) : ℝ) ≤ E m := by
        have : d (cl (n m)) (pc (c.emb m (l₀ m))) ≤ E m :=
          Finset.le_sup (f := fun q : Fin (c.partSize m) => d (cl (n m)) (pc (c.emb m q)))
            (Finset.mem_univ (l₀ m))
        exact_mod_cast this
      nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ R / 2)]
    have hEle : ∀ m, E m ≤ ∑ m', E m' := fun m =>
      Finset.single_le_sum (f := E) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have hpar : ∀ i, d Y (pc i) ≤ Δ + ∑ m', E m' := by
      intro i
      have hl : c.emb (c.index i) (c.invEmbedding i) = i := c.emb_invEmbedding i
      have h3 : d (cl (n (c.index i))) (pc i) ≤ E (c.index i) := by
        have := Finset.le_sup (f := fun q : Fin (c.partSize (c.index i)) =>
          d (cl (n (c.index i))) (pc (c.emb (c.index i) q))) (Finset.mem_univ (c.invEmbedding i))
        simpa [hl] using this
      have h4 : d Y (cl (n (c.index i))) ≤ Δ :=
        Finset.le_sup (f := fun m : Fin c.length => d Y (cl (n m))) (Finset.mem_univ (c.index i))
      have h5 := htri Y (cl (n (c.index i))) (pc i)
      have h6 := hEle (c.index i)
      omega
    have hfar : ∀ u ∈ P, d Y u ≤ Δ + ∑ m', E m' := by
      intro u hu
      rcases hP u hu with rfl | ⟨i, rfl⟩
      · rw [hz]
        exact Nat.zero_le _
      · exact hpar i
    have hDle : D ≤ 2 * Δ + 2 * ∑ m', E m' := by
      simp only [hD]
      refine Finset.sup_le fun u hu => Finset.sup_le fun u' hu' => ?_
      have h3 := htri u Y u'
      have h4 := hfar u hu
      have h5 := hfar u' hu'
      rw [hsym u Y] at h3
      omega
    have hDr : (D : ℝ) ≤ 2 * Δ + 2 * ∑ m', (E m' : ℝ) := by
      have : ((D : ℕ) : ℝ) ≤ ((2 * Δ + 2 * ∑ m', E m' : ℕ) : ℝ) := by exact_mod_cast hDle
      push_cast at this
      exact this
    have hsE : (0 : ℝ) ≤ ∑ m', (E m' : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    have hprod : ∏ m, |v m (n m)| ≤
        (∏ m, M (c.partSize m)) * Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * ∏ m, g m (n m) := by
      calc ∏ m, |v m (n m)| ≤
            ∏ m, (M (c.partSize m) * Real.exp (-(R / 2 * E m)) * g m (n m)) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun m _ => hslot m
        _ = _ := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            congr 2
            rw [← Real.exp_sum]
            congr 1
            rw [Finset.mul_sum, Finset.sum_neg_distrib]
    have hgp : 0 ≤ ∏ m, g m (n m) := Finset.prod_nonneg fun m _ => hg0 m _
    have hexp : Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * Real.exp (-(r₁ * Δ)) ≤
        Real.exp (-(r₀ * D)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have e1 : r₀ * D ≤ r₀ * (2 * Δ + 2 * ∑ m', (E m' : ℝ)) := mul_le_mul_of_nonneg_left hDr hr₀
      have e2 : 2 * r₀ * Δ ≤ r₁ * Δ := mul_le_mul_of_nonneg_right h1 hΔ0
      have e3 : 4 * r₀ * ∑ m', (E m' : ℝ) ≤ R * ∑ m', (E m' : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hsE
      nlinarith
    calc (∏ m, |v m (n m)|) * Real.exp (-(r₁ * Δ))
        ≤ ((∏ m, M (c.partSize m)) * Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * ∏ m, g m (n m)) *
            Real.exp (-(r₁ * Δ)) :=
          mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = (∏ m, M (c.partSize m)) * (Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) *
            Real.exp (-(r₁ * Δ))) * ∏ m, g m (n m) := by ring
      _ ≤ (∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D)) * ∏ m, g m (n m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hMp) hgp
  have hsumg : ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
      ∏ m, g m (n m) ≤ Cs ^ c.length := by
    rw [← Finset.prod_univ_sum]
    calc ∏ m, ∑ n, g m n ≤ ∏ _m : Fin c.length, Cs :=
          Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun n _ => hg0 m n) fun m _ => hs _
      _ = _ := by simp
  have hpre : 0 ≤ (∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D)) :=
    mul_nonneg hMp (Real.exp_pos _).le
  calc _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
        ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * ∏ m, g m (n m) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) *
          ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
            ∏ m, g m (n m) := by rw [Finset.mul_sum]
    _ ≤ ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * Cs ^ c.length :=
        mul_le_mul_of_nonneg_left hsumg hpre
    _ = _ := by ring
end sums
section imaginaryQuaternions
private def imCoord (r : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] r
private def imBasis (r : Fin 3) : imaginaryQuaternions :=
  ![⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 1, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 0, 1⟩ : ℍ[ℝ]), rfl⟩] r
private theorem sum_imCoord_smul_imBasis (w : imaginaryQuaternions) :
    ∑ r, imCoord r w • imBasis r = w := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, imCoord, imBasis]
  apply Quaternion.ext
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    simp [hw]
  · change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    simp
private theorem imCoord_add (r : Fin 3) (w w' : imaginaryQuaternions) :
    imCoord r (w + w') = imCoord r w + imCoord r w' := by
  fin_cases r <;> simp [imCoord]
private theorem imCoord_smul (r : Fin 3) (u : ℝ) (w : imaginaryQuaternions) :
    imCoord r (u • w) = u * imCoord r w := by
  fin_cases r <;> simp [imCoord]
private theorem imaginary_ext {w w' : imaginaryQuaternions} (h : ∀ r, imCoord r w = imCoord r w') :
    w = w' := by
  rw [← sum_imCoord_smul_imBasis w, ← sum_imCoord_smul_imBasis w']
  simp only [h]
private theorem imCoord_imBasis (r r' : Fin 3) :
    imCoord r (imBasis r') = if r = r' then 1 else 0 := by
  fin_cases r <;> fin_cases r' <;> simp [imCoord, imBasis]
private theorem imCoord_toImaginary (r : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    imCoord r (toImaginary v) = v r := by
  fin_cases r <;> rfl
private theorem sq_norm_imaginary (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by apply _root_.YangMills.SharedProofs.p1745 <;> assumption
private theorem abs_imCoord_le (r : Fin 3) (w : imaginaryQuaternions) : |imCoord r w| ≤ ‖w‖ := by
  apply abs_le_of_sq_le_sq _ (norm_nonneg _)
  rw [sq_norm_imaginary]
  have h1 := sq_nonneg (w : ℍ[ℝ]).imI
  have h2 := sq_nonneg (w : ℍ[ℝ]).imJ
  have h3 := sq_nonneg (w : ℍ[ℝ]).imK
  fin_cases r <;> simp [imCoord] <;> linarith
private theorem norm_imBasis (r : Fin 3) : ‖imBasis r‖ = 1 := by
  have h : ‖imBasis r‖ ^ 2 = 1 := by
    rw [sq_norm_imaginary]
    fin_cases r <;> simp [imBasis]
  have h0 := norm_nonneg (imBasis r)
  nlinarith
private def imCoordL (r : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := imCoord r
      map_add' := imCoord_add r
      map_smul' := fun u w => by simp [imCoord_smul] } 1
    (fun w => by simpa using abs_imCoord_le r w)
private theorem imCoordL_apply (r : Fin 3) (w : imaginaryQuaternions) : imCoordL r w = imCoord r w := rfl
private theorem imCoord_sum_smul_imBasis (r : Fin 3) (t : Fin 3 → ℝ) :
    imCoord r (∑ r', t r' • imBasis r') = t r := by
  rw [← imCoordL_apply, map_sum]
  simp only [map_smul, imCoordL_apply, imCoord_imBasis, smul_eq_mul]
  simp
end imaginaryQuaternions
section spread
variable {F : BlockFrame}
private theorem bondSpread_zero {i k : ℕ} (c : Fin k → F.Site i × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ColdStepAtMirrorFrames.bondSpread c X 0 = fun _ _ => 0 := by apply _root_.YangMills.SharedProofs.p27189 <;> assumption
private theorem leftTranslate_zero {i : ℕ} (W : F.GaugeField i) : leftTranslate (fun _ _ => 0) W = W := by apply _root_.YangMills.SharedProofs.p21302 <;> assumption
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top)
    (h : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
end spread
section parameters
variable {F : BlockFrame} {l j : ℕ}
private def topProj (l j : ℕ) : (Fin (l + j) → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd l i)
private theorem topProj_single_castAdd (i : Fin l) :
    topProj l j (Pi.single (Fin.castAdd j i) 1) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501334 <;> assumption
private theorem topProj_single_natAdd (i : Fin j) :
    topProj l j (Pi.single (Fin.natAdd l i) 1) = Pi.single i 1 := by apply _root_.YangMills.DeltaSharedProofs.p501018 <;> assumption
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private theorem iteratedFDeriv_comp_topProj_eq_zero {H : (Fin j → ℝ) → E} (hH : AnalyticAt ℝ H 0)
    {q : ℕ} (J : Fin q → Fin (l + j)) (e₀ : Fin q) (i : Fin l) (he : J e₀ = Fin.castAdd j i) :
    iteratedFDeriv ℝ q (H ∘ topProj l j) 0 (fun e => Pi.single (J e) 1) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501352 <;> assumption
private theorem iteratedFDeriv_comp_topProj_eq_bondDeriv {fr : F.GaugeField F.top → E}
    {V : F.GaugeField F.top}
    {c : Fin j → F.Site F.top × Fin 4} {X : Fin j → imaginaryQuaternions}
    (hH : AnalyticAt ℝ
      (fun τ : Fin j → ℝ => fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0)
    {q : ℕ} (J : Fin q → Fin (l + j)) (J' : Fin q → Fin j) (he : ∀ e, J e = Fin.natAdd l (J' e)) :
    iteratedFDeriv ℝ q ((fun τ : Fin j → ℝ =>
        fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∘ topProj l j) 0
        (fun e => Pi.single (J e) 1) = bondDeriv fr V (c ∘ J') (X ∘ J') := by apply _root_.YangMills.DeltaSharedProofs.p501288 <;> assumption
end parameters
section coordinates
variable {F : BlockFrame} {l j : ℕ}
  (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
  (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
  (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
private abbrev SlotIndex (F : BlockFrame) (j : ℕ) : Type :=
  (↥(chordBonds (finiteCells F)) × Fin 3) ⊕ Fin j
private def indexDirection : SlotIndex F j → ChartDirection F
  | .inl p => .inl (p.1.1.1, p.1.1.2, imBasis p.2)
  | .inr i => .inr ((c i).1, (c i).2, X i)
open Classical in
private def chartShiftLin (β : ↥(chordBonds (finiteCells F))) (r : Fin 3) :
    (Fin (l + j) → ℝ) →L[ℝ] ℝ :=
  ∑ i, (if b i = β then u i r else 0) •
    (ContinuousLinearMap.proj (Fin.castAdd j i) : (Fin (l + j) → ℝ) →L[ℝ] ℝ)
private def frameAlongTop (d : F.Site F.depth × Fin 4) : (Fin j → ℝ) → imaginaryQuaternions :=
  fun τ => fr d (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
private def slotCoefficient : SlotIndex F j → (Fin (l + j) → ℝ) → ℝ
  | .inl p => fun τ => imCoordL p.2 (frameAlongTop fr V c X p.1.1 (topProj l j τ)) +
      (-imCoord p.2 (fr p.1.1 V) + chartShiftLin (j := j) b u p.1 p.2 τ)
  | .inr i => fun τ => 0 + (ContinuousLinearMap.proj (Fin.natAdd l i) : (Fin (l + j) → ℝ) →L[ℝ] ℝ) τ
private def parameterCell : Fin (l + j) → F.Cell :=
  Fin.addCases (fun i => enclosingCell (b i).1.1) (fun i => (c i).1)
private theorem slotCoefficient_zero (z : SlotIndex F j) : slotCoefficient fr V b u c X z 0 = 0 := by
  cases z with
  | inl p =>
    simp only [slotCoefficient, frameAlongTop, map_zero, bondSpread_zero, leftTranslate_zero,
      imCoordL_apply]
    ring
  | inr i => simp [slotCoefficient]
private theorem analyticAt_imCoord_frameAlongTop {d : F.Site F.depth × Fin 4}
    (hA : IsBondAnalyticAt (fr d) V) (r : Fin 3) :
    AnalyticAt ℝ (fun τ : Fin (l + j) → ℝ => imCoordL r (frameAlongTop fr V c X d (topProj l j τ))) 0 := by
  have h1 : AnalyticAt ℝ (frameAlongTop fr V c X d) (topProj l j 0) := by
    rw [map_zero]
    exact hA j c X
  have h2 : AnalyticAt ℝ (frameAlongTop fr V c X d ∘ topProj l j) 0 :=
    h1.comp ((topProj l j).analyticAt 0)
  exact (imCoordL r).analyticAt _ |>.comp h2
private theorem contDiffAt_slotCoefficient
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    (z : SlotIndex F j) (n : ℕ) : ContDiffAt ℝ n (slotCoefficient fr V b u c X z) 0 := by
  cases z with
  | inl p =>
    have h1 := (analyticAt_imCoord_frameAlongTop fr V c X (hana p.1.1 p.1.2) (l := l) p.2).contDiffAt
      (n := n)
    exact h1.add (contDiffAt_const.add (chartShiftLin (j := j) b u p.1 p.2).contDiff.contDiffAt)
  | inr i =>
    exact contDiffAt_const.add (ContinuousLinearMap.proj (Fin.natAdd l i) :
      (Fin (l + j) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
private theorem abs_iteratedFDeriv_slotCoefficient_le
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    {K : ℕ → ℝ} {r : ℝ} (hK : ∀ k, 0 ≤ K k) (hr : 0 ≤ r)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (fr d) V c' X'‖ ≤ K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c')))
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (hz : ∀ y : F.Cell, cellSupDist y y = 0)
    (z : SlotIndex F j) {q : ℕ} (J : Fin q → Fin (l + j)) (e : Fin q) :
    |iteratedFDeriv ℝ q (slotCoefficient fr V b u c X z) 0 (fun e => Pi.single (J e) 1)| ≤
      (K q + 1) * Real.exp (-(r * cellSupDist (directionCell (indexDirection c X z))
        (parameterCell b c (J e)))) := by
  classical
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact e.elim0
  have hKq : 0 ≤ K q + 1 := by have := hK q; linarith
  have hnn : 0 ≤ (K q + 1) *
      Real.exp (-(r * cellSupDist (directionCell (indexDirection c X z)) (parameterCell b c (J e)))) :=
    mul_nonneg hKq (Real.exp_pos _).le
  cases z with
  | inr i' =>
    have hf : slotCoefficient fr V b u c X (.inr i') = fun τ => 0 + (ContinuousLinearMap.proj
        (Fin.natAdd l i') : (Fin (l + j) → ℝ) →L[ℝ] ℝ) τ := rfl
    rcases Nat.lt_or_ge q 2 with h2 | h2
    · obtain rfl : q = 1 := by omega
      have he0 : e = 0 := Subsingleton.elim _ _
      subst he0
      rw [hf, iteratedFDeriv_affine_one]
      by_cases hJ : J 0 = Fin.natAdd l i'
      · have hcell : parameterCell b c (J 0) = (c i').1 := by
          rw [hJ]
          simp [parameterCell]
        have hs : directionCell (indexDirection c X (.inr i' : SlotIndex F j)) = (c i').1 := rfl
        rw [hcell, hs, hz, hJ]
        have := hK 1
        simp
        linarith
      · have h0 : (ContinuousLinearMap.proj (Fin.natAdd l i') : (Fin (l + j) → ℝ) →L[ℝ] ℝ)
            (Pi.single (J 0) 1) = 0 := by
          have hne : Fin.natAdd l i' ≠ J 0 := fun h => hJ h.symm
          simp [Pi.single_apply, hne]
        rw [h0, abs_zero]
        exact hnn
    · rw [hf, iteratedFDeriv_affine_of_two_le _ _ h2]
      simpa using hnn
  | inl p =>
    obtain ⟨β, ρ⟩ := p
    have hA := hana β.1 β.2
    have hf : slotCoefficient fr V b u c X (.inl (β, ρ)) =
        (fun τ => imCoordL ρ (frameAlongTop fr V c X β.1 (topProj l j τ))) +
          fun τ => -imCoord ρ (fr β.1 V) + chartShiftLin (j := j) b u β ρ τ := rfl
    have h1 := (analyticAt_imCoord_frameAlongTop fr V c X hA (l := l) ρ).contDiffAt (n := q)
    have h2 : ContDiffAt ℝ q (fun τ => -imCoord ρ (fr β.1 V) + chartShiftLin (j := j) b u β ρ τ) 0 :=
      contDiffAt_const.add (chartShiftLin (j := j) b u β ρ).contDiff.contDiffAt
    have h3 : AnalyticAt ℝ (frameAlongTop fr V c X β.1) 0 := hA j c X
    have h4 : ContDiffAt ℝ q (frameAlongTop fr V c X β.1 ∘ topProj l j) 0 := by
      have h5 : AnalyticAt ℝ (frameAlongTop fr V c X β.1 ∘ topProj l j) 0 :=
        AnalyticAt.comp (by rw [map_zero]; exact h3) ((topProj l j).analyticAt 0)
      exact h5.contDiffAt
    have h6 := (imCoordL ρ).iteratedFDeriv_comp_left h4 (i := q) le_rfl
    have h7 := congrArg (fun M => M fun e => (Pi.single (J e) 1 : Fin (l + j) → ℝ)) h6
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h7
    have h7' : iteratedFDeriv ℝ q
        (fun τ => imCoordL ρ (frameAlongTop fr V c X β.1 (topProj l j τ))) 0
        (fun e => Pi.single (J e) 1) = imCoordL ρ
          (iteratedFDeriv ℝ q (frameAlongTop fr V c X β.1 ∘ topProj l j) 0
            fun e => Pi.single (J e) 1) := by
      simpa [Function.comp_def] using h7
    rw [hf, iteratedFDeriv_add_apply h1 h2]
    simp only [ContinuousMultilinearMap.add_apply]
    rw [h7']
    by_cases hit : ∃ (e₀ : Fin q) (i : Fin l), J e₀ = Fin.castAdd j i
    · obtain ⟨e₀, i, he₀⟩ := hit
      rw [iteratedFDeriv_comp_topProj_eq_zero h3 J e₀ i he₀, map_zero, zero_add]
      rcases Nat.lt_or_ge q 2 with h2' | h2'
      · obtain rfl : q = 1 := by omega
        have he0 : e = 0 := Subsingleton.elim _ _
        have he1 : e₀ = 0 := Subsingleton.elim _ _
        subst he0 he1
        rw [iteratedFDeriv_affine_one]
        have hlin : chartShiftLin (j := j) b u β ρ (Pi.single (J 0) 1) =
            if b i = β then u i ρ else 0 := by
          rw [he₀]
          simp only [chartShiftLin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]
          rw [Finset.sum_eq_single i]
          · simp
          · intro i' _ hne
            have h8 : Fin.castAdd j i' ≠ Fin.castAdd j i := fun h => hne (Fin.castAdd_injective _ _ h)
            simp [Pi.single_apply, h8]
          · simp
        rw [hlin]
        by_cases hb : b i = β
        · have hcell : parameterCell b c (J 0) = enclosingCell β.1.1 := by
            rw [he₀, ← hb]
            simp [parameterCell]
          have hs : directionCell (indexDirection c X (.inl (β, ρ) : SlotIndex F j)) =
              enclosingCell β.1.1 := rfl
          rw [hcell, hs, hz, if_pos hb]
          have h9 : |u i ρ| ≤ 1 := by
            have := PiLp.norm_apply_le (u i) ρ
            rw [hu i] at this
            simpa using this
          have := hK 1
          simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
          linarith
        · rw [if_neg hb, abs_zero]
          exact hnn
      · rw [iteratedFDeriv_affine_of_two_le _ _ h2']
        simpa using hnn
    · push_neg at hit
      have hex : ∀ e', ∃ i', J e' = Fin.natAdd l i' := by
        intro e'
        induction h : J e' using Fin.addCases with
        | left i => exact absurd h (hit e' i)
        | right i' => exact ⟨i', rfl⟩
      choose J' hJ' using hex
      have hder := iteratedFDeriv_comp_topProj_eq_bondDeriv (fr := fr β.1) (V := V) (c := c) (X := X)
        h3 J J' hJ'
      have hu' : AreUnitVectors (X ∘ J') := fun e' => hX (J' e')
      have hb1 := hdec β.1 β.2 q (c ∘ J') (X ∘ J') hq1 hu'
      have hcell : parameterCell b c (J e) = (c (J' e)).1 := by
        rw [hJ']
        simp [parameterCell]
      have hs : directionCell (indexDirection c X (.inl (β, ρ) : SlotIndex F j)) =
          enclosingCell β.1.1 := rfl
      have hdist : ((cellSupDist (enclosingCell β.1.1) (c (J' e)).1 : ℕ) : ℝ) ≤
          bondListDistance (enclosingCell β.1.1) (c ∘ J') := by
        have : cellSupDist (enclosingCell β.1.1) (c (J' e)).1 ≤
            bondListDistance (enclosingCell β.1.1) (c ∘ J') :=
          Finset.le_sup (f := fun l' => cellSupDist (enclosingCell β.1.1) (((c ∘ J') l').1))
            (Finset.mem_univ e)
        exact_mod_cast this
      have hmain : |imCoordL ρ (iteratedFDeriv ℝ q (frameAlongTop fr V c X β.1 ∘ topProj l j) 0
          fun e => Pi.single (J e) 1)| ≤
            K q * Real.exp (-(r * cellSupDist (enclosingCell β.1.1) (c (J' e)).1)) := by
        have hd : (iteratedFDeriv ℝ q (frameAlongTop fr V c X β.1 ∘ topProj l j) 0
            fun e => Pi.single (J e) 1) = bondDeriv (fr β.1) V (c ∘ J') (X ∘ J') := hder
        rw [hd, imCoordL_apply]
        refine (abs_imCoord_le _ _).trans (hb1.trans ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hK q)
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hdist hr]
      have hexp0 : 0 ≤ Real.exp (-(r * cellSupDist (enclosingCell β.1.1) (c (J' e)).1)) :=
        (Real.exp_pos _).le
      rw [hcell, hs]
      rcases Nat.lt_or_ge q 2 with h2' | h2'
      · obtain rfl : q = 1 := by omega
        have hlin : chartShiftLin (j := j) b u β ρ (Pi.single (J 0) 1) = 0 := by
          rw [hJ' 0]
          simp only [chartShiftLin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun i _ => ?_
          have h8 : Fin.castAdd j i ≠ Fin.natAdd l (J' 0) := by
            intro e'
            have := congrArg Fin.val e'
            simp at this
            omega
          simp [Pi.single_apply, h8]
        rw [iteratedFDeriv_affine_one, hlin, add_zero]
        have he0 : e = 0 := Subsingleton.elim _ _
        subst he0
        refine hmain.trans ?_
        nlinarith
      · rw [iteratedFDeriv_affine_of_two_le _ _ h2']
        simp only [ContinuousMultilinearMap.zero_apply, add_zero]
        refine hmain.trans ?_
        nlinarith
end coordinates
section core
variable {F : BlockFrame} {l j : ℕ}
private abbrev ChartFunction (F : BlockFrame) : Type :=
  (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ
private def alongDirections (G : ChartFunction F) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) (σ : Fin k → ℝ) : ℝ :=
  G (fun x i => w x i + ∑ l, σ l • directionCoordinate (q l) x i)
    (leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V)
private def mixedKernel (G : ChartFunction F) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) : ℝ :=
  iteratedFDeriv ℝ k (alongDirections G w V q) 0 fun l => Pi.single l 1
private theorem jointDisplacement_eq_comp (G : ChartFunction F)
    (hG : ∀ (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
      (∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) → G w V = G w' V)
    (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    {N : ℕ} (e : SlotIndex F j ≃ Fin N) :
    jointDisplacement (fun ζ V' => G (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X =
      alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V
        (fun n => indexDirection c X (e.symm n)) ∘
        fun τ n => slotCoefficient fr V b u c X (e.symm n) τ := by
  classical
  funext τ
  simp only [jointDisplacement, Function.comp, alongDirections]
  have htop : (fun y i => ∑ n : Fin N, slotCoefficient fr V b u c X (e.symm n) τ •
        directionMove (indexDirection c X (e.symm n)) y i) =
      ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i) := by
    funext y i
    rw [Equiv.sum_comp e.symm
      (fun z : SlotIndex F j => slotCoefficient fr V b u c X z τ • directionMove (indexDirection c X z) y i),
      Fintype.sum_sum_type]
    have h0 : ∀ p : ↥(chordBonds (finiteCells F)) × Fin 3,
        slotCoefficient fr V b u c X (.inl p) τ •
          directionMove (indexDirection c X (.inl p : SlotIndex F j)) y i = 0 := by
      intro p
      simp [indexDirection, directionMove]
    simp only [h0, Finset.sum_const_zero, zero_add, ColdStepAtMirrorFrames.bondSpread]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [slotCoefficient, indexDirection, directionMove]
    have hiff : ((c i').1 = y ∧ (c i').2 = i) ↔ c i' = (y, i) := by
      rw [Prod.ext_iff]
    by_cases h : c i' = (y, i)
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
      simp
  rw [htop]
  refine hG _ _ _ ?_
  intro x i ht
  have hmem := hchart (x, i) ht
  set β₀ : ↥(chordBonds (finiteCells F)) := ⟨(x, i), hmem⟩ with hβ₀
  have hsum : ∑ n : Fin N, slotCoefficient fr V b u c X (e.symm n) τ •
        directionCoordinate (indexDirection c X (e.symm n)) x i =
      ∑ r, slotCoefficient fr V b u c X (.inl (β₀, r)) τ • imBasis r := by
    rw [Equiv.sum_comp e.symm
      (fun z : SlotIndex F j => slotCoefficient fr V b u c X z τ •
        directionCoordinate (indexDirection c X z) x i),
      Fintype.sum_sum_type]
    have h0 : ∀ i' : Fin j,
        slotCoefficient fr V b u c X (.inr i') τ •
          directionCoordinate (indexDirection c X (.inr i' : SlotIndex F j)) x i = 0 := by
      intro i'
      simp [indexDirection, directionCoordinate]
    simp only [h0, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single β₀]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [indexDirection, directionCoordinate, hβ₀]
    · intro β _ hne
      refine Finset.sum_eq_zero fun r _ => ?_
      have hne' : ¬ (β.1.1 = x ∧ β.1.2 = i) := by
        rintro ⟨h1, h2⟩
        exact hne (Subtype.ext (Prod.ext h1 h2))
      simp [indexDirection, directionCoordinate, hne']
    · simp
  rw [hsum]
  have hco : ∀ ζ : StepVariable (finiteCells F), stepCoordinates ζ x i = toImaginary (ζ β₀) := by
    intro ζ
    simp only [stepCoordinates]
    rw [dif_pos hmem]
  apply imaginary_ext
  intro r
  rw [imCoord_add, imCoord_add, imCoord_add, imCoord_sum_smul_imBasis, hco, hco, imCoord_toImaginary,
    imCoord_toImaginary]
  simp only [slotCoefficient, frameAlongTop, imCoordL_apply, displacedPoint, chartShiftLin,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.add_apply, Finset.sum_apply]
  have htp : (topProj l j τ) = fun i => τ (Fin.natAdd l i) := rfl
  rw [htp]
  have hlin : ∀ i' : Fin l, ((Pi.single (b i') (τ (Fin.castAdd j i') • u i') :
      StepVariable (finiteCells F)) β₀) r =
        (if b i' = β₀ then u i' r else 0) * τ (Fin.castAdd j i') := by
    intro i'
    by_cases hb : b i' = β₀
    · rw [if_pos hb, ← hb]
      simp [mul_comm]
    · rw [if_neg hb, Pi.single_eq_of_ne (fun h => hb h.symm)]
      simp
  have hpt : (η β₀ + ∑ i', (Pi.single (b i') (τ (Fin.castAdd j i') • u i') :
      StepVariable (finiteCells F)) β₀) r = η β₀ r +
        ∑ i', (if b i' = β₀ then u i' r else 0) * τ (Fin.castAdd j i') := by
    simp only [PiLp.add_apply]
    congr 1
    rw [← Finset.sum_congr rfl fun i' _ => hlin i']
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) r : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) _ _
  rw [hpt]
  ring
private theorem iteratedFDeriv_alongDirections_eq_mixedKernel (G : ChartFunction F)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {N k : ℕ}
    (q : Fin N → ChartDirection F) (n : Fin k → Fin N) (hA : AnalyticAt ℝ (alongDirections G w V q) 0) :
    iteratedFDeriv ℝ k (alongDirections G w V q) 0 (fun m => Pi.single (n m) 1) =
      mixedKernel G w V (q ∘ n) := by
  have h1 : alongDirections G w V (q ∘ n) = alongDirections G w V q ∘ reindexMap n := by
    funext ρ
    simp only [alongDirections, Function.comp]
    have e1 : (fun x i => w x i + ∑ p, reindexMap n ρ p • directionCoordinate (q p) x i) =
        fun x i => w x i + ∑ m, ρ m • directionCoordinate (q (n m)) x i := by
      funext x i
      rw [sum_reindexMap_smul n ρ (fun p => directionCoordinate (q p) x i)]
    have e2 : (fun y i => ∑ p, reindexMap n ρ p • directionMove (q p) y i) =
        fun y i => ∑ m, ρ m • directionMove (q (n m)) y i := by
      funext y i
      rw [sum_reindexMap_smul n ρ (fun p => directionMove (q p) y i)]
    rw [e1, e2]
  have hz : reindexMap n 0 = 0 := map_zero _
  have h2 := iteratedFDeriv_comp_clm (reindexMap n) (x := 0) (n := k) (f := alongDirections G w V q)
    (by rw [hz]; exact hA.contDiffAt) (fun m => Pi.single m 1)
  simp only [mixedKernel]
  rw [h1, h2, hz]
  simp only [reindexMap_single]
private theorem sum_exp_slot_cell_le {N : ℕ} (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (e : SlotIndex F j ≃ Fin N) {R Cb : ℝ} (hR : 0 ≤ R) (z : F.Cell)
    (hsum : ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(R * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb) :
    ∑ n : Fin N, Real.exp (-(R * cellSupDist (directionCell (indexDirection c X (e.symm n))) z)) ≤
      3 * Cb + j := by
  rw [Equiv.sum_comp e.symm
      (fun y : SlotIndex F j => Real.exp (-(R * cellSupDist (directionCell (indexDirection c X y)) z))),
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∀ β : ↥(chordBonds (finiteCells F)),
      ∑ r : Fin 3, Real.exp (-(R * cellSupDist
          (directionCell (indexDirection c X (.inl (β, r) : SlotIndex F j))) z)) =
        3 * Real.exp (-(R * cellSupDist (enclosingCell β.1.1) z)) := by
    intro β
    have : ∀ r : Fin 3, directionCell (indexDirection c X (.inl (β, r) : SlotIndex F j)) =
        enclosingCell β.1.1 := fun r => rfl
    simp [this]
  have h2 : ∑ i : Fin j, Real.exp (-(R * cellSupDist
      (directionCell (indexDirection c X (.inr i : SlotIndex F j))) z)) ≤ j := by
    calc _ ≤ ∑ _i : Fin j, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          apply Real.exp_le_one_iff.2
          have : (0 : ℝ) ≤ R * cellSupDist (directionCell (indexDirection c X (.inr i : SlotIndex F j))) z :=
            mul_nonneg hR (Nat.cast_nonneg _)
          linarith
      _ = j := by simp
  simp only [h1]
  rw [← Finset.mul_sum]
  linarith
private theorem jointMixedDeriv_bound (G : ChartFunction F)
    (hG : ∀ (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
      (∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) → G w V = G w' V)
    (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    {K Ck : ℕ → ℝ} {κ₂ δ₁ r₀ Cb : ℝ} (Y : F.Cell) (hK : ∀ k, 0 ≤ K k) (hκ : 0 ≤ κ₂)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (fr d) V c' X'‖ ≤ K k * Real.exp (-(κ₂ * bondListDistance (enclosingCell d.1) c')))
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (hCk : ∀ k, 0 ≤ Ck k)
    (hker : ∀ (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0 ∧
      (1 ≤ k → (∀ m, ‖directionVector (q m)‖ = 1) →
        |mixedKernel G (fun z i => fr (z, i) V + stepCoordinates η z i) V q| ≤
          Ck k * Real.exp (-(δ₁ * directionReach Y q))))
    (hz : ∀ y : F.Cell, cellSupDist y y = 0) (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (hCb : 0 ≤ Cb)
    (hsum : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(κ₂ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb)
    (hl : 1 ≤ l + j) (hr₀ : 0 ≤ r₀) (h1 : 2 * r₀ ≤ δ₁) (h2 : 4 * r₀ ≤ κ₂) :
    ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => G
      (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X) 0 ∧
    |jointMixedDeriv (fun ζ V' => G (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V')
        η V b u c X| ≤
      (∑ c' : OrderedFinpartition (l + j), Ck c'.length * (∏ m, (K (c'.partSize m) + 1)) *
        (3 * Cb + j) ^ c'.length) *
        Real.exp (-(r₀ * cellSetDiameter ({Y} ∪ chordBondCells b ∪ topBondCells c))) := by
  classical
  let e := Fintype.equivFin (SlotIndex F j)
  let q : Fin (Fintype.card (SlotIndex F j)) → ChartDirection F := fun n => indexDirection c X (e.symm n)
  let Tt : (Fin (l + j) → ℝ) → Fin (Fintype.card (SlotIndex F j)) → ℝ :=
    fun τ n => slotCoefficient fr V b u c X (e.symm n) τ
  have hfun := jointDisplacement_eq_comp G hG fr V η b u c X hchart e
  have hA := (hker _ q).1
  have T0 : Tt 0 = 0 := funext fun n => slotCoefficient_zero fr V b u c X _
  have hT : ∀ n : ℕ, ContDiffAt ℝ n Tt 0 := fun n =>
    contDiffAt_pi.2 fun m => contDiffAt_slotCoefficient fr V b u c X hana _ n
  have hA' : ContDiffAt ℝ (l + j : ℕ)
      (alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V q) (Tt 0) := by
    rw [T0]
    exact hA.contDiffAt
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ContDiffAt.comp (0 : Fin (l + j) → ℝ) hA' (hT _)
  simp only [jointMixedDeriv]
  rw [hfun]
  have hcomp := iteratedFDeriv_comp_eq_sum hA' (hT (l + j)) (fun i => Pi.single i 1)
  rw [T0] at hcomp
  rw [hcomp]
  set D := cellSetDiameter ({Y} ∪ chordBondCells b ∪ topBondCells c) with hD
  have hCs : 0 ≤ 3 * Cb + (j : ℝ) := by positivity
  have hterm : ∀ c' : OrderedFinpartition (l + j),
      |iteratedFDeriv ℝ c'.length
        (alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
        (c'.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c'.partSize m) Tt 0)
          fun i => Pi.single i 1)| ≤
        Ck c'.length * (∏ m, (K (c'.partSize m) + 1)) * (3 * Cb + j) ^ c'.length *
          Real.exp (-(r₀ * D)) := by
    intro c'
    set vv := c'.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c'.partSize m) Tt 0)
      (fun i => (Pi.single i 1 : Fin (l + j) → ℝ)) with hvvdef
    have hvv : ∀ (m : Fin c'.length) (n : Fin (Fintype.card (SlotIndex F j))),
        vv m n = iteratedFDeriv ℝ (c'.partSize m) (slotCoefficient fr V b u c X (e.symm n)) 0
          (fun q' => Pi.single (c'.emb m q') 1) := by
      intro m n
      simp only [hvvdef, OrderedFinpartition.applyOrderedFinpartition_apply]
      have h3 := (ContinuousLinearMap.proj n :
        (Fin (Fintype.card (SlotIndex F j)) → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left (hT (c'.partSize m))
          (i := c'.partSize m) le_rfl
      have h4 := congrArg (fun M => M fun l' => (Pi.single (c'.emb m l') 1 : Fin (l + j) → ℝ)) h3
      simpa [Tt, Function.comp_def] using h4.symm
    have hk : 1 ≤ c'.length := (c'.index ⟨0, hl⟩).pos
    have hkern : ∀ n : Fin c'.length → Fin (Fintype.card (SlotIndex F j)),
        |iteratedFDeriv ℝ c'.length
          (alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
            (fun m => Pi.single (n m) 1)| ≤
          Ck c'.length * Real.exp (-(δ₁ * (Finset.univ.sup fun m : Fin c'.length =>
            cellSupDist Y (directionCell (q (n m))) : ℕ))) := by
      intro n
      rw [iteratedFDeriv_alongDirections_eq_mixedKernel G _ V q n hA]
      refine (hker _ (q ∘ n)).2 hk fun m => ?_
      show ‖directionVector (indexDirection c X (e.symm (n m)))‖ = 1
      cases e.symm (n m) with
      | inl p => exact norm_imBasis p.2
      | inr i => exact hX i
    have hP : ∀ y ∈ {Y} ∪ chordBondCells b ∪ topBondCells c,
        y = Y ∨ ∃ i, parameterCell b c i = y := by
      intro y hy
      rcases Finset.mem_union.1 hy with hy | hy
      · rcases Finset.mem_union.1 hy with hy | hy
        · exact Or.inl (Finset.mem_singleton.1 hy)
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
          exact Or.inr ⟨Fin.castAdd j i, by simp [parameterCell]⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact Or.inr ⟨Fin.natAdd l i, by simp [parameterCell]⟩
    have hplaces := sum_over_slot_cells_le cellSupDist hz hsym htri Y (fun n => directionCell (q n))
      (parameterCell b c) ({Y} ∪ chordBondCells b ∪ topBondCells c) hP c' vv (fun k => K k + 1)
      (fun k => by have := hK k; linarith) hr₀ h1 h2
      (fun m n q' => by
        rw [hvv]
        exact abs_iteratedFDeriv_slotCoefficient_le fr V b u c X hana hK hκ hdec hu hX hz _
          (c'.emb m) q')
      (fun y => sum_exp_slot_cell_le c X e (by linarith) y (hsum y))
    rw [multilinear_eq_sum_basis]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∀ n ∈ Fintype.piFinset fun _ : Fin c'.length =>
        (Finset.univ : Finset (Fin (Fintype.card (SlotIndex F j)))),
        |(∏ m, vv m (n m)) * iteratedFDeriv ℝ c'.length
          (alongDirections G (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
            (fun m => Pi.single (n m) 1)| ≤
          Ck c'.length * ((∏ m, |vv m (n m)|) *
            Real.exp (-(δ₁ * (Finset.univ.sup fun m : Fin c'.length =>
              cellSupDist Y (directionCell (q (n m))) : ℕ)))) := by
      intro n _
      rw [abs_mul, Finset.abs_prod]
      have hp0 : 0 ≤ ∏ m, |vv m (n m)| := Finset.prod_nonneg fun m _ => abs_nonneg _
      calc _ ≤ (∏ m, |vv m (n m)|) * _ := mul_le_mul_of_nonneg_left (hkern n) hp0
        _ = _ := by ring
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left hplaces (hCk _)).trans (le_of_eq ?_)
    simp only [hD, cellSetDiameter]
    ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c' _ => hterm c').trans ?_)
  rw [Finset.sum_mul]
end core
section table
variable {F : BlockFrame}
private theorem eventually_parameter_bounds (g : ℝ → ℕ → ColdChainParameters → ℝ)
    (hg : ∀ a L c, 1 ≤ a → Odd L → ColdChainParameters.Admissible c a L → 0 < g a L c) :
    EventuallyInParameters fun T => 1 ≤ T.a ∧ Odd T.L ∧ 2 ^ 40 ≤ T.L ∧
      T.chainParams.Admissible T.a T.L ∧ 0 < T.σ ∧
      T.σ ≤ g T.a T.L T.chainParams ∧ 64 ≤ T.n₀ ∧ 0 < T.κ ∧ 2 ^ 10 * T.κ ≤ T.chainParams.δ₁ ∧
      2 ^ 10 * T.κ ≤ T.chainParams.κ₂ := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ⟨0, fun Ct _ => ?_⟩⟩
  obtain ⟨-, -, -, hδ₂, hκδ, -, -, -⟩ := hc.classical.1
  have hδ₁ := hc.positivity.1
  have hκ₂ : 0 < c.κ₂ := by nlinarith
  refine ⟨min c.δ₁ c.κ₂ / 2 ^ 10, by positivity, fun κ hκ hκ' => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨g a L c, hg a L c ha hL hc, fun σ h0 hσ p hp => ⟨0,
      fun Cs _ E _ => ⟨64, fun n₀ hn => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  have h1 : 2 ^ 10 * κ ≤ min c.δ₁ c.κ₂ := by
    rw [le_div_iff₀ (by positivity)] at hκ'
    linarith
  exact ⟨ha, hL, hL₀, hc, h0, hσ, hn, hκ, h1.trans (min_le_left _ _), h1.trans (min_le_right _ _)⟩
private theorem norm_stepCoordinates_le {F : BlockFrame} (η : StepVariable (finiteCells F)) {r : ℝ}
    (h0 : 0 ≤ r) (hη : ∀ b, ‖η b‖ ≤ r) (x : F.Site F.depth) (i : Fin 4) :
    ‖stepCoordinates η x i‖ ≤ r := by apply _root_.YangMills.Construction.SecondOrderMoves.norm_stepCoordinates_le <;> assumption
private theorem exists_kernel_constants (hB : CellEnergyKernelBound)
    (hS : WeightedResponses.SiteShareKernelBound)
    (hgeo : CubicTorusCellGeometry) (hcov : BlocksCoverLowerLevel)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) :
    ∃ D₀ : ℕ → ℕ → ℝ, (∀ l j, 0 < D₀ l j) ∧
      (1 ≤ T.a → Odd T.L → 2 ^ 40 ≤ T.L → T.chainParams.Admissible T.a T.L → 0 < T.κ →
        2 ^ 10 * T.κ ≤ T.chainParams.δ₁ → 2 ^ 10 * T.κ ≤ T.chainParams.κ₂ →
        ∀ (F : BlockFrame) (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
          (V : F.GaugeField F.top)
          (η : StepVariable (finiteCells F)), IsBlockTorus T.L F →
          IsAdmissibleChartPoint T.L T.chainParams.σA
            (fun z i => fr (z, i) V + stepCoordinates η z i) V →
          (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V) →
          (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
            (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
            ‖bondDeriv (fr d) V c' X'‖ ≤
              16 ^ k * T.chainParams.Kk k *
                Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c'))) →
          ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
            (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
            (X : Fin j → imaginaryQuaternions),
            1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
            (∀ Y : F.Cell, HasDecayingKernelAt (fun ζ V' => cellEnergyShare T.a Y
              (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') (D₀ l j) (2 ^ 7 * T.κ) {Y}
                η V b u c X) ∧
            ∀ y : F.Site F.depth, HasDecayingKernelAt (fun ζ V' => minimalSiteShare T.a y
              (chartedField (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V'))
              (D₀ l j) (2 ^ 7 * T.κ) {enclosingCell y} η V b u c X) := by
  by_cases hgood : 1 ≤ T.a ∧ Odd T.L ∧ 2 ^ 40 ≤ T.L ∧ T.chainParams.Admissible T.a T.L
  · obtain ⟨ha, hL, hL40, hc⟩ := hgood
    obtain ⟨Ck₁, hCk₁, hker₁⟩ := hB T.a T.L T.chainParams ha hL hL40 hc
    obtain ⟨Ck₂, hCk₂, hker₂⟩ := hS T.a T.L T.chainParams ha hL hL40 hc
    obtain ⟨-, -, -, hδ₂, hκδ, -, -, hKk⟩ := hc.classical.1
    have hκ₂ : 0 < T.chainParams.κ₂ := by nlinarith
    obtain ⟨Cg, hCg, hsum⟩ := hgeo.2 (T.chainParams.κ₂ / 2) (by linarith)
    have hL0 : 0 < T.L := by omega
    let Cb : ℝ := Cg * (T.L : ℝ) ^ 4
    have hCb : 0 ≤ Cb := by positivity
    let K : ℕ → ℝ := fun k => 16 ^ k * T.chainParams.Kk k
    have hK0 : ∀ k, 0 ≤ K k := fun k => mul_nonneg (by positivity) (hKk k).le
    let B : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun Ck l j => ∑ c' : OrderedFinpartition (l + j), Ck c'.length *
      (∏ m, (K (c'.partSize m) + 1)) * (3 * Cb + j) ^ c'.length
    have hB0 : ∀ Ck : ℕ → ℝ, (∀ k, 0 < Ck k) → ∀ l j, 0 ≤ B Ck l j := fun Ck hCk l j =>
      Finset.sum_nonneg fun c' _ =>
      mul_nonneg (mul_nonneg (hCk _).le (Finset.prod_nonneg fun m _ => by
        have := hK0 (c'.partSize m); linarith)) (by positivity)
    have h₁ := hB0 Ck₁ hCk₁
    have h₂ := hB0 Ck₂ hCk₂
    refine ⟨fun l j => B Ck₁ l j + B Ck₂ l j + 1, fun l j => by
      have := h₁ l j; have := h₂ l j; linarith, ?_⟩
    intro _ _ _ _ hκ0 hκδ₁ hκκ₂ F fr V η hF hsmall hana hdec l j b u c X hl hu hX
    have hodd : Odd F.blockSide := hF.1 ▸ hL
    have hcub := hF.2
    obtain ⟨n, hn64, hside⟩ := id hcub
    have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
    have hall := hcov F hodd hpos
    have hbond : ∀ d : F.Site F.depth × Fin 4, d ∈ fineBonds F := fun d => by
      simp [fineBonds, hall]
    have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
      have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
      simp [chordBonds, innerBonds, hall, hd]
    have hg1 := hgeo.1 F hodd hcub
    have hsum' : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
        Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb := by
      intro z
      have h1 := hsum F hodd hcub z
      rw [hF.1] at h1
      rw [Finset.sum_coe_sort (chordBonds (finiteCells F))
        (fun d => Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell d.1) z)))]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun d _ => hbond d)
        fun _ _ _ => (Real.exp_pos _).le) h1
    have hr₀ : (0 : ℝ) ≤ 2 ^ 7 * T.κ := by positivity
    have hr₁ : 2 * (2 ^ 7 * T.κ) ≤ T.chainParams.δ₁ := by nlinarith
    have hr₂ : 4 * (2 ^ 7 * T.κ) ≤ T.chainParams.κ₂ := by nlinarith
    have hzd : ∀ z : F.Cell, cellSupDist z z = 0 := fun z => by simp [cellSupDist]
    refine ⟨fun Y => ?_, fun y => ?_⟩
    · have hcore := jointMixedDeriv_bound (fun w V' => cellEnergyShare T.a Y w V')
        (fun w w' V' h => by
          show cellEnergyShare T.a Y w V' = cellEnergyShare T.a Y w' V'
          unfold cellEnergyShare
          rw [chartedField_congr V' h]) fr V η b u c X hchart hana (K := K) (Ck := Ck₁)
        (κ₂ := T.chainParams.κ₂) (δ₁ := T.chainParams.δ₁) (r₀ := 2 ^ 7 * T.κ) (Cb := Cb) Y hK0 hκ₂.le
        hdec hu hX
        (fun k => (hCk₁ k).le)
        (fun k q => by
          have := hker₁ F _ V hF hsmall Y k q
          exact ⟨this.1, fun h2 hq => this.2 h2 hq⟩)
        hzd hg1.2.2.1 hg1.2.2.2.1 hCb hsum' hl hr₀ hr₁ hr₂
      refine ⟨hcore.1, hcore.2.trans ?_⟩
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      show B Ck₁ l j ≤ B Ck₁ l j + B Ck₂ l j + 1
      have := h₂ l j
      linarith
    · have hcore := jointMixedDeriv_bound (fun w V' => minimalSiteShare T.a y (chartedField w V'))
        (fun w w' V' h => by
          show minimalSiteShare T.a y (chartedField w V') = minimalSiteShare T.a y (chartedField w' V')
          rw [chartedField_congr V' h]) fr V η b u c X hchart hana (K := K) (Ck := Ck₂)
        (κ₂ := T.chainParams.κ₂) (δ₁ := T.chainParams.δ₁) (r₀ := 2 ^ 7 * T.κ) (Cb := Cb)
        (enclosingCell y) hK0 hκ₂.le hdec hu hX
        (fun k => (hCk₂ k).le)
        (fun k q => by
          have := hker₂ F _ V hF hsmall y k q
          exact ⟨this.1, fun h2 hq => this.2 h2 hq⟩)
        hzd hg1.2.2.1 hg1.2.2.2.1 hCb hsum' hl hr₀ hr₁ hr₂
      refine ⟨hcore.1, hcore.2.trans ?_⟩
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      show B Ck₂ l j ≤ B Ck₁ l j + B Ck₂ l j + 1
      have := h₁ l j
      linarith
  · refine ⟨fun _ _ => 1, fun _ _ => one_pos, ?_⟩
    intro h1 h2 h3 h4
    exact absurd ⟨h1, h2, h3, h4⟩ hgood
end table
theorem blockKernelBounds (hD : SummableBounds.interpolatedFrameDecayStatement)
    (hB : CellEnergyKernelBound) (hS : WeightedResponses.SiteShareKernelBound)
    (hgeo : CubicTorusCellGeometry) (hcov : BlocksCoverLowerLevel) :
    blockKernelBoundsStatement := by
  obtain ⟨Cz, hCz, hD⟩ := hD
  choose D₀ hpos hprop using exists_kernel_constants hB hS hgeo hcov
  refine ⟨D₀, hpos, ?_⟩
  let g : ℝ → ℕ → ColdChainParameters → ℝ := fun a L c =>
    min (1 / (64 * (L : ℝ) * (Cz a L c + 1))) (c.σA / (16 * (Cz a L c + 2)))
  have hg : ∀ a L c, 1 ≤ a → Odd L → ColdChainParameters.Admissible c a L → 0 < g a L c := by
    intro a L c _ hL hc
    have hL0 : (0 : ℝ) < L := by
      have : 0 < L := hL.pos
      exact_mod_cast this
    have h1 := hCz a L c
    have h2 := hc.positivity.2.2.2.1
    exact lt_min (by positivity) (by positivity)
  refine EventuallyInParameters.mono (EventuallyInParameters.and hD (eventually_parameter_bounds g hg)) ?_
  rintro T ⟨gD, ha, hL, hL40, hc, hσ0, hσ, hn, hκ0, hκδ, hκκ⟩ x t F V s η hx hF hV hs hs' hη l j b u c X
    hl hu hX
  obtain ⟨hFL, hFt, n, hside, hn₀⟩ := hF
  have hF' : IsCubicTopTorus T.L t T.n₀ F := ⟨hFL, hFt, n, hside, hn₀⟩
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hchain : IsBlockTorus T.L F := ⟨hFL, n, hn.trans hn₀, hside⟩
  have hsides : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hall := hcov F hodd fun i => by have := hsides i; omega
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
    simp [chordBonds, innerBonds, hall, hd]
  set fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions :=
    fun d => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d with hfr
  have hframe := fun d hd => gD x t F V s hx hF' hV hs hs' d hd
  set Cn := Cz T.a T.L T.chainParams with hCn
  have hCn0 : 0 < Cn := hCz _ _ _
  have hLr : (0 : ℝ) < T.L := by
    have : 0 < T.L := hL.pos
    exact_mod_cast this
  have hσ₁ : T.σ ≤ 1 / (64 * (T.L : ℝ) * (Cn + 1)) := hσ.trans (min_le_left _ _)
  have hσ₂ : T.σ ≤ T.chainParams.σA / (16 * (Cn + 2)) := hσ.trans (min_le_right _ _)
  have hρ : T.ballRadius ≤ T.σ := by
    simp only [StepParameters.ballRadius]
    linarith
  have hcoord : ∀ x' i, ‖stepCoordinates η x' i‖ ≤ T.σ :=
    norm_stepCoordinates_le η hσ0.le fun b' => (hη b').trans hρ
  have he₁ : (Cn + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ)) := by
    rw [le_div_iff₀ (by positivity)] at hσ₁ ⊢
    nlinarith
  have hsize : ∀ d ∈ chordBonds (finiteCells F),
      ‖fr d V + stepCoordinates η d.1 d.2‖ ≤ (Cn + 1) * T.σ := by
    intro d hd
    refine (norm_add_le _ _).trans ?_
    have h1 := (hframe d hd).1
    have h2 := hcoord d.1 d.2
    linarith
  have hsmall : IsAdmissibleChartPoint T.L T.chainParams.σA
      (fun z i => fr (z, i) V + stepCoordinates η z i) V := by
    refine ⟨fun d hd => (hsize d hd).trans he₁, ?_⟩
    set w' : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i =>
      open Classical in if IsAxialTreeBond (z, i) then 0 else fr (z, i) V + stepCoordinates η z i
      with hw'
    have hcf : chartedField (fun z i => fr (z, i) V + stepCoordinates η z i) V = chartedField w' V :=
      chartedField_congr V fun z i ht => by simp [hw', ht]
    rw [hcf]
    have hL64 : (1 : ℝ) ≤ 64 * T.L := by
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hL.pos
      linarith
    have he₂ : (Cn + 1) * T.σ ≤ 1 / 4 := by
      refine he₁.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hL.pos
      linarith
    have hcold : IsCold (finiteCells F) F.top (5 / 4 * T.σ) V := fun p hp => by
      simp only [innerPlaquettes, Finset.mem_filter] at hp
      exact hV p hp.2.1
    intro p hp
    have hmem : p ∈ innerPlaquettes (finiteCells F) F.depth := by
      simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨hall _, hp, fun y _ => hall y⟩
    have hcur := GaugeFixing.plaquetteDefect_chartedField_le hsides hodd (finiteCells F) V
      (5 / 4 * T.σ) ((Cn + 1) * T.σ) (by positivity) hcold w' he₂ (fun d _ => by
        by_cases ht : IsAxialTreeBond (d.1, d.2)
        · have : w' d.1 d.2 = 0 := by simp [hw', ht]
          rw [this]
          simp only [ZeroMemClass.coe_zero, norm_zero]
          positivity
        · have : w' d.1 d.2 = fr (d.1, d.2) V + stepCoordinates η d.1 d.2 := by simp [hw', ht]
          rw [this]
          exact hsize (d.1, d.2) (hchart _ ht)) p hmem
    have hlt : 5 / 4 * T.σ + 8 * ((Cn + 1) * T.σ) < T.chainParams.σA := by
      have h2 := hc.positivity.2.2.2.1
      rw [le_div_iff₀ (by positivity)] at hσ₂
      nlinarith
    linarith
  have hgo := hprop (rateParameters T) ha hL hL40 hc hκ0 hκδ hκκ F fr V η hchain hsmall
    (fun d hd => (hframe d hd).2.1)
    (fun d hd k c' X' hk hX' => (hframe d hd).2.2 k c' X' hk hX') l j b u c X hl hu hX
  exact hgo
end ResponseInTheExpansion
end YangMills.Construction
end
