import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction
open Coordinates
namespace ComplexVariables.HolomorphicFacts
variable {n : ℕ}
theorem isHolomorphicScalar_iff_lines {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} :
    IsHolomorphicScalar U F ↔ IsOpen U ∧ ContinuousOn F U ∧
      ∀ a ∈ U, ∀ j : Fin n, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => F (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.DeltaSharedProofs.p501560 <;> assumption
theorem isHolomorphicScalar_of_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    IsHolomorphicScalar U F := by
  refine isHolomorphicScalar_iff_lines.2 ⟨hU, hF.continuousOn, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hmem : ∀ᶠ ζ : ℂ in 𝓝 0, a + ζ • ComplexCoordinates.stdBasisVector j ∈ U :=
    hline.continuousAt.eventually_mem (by simpa using hU.mem_nhds ha)
  filter_upwards [hmem] with ζ hζ
  have hd : DifferentiableAt ℂ F (a + ζ • ComplexCoordinates.stdBasisVector j) :=
    (hF _ hζ).differentiableAt (hU.mem_nhds hζ)
  have hl : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact hd.comp ζ hl
section Holomorphic
variable (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
include H
theorem differentiableOn_of_isHolomorphicScalar {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar U F) : DifferentiableOn ℂ F U := by
  have hU : IsOpen U := hF.1
  have hL : ∀ b ∈ U, ∃ L : ComplexCoordinates n →L[ℂ] ComplexCoordinates 1,
      HasFDerivAt ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) (L.restrictScalars ℝ) b :=
    ((H.1 n U hU).1 1 _ hF).2.2.1
  intro b hb
  obtain ⟨L, hL⟩ := hL b hb
  let P : ComplexCoordinates 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : HasFDerivAt (fun y : ComplexCoordinates 1 => y 0) (P.restrictScalars ℝ)
      (((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) b) :=
    (P.restrictScalars ℝ).hasFDerivAt
  have hc := hP.comp b hL
  have hFe : (fun y : ComplexCoordinates 1 => y 0) ∘ ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) = F := by
    funext z
    simp [Equiv.funUnique]
  rw [hFe] at hc
  have hd : HasFDerivAt F (P.comp L) b :=
    hasFDerivAt_of_restrictScalars ℝ hc (by ext; rfl)
  exact hd.differentiableAt.differentiableWithinAt
theorem contDiffOn_real_of_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    ContDiffOn ℝ ∞ F U := by
  have h := ((H.1 n U hU).1 1 _ (isHolomorphicScalar_of_differentiableOn hU hF)).2.1
  have hc := contDiffOn_pi.1 h 0
  refine hc.congr fun z _ => ?_
  simp [Equiv.funUnique]
theorem exists_symmetric_second_deriv {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : ComplexCoordinates n} (hz : z ∈ U) :
    ∃ T : ComplexCoordinates n → ComplexCoordinates n → ℂ,
      (∀ v, ∃ L : ComplexCoordinates n →L[ℂ] ℂ,
        HasFDerivAt (fun w => fderiv ℂ F w v) L z ∧ ∀ u, L u = T u v) ∧
      ∀ u v, T u v = T v u := by
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  have hsm : ContDiffAt ℝ ∞ F z := (contDiffOn_real_of_differentiableOn H hU hF).contDiffAt
    (hU.mem_nhds hz)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hsm.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ F z := hsm.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    norm_cast)
  have hcr : ∀ᶠ w in 𝓝 z, ∀ v, fderiv ℂ F w v = fderiv ℝ F w v := by
    filter_upwards [hnear] with w hw v
    have h1 := ((hF w hw).differentiableAt (hU.mem_nhds hw)).hasFDerivAt
    rw [(h1.restrictScalars ℝ).fderiv]
    rfl
  set T := fderiv ℝ (fderiv ℝ F) z with hT
  have hev : ∀ v, HasFDerivAt (fun w => fderiv ℝ F w v) (T.flip v) z := fun v =>
    (((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp z hD.hasFDerivAt).congr_fderiv
      (ContinuousLinearMap.ext fun u => rfl)
  have hI : ∀ u v, T u (Complex.I • v) = Complex.I * T u v := by
    intro u v
    have h1 : HasFDerivAt (fun w => Complex.I * fderiv ℝ F w v) (Complex.I • T.flip v) z :=
      (hev v).const_smul Complex.I
    have h2 : HasFDerivAt (fun w => Complex.I * fderiv ℝ F w v) (T.flip (Complex.I • v)) z := by
      refine (hev (Complex.I • v)).congr_of_eventuallyEq ?_
      filter_upwards [hcr] with w hw
      rw [← hw, ← hw, map_smul, smul_eq_mul]
    have := congrArg (fun A => A u) (h1.unique h2)
    simpa using this.symm
  have hI' : ∀ u v, T (Complex.I • u) v = Complex.I * T u v := fun u v => by
    rw [hsym, hI, hsym]
  refine ⟨fun u v => T u v, fun v => ?_, fun u v => hsym u v⟩
  let L0 : ComplexCoordinates n →ₗ[ℂ] ℂ :=
    { toFun := fun u => T u v
      map_add' := fun a b => by simp
      map_smul' := fun c u => by
        have hc : c • u = (c.re : ℝ) • u + (c.im : ℝ) • (Complex.I • u) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [hc, map_add, map_smul, map_smul, add_apply, smul_apply, smul_apply, hI']
        simp only [RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  let L : ComplexCoordinates n →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L0
  refine ⟨L, ?_, fun u => rfl⟩
  have h3 : HasFDerivAt (fun w => fderiv ℂ F w v) (T.flip v) z := by
    refine (hev v).congr_of_eventuallyEq ?_
    filter_upwards [hcr] with w hw
    exact hw v
  exact hasFDerivAt_of_restrictScalars ℝ h3 (by ext u; rfl)
end Holomorphic
theorem tendsto_diffQuot_of_hasDerivAt {F : ComplexCoordinates n → ℂ} {z : ComplexCoordinates n}
    {j : Fin n} {l : ℂ}
    (h : HasDerivAt (fun ζ : ℂ => F (z + ζ • ComplexCoordinates.stdBasisVector j)) l 0) :
    Tendsto (diffQuot F z j) (𝓝[≠] 0) (𝓝 l) := by
  have h1 := hasDerivAt_iff_tendsto_slope_zero.1 h
  refine h1.congr fun ζ => ?_
  simp [diffQuot]
theorem partialDeriv_eq_of_hasDerivAt {F : ComplexCoordinates n → ℂ} {z : ComplexCoordinates n}
    {j : Fin n} {l : ℂ}
    (h : HasDerivAt (fun ζ : ℂ => F (z + ζ • ComplexCoordinates.stdBasisVector j)) l 0) :
    partialDeriv j F z = l :=
  (tendsto_diffQuot_of_hasDerivAt h).limUnder_eq
theorem hasDerivAt_along_basis {F : ComplexCoordinates n → ℂ} {z : ComplexCoordinates n}
    (h : DifferentiableAt ℂ F z) (j : Fin n) :
    HasDerivAt (fun ζ : ℂ => F (z + ζ • ComplexCoordinates.stdBasisVector j))
      (fderiv ℂ F z (ComplexCoordinates.stdBasisVector j)) 0 :=
  h.hasFDerivAt.hasLineDerivAt _
theorem partialDeriv_eq_fderiv {F : ComplexCoordinates n → ℂ} {z : ComplexCoordinates n}
    (h : DifferentiableAt ℂ F z) (j : Fin n) :
    partialDeriv j F z = fderiv ℂ F z (ComplexCoordinates.stdBasisVector j) :=
  partialDeriv_eq_of_hasDerivAt (hasDerivAt_along_basis h j)
theorem hasPartialDeriv_of_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (j : Fin n) :
    HasPartialDeriv U F j :=
  ⟨hU, fun z hz => ⟨_, tendsto_diffQuot_of_hasDerivAt
    (hasDerivAt_along_basis ((hF z hz).differentiableAt (hU.mem_nhds hz)) j)⟩⟩
theorem partialDeriv_eqOn_of_eqOn {U : Set (ComplexCoordinates n)}
    {F G : ComplexCoordinates n → ℂ}
    (hU : IsOpen U) (h : EqOn F G U) (j : Fin n) :
    EqOn (partialDeriv j F) (partialDeriv j G) U := by
  intro z hz
  have hline : Continuous fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hmem : ∀ᶠ ζ : ℂ in 𝓝 0, z + ζ • ComplexCoordinates.stdBasisVector j ∈ U :=
    hline.continuousAt.eventually_mem (by simpa using hU.mem_nhds hz)
  have hq : diffQuot F z j =ᶠ[𝓝[≠] 0] diffQuot G z j := by
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with ζ hζ
    simp only [diffQuot, h hζ, h hz]
  simp only [partialDeriv, limUnder]
  rw [Filter.map_congr hq]
theorem iteratedPartials_eqOn_of_eqOn {U : Set (ComplexCoordinates n)}
    {F G : ComplexCoordinates n → ℂ}
    (hU : IsOpen U) (h : EqOn F G U) (l : List (Fin n)) :
    EqOn (iteratedPartials l F) (iteratedPartials l G) U := by
  induction l with
  | nil => exact h
  | cons j l ih => exact partialDeriv_eqOn_of_eqOn hU ih j
section Holomorphic
variable (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
include H
theorem partialDeriv_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (j : Fin n) :
    DifferentiableOn ℂ (partialDeriv j F) U := by
  intro z hz
  obtain ⟨T, hT, -⟩ := exists_symmetric_second_deriv H hU hF hz
  obtain ⟨L, hL, -⟩ := hT (ComplexCoordinates.stdBasisVector j)
  refine hL.differentiableAt.differentiableWithinAt.congr (fun w hw => ?_) ?_
  · exact partialDeriv_eq_fderiv ((hF w hw).differentiableAt (hU.mem_nhds hw)) j
  · exact partialDeriv_eq_fderiv ((hF z hz).differentiableAt (hU.mem_nhds hz)) j
theorem partialDeriv_comm {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (j l : Fin n) :
    EqOn (partialDeriv j (partialDeriv l F))
      (partialDeriv l (partialDeriv j F)) U := by
  intro z hz
  obtain ⟨T, hT, hsym⟩ := exists_symmetric_second_deriv H hU hF hz
  have key : ∀ p q : Fin n, partialDeriv p (partialDeriv q F) z =
      T (ComplexCoordinates.stdBasisVector p) (ComplexCoordinates.stdBasisVector q) := by
    intro p q
    obtain ⟨L, hL, hLT⟩ := hT (ComplexCoordinates.stdBasisVector q)
    have he : EqOn (partialDeriv q F)
        (fun w => fderiv ℂ F w (ComplexCoordinates.stdBasisVector q)) U := fun w hw =>
      partialDeriv_eq_fderiv ((hF w hw).differentiableAt (hU.mem_nhds hw)) q
    rw [partialDeriv_eqOn_of_eqOn hU he p hz, partialDeriv_eq_fderiv hL.differentiableAt,
      hL.fderiv, hLT]
  rw [key, key, hsym]
theorem iteratedPartials_exist_and_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (l : List (Fin n)) :
    HasIteratedPartials U l F ∧ DifferentiableOn ℂ (iteratedPartials l F) U := by
  induction l with
  | nil => exact ⟨hU, hF⟩
  | cons j l ih =>
    exact ⟨⟨ih.1, hasPartialDeriv_of_differentiableOn hU ih.2 j⟩,
      partialDeriv_differentiableOn H hU ih.2 j⟩
theorem iteratedPartials_eqOn_of_perm {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {l l' : List (Fin n)} (h : l.Perm l') :
    EqOn (iteratedPartials l F) (iteratedPartials l' F) U := by
  induction h with
  | nil => exact fun _ _ => rfl
  | cons x _ ih => exact partialDeriv_eqOn_of_eqOn hU ih x
  | swap x y l =>
    exact partialDeriv_comm H hU (iteratedPartials_exist_and_differentiableOn H hU hF l).2 y x
  | trans _ _ ih₁ ih₂ => exact fun z hz => (ih₁ hz).trans (ih₂ hz)
theorem partialDerivProperties_of_isHolomorphicScalar {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar U F) : PartialDerivProperties U F := by
  have hU : IsOpen U := hF.1
  have hd := differentiableOn_of_isHolomorphicScalar H hF
  refine ⟨fun j => ⟨hasPartialDeriv_of_differentiableOn hU hd j,
      isHolomorphicScalar_of_differentiableOn hU (partialDeriv_differentiableOn H hU hd j)⟩,
    partialDeriv_comm H hU hd, fun J => ⟨(iteratedPartials_exist_and_differentiableOn H hU hd _).1,
      isHolomorphicScalar_of_differentiableOn hU
        (iteratedPartials_exist_and_differentiableOn H hU hd _).2⟩,
    fun α => ⟨(iteratedPartials_exist_and_differentiableOn H hU hd _).1,
      isHolomorphicScalar_of_differentiableOn hU
        (iteratedPartials_exist_and_differentiableOn H hU hd _).2⟩,
    fun J l hl => ⟨(iteratedPartials_exist_and_differentiableOn H hU hd _).1,
      iteratedPartials_eqOn_of_perm H hU hd hl⟩,
    fun α l hl => ⟨(iteratedPartials_exist_and_differentiableOn H hU hd _).1,
      iteratedPartials_eqOn_of_perm H hU hd hl⟩,
    fun J s hs => ?_, fun U' hU' hsub G hG =>
      ⟨?_, fun J => iteratedPartials_eqOn_of_eqOn hU' hG _⟩⟩
  · have hperm : (s :: J.sort).Perm (insert s J).sort := by
      refine (List.perm_ext_iff_of_nodup ?_ (Finset.sort_nodup _ _)).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hs, Finset.sort_nodup _ _⟩
      · simp
    exact iteratedPartials_eqOn_of_perm H hU hd hperm
  · exact isHolomorphicScalar_of_differentiableOn hU' ((hd.mono hsub).congr hG)
end Holomorphic
section Rules
variable (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
include H
theorem algebraRules_of_isOpen {U : Set (ComplexCoordinates n)} (hU : IsOpen U) :
    AlgebraRules U := by
  have hcoord : ∀ (z : ComplexCoordinates n) (l : Fin n),
      HasFDerivAt (fun z : ComplexCoordinates n => z l)
        (ContinuousLinearMap.proj l : ComplexCoordinates n →L[ℂ] ℂ) z := fun z l =>
    (ContinuousLinearMap.proj l : ComplexCoordinates n →L[ℂ] ℂ).hasFDerivAt
  have hat : ∀ {F : ComplexCoordinates n → ℂ}, IsHolomorphicScalar U F → ∀ z ∈ U,
      DifferentiableAt ℂ F z := fun hF z hz =>
    (differentiableOn_of_isHolomorphicScalar H hF z hz).differentiableAt (hU.mem_nhds hz)
  refine ⟨fun c => ⟨isHolomorphicScalar_of_differentiableOn hU (differentiableOn_const c),
      fun s z _ => ?_⟩,
    fun l => isHolomorphicScalar_of_differentiableOn hU
      fun z _ => (hcoord z l).differentiableAt.differentiableWithinAt,
    fun s z _ => ?_, fun s l hls z _ => ?_, fun F F' hF hF' a a' => ?_,
    fun k _ F hF s z hz => ?_, fun p => ?_⟩
  · rw [partialDeriv_eq_fderiv (differentiableAt_const c)]
    simp
  · rw [partialDeriv_eq_fderiv (hcoord z s).differentiableAt, (hcoord z s).fderiv]
    simp [ComplexCoordinates.stdBasisVector]
  · rw [partialDeriv_eq_fderiv (hcoord z l).differentiableAt, (hcoord z l).fderiv]
    simp [ComplexCoordinates.stdBasisVector, hls]
  · have dF := differentiableOn_of_isHolomorphicScalar H hF
    have dF' := differentiableOn_of_isHolomorphicScalar H hF'
    refine ⟨isHolomorphicScalar_of_differentiableOn hU ((dF.const_mul a).add (dF'.const_mul a')),
      isHolomorphicScalar_of_differentiableOn hU (dF.mul dF'),
      fun s => ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
    · have h1 := hat hF z hz
      have h2 := hat hF' z hz
      have hd : HasFDerivAt (fun z => a * F z + a' * F' z)
          (a • fderiv ℂ F z + a' • fderiv ℂ F' z) z :=
        (h1.hasFDerivAt.const_mul a).add (h2.hasFDerivAt.const_mul a')
      rw [partialDeriv_eq_fderiv hd.differentiableAt, hd.fderiv]
      beta_reduce
      rw [partialDeriv_eq_fderiv h1, partialDeriv_eq_fderiv h2]
      simp
    · have h1 := hat hF z hz
      have h2 := hat hF' z hz
      have hd : HasFDerivAt (fun z => F z * F' z)
          (F z • fderiv ℂ F' z + F' z • fderiv ℂ F z) z :=
        h1.hasFDerivAt.mul h2.hasFDerivAt
      rw [partialDeriv_eq_fderiv hd.differentiableAt, hd.fderiv]
      beta_reduce
      rw [partialDeriv_eq_fderiv h1, partialDeriv_eq_fderiv h2]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
  · have hd : HasFDerivAt (fun z => ∏ i, F i z)
        (∑ i, (∏ i' ∈ Finset.univ.erase i, F i' z) • fderiv ℂ (F i) z) z :=
      HasFDerivAt.finsetProd fun i _ => (hat (hF i) z hz).hasFDerivAt
    rw [partialDeriv_eq_fderiv hd.differentiableAt, hd.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [partialDeriv_eq_fderiv (hat (hF i) z hz), mul_comm]
  · have hp : Differentiable ℂ fun z : ComplexCoordinates n => MvPolynomial.eval z p := by
      induction p using MvPolynomial.induction_on with
      | C a =>
        simp only [MvPolynomial.eval_C]
        exact differentiable_const a
      | add p q hp hq =>
        simp only [map_add]
        exact hp.add hq
      | mul_X p i hp =>
        simp only [map_mul, MvPolynomial.eval_X]
        exact hp.mul fun z => (hcoord z i).differentiableAt
    exact isHolomorphicScalar_of_differentiableOn isOpen_univ hp.differentiableOn
theorem chainRuleHolds_of (U : Set (ComplexCoordinates n)) : ChainRuleHolds U := by
  intro W V η hW hV hm hη
  have dV := differentiableOn_of_isHolomorphicScalar H hV
  have hU : IsOpen U := hV.1
  have hVat : ∀ z ∈ U, DifferentiableAt ℂ V z := fun z hz =>
    (dV z hz).differentiableAt (hU.mem_nhds hz)
  have key : ∀ z ∈ U, HasFDerivAt (η ∘ V) (deriv η (V z) • fderiv ℂ V z) z := fun z hz =>
    ((hη _ (hm hz)).differentiableAt (hW.mem_nhds (hm hz))).hasDerivAt.comp_hasFDerivAt z
      (hVat z hz).hasFDerivAt
  refine ⟨isHolomorphicScalar_of_differentiableOn hU
    fun z hz => (key z hz).differentiableAt.differentiableWithinAt, fun s z hz => ?_⟩
  rw [partialDeriv_eq_fderiv (key z hz).differentiableAt, (key z hz).fderiv]
  beta_reduce
  rw [partialDeriv_eq_fderiv (hVat z hz)]
  simp
theorem connectedOpenProperties_holds : ConnectedOpenProperties n := by
  refine ⟨fun O hO a ha => ⟨hO.connectedComponentIn, isConnected_connectedComponentIn_iff.2 ha⟩,
    fun O hO hc => ⟨fun F hF h0 => ?_, fun f hf hm => ?_⟩,
    fun w hw => Complex.exp_eq_one_iff.1 hw⟩
  · have dF := differentiableOn_of_isHolomorphicScalar H hF
    obtain ⟨a, ha⟩ := hc.nonempty
    refine ⟨F a, fun z hz => hO.is_const_of_fderiv_eq_zero hc.isPreconnected dF ?_ hz ha⟩
    intro w hw
    have hat := (dF w hw).differentiableAt (hO.mem_nhds hw)
    apply ContinuousLinearMap.coe_injective
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : ComplexCoordinates n) = x • ComplexCoordinates.stdBasisVector i := by
      ext k
      simp [ComplexCoordinates.stdBasisVector, Pi.single_apply]
    have h1 := h0 i hw
    rw [partialDeriv_eq_fderiv hat] at h1
    simp [hx, h1]
  · have hcne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero]
    have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) := by
      rw [isDiscrete_iff_discreteTopology]
      exact Int.isClosedEmbedding_coe_real.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology
    have hg : ContinuousOn (fun z => (f z / (2 * Real.pi * Complex.I)).re) O :=
      Complex.continuous_re.comp_continuousOn (hf.div_const _)
    have hval : ∀ z ∈ O, ∃ k : ℤ, f z = k * (2 * Real.pi * Complex.I) ∧
        (f z / (2 * Real.pi * Complex.I)).re = k := by
      intro z hz
      obtain ⟨k, hk⟩ := hm z hz
      refine ⟨k, hk, ?_⟩
      rw [hk, mul_div_cancel_right₀ _ hcne]
      simp
    have hmaps : MapsTo (fun z => (f z / (2 * Real.pi * Complex.I)).re) O
        (range ((↑) : ℤ → ℝ)) := fun z hz => by
      obtain ⟨k, -, hk⟩ := hval z hz
      exact ⟨k, hk.symm⟩
    obtain ⟨a, ha⟩ := hc.nonempty
    refine ⟨f a, fun z hz => ?_⟩
    have hconst := hc.isPreconnected.constant_of_mapsTo hdisc hg hmaps hz ha
    obtain ⟨k, hk, hk'⟩ := hval z hz
    obtain ⟨l, hl, hl'⟩ := hval a ha
    simp only [hk', hl'] at hconst
    have hkl : k = l := by exact_mod_cast hconst
    rw [hk, hl, hkl]
end Rules
theorem nonpositiveRayComplement_eq_slitPlane : nonpositiveRayComplement = Complex.slitPlane := by
  ext w
  constructor
  · intro hw
    rw [Complex.mem_slitPlane_iff]
    by_contra hc
    push Not at hc
    exact hw w.re hc.1 (Complex.ext rfl (by simpa using hc.2))
  · intro hw x hx h
    rw [Complex.mem_slitPlane_iff, h] at hw
    simp at hw
    linarith
theorem logExpProperties_holds : LogExpProperties := by
  have hlog : logPrincipal = Complex.log := rfl
  unfold LogExpProperties
  rw [nonpositiveRayComplement_eq_slitPlane, hlog]
  refine ⟨Complex.isOpen_slitPlane,
    fun w hw => (Complex.differentiableAt_log hw).differentiableWithinAt, fun w hw => ?_,
    fun w hw => Complex.exp_log (Complex.slitPlane_ne_zero hw), Complex.log_one,
    fun w hw => (Complex.ofReal_log hw.le).symm, fun w hw => ?_, Complex.differentiable_exp,
    Complex.deriv_exp, Complex.exp_ne_zero⟩
  · rw [(Complex.hasDerivAt_log hw).deriv, one_div]
  · have h := Complex.mem_slitPlane_of_norm_lt_one (z := w - 1) hw
    simpa using h
def monomialAway {M : Type*} [CommMonoid M] (j : Fin n) (y : Fin n → M)
    (α : PowerSeries.MultiIndex n) : M :=
  ∏ i ∈ Finset.univ.erase j, y i ^ α i
theorem monomial_eq_mul_monomialAway {M : Type*} [CommMonoid M] (j : Fin n) (y : Fin n → M)
    (α : PowerSeries.MultiIndex n) :
    PowerSeries.MultiIndex.monomial y α = y j ^ α j * monomialAway j y α :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
theorem monomialAway_congr {M : Type*} [CommMonoid M] {j : Fin n} {y y' : Fin n → M}
    {α α' : PowerSeries.MultiIndex n} (h : ∀ i, i ≠ j → y i ^ α i = y' i ^ α' i) :
    monomialAway j y α = monomialAway j y' α' :=
  Finset.prod_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)
theorem singleIndex_apply (j i : Fin n) : singleIndex j i = if i = j then 1 else 0 := by
  simp [singleIndex, indicatorIndex]
theorem add_singleIndex_self (β : PowerSeries.MultiIndex n) (j : Fin n) :
    (β + singleIndex j) j = β j + 1 := by
  simp [singleIndex_apply]
theorem add_singleIndex_of_ne (β : PowerSeries.MultiIndex n) {i j : Fin n} (h : i ≠ j) :
    (β + singleIndex j) i = β i := by
  simp [singleIndex_apply, h]
theorem exists_add_singleIndex {α : PowerSeries.MultiIndex n} {j : Fin n} (h : α j ≠ 0) :
    ∃ β : PowerSeries.MultiIndex n, β + singleIndex j = α := by
  refine ⟨α - singleIndex j, funext fun i => ?_⟩
  by_cases hi : i = j
  · subst hi
    simp only [Pi.add_apply, Pi.sub_apply, singleIndex_apply, if_true]
    omega
  · simp [singleIndex_apply, hi]
theorem monomial_along_basis (z : ComplexCoordinates n) (j : Fin n) (ζ : ℂ)
    (α : PowerSeries.MultiIndex n) :
    PowerSeries.MultiIndex.monomial (z + ζ • ComplexCoordinates.stdBasisVector j) α =
      (z j + ζ) ^ α j * monomialAway j z α := by
  rw [monomial_eq_mul_monomialAway j]
  congr 1
  · simp [ComplexCoordinates.stdBasisVector]
  · refine monomialAway_congr fun i hi => ?_
    simp [ComplexCoordinates.stdBasisVector, hi]
theorem norm_monomial (z : ComplexCoordinates n) (α : PowerSeries.MultiIndex n) :
    ‖PowerSeries.MultiIndex.monomial z α‖ = absMonomial z α := by
  simp [PowerSeries.MultiIndex.monomial, absMonomial]
theorem norm_monomialAway (j : Fin n) (z : ComplexCoordinates n) (α : PowerSeries.MultiIndex n) :
    ‖monomialAway j z α‖ = monomialAway j (fun i => ‖z i‖) α := by
  simp [monomialAway]
theorem absMonomial_nonneg (z : ComplexCoordinates n) (α : PowerSeries.MultiIndex n) :
    0 ≤ absMonomial z α := by
  unfold absMonomial PowerSeries.MultiIndex.monomial
  exact Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _
theorem monomialAway_norm_nonneg (j : Fin n) (z : ComplexCoordinates n)
    (α : PowerSeries.MultiIndex n) :
    0 ≤ monomialAway j (fun i => ‖z i‖) α :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
def IsAbsSummableEverywhere (a : PowerSeries.MultiIndex n → ℂ) : Prop :=
  ∀ z : ComplexCoordinates n, Summable fun α => ‖a α‖ * absMonomial z α
theorem summable_coeff_mul_monomial {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (z : ComplexCoordinates n) :
    Summable fun α => a α * PowerSeries.MultiIndex.monomial z α := by
  refine Summable.of_norm ((hS z).congr fun α => ?_)
  rw [norm_mul, norm_monomial]
theorem summable_shifted_coeff {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (j : Fin n) (z : ComplexCoordinates n) :
    Summable fun β : PowerSeries.MultiIndex n =>
      ((β j : ℝ) + 1) * ‖a (β + singleIndex j)‖ * absMonomial z β := by
  have hx : 0 ≤ ‖z j‖ := norm_nonneg _
  set W : ℝ := 2 * (‖z j‖ + 1) with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith
  let w : ComplexCoordinates n := Function.update z j (W : ℂ)
  have hs := (hS w).comp_injective (add_left_injective (singleIndex j))
  refine Summable.of_nonneg_of_le (fun β => ?_) (fun β => ?_) hs
  · have := absMonomial_nonneg z β
    positivity
  · simp only [Function.comp_def]
    have h1 : absMonomial w (β + singleIndex j) =
        W ^ (β j + 1) * monomialAway j (fun i => ‖z i‖) β := by
      rw [absMonomial, monomial_eq_mul_monomialAway j, add_singleIndex_self]
      congr 1
      · simp [w, abs_of_nonneg (by linarith : (0 : ℝ) ≤ W)]
      · refine monomialAway_congr fun i hi => ?_
        simp [w, hi, add_singleIndex_of_ne β hi]
    have h2 : absMonomial z β = ‖z j‖ ^ β j * monomialAway j (fun i => ‖z i‖) β :=
      monomial_eq_mul_monomialAway j _ β
    rw [h1, h2]
    have hP := monomialAway_norm_nonneg j z β
    have h3 : ((β j : ℝ) + 1) * ‖z j‖ ^ β j ≤ W ^ (β j + 1) := by
      have hm : ((β j : ℝ) + 1) ≤ 2 ^ β j := by
        exact_mod_cast (Nat.lt_two_pow_self : β j < 2 ^ β j)
      calc ((β j : ℝ) + 1) * ‖z j‖ ^ β j ≤ 2 ^ β j * (‖z j‖ + 1) ^ β j := by
            gcongr
            linarith
        _ = W ^ β j := by rw [hW, mul_pow]
        _ ≤ W ^ (β j + 1) := pow_le_pow_right₀ hW1 (Nat.le_succ _)
    calc ((β j : ℝ) + 1) * ‖a (β + singleIndex j)‖ *
          (‖z j‖ ^ β j * monomialAway j (fun i => ‖z i‖) β)
        = ‖a (β + singleIndex j)‖ * monomialAway j (fun i => ‖z i‖) β *
            (((β j : ℝ) + 1) * ‖z j‖ ^ β j) := by ring
      _ ≤ ‖a (β + singleIndex j)‖ * monomialAway j (fun i => ‖z i‖) β * W ^ (β j + 1) := by
          gcongr
      _ = ‖a (β + singleIndex j)‖ * (W ^ (β j + 1) * monomialAway j (fun i => ‖z i‖) β) := by
          ring
def derivCoeffs (j : Fin n) (a : PowerSeries.MultiIndex n → ℂ) :
    PowerSeries.MultiIndex n → ℂ :=
  fun β => ((β j : ℂ) + 1) * a (β + singleIndex j)
theorem isAbsSummableEverywhere_derivCoeffs {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (j : Fin n) :
    IsAbsSummableEverywhere (derivCoeffs j a) := by
  intro z
  refine (summable_shifted_coeff hS j z).congr fun β => ?_
  have h : ‖(β j : ℂ) + 1‖ = (β j : ℝ) + 1 := by
    have : ((β j : ℂ) + 1) = ((β j + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_natCast]
    push_cast
    rfl
  rw [derivCoeffs, norm_mul, h]
theorem hasDerivAt_powerSeriesSum_along_basis {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (z : ComplexCoordinates n) (j : Fin n) (y : ℂ) :
    HasDerivAt (fun ζ : ℂ => powerSeriesSum a (z + ζ • ComplexCoordinates.stdBasisVector j))
      (powerSeriesSum (derivCoeffs j a) (z + y • ComplexCoordinates.stdBasisVector j)) y := by
  set R : ℝ := ‖y‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  let g : PowerSeries.MultiIndex n → ℂ → ℂ := fun α ζ =>
    a α * ((z j + ζ) ^ α j * monomialAway j z α)
  let g' : PowerSeries.MultiIndex n → ℂ → ℂ := fun α ζ =>
    a α * (((α j : ℂ) * (z j + ζ) ^ (α j - 1)) * monomialAway j z α)
  let u : PowerSeries.MultiIndex n → ℝ := fun α =>
    ‖a α‖ * (((α j : ℝ) * (‖z j‖ + R) ^ (α j - 1)) * monomialAway j (fun i => ‖z i‖) α)
  have hg : ∀ α ζ, ζ ∈ Metric.ball (0 : ℂ) R → HasDerivAt (g α) (g' α ζ) ζ := by
    intro α ζ _
    have h1 : HasDerivAt (fun ζ : ℂ => z j + ζ) 1 ζ := (hasDerivAt_id ζ).const_add (z j)
    have h2 := h1.fun_pow (α j)
    have h3 := (h2.mul_const (monomialAway j z α)).const_mul (a α)
    refine h3.congr_deriv ?_
    change _ = a α * (((α j : ℂ) * (z j + ζ) ^ (α j - 1)) * monomialAway j z α)
    ring
  have hg' : ∀ α ζ, ζ ∈ Metric.ball (0 : ℂ) R → ‖g' α ζ‖ ≤ u α := by
    intro α ζ hζ
    have h1 : ‖z j + ζ‖ ≤ ‖z j‖ + R :=
      (norm_add_le _ _).trans (by gcongr; exact (mem_ball_zero_iff.1 hζ).le)
    simp only [g', u, norm_mul, norm_pow, Complex.norm_natCast, norm_monomialAway]
    have := monomialAway_norm_nonneg j z α
    gcongr
  have hu : Summable u := by
    let W : ComplexCoordinates n := Function.update z j ((‖z j‖ + R : ℝ) : ℂ)
    have hs := summable_shifted_coeff hS j W
    refine ((add_left_injective (singleIndex j)).summable_iff ?_).1 ?_
    · intro α hα
      have h0 : α j = 0 := by
        by_contra h
        obtain ⟨β, hβ⟩ := exists_add_singleIndex h
        exact hα ⟨β, hβ⟩
      simp [u, h0]
    · refine hs.congr fun β => ?_
      have hb : absMonomial W β =
          (‖z j‖ + R) ^ β j * monomialAway j (fun i => ‖z i‖) β := by
        rw [absMonomial, monomial_eq_mul_monomialAway j]
        congr 1
        · have hn : ‖((‖z j‖ + R : ℝ) : ℂ)‖ = ‖z j‖ + R := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          simp only [W, Function.update_self, hn]
        · refine monomialAway_congr fun i hi => ?_
          simp [W, hi]
      have hoff : monomialAway j (fun i => ‖z i‖) (β + singleIndex j) =
          monomialAway j (fun i => ‖z i‖) β :=
        monomialAway_congr fun i hi => by rw [add_singleIndex_of_ne β hi]
      simp only [Function.comp_def, u, add_singleIndex_self, hoff, hb]
      push_cast
      ring_nf
  have hg0 : Summable fun α => g α 0 :=
    (summable_coeff_mul_monomial hS z).congr fun α => by
      simp only [g, add_zero, ← monomial_eq_mul_monomialAway j]
  have hy : y ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, hRdef]
    linarith
  have hsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected hg hg' (Metric.mem_ball_self hR) hg0 hy
  have hF : (fun ζ : ℂ => powerSeriesSum a (z + ζ • ComplexCoordinates.stdBasisVector j)) =
      fun ζ => ∑' α, g α ζ := by
    funext ζ
    simp only [powerSeriesSum, indexSum, g, monomial_along_basis]
  have hsupp : Function.support (fun α => g' α y) ⊆
      range fun β : PowerSeries.MultiIndex n => β + singleIndex j := by
    intro α hα
    by_cases h : α j = 0
    · exact absurd (by simp [g', h]) hα
    · exact exists_add_singleIndex h
  have hD : powerSeriesSum (derivCoeffs j a) (z + y • ComplexCoordinates.stdBasisVector j) =
      ∑' α, g' α y := by
    rw [← (add_left_injective (singleIndex j)).tsum_eq hsupp]
    simp only [powerSeriesSum, indexSum]
    refine tsum_congr fun β => ?_
    have hoff : monomialAway j z (β + singleIndex j) = monomialAway j z β :=
      monomialAway_congr fun i hi => by rw [add_singleIndex_of_ne β hi]
    simp only [monomial_along_basis, g', add_singleIndex_self, hoff, derivCoeffs]
    push_cast
    ring_nf
  rw [hF, hD]
  exact hsum
theorem continuous_powerSeriesSum {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) : Continuous (powerSeriesSum a) := by
  rw [continuous_iff_continuousAt]
  intro z
  set R : ℝ := ‖z‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  have hon : ContinuousOn (powerSeriesSum a) (Metric.ball 0 R) := by
    refine continuousOn_tsum (u := fun α => ‖a α‖ * absMonomial (fun _ => (R : ℂ)) α)
      (fun α => ?_) (hS _) fun α x hx => ?_
    · refine Continuous.continuousOn ?_
      unfold PowerSeries.MultiIndex.monomial
      fun_prop
    · rw [norm_mul, norm_monomial]
      gcongr
      unfold absMonomial PowerSeries.MultiIndex.monomial
      refine Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg (x i)) _) fun i _ => ?_
      have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
      have h2 : ‖x‖ < R := mem_ball_zero_iff.1 hx
      have h3 : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
      beta_reduce
      rw [h3]
      gcongr
      linarith
  refine hon.continuousAt (Metric.isOpen_ball.mem_nhds ?_)
  rw [mem_ball_zero_iff, hRdef]
  linarith
theorem isEntireFun_powerSeriesSum {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) : IsEntireFun (powerSeriesSum a) :=
  isHolomorphicScalar_iff_lines.2 ⟨isOpen_univ, (continuous_powerSeriesSum hS).continuousOn,
    fun z _ j => Eventually.of_forall fun ζ =>
      (hasDerivAt_powerSeriesSum_along_basis hS z j ζ).differentiableAt⟩
theorem partialDeriv_powerSeriesSum {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (j : Fin n) :
    partialDeriv j (powerSeriesSum a) = powerSeriesSum (derivCoeffs j a) := by
  funext z
  have h := hasDerivAt_powerSeriesSum_along_basis hS z j 0
  rw [partialDeriv_eq_of_hasDerivAt h]
  simp
def iteratedDerivCoeffs (l : List (Fin n)) (a : PowerSeries.MultiIndex n → ℂ) :
    PowerSeries.MultiIndex n → ℂ :=
  l.foldr derivCoeffs a
theorem iteratedPartials_powerSeriesSum {a : PowerSeries.MultiIndex n → ℂ}
    (hS : IsAbsSummableEverywhere a) (l : List (Fin n)) :
    IsAbsSummableEverywhere (iteratedDerivCoeffs l a) ∧
      iteratedPartials l (powerSeriesSum a) = powerSeriesSum (iteratedDerivCoeffs l a) := by
  induction l with
  | nil => exact ⟨hS, rfl⟩
  | cons j l ih =>
    refine ⟨isAbsSummableEverywhere_derivCoeffs ih.1 j, ?_⟩
    change partialDeriv j (iteratedPartials l (powerSeriesSum a)) = _
    rw [ih.2, partialDeriv_powerSeriesSum ih.1]
    rfl
theorem factorial_add_singleIndex (β : PowerSeries.MultiIndex n) (j : Fin n) :
    PowerSeries.MultiIndex.factorial (β + singleIndex j) =
      (β j + 1) * PowerSeries.MultiIndex.factorial β := by
  unfold PowerSeries.MultiIndex.factorial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase (a := j) _ (fun i => (β i).factorial) (Finset.mem_univ j),
    add_singleIndex_self, Nat.factorial_succ, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun i hi =>
    by rw [add_singleIndex_of_ne β (Finset.ne_of_mem_erase hi)]
def countIndex (l : List (Fin n)) : PowerSeries.MultiIndex n := fun i => l.count i
theorem iteratedDerivCoeffs_mul_factorial (a : PowerSeries.MultiIndex n → ℂ)
    (l : List (Fin n)) :
    ∀ β : PowerSeries.MultiIndex n,
      iteratedDerivCoeffs l a β * (PowerSeries.MultiIndex.factorial β : ℂ) =
        (PowerSeries.MultiIndex.factorial (β + countIndex l) : ℂ) * a (β + countIndex l) := by
  induction l with
  | nil =>
    intro β
    have : β + countIndex ([] : List (Fin n)) = β := by
      funext i
      simp [countIndex]
    rw [this]
    exact mul_comm _ _
  | cons j l ih =>
    intro β
    have hidx : β + countIndex (j :: l) = β + singleIndex j + countIndex l := by
      funext i
      simp only [Pi.add_apply, countIndex, singleIndex_apply, List.count_cons, beq_iff_eq]
      by_cases h : i = j
      · simp only [h, if_true]
        omega
      · have h' : j ≠ i := fun e => h e.symm
        simp [h, h']
    have h1 := ih (β + singleIndex j)
    rw [hidx, ← h1, factorial_add_singleIndex]
    change ((β j : ℂ) + 1) * iteratedDerivCoeffs l a (β + singleIndex j) * _ = _
    push_cast
    ring
theorem countIndex_multiIndexSteps (α : PowerSeries.MultiIndex n) :
    countIndex (multiIndexSteps α) = α := by
  funext i
  simp only [countIndex, multiIndexSteps, List.count_flatMap]
  have h := Fin.sum_univ_def fun k : Fin n => if k = i then α k else 0
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
theorem powerSeriesSum_at_zero (c : PowerSeries.MultiIndex n → ℂ) :
    powerSeriesSum c 0 = c 0 := by
  unfold powerSeriesSum indexSum
  rw [tsum_eq_single 0]
  · simp [PowerSeries.MultiIndex.monomial]
  · intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      exact hα (funext h)
    have : PowerSeries.MultiIndex.monomial (0 : ComplexCoordinates n) α = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [this, mul_zero]
theorem termwiseDifferentiable_holds : TermwiseDifferentiable n := by
  intro a hS
  have hS' : IsAbsSummableEverywhere a := hS
  refine ⟨isEntireFun_powerSeriesSum hS', fun j z => ⟨?_, summable_shifted_coeff hS' j z⟩,
    fun α => ?_⟩
  · rw [partialDeriv_powerSeriesSum hS' j]
    rfl
  · have h := (iteratedPartials_powerSeriesSum hS' (multiIndexSteps α)).2
    have hf := iteratedDerivCoeffs_mul_factorial a (multiIndexSteps α) 0
    simp only [zero_add, countIndex_multiIndexSteps] at hf
    have h0 : PowerSeries.MultiIndex.factorial (0 : PowerSeries.MultiIndex n) = 1 := by
      simp [PowerSeries.MultiIndex.factorial]
    rw [h0, Nat.cast_one, mul_one] at hf
    rw [partialOfIndex, h, powerSeriesSum_at_zero, hf]
theorem standardFacts_holds (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    StandardFacts := fun _ _ U hU =>
  ⟨fun _ hF => partialDerivProperties_of_isHolomorphicScalar H hF, algebraRules_of_isOpen H hU,
    chainRuleHolds_of H U, termwiseDifferentiable_holds, logExpProperties_holds,
    connectedOpenProperties_holds H⟩
end ComplexVariables.HolomorphicFacts
end YangMills.Construction
