import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAndThePrincipalLogarithm
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ContDiff
namespace YangMills.Construction.SeveralComplexVariables.HolomorphicContDiff
variable {ι : Type} [Fintype ι]
omit [Fintype ι] in
lemma eventually_add_smul_basisVector_mem {U : Set (ι → ℂ)} (hU : IsOpen U) {z : ι → ℂ}
    (hz : z ∈ U) (k : ι) :
    ∀ᶠ t in 𝓝 (0 : ℂ), z + t • basisVector k ∈ U := by
  have hcont : Continuous fun t : ℂ => z + t • basisVector k := by fun_prop
  exact hcont.continuousAt.eventually (hU.mem_nhds (by simpa using hz))
omit [Fintype ι] in
lemma differentiableAt_add_smul_basisVector {U : Set (ι → ℂ)} {f : (ι → ℂ) → ℂ}
    (hf : IsHolomorphicOnOpen U f) (z : ι → ℂ) (k : ι) {t₀ : ℂ}
    (ht₀ : z + t₀ • basisVector k ∈ U) :
    DifferentiableAt ℂ (fun t : ℂ => f (z + t • basisVector k)) t₀ := by
  have h0 := (hf.2.2 _ ht₀ k).self_of_nhds
  have hs : DifferentiableAt ℂ (fun t : ℂ => t - t₀) t₀ := differentiableAt_id.sub_const t₀
  have hcomp := DifferentiableAt.comp
    (g := fun s : ℂ => f (z + t₀ • basisVector k + s • basisVector k)) t₀ (by simpa using h0) hs
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Function.comp]
  congr 1
  rw [add_assoc, ← add_smul]
  simp
lemma differentiableOn_of_isHolomorphicOnOpen
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (ι → ℂ)} {f : (ι → ℂ) → ℂ} (hf : IsHolomorphicOnOpen U f) :
    DifferentiableOn ℂ f U := by
  classical
  let e := Fintype.equivFin ι
  let ofFin : (Fin (Fintype.card ι) → ℂ) → ι → ℂ := fun w i => w (e i)
  let toFin : (ι → ℂ) → Fin (Fintype.card ι) → ℂ := fun z j => z (e.symm j)
  have hofFin : Continuous ofFin := continuous_pi fun i => continuous_apply _
  have hinv : ∀ z, ofFin (toFin z) = z := fun z => by
    funext i
    simp [ofFin, toFin]
  let g : Coordinates.ComplexCoordinates (Fintype.card ι) → Coordinates.ComplexCoordinates 1 :=
    fun w _ => f (ofFin w)
  let V : Set (Coordinates.ComplexCoordinates (Fintype.card ι)) := ofFin ⁻¹' U
  have hV : IsOpen V := hf.1.preimage hofFin
  have hline : ∀ (w : Coordinates.ComplexCoordinates (Fintype.card ι)) (j : Fin (Fintype.card ι))
      (t : ℂ),
      ofFin (w + t • Coordinates.ComplexCoordinates.stdBasisVector j)
        = ofFin w + t • basisVector (e.symm j) := by
    intro w j t
    funext i
    by_cases hij : e i = j
    · have : i = e.symm j := by rw [← hij]; simp
      simp [ofFin, Coordinates.ComplexCoordinates.stdBasisVector, basisVector, this]
    · have : i ≠ e.symm j := fun hc => hij (by rw [hc]; simp)
      simp [ofFin, Coordinates.ComplexCoordinates.stdBasisVector, basisVector, hij, this]
  have hg : Coordinates.ComplexCoordinates.IsHolomorphicIn V g := by
    refine ⟨hV, continuousOn_pi.2 fun _ => hf.2.1.comp hofFin.continuousOn fun w hw => hw, ?_⟩
    intro w hw j
    filter_upwards [eventually_add_smul_basisVector_mem hf.1 (show ofFin w ∈ U from hw)
      (e.symm j)] with t ht
    refine differentiableAt_pi.2 fun _ => ?_
    simp only [g, hline]
    exact differentiableAt_add_smul_basisVector hf (ofFin w) (e.symm j) ht
  obtain ⟨-, -, hD, -, -⟩ := (H.1 _ V hV).1 1 g hg
  have hmaps : MapsTo toFin U V := fun z hz => by
    show ofFin (toFin z) ∈ U
    rwa [hinv]
  have hrepr : ∀ z, f z = g (toFin z) 0 := fun z => by simp [g, hinv]
  intro z hz
  obtain ⟨D, hDz⟩ := hD _ (hmaps hz)
  have hgz : DifferentiableAt ℂ g (toFin z) :=
    (hasFDerivAt_of_restrictScalars ℝ hDz rfl).differentiableAt
  have htoFin : DifferentiableAt ℂ toFin z :=
    differentiableAt_pi.2 fun j => differentiableAt_apply (e.symm j) z
  have hcomp : DifferentiableAt ℂ (fun z' => g (toFin z') 0) z :=
    (differentiableAt_pi.1 hgz 0).comp z htoFin
  exact (hcomp.congr_of_eventuallyEq (Eventually.of_forall hrepr)).differentiableWithinAt
lemma partialDeriv_eq_fderiv_apply {f : (ι → ℂ) → ℂ} {z : ι → ℂ} (k : ι)
    (hd : DifferentiableAt ℂ f z) :
    partialDeriv k f z = fderiv ℂ f z (basisVector k) := by
  have hl : HasDerivAt (fun t : ℂ => z + t • basisVector k) (basisVector k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (basisVector k)).const_add z
  have hz0 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • basisVector k) := by
    simpa using hd.hasFDerivAt
  exact (hz0.comp_hasDerivAt 0 hl).deriv
lemma sum_smul_basisVector (v : ι → ℂ) : ∑ k, v k • basisVector k = v := by
  classical
  funext i
  simp [Finset.sum_apply, basisVector]
lemma fderiv_apply_eq_sum_partialDeriv {f : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (hd : DifferentiableAt ℂ f z) (v : ι → ℂ) :
    fderiv ℂ f z v = ∑ k, v k * partialDeriv k f z := by
  conv_lhs => rw [← sum_smul_basisVector v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, partialDeriv_eq_fderiv_apply k hd, smul_eq_mul]
lemma contDiffOn_nat_of_isHolomorphicOnOpen [Nonempty ι]
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (P : HolomorphicCalculus.PartialDerivsHolomorphicAndCommute)
    {U : Set (ι → ℂ)} (n : ℕ) :
    ∀ f : (ι → ℂ) → ℂ, IsHolomorphicOnOpen U f → ContDiffOn ℂ n f U := by
  induction n with
  | zero =>
    intro f hf
    have h0 : ContDiffOn ℂ 0 f U := contDiffOn_zero.2 hf.2.1
    simpa using h0
  | succ n ih =>
    intro f hf
    have hd := differentiableOn_of_isHolomorphicOnOpen H hf
    have hU : IsOpen U := hf.1
    push_cast
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨hd, by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun v => ?_
    have hsum : ContDiffOn ℂ n (fun z => ∑ k, v k * partialDeriv k f z) U :=
      ContDiffOn.sum fun k _ => contDiffOn_const.mul (ih _ ((P ι U hU f hf).1 k))
    exact hsum.congr fun z hz =>
      fderiv_apply_eq_sum_partialDeriv (hd.differentiableAt (hU.mem_nhds hz)) v
theorem statement_holds (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (C : HolomorphicCalculus.Statement) : Statement := by
  intro ι _ _ U f hf
  exact contDiffOn_infty.2 fun n => contDiffOn_nat_of_isHolomorphicOnOpen H C.2.1 n f hf
end YangMills.Construction.SeveralComplexVariables.HolomorphicContDiff
