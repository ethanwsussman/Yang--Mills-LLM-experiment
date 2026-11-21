import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinatesProof
import YangMills.Construction.FormsOnATorus.FormsAlongPathsOfATorus
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import Mathlib
set_option autoImplicit false

noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions TorusFields FlatLinearization
def ContourAverageCurlBound : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L]
    (ξ : RealOneForm (n * L)), curlEnergy (fun c : TorusBond n => contourAverage L ξ c) ≤ C * curlEnergy ξ
end YangMills.Construction.RunningCouplingSlope
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.RunningCouplingSlope
open FlatLinearization TorusFields TorusContours PathForms
variable {m n L : ℕ}
private def quaternionForm (ξ : RealOneForm m) : TorusBond m → ℍ[ℝ] := fun b => ((ξ b : ℝ) : ℍ[ℝ])
private theorem quaternion_re_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_finset_sum <;> assumption
private theorem re_formPathSum (ξ : RealOneForm m) (x : TorusSite m) (l : List BlockAverages.PathStep) :
    (formPathSum (quaternionForm ξ) x l).re = pathIntegral ξ x l := by
  induction l generalizing x with
  | nil => simp [formPathSum, pathIntegral]
  | cons st r ih =>
    have e : stepEndpoint x st = x + stepShift m st := by
      rcases st with ⟨i, c⟩
      cases c <;> simp [stepEndpoint, stepShift, sub_eq_add_neg]
    rw [formPathSum, pathIntegral, e, ← ih]
    rcases st with ⟨i, c⟩
    cases c <;> simp [stepForm, quaternionForm]
private theorem slope_blockCentreSite_eq [NeZero n] (y : TorusSite n) :
    SlopeCoefficient.blockCentreSite L y = TorusBlocks.blockCentreSite L y := by
  funext i
  simp only [SlopeCoefficient.blockCentreSite, TorusBlocks.blockCentreSite, siteOfInt]
  rw [← ZMod.natCast_val (R := ℤ) (y i)]
  push_cast
  rfl
abbrev _root_.YangMills.SharedProofs.p7467 := @slope_blockCentreSite_eq
private theorem re_contourMean [NeZero n] (ξ : RealOneForm (n * L)) (c : TorusBond n) :
    (contourMean L (quaternionForm ξ) c).re = contourAverage L ξ c := by
  unfold contourMean contourAverage contourIndex TorusContours.contourWeight
  rw [Quaternion.re_smul, Finset.sum_product, quaternion_re_sum, smul_eq_mul, slope_blockCentreSite_eq]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [quaternion_re_sum]
  exact Finset.sum_congr rfl fun π _ => re_formPathSum ξ _ _
private theorem plaquetteCurl_contourAverage [NeZero n] [NeZero L] (hL : Odd L) (ξ : RealOneForm (n * L))
    (Y : TorusSite n) (μ ν : Fin 4) :
    plaquetteCurl (fun c : TorusBond n => contourAverage L ξ c) Y μ ν =
      ((L : ℝ) ^ 4)⁻¹ * ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        plaquetteCurl ξ (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ
          + b • unitStep (n * L) ν) μ ν := by
  have key := congrArg (fun q : ℍ[ℝ] => q.re) (formCurl_contourMean hL (quaternionForm ξ) Y μ ν)
  simp only [formCurl, Quaternion.re_sub, Quaternion.re_add, re_contourMean, Quaternion.re_smul, smul_eq_mul,
    quaternion_re_sum, squareCurlSum] at key
  simp only [plaquetteCurl]
  rw [key]
  congr 1
private theorem sum_blocks_centredCube [NeZero n] [NeZero L] [NeZero (n * L)] (hL : Odd L)
    (g : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ h ∈ BlockAverages.centredCube L, g (TorusBlocks.blockCentreSite L Y + siteOfInt h)
      = ∑ x, g x := by
  classical
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (TorusSite (n * L)))) (g := TorusLumps.parentBlock L)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hs : Finset.univ.filter (fun x : TorusSite (n * L) => TorusLumps.parentBlock L x = Y) =
      (BlockAverages.centredCube L).image
        (fun h : Fin 4 → ℤ => (TorusBlocks.blockCentreSite L Y + siteOfInt h : TorusSite (n * L))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have := mem_image_centredCube hL x
      rwa [hx] at this
    · intro hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      exact parentBlock_blockCentreSite_add_of_mem hL Y hh
  rw [hs, Finset.sum_image (blockCentreSite_add_injOn hL Y)]
private theorem plaquetteCurl_contourAverage_sq_le [NeZero n] [NeZero L] (hL : Odd L)
    (ξ : RealOneForm (n * L)) (Y : TorusSite n) (μ ν : Fin 4) :
    plaquetteCurl (fun c : TorusBond n => contourAverage L ξ c) Y μ ν ^ 2 ≤
      ((L : ℝ) ^ 2)⁻¹ * ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        plaquetteCurl ξ (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ
          + b • unitStep (n * L) ν) μ ν ^ 2 := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne L))
  set F : (Fin 4 → ℤ) × ℕ × ℕ → ℝ := fun p =>
    plaquetteCurl ξ (TorusBlocks.blockCentreSite L Y + siteOfInt p.1 + p.2.1 • unitStep (n * L) μ
      + p.2.2 • unitStep (n * L) ν) μ ν with hF
  set S : Finset ((Fin 4 → ℤ) × ℕ × ℕ) :=
    BlockAverages.centredCube L ×ˢ (Finset.range L ×ˢ Finset.range L) with hS
  have e1 : ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      plaquetteCurl ξ (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ
        + b • unitStep (n * L) ν) μ ν = ∑ p ∈ S, F p := by
    rw [hS, Finset.sum_product]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_product]
  have e2 : ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      plaquetteCurl ξ (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ
        + b • unitStep (n * L) ν) μ ν ^ 2 = ∑ p ∈ S, F p ^ 2 := by
    rw [hS, Finset.sum_product]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_product]
  have hcard : (S.card : ℝ) = (L : ℝ) ^ 6 := by
    rw [hS, Finset.card_product, Finset.card_product, Finset.card_range, card_centredCube hL]
    push_cast
    ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := F)
  rw [hcard] at hcs
  rw [plaquetteCurl_contourAverage hL, e1, e2, mul_pow]
  calc (((L : ℝ) ^ 4)⁻¹) ^ 2 * (∑ p ∈ S, F p) ^ 2
      ≤ (((L : ℝ) ^ 4)⁻¹) ^ 2 * ((L : ℝ) ^ 6 * ∑ p ∈ S, F p ^ 2) := by gcongr
    _ = ((L : ℝ) ^ 2)⁻¹ * ∑ p ∈ S, F p ^ 2 := by
        field_simp
private theorem plane_curlEnergy_le [NeZero n] [NeZero L] [NeZero (n * L)] (hL : Odd L)
    (ξ : RealOneForm (n * L)) (μ ν : Fin 4) :
    ∑ Y : TorusSite n, plaquetteCurl (fun c : TorusBond n => contourAverage L ξ c) Y μ ν ^ 2 ≤
      ∑ x : TorusSite (n * L), plaquetteCurl ξ x μ ν ^ 2 := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne L))
  set g : TorusSite (n * L) → ℝ := fun x => plaquetteCurl ξ x μ ν ^ 2 with hg
  have shift : ∀ a b : ℕ, ∑ Y : TorusSite n, ∑ h ∈ BlockAverages.centredCube L,
      g (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ + b • unitStep (n * L) ν)
        = ∑ x, g x := by
    intro a b
    have h1 := sum_blocks_centredCube hL (fun x => g (x + a • unitStep (n * L) μ + b • unitStep (n * L) ν))
    rw [h1]
    have h2 : ∀ x : TorusSite (n * L), x + a • unitStep (n * L) μ + b • unitStep (n * L) ν =
        (Equiv.addRight (a • unitStep (n * L) μ + b • unitStep (n * L) ν)) x := by
      intro x
      simp [add_assoc]
    simp_rw [h2]
    exact Equiv.sum_comp (Equiv.addRight (a • unitStep (n * L) μ + b • unitStep (n * L) ν)) g
  calc ∑ Y : TorusSite n, plaquetteCurl (fun c : TorusBond n => contourAverage L ξ c) Y μ ν ^ 2
      ≤ ∑ Y : TorusSite n, ((L : ℝ) ^ 2)⁻¹ * ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L,
          ∑ b ∈ Finset.range L,
          g (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ + b • unitStep (n * L) ν) :=
        Finset.sum_le_sum fun Y _ => plaquetteCurl_contourAverage_sq_le hL ξ Y μ ν
    _ = ((L : ℝ) ^ 2)⁻¹ * ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, ∑ Y : TorusSite n,
          ∑ h ∈ BlockAverages.centredCube L,
          g (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ + b • unitStep (n * L) ν) := by
        rw [← Finset.mul_sum]
        congr 1
        have e : ∀ Y : TorusSite n, ∑ h ∈ BlockAverages.centredCube L, ∑ a ∈ Finset.range L,
            ∑ b ∈ Finset.range L,
            g (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ + b • unitStep (n * L) ν) =
            ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, ∑ h ∈ BlockAverages.centredCube L,
              g (TorusBlocks.blockCentreSite L Y + siteOfInt h + a • unitStep (n * L) μ
                + b • unitStep (n * L) ν) := by
          intro Y
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
        simp_rw [e]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, g x := by
        simp_rw [shift]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
private theorem curlEnergy_eq_sum_planes [NeZero m] (ξ : RealOneForm m) :
    curlEnergy ξ = ∑ μ : Fin 4, ∑ ν : Fin 4,
      if μ < ν then ∑ x : TorusSite m, plaquetteCurl ξ x μ ν ^ 2 else 0 := by
  unfold curlEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp
theorem contourAverageCurlBound : ContourAverageCurlBound := by
  intro L hL
  refine ⟨1, one_pos, Filter.Eventually.of_forall fun n _ _ ξ => ?_⟩
  rw [one_mul, curlEnergy_eq_sum_planes, curlEnergy_eq_sum_planes]
  refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => ?_
  split_ifs
  · exact plane_curlEnergy_le hL.1 ξ μ ν
  · exact le_rfl
end YangMills.Construction.RunningCouplingSlope
end
