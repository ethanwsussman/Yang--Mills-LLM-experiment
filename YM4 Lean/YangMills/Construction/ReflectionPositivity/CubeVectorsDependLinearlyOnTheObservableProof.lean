import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.CorrelationsOfTwoLinkCubes
import YangMills.Construction.ReflectionPositivity.CubeVectorsDependLinearlyOnTheObservable
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField IsBoundedObservable LatticePoint
  UnitLatticeSymmetry halfSpaceLocalObservables observableSupNorm shift unitRegionObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (UnitMirrorPair unitPositiveClass
  linkReflect siteReflect)
namespace CubeVectorLinearity
private theorem reflect_reflect_actOn
    (hSym : MirrorHyperplanes.SymmetryActionAndReflections)
    (P : UnitMirrorPair) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    P.reflect.actOn (P.reflect.actOn F) = F := by
  have hid := (hSym.2.2.2.2.2.2.2.2.1 P).2.1
  have hinv : Function.LeftInverse P.reflect.toFun P.reflect.toFun := fun x =>
    congrFun hid x
  exact (hSym.2.2.2.2.2.1 P.reflect P.reflect F F hF hF).2.1 P.reflect ⟨hinv, hinv⟩
private theorem actOn_evenPartUnder (g : UnitLatticeSymmetry)
    {B : GaugeField (1 : ℝ) → ℂ} (hg : g.actOn (g.actOn B) = B) :
    g.actOn (evenPartUnder g B) = evenPartUnder g B := by
  have hexp : g.actOn (evenPartUnder g B) =
      (1 / 2 : ℂ) • (g.actOn B + g.actOn (g.actOn B)) := rfl
  rw [hexp, hg, add_comm]
  rfl
private theorem actOn_oddPartUnder (g : UnitLatticeSymmetry)
    {B : GaugeField (1 : ℝ) → ℂ} (hg : g.actOn (g.actOn B) = B) :
    g.actOn (oddPartUnder g B) = -oddPartUnder g B := by
  have hexp : g.actOn (oddPartUnder g B) =
      (1 / 2 : ℂ) • (g.actOn B - g.actOn (g.actOn B)) := rfl
  rw [hexp, hg, oddPartUnder, ← smul_neg, neg_sub]
private theorem eq_evenPart_add_oddPart (g : UnitLatticeSymmetry) (B : GaugeField (1 : ℝ) → ℂ) :
    B = evenPartUnder g B + oddPartUnder g B := by
  funext U
  simp only [evenPartUnder, oddPartUnder, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  ring
private theorem evenPartUnder_mem (W : Submodule ℂ (GaugeField (1 : ℝ) → ℂ))
    (g : UnitLatticeSymmetry) {B : GaugeField (1 : ℝ) → ℂ} (hB : B ∈ W)
    (hgB : g.actOn B ∈ W) : evenPartUnder g B ∈ W :=
  W.smul_mem _ (W.add_mem hB hgB)
private theorem oddPartUnder_mem (W : Submodule ℂ (GaugeField (1 : ℝ) → ℂ))
    (g : UnitLatticeSymmetry) {B : GaugeField (1 : ℝ) → ℂ} (hB : B ∈ W)
    (hgB : g.actOn B ∈ W) : oddPartUnder g B ∈ W :=
  W.smul_mem _ (W.sub_mem hB hgB)
private theorem exists_linearMap_obsClass_shift (q : ReflectionPair) (c : unitPositiveClass)
    (μ : Fin 4) (a : LatticePoint (1 : ℝ)) (W : Submodule ℂ (GaugeField (1 : ℝ) → ℂ))
    (hW : ∀ B ∈ W, (shift a).actOn B ∈ halfSpaceLocalObservables μ) :
    ∃ Λ : W →ₗ[ℂ] q.Hilb c μ, ∀ B : W,
      Λ B = q.obsClass c μ ((shift a).actOn (B : GaugeField (1 : ℝ) → ℂ)) := by
  let T : W →ₗ[ℂ] halfSpaceLocalObservables μ :=
    { toFun := fun B => ⟨(shift a).actOn (B : GaugeField (1 : ℝ) → ℂ), hW B B.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨(FormHilbert.formClass (q.pairForm c μ)).comp T, fun B => ?_⟩
  rw [ReflectionPair.obsClass, dif_pos (hW B B.2)]
  rfl
private theorem apply_eq_add_of_linear {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (GaugeField (1 : ℝ) → ℂ)) (Λ : W →ₗ[ℂ] V)
    (f : (GaugeField (1 : ℝ) → ℂ) → V) (hΛ : ∀ B : W, Λ B = f B)
    {B C D : GaugeField (1 : ℝ) → ℂ} (hC : C ∈ W) (hD : D ∈ W) (hsum : B = C + D) :
    f B = f C + f D := by
  have hB : B ∈ W := hsum ▸ W.add_mem hC hD
  have hpt : (⟨B, hB⟩ : W) = ⟨C, hC⟩ + ⟨D, hD⟩ := Subtype.ext hsum
  have := congrArg Λ hpt
  rw [map_add, hΛ, hΛ, hΛ] at this
  exact this
private theorem cubeReflectionNorm_nonneg' (c : unitPositiveClass) (r : ℕ+)
    (B : GaugeField (1 : ℝ) → ℂ) : 0 ≤ cubeReflectionNorm c r B := by
  obtain ⟨w, hw⟩ := (isGreatest_cubeReflectionNorm c r B).1
  rw [← hw]
  positivity
private def siteReflectElement (μ : Fin 4) : axisReflectionGroup :=
  ⟨siteReflectPerm μ, Subgroup.subset_closure ⟨μ, rfl⟩⟩
private theorem le_of_sqrt_seminorm_half {W : Submodule ℂ (GaugeField (1 : ℝ) → ℂ)}
    (n : (GaugeField (1 : ℝ) → ℂ) → ℝ) (hn : ∀ B, 0 ≤ n B) (s : Seminorm ℂ W)
    (hs : ∀ B : W, s B = n B ^ (1 / 2 : ℝ)) (B G : W) (hG : n G = n B) (Y : W)
    (hY : s Y ≤ ‖(1 / 2 : ℂ)‖ * (s B + s G)) : n Y ≤ n B := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf, hs G, hG, ← hs B] at hY
  have hroot : n Y ^ (1 / 2 : ℝ) ≤ n B ^ (1 / 2 : ℝ) := by
    rw [← hs Y, ← hs B]
    linarith
  exact (Real.rpow_le_rpow_iff (hn _) (hn _) (by norm_num)).mp hroot
private theorem siteCase_holds (hSym : MirrorHyperplanes.SymmetryActionAndReflections)
    (hSite : SiteReflectionPair.Conclusion) (c : unitPositiveClass) (μ : Fin 4)
    (r : ℕ+) : SiteCase c μ r := by
  obtain ⟨hCube, -, -, -, -, hNorm⟩ := hSite c μ r
  have hsh : ∀ B ∈ cubeObservableSpace r,
      (shift ((r : ℕ) • InfiniteLattice.axisStep (1 : ℝ) μ)).actOn B ∈
        halfSpaceLocalObservables μ := fun B hB => ((hCube.2.2.2.2.2 B hB).2).1
  obtain ⟨Λ, hΛ⟩ := exists_linearMap_obsClass_shift ReflectionPair.site c μ _
    (cubeObservableSpace r) hsh
  have hrefl : ∀ B ∈ cubeObservableSpace r,
      (siteReflect μ).actOn B ∈ cubeObservableSpace r := fun B hB =>
    hCube.2.2.2.2.1 (siteReflectElement μ) B hB
  refine ⟨rfl, ⟨Λ, hΛ⟩, fun B hB => ?_⟩
  have hB' : B ∈ cubeObservableSpace r := hB
  have hgB := hrefl B hB'
  have heven := evenPartUnder_mem _ (siteReflect μ) hB' hgB
  have hodd := oddPartUnder_mem _ (siteReflect μ) hB' hgB
  have hinv : (siteReflect μ).actOn ((siteReflect μ).actOn B) = B :=
    reflect_reflect_actOn hSym _ hB.1
  obtain ⟨⟨s, hs⟩, hpres, -⟩ := hNorm
  have hs' : ∀ D : cubeObservableSpace r,
      s D = cubeReflectionNorm c r (D : GaugeField (1 : ℝ) → ℂ) ^ (1 / 2 : ℝ) := hs
  have hG : cubeReflectionNorm c r ((siteReflect μ).actOn B) =
      cubeReflectionNorm c r B := hpres (siteReflectElement μ) B hB
  refine ⟨heven, hodd, actOn_evenPartUnder _ hinv, actOn_oddPartUnder _ hinv,
    apply_eq_add_of_linear _ Λ (cubeVector c μ r) hΛ heven hodd (eq_evenPart_add_oddPart _ B), ?_, ?_⟩
  · refine le_of_sqrt_seminorm_half (cubeReflectionNorm c r) (cubeReflectionNorm_nonneg' c r) s hs'
      ⟨B, hB'⟩ ⟨_, hgB⟩ hG ⟨_, heven⟩ ?_
    have hpt : (⟨_, heven⟩ : cubeObservableSpace r) =
        (1 / 2 : ℂ) • ((⟨B, hB'⟩ : cubeObservableSpace r) + ⟨_, hgB⟩) := rfl
    rw [hpt, map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (map_add_le_add s _ _) (norm_nonneg _)
  · refine le_of_sqrt_seminorm_half (cubeReflectionNorm c r) (cubeReflectionNorm_nonneg' c r) s hs'
      ⟨B, hB'⟩ ⟨_, hgB⟩ hG ⟨_, hodd⟩ ?_
    have hpt : (⟨_, hodd⟩ : cubeObservableSpace r) =
        (1 / 2 : ℂ) • ((⟨B, hB'⟩ : cubeObservableSpace r) - ⟨_, hgB⟩) := rfl
    rw [hpt, map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (map_sub_le_add s _ _) (norm_nonneg _)
private theorem observableSupNorm_le_of_half {B Y : GaugeField (1 : ℝ) → ℂ}
    (hB : IsBoundedObservable B) (g : UnitLatticeSymmetry)
    (hY : ∀ U, ‖Y U‖ ≤ (1 / 2 : ℝ) * (‖B U‖ + ‖g.actOn B U‖)) :
    observableSupNorm Y ≤ observableSupNorm B := by
  obtain ⟨-, K, hK⟩ := hB
  have hbdd : BddAbove (Set.range fun U => ‖B U‖) :=
    ⟨K, by rintro _ ⟨U, rfl⟩; exact hK U⟩
  have hpt : ∀ U, ‖B U‖ ≤ observableSupNorm B := fun U => le_ciSup hbdd U
  have hnn : 0 ≤ observableSupNorm B := Real.iSup_nonneg fun _ => norm_nonneg _
  refine Real.iSup_le (fun U => (hY U).trans ?_) hnn
  have h₁ := hpt U
  have h₂ : ‖g.actOn B U‖ ≤ observableSupNorm B := hpt _
  linarith
private theorem linkCase_holds (hSym : MirrorHyperplanes.SymmetryActionAndReflections)
    (hLink : LinkBlockCorrelationTheorem) (c : unitPositiveClass) (μ : Fin 4)
    (r : ℕ+) : LinkCase c μ r := by
  have hmem : ∀ B ∈ unitRegionObservables (DirectionPictures.linkBlock r),
      (linkReflect μ).actOn B ∈ unitRegionObservables (DirectionPictures.linkBlock r) ∧
      (shift ((r : ℕ) • InfiniteLattice.axisStep (1 : ℝ) μ)).actOn B ∈
        halfSpaceLocalObservables μ := fun B hB =>
    have hc := (hLink c r B B hB hB 0).1 μ
    ⟨hc.2.1, hc.2.2.2.1⟩
  obtain ⟨Λ, hΛ⟩ := exists_linearMap_obsClass_shift ReflectionPair.link c μ _
    (linkBlockObservables r) fun B hB => (hmem B hB).2
  refine ⟨rfl, ⟨Λ, hΛ⟩, fun B hB => ?_⟩
  have hB' : B ∈ linkBlockObservables r := hB
  have hgB : (linkReflect μ).actOn B ∈ linkBlockObservables r := (hmem B hB).1
  have heven := evenPartUnder_mem _ (linkReflect μ) hB' hgB
  have hodd := oddPartUnder_mem _ (linkReflect μ) hB' hgB
  have hinv : (linkReflect μ).actOn ((linkReflect μ).actOn B) = B :=
    reflect_reflect_actOn hSym _ hB.1
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  refine ⟨heven, hodd, actOn_evenPartUnder _ hinv, actOn_oddPartUnder _ hinv,
    apply_eq_add_of_linear _ Λ (linkBlockVector c μ r) hΛ heven hodd (eq_evenPart_add_oddPart _ B), ?_, ?_⟩
  · refine observableSupNorm_le_of_half hB.1 (linkReflect μ) fun U => ?_
    simp only [evenPartUnder, Pi.smul_apply, Pi.add_apply, norm_smul, hhalf]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
  · refine observableSupNorm_le_of_half hB.1 (linkReflect μ) fun U => ?_
    simp only [oddPartUnder, Pi.smul_apply, Pi.sub_apply, norm_smul, hhalf]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
theorem statement_holds
    (hSym : MirrorHyperplanes.SymmetryActionAndReflections)
    (hSite : SiteReflectionPair.Conclusion) (hLink : LinkBlockCorrelationTheorem) :
    Statement := fun c μ r => ⟨siteCase_holds hSym hSite c μ r, linkCase_holds hSym hLink c μ r⟩
end CubeVectorLinearity
end YangMills.Construction.ReflectionPositivity.DirectionPictures
