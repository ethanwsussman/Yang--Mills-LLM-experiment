import YangMills.Construction.Matrices.CompositesOfDifferentiableMapsOnPowersOfGProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.GraphsInTheLeftChartAreSubmanifolds
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartGraphProof
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.PowerExpCharts
section Complements
variable {σ : Type} [Fintype σ]
theorem exists_linear_coords (E : Submodule ℝ (σ → ComplexMatrix2)) :
    ∃ (d : ℕ) (ι : (Fin d → ℝ) →L[ℝ] (σ → ComplexMatrix2))
      (κ : (σ → ComplexMatrix2) →L[ℝ] (Fin d → ℝ)),
      (∀ u, ι u ∈ E) ∧ (∀ u, κ (ι u) = u) ∧ ∀ x ∈ E, ι (κ x) = x := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E
  let e := (Module.finBasis ℝ E).equivFun
  let pr := Submodule.linearProjOfIsCompl E C hC
  have hpr : ∀ x : E, pr x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hC x
  refine ⟨Module.finrank ℝ E,
    LinearMap.toContinuousLinearMap (E.subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ pr), fun u => ?_, fun u => ?_,
    fun x hx => ?_⟩
  · exact (e.symm u).2
  · change e (pr ((e.symm u : E) : σ → ComplexMatrix2)) = u
    rw [hpr, LinearEquiv.apply_symm_apply]
  · change ((e.symm (e (pr x)) : E) : σ → ComplexMatrix2) = x
    rw [LinearEquiv.symm_apply_apply, hpr ⟨x, hx⟩]
theorem isCompl_sup_right_of_isCompl_sup {E E' C : Submodule ℝ (σ → ComplexMatrix2)}
    (hinf : E ⊓ E' = ⊥) (hC : IsCompl (E ⊔ E') C) : IsCompl E (E' ⊔ C) :=
  ⟨Disjoint.disjoint_sup_right_of_disjoint_sup_left (disjoint_iff.2 hinf) hC.disjoint,
    codisjoint_iff.2 (by rw [← sup_assoc]; exact hC.sup_eq_top)⟩
theorem exists_sum_projections {E E' : Submodule ℝ (σ → ComplexMatrix2)} (hinf : E ⊓ E' = ⊥) :
    ∃ π π' : (σ → ComplexMatrix2) →L[ℝ] (σ → ComplexMatrix2),
      ∀ x ∈ E, ∀ y ∈ E', π (x + y) = x ∧ π' (x + y) = y := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (E ⊔ E')
  have h₁ : IsCompl E (E' ⊔ C) := isCompl_sup_right_of_isCompl_sup hinf hC
  have h₂ : IsCompl E' (E ⊔ C) :=
    isCompl_sup_right_of_isCompl_sup (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact hC)
  refine ⟨LinearMap.toContinuousLinearMap (E.subtype ∘ₗ Submodule.linearProjOfIsCompl E _ h₁),
    LinearMap.toContinuousLinearMap (E'.subtype ∘ₗ Submodule.linearProjOfIsCompl E' _ h₂),
    fun x hx y hy => ⟨?_, ?_⟩⟩
  · change ((Submodule.linearProjOfIsCompl E _ h₁ (x + y) : E) : σ → ComplexMatrix2) = x
    have a₁ : Submodule.linearProjOfIsCompl E _ h₁ x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left h₁ ⟨x, hx⟩
    have a₂ : Submodule.linearProjOfIsCompl E _ h₁ y = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' h₁ (Submodule.mem_sup_left hy)
    rw [map_add, a₁, a₂, add_zero]
  · change ((Submodule.linearProjOfIsCompl E' _ h₂ (x + y) : E') : σ → ComplexMatrix2) = y
    have a₁ : Submodule.linearProjOfIsCompl E' _ h₂ y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left h₂ ⟨y, hy⟩
    have a₂ : Submodule.linearProjOfIsCompl E' _ h₂ x = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' h₂ (Submodule.mem_sup_left hx)
    rw [map_add, a₁, a₂, zero_add]
theorem isRelativelyOpen_sums {E E' R : Submodule ℝ (σ → ComplexMatrix2)} (hsup : E ⊔ E' = R)
    (hinf : E ⊓ E' = ⊥) {O O' : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (E : Set (σ → ComplexMatrix2)) O)
    (hO' : ComplexMatrix2.IsRelativelyOpen (E' : Set (σ → ComplexMatrix2)) O') :
    ComplexMatrix2.IsRelativelyOpen (R : Set (σ → ComplexMatrix2))
      {w | ∃ X ∈ O, ∃ X' ∈ O', w = X + X'} := by
  obtain ⟨π, π', hπ⟩ := exists_sum_projections hinf
  obtain ⟨O₁, h₁, rfl⟩ := hO
  obtain ⟨O₂, h₂, rfl⟩ := hO'
  refine ⟨π ⁻¹' O₁ ∩ π' ⁻¹' O₂, (h₁.preimage π.continuous).inter (h₂.preimage π'.continuous), ?_⟩
  ext w
  constructor
  · rintro ⟨X, ⟨hX, hXE⟩, X', ⟨hX', hXE'⟩, rfl⟩
    have h := hπ X hXE X' hXE'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change π (X + X') ∈ O₁
      rw [h.1]
      exact hX
    · change π' (X + X') ∈ O₂
      rw [h.2]
      exact hX'
    · rw [← hsup]
      exact Submodule.add_mem_sup hXE hXE'
  · rintro ⟨⟨h1, h2⟩, hw⟩
    have hw' : w ∈ E ⊔ E' := by rw [hsup]; exact hw
    obtain ⟨X, hXE, X', hXE', rfl⟩ := Submodule.mem_sup.1 hw'
    have h := hπ X hXE X' hXE'
    have h1' : π (X + X') ∈ O₁ := h1
    have h2' : π' (X + X') ∈ O₂ := h2
    rw [h.1] at h1'
    rw [h.2] at h2'
    exact ⟨X, ⟨h1', hXE⟩, X', ⟨h2', hXE'⟩, rfl⟩
theorem fderiv_apply_mem_of_eventually_mem {d : ℕ} {S : Submodule ℝ (σ → ComplexMatrix2)}
    {ψ : (Fin d → ℝ) → σ → ComplexMatrix2} {u : Fin d → ℝ} (hψ : DifferentiableAt ℝ ψ u)
    (h : ∀ᶠ v in 𝓝 u, ψ v ∈ S) (w : Fin d → ℝ) : fderiv ℝ ψ u w ∈ S := by
  have hS : IsClosed (S : Set (σ → ComplexMatrix2)) := Submodule.closed_of_finiteDimensional S
  have hc : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
  have h0 : HasFDerivAt ψ (fderiv ℝ ψ u) (u + (0 : ℝ) • w) := by
    simpa using hψ.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ψ (u + t • w)) (fderiv ℝ ψ u w) 0 :=
    h0.comp_hasDerivAt 0 hc
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ψ (u + t • w) ∈ S := by
    have hcont : Tendsto (fun t : ℝ => u + t • w) (𝓝 0) (𝓝 u) := by
      simpa using hc.continuousAt.tendsto
    exact hcont.eventually h
  have ht := hasDerivAt_iff_tendsto_slope.1 hl
  refine hS.mem_of_tendsto ht ?_
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with t hft
  rw [slope_def_module]
  exact S.smul_mem _ (S.sub_mem hft hev.self_of_nhds)
def expLeft (p w : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun s => ComplexMatrix2.matExp (Complex.I • w s) * p s
theorem expLeft_zero (p : σ → ComplexMatrix2) : expLeft p 0 = p := by
  funext s
  simp [expLeft, ComplexMatrix2.matExp, NormedSpace.exp_zero]
theorem contDiff_expLeft (p : σ → ComplexMatrix2) : ContDiff ℝ ∞ (expLeft p) := by
  have hE : ContDiff ℝ ∞ (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  refine contDiff_pi.2 fun s => ?_
  exact (hE.comp ((contDiff_apply ℝ ComplexMatrix2 s).const_smul Complex.I)).mul contDiff_const
theorem hasDerivAt_expLeft {w : ℝ → σ → ComplexMatrix2} {v : σ → ComplexMatrix2}
    (hw : HasDerivAt w v 0) (h0 : w 0 = 0) (p : σ → ComplexMatrix2) (s : σ) :
    HasDerivAt (fun t => expLeft p (w t) s) (Complex.I • v s * p s) 0 := by
  have hs : HasDerivAt (fun t => Complex.I • w t s) (Complex.I • v s) 0 :=
    ((hasDerivAt_pi.1 hw) s).const_smul Complex.I
  have hE : HasFDerivAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
      (1 : ComplexMatrix2 →L[ℝ] ComplexMatrix2) (Complex.I • w 0 s) := by
    rw [h0]
    simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ComplexMatrix2)
  have hc := hE.comp_hasDerivAt 0 hs
  exact hc.mul_const (p s)
theorem mem_hermitianTracelessFunctions {w : σ → ComplexMatrix2} :
    w ∈ GroupLieProduct.hermitianTracelessFunctions σ ↔
      ∀ s, w s ∈ ComplexMatrix2.hermitianTraceless := by
  simp [GroupLieProduct.hermitianTracelessFunctions, Submodule.mem_pi]
def halfBall (σ : Type) : Set (σ → ComplexMatrix2) :=
  {w | w ∈ GroupLieProduct.hermitianTracelessFunctions σ ∧
    ∀ s, ComplexMatrix2.operatorNorm (w s) < 1 / 2}
def toLieFamily (w : σ → ComplexMatrix2) (h : ∀ s, w s ∈ ComplexMatrix2.hermitianTraceless) :
    σ → ComplexMatrix2.LieElement :=
  fun s => (⟨w s, h s⟩ : ComplexMatrix2.hermitianTraceless)
theorem exp_half_le_nineteen_tenths : Real.exp (1 / 2) ≤ 19 / 10 := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exp_half_le_nineteen_tenths <;> assumption
structure ExpChartProps (p : σ → ComplexMatrix2) : Prop where
  mapsTo_group : ∀ w ∈ GroupLieProduct.hermitianTracelessFunctions σ,
    expLeft p w ∈ specialUnitaryPower σ
  isOpen_logDomain : IsOpen (logDomain p)
  contDiffOn_log : ContDiffOn ℝ ∞ (logChart p) (logDomain p)
  log_expLeft : ∀ w ∈ halfBall σ,
    expLeft p w ∈ logDomain p ∧ logChart p (expLeft p w) = w
  isRelativelyOpen_image :
    ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ) (expLeft p '' halfBall σ)
theorem expChartProps (hC : PowerCharts σ) {p : σ → ComplexMatrix2}
    (hp : p ∈ specialUnitaryPower σ) : ExpChartProps p := by
  obtain ⟨-, h2, h3⟩ := hC p hp
  obtain ⟨-, hopen, -, -, hlogopen, hlogC, hsub, hlog, -⟩ :=
    h3 (1 / 2) (by norm_num) exp_half_le_nineteen_tenths
  have hY : ∀ Y : σ → ComplexMatrix2.LieElement,
      expChartI p Y = expLeft p fun s => (Y s).toMatrix :=
    fun Y => (h2 Y).2.1
  have hsmall : ∀ w (hw : w ∈ halfBall σ),
      toLieFamily w (mem_hermitianTracelessFunctions.1 hw.1) ∈ smallBall σ (1 / 2) :=
    fun w hw s => hw.2 s
  have hval : ∀ (w : σ → ComplexMatrix2) (h : ∀ s, w s ∈ ComplexMatrix2.hermitianTraceless),
      (fun s => (toLieFamily w h s).toMatrix) = w :=
    fun w h => rfl
  have himg : expChartI p '' smallBall σ (1 / 2) = expLeft p '' halfBall σ := by
    ext q
    constructor
    · rintro ⟨Y, hYs, rfl⟩
      refine ⟨fun s => (Y s).toMatrix, ⟨mem_hermitianTracelessFunctions.2 fun s =>
        Subtype.property (p := (· ∈ ComplexMatrix2.hermitianTraceless)) (Y s), hYs⟩, ?_⟩
      exact (hY Y).symm
    · rintro ⟨w, hw, rfl⟩
      refine ⟨toLieFamily w (mem_hermitianTracelessFunctions.1 hw.1), hsmall w hw, ?_⟩
      rw [hY, hval]
  refine ⟨fun w hw => ?_, hlogopen, hlogC, fun w hw => ?_, himg ▸ hopen⟩
  · have h := (h2 (toLieFamily w (mem_hermitianTracelessFunctions.1 hw))).2
    rw [h.1] at h
    exact h.2
  · have hin := hsub (mem_image_of_mem _ (hsmall w hw))
    have hl := hlog _ (hsmall w hw)
    rw [hY, hval] at hin hl
    exact ⟨hin, hl⟩
structure IsExpGraph (M : Set (σ → ComplexMatrix2)) (p : σ → ComplexMatrix2)
    (E E' : Submodule ℝ (σ → ComplexMatrix2)) (O O' : Set (σ → ComplexMatrix2))
    (f : (σ → ComplexMatrix2) → σ → ComplexMatrix2) : Prop where
  sup_eq : E ⊔ E' = GroupLieProduct.hermitianTracelessFunctions σ
  inf_eq : E ⊓ E' = ⊥
  relOpen_left : ComplexMatrix2.IsRelativelyOpen (E : Set (σ → ComplexMatrix2)) O
  relOpen_right : ComplexMatrix2.IsRelativelyOpen (E' : Set (σ → ComplexMatrix2)) O'
  norm_lt : ∀ X ∈ O, ∀ X' ∈ O', ∀ c, ComplexMatrix2.operatorNorm ((X + X') c) < 1 / 2
  mapsTo : MapsTo f O O'
  contDiffOn_comp : ∀ (d : ℕ) (ι : (Fin d → ℝ) →L[ℝ] (σ → ComplexMatrix2)), (∀ u, ι u ∈ E) →
    ContDiffOn ℝ ∞ (f ∘ ι) (ι ⁻¹' O)
  mem_iff : ∀ X ∈ O, ∀ X' ∈ O', (expLeft p (X + X') ∈ M ↔ X' = f X)
variable {M : Set (σ → ComplexMatrix2)} {p : σ → ComplexMatrix2}
  {E E' : Submodule ℝ (σ → ComplexMatrix2)} {O O' : Set (σ → ComplexMatrix2)}
  {f : (σ → ComplexMatrix2) → σ → ComplexMatrix2}
namespace IsExpGraph
theorem mem_left (h : IsExpGraph M p E E' O O' f) {X : σ → ComplexMatrix2} (hX : X ∈ O) :
    X ∈ E := by
  obtain ⟨O₁, -, e⟩ := h.relOpen_left
  rw [e] at hX
  exact hX.2
theorem mem_right (h : IsExpGraph M p E E' O O' f) {X : σ → ComplexMatrix2} (hX : X ∈ O') :
    X ∈ E' := by
  obtain ⟨O₁, -, e⟩ := h.relOpen_right
  rw [e] at hX
  exact hX.2
theorem add_mem_halfBall (h : IsExpGraph M p E E' O O' f) {X X' : σ → ComplexMatrix2}
    (hX : X ∈ O) (hX' : X' ∈ O') : X + X' ∈ halfBall σ :=
  ⟨by rw [← h.sup_eq]; exact Submodule.add_mem_sup (h.mem_left hX) (h.mem_right hX'),
    h.norm_lt X hX X' hX'⟩
theorem eq_of_add_eq (h : IsExpGraph M p E E' O O' f) {X X' Z Z' : σ → ComplexMatrix2}
    (hX : X ∈ O) (hX' : X' ∈ O') (hZ : Z ∈ O) (hZ' : Z' ∈ O') (e : X + X' = Z + Z') :
    X = Z ∧ X' = Z' := by
  have h₁ : X - Z ∈ E := E.sub_mem (h.mem_left hX) (h.mem_left hZ)
  have h₂ : X - Z ∈ E' := by
    have : X - Z = Z' - X' := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm Z' , add_comm X]
      rw [add_comm X' X, e, add_comm]
    rw [this]
    exact E'.sub_mem (h.mem_right hZ') (h.mem_right hX')
  have h₃ : X - Z ∈ E ⊓ E' := ⟨h₁, h₂⟩
  rw [h.inf_eq, Submodule.mem_bot, sub_eq_zero] at h₃
  subst h₃
  exact ⟨rfl, add_left_cancel e⟩
theorem eq_of_expLeft_eq (hF : ExpChartProps p) (h : IsExpGraph M p E E' O O' f)
    {X X' Z Z' : σ → ComplexMatrix2} (hX : X ∈ O) (hX' : X' ∈ O') (hZ : Z ∈ O) (hZ' : Z' ∈ O')
    (e : expLeft p (X + X') = expLeft p (Z + Z')) : X = Z ∧ X' = Z' := by
  refine h.eq_of_add_eq hX hX' hZ hZ' ?_
  rw [← (hF.log_expLeft _ (h.add_mem_halfBall hX hX')).2, e,
    (hF.log_expLeft _ (h.add_mem_halfBall hZ hZ')).2]
theorem isRelativelyOpen_expLeft_image (hF : ExpChartProps p) (h : IsExpGraph M p E E' O O' f)
    {W : Set (σ → ComplexMatrix2)} (hWO : W ⊆ O)
    (hW : ComplexMatrix2.IsRelativelyOpen (E : Set (σ → ComplexMatrix2)) W) :
    ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ)
      (expLeft p '' {w | ∃ X ∈ W, ∃ X' ∈ O', w = X + X'}) := by
  obtain ⟨S₁, hS₁, hS⟩ := isRelativelyOpen_sums h.sup_eq h.inf_eq hW h.relOpen_right
  obtain ⟨A₁, hA₁, hA⟩ := hF.isRelativelyOpen_image
  have hcont : ContinuousOn (logChart p) (logDomain p) := hF.contDiffOn_log.continuousOn
  refine ⟨A₁ ∩ (logDomain p ∩ logChart p ⁻¹' S₁),
    hA₁.inter (hcont.isOpen_inter_preimage hF.isOpen_logDomain hS₁), ?_⟩
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwS : w ∈ S₁ ∩ (GroupLieProduct.hermitianTracelessFunctions σ :
      Set (σ → ComplexMatrix2)) := hS ▸ hw
    obtain ⟨X, hX, X', hX', rfl⟩ := hw
    have hsm := h.add_mem_halfBall (hWO hX) hX'
    have hq : expLeft p (X + X') ∈ A₁ ∩ specialUnitaryPower σ := hA ▸ mem_image_of_mem _ hsm
    have hl := hF.log_expLeft _ hsm
    refine ⟨⟨hq.1, hl.1, ?_⟩, hq.2⟩
    change logChart p _ ∈ S₁
    rw [hl.2]
    exact hwS.1
  · rintro ⟨⟨hq₁, hq₂, hq₃⟩, hq₄⟩
    have hq : q ∈ expLeft p '' halfBall σ :=
      hA ▸ (⟨hq₁, hq₄⟩ : q ∈ A₁ ∩ specialUnitaryPower σ)
    obtain ⟨w, hw, rfl⟩ := hq
    have hl : logChart p (expLeft p w) ∈ S₁ := hq₃
    rw [(hF.log_expLeft w hw).2] at hl
    have hwS : w ∈ {w | ∃ X ∈ W, ∃ X' ∈ O', w = X + X'} := hS ▸ (⟨hl, hw.1⟩ :
      w ∈ S₁ ∩ (GroupLieProduct.hermitianTracelessFunctions σ : Set (σ → ComplexMatrix2)))
    exact mem_image_of_mem _ hwS
theorem exists_chart_at (hF : ExpChartProps p) (h : IsExpGraph M p E E' O O' f)
    (hM : M ⊆ specialUnitaryPower σ) (h0 : (0 : σ → ComplexMatrix2) ∈ O) (hf0 : f 0 = 0) :
    ∃ (c : EmbeddedSubmanifold.Chart M) (u : Fin c.dim → ℝ),
      u ∈ c.source ∧ c.param u = p := by
  obtain ⟨d, ι, κ, hι, hκ, hκ'⟩ := exists_linear_coords E
  obtain ⟨O₁, hO₁, hOe⟩ := h.relOpen_left
  have hιinj : Function.Injective ι := fun u v e => by rw [← hκ u, ← hκ v, e]
  have hD : ι ⁻¹' O = ι ⁻¹' O₁ := by
    ext u
    constructor
    · intro hu
      have hu' : ι u ∈ O := hu
      rw [hOe] at hu'
      exact hu'.1
    · intro hu
      change ι u ∈ O
      rw [hOe]
      exact ⟨hu, hι u⟩
  have hDopen : IsOpen (ι ⁻¹' O) := by
    rw [hD]
    exact hO₁.preimage ι.continuous
  have hs := h.contDiffOn_comp d ι hι
  let φ : (Fin d → ℝ) → σ → ComplexMatrix2 := fun u => expLeft p (ι u + f (ι u))
  have hφ : ContDiffOn ℝ ∞ φ (ι ⁻¹' O) :=
    (contDiff_expLeft p).comp_contDiffOn (ι.contDiff.contDiffOn.add hs)
  have hmem : ∀ u ∈ ι ⁻¹' O, f (ι u) ∈ O' := fun u hu => h.mapsTo hu
  have hlog : ∀ u ∈ ι ⁻¹' O, logChart p (φ u) = ι u + f (ι u) := fun u hu =>
    (hF.log_expLeft _ (h.add_mem_halfBall hu (hmem u hu))).2
  have hfd : ∀ u ∈ ι ⁻¹' O, Function.Injective (fderiv ℝ φ u) := by
    intro u hu
    have hnb : ι ⁻¹' O ∈ 𝓝 u := hDopen.mem_nhds hu
    have hφd : DifferentiableAt ℝ φ u :=
      (hφ.contDiffAt hnb).differentiableAt (by simp)
    have hψd : DifferentiableAt ℝ (f ∘ ι) u :=
      (hs.contDiffAt hnb).differentiableAt (by simp)
    have hld : DifferentiableAt ℝ (logChart p) (φ u) :=
      (hF.contDiffOn_log.contDiffAt (hF.isOpen_logDomain.mem_nhds
        (hF.log_expLeft _ (h.add_mem_halfBall hu (hmem u hu))).1)).differentiableAt (by simp)
    have hev : logChart p ∘ φ =ᶠ[𝓝 u] fun v => ι v + (f ∘ ι) v := by
      filter_upwards [hnb] with v hv using hlog v hv
    have hcomp : HasFDerivAt (logChart p ∘ φ)
        ((fderiv ℝ (logChart p) (φ u)).comp (fderiv ℝ φ u)) u :=
      hld.hasFDerivAt.comp u hφd.hasFDerivAt
    have hsum : HasFDerivAt (logChart p ∘ φ) (ι + fderiv ℝ (f ∘ ι) u) u :=
      (ι.hasFDerivAt.add hψd.hasFDerivAt).congr_of_eventuallyEq hev
    have heq := hcomp.unique hsum
    refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
    have h1 : ι w + fderiv ℝ (f ∘ ι) u w = 0 := by
      have := congrArg (fun T => T w) heq
      simpa [hw] using this.symm
    have h2 : fderiv ℝ (f ∘ ι) u w ∈ E' := by
      refine fderiv_apply_mem_of_eventually_mem hψd ?_ w
      filter_upwards [hnb] with v hv using h.mem_right (hmem v hv)
    have h3 : ι w ∈ E' := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact E'.neg_mem h2
    have h4 : ι w ∈ E ⊓ E' := ⟨hι w, h3⟩
    rw [h.inf_eq, Submodule.mem_bot] at h4
    exact hιinj (by rw [h4, map_zero])
  refine ⟨{ dim := d
            source := ι ⁻¹' O
            param := φ
            isOpen_source := hDopen
            contDiffOn_param := hφ
            injective_fderiv_param := hfd
            injOn_param := fun u hu v hv e =>
              hιinj (h.eq_of_expLeft_eq hF hu (hmem u hu) hv (hmem v hv) e).1
            isRelativelyOpen_image := fun W hW hWo => ?_ }, 0, ?_, ?_⟩
  · have hWE : ComplexMatrix2.IsRelativelyOpen (E : Set (σ → ComplexMatrix2)) (ι '' W) := by
      refine ⟨κ ⁻¹' W, hWo.preimage κ.continuous, ?_⟩
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨?_, hι u⟩
        change κ (ι u) ∈ W
        rw [hκ]
        exact hu
      · rintro ⟨hx₁, hx₂⟩
        exact ⟨κ x, hx₁, hκ' x hx₂⟩
    have hWO : ι '' W ⊆ O := by
      rintro _ ⟨u, hu, rfl⟩
      exact hW hu
    obtain ⟨Q, hQ, hQe⟩ := h.isRelativelyOpen_expLeft_image hF hWO hWE
    refine ⟨Q, hQ, ?_⟩
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hq : φ u ∈ expLeft p '' {w | ∃ X ∈ ι '' W, ∃ X' ∈ O', w = X + X'} :=
        ⟨_, ⟨ι u, mem_image_of_mem _ hu, f (ι u), hmem u (hW hu), rfl⟩, rfl⟩
      rw [hQe] at hq
      exact ⟨hq.1, (h.mem_iff _ (hW hu) _ (hmem u (hW hu))).2 rfl⟩
    · rintro ⟨hq₁, hq₂⟩
      have hq : q ∈ Q ∩ specialUnitaryPower σ := ⟨hq₁, hM hq₂⟩
      rw [← hQe] at hq
      obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, X', hX', rfl⟩, rfl⟩ := hq
      have hX : X' = f (ι u) := (h.mem_iff _ (hW hu) _ hX').1 hq₂
      subst hX
      exact ⟨u, hu, rfl⟩
  · change ι 0 ∈ O
    rw [map_zero]
    exact h0
  · change expLeft p (ι 0 + f (ι 0)) = p
    rw [map_zero, hf0, add_zero, expLeft_zero]
end IsExpGraph
end Complements
section Edges
variable {L n k a : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem opposite_opposite (b : Edge L n k a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem edgeFormOfPositiveValues_of_pos (w : PositiveEdge L n k a → ComplexMatrix2)
    {b : Edge L n k a} (h : b.IsPositivelyOriented) :
    edgeFormOfPositiveValues w b = w ⟨b, h⟩ := by
  simp only [edgeFormOfPositiveValues, dif_pos h]
theorem restrict_expTwist (w : PositiveEdge L n k a → ComplexMatrix2)
    (V : Edge L n k a → ComplexMatrix2) :
    restrictToPositiveEdges (PeriodicLattice.expTwist (edgeFormOfPositiveValues w) V) =
      expLeft (restrictToPositiveEdges V) w := by
  funext b
  simp only [restrictToPositiveEdges, expLeft, PeriodicLattice.expTwist, if_pos b.2,
    edgeFormOfPositiveValues_of_pos _ b.2]
theorem eq_expTwist {U V : Edge L n k a → ComplexMatrix2}
    {w : PositiveEdge L n k a → ComplexMatrix2} (hU : U ∈ fieldSpace L n k a)
    (h : restrictToPositiveEdges U = expLeft (restrictToPositiveEdges V) w) :
    U = PeriodicLattice.expTwist (edgeFormOfPositiveValues w) V := by
  have h' := h.trans (restrict_expTwist w V).symm
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact congrFun h' ⟨b, hb⟩
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have hv := congrFun h' ⟨b.opposite, hr⟩
    have hv' : U b.opposite =
        PeriodicLattice.expTwist (edgeFormOfPositiveValues w) V b.opposite := hv
    have hinv := hU.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at hinv
    rw [hinv, hv']
    simp only [PeriodicLattice.expTwist, if_pos hr, if_neg hb]
variable [Fintype (PositiveEdge L n k a)]
theorem expTwist_mem (hB : BijOn restrictToPositiveEdges (fieldSpace L n k a)
      (specialUnitaryPower (PositiveEdge L n k a))) {V : Edge L n k a → ComplexMatrix2}
    {w : PositiveEdge L n k a → ComplexMatrix2} (hF : ExpChartProps (restrictToPositiveEdges V))
    (hw : w ∈ GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a)) :
    PeriodicLattice.expTwist (edgeFormOfPositiveValues w) V ∈ fieldSpace L n k a := by
  obtain ⟨U, hU, e⟩ := hB.surjOn (hF.mapsTo_group w hw)
  rw [← eq_expTwist hU e]
  exact hU
theorem isExpGraph {N : Set (Edge L n k a → ComplexMatrix2)} (hN : N ⊆ fieldSpace L n k a)
    {V : Edge L n k a → ComplexMatrix2} {E E' : Submodule ℝ (PositiveEdge L n k a → ComplexMatrix2)}
    {O O' : Set (PositiveEdge L n k a → ComplexMatrix2)}
    {f : (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k a → ComplexMatrix2}
    (g : IsLeftChartGraphAt N V E E' O O' f) :
    IsExpGraph (restrictToPositiveEdges '' N) (restrictToPositiveEdges V) E E' O O' f where
  sup_eq := g.sup_eq
  inf_eq := g.inf_eq
  relOpen_left := g.relOpen_left
  relOpen_right := g.relOpen_right
  norm_lt := g.norm_sum_lt
  mapsTo := g.mapsTo
  contDiffOn_comp := g.contDiff
  mem_iff := fun X hX X' hX' => by
    constructor
    · rintro ⟨U, hU, e⟩
      have := eq_expTwist (hN hU) e
      exact (g.mem_iff X hX X' hX').1 (this ▸ hU)
    · intro h
      exact ⟨_, (g.mem_iff X hX X' hX').2 h, restrict_expTwist _ _⟩
theorem edgeForm_mem_tangentSpan {N : Set (Edge L n k a → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k a) {V : Edge L n k a → ComplexMatrix2} (hV : V ∈ N)
    {E E' : Submodule ℝ (PositiveEdge L n k a → ComplexMatrix2)}
    {O O' : Set (PositiveEdge L n k a → ComplexMatrix2)}
    {f : (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k a → ComplexMatrix2}
    (g : IsLeftChartGraphAt N V E E' O O' f) {X : PositiveEdge L n k a → ComplexMatrix2}
    (hX : X ∈ E) :
    edgeFormOfPositiveValues X ∈ (fieldCurveData L n k a).tangentSpan N V := by
  obtain ⟨O₁, hO₁, hOe⟩ := g.relOpen_left
  have hT : IsOpen ((fun t : ℝ => t • X) ⁻¹' O₁) :=
    hO₁.preimage (continuous_id.smul continuous_const)
  have h0T : (0 : ℝ) ∈ (fun t : ℝ => t • X) ⁻¹' O₁ := by
    have h0 := g.zero_mem_left
    rw [hOe] at h0
    change (0 : ℝ) • X ∈ O₁
    rw [zero_smul]
    exact h0.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT 0 h0T
  have hI : ∀ t ∈ Ioo (-ε) ε, t • X ∈ O := fun t ht => by
    rw [hOe]
    refine ⟨hball ?_, E.smul_mem t hX⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ht
  have h0I : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  let ι : (Fin 1 → ℝ) →L[ℝ] (PositiveEdge L n k a → ComplexMatrix2) :=
    (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight X
  have hs := g.contDiff 1 ι (fun u => E.smul_mem _ hX)
  have hh : DifferentiableOn ℝ (fun t : ℝ => f (t • X)) (Ioo (-ε) ε) := by
    let c : ℝ → Fin 1 → ℝ := fun t _ => t
    have hc : ContDiff ℝ ∞ c := contDiff_pi.2 fun _ => contDiff_id
    have hmaps : MapsTo c (Ioo (-ε) ε) (ι ⁻¹' O) := fun t ht => hI t ht
    have hcomp := hs.comp hc.contDiffOn hmaps
    exact hcomp.differentiableOn (by simp)
  let w : ℝ → PositiveEdge L n k a → ComplexMatrix2 := fun t => t • X + f (t • X)
  have hwd : DifferentiableOn ℝ w (Ioo (-ε) ε) :=
    (differentiableOn_id.smul_const X).add hh
  have hf0 : f ((0 : ℝ) • X) = 0 := by rw [zero_smul]; exact g.map_zero
  have hw0 : w 0 = 0 := by
    change (0 : ℝ) • X + f ((0 : ℝ) • X) = 0
    rw [hf0, zero_smul, add_zero]
  have hw' : HasDerivAt w X 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • X) X 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
    have h2 := h1.add (g.hasDerivAt_zero X hX)
    rw [add_zero] at h2
    exact h2
  let γ : ℝ → Edge L n k a → ComplexMatrix2 :=
    fun t => PeriodicLattice.expTwist (edgeFormOfPositiveValues (w t)) V
  have hγN : MapsTo γ (Ioo (-ε) ε) N := fun t ht =>
    (g.mem_iff _ (hI t ht) _ (g.mapsTo (hI t ht))).2 rfl
  have hV' := hN hV
  have hγ0 : γ 0 = V := by
    change PeriodicLattice.expTwist (edgeFormOfPositiveValues (w 0)) V = V
    rw [hw0]
    exact (eq_expTwist hV' (expLeft_zero _).symm).symm
  have hγb : ∀ b (hb : b.IsPositivelyOriented) t,
      γ t b = expLeft (restrictToPositiveEdges V) (w t) ⟨b, hb⟩ := fun b hb t =>
    congrFun (restrict_expTwist (w t) V) ⟨b, hb⟩
  have hcurve : (fieldCurveData L n k a).IsCurve (Ioo (-ε) ε) γ := by
    refine ⟨⟨isOpen_Ioo, ordConnected_Ioo, h0I⟩, fun t ht => hN (hγN ht), fun b hb => ?_⟩
    have hd : DifferentiableOn ℝ (expLeft (restrictToPositiveEdges V) ∘ w) (Ioo (-ε) ε) :=
      ((contDiff_expLeft _).differentiable (by simp)).comp_differentiableOn hwd
    have hd' := differentiableOn_pi.1 hd ⟨b, hb⟩
    refine hd'.congr fun t _ => ?_
    exact hγb b hb t
  refine Submodule.subset_span ⟨Ioo (-ε) ε, γ, hcurve, hγN, hγ0, ?_⟩
  have hval : ∀ b (hb : b.IsPositivelyOriented),
      Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹) = X ⟨b, hb⟩ := by
    intro b hb
    have hd := hasDerivAt_expLeft hw' hw0 (restrictToPositiveEdges V) ⟨b, hb⟩
    have hfun : (fun t => γ t b) =
        fun t => expLeft (restrictToPositiveEdges V) (w t) ⟨b, hb⟩ := funext (hγb b hb)
    rw [hfun, hd.deriv, hγ0]
    have hdet : IsUnit (V b).det := by
      have h1 := (Matrix.mem_specialUnitaryGroup_iff.1 (hV'.1 b (mem_univ b))).2
      rw [h1]
      exact isUnit_one
    change Complex.I⁻¹ • (Complex.I • X ⟨b, hb⟩ * V b * (V b)⁻¹) = X ⟨b, hb⟩
    rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  change curveTangent γ = _
  unfold curveTangent
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb]
    rw [hval b hb, edgeFormOfPositiveValues_of_pos _ hb]
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [extendOddly, if_neg hb]
    rw [hval _ hr]
    simp only [edgeFormOfPositiveValues, dif_neg hb, dif_pos hr]
theorem isAnalyticFieldSubmanifold (hC : PowerCharts (PositiveEdge L n k a))
    (hB : BijOn restrictToPositiveEdges (fieldSpace L n k a)
      (specialUnitaryPower (PositiveEdge L n k a)))
    {N : Set (Edge L n k a → ComplexMatrix2)} (hN : N ⊆ fieldSpace L n k a)
    (hg : ∀ V ∈ N, ∃ E E' O O' f, IsLeftChartGraphAt N V E E' O O' f) :
    IsAnalyticFieldSubmanifold N := by
  have hM : restrictToPositiveEdges '' N ⊆ specialUnitaryPower (PositiveEdge L n k a) := by
    rintro _ ⟨U, hU, rfl⟩
    exact hB.mapsTo (hN hU)
  refine ⟨⟨hN, ‹_›, ?_⟩, ‹_›, fun x hx => ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨E, E', O, O', f, g⟩ := hg V hV
    exact (isExpGraph hN g).exists_chart_at (expChartProps hC (hB.mapsTo (hN hV))) hM
      g.zero_mem_left g.map_zero
  · obtain ⟨E, E', O, O', f, g⟩ := hg x hx
    have hF : ExpChartProps (restrictToPositiveEdges x) := expChartProps hC (hB.mapsTo (hN hx))
    have hG := isExpGraph hN g
    let 𝒰 : Set (Edge L n k a → ComplexMatrix2) :=
      {U | ∃ X ∈ O, ∃ X' ∈ O',
        U = PeriodicLattice.expTwist (edgeFormOfPositiveValues (X + X')) x}
    have himg : restrictToPositiveEdges '' 𝒰 =
        expLeft (restrictToPositiveEdges x) '' {w | ∃ X ∈ O, ∃ X' ∈ O', w = X + X'} := by
      ext q
      constructor
      · rintro ⟨_, ⟨X, hX, X', hX', rfl⟩, rfl⟩
        exact ⟨X + X', ⟨X, hX, X', hX', rfl⟩, (restrict_expTwist _ _).symm⟩
      · rintro ⟨_, ⟨X, hX, X', hX', rfl⟩, rfl⟩
        exact ⟨_, ⟨X, hX, X', hX', rfl⟩, restrict_expTwist _ _⟩
    have hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨X, hX, X', hX', rfl⟩
        exact expTwist_mem hB hF (hG.add_mem_halfBall hX hX').1
      · change ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower (PositiveEdge L n k a))
          (restrictToPositiveEdges '' 𝒰)
        rw [himg]
        exact hG.isRelativelyOpen_expLeft_image hF subset_rfl g.relOpen_left
    have hx𝒰 : x ∈ 𝒰 := by
      refine ⟨0, g.zero_mem_left, 0, g.zero_mem_right, ?_⟩
      rw [add_zero]
      exact eq_expTwist (hN hx) (expLeft_zero _).symm
    refine ⟨𝒰, x, E, E', O, O', f, hopen, hx𝒰, hN hx, g.sup_eq, g.inf_eq, g.relOpen_left,
      g.relOpen_right, g.analytic, ?_⟩
    rintro U ⟨X, hX, X', hX', rfl⟩
    refine ⟨⟨(X, X'), ⟨hX, hX', rfl⟩, ?_⟩, fun Z hZ Z' hZ' e => ?_⟩
    · rintro ⟨Z, Z'⟩ ⟨hZ, hZ', e⟩
      have e' := congrArg restrictToPositiveEdges e
      rw [restrict_expTwist, restrict_expTwist] at e'
      obtain ⟨h1, h2⟩ := hG.eq_of_expLeft_eq hF hZ hZ' hX hX' e'.symm
      exact Prod.ext h1 h2
    · rw [e]
      exact g.mem_iff Z hZ Z' hZ'
end Edges
theorem leftChartGraphsAreSubmanifolds_holds (hA : LeftChartFields.Claim)
    (hC : PowerExpCharts.ExpChartsStatement) : LeftChartGraphsAreSubmanifolds := by
  intro L n k a hL hn ha _ N hN
  have hne : Nonempty (PositiveEdge L n k a) := by
    rcases isPositivelyOriented_or_opposite
      (PeriodicLattice.Bond.forwardFrom (0 : Vertex L n k a) 0) with h | h
    · exact ⟨⟨_, h⟩⟩
    · exact ⟨⟨_, h⟩⟩
  have hB := (((hA.2.2 L k a hL ha).1 n hn).2.1).2.1
  have hC' := (hC (PositiveEdge L n k a) (PositiveEdge L n k a)).1
  exact ⟨isAnalyticFieldSubmanifold hC' hB hN, fun V hV E E' O O' f g X hX =>
    edgeForm_mem_tangentSpan hN hV g hX⟩
end YangMills.Construction.Tower.LeftChartGraphProof
end
