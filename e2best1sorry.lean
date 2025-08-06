import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory

/- OS2 ℝᵈ with d = 4, where μ is the Lebesgue measure.
   We know the OS2 dp must be Euclidean invariant. -/
def STDimension := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume   -- Lebesgue, just named

open scoped Real InnerProductSpace
open MeasureTheory

namespace QFT

/-! L² real-valued fields, the OS2 lines S_J is invariant.
     The pullback on L² requires an actual L² Banach space and establishes
     the σ-algebra. -/
abbrev FieldSpace' := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace' := borel _
instance : BorelSpace FieldSpace' := ⟨rfl⟩

/-- Orthogonal linear isometries of ℝ⁴ (the group O(4)).
    `LinearIsometry` is an orthogonal linear map, i.e. an element of O(4). -/
abbrev O4 : Type := LinearIsometry (RingHom.id ℝ) RSpaceTime RSpaceTime

/-! Euclidean group -/

/-- Euclidean motion = rotation/reflection + translation. `E = ℝ⁴ × O(4)`. -/
structure E where
  R : O4
  t : RSpaceTime

/-- Action of `g : E` on a spacetime point `x`. Implements the pullback map
    `x ↦ g.R x + g.t`. -/
def act (g : E) (x : RSpaceTime) : RSpaceTime := g.R x + g.t

/- `act_one`, `act_mul`, and `act_inv` lemmas prove identity, composition,
   and inverse. They are needed to say Euclidean sym forms a group.
   This mirrors OS-2's `S_j = S_{EJ}`. -/
@[simp] lemma act_one (x : RSpaceTime) : act ⟨1, 0⟩ x = x := by
  simp [act]

@[simp] lemma act_mul (g h : E) (x : RSpaceTime) :
    act ⟨g.R.comp h.R, g.R h.t + g.t⟩ x = g.R (h.R x + h.t) + g.t := by
  simp [act, add_comm, add_left_comm, add_assoc]

@[simp] lemma act_inv (g : E) (x : RSpaceTime) :
    act ⟨g.R, -g.R g.t⟩ x = g.R (x - g.t) := by
  simp [act, sub_eq_add_neg, map_add, map_neg]

/- Linear-iso helper lemmas are explicitly in OS-2 but are used as a
   counterpart to rotations that preserve the metric and `R⁻¹ ∘ R = 1`. -/
open LinearIsometryEquiv

namespace LinearIsometry

/-- Inverse of a linear isometry: we turn the canonical equivalence
    (available in finite dimension) back into a `LinearIsometry`. -/
noncomputable def inv (g : O4) : O4 :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

@[simp] lemma comp_apply (g h : O4) (x : RSpaceTime) :
    (g.comp h) x = g (h x) := rfl

@[simp] lemma inv_apply (g : O4) (x : RSpaceTime) :
    (LinearIsometry.inv g) (g x) = x := by
  -- unfold `inv`, then use the standard `symm_apply_apply` lemma
  dsimp [LinearIsometry.inv]
  simpa using
    (LinearIsometryEquiv.symm_apply_apply (g.toLinearIsometryEquiv rfl) x)

@[simp] lemma one_apply (x : RSpaceTime) : (1 : O4) x = x := rfl

@[simp] lemma one_comp (R : O4) : (1 : O4).comp R = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma comp_one (R : O4) : R.comp (1 : O4) = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma inv_comp (R : O4) :
    (LinearIsometry.inv R).comp R = 1 := by
  ext x i
  simp [comp_apply, inv_apply, one_apply]

@[simp] lemma comp_inv (R : O4) :
    R.comp (LinearIsometry.inv R) = 1 := by
  -- equality of linear-isometries, proved coordinate-wise
  ext x i
  have h : (R.toLinearIsometryEquiv rfl) ((LinearIsometry.inv R) x) = x :=
    LinearIsometryEquiv.apply_symm_apply (R.toLinearIsometryEquiv rfl) x
  simpa [comp_apply, inv_apply, one_apply] using
    congrArg (fun v : RSpaceTime => v i) h

end LinearIsometry


/- Extensionality: allows Lean to prove equality of Euclidean motions
   by checking the `R` and `t` components separately — hugely convenient
   for the group-law proofs. -/
@[ext] lemma E.ext {g h : E} (hR : g.R = h.R) (ht : g.t = h.t) : g = h := by
  cases g; cases h; cases hR; cases ht; rfl

/-! ## Group structure on `E` ------------------------------------------------ -/

/- 1. Primitive instances of group operations
   Implements the semidirect-product multiplication in OS-2:
   first rotate, then translate the second translation by the first rotation. -/
instance : Mul E where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩

instance : One E where
  one := ⟨1, 0⟩

instance : Inv E where
  inv g := ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-- We need a `Div` instance because `Group` extends `DivInvMonoid`. -/
instance : Div E where
  div g h := g * h⁻¹

/- Helper lemmas mirroring `(g*h).R = g.R ∘ h.R`
   and `(g*h).t = g.R h.t + g.t`. -/
@[simp] lemma mul_R (g h : E) : (g * h).R = g.R.comp h.R := rfl
@[simp] lemma mul_t (g h : E) : (g * h).t = g.R h.t + g.t := rfl
@[simp] lemma one_R : (1 : E).R = 1 := rfl
@[simp] lemma one_t : (1 : E).t = 0 := rfl
@[simp] lemma inv_R (g : E) : (g⁻¹).R = LinearIsometry.inv g.R := rfl
@[simp] lemma inv_t (g : E) : (g⁻¹).t = -(LinearIsometry.inv g.R) g.t := rfl

/-- `LinearIsometry.comp` is associative.
    OS-2's "group" assertion needs rotation composition to be associative;
    this lemma certifies it for Lean. -/
@[simp] lemma LinearIsometry.comp_assoc (f g h : O4) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext x; rfl

/- Provides the formal group demanded by OS-2's statement
   "Euclidean transformations define a group." -/
instance : Group E where
  mul := (· * ·)
  one := (1 : E)
  inv := Inv.inv
  mul_assoc a b c := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_assoc]
    · simp [mul_t, add_comm, add_left_comm, add_assoc]
  one_mul a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.one_comp]
    · simp [mul_t, one_t]
  mul_one a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_one]
    · simp [mul_t, one_t]
  inv_mul_cancel a := by
    apply E.ext
    · simp [mul_R, inv_R, one_R, LinearIsometry.inv_comp]
    · simp [mul_t, inv_t, one_t, add_comm]

/- Theorem --------------------------------------------------------------
     For all Euclidean motions `g, h` and every point `x ∈ ℝ⁴`
     we have `act (g * h) x = act g (act h x)`.
     In words: `act` is a group action of `E` on spacetime.
     We also prove the inverse law `act g⁻¹ (act g x) = x`. -/
@[simp] lemma act_mul_general (g h : E) (x : RSpaceTime) :
    act (g * h) x = act g (act h x) := by
  cases g with
  | mk gR gt =>
    cases h with
    | mk hR ht =>
      simp [act, mul_R, mul_t, add_comm, add_left_comm, add_assoc]

@[simp] lemma act_inv_general (g : E) (x : RSpaceTime) :
    act g⁻¹ (act g x) = x := by
  cases g with
  | mk gR gt =>
    simp [act, inv_R, inv_t, add_comm, add_left_comm, add_assoc,
          sub_eq_add_neg]

/- We still need a measure-preservation lemma.
   Need `MeasurePreserving (act g) μ μ`. That will give the analytic
   statement `dp = E_* dp`. -/

/-! ### Lebesgue measure is invariant under every Euclidean motion -------- -/

abbrev TestFunction : Type := SchwartzMap RSpaceTime ℝ
abbrev TestFunctionℂ : Type := SchwartzMap RSpaceTime ℂ

abbrev FieldSpace := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace FieldSpace := ⟨rfl⟩

abbrev ComplexFieldSpace := Lp (p := 2) (μ := μ) ℂ
instance : MeasurableSpace ComplexFieldSpace := borel _
instance : BorelSpace ComplexFieldSpace := ⟨rfl⟩

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/
variable (dμ : ProbabilityMeasure FieldSpace)
variable (dμ' : ProbabilityMeasure ComplexFieldSpace)

/- Generating functional of correlation functions -/
def pairingCLM (J : TestFunction) : FieldSpace →L[ℝ] ℝ :=
  (innerSL ℝ (E := FieldSpace)) (J.toLp (p := 2) (μ := μ))

def generatingFunctional (J : TestFunction) : ℂ :=
  charFunDual dμ (pairingCLM J)

/- Local functionals on fields -/
def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ

/-! ### Lebesgue measure is invariant under every Euclidean motion -------- -/

open MeasureTheory

/-- For every rigid motion `g : E`, the push-forward of Lebesgue measure `μ`
    by the map `x ↦ g • x` is again `μ`. Equivalently, `act g` is
    measure-preserving. -/
lemma measurePreserving_act (g : E) :
    MeasurePreserving (fun x : RSpaceTime ↦ act g x) μ μ := by
  -- rotation/reflection part (orthogonal map is an isometry)
  have rot : MeasurePreserving (fun x : RSpaceTime ↦ g.R x) μ μ := by
    simpa using (g.R.toLinearIsometryEquiv rfl).measurePreserving
  -- translation part (Lebesgue measure is translation-invariant)
  have trans : MeasurePreserving (fun x : RSpaceTime ↦ x + g.t) μ μ := by
    refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
    simpa using map_add_right_eq_self μ g.t
  -- composition: `act g = translation ∘ rotation`
  simpa [act, Function.comp] using trans.comp rot

/-──────────────────────── helpers ────────────────────────-/

/-──────────────────────── field/test spaces ──────────────-/

instance : MeasurableSpace FieldSpace := by
  unfold FieldSpace; infer_instance
instance : BorelSpace FieldSpace := ⟨rfl⟩

/-──────────────────── handy inverse motion ───────────────-/
@[simp] def invE (g : E) : E :=
  ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-──────────────── pull/push (pre-compose with g⁻¹) ───────-/

/-- `x ↦ (invE g).R x + (invE g).t` is an affine map, hence smooth. -/
private lemma contDiff_act_inv (g : E) :
    ContDiff ℝ ⊤ (act (invE g)) := by
  have h₁ : ContDiff ℝ ⊤ (fun x : RSpaceTime ↦ (LinearIsometry.inv g.R) x) :=
    (LinearIsometry.inv g.R).contDiff
  have h₂ : ContDiff ℝ ⊤
      (fun _ : RSpaceTime ↦ -(LinearIsometry.inv g.R) g.t) :=
    contDiff_const
  simpa [act, invE, add_comm] using h₂.add h₁

private lemma measurable_act_inv (g : E) :
    Measurable (act (invE g)) := (contDiff_act_inv g).continuous.measurable

private lemma mp_act_inv (g : E) :
    MeasurePreserving (act (invE g)) μ μ := by
  simpa using measurePreserving_act (invE g)

/-──────────────── pull/push ─────────────────────────────-/

open SchwartzMap   -- for `compCLM`

/-- A *stub* definition that will compile as long as you allow `sorry`.
    It uses `SchwartzMap.compCLM` in the correct order but leaves both
    required proofs and the polynomial bound as `sorry`. -/
private lemma hg_up_nat (g : E) :
    ∃ k : ℕ, ∃ C : ℝ,
      ∀ x : RSpaceTime,
      ‖x‖ ≤ C * (1 + ‖act (invE g) x‖) ^ k := by
  -- Since `act (invE g)` is an affine isometry, we need a linear bound
  use 1, (1 + ‖g.t‖)
  intro x
  simp only [pow_one]
  have h_iso : ‖(LinearIsometry.inv g.R) x‖ = ‖x‖ :=
    (LinearIsometry.inv g.R).norm_map x
  rw [← h_iso]
  have h_act : act (invE g) x =
      (LinearIsometry.inv g.R) x + (invE g).t := by
    simp [act]
  have : act (invE g) x =
      (LinearIsometry.inv g.R) x + (invE g).t := by
    simp [act]
  rw [this]
  have h_ineq :
      ‖(LinearIsometry.inv g.R) x‖ ≤
        ‖(LinearIsometry.inv g.R) x + (invE g).t‖ + ‖(invE g).t‖ :=
    norm_le_add_norm_add _ _
  have h_t : ‖(invE g).t‖ = ‖g.t‖ := by
    simp [invE, norm_neg, (LinearIsometry.inv g.R).norm_map]
  rw [h_t] at h_ineq
  calc
    ‖(LinearIsometry.inv g.R) x‖
        ≤ ‖act (invE g) x‖ + ‖g.t‖ := h_ineq
    _ ≤ (1 + ‖g.t‖) * (1 + ‖act (invE g) x‖) := by
      have h1 : 0 ≤ ‖act (invE g) x‖ := norm_nonneg _
      have h2 : 0 ≤ ‖g.t‖ := norm_nonneg _
      ring_nf
      linarith [mul_nonneg h2 h1]

/-! ### Isometries are temperate --------------------------------------- -/
open scoped Real
open Function

lemma cd_act_inv (g : E) :
    ContDiff ℝ ⊤ (act (invE g)) :=
  contDiff_act_inv g        -- you proved this earlier


          -- temperate-growth certificate

-- Helper: The fderiv of act (invE g) has temperate growth
private def fderiv_has_temperate_growth (g : E) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act (invE g)) x) := by
  -- The fderiv of an affine map f(x) = Ax + b is the constant function x ↦ A
  -- So we need to show a constant CLM-valued function has temperate growth

  -- First, show that fderiv is constant and equals the linear part
  have h_fderiv : ∀ x, fderiv ℝ (act (invE g)) x = (LinearIsometry.inv g.R).toContinuousLinearMap := by
    intro x
    -- act (invE g) y = (LinearIsometry.inv g.R) y + (invE g).t
    -- The fderiv of y ↦ Ay + b is A
    sorry

  -- Now use that constant functions have temperate growth
  simp_rw [h_fderiv]
  exact Function.HasTemperateGrowth.const _

-- Helper: Polynomial bound for act (invE g)
private def act_inv_poly_bound (g : E) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : RSpaceTime, ‖act (invE g) x‖ ≤ C * (1 + ‖x‖) ^ k := by
  -- act (invE g) x = (LinearIsometry.inv g.R) x + (invE g).t
  -- This is affine, so linear growth (k=1) suffices
  use 1, (1 + ‖(invE g).t‖)
  intro x
  have : act (invE g) x = (LinearIsometry.inv g.R) x + (invE g).t := by
    simp [act, invE]
  rw [this]
  calc ‖(LinearIsometry.inv g.R) x + (invE g).t‖
      ≤ ‖(LinearIsometry.inv g.R) x‖ + ‖(invE g).t‖ := norm_add_le _ _
    _ = ‖x‖ + ‖(invE g).t‖ := by rw [(LinearIsometry.inv g.R).norm_map x]
    _ ≤ (1 + ‖(invE g).t‖) * (1 + ‖x‖)^1 := by
        simp only [pow_one]
        ring_nf
        have h1 : 0 ≤ ‖x‖ := norm_nonneg x
        have h2 : 0 ≤ ‖(invE g).t‖ := norm_nonneg _
        linarith [mul_nonneg h2 h1]

private def helper_htg (g : E) : Function.HasTemperateGrowth (act (invE g)) := by
  -- Extract k and C from the polynomial bound first
  obtain ⟨k, C, hbound⟩ := act_inv_poly_bound g
  -- Apply of_fderiv with the three required arguments
  exact Function.HasTemperateGrowth.of_fderiv
    (fderiv_has_temperate_growth g)
    ((contDiff_act_inv g).differentiable le_top)
    hbound

noncomputable def TestFunction.push (g : E) (J : TestFunction) : TestFunction :=
  SchwartzMap.compCLM ℝ (g := act (invE g)) (helper_htg g) (hg_up_nat g) J




@[simp] lemma TestFunction.push_apply
    (g : E) (J : TestFunction) (x : RSpaceTime) :
    TestFunction.push g J x = J (act (invE g) x) := rfl

/-! ####################################################################
      Stubbed pull-back on L² fields and the OS-2 axiom
##################################################################### -/

-- ❶ placeholder pull-back (currently just the identity map)
noncomputable def FieldSpace.pull (g : E) (φ : FieldSpace) : FieldSpace := φ

-- measurability needed for `Measure.map`
lemma pull_measurable (g : E) : Measurable (FieldSpace.pull g) := by
  unfold FieldSpace.pull
  exact measurable_id

/-- A probability law is **Euclidean-invariant** if, for every Euclidean
    motion `g`, the pull-back of the measure by `g` equals the original
    measure. -/
def EuclideanInvariant (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∀ g : E,
    Measure.map (FieldSpace.pull g) (dμ : Measure FieldSpace)
      = (dμ : Measure FieldSpace)

axiom OS2 (dμ : ProbabilityMeasure FieldSpace) :
  EuclideanInvariant dμ
