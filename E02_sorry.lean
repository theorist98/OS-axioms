/-© 2025 SYH - OS-2 (Euclidean invariance)
-/

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

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory

/-OS2 R^d with d=4, where mu is the Lebegue measure.
We know the OS2 dp must be Euclidean invariant -/

def STDimension := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume    -- Lebesgue, just named “μ”

open scoped Real InnerProductSpace
open MeasureTheory
namespace QFT



/-!L² real-valued fields, the OS2 lines S_J is invariant,
the pullback on L^2 require an actual L^2 Banach space and establish the sigma alg -/

abbrev FieldSpace' := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace' := borel _
instance : BorelSpace    FieldSpace' := ⟨rfl⟩

/-- Orthogonal linear isometries of ℝ⁴ (the group O(4)).
LinearIsometry is an orthogonal linear map, ie an element of O(4)-/
abbrev O4 : Type :=
  LinearIsometry (RingHom.id ℝ) RSpaceTime RSpaceTime


/-!  Euclidean group -/
/-- Euclidean motion = rotation / reflection + translation. E= R^4 x O(4)-/
structure E where
  R : O4
  t : RSpaceTime

/-- Action of g : E on a spacetime point x.
Impliments the pullback map x to Rx+ t -/
def act (g : E) (x : RSpaceTime) : RSpaceTime := g.R x + g.t

/-act_one, act_mul and act_inv lemmas prove
identity, composition and inverse. They are needed to say Euclidean sym
form a group. This mirrors OS-2's S_j= S_{EJ} -/
@[simp] lemma act_one   (x : RSpaceTime) : act ⟨1,0⟩ x = x := by
  simp [act]

@[simp] lemma act_mul   (g h : E) (x : RSpaceTime) :
    act ⟨g.R.comp h.R, g.R h.t + g.t⟩ x = g.R (h.R x + h.t) + g.t := by
  simp [act, add_comm, add_left_comm, add_assoc]

@[simp] lemma act_inv (g : E) (x : RSpaceTime) :
    act ⟨g.R, -g.R g.t⟩ x = g.R (x - g.t) := by
  -- unfold the two sides and use linearity of g.R
  simp [act, sub_eq_add_neg, map_add, map_neg]
        -- the map_sub lemma is in mathlib
/- Linear-iso helper lemmas are explicitly in Os-2
but are used as a counter part to rotations that preserve the metric and R^-1 R=1-/
open LinearIsometryEquiv

namespace LinearIsometry
/-- Inverse of a linear isometry : we turn the canonical equivalence
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
  simpa [comp_apply, inv_apply, one_apply] using congrArg (fun v : RSpaceTime => v i) h

end LinearIsometry
/-(extentionality) Allows Lean to prove equality of Euclidean motions by checking the R and t
components separately—hugely convenient for the group-law proofs. -/
@[ext] lemma E.ext {g h : E} (hR : g.R = h.R) (ht : g.t = h.t) : g = h := by
  cases g; cases h; cases hR; cases ht; rfl

/-!  ##  Group structure on `E`  ----------------------------------------- -/

/- 1.  Primitive instances of group operations
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

/- helper lemmas mirroring (g. h)_R= g_R dot h_r, and
(g.h)_t= g_R h_t+ g_t)-
-/
@[simp] lemma mul_R (g h : E) : (g * h).R = g.R.comp h.R := rfl
@[simp] lemma mul_t (g h : E) : (g * h).t = g.R h.t + g.t := rfl
@[simp] lemma one_R : (1 : E).R = 1 := rfl
@[simp] lemma one_t : (1 : E).t = 0 := rfl
@[simp] lemma inv_R (g : E) : (g⁻¹).R = LinearIsometry.inv g.R := rfl
@[simp] lemma inv_t (g : E) : (g⁻¹).t = -(LinearIsometry.inv g.R) g.t := rfl

/-- LinearIsometry.comp is associative.
OS-2’s “group” assertion needs rotation composition to be associative; this
lemma certifies it for Lean.
-/
@[simp] lemma LinearIsometry.comp_assoc (f g h : O4) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext x; rfl




/-Provides the formal group demanded by OS-2’s statement
“Euclidean transformations define a group.”-/
instance : Group E where
  mul := (· * ·)
  one := (1 : E)
  inv := Inv.inv

  -- associativity
  mul_assoc a b c := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_assoc]
    · simp [mul_t, add_comm, add_left_comm, add_assoc]

  -- left and right identity
  one_mul a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.one_comp]
    · simp [mul_t, one_t]

  mul_one a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_one]
    · simp [mul_t, one_t]
  inv_mul_cancel a := by
    -- prove  a⁻¹ * a = 1
    apply E.ext
    · simp [mul_R, inv_R, one_R, LinearIsometry.inv_comp]
    · simp [mul_t, inv_t, one_t, add_comm]

/-theorem ---------------------------------------------

     For all Euclidean motions g,h and every point x ∈ ℝ⁴ we have
         act (g * h) x  =  act g (act h x).
     In words: the `act` map is a group action of E on spacetime.

     We also prove the inverse law
         act g⁻¹ (act g x) = x.
-/

/-for all Euclidean motions g and h and any point x ∈ ℝ⁴, pulling x forward by the product g*h equals pulling by h first and then by g.
This is precisely the group-action law(𝑔ℎ)⁣⋅𝑥=𝑔.(ℎ. 𝑥)(gh)⋅x=g⋅(h⋅x).-/

@[simp] lemma act_mul_general (g h : E) (x : RSpaceTime) :
    act (g * h) x = act g (act h x) := by
  -- destructure g and h so Lean can see their components
/-cases on g/h: expands each motion into its components
gR : O4 the rotation, gt : ℝ⁴ the translation.
hR, ht likewise. That lets Lean see the literal structure of g*h.-/
  cases g with
  | mk gR gt =>
    cases h with
    | mk hR ht =>
      -- unfold everything; `mul_R`, `mul_t` give the components of g*h
      /-simp does it all:

act unfolds to R x + t.

mul_R, mul_t give formulas for the rotation/translation of g*h.

A handful of commutativity/associativity lemmas reorganise 𝑔𝑅(ℎ𝑅𝑥+ℎ𝑡)+𝑔𝑡gR(hRx+ht)+g
t into the desired form.
→ Goal reduces to reflexive equality, proof finished.-/
      simp [act, mul_R, mul_t, add_comm, add_left_comm, add_assoc]

/-Statement: applying g to x and then applying the inverse motion g⁻¹ returns you to x.
This is the inverse law of a group action.-/
/-Result: we’ve established that act : E → (ℝ⁴ → ℝ⁴) is a homomorphism into the function-composition monoid—exactly what OS-2 needs for its pull-back action on fields.-/

@[simp] lemma act_inv_general (g : E) (x : RSpaceTime) :
    act g⁻¹ (act g x) = x := by
  cases g with
  | mk gR gt =>
      -- unfold act, inverse components, then use linearity of gR
      simp [act, inv_R, inv_t, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
/-Result: confirms that act really is a faithful left action of the Euclidean group; no hidden sign or composition mistakes remain.-/



/-We still need a measure-preservation lemma
Need a lemma MeasurePreserving (act g) μ μ.
That will give the analytic statement “dp = E_* dp”-/

/-! ### Lebesgue measure is invariant under every Euclidean motion --------- -/




abbrev TestFunction : Type := SchwartzMap RSpaceTime ℝ
abbrev TestFunctionℂ : Type := SchwartzMap RSpaceTime ℂ

abbrev FieldSpace := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

abbrev ComplexFieldSpace := Lp (p := 2) (μ := μ) ℂ
instance : MeasurableSpace ComplexFieldSpace := borel _
instance : BorelSpace    ComplexFieldSpace := ⟨rfl⟩

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

variable (dμ' : ProbabilityMeasure ComplexFieldSpace)

/- Generating functional of correlation functions -/

def pairingCLM (J : TestFunction) : FieldSpace →L[ℝ] ℝ :=
  (innerSL ℝ (E := FieldSpace))
    (J.toLp (p := 2) (μ := μ))

def generatingFunctional (J : TestFunction) : ℂ :=
  charFunDual dμ (pairingCLM J)

/- Local functionals on fields -/
def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ

/-! ### Lebesgue measure is invariant under every Euclidean motion --------- -/

open MeasureTheory
/-- For every rigid motion `g : E`, the push‑forward of Lebesgue measure `μ`
    by the map `x ↦ g • x` is again `μ`.  Equivalently, `act g` is
    measure‑preserving. -/
lemma measurePreserving_act (g : E) :
    MeasurePreserving (fun x : RSpaceTime => act g x) μ μ := by
  -- rotation / reflection part (orthogonal map is an isometry)
  have rot : MeasurePreserving (fun x : RSpaceTime => g.R x) μ μ := by
    simpa using (g.R.toLinearIsometryEquiv rfl).measurePreserving

  -- translation part (Lebesgue measure is translation‑invariant)
  have trans : MeasurePreserving (fun x : RSpaceTime => x + g.t) μ μ := by
    refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
    simpa using map_add_right_eq_self μ g.t
  -- composition:  act g = translation ∘ rotation
  simpa [act, Function.comp] using trans.comp rot

  /-────────────────────────  helpers  ────────────────────────-/


/-────────────────────────  field/test spaces  ────────────────────────-/



instance : MeasurableSpace FieldSpace := by
  unfold FieldSpace; infer_instance
instance : BorelSpace FieldSpace := ⟨rfl⟩

/-─────────────────────  handy inverse motion  ───────────────────────-/

@[simp] def invE (g : E) : E :=
  ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-──────────────── pull / push  (pre‑compose with g⁻¹) ───────────────-/

/-────────────────────────  helpers  ────────────────────────-/


/-- `x ↦ (invE g).R x + (invE g).t` is an affine map, hence smooth. -/
private lemma contDiff_act_inv (g : E) :
    ContDiff ℝ ⊤ (act (invE g)) := by
  -- linear part
  have h₁ : ContDiff ℝ ⊤ (fun x : RSpaceTime =>
      (LinearIsometry.inv g.R) x) :=
    (LinearIsometry.inv g.R).contDiff
  -- constant translation
  have h₂ : ContDiff ℝ ⊤
      (fun _ : RSpaceTime => -(LinearIsometry.inv g.R) g.t) :=
    contDiff_const
  -- sum is smooth
  simpa [act, invE, add_comm] using h₂.add h₁

private lemma measurable_act_inv (g : E) :
    Measurable (act (invE g)) := (contDiff_act_inv g).continuous.measurable


private lemma mp_act_inv (g : E) :
    MeasurePreserving (act (invE g)) μ μ :=
  by
    simpa using measurePreserving_act (invE g)

/-──────────────────  pull / push  ─────────────────────────-/

open MeasureTheory
open SchwartzMap   -- for compCLM



/--
A *stub* definition that will compile as long as you allow `sorry`.
It uses `SchwartzMap.compCLM` in the correct order but leaves both
required proofs and the polynomial bound as `sorry`.
-/
private lemma hg_up_nat (g : E) :
    ∃ k : ℕ, ∃ C : ℝ,
      ∀ x : RSpaceTime,
        ‖x‖ ≤ C * (1 + ‖act (invE g) x‖) ^ k := by
  -- TODO: give a real bound; `sorry` is fine for now
  sorry


noncomputable def TestFunction.push (g : E) (J : TestFunction) : TestFunction :=
  by
    -- you *must* fill these two sorries to eliminate all red:
    have hg     : Function.HasTemperateGrowth (act (invE g)) := sorry
    have hg_up  : ∃ k C : ℝ, ∀ x : RSpaceTime,
                    ‖x‖ ≤ C * (1 + ‖act (invE g) x‖) ^ k      := sorry

    exact
     (SchwartzMap.compCLM ℝ hg (hg_up_nat g)) J



@[simp] lemma TestFunction.push_apply
    (g : E) (J : TestFunction) (x : RSpaceTime) :
    TestFunction.push g J x = J (act (invE g) x) := by
  -- once the two sorries above are replaced by real proofs
  -- the linear‐map produced by `compCLM` *does* evaluate to `λx, J (act…)`,
  -- hence `rfl` works here.
  rfl

/-! ####################################################################
     Stubbed pull‑back on L² fields and the OS‑2 axiom
######################################################################## -/

-- ❶ placeholder pull‑back (currently just the identity map)
noncomputable def FieldSpace.pull (g : E) (φ : FieldSpace) : FieldSpace := φ

-- measurability needed for `Measure.map`
lemma pull_measurable (g : E) : Measurable (FieldSpace.pull g) := by
  simpa using measurable_id

/-- A probability law is **Euclidean‑invariant** if, for every Euclidean
    motion `g`, the pull‑back of the measure by `g` equals the original
    measure. -/
def EuclideanInvariant (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∀ g : E,
    Measure.map (FieldSpace.pull g) (dμ : Measure FieldSpace)
      = (dμ : Measure FieldSpace)

/-- **OS‑2 (axiom).** We assume the field law is Euclidean‑invariant. -/
axiom OS2 (dμ : ProbabilityMeasure FieldSpace) : EuclideanInvariant dμ
