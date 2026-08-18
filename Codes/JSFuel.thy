theory JSFuel
imports JSEval
begin

(* ==========================================================================
   Fuel infrastructure for eval_expr_fuel
   ========================================================================== *)

definition out_of_fuel :: "js_vle => bool" where
  "out_of_fuel v = (v = VTypeError ''Out of fuel'')"


(* --------------------------------------------------------------------------
   Fuel zero
   -------------------------------------------------------------------------- *)

lemma eval_expr_fuel_0:
  "eval_expr_fuel 0 e s = (VTypeError ''Out of fuel'', s)"
  by simp


lemma eval_exprs_fuel_0:
  "eval_exprs_fuel 0 es s = ([], s)"
  by simp


lemma out_of_fuel_eval_expr_fuel_0:
  "out_of_fuel (fst (eval_expr_fuel 0 e s))"
  by (simp add: out_of_fuel_def)


(* --------------------------------------------------------------------------
   Functional determinism

   eval_expr_fuel is a HOL function, therefore evaluation with the same
   fuel, expression and initial state has a unique result.
   -------------------------------------------------------------------------- *)

lemma eval_expr_fuel_deterministic:
  assumes
    "eval_expr_fuel n e s = r1"
    "eval_expr_fuel n e s = r2"
  shows
    "r1 = r2"
  using assms by simp


lemma eval_exprs_fuel_deterministic:
  assumes
    "eval_exprs_fuel n es s = r1"
    "eval_exprs_fuel n es s = r2"
  shows
    "r1 = r2"
  using assms by simp


lemma run_handler_deterministic:
  assumes
    "run_handler target_id h s = s1"
    "run_handler target_id h s = s2"
  shows
    "s1 = s2"
  using assms by simp


(* --------------------------------------------------------------------------
   Successful top-level evaluation
   -------------------------------------------------------------------------- *)

definition eval_succeeds :: "nat => expr => js_state => bool" where
  "eval_succeeds n e s =
     (~ out_of_fuel (fst (eval_expr_fuel n e s)))"


(* --------------------------------------------------------------------------
   Relationship between eval_expr and default_fuel.

   This is NOT fuel monotonicity.  It only unfolds the definition of
   eval_expr, whose implementation uses default_fuel.
   -------------------------------------------------------------------------- *)

lemma eval_expr_is_default_fuel:
  "eval_expr e s = eval_expr_fuel default_fuel e s"
  by (simp add: eval_expr_def)


lemma eval_expr_result_default_fuel:
  assumes "eval_expr e s = (v, s')"
  shows "eval_expr_fuel default_fuel e s = (v, s')"
  using assms
  by (simp add: eval_expr_def)


(* ==========================================================================
   IMPORTANT NOTE

   A general theorem of the form

     eval_expr_fuel n e s = (v,s')
     ==> ~ out_of_fuel v
     ==> n <= m
     ==> eval_expr_fuel m e s = (v,s')

   is NOT established for the current evaluator.

   The current semantics does not propagate fuel exhaustion through all
   compound expressions.

   For example, in a binary operation, a recursive evaluation can return

       VTypeError ''Out of fuel''

   and eval_binop can subsequently replace this value by another VTypeError.
   Therefore the final value may satisfy ~ out_of_fuel even though an
   internal recursive call exhausted its fuel.

   The evaluator must first be changed so that fuel exhaustion propagates
   explicitly through compound evaluations before the desired general fuel
   monotonicity theorem can be proved soundly.
   ========================================================================== *)

end