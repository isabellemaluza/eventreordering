theory JSEval
imports JSMemoryModel
begin

(* ==========================================================================
   Avaliador OFICIAL.

   Antes existiam três avaliadores incompatíveis (JSMemoryModelCmt.eval,
   JSEventSimulation.eval_expr_fuel, JSEvents.eval_expr). Este arquivo
   consolida tudo num único avaliador, baseado no antigo eval_expr_fuel
   (o mais completo: total via fuel, thread do estado, suporta EAssign e
   closures). Duas correções em relação ao original:

     1. Faltava o caso de ESeq (usado pelos handlers onclick com
        alert(...) seguido de changeColor(...)); adicionado abaixo.
     2. EVar agora cai para load_global quando a variável não está na
        pilha, para que "alert" / "changeColor" / "createElement"
        resolvam para os builtins da window (heap id 0).

   Os builtins (alert, changeColor, createElement) deixam de devolver uma
   lista de "outputs" para serem aplicados depois (como em JSEvents/
   JSRender antigos) — eles alteram o js_state diretamente, no mesmo
   passo da avaliação. Isso elimina a necessidade do tipo js_output.
   ========================================================================== *)

fun is_truthy :: "js_vle => bool" where
  "is_truthy (VBool b)        = b"
| "is_truthy VNull            = False"
| "is_truthy VUndefined       = False"
| "is_truthy VNaN             = False"
| "is_truthy (VNumber n)      = (n ~= 0)"
| "is_truthy (VString s)      = (s ~= '''')"
| "is_truthy (VObject _)      = True"
| "is_truthy (VDOMElement _ _) = True"
| "is_truthy (VWindow _)      = True"
| "is_truthy (VRef _)         = True"
| "is_truthy (VFunction _ _ _) = True"
| "is_truthy (VBuiltin _)     = True"
| "is_truthy (VTypeError _)   = False"

fun eval_binop :: "string => js_vle => js_vle => js_vle" where
  "eval_binop ''+'' (VNumber a) (VNumber b) = VNumber (a + b)"
| "eval_binop op _ _ = VTypeError (''Unsupported binop: '' @ op)"

fun eval_expr_fuel  :: "nat => expr => js_state => (js_vle * js_state)"
and eval_exprs_fuel :: "nat => expr list => js_state => (js_vle list * js_state)"
where
  "eval_expr_fuel 0 e st = (VTypeError ''Out of fuel'', st)"

| "eval_expr_fuel (Suc n) (EConst v) st = (v, st)"

| "eval_expr_fuel (Suc n) (EVar x) st =
     (case load_var x st of
        Some v => (v, st)
      | None =>
          (case load_global x st of
             Some v => (v, st)
           | None   => (VUndefined, st)))"

| "eval_expr_fuel (Suc n) (EAssign x e) st =
     (let (v, st1) = eval_expr_fuel n e st
      in (v, write_var x v st1))"

| "eval_expr_fuel (Suc n) (EBinOp op e1 e2) st =
     (let (v1, st1) = eval_expr_fuel n e1 st;
          (v2, st2) = eval_expr_fuel n e2 st1
      in (eval_binop op v1 v2, st2))"

| "eval_expr_fuel (Suc n) (EIf c t f) st =
     (let (vc, st1) = eval_expr_fuel n c st
      in if is_truthy vc then eval_expr_fuel n t st1 else eval_expr_fuel n f st1)"

| "eval_expr_fuel (Suc n) (ESeq e1 e2) st =
     (let (_, st1) = eval_expr_fuel n e1 st
      in eval_expr_fuel n e2 st1)"

| "eval_expr_fuel (Suc n) (EReturn e) st = eval_expr_fuel n e st"

| "eval_expr_fuel (Suc n) (ECall fexp args) st =
     (let (vf, st1)     = eval_expr_fuel n fexp st;
          (vargs, st2)  = eval_exprs_fuel n args st1
      in case vf of
           VBuiltin BAlert =>
             (case vargs of
                [VString msg] => (VUndefined, st2(|Alerts_s := Alerts_s st2 @ [msg]|))
              | _             => (VTypeError ''alert: bad args'', st2))

         | VBuiltin BChangeColor =>
             (case vargs of
                [VRef obj_id, VString color] =>
                  (VUndefined, change_element_color obj_id color st2)
              | _ => (VTypeError ''changeColor: bad args'', st2))

         | VBuiltin BCreateElement =>
             (case vargs of
                [VString tag] =>
                  (let (new_id, st3) = alloc_dom_element tag [] st2
                   in (VRef new_id, st3))
              | _ => (VTypeError ''createElement: bad args'', st2))

         | VFunction params body clos_env =>
             (let call_frame = zip params vargs @ clos_env;
                  st3        = push_frame call_frame st2;
                  (vres, st4) = eval_expr_fuel n body st3;
                  st5        = pop_frame st4
              in (vres, st5))

         | _ => (VTypeError ''Call on non-function'', st2))"

| "eval_exprs_fuel 0 es st = ([], st)"
| "eval_exprs_fuel (Suc n) [] st = ([], st)"
| "eval_exprs_fuel (Suc n) (e # es) st =
     (let (v1, st1) = eval_expr_fuel n e st;
          (vs, st2) = eval_exprs_fuel n es st1
      in (v1 # vs, st2))"

definition default_fuel :: nat where
  "default_fuel = 200"

definition eval_expr :: "expr => js_state => (js_vle * js_state)" where
  "eval_expr e st = eval_expr_fuel default_fuel e st"

definition eval_exprs :: "expr list => js_state => (js_vle list * js_state)" where
  "eval_exprs es st = eval_exprs_fuel default_fuel es st"

(* Executa o corpo de um handler de evento (ex.: onclick) associado ao
   elemento target_id, vinculando "this" a uma referência ao próprio
   elemento. Usado por JSEvents.make_event_handler. *)
fun run_handler :: "nat => js_vle => js_state => js_state" where
  "run_handler target_id (VFunction params body clos_env) st =
     (let frame       = clos_env @ [(''this'', VRef target_id)];
          st1         = push_frame frame st;
          (_, st2)    = eval_expr body st1
      in pop_frame st2)"
| "run_handler _ _ st = st"

value "eval_expr (EBinOp ''+'' (EConst (VNumber 1)) (EConst (VNumber 2))) browser_init_state"
value "eval_expr (ECall (EVar ''alert'') [EConst (VString ''oi'')]) browser_init_state"

end
