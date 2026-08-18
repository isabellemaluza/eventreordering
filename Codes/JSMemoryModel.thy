theory JSMemoryModel
imports Complex_Main
begin

(* ==========================================================================
   Tipos base
   ========================================================================== *)

datatype builtin =
    BAlert
  | BChangeColor
  | BCreateElement

datatype js_vle =
    VNumber real
  | VNaN
  | VBool bool
  | VString string
  | VNull
  | VUndefined
  | VRef nat
  | VObject "(string * js_vle) list"
  | VWindow "(string * js_vle) list"
  | VDOMElement string "(string * js_vle) list"   (* representação ÚNICA de elemento DOM *)
  | VFunction "string list" expr "(string * js_vle) list"
  | VBuiltin builtin
  | VTypeError string

and expr =
    EConst js_vle
  | EVar string
  | EAssign string expr
  | EBinOp string expr expr
  | ECall expr "expr list"
  | EIf expr expr expr
  | ESeq expr expr
  | EReturn expr

type_synonym frame = "(string * js_vle) list"
type_synonym stack = "frame list"
type_synonym heap  = "(nat * js_vle) list"

type_synonym event       = "string * expr"
type_synonym event_queue = "event list"

record js_state =
  Stack_s  :: stack
  Heap_s   :: heap
  Events_s :: event_queue
  Alerts_s :: "string list"

(* ==========================================================================
   Propriedades de objetos
   ========================================================================== *)

fun get_prop :: "string => (string * js_vle) list => js_vle option" where
  "get_prop key [] = None"
| "get_prop key ((k,v)#xs) = (if k = key then Some v else get_prop key xs)"

fun update_prop :: "string => js_vle => (string * js_vle) list => (string * js_vle) list" where
  "update_prop key val [] = [(key,val)]"
| "update_prop key val ((k,v)#xs) =
     (if k = key then (key,val)#xs else (k,v)#update_prop key val xs)"

(* ==========================================================================
   Pilha (variáveis léxicas)
   ========================================================================== *)

fun lookup_stack :: "string => stack => js_vle option" where
  "lookup_stack x [] = None"
| "lookup_stack x (frame # rest) =
     (case map_of frame x of
        Some v => Some v
      | None   => lookup_stack x rest)"

fun load_var :: "string => js_state => js_vle option" where
  "load_var x state = lookup_stack x (Stack_s state)"

fun update_in_frame :: "string => js_vle => frame => frame" where
  "update_in_frame x v [] = [(x,v)]"
| "update_in_frame x v ((k,val)#xs) =
     (if x = k then (x,v)#xs else (k,val)#update_in_frame x v xs)"

fun write_var :: "string => js_vle => js_state => js_state" where
  "write_var x v state =
     (case Stack_s state of
        []          => state(|Stack_s := [[(x,v)]]|)
      | frame # rest => state(|Stack_s := update_in_frame x v frame # rest|))"

fun push_frame :: "frame => js_state => js_state" where
  "push_frame f state = state(|Stack_s := f # Stack_s state|)"

fun pop_frame :: "js_state => js_state" where
  "pop_frame state =
     (case Stack_s state of
        []       => state
      | _ # rest => state(|Stack_s := rest|))"

(* ==========================================================================
   Heap
   ========================================================================== *)

fun load_object :: "nat => js_state => js_vle option" where
  "load_object obj_id state =
     (case find (%(k, v). k = obj_id) (Heap_s state) of
        None        => None
      | Some (_, v) => Some v)"

fun load_global :: "string => js_state => js_vle option" where
  "load_global name state =
     (case load_object 0 state of
        Some (VWindow props) => get_prop name props
      | _                    => None)"

fun max_heap_id :: "heap => nat" where
  "max_heap_id [] = 0"
| "max_heap_id ((k,_)#rest) = max k (max_heap_id rest)"

fun alloc_object :: "(string * js_vle) list => js_state => (nat * js_state)" where
  "alloc_object props state =
     (let new_id   = max_heap_id (Heap_s state) + 1;
          new_heap = (new_id, VObject props) # Heap_s state
      in (new_id, state(|Heap_s := new_heap|)))"

fun alloc_dom_element :: "string => (string * js_vle) list => js_state => (nat * js_state)" where
  "alloc_dom_element tag props state =
     (let new_id   = max_heap_id (Heap_s state) + 1;
          new_heap = (new_id, VDOMElement tag props) # Heap_s state
      in (new_id, state(|Heap_s := new_heap|)))"

fun write_object :: "nat => js_vle => js_state => js_state" where
  "write_object obj_id v state =
     (let new_heap = (obj_id, v) # filter (%(k, _). k ~= obj_id) (Heap_s state)
      in state(|Heap_s := new_heap|))"

fun remove_object :: "nat => js_state => js_state" where
  "remove_object obj_id state =
     state(|Heap_s := filter (%(k,_). k ~= obj_id) (Heap_s state)|)"

fun write_dom_element :: "nat => string => (string * js_vle) list => js_state => js_state" where
  "write_dom_element obj_id tag props state = write_object obj_id (VDOMElement tag props) state"

fun write_window :: "nat => (string * js_vle) list => js_state => js_state" where
  "write_window obj_id props state = write_object obj_id (VWindow props) state"

fun insert_dom_element :: "nat => string => (string * js_vle) list => js_state => js_state" where
  "insert_dom_element obj_id tag props state = write_object obj_id (VDOMElement tag props) state"

(* Operação de domínio reutilizada por: o builtin changeColor (JSEval),
   os testes de querySelector (JSQuerySelector) e as provas de idempotência
   (JSProofs). Antes existiam três implementações distintas disso — agora
   é uma só. *)
fun change_element_color :: "nat => string => js_state => js_state" where
  "change_element_color obj_id color state =
     (case load_object obj_id state of
        Some (VDOMElement tag props) =>
          write_dom_element obj_id tag (update_prop ''color'' (VString color) props) state
      | _ => state)"

(* ==========================================================================
   Estado inicial canônico

   Um único estado inicial "vazio" (só a window global com os builtins).
   Qualquer estado "com DOM" é obtido aplicando alloc_dom_element /
   build_dom_list (ver JSDOM) sobre este estado — nunca escrevendo o heap
   à mão com ids fixos.
   ========================================================================== *)

definition browser_init_state :: js_state where
  "browser_init_state = (|
     Stack_s  = [],
     Heap_s   = [
       (0, VWindow [
             (''alert'',        VBuiltin BAlert),
             (''changeColor'',  VBuiltin BChangeColor),
             (''createElement'', VBuiltin BCreateElement)
           ])
     ],
     Events_s = [],
     Alerts_s = []
   |)"

value "browser_init_state"
value "load_object 0 browser_init_state"
value "alloc_dom_element ''div'' [(''color'', VString ''red'')] browser_init_state"

end
