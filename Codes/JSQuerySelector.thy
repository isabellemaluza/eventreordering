theory JSQuerySelector
imports JSDOM
begin

(* Antes esta theory tratava "elemento DOM" como um VObject genérico com
   uma prop "tag" (is_dom_element / tag_of / matches_selector casavam em
   VObject). Isso duplicava a noção de elemento já existente como
   VDOMElement (usada por JSDOM/JSEvents/JSRender). Agora tudo casa
   diretamente em VDOMElement, e a troca de cor usa
   JSMemoryModel.change_element_color em vez de uma implementação própria
   de "set_style_color_at". *)

fun tag_of :: "js_vle => string option" where
  "tag_of (VDOMElement t _) = Some t"
| "tag_of _ = None"

datatype selector =
    SelTag string
  | SelClass string
  | SelId string
  | SelUnsupported string

fun parse_selector :: "string => selector" where
  "parse_selector [] = SelUnsupported []"
| "parse_selector (c # cs) =
     (if c = CHR ''.'' then SelClass cs
      else if c = CHR ''#'' then SelId cs
      else SelTag (c # cs))"

fun matches_selector :: "js_vle => selector => bool" where
  "matches_selector v (SelTag t) = (tag_of v = Some t)"
| "matches_selector v (SelClass c) =
     (case v of
        VDOMElement _ props => get_prop ''class'' props = Some (VString c)
      | _ => False)"
| "matches_selector v (SelId i) =
     (case v of
        VDOMElement _ props => get_prop ''id'' props = Some (VString i)
      | _ => False)"
| "matches_selector _ (SelUnsupported _) = False"

fun querySelector :: "js_state => string => nat option" where
  "querySelector st selStr =
     (let sel = parse_selector selStr
      in case find (%(k, v). matches_selector v sel) (Heap_s st) of
           None        => None
         | Some (k, _) => Some k)"

fun querySelectorAll :: "js_state => string => nat list" where
  "querySelectorAll st selStr =
     (let sel = parse_selector selStr
      in map fst (filter (%(k, v). matches_selector v sel) (Heap_s st)))"

definition JS_querySelector_blue :: "string => js_state => js_state" where
  "JS_querySelector_blue sel st =
     (case querySelector st sel of
        None        => st
      | Some obj_id => change_element_color obj_id ''blue'' st)"

definition JS_querySelectorAll_yellow :: "string => js_state => js_state" where
  "JS_querySelectorAll_yellow sel st =
     fold (%obj_id acc. change_element_color obj_id ''yellow'' acc) (querySelectorAll st sel) st"

(* Demo construída em cima do estado canônico dom_state (JSDOM), apenas
   acrescentando alguns elementos via alloc_dom_element — nunca escrevendo
   ids de heap à mão. *)
definition demo_state :: js_state where
  "demo_state =
     (let (_, s1) = alloc_dom_element ''li'' [(''class'', VString ''item'')] dom_state;
          (_, s2) = alloc_dom_element ''li'' [(''id'', VString ''special'')] s1
      in s2)"

value "demo_state"
value "querySelector demo_state ''p''"
value "querySelector demo_state ''#msg''"
value "querySelectorAll demo_state ''li''"
value "JS_querySelector_blue ''#msg'' demo_state"
value "JS_querySelectorAll_yellow ''li'' demo_state"

end
