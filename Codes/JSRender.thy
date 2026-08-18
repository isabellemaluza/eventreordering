theory JSRender
imports JSEvents
begin

(* A antiga camada js_output / apply_output / step foi removida: como
   JSEval agora aplica os efeitos de alert/changeColor diretamente no
   js_state durante a avaliação, não existe mais uma lista de "outputs"
   intermediária para "aplicar" depois. Quem quiser mudar a cor de um
   elemento usa JSMemoryModel.change_element_color diretamente. *)

type_synonym dom_pos = "(nat * nat) list"

fun build_pos :: "html_node list => nat => nat => dom_pos" where
  "build_pos [] _ _ = []"
| "build_pos (_ # ns) heap_start pos =
     (heap_start, pos) # build_pos ns (heap_start + 1) (pos + 1)"

fun lookup_pos :: "nat => dom_pos => nat option" where
  "lookup_pos _ [] = None"
| "lookup_pos oid ((k, p) # xs) = (if oid = k then Some p else lookup_pos oid xs)"

fun prop_to_attr :: "string * js_vle => html_attr option" where
  "prop_to_attr (k, v) =
     (if k = ''text'' then None
      else case (k, v) of
             (''onclick'',      VFunction _ body _) => Some (AttrOnClick body)
           | (''onmouseover'',  VFunction _ body _) => Some (AttrOnMouseOver body)
           | (_,                VString s)          => Some (Attr k s)
           | _                                      => None)"

fun props_to_attrs :: "(string * js_vle) list => html_attr list" where
  "props_to_attrs [] = []"
| "props_to_attrs (p # ps) =
     (case prop_to_attr p of
        Some a => a # props_to_attrs ps
      | None   => props_to_attrs ps)"

fun props_to_text :: "(string * js_vle) list => html_node list" where
  "props_to_text [] = []"
| "props_to_text ((k, VString v) # ps) =
     (if k = ''text'' then [HtmlText v] else props_to_text ps)"
| "props_to_text (_ # ps) = props_to_text ps"

fun dom_to_html_node :: "string => (string * js_vle) list => html_node" where
  "dom_to_html_node tag props = HtmlElement tag (props_to_attrs props) (props_to_text props)"

fun collect_dom_nodes :: "heap => dom_pos => (nat * html_node) list" where
  "collect_dom_nodes [] _ = []"
| "collect_dom_nodes ((oid, VDOMElement tag props) # rest) pos =
     (case lookup_pos oid pos of
        Some p => (p, dom_to_html_node tag props) # collect_dom_nodes rest pos
      | None   => collect_dom_nodes rest pos)"
| "collect_dom_nodes (_ # rest) pos = collect_dom_nodes rest pos"

fun insert_by_pos :: "(nat * html_node) => (nat * html_node) list => (nat * html_node) list" where
  "insert_by_pos x [] = [x]"
| "insert_by_pos (p, n) ((q, m) # xs) =
     (if p <= q then (p, n) # (q, m) # xs else (q, m) # insert_by_pos (p, n) xs)"

fun sort_by_pos :: "(nat * html_node) list => (nat * html_node) list" where
  "sort_by_pos [] = []"
| "sort_by_pos (x # xs) = insert_by_pos x (sort_by_pos xs)"

fun strip_pos :: "(nat * html_node) list => html_node list" where
  "strip_pos [] = []"
| "strip_pos ((_, n) # xs) = n # strip_pos xs"

definition tohtml :: "js_state => dom_pos => html_node list" where
  "tohtml state pos = strip_pos (sort_by_pos (collect_dom_nodes (Heap_s state) pos))"

(* heap_start = 1 porque o id 0 é sempre a VWindow em browser_init_state *)
definition sample_pos :: dom_pos where
  "sample_pos = build_pos sample_html 1 0"

value "dom_state"
value "sample_pos"
value "tohtml dom_state sample_pos"

(* Dispara o click no botão (obj 2); o estado resultante já tem o alerta
   registrado e a cor do parágrafo (obj 1) trocada — sem passo intermediário. *)
value "make_event_handler EvClick 2 dom_state"
value "Alerts_s (make_event_handler EvClick 2 dom_state)"
value "load_object 1 (make_event_handler EvClick 2 dom_state)"
value "tohtml (make_event_handler EvClick 2 dom_state) sample_pos"

(* Mudar a cor diretamente, sem passar por evento algum *)
value "tohtml (change_element_color 1 ''red'' dom_state) sample_pos"

end
