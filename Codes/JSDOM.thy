theory JSDOM
imports JSHTMLSyntax
begin

(* Constrói o DOM (sempre como VDOMElement no heap — nunca VObject "fingindo"
   ser elemento, nunca uma árvore js_node/node à parte) a partir da sintaxe
   HTML de superfície. *)

fun attr_to_prop :: "html_attr => (string * js_vle) list" where
  "attr_to_prop (Attr key val)   = [(key, VString val)]"
| "attr_to_prop (AttrOnClick e)     = [(''onclick'', VFunction [] e [])]"
| "attr_to_prop (AttrOnMouseOver e) = [(''onmouseover'', VFunction [] e [])]"

fun attrs_to_props :: "html_attr list => (string * js_vle) list" where
  "attrs_to_props [] = []"
| "attrs_to_props (a # as) = attr_to_prop a @ attrs_to_props as"

fun collect_text :: "html_node list => string" where
  "collect_text [] = ''''"
| "collect_text (HtmlText t # xs) = t @ collect_text xs"
| "collect_text (HtmlElement tag attrs children # xs) = collect_text xs"

fun build_dom_node :: "html_node => js_state => (nat * js_state)" where
  "build_dom_node (HtmlText txt) state =
     alloc_dom_element ''#text'' [(''text'', VString txt)] state"
| "build_dom_node (HtmlElement tag attrs children) state =
     (let props  = attrs_to_props attrs;
          txt    = collect_text children;
          props' = (if txt = '''' then props else (''text'', VString txt) # props)
      in alloc_dom_element tag props' state)"

fun build_dom_list :: "html_node list => js_state => js_state" where
  "build_dom_list [] state = state"
| "build_dom_list (n # ns) state =
     (let (_, s1) = build_dom_node n state
      in build_dom_list ns s1)"

definition sample_html :: "html_node list" where
  "sample_html = [
     HtmlElement ''p''
       [Attr ''id'' ''msg'', Attr ''color'' ''yellow'']
       [HtmlText ''Ola''],
     HtmlElement ''button''
       [AttrOnClick
          (ESeq
             (ECall (EVar ''alert'') [EConst (VString ''Ola'')])
             (ECall (EVar ''changeColor'')
                    [EVar ''this'', EConst (VString ''blue'')]))]
       [HtmlText ''Clique'']
   ]"

(* Estado canônico "com conteúdo": construído sempre a partir do estado
   inicial canônico (browser_init_state, definido em JSMemoryModel) —
   nunca com um heap escrito à mão. Esta é a referência usada por
   JSEvents, JSRender, JSQuerySelector e JSProofs. *)
definition dom_state :: js_state where
  "dom_state = build_dom_list sample_html browser_init_state"

value "sample_html"
value "dom_state"
value "load_object 0 dom_state"
value "load_object 1 dom_state"
value "load_object 2 dom_state"

end
