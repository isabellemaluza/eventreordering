theory JSEvents
imports JSDOM JSEval
begin

(* Antes esta theory tinha seu PRÓPRIO eval_expr (assinatura
   expr => nat => js_state => (js_state × js_output list)), que só entendia
   ESeq e chamadas literais a "alert"/"changeColor". Isso duplicava o
   avaliador oficial e não suportava EIf, EBinOp, EAssign, closures, etc.

   Agora o disparo de evento é: achar o objeto DOM alvo no heap, ler a
   propriedade do handler (onclick/onmouseover), e rodar o corpo com o
   avaliador oficial (JSEval.run_handler), que já injeta "this" e já
   aplica os efeitos de alert/changeColor diretamente no estado. Não há
   mais lista de "outputs" para aplicar depois — ver JSRender. *)

datatype js_event_kind =
    EvClick
  | EvMouseOver

fun prop_of_event :: "js_event_kind => string" where
  "prop_of_event EvClick      = ''onclick''"
| "prop_of_event EvMouseOver  = ''onmouseover''"

fun make_event_handler :: "js_event_kind => nat => js_state => js_state" where
  "make_event_handler ev_kind target_id state =
     (let prop = prop_of_event ev_kind
      in case load_object target_id state of
           Some (VDOMElement tag props) =>
             (case get_prop prop props of
                Some f => run_handler target_id f state
              | None   => state)
         | _ => state)"

value "dom_state"
value "make_event_handler EvClick 2 dom_state"
value "make_event_handler EvMouseOver 2 dom_state"
value "make_event_handler EvClick 99 dom_state"

value "Alerts_s (make_event_handler EvClick 2 dom_state)"
value "load_object 1 (make_event_handler EvClick 2 dom_state)"

end
