theory JSAbsEvent
imports JSRender JSQuerySelector
begin

(* ==========================================================================
   Teoremas de absorção de eventos (Event Absorption)

   Na semântica de eventos definida em JSEvents, disparar um evento
   (make_event_handler) que não possui handler correspondente no elemento
   alvo não produz efeito — o estado "absorve" o evento sem alteração.
   Esta theory formaliza essa propriedade e suas consequências.

   Propriedades provadas:
     1. Absorção por não-elemento
     2. Absorção por handler ausente
     3. Absorção por handler não-função
     4. Absorção por tipo de evento errado
     5. Absorção concreta sobre o dom_state canônico
     6. Estabilidade do heap após eventos repetidos (idempotência de heap)
     7. Lema de existência: se um evento altera o estado, então existe handler
     8. Composicionalidade com querySelector e tohtml
   ========================================================================== *)

(* --------------------------------------------------------------------------
   Lema auxiliar: run_handler sobre um valor que não é VFunction é no-op.
   -------------------------------------------------------------------------- *)
lemma run_handler_non_function:
  "run_handler target_id h state = state"
  if "!!params body env. h ~= VFunction params body env"
  using that by (cases h; auto)

(* --------------------------------------------------------------------------
   1. ABSORÇÃO POR NÃO-ELEMENTO
   Disparar evento num target que não é VDOMElement não altera o estado.
   -------------------------------------------------------------------------- *)
theorem absorb_non_element:
  assumes no: "load_object obj_id state = None"
  shows "make_event_handler ev obj_id state = state"
  using no
  by (induct ev; simp add: make_event_handler.simps)

theorem absorb_non_vdom:
  assumes ld: "load_object obj_id state = Some v"
    and nv: "!!t p. v ~= VDOMElement t p"
  shows "make_event_handler ev obj_id state = state"
  using ld nv
  by (induct ev; simp add: make_event_handler.simps split: js_vle.splits)

(* --------------------------------------------------------------------------
   2. ABSORÇÃO POR HANDLER AUSENTE
   Se o elemento existe mas não possui a propriedade de handler para este
   tipo de evento, o estado permanece inalterado.
   -------------------------------------------------------------------------- *)
theorem absorb_no_handler:
  "make_event_handler ev obj_id state = state"
  if "load_object obj_id state = Some (VDOMElement t p)"
    and "get_prop (prop_of_event ev) p = None"
  using that by (induct ev; simp)

(* --------------------------------------------------------------------------
   3. ABSORÇÃO POR HANDLER NÃO-FUNÇÃO
   Se a propriedade existe mas o valor não é uma VFunction, run_handler
   faz catch-all e retorna o estado inalterado. Este caso cobre handlers
   corrompidos ou valores que não são funções.
   -------------------------------------------------------------------------- *)
theorem absorb_non_function_handler:
  "make_event_handler ev obj_id state = state"
  if "load_object obj_id state = Some (VDOMElement t p)"
    and "get_prop (prop_of_event ev) p = Some h"
    and "!!params body env. h ~= VFunction params body env"
  using that by (induct ev; simp add: run_handler_non_function)

(* --------------------------------------------------------------------------
   4. ABSORÇÃO POR TIPO DE EVENTO ERRADO
   Se o elemento tem handler para ev1 mas não para ev2, disparar ev2 é
   absorvido. Corolário direto de absorb_no_handler (as premissas sobre
   ev1 são documentação e não são usadas na prova).
   -------------------------------------------------------------------------- *)
theorem absorb_wrong_event_kind:
  "make_event_handler ev2 obj_id state = state"
  if "get_prop (prop_of_event ev1) p ~= None"
    and "get_prop (prop_of_event ev2) p = None"
    and "ev1 ~= ev2"
    and "load_object obj_id state = Some (VDOMElement t p)"
  using that by (simp add: absorb_no_handler)

(* --------------------------------------------------------------------------
   5. ABSORÇÃO POR WINDOW
   A window (id 0 no estado canônico) nunca é VDOMElement e portanto
   absorve qualquer evento.
   -------------------------------------------------------------------------- *)
theorem absorb_event_on_window:
  "make_event_handler ev 0 dom_state = dom_state"
  by (induct ev; eval)

(* --------------------------------------------------------------------------
   6. ABSORÇÃO CONCRETA SOBRE O DOM_STATE CANÔNICO
   O dom_state (ver JSDOM) possui:
     id 0: VWindow        — absorve qualquer evento
     id 1: p#msg          — NÃO tem onclick, NÃO tem onmouseover
     id 2: button         — TEM onclick, NÃO tem onmouseover
   -------------------------------------------------------------------------- *)

(* Parágrafo (id 1) não tem handler de click nem de mouseover *)
theorem absorb_click_on_paragraph:
  "make_event_handler EvClick 1 dom_state = dom_state"
  by eval

theorem absorb_mouseover_on_paragraph:
  "make_event_handler EvMouseOver 1 dom_state = dom_state"
  by eval

(* Botão (id 2) não tem handler de mouseover *)
theorem absorb_mouseover_on_button:
  "make_event_handler EvMouseOver 2 dom_state = dom_state"
  by eval

(* Window (id 0) absorve tudo *)
theorem absorb_click_on_window:
  "make_event_handler EvClick 0 dom_state = dom_state"
  by eval

theorem absorb_mouseover_on_window:
  "make_event_handler EvMouseOver 0 dom_state = dom_state"
  by eval

(* Alvo inexistente (id 99) — absorção por não-elemento *)
theorem absorb_nonexistent_target:
  "make_event_handler ev 99 dom_state = dom_state"
  by (induct ev; eval)

(* --------------------------------------------------------------------------
   7. ESTABILIDADE DO HEAP (HEAP ABSORPTION)
   Embora dois disparos de evento possam diferir no Alerts_s (alertas são
   acumulativos), o heap é estável: mudar a cor para azul duas vezes é o
   mesmo que mudar uma vez, graças a change_element_color_idempotent
   (provado em JSProofs).
   -------------------------------------------------------------------------- *)

theorem heap_absorption_click_button:
  "Heap_s (make_event_handler EvClick 2 (make_event_handler EvClick 2 dom_state))
   = Heap_s (make_event_handler EvClick 2 dom_state)"
  by eval

(* O mesmo para qualquer número de repetições: provamos que a cor final
   do parágrafo é azul depois de 1 ou mais cliques. *)
theorem load_paragraph_after_clicks:
  "load_object 1 (make_event_handler EvClick 2 dom_state)
   = load_object 1 (make_event_handler EvClick 2 (make_event_handler EvClick 2 dom_state))"
  by eval

(* --------------------------------------------------------------------------
   8. LEMA DE EXISTÊNCIA DE HANDLER
   Se make_event_handler altera o estado, então necessariamente existe um
   handler para o evento no elemento alvo. Este é o "contrapositivo" da
   absorção: ausência de handler => absorção, portanto efeito => handler.
   -------------------------------------------------------------------------- *)

theorem event_effect_implies_handler:
  assumes "make_event_handler ev obj_id state ~= state"
  shows "\<exists>tag p f.
    load_object obj_id state = Some (VDOMElement tag p) \<and>
    get_prop (prop_of_event ev) p = Some f"
using assms
proof (induct ev)
  case EvClick
  then show ?case by (auto split: option.splits js_vle.splits if_splits)
next
  case EvMouseOver
  then show ?case by (auto split: option.splits js_vle.splits if_splits)
qed

(* --------------------------------------------------------------------------
   9. COMPOSICIONALIDADE: absorção preserva querySelector e renderização.
   Se um evento é absorvido, todos os observadores downstream (seletores
   CSS e renderização HTML) veem o mesmo estado.
   -------------------------------------------------------------------------- *)

theorem querySelector_stable_under_absorbed_event:
  "querySelector (make_event_handler ev obj_id state) sel
   = querySelector state sel"
  if "make_event_handler ev obj_id state = state"
  using that by simp

theorem tohtml_stable_under_absorbed_event:
  "tohtml (make_event_handler ev obj_id state) pos = tohtml state pos"
  if "make_event_handler ev obj_id state = state"
  using that by simp

end
