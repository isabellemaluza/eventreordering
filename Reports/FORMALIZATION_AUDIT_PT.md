# Auditoria da Formalização — Independência e Reordenação de Eventos em JavaScript com Isabelle/HOL

**Data da auditoria:** 2026-08-18
**Workspace:** `/Users/isamaluza/Documents/eventreordering`
**Objeto auditado:** todos os arquivos de teoria Isabelle/HOL em `Codes/` (14 arquivos `.thy` reais; backups `*.thy~` ignorados conforme instruções).
**Caráter da auditoria:** auditoria científica estática. Uma verificação independente com Isabelle/HOL das teorias foi executada de forma não destrutiva sobre cópias durante esta auditoria e **concluiu com sucesso** (ver o Apêndice ao final deste relatório para os comandos e resultados exatos).

> Legenda usada em todo o documento:
> **DEFINIDO (DEFINED)** — explicitamente definido em Isabelle.
> **PROVADO (PROVED)** — explicitamente estabelecido por teorema/lema nos arquivos (incluindo provas por normalização/`eval`).
> **DERIVADO (DERIVED)** — decorre de resultados já provados por combinação simples (não mecanizado por si só).
> **INTERPRETAÇÃO (INTERPRETATION)** — leitura científica de um resultado formal.
> **NÃO PROVADO (NOT PROVED)** — exigiria mecanização adicional.

---

## 1. Sumário Executivo

O diretório `Codes/` contém um desenvolvimento Isabelle/HOL coerente e em camadas (14 teorias, ~2.800 linhas) que modela um **ambiente simplificado de execução de JavaScript/DOM**: um heap como lista de associação, um registro `js_state` (pilha, heap, campo de fila de eventos, histórico de alertas), um avaliador com combustível (fuel), elementos DOM como valores de heap (`VDOMElement`), despacho de eventos com dois tipos (`make_event_handler`), um renderizador HTML (`tohtml`) e uma relação de equivalência observacional (`obs_equiv` = mesmo HTML renderizado + mesmo histórico de alertas).

**O que está genuinamente mecanizado e é forte:**

- *Localidade de heap* (JSLocality.thy): operações sobre **identificadores de heap distintos** não interferem entre si nas leituras (`load_object`), e duas escritas em identificadores distintos **comutam a menos de igualdade extensional do heap** (`heap_ext_eq`, isto é, todos os resultados de `load_object` coincidem). Esses resultados têm estrutura incondicional (única hipótese: `i ≠ j`).
- *Absorção de eventos* (JSAbsEvent.thy): eventos cujo alvo não existe, não é um elemento DOM, ou não possui handler para aquele tipo de evento deixam o estado **inalterado** (`make_event_handler ev obj s = s`), com consequências observacionais em JSObsEquiv.thy.
- *Absorção de escritas / idempotência* (JSProofs.thy, JSFrameRule.thy): mudanças repetidas de cor no **mesmo** elemento obedecem a "a última escrita vence" (`change_element_color_absorbs`), empacotado observacionalmente como `write_absorption_law`.
- *Infraestrutura de equivalência observacional* (JSObsEquiv.thy): `obs_equiv` é uma relação de equivalência; igualdade de estados implica `obs_equiv`; absorção implica `obs_equiv`.
- *Teoremas de reordenação de eventos* (JSFrameRule.thy): `frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect` **existem e estão provados** — mas são **condicionais**: suas hipóteses afirmam (a menos de desdobramento definicional) a própria equivalência observacional, ou igualdades de efeito sobre estados intermediários que a implicam diretamente, para as duas ordens de execução.

**A lacuna central.** A cadeia sugerida pelo resumo proposto — *localidade ⇒ independência ⇒ regra de enquadramento ⇒ comutatividade ⇒ reordenação ⇒ consequência observacional* — está **apenas parcialmente fechada**:

1. **Não existe teorema** da forma "dois handlers que só alteram elementos DOM distintos podem ser reordenados sem alterar o comportamento observável". Independência no nível de handlers de eventos (`make_event_handler`) **NÃO ESTÁ PROVADA**; apenas a independência de operações de heap está provada.
2. **Não existe lema-ponte** conectando `heap_ext_eq` a `tohtml`/`obs_equiv` (verificado por busca exaustiva: `heap_ext_eq` aparece apenas em JSLocality.thy e nas duas regras de enquadramento de heap em JSFrameRule.thy).
3. As "regras de enquadramento" e os teoremas de reordenação em nível de evento tomam `obs_equiv` das duas ordens (ou equações de efeito que a implicam) **como hipóteses**. São teoremas de contabilidade (bookkeeping) corretos, não critérios de independência. Os próprios comentários do cabeçalho de JSFrameRule.thy confirmam esse desenho.

**Consequência para o artigo.** A afirmação cientificamente mais defensável hoje diz respeito a **localidade, comutatividade e absorção em nível de heap**, além de **reordenação condicional de eventos**. A frase do resumo de que manipuladores atuando sobre partes distintas do estado podem ser executados em ordens diferentes "sem alterar o resultado observável" **NÃO ESTÁ ATUALMENTE PROVADA** e precisa ser qualificada — ou os resultados-ponte ausentes precisam ser mecanizados primeiro (a Seção 19 os classifica como ESSENCIAIS).

**Título.** "Verificação Formal de Independência e Reordenação de Eventos em JavaScript com Isabelle/HOL" é classificado como **AMPLO DEMAIS (TOO BROAD)** para a mecanização atual (independência em nível de evento não está provada; a reordenação é condicional). Alternativas são propostas na Seção 14.

---

## 2. Escopo da Formalização

### 2.1 Arquivos

14 arquivos `.thy` reais em `Codes/` (backups `*.thy~` excluídos):

| Teoria | Linhas | Importa | Papel |
|---|---|---|---|
| `JSMemoryModel.thy` | 187 | `Complex_Main` | Valores base, expressões, pilha/heap/estado, operações de heap, `browser_init_state` |
| `JSHTMLSyntax.thy` | 28 | `JSMemoryModel` | Sintaxe HTML/atributos de superfície (`html_node`, `html_attr`) |
| `JSDOM.thy` | 65 | `JSHTMLSyntax` | Construção do DOM a partir do HTML (`build_dom_list`, `sample_html`, `dom_state`) |
| `JSEval.thy` | 140 | `JSMemoryModel` | O avaliador oficial (`eval_expr_fuel`, `eval_expr`), builtins, `run_handler` |
| `JSEvents.thy` | 42 | `JSDOM`, `JSEval` | Tipos de evento, busca e despacho de handler (`make_event_handler`) |
| `JSRender.thy` | 89 | `JSEvents` | Renderização: `tohtml`, `sample_pos` |
| `JSQuerySelector.thy` | 80 | `JSDOM` | Subconjunto de seletores CSS (`querySelector`, `querySelectorAll`), wrappers de mudança de cor |
| `JSAbsEvent.thy` | 190 | `JSRender`, `JSQuerySelector` | Teoremas de absorção de eventos e consequências |
| `JSHeapWF.thy` | 454 | `JSDOM` | Boa-formação do heap (`heap_wf` = ids distintos), frescor, preservação |
| `JSLocality.thy` | 580 | `JSHeapWF` | **Localidade**: independência de leituras, `heap_ext_eq`, comutatividade de escritas distintas |
| `JSProofs.thy` | 109 | `JSRender`, `JSQuerySelector` | Idempotência, última escrita vence, propriedades insert/remove |
| `JSFuel.thy` | 122 | `JSEval` | Lemas de fuel, determinismo (e nota explícita de que monotonicidade de fuel **não** está estabelecida) |
| `JSObsEquiv.thy` | 280 | `JSRender`, `JSLocality`, `JSProofs`, `JSAbsEvent` | Equivalência observacional (`observable`, `obs_equiv`) e consequências |
| `JSFrameRule.thy` | 461 | `JSObsEquiv`, `JSFuel` | **Regras de enquadramento e reordenação de eventos** (`run_events`, `frame_rule_*`, `events_reorder_*`) |

Não há arquivo de sessão `ROOT`/`ROOTS` no workspace; as teorias formam um diretório plano com imports por nome. Nenhuma teoria-raiz importa `JSFrameRule` explicitamente, mas ela cobre transitivamente as 14 teorias.

### 2.2 O que o modelo contém (DEFINIDO)

- **Valores** (`js_vle`): números (reais), NaN, booleanos, strings, null, undefined, referências de heap (`VRef nat`), objetos, janela, elementos DOM (`VDOMElement tag props`), funções (params/corpo/env), builtins, erros de tipo.
- **Expressões** (`expr`): constantes, variáveis, atribuição, operadores binários, chamadas, if, sequência, return.
- **Estado** (`js_state` registro): `Stack_s` (frames léxicos), `Heap_s` (lista de associação `(nat * js_vle) list`), `Events_s` (`event_queue = (string * expr) list` — **declarado mas não usado pela maquinaria de eventos**), `Alerts_s` (histórico de alertas).
- **Builtins**: `BAlert`, `BChangeColor`, `BCreateElement`.
- **Eventos**: `js_event_kind = EvClick | EvMouseOver`; despacho via `make_event_handler :: js_event_kind => nat => js_state => js_state`, que busca `onclick`/`onmouseover` no `VDOMElement` alvo e executa o handler com `this` ligado a `VRef target_id`.
- **Comportamento observável**: `observable s p = (tohtml s p, Alerts_s s)`; `obs_equiv s1 s2 p ⟺ tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2` (parametrizado por um mapa de posições `p :: dom_pos`).
- **Relação de localidade**: `heap_ext_eq s1 s2 ⟺ (∀k. load_object k s1 = load_object k s2)`.
- **Sequências de eventos**: `run_events :: (js_event_kind * nat) list => js_state => js_state`.

### 2.3 O que o modelo não contém

Sem event loop, sem filas de tasks/microtasks, sem promises, sem assincronia, sem concorrência (o despacho é um transformador de estado síncrono e total); sem bubbling/captura de eventos nem objeto de evento; sem layout CSS; sem mutação de texto/nós dentro de handlers além de `alert`/`changeColor`/`createElement`; `Events_s` nunca é lido nem escrito por `make_event_handler`/`run_events`/pelo avaliador (busca confirma: `Events_s` ocorre apenas na definição do registro e em `browser_init_state`).

---

## 3. Mapa de Dependência entre Teorias

```
JSMemoryModel.thy (Complex_Main)
 ├─ JSHTMLSyntax.thy
 │    └─ JSDOM.thy
 │         ├─ JSEvents.thy ────────────┐
 │         │    └─ JSRender.thy ───────┼──────────────────────────┐
 │         ├─ JSQuerySelector.thy ─────┤                          │
 │         │    └──────────────────────┼─ JSAbsEvent.thy ──┐      │
 │         ├─ JSHeapWF.thy             │                   │      │
 │         │    └─ JSLocality.thy ─────┼───────────────────┼──┐   │
 │         └─ JSProofs.thy (via JSRender, JSQuerySelector) ─┼──┤   │
 ├─ JSEval.thy                                                 │  │   │
 │    ├─ JSEvents.thy (com JSDOM) ──(ver acima)                │  │   │
 │    └─ JSFuel.thy ──────────────────────────────────────────┼──┼───┼──┐
 │                                                            │  │   │  │
 └─ JSObsEquiv.thy (importa JSRender, JSLocality, JSProofs, JSAbsEvent)
      └─ JSFrameRule.thy (importa JSObsEquiv, JSFuel)
```

Arestas (verificadas nas cláusulas `imports`): `JSEval → JSMemoryModel`; `JSHTMLSyntax → JSMemoryModel`; `JSDOM → JSHTMLSyntax`; `JSEvents → JSDOM, JSEval`; `JSRender → JSEvents`; `JSQuerySelector → JSDOM`; `JSAbsEvent → JSRender, JSQuerySelector`; `JSHeapWF → JSDOM`; `JSLocality → JSHeapWF`; `JSProofs → JSRender, JSQuerySelector`; `JSFuel → JSEval`; `JSObsEquiv → JSRender, JSLocality, JSProofs, JSAbsEvent`; `JSFrameRule → JSObsEquiv, JSFuel`.

`JSFrameRule.thy` é o topo do cone de dependências e inclui transitivamente as outras 13 teorias.

---

## 4. Definições Relevantes

### 4.1 `JSMemoryModel.thy` (DEFINIDO)

- `datatype builtin = BAlert | BChangeColor | BCreateElement`
- `datatype js_vle = VNumber real | VNaN | VBool bool | VString string | VNull | VUndefined | VRef nat | VObject "(string*js_vle) list" | VWindow "(string*js_vle) list" | VDOMElement string "(string*js_vle) list" | VFunction "string list" expr "(string*js_vle) list" | VBuiltin builtin | VTypeError string` — mutuamente recursivo com `expr = EConst js_vle | EVar string | EAssign string expr | EBinOp string expr expr | ECall expr "expr list" | EIf expr expr expr | ESeq expr expr | EReturn expr`.
- `type_synonym frame = "(string*js_vle) list"`; `stack = "frame list"`; `heap = "(nat*js_vle) list"`; `event = "string*expr"`; `event_queue = "event list"`.
- `record js_state = Stack_s :: stack | Heap_s :: heap | Events_s :: event_queue | Alerts_s :: "string list"`.
- Acesso/atualização de propriedades: `get_prop`, `update_prop`.
- Pilha: `lookup_stack`, `load_var`, `update_in_frame`, `write_var`, `push_frame`, `pop_frame`.
- Heap: `load_object`, `load_global`, `max_heap_id`, `alloc_object`, `alloc_dom_element`, `write_object`, `remove_object`, `write_dom_element`, `write_window`, `insert_dom_element`, `change_element_color`.
- `browser_init_state` — estado inicial canônico: janela no id de heap 0 com os três builtins; pilha/eventos/alertas vazios.

### 4.2 `JSHTMLSyntax.thy` / `JSDOM.thy` (DEFINIDO)

- `html_attr = Attr string string | AttrOnClick expr | AttrOnMouseOver expr`; `html_node = HtmlText string | HtmlElement string "html_attr list" "html_node list"`.
- `attr_to_prop` mapeia `AttrOnClick e ↦ [("onclick", VFunction [] e [])]`, `AttrOnMouseOver e ↦ [("onmouseover", VFunction [] e [])]`.
- `build_dom_node`/`build_dom_list` constroem entradas de heap via `alloc_dom_element`; `sample_html` (um `<p id="msg" color="yellow">` e um `<button onclick="alert('Ola'); changeColor(this,'blue')">`); `dom_state = build_dom_list sample_html browser_init_state` (heap: id 0 janela, id 1 parágrafo, id 2 botão).

### 4.3 `JSEval.thy` (DEFINIDO)

- `is_truthy`, `eval_binop` (apenas `+` sobre números; todo o resto → `VTypeError`).
- `eval_expr_fuel :: nat => expr => js_state => (js_vle * js_state)` / `eval_exprs_fuel` — limitado por combustível, total; builtins alteram o estado diretamente (`alert` anexa a `Alerts_s`; `changeColor` chama `change_element_color`; `createElement` aloca e devolve `VRef`).
- `default_fuel = 200`; `eval_expr = eval_expr_fuel default_fuel`; `eval_exprs`.
- `run_handler target_id (VFunction params body clos_env) st` — empurra `clos_env @ [("this", VRef target_id)]`, avalia o corpo, desempilha o frame; não-funções são no-op.

### 4.4 `JSEvents.thy` (DEFINIDO)

- `js_event_kind = EvClick | EvMouseOver`; `prop_of_event EvClick = "onclick"`, `prop_of_event EvMouseOver = "onmouseover"`.
- `make_event_handler ev_kind target_id state` — carrega `target_id`; se for um `VDOMElement` com a propriedade `prop_of_event ev_kind`, executa via `run_handler`; caso contrário devolve o estado inalterado.

### 4.5 `JSRender.thy` (DEFINIDO)

- `dom_pos = (nat*nat) list`; `tohtml state pos = strip_pos (sort_by_pos (collect_dom_nodes (Heap_s state) pos))` — renderiza os `VDOMElement` do heap numa lista plana `html_node list` ordenada pelas posições dadas; `sample_pos = build_pos sample_html 1 0`.

### 4.6 `JSQuerySelector.thy` (DEFINIDO)

- `selector` (tag/class/id/não suportado), `parse_selector`, `matches_selector`, `querySelector`, `querySelectorAll`, `JS_querySelector_blue`, `JS_querySelectorAll_yellow`, `demo_state`.

### 4.7 `JSHeapWF.thy` (DEFINIDO)

- `distinct_heap_ids h ⟺ distinct (map fst h)`; `heap_wf s ⟺ distinct_heap_ids (Heap_s s)`.

### 4.8 `JSLocality.thy` (DEFINIDO)

- `heap_ext_eq s1 s2 ⟺ (∀k. load_object k s1 = load_object k s2)` — **igualdade extensional de heap** (todas as leituras coincidem), uma relação de equivalência (`heap_ext_eq_refl/sym/trans`).

### 4.9 `JSObsEquiv.thy` (DEFINIDO)

- `observable s pos = (tohtml s pos, Alerts_s s)`; `obs_equiv s1 s2 p ⟺ tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2`.

### 4.10 `JSFrameRule.thy` (DEFINIDO)

- `run_events [] s = s`; `run_events ((ev,target)#rest) s = run_events rest (make_event_handler ev target s)`.

### 4.11 `JSFuel.thy` (DEFINIDO)

- `out_of_fuel v ⟺ v = VTypeError "Out of fuel"`; `eval_succeeds n e s ⟺ ¬ out_of_fuel (fst (eval_expr_fuel n e s))`.

---

## 5. Resultados de Localidade (JSLocality.thy)

**O que "localidade" significa aqui (DEFINIDO + PROVADO):** *independência extensional de operações de heap sobre identificadores de heap distintos* — uma operação no identificador `j` nunca altera o que um `load_object i` observa para qualquer `i ≠ j`, e duas operações em identificadores distintos comutam a menos de `heap_ext_eq`. A localidade é expressa **em termos de identificadores de heap** (`nat`), não em termos de elementos DOM ou de estados completos; as operações de elementos DOM (`write_dom_element`, `change_element_color`) herdam a localidade porque são definidas como escritas no heap.

### Independência leitura/escrita (PROVADO)

- `load_object_write_same`: `load_object i (write_object i v s) = Some v`.
- `load_object_write_independent`: `i ≠ j ⟹ load_object i (write_object j v s) = load_object i s`.
- `load_object_remove_same`: `load_object i (remove_object i s) = None`.
- `load_object_remove_independent`: `i ≠ j ⟹ load_object i (remove_object j s) = load_object i s`.
- `load_object_write_dom_same`: `load_object i (write_dom_element i tag props s) = Some (VDOMElement tag props)`.
- `load_object_write_dom_independent`: `i ≠ j ⟹ load_object i (write_dom_element j tag props s) = load_object i s`.
- `load_object_change_color_independent`: `i ≠ j ⟹ load_object i (change_element_color j color s) = load_object i s` (provado por análise de casos completa sobre o valor armazenado).
- Apelidos (usados como blocos de construção): `write_object_observational_independent`, `write_dom_element_observational_independent`, `change_element_color_observational_independent` — atenção: esses nomes são ligeiramente enganosos: eles afirmam **igualdade de leitura**, não `obs_equiv`.

### Comutatividade a menos de igualdade extensional de heap (PROVADO)

- `write_object_commute_load` (lema): `i ≠ j ⟹ load_object k (write_object i vi (write_object j vj s)) = load_object k (write_object j vj (write_object i vi s))`.
- `write_object_commute_ext` (teorema): `i ≠ j ⟹ heap_ext_eq (write_object i vi (write_object j vj s)) (write_object j vj (write_object i vi s))`.
- `write_dom_element_commute_ext` (teorema): `i ≠ j ⟹ heap_ext_eq (write_dom_element i tag props (write_dom_element j tag' props' s)) (write_dom_element j tag' props' (write_dom_element i tag props s))`.

**Resultados de localidade mais fortes para o artigo SIICUSP:** `write_object_commute_ext`, `write_dom_element_commute_ext` e `load_object_change_color_independent` (a propriedade de pegada/footprint usada por `frame_rule_change_color_load`).

**Ressalvas:** (i) a conclusão é `heap_ext_eq` — os dois heaps são extensionalmente iguais mas **não** são listas iguais (a ordem das entradas difere), e nada conecta `heap_ext_eq` a `tohtml`/`obs_equiv` no desenvolvimento; (ii) nenhum teorema cobre interferência de `alloc_object`/`alloc_dom_element` além da boa-formação (frescor é provado em JSHeapWF); (iii) **não** existe teorema de localidade no nível de `make_event_handler`.

---

## 6. Resultados de Independência

A formalização contém **independência de operações de heap**, não independência de eventos/handlers:

| Resultado | Teoria | Hipóteses | Conclusão | Tipo |
|---|---|---|---|---|
| `load_object_write_independent` | JSLocality | `i ≠ j` | `load_object i (write_object j v s) = load_object i s` | preservação de leitura |
| `load_object_remove_independent` | JSLocality | `i ≠ j` | `load_object i (remove_object j s) = load_object i s` | preservação de leitura |
| `load_object_write_dom_independent` | JSLocality | `i ≠ j` | `load_object i (write_dom_element j tag props s) = load_object i s` | preservação de leitura |
| `load_object_change_color_independent` | JSLocality | `i ≠ j` | `load_object i (change_element_color j color s) = load_object i s` | preservação de leitura |
| `write_object_commute_ext` | JSLocality | `i ≠ j` | `heap_ext_eq` das duas ordens de escrita | igualdade extensional de heap |
| `write_dom_element_commute_ext` | JSLocality | `i ≠ j` | `heap_ext_eq` das duas ordens de escrita | igualdade extensional de heap |

**Que independência está formalizada:** duas operações de heap em identificadores distintos são mutuamente não-interferentes (em relação a leituras) e comutam extensionalmente. **O que NÃO está formalizado:** independência de *handlers de eventos* (resultados de `make_event_handler`), independência de *eventos*, ou independência de programas JavaScript arbitrários. A distinção de identificadores (`i ≠ j`) é a única condição estrutural — não há análise de células alcançáveis nem de aliasing.

---

## 7. Resultados de Regras de Enquadramento (JSFrameRule.thy)

### 7.1 Regras de enquadramento em nível de heap (PROVADO, condicionais apenas a `i ≠ j`)

- `frame_rule_write_object`: `i ≠ j ⟹ heap_ext_eq (write_object i vi (write_object j vj s)) (write_object j vj (write_object i vi s))` — reformulação de `write_object_commute_ext`.
- `frame_rule_write_dom_element`: mesma forma para `write_dom_element` (reformulação de `write_dom_element_commute_ext`).
- `frame_rule_change_color_load`: `i ≠ j ⟹ load_object i (change_element_color j color s) = load_object i s` — a pegada (footprint) de uma mudança de cor.

Estes são os únicos resultados do arquivo cuja hipótese é a condição estrutural `i ≠ j`.

### 7.2 Regras de enquadramento em nível de evento (PROVADO, mas condicionais a hipóteses observacionais)

- `frame_rule_events`:
  - Hipóteses: `LEFT: make_event_handler ev_j j (make_event_handler ev_i i s) = left_state`; `RIGHT: make_event_handler ev_i i (make_event_handler ev_j j s) = right_state`; `OBS: obs_equiv left_state right_state p`.
  - Conclusão: `obs_equiv (make_event_handler ev_j j (make_event_handler ev_i i s)) (make_event_handler ev_i i (make_event_handler ev_j j s)) p`.
  - Avaliação: desdobrando `LEFT`/`RIGHT`, a conclusão *é* `OBS`. O teorema empacota a hipótese sobre estados intermediários nomeados; ele **não fornece critério** para quando `OBS` vale. Não há hipótese `i ≠ j`.
- `frame_rule_events_by_effect`:
  - Hipóteses: `HI: make_event_handler ev_i i (make_event_handler ev_j j s) = change_element_color i ci (make_event_handler ev_j j s)`; `HJ: make_event_handler ev_j j (make_event_handler ev_i i s) = change_element_color j cj (make_event_handler ev_i i s)`; `OBS: obs_equiv (change_element_color j cj (make_event_handler ev_i i s)) (change_element_color i ci (make_event_handler ev_j j s)) p`.
  - Conclusão: `obs_equiv` das duas ordens de execução dos handlers.
  - Avaliação: `HI`/`HJ` caracterizam o efeito de cada handler **sobre os estados intermediários reais** como uma mudança de cor; novamente, desdobrando `HI`/`HJ`, a conclusão fica igual a `OBS`. É a "forma útil para provar handlers independentes concretos" (segundo comentário do arquivo) — mas as **instâncias de handlers independentes nunca são provadas** no desenvolvimento.

### 7.3 O que a formalização chama de regra de enquadramento

Uma **regra de enquadramento (frame rule)** aqui significa: (nível de heap) operações sobre alvos distintos comutam extensionalmente, enunciadas como teoremas; (nível de evento) teoremas que transferem uma hipótese de equivalência observacional sobre as duas execuções concretas para uma conclusão sobre elas, com caracterizações de efeito opcionais. As regras em nível de evento são **condicionais** — assumem (essencialmente) o que concluem. O desenvolvimento **não** usa lógica de separação; descrever essas regras como regras de enquadramento de lógica de separação seria um exagero. O cabeçalho do arquivo afirma explicitamente: *"Não assumimos que um handler de evento não é afetado meramente porque uma célula de heap diferente foi alterada… a reordenação em nível de evento usa hipóteses explícitas sobre as duas execuções intermediárias."*

---

## 8. Resultados de Reordenação de Eventos (JSFrameRule.thy)

### 8.1 Inventário

| Nome | Existe? | Provado? | Forma |
|---|---|---|---|
| `frame_rule_events` | SIM (linha 110) | SIM | condicional (assume obs-equiv das duas ordens) |
| `frame_rule_events_by_effect` | SIM (linha 139) | SIM | condicional (equações de efeito + obs-equiv) |
| `events_reorder_two` | SIM (linha 177) | SIM | condicional (assume obs-equiv das duas ordens) |
| `events_reorder_two_by_effect` | SIM (linha 198) | SIM | condicional (equações de estados intermediários + obs-equiv) |

### 8.2 Enunciados exatos

- `events_reorder_two`:
  - Hipótese `FRAME`: `obs_equiv (make_event_handler ev_j j (make_event_handler ev_i i s)) (make_event_handler ev_i i (make_event_handler ev_j j s)) p`.
  - Conclusão: `obs_equiv (run_events [(ev_i,i),(ev_j,j)] s) (run_events [(ev_j,j),(ev_i,i)] s) p`.
  - Prova: `using FRAME by simp` — desdobra `run_events_two`. A hipótese é a conclusão a menos da definição de `run_events`.
- `events_reorder_two_by_effect`:
  - Hipóteses: `HI: make_event_handler ev_i i (make_event_handler ev_j j s) = si`; `HJ: make_event_handler ev_j j (make_event_handler ev_i i s) = sj`; `OBS: obs_equiv sj si p`.
  - Conclusão: `obs_equiv (run_events [(ev_i,i),(ev_j,j)] s) (run_events [(ev_j,j),(ev_i,i)] s) p`.
  - Prova: `run_events [(ev_i,i),(ev_j,j)] s = sj` (via `HJ`), `run_events [(ev_j,j),(ev_i,i)] s = si` (via `HI`), então `OBS`.

### 8.3 Explicação em três níveis do teorema de reordenação mais forte

**Nível 1 — Enunciado formal exato.** Ver `events_reorder_two_by_effect` acima. Fato em Isabelle/HOL: das duas hipóteses de equação que nomeiam os resultados `si`, `sj` das duas composições sequenciais e da hipótese `obs_equiv sj si p`, segue que executar as sequências de dois eventos em qualquer ordem produz estados `obs_equiv` (mesmo `tohtml` e mesmo `Alerts_s` nas posições `p`).

**Nível 2 — Interpretação matemática.** O teorema é um fato de congruência/transporte: se dois transformadores de estado (as execuções de handlers) aplicados em qualquer ordem chegam a estados finais observacionalmente equivalentes — o que as hipóteses afirmam após renomeação — então o mesmo vale quando as execuções são empacotadas como a função de sequência de eventos `run_events` de dois elementos. Ele transfere, mas não *estabelece*, a equivalência: o conteúdo não trivial (por que `sj` e `si` são observacionalmente equivalentes) precisa ser fornecido em outro lugar, por exemplo, a partir da comutatividade em nível de heap mais uma ponte heap→observável (atualmente ausente).

**Nível 3 — Interpretação Web/JavaScript.** No subconjunto modelado, *se* já se estabeleceu que disparar `ev_i` no elemento `i` e depois `ev_j` no elemento `j` produz o mesmo HTML renderizado e o mesmo histórico de alertas que a ordem inversa, *então* o mesmo vale para o sequenciamento `run_events` desses dois despachos. O teorema em si **não** diz quais pares de handlers são reordenáveis; em particular, isso não segue meramente de `i ≠ j` ou de os handlers terem alvos DOM distintos.

### 8.4 Respostas às perguntas específicas

- **O que conta como dois eventos independentes?** Nada é definido em nível de evento. Independência existe apenas para operações de heap em identificadores distintos (`i ≠ j`).
- **O que pode diferir entre eles?** Os teoremas quantificam sobre `ev_i`, `ev_j`, `i`, `j` arbitrários — mas apenas as hipóteses (obs-equivalência/equações de efeito) tornam um par reordenável.
- **Precisam ter alvos DOM distintos?** Nenhuma condição desse tipo aparece nos teoremas de nível de evento. Distinção (`i ≠ j`) aparece apenas nos resultados de nível de heap.
- **Precisam produzir efeitos específicos?** Apenas em `frame_rule_events_by_effect`, cujas hipóteses exigem que o efeito de cada handler (sobre o estado intermediário) seja exatamente `change_element_color i ci` / `change_element_color j cj`.
- **Está provado que `e1;e2 ≡ e2;e1`?** Apenas condicionalmente: dadas as hipóteses, sim — no sentido preciso de `obs_equiv` entre as duas execuções de `run_events`. Incondicionalmente a partir de estrutura (ex.: alvos distintos): **NÃO PROVADO**.
- **Noção precisa de equivalência:** `obs_equiv` nas posições `p`: `tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2`. Não é igualdade de estados, não é igualdade da lista do heap, não é igualdade extensional de heap.

### 8.5 Classificação honesta

`events_reorder_two` e `events_reorder_two_by_effect` são **teoremas de contabilidade corretos, mas quase tautológicos**: suas hipóteses afirmam, a menos de desdobramento definicional, a equivalência observacional que as conclusões afirmam. São valiosos como *empacotamento* (interface `run_events`, estados intermediários nomeados) uma vez que exista uma prova real de independência — mas o desenvolvimento atualmente **não contém teorema** que derive a hipótese `obs_equiv` desses resultados de uma condição estrutural como alvos distintos. Consequentemente, a "reordenação de eventos" alegada pelo resumo proposto está apenas parcialmente mecanizada.

---

## 9. Consequências Observacionais

`JSObsEquiv.thy` (com `JSAbsEvent.thy`) fornece a camada observacional:

**Infraestrutura (PROVADO):** `obs_equiv_iff_observable`; `obs_equiv_refl/sym/trans` (equivalência); `state_eq_imp_obs_equiv`; projeções `obs_equiv_tohtml`, `obs_equiv_alerts`.

**Absorção → estabilidade observacional (PROVADO):** `absorbed_event_preserves_obs_equiv`, `absorption_implies_obs_stable`, `absorption_implies_alerts_stable` (todos condicionais a `make_event_handler ev obj s = s`); instâncias concretas `absorbed_click_on_paragraph_obs`, `absorbed_mouseover_on_paragraph_obs`, `absorbed_mouseover_on_button_obs`, `absorbed_click_on_window_obs`, `absorbed_nonexistent_target_obs`; além de `querySelector_stable_under_absorbed_event` e `tohtml_stable_under_absorbed_event` (JSAbsEvent.thy).

**Idempotência/absorção → equivalência observacional (PROVADO):** `color_change_idempotent_obs` (a partir de `change_element_color_idempotent`, JSProofs.thy), `color_change_same_result_obs`, `write_absorption_law` (a partir de `change_element_color_absorbs`, JSFrameRule.thy).

**Conexão AUSENTE (NÃO PROVADO):** nenhum lema da forma `heap_ext_eq s1 s2 ⟹ tohtml s1 p = tohtml s2 p` (nem com `Alerts_s`), e portanto nenhuma maneira de elevar os teoremas de comutatividade em nível de heap (`write_object_commute_ext` etc.) a `obs_equiv`. Verificado por busca: `heap_ext_eq` ocorre apenas em JSLocality.thy e em `frame_rule_write_object`/`frame_rule_write_dom_element`.

**Nota sobre as igualdades.** Neste desenvolvimento: igualdade de estados (`s1 = s2`) ⇒ `obs_equiv` (provado). `heap_ext_eq` **não** implica igualdade da lista do heap, **não** implica `obs_equiv` na mecanização, e as implicações inversas são igualmente não provadas. Essas distinções devem ser preservadas em qualquer texto do artigo.

---

## 10. Hierarquia de Dependência de Provas/Resultados

A hierarquia real (reconstruída) é:

```
[Definições fundacionais]
  JSMemoryModel (valores, expr, js_state, operações de heap, browser_init_state)
  JSHTMLSyntax → JSDOM (sintaxe de superfície → DOM no heap; dom_state)
  JSEval (eval_expr_fuel, run_handler)   JSHeapWF (heap_wf, frescor, preservação)
        │                                        │
[Resultados semânticos básicos]
  JSEvents (make_event_handler)                  JSLocality (independência de leituras,
  JSRender (tohtml)        JSProofs (idempotência,     heap_ext_eq, comutatividade de
  JSQuerySelector          última escrita vence)       escritas distintas)
  JSFuel (determinismo; monotonicidade de fuel explicitamente NÃO estabelecida)
        │                                        │
[Resultados de localidade]  ← independência/comutatividade extensional de heap
                               (PROVADO, cond. i≠j)
        │
[Regras de enquadramento]  ← nível de heap: reformulações da comutatividade (PROVADO, cond. i≠j)
                          ← nível de evento: transferência condicional de obs-equivalência
                            (PROVADO, cond. a obs_equiv)
        │
[Reordenação de eventos]  ← events_reorder_two(_by_effect) (PROVADO, cond. a obs_equiv das duas ordens)
        │
[Consequências observacionais] ← infra de obs_equiv; absorção→obs; idempotência→obs (PROVADO)
        │
        ✗  ELO AUSENTE: ponte heap_ext_eq ⟹ tohtml/obs_equiv (NÃO PROVADO)
```

**Fatos de dependência (verificados nos arquivos):**
- `frame_rule_write_object` usa `write_object_commute_ext` (JSLocality); `frame_rule_write_dom_element` usa `write_dom_element_commute_ext`; `frame_rule_change_color_load` usa `load_object_change_color_independent`.
- `write_absorption_law` usa `change_element_color_absorbs` + `state_eq_imp_obs_equiv`.
- `color_change_idempotent_obs` usa `change_element_color_idempotent` (JSProofs) + `state_eq_imp_obs_equiv`.
- `absorbed_event_preserves_obs_equiv` e afins usam `obs_equiv_def` + fatos de absorção de JSAbsEvent.
- Os teoremas de reordenação usam apenas `run_events_two` (+ hipóteses), isto é, assentam sobre a semântica de eventos, não sobre os resultados de localidade — os resultados de localidade **não** estão atualmente conectados a eles.

**Conclusão:** a cadeia hipotetizada *modelo memória/DOM → localidade → independência → regra de enquadramento → comutatividade/reordenação → consequência observacional* está realizada **apenas no seu prefixo em nível de heap** (localidade → independência → comutatividade) e **formalmente desconectada** do sufixo observacional/de reordenação. Os teoremas do sufixo estão provados condicionalmente, mas não são derivados do prefixo.

---

## 11. Resultados Mecanizados Mais Fortes para o Artigo SIICUSP

Núcleo técnico recomendado (3–6 resultados):

1. **`write_object_commute_ext`** (JSLocality.thy) — escritas distintas no heap comutam a menos de `heap_ext_eq`. Papel: o resultado fundamental de comutatividade/independência. Cientificamente importante porque isola *toda* a hipótese estrutural (`i ≠ j`) e a noção *precisa* de igualdade resultante (extensional). Conexão com a reordenação: é a única comutatividade incondicionada disponível para justificar a troca de dois efeitos.
2. **`write_dom_element_commute_ext`** (JSLocality.thy) — a instância em nível de elemento DOM. Papel: eleva a comutatividade de objetos genéricos para elementos DOM (`VDOMElement`), o bloco de construção dos efeitos de handlers.
3. **`load_object_change_color_independent`** / **`frame_rule_change_color_load`** (JSLocality.thy / JSFrameRule.thy) — a pegada de uma mudança de cor: mudar `j` nunca altera o que uma leitura de `i ≠ j` observa. Papel: a afirmação concreta de "partes distintas do estado" a que o resumo alude.
4. **`absorb_no_handler`** (JSAbsEvent.thy) + **`absorbed_event_preserves_obs_equiv`** (JSObsEquiv.thy) — eventos sem handler correspondente deixam o estado inalterado e preservam todos os observáveis. Papel: caracteriza os casos degenerados-mas-reais de reordenação.
5. **`change_element_color_absorbs`** / **`write_absorption_law`** (JSFrameRule.thy) — efeitos repetidos no mesmo elemento colapsam (última escrita vence), invisíveis observacionalmente. Papel: justifica ignorar efeitos repetidos/desordenados sobre o mesmo alvo.
6. **`events_reorder_two_by_effect`** (JSFrameRule.thy) — o teorema de reordenação de sequências de eventos, **apresentado honestamente como condicional**: dadas equações de efeito sobre estados intermediários e `obs_equiv` dos dois estados finais, as duas ordens de `run_events` são observacionalmente equivalentes. Papel: o teorema de empacotamento que será o enunciado principal do artigo **uma vez que suas hipóteses sejam descarregadas** por um resultado de independência (essencial, atualmente ausente).

**Candidato a teorema principal:** o resultado principal pretendido do artigo é o teorema de reordenação — `events_reorder_two_by_effect` é o candidato existente mais próximo — mas deve ser apresentado com sua natureza condicional explícita, ou complementado pelos resultados ausentes da Seção 19. Como está o desenvolvimento, o resultado mais forte *de estrutura incondicional* é `write_object_commute_ext` / `write_dom_element_commute_ext`.

---

## 12. Avaliação da Pergunta de Pesquisa Proposta

> **Sob quais condições formalmente especificadas dois eventos/manipuladores de eventos JavaScript/DOM podem ser executados em ordens diferentes sem alterar o comportamento observável da página?**

1. **A formalização contém um resultado genuíno e não trivial de reordenação de eventos?** Parcialmente. Os teoremas de reordenação existem e estão mecanizados, mas suas hipóteses *são* (a menos de desdobramento) a equivalência observacional das duas ordens. Um resultado genuíno de reordenação derivado de uma condição estrutural de independência (ex.: alvos distintos) **ainda não existe**.
2. **Sob exatamente quais condições os eventos podem ser reordenados?** Formalmente: sempre que as duas execuções sequenciais chegam a estados `obs_equiv` (`events_reorder_two`), ou quando o efeito de cada handler sobre o estado intermediário real é uma mudança de cor e os dois estados resultantes são `obs_equiv` (`events_reorder_two_by_effect`, `frame_rule_events_by_effect`). Nenhuma condição mais forte está mecanizada.
3. **Que noção de independência está de fato formalizada?** Não-interferência extensional de operações de heap em identificadores distintos: `load_object_write_independent`, `load_object_write_dom_independent`, `load_object_change_color_independent`, e comutatividade `write_object_commute_ext`, `write_dom_element_commute_ext` (`heap_ext_eq`). Independência em nível de eventos/handlers **não** está formalizada.
4. **Que noção de comportamento observável está formalizada?** `obs_equiv` = igualdade do HTML renderizado (`tohtml`, num `dom_pos p` fixo) e igualdade do histórico de alertas (`Alerts_s`). Nada mais (pilha, heap, fila de eventos, resultados de seletores) é observável.
5. **O que a reordenação preserva?** Nos teoremas condicionais provados: `obs_equiv` (logo igualdade de `tohtml` e de `Alerts_s`). Os teoremas em nível de heap preservam `heap_ext_eq` (leituras), **não** a lista do heap, **não** o estado completo, **não** `tohtml` por si sós. Igualdade exata de estado, da lista do heap e da estrutura do DOM **não** são preservadas nem alegadas.
6. **Restrita a elementos DOM distintos?** Os resultados estruturais são restritos a **identificadores de heap** distintos (`i ≠ j`); os teoremas em nível de evento não impõem distinção e, em vez disso, impõem hipóteses observacionais.
7. **Há hipóteses significativas sobre estados intermediários?** Sim: `frame_rule_events_by_effect` e `events_reorder_two_by_effect` descrevem efeitos *sobre os estados intermediários* (o estado após o primeiro handler); `frame_rule_events` nomeia as duas execuções concretas. Os comentários do arquivo reconhecem que descrever handlers apenas sobre o estado inicial era "insuficiente" e que este é o desenho corrigido.
8. **A regra de enquadramento é condicional?** Sim — regras em nível de heap condicionais a `i ≠ j`; regras em nível de evento condicionais a hipóteses de `obs_equiv`/efeito.
9. **Afirmação cientificamente mais defensável hoje:** *"No subconjunto modelado de JavaScript/DOM, operações sobre identificadores de heap distintos são mutuamente não-interferentes e comutam a menos de igualdade extensional de heap; eventos sem handler correspondente são absorvidos, preservando o estado observável (HTML renderizado e histórico de alertas); efeitos repetidos sobre o mesmo elemento colapsam no último; e a reordenação de sequências de eventos é provada correta **condicionalmente** à equivalência observacional das duas ordens — que hoje é assumida, não derivada da localidade."*

---

## 13. Auditoria de Alegações do Resumo Preliminar

O resumo provisório (em português) é auditado alegação por alegação.

**Alegação 1** — *"Aplicações web modernas são fortemente orientadas a eventos, nos quais diferentes manipuladores podem atuar sobre elementos distintos do DOM. Nesse contexto, compreender quando a ordem de execução desses eventos pode ser alterada sem modificar o comportamento observável da página é relevante…"*
- Classificação: **INTERPRETAÇÃO / motivação**. Não há conteúdo formal a verificar; aceitável como motivação se o resto do resumo for preciso.

**Alegação 2** — *"Este trabalho apresenta uma formalização, em Isabelle/HOL, de propriedades de independência e reordenação de eventos em um modelo simplificado de execução de JavaScript sobre o DOM."*
- Classificação: **SUPORTADO (com qualificação)**. Existe em `Codes/` uma formalização em Isabelle/HOL de independência (nível de heap) e reordenação (condicional); "modelo simplificado" é preciso. Qualificação: a independência mecanizada é de operações de heap, não dos eventos em si; os teoremas de reordenação são condicionais.

**Alegação 3** — *"A abordagem estabelece condições de localidade que permitem identificar operações que atuam sobre partes distintas do estado da página"*
- Classificação: **SUPORTADO (com qualificação)**. Localidade = identificadores de heap distintos (`i ≠ j`); "partes distintas do estado" deveria dizer "células/identificadores distintos do heap". Fatos de suporte: `heap_ext_eq` (JSLocality.thy), `load_object_write_independent`, etc.

**Alegação 4** — *"e, a partir dessas condições, demonstrar formalmente que determinados manipuladores de eventos podem ser executados em ordens diferentes sem alterar o resultado observável"*
- Classificação: **NÃO PROVADO ATUALMENTE** — o problema central. O desenvolvimento não contém teorema que derive equivalência observacional de execuções reordenadas de handlers a partir das condições de localidade. Os resultados de localidade concluem `heap_ext_eq`; os teoremas de reordenação **assumem** `obs_equiv` das duas ordens; e não existe ponte `heap_ext_eq ⟹ obs_equiv`. Arquivos: JSLocality.thy, JSFrameRule.thy (`frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect`), JSObsEquiv.thy. Redação corrigida proposta: *"a partir dessas condições, demonstra-se formalmente a comutatividade extensional das operações de escrita em células distintas do heap; a reordenação de sequências de eventos é verificada mecanicamente sob hipóteses explícitas de equivalência observacional entre as duas ordens de execução."*

**Alegação 5** — *"A formalização inclui resultados de independência entre operações sobre elementos distintos"*
- Classificação: **SUPORTADO (com qualificação) / DIRETAMENTE PROVADO em nível de heap**. Provado: `load_object_write_dom_independent`, `load_object_change_color_independent`, `write_dom_element_commute_ext` (JSLocality.thy). Qualificação: "elementos distintos" deve ser lido como identificadores de heap distintos; a igualdade obtida é `heap_ext_eq`, não equivalência observacional.

**Alegação 6** — *"regras de enquadramento para eventos"*
- Classificação: **NECESSITA QUALIFICAÇÃO**. `frame_rule_events`/`frame_rule_events_by_effect` existem (JSFrameRule.thy) mas são condicionais a hipóteses observacionais/de efeito; as regras de enquadramento de estrutura incondicional (`frame_rule_write_object`, `frame_rule_write_dom_element`, `frame_rule_change_color_load`) estão em nível de heap. O artigo não deve apresentá-las como regras de enquadramento de lógica de separação.

**Alegação 7** — *"teoremas de comutatividade e reordenação da execução"*
- Classificação: **NECESSITA QUALIFICAÇÃO**. Comutatividade: DIRETAMENTE PROVADO em nível de heap (`write_object_commute_ext`, `write_dom_element_commute_ext`). Reordenação: PROVADO mas condicional (`events_reorder_two`, `events_reorder_two_by_effect`). Os dois devem ser distinguidos; atualmente **não** estão ligados por teorema algum.

**Alegação 8** — *"As propriedades são verificadas mecanicamente pelo provador de teoremas Isabelle/HOL, fornecendo garantias formais de que os resultados decorrem das definições do modelo adotado."*
- Classificação: **SUPORTADO** — os teoremas são enunciados Isabelle com provas verificadas nos arquivos `.thy`. (Reverificação independente por Isabelle durante esta auditoria: ver o Apêndice e a avaliação final quanto ao resultado executado.)

**Alegação 9** — *"Os resultados demonstram como técnicas de métodos formais podem ser utilizadas para caracterizar situações em que interações independentes em aplicações web preservam seu comportamento mesmo diante de diferentes ordens de execução"*
- Classificação: **NÃO PROVADO ATUALMENTE / NECESSITA QUALIFICAÇÃO**. "Interações independentes … preservam seu comportamento" é precisamente a afirmação que nenhum teorema atual estabelece de ponta a ponta: não se mostrou que independência em nível de heap preserva `tohtml`/`Alerts_s` sob reordenação. Redação corrigida: *"Os resultados demonstram como técnicas de métodos formais podem caracterizar, em um modelo simplificado, a comutatividade de operações sobre células distintas e a reordenação de eventos sob condições explícitas de equivalência observacional, apontando resultados de reordenação incondicionais como trabalho futuro."*

**Verificação das expressões especiais:**
- *"comportamento observável"* → refere-se legitimamente a `obs_equiv` (JSObsEquiv.thy) = `tohtml` + `Alerts_s`. OK quando usada em teoremas de `obs_equiv`.
- *"manipuladores podem ser executados em ordens diferentes"* → apenas suportado **condicionalmente** (Alegação 4).
- *"operações sobre partes distintas do estado"* → deve ser "operações sobre identificadores distintos do heap" (`i ≠ j`).
- *"independência entre operações sobre elementos distintos"* → apenas em nível de heap (Alegação 5).
- *"regras de enquadramento para eventos"* → regras de enquadramento condicionais (Alegação 6).
- *"comutatividade"* → comutatividade `heap_ext_eq` em nível de heap; **não** comutatividade `obs_equiv` de handlers.
- *"reordenação da execução"* → reordenação de `run_events`, condicional (Alegação 7).
- *"preservam seu comportamento"* → **não** provado a partir de independência; apenas absorção e colapso no mesmo elemento preservam observáveis incondicionalmente.

---

## 14. Avaliação do Título Proposto

**Título:** *Formal Verification of Event Independence and Reordering in JavaScript with Isabelle/HOL* (PT: *Verificação Formal de Independência e Reordenação de Eventos em JavaScript com Isabelle/HOL*).

**Classificação: AMPLO DEMAIS (TOO BROAD)** para a mecanização atual.

Justificativa: o título afirma verificação formal de **independência de eventos**, mas independência em nível de evento/handler não é definida nem provada em lugar algum; apenas a independência de operações de heap sobre identificadores distintos é provada. Também afirma **reordenação de eventos**, que existe, mas apenas como teoremas condicionais cujas hipóteses contêm a equivalência observacional que está sendo concluída. O título descreve com precisão o *programa de pesquisa*, mas exagera os *resultados atuais*. (Se os resultados essenciais da Seção 19 forem mecanizados, o título torna-se defensável como está, a menos de "JavaScript" → "um modelo simplificado de JavaScript/DOM".)

Títulos alternativos, mais precisos:

1. EN: *Locality, Commutativity, and Conditional Event Reordering in a Mechanized JavaScript/DOM Model* — PT: *Localidade, Comutatividade e Reordenação Condicional de Eventos em um Modelo Mecanizado de JavaScript/DOM*
2. EN: *Formalizing Heap Locality and Event Reordering in a Simplified JavaScript DOM Semantics with Isabelle/HOL* — PT: *Formalização de Localidade de Heap e Reordenação de Eventos em uma Semântica Simplificada de DOM em JavaScript com Isabelle/HOL*
3. EN: *Independence of Distinct Heap Cells and Event Reordering in a Verified JavaScript/DOM Subset* — PT: *Independência de Células Distintas do Heap e Reordenação de Eventos em um Subconjunto Verificado de JavaScript/DOM*

---

## 15. Relação com a Pesquisa Anterior de Equivalência Observacional

Baseada nos artefatos presentes neste workspace (os arquivos do projeto anterior não estão presentes; a comparação usa a infraestrutura visível aqui, que o enunciado afirma originar-se da pesquisa anterior de equivalência observacional).

### Infraestrutura reutilizada
- O modelo de memória/valores/expressões (`js_vle`, `expr`, `js_state`, operações de heap) — JSMemoryModel.thy.
- A construção do DOM a partir de HTML de superfície (`dom_state`) — JSHTMLSyntax.thy, JSDOM.thy.
- O avaliador e a execução de handlers (`eval_expr_fuel`, `run_handler`) — JSEval.thy.
- O despacho de eventos (`make_event_handler`) — JSEvents.thy.
- O renderizador `tohtml` e `dom_pos` — JSRender.thy.
- As definições observacionais `observable`/`obs_equiv` — JSObsEquiv.thy.
- A teoria de absorção — JSAbsEvent.thy; idempotência básica — JSProofs.thy; boa-formação — JSHeapWF.thy; fuel/determinismo — JSFuel.thy; seletores — JSQuerySelector.thy.

### Novo foco central
- **Localidade e independência:** `heap_ext_eq`, a família `load_object_*_independent` e os teoremas de comutatividade (JSLocality.thy).
- **Regras de enquadramento e reordenação de eventos:** `run_events`, `frame_rule_*`, `events_reorder_*` (JSFrameRule.thy).

### Sobreposição
- A equivalência observacional é sobreposição inevitável: `obs_equiv` é o *observável* usado pelas conclusões de reordenação, e `tohtml` é a espinha dorsal da renderização.
- Os resultados de absorção servem a ambas as narrativas (são os casos triviais reordenáveis).

### Distinção
- A pergunta anterior era de *equivalência*: quando dois programas/estados são observacionalmente iguais? A nova pergunta é de *reordenação*: quando a **ordem de execução de despachos de eventos** pode ser trocada sem alterar o observável, e quais **condições de localidade/enquadramento** justificam a troca? Os objetos técnicos novos são os teoremas de comutatividade, as regras de enquadramento e os enunciados de reordenação de `run_events`.
- **Avaliação honesta:** a distinção é real no nível da pergunta de pesquisa e dos resultados em nível de heap, mas a mecanização atual **ainda não entregou** o teorema de reordenação de eventos principal, de modo que a distância científica em relação ao trabalho anterior é hoje menor do que a proposta implica. O artigo será genuinamente distinto apenas se os resultados essenciais ausentes (Seção 19) forem adicionados, ou se o artigo for reenquadrado em torno de localidade/comutatividade de heap com a reordenação condicional apresentada como sua consequência-por-hipótese.

---

## 16. Limitações e Alegações que Não Devemos Fazer

Limitações verificadas **deste** desenvolvimento (cada uma confirmada nos arquivos):

1. **Semântica JavaScript simplificada (confirmado).** A linguagem de expressões tem 8 construtores; `eval_binop` suporta apenas `+` sobre números (todo o resto → `VTypeError`); sem laços, literais de objeto, arrays, exceções, protótipos, sutilezas de escopo de `var`, ou ECMAScript completo. Qualquer afirmação deve dizer "subconjunto/modelo simplificado".
2. **DOM simplificado (confirmado).** Elementos DOM são listas planas de propriedades no heap (`VDOMElement tag props`); o renderizador os achata por um mapa de posições (`dom_pos`); não há API de mutação de árvore em handlers, nem generalidade de get/set de atributos além de `color`, nem CSS ou layout.
3. **Semântica de eventos restrita (confirmado).** Apenas `EvClick`/`EvMouseOver`; handlers buscados diretamente na propriedade do elemento alvo; sem bubbling/captura, sem controle de propagação, sem objeto de evento, sem `preventDefault`. O campo declarado `event`/`event_queue`/`Events_s` é **código morto**: `Events_s` nunca é lido nem escrito pela maquinaria de eventos ou de avaliação (verificado por busca).
4. **Sem concorrência de navegador real / sem event loop (confirmado).** O despacho é um transformador de estado síncrono e determinístico (`make_event_handler`); não há fila de tasks/microtasks, nem promises, nem assincronia. Alegar relevância para o comportamento real do event loop de navegadores é insustentável.
5. **Efeitos de handler restritos (confirmado).** Efeitos modelados: `alert` (anexa a `Alerts_s`), `changeColor` (escrita de cor em um único elemento), `createElement` (alocação). Nenhum handler no desenvolvimento remove nós, reordena o DOM ou escreve propriedades arbitrárias.
6. **Hipóteses de identificadores distintos (confirmado).** Todos os teoremas de independência/comutatividade exigem `i ≠ j`; não há análise de aliasing/alcançabilidade.
7. **Hipóteses de estados intermediários (confirmado).** `frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect` todos carregam hipóteses sobre os estados intermediários/finais reais ou sobre sua `obs_equiv`.
8. **Igualdade de heap vs equivalência observacional (confirmado).** `heap_ext_eq` (todas as leituras coincidem) **não** está conectada a `tohtml`/`obs_equiv`; igualdade de estados ⇒ `obs_equiv` está provada, a recíproca e as pontes de heap não. O artigo não deve confundir essas noções.
9. **Limites do modelo de renderização (confirmado).** `tohtml` depende da lista do heap e de um `dom_pos` fixo; nenhum lema mostra robustez a ordem/permutação, e `obs_equiv` é parametrizada por `p`.
10. **Sem monotonicidade de fuel (confirmado).** JSFuel.thy documenta explicitamente que `eval_expr_fuel n … = (v,s') ∧ ¬out_of_fuel v ∧ n ≤ m ⟹ eval_expr_fuel m … = (v,s')` **não** está estabelecida, e que a exaustão de fuel não se propaga por expressões compostas (ex.: `eval_binop` pode sobrescrever o erro de falta de fuel). `default_fuel = 200` é um limite arbitrário; afirmações sobre "a semântica" devem reconhecer o fuel.
11. **Sem validação contra motores de navegador (confirmado).** Nada liga o modelo a qualquer motor real ou ao event loop da especificação HTML.
12. **Sem semântica ECMAScript completa (confirmado).** Ver item 1.

Consequências para o artigo: toda afirmação forte deve ser escopada ao "subconjunto modelado"; o artigo não deve alegar garantias para navegadores reais; não deve igualar igualdade extensional de heap a equivalência observacional; e deve apresentar os teoremas de reordenação com suas hipóteses.

---

## 17. Estrutura Recomendada do Artigo SIICUSP

(Baseada no Anexo I do edital: resumo de até 2 páginas, duas colunas, seções abaixo; submetido em português **e** inglês.)

1. **Título (PT/EN conforme o arquivo)** — usar um título qualificado conforme a Seção 14.
2. **Objetivos** — colocar a pergunta de pesquisa exatamente como na Seção 12; enunciar as hipóteses a verificar (localidade ⇒ independência ⇒ reordenação ⇒ observáveis). Teorias Isabelle: todo o desenvolvimento (visão geral). Apresentar: a pergunta, não resultados.
3. **Métodos e Procedimentos** — resumo do modelo: `js_state`, heap, `VDOMElement`, `eval_expr_fuel`/`run_handler`, `make_event_handler`, `tohtml`, `observable`/`obs_equiv`, `heap_ext_eq`, `run_events`; Isabelle/HOL + provas verificadas; mapa de teorias (JSMemoryModel → … → JSFrameRule). Apresentar: uma pequena figura do mapa de dependências; equações numeradas conforme o edital. Omitir: demos `value`, detalhes de seletores, internos de fuel (uma linha).
4. **Resultados** — os 3–6 resultados da Seção 11, com nomes exatos e hipóteses; distinguir explicitamente `heap_ext_eq` de `obs_equiv`; enunciar os teoremas de reordenação **com suas hipóteses**. Apresentar: `write_object_commute_ext`, `write_dom_element_commute_ext`, `load_object_change_color_independent`, `absorb_no_handler`+`absorbed_event_preserves_obs_equiv`, `change_element_color_absorbs`/`write_absorption_law`, `events_reorder_two_by_effect` (condicional). Omitir: a cascata de lemas de boa-formação (citar como invariante), wrappers de seletores.
5. **Conclusões** — responder à pergunta de pesquisa com qualificação (o que está provado: localidade/comutatividade de heap, absorção, reordenação condicional; o que está aberto: a ponte heap→observável e independência de handlers). Mencionar limitações (Seção 16) e as próximas provas planejadas. Terminar com as declarações exigidas: conflito de interesses; contribuições dos autores; bolsa (se houver).
6. **Referências bibliográficas** — Isabelle/HOL (Nipkow, Paulson, Wenzel); lógica de separação (Reynolds) apenas se a discussão de regras de enquadramento justificar (notar que o modelo **não** é lógica de separação); referência do modelo de eventos HTML/DOM; referência do projeto anterior; eventualmente uma referência de survey de semântica de JavaScript. Manter poucas — 2 páginas no total.

O artigo deve permanecer centrado em **independência e reordenação**, usando o avaliador/DOM/renderizador apenas como infraestrutura.

---

## 18. Requisitos do Template/Edital SIICUSP

Extraídos de `Siicusp/edital.pdf` (34º SIICUSP) e de `Siicusp/template.doc` / `template (1).doc` (dois templates Word de 2 páginas quase idênticos, ~830–850 palavras de texto-placeholder):

- **Documento:** "Resumo" (abstract), **até 2 páginas**, com o logotipo do 34º SIICUSP, organizado em: (a) Título; (b) Autor(es), colaborador(es) e orientador; (c) Unidade e Universidade; (d) E-mail do primeiro autor; (e) Objetivos; (f) Métodos e Procedimentos; (g) Resultados; (h) Conclusões (parciais ou finais); (i) Declaração de conflito de interesses; (j) Contribuições de cada autor (se houver mais de um); (k) informação sobre recebimento de bolsa acadêmica (se houver); (l) Referências Bibliográficas.
- **Idioma:** redigido em Português **e** Inglês (dois arquivos PDF; estudantes estrangeiros podem submeter apenas em Inglês).
- **Formatação:** A4 (210×297 mm); margens superior 3,3 cm, inferior 4,2 cm, esquerda/direita 2,6 cm (margens espelho); duas colunas de 7,5 cm cada com 0,8 cm entre colunas; Arial; títulos/subtítulos 13 pt negrito centralizados; nomes 13 pt negrito centralizados; faculdade/universidade 13 pt centralizado; e-mail 10 pt centralizado; texto justificado, espaçamento simples, 10 pt.
- **Equações:** em linhas separadas, numeradas. **Tabelas:** numeradas, títulos acima (9 pt, sem negrito/itálico), podem ocupar duas colunas. **Figuras:** numeradas, títulos abaixo (9 pt), podem ocupar duas colunas.
- **Cabeçalho do template:** TÍTULO; Autor(es) – Estudante(s) de Graduação; Colaborador(es) (máximo 3); Orientador(a); Faculdade/Universidade; E-mail do primeiro autor.
- **Restrições de submissão:** inscrições 20/07–24/08/2026; dois PDFs (resumo PT e EN); título idêntico no formulário, no resumo e na apresentação; resumos fora do padrão não serão publicados; resumos corrigidos até 26/10/2026; apresentações da 1ª etapa 01/09–19/10/2026; etapa internacional 25–26/11/2026 (materiais em inglês).
- **Critérios de avaliação (Anexo II):** conhecimento do conteúdo, virtudes/limitações da metodologia, entendimento dos resultados, conclusões que respondem à pergunta da pesquisa, relevância; clareza da comunicação oral; resumo sintético, referências adequadas e conformidade com o modelo.
- **Nota sobre `Siicusp/document.pdf`:** documento de 1 página com assinatura digital da Secretaria de Segurança Pública do Estado de São Paulo (documento policial) — **não relacionado** à formatação SIICUSP; não faz parte do edital/template. Foi extraído textualmente e não contém instruções SIICUSP. `template.doc`/`template (1).doc` foram inspecionados via conversão `textutil` (nenhum original modificado).

---

## 19. Questões em Aberto ou Provas Faltantes

Estado atual: a formalização é **internamente coerente** e suficiente para um artigo centrado em *localidade de heap, comutatividade, absorção e reordenação condicional*. **Ainda não é suficiente** para a afirmação forte do resumo/título propostos. Resultados mecanizados ausentes, classificados:

1. **Ponte heap→observável** — `heap_ext_eq s1 s2 ⟹ tohtml s1 p = tohtml s2 p` (mais uma condição de preservação de `Alerts_s` ou hipótese de ausência de alertas). Atualmente ausente; necessária para elevar `write_object_commute_ext`/`write_dom_element_commute_ext` a `obs_equiv`. Teorias envolvidas: JSLocality.thy, JSRender.thy, JSObsEquiv.thy. Classificação: **ESSENCIAL**.
2. **Lema de pegada/independência de handler** — ex.: se o corpo de um handler apenas `changeColor` seu próprio alvo e não emite alertas, então `make_event_handler` preserva leituras de outros ids (ou alguma caracterização precisa de efeito suficiente para reordenação). Atualmente ausente; as hipóteses de efeito (`HI`/`HJ`) dos teoremas de reordenação nunca são descarregadas. Teorias: JSEval.thy, JSEvents.thy, JSLocality.thy, JSFrameRule.thy. Classificação: **ESSENCIAL**.
3. **Teorema de reordenação incondicional** — o resultado principal: dois handlers com alvos distintos, efeitos restritos a mudança de cor e sem alertas podem ser reordenados preservando `obs_equiv` (idealmente enunciado via `run_events`). Segue uma vez que (1)+(2) existam. Classificação: **ESSENCIAL** (para o artigo como proposto).
4. **Congruência de `tohtml` sob permutação do heap / robustez de ordem** — `collect_dom_nodes`/`sort_by_pos` hoje não têm lemas de corretude; um lema de invariância por permutação tornaria (1) robusto e tem valor independente. Teorias: JSRender.thy. Classificação: **FORTEMENTE RECOMENDADO**.
5. **Instância concreta reordenada** — uma instância provada sobre um estado com dois elementos distintos portadores de handler (o `dom_state` atual tem apenas um handler de click; `sample_html` precisaria de um segundo elemento com handler), ex.: `obs_equiv (run_events [(EvClick,2),(EvMouseOver,3)] s) (run_events [(EvMouseOver,3),(EvClick,2)] s) sample_pos`. Classificação: **FORTEMENTE RECOMENDADO** (ilustração do artigo).
6. **Congruência de `obs_equiv` (lema de contexto)** — `obs_equiv s1 s2 p ∧ … ⟹ obs_equiv (run_events l s1) (run_events l s2) p` (determinismo + congruência do despacho) permitiria compor reordenação com eventos adicionais. Teorias: JSObsEquiv.thy, JSFrameRule.thy, JSFuel.thy. Classificação: **FORTEMENTE RECOMENDADO**.
7. **Reordenação n-ária / permutação de sequências de eventos** — além de dois eventos, via resultados de permutação de fold. Classificação: **OPCIONAL**.
8. **Monotonicidade de fuel para o avaliador** — o próprio JSFuel.thy sinaliza isso como não provado; relevante apenas se o artigo discutir adequação da semântica. Classificação: **OPCIONAL** (a menos que fuel seja discutido).
9. **Semântica de fila de eventos** — tornar `Events_s` vivo (eventos pendentes, laço de despacho) ampliaria a história de "reordenação" para reordenação de filas. Classificação: **OPCIONAL**.

Conforme instruções, nenhum desses foi implementado durante esta auditoria.

---

## 20. Avaliação Final

- **Completude:** os 14 arquivos `.thy` foram lidos integralmente (2.822 linhas no total); cada teorema/lema (102 declarações) foi inventariado com arquivo e linha.
- **Alegações verificadas:** os três resultados nomeados **existem e estão provados**: `frame_rule_events` (JSFrameRule.thy:110), `events_reorder_two` (JSFrameRule.thy:177), `events_reorder_two_by_effect` (JSFrameRule.thy:198) — todos **condicionais** a hipóteses observacionais; `frame_rule_events_by_effect` (JSFrameRule.thy:139) idem.
- **Verificação com Isabelle:** uma verificação independente das teorias copiadas foi executada com Isabelle2025-2 e **concluiu com sucesso** — `isabelle process_theories` processou todas as 14 teorias com código de saída 0, zero linhas de erro e apenas avisos benignos de "regra de reescrita duplicada" (comandos e resultados exatos no Apêndice); nenhum arquivo de teoria em `Codes/` foi modificado.
- **Resumo proposto:** requer revisão — especificamente a Alegação 4 ("…demonstrar formalmente que determinados manipuladores… podem ser executados em ordens diferentes sem alterar o resultado observável") está **NÃO PROVADA ATUALMENTE**; as Alegações 3, 5, 6, 7, 9 precisam de qualificação.
- **Título proposto:** **AMPLO DEMAIS** para a mecanização atual (alternativas na Seção 14).
- **Suficiência para o artigo SIICUSP:** suficiente para um artigo honesto sobre localidade/comutatividade de heap/absorção com reordenação *condicional*; **não suficiente** para o artigo como o resumo provisório o descreve. A lacuna pode ser fechada pelos resultados ESSENCIAIS da Seção 19 (ponte heap→observável, lema de pegada de handler, teorema de reordenação incondicional) — mecanicamente plausíveis dentro das teorias existentes.
- **Limitação mais importante:** o elo ausente entre igualdade extensional de heap (`heap_ext_eq`) e equivalência observacional (`obs_equiv`), que deixa os teoremas de reordenação de eventos com hipóteses de equivalência observacional que nada no desenvolvimento descarrega a partir de condições estruturais.
- **Afirmação cientificamente mais defensável:** conforme a Seção 12, item 9.

---

## Apêndice — Verificação com Isabelle (Seção 19 da tarefa)

- **Disponibilidade:** `/opt/homebrew/bin/isabelle` → `Isabelle2025-2` (também `/Applications/Isabelle2025.app`, `/Applications/Isabelle2025-2.app`). Isabelle/HOL foi executado durante esta auditoria.
- **Procedimento não destrutivo:** os 14 arquivos `.thy` foram **copiados** para `/tmp/isaudit/AuditSession/` (nenhum arquivo do workspace foi modificado); um `ROOT` mínimo (`session AuditSession = HOL + options [document = false] theories [JSFrameRule]`) foi criado **apenas em /tmp**.
- **Tentativa 1 (compilação de sessão):** `isabelle build -d /tmp/isaudit -b AuditSession` → falhou com `*** Bad session root directory: "/private/tmp/isaudit" (missing "ROOT" or "ROOTS")` — erro de caminho (o arquivo ROOT está no subdiretório da sessão), não erro de teoria.
- **Tentativa 2 (compilação de sessão, caminho corrigido):** `isabelle build -d /tmp/isaudit/AuditSession -b AuditSession` → falhou com `*** [SQLITE_CANTOPEN] Unable to open the database file`. Repetida com `-o build_database=false` e com `ISABELLE_HOME_USER`/`ISABELLE_OUTPUT`/`ISABELLE_BROWSER_INFO` apontados para diretórios recém-criados e graváveis em `/tmp` — mesmo erro. Causa raiz identificada: o ambiente de execução nega escritas em `~/.isabelle/Isabelle2025-2` (`touch` → `Operation not permitted`), e `isabelle build` precisa do banco SQLite hospedeiro lá; a substituição de `ISABELLE_HOME_USER` pelo ambiente é ignorada pelo lançador do Isabelle2025-2. Trata-se de uma **limitação de ambiente**, não de erro de teoria. Nenhum reparo de teoria foi tentado.
- **Verificação bem-sucedida (processamento ad hoc de teorias, sem banco de dados de sessão):** `isabelle process_theories -l HOL -D /tmp/isaudit/AuditSession -O -v JSMemoryModel JSHTMLSyntax JSDOM JSEval JSEvents JSRender JSQuerySelector JSHeapWF JSLocality JSProofs JSFuel JSAbsEvent JSObsEquiv JSFrameRule`
  - **Resultado:** código de saída **0** (sucesso); o log termina com `Timing Draft (8 threads, 101.872s elapsed time, …)` e `Finished Draft (0:01:43 elapsed time, …)`.
  - Todas as **14** teorias foram processadas (`Draft: theory Draft.JSMemoryModel` … `Draft.JSFrameRule`); **0** linhas casando com `***` (nenhum erro); os únicos avisos são benignos `Ignoring duplicate rewrite rule` (de `simp add: …simps`), além de linhas normais de `Output` dos comandos `value` das teorias.
- **Conclusão:** as 14 teorias de `Codes/` **foram verificadas de forma independente por Isabelle/HOL (Isabelle2025-2) durante esta auditoria**, sobre cópias byte-idênticas, sem qualquer modificação. Esta auditoria, portanto, **não** se enquadra na ressalva de "auditadas estaticamente, mas não verificadas de forma independente".
